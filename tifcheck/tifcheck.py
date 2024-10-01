# tifcheck.py
#
# Copyright (c) 2024 Leica Microsystems CMS GmbH
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

"""
Validate and repair TIFF files.

This standalone Python 3.12 script produces a JSON formatted report listing
items that describe conformance to TIFF Version 6, BigTIFF, and related
formats, categorized by severity.

  Fail   An unrecoverable condition.
  Error  A condition that is recoverable but disallowed.
  Warn   A condition that is allowed but not expected.
  Note   A condition that some implementations might not support.
  Info   Supplementary information.

The set of conditions analyzed is not intended to be exhaustive.  It will
grow over time as resources allow.  Use the list command to output a report
with the metadata of existing items.

The repair command attempts to rewrite the input file in place, in order to
clear selected item codes.  Repairs include:

  203 Tag out of order
  204 Tag conflict

The current design of this script prioritizes minimal assumptions about
input, minimal dependencies, and low memory use.  It does not prioritize
speed optimization or integrity checking of i/o.

Author: Chris Birnbaum, christopher.birnbaum@leica-microsystems.com
Homepage: https://github.com/AiviaCommunity
License: MIT
"""

ISO_8601_UTC = '%Y-%m-%dT%H:%M:%SZ'
TAG_CUTOFF = 50

__version__ = '20240930'

import dataclasses
import enum
import inspect
import json
import math
import os
import platform
import struct
import sys
import tkinter
import tkinter.filedialog
import traceback
from datetime import datetime, UTC
from time import time

############################################################################
# Classes.

class TifPreamble:
    struct32 = struct.Struct('=2s2s4s')  # The '=' is for no padding.
    struct64 = struct.Struct('=2s2s4s8s')

    sig: bytes
    ver: bytes

    order: str
    bits: int
    is64: bool
    link: int

    pre_struct: struct.Struct
    count_struct: struct.Struct
    entry_struct: struct.Struct
    link_struct: struct.Struct

    def __init__(self, src):
        self.sig, self.ver, link32, link64 = TifPreamble.struct64.unpack(src)

        self.order = '<' if self.sig == b'II' else \
                     '>' if self.sig == b'MM' else ''

        version_number = struct.unpack(self.order + 'H', self.ver)[0]
        offset_size, reserved = struct.unpack(self.order + 'HH', link32)

        if version_number == 43:
            self.ver += link32  # For error payload if any.

        self.bits = 64 if version_number == 43 and offset_size == 8 and reserved == 0 else \
                    32 if version_number == 42 else 0

        self.is64 = self.bits == 64
        self.link = struct.unpack(self.order + 'Q', link64)[0] if self.is64 else \
                    struct.unpack(self.order + 'I', link32)[0]

        self.pre_struct = TifPreamble.struct64 if self.is64 else TifPreamble.struct32
        self.count_struct = struct.Struct(self.order + ('Q' if self.is64 else 'H'))
        self.entry_struct = struct.Struct(self.order + ('HHQQ' if self.is64 else 'HHII'))
        self.link_struct = struct.Struct(self.order + ('Q' if self.is64 else 'I'))

    def is_wellformed(self):
        return self.order and self.bits and self.link

    def sizeof_ifd(self, tag_count):
        return self.offset_ifd_link(tag_count) + self.link_struct.size

    def offset_ifd_link(self, tag_count):
        return self.count_struct.size + tag_count * self.entry_struct.size

@dataclasses.dataclass
class TifEntry:
    tag: int
    dtype: int
    count: int
    value: int

class ItemCategory(int, enum.Enum):
    none = 0
    info = 1
    note = 2
    warn = 3
    error = 4
    fail = 5

class ItemStatus(int, enum.Enum):
    none = 0
    deprecated = 1
    proposed = 2
    pending = 3
    preview = 4
    standard = 5
    repairable = 6

@dataclasses.dataclass
class Item:
    # The first five fields come from a static definition.  The value field is
    # optional and may be different for every checked occurrence.
    code: int
    category: ItemCategory
    status: ItemStatus
    name: str
    comment: str
    value: str

    def valdict(self):
        return {'code': self.code, 'name': self.name, 'value': self.value}

    def metadict(self):
        return {k: v.name if isinstance(v, enum.Enum) else v
                for k, v in self.__dict__.items() if k != 'value'}

class RepairList:
    command: str
    enabled: dict[int,str]
    repaired: list[Item]

    def __init__(self, command=''):
        self.command = command
        if command == '-repair':
            self.enabled = {i.code: '' for i in list_all() if i.status == ItemStatus.repairable}
        else:
            self.enabled = {}
            parts = command[len('-repair-'):].split('-')
            for i in reversed(range(len(parts) - 1)):
                if not str.isdecimal(parts[i + 1][0]) or (not str.isdecimal(parts[i][-1]) and parts[i][-1] != ')'):
                    parts[i] += parts[i + 1]  # Allow negative numbers inside parameters.
            for p in parts:
                if p:
                    paren = p.find('(')
                    if paren == -1:
                        self.enabled[int(p)] = ''
                    else:
                        self.enabled[int(p[:paren])] = p[paren + 1:-1]
        self.repaired = []

# Item definitions are maintained here in the form of method decls, which
# synthesize items from parameters combined with reflection on the method
# name.  This is for prototyping ergonomics, and will change eventually.
class TifCheck:
    items: list[Item] = []
    repairs: RepairList
    fsize: int
    file_size_digits: int
    tp: TifPreamble
    ifd_count: int

    def __init__(self, path, repairs):
        if path:
            self.repairs = repairs
            self._check_file(path)
            with open(path, 'r+b' if repairs.enabled else 'rb') as f:
                if self._check_preamble(f) and self._check_primary_chain(f):
                    self._check_tags(f)

    #####################
    # Begin definitions #
    #####################

    def fail_signature_missing(self, v=None):  return self._a(v, 101, ItemStatus.standard)
    def fail_signature_unknown(self, v=None):  return self._a(v, 102, ItemStatus.standard)
    def fail_tiff_version_unknown(self, v=None):      return self._a(v, 103, ItemStatus.standard)
    def fail_ifd_start_invalid(self, v=None):  return self._a(v, 104, ItemStatus.standard, "Before the end of the preamble.")
    def fail_ifd_start_out_of_bounds(self, v=None):   return self._a(v, 105, ItemStatus.standard, "Beyond the end of the file.")
    def fail_ifd_size_out_of_bounds(self, v=None):    return self._a(v, 106, ItemStatus.standard)

    def error_ifd_link_invalid(self, v=None):  return self._a(v, 200, ItemStatus.standard, "An invalid position before the end of the file.")
    def error_ifd_link_out_of_bounds(self, v=None):   return self._a(v, 201, ItemStatus.standard, "Beyond the end of the file.")
    def error_ifd_circular_link(self, v=None): return self._a(v, 202, ItemStatus.standard)
    def error_tag_out_of_order(self, v=None):  return self._a(v, 203, ItemStatus.repairable)
    def error_tag_conflict(self, v=None):      return self._a(v, 204, ItemStatus.repairable)

    def warn_ifd_empty(self, v=None):          return self._a(v, 300, ItemStatus.standard)
    def warn_ifd_oversize(self, v=None):       return self._a(v, 301, ItemStatus.standard)

    def note_nonstandard_ext(self, v=None):    return self._a(v, 400, ItemStatus.standard, "Expected 'tif', all lowercase, no dot.  One 'f' for 'file', not two for 'file format'.")

    def info_file_path_resolved(self, v=None): return self._a(v, 1000, ItemStatus.standard)
    def info_file_size(self, v=None):          return self._a(v, 1001, ItemStatus.standard, "Bytes.")
    def info_file_modified(self, v=None):      return self._a(v, 1002, ItemStatus.standard, "ISO 8601 file modified time according to platform.")
    def info_file_created(self, v=None):       return self._a(v, 1003, ItemStatus.standard, "ISO 8601 file creation time.  This does not exist on some plaforms.  It can be later than modified time due to file copy.")
    def info_tiff_bits(self, v=None):          return self._a(v, 1004, ItemStatus.standard, "Either 32 or 64.")
    def info_tiff_order(self, v=None):         return self._a(v, 1005, ItemStatus.standard, "Either LE or BE.")
    def info_ifd_first_offset(self, v=None):   return self._a(v, 1006, ItemStatus.standard, "Byte offset of the first IFD.")
    def info_ifd_last_offset(self, v=None):    return self._a(v, 1007, ItemStatus.standard, "Byte offset of the last IFD.")
    def info_ifd_count(self, v=None):          return self._a(v, 1008, ItemStatus.standard)
    def info_ifd_fragmentation(self, v=None):  return self._a(v, 1009, ItemStatus.standard)
    def info_unaligned_offset_count(self, v=None):    return self._a(v, 1010, ItemStatus.standard, "TIFF6 requires 16bit alignment.  Almost no one cares.")

    #####################
    #  End definitions  #
    #####################

    def _a(self, val, code, status, comment=''):
        parts = inspect.stack()[1].function.split('_')
        name = ' '.join(parts[1:])
        if val != None:
            i = Item(code, ItemCategory[parts[0]], status, name, comment, str(val))
            return self.items.append(i) or i
        else:
            for i in self.items:
                if i.name == name:
                    return i
            return None

    def zfill(self, n):
        return str(n).zfill(self.file_size_digits)

    def _check_file(self, path):
        if not path.endswith('.tif'):
            self.note_nonstandard_ext(os.path.splitext(path)[-1].lstrip('.'))
        finfo = os.stat(path)
        self.fsize = finfo.st_size
        self.file_size_digits = math.ceil(math.log(self.fsize, 10))
        try:
            self.info_file_path_resolved(os.path.realpath(path))
            self.info_file_size(self.fsize)
            self.info_file_modified(datetime.fromtimestamp(finfo.st_mtime, UTC).strftime(ISO_8601_UTC))
            self.info_file_created(datetime.fromtimestamp(_creation_time(finfo), UTC).strftime(ISO_8601_UTC))
        except:
            pass  # OS problems.

    def _check_preamble(self, f):
        b = f.read(TifPreamble.struct64.size)
        if len(b) < TifPreamble.struct64.size:
            # For simplicity we also trap here for file size between 32 and 64-bit preamble size, which is not recoverable.
            self.fail_signature_missing(f'File size of {len(b)} is too small.')
            return False

        self.tp = TifPreamble(b)
        if not self.tp.order:
            self.fail_signature_unknown('0x' + self.tp.sig.hex())
            return False

        if not self.tp.bits:
            self.fail_tiff_version_unknown('0x' + self.tp.ver.hex())
            return False

        self.info_tiff_bits(self.tp.bits)
        self.info_tiff_order('LE' if self.tp.order == '<' else 'BE')
        self.info_ifd_first_offset(self.zfill(self.tp.link))
        return True

    def _check_primary_chain(self, f):
        link = min_start = max_stop = self.tp.link
        self.ifd_count = unaligned = ifd_size_total = validated = 0
        ifd_range = lambda: max_stop - min_start

        while link:
            # Check the link.
            if link < self.tp.pre_struct.size:
                if link == self.tp.link:
                    self.fail_ifd_start_invalid(link)
                    return False
                self.error_ifd_link_invalid(link)
                break

            if link > self.fsize - self.tp.sizeof_ifd(0):
                if link == self.tp.link:
                    self.fail_ifd_start_out_of_bounds(link)
                    return False
                self.error_ifd_link_out_of_bounds(link)
                break

            if link & 1:
                unaligned += 1

            # Check entry count at the link.
            entry_count = _read_struct(f, self.tp.count_struct, link)
            ifd_size = self.tp.sizeof_ifd(entry_count)

            if ifd_size > self.fsize - link:
                self.fail_ifd_size_out_of_bounds(
                    f'IFD #{self.ifd_count} at {self.zfill(link)}: Size of {ifd_size} with {entry_count} tags exceeds file size of {self.fsize}.')
                return False

            if entry_count > TAG_CUTOFF:
                self.warn_ifd_oversize(
                    f'IFD #{self.ifd_count} at {self.zfill(link)}: Ignoring {entry_count - TAG_CUTOFF} of {entry_count} tags.')

            if entry_count < 1:
                self.warn_ifd_undersize(link)

            # Cycle detection.  Low precision, constant memory.
            min_start = min(min_start, link)
            max_stop = max(max_stop, link + ifd_size)
            ifd_size_total += ifd_size
            if ifd_size_total > ifd_range():
                self.error_ifd_circular_link('')  # TODO: Iterate again to find the first circular link.
                break

            # Accept IFD and read next link.
            self.ifd_count += 1
            validated = link
            link = _read_struct(f, self.tp.link_struct, link + self.tp.offset_ifd_link(entry_count))

        self.info_ifd_count(self.ifd_count)
        if validated:
            self.info_ifd_last_offset(self.zfill(validated))

        if ifd_size_total <= ifd_range():
            self.info_ifd_fragmentation(f'{1 - (ifd_size_total / ifd_range()):.2f}')

        if unaligned:
            self.info_unaligned_offset_count(unaligned)
        return True

    def _check_tags(self, f):
        pos = self.tp.link
        for ifd_index in range(self.ifd_count):
            entry_count = _read_struct(f, self.tp.count_struct, pos)  # Count is pre-cutoff, for editing down below.
            b = f.read(min(entry_count, TAG_CUTOFF) * self.tp.entry_struct.size)
            entries = [TifEntry(*t) for t in self.tp.entry_struct.iter_unpack(b)]

            original = [i.tag for i in entries]
            ordered = sorted(original)
            if original != ordered:
                entries = try_fix_tag_out_of_order(self, f, pos, ifd_index, entry_count, entries)

            conflicts = {ordered[i] for i in range(len(ordered) - 1) if ordered[i] == ordered[i + 1]}
            for tag in conflicts:
                count = sum(1 for i in entries if i.tag == tag)
                entries, entry_count = try_fix_tag_conflict(self, f, pos, ifd_index, entry_count, entries, tag, count)

            pos = _read_struct(f, self.tp.link_struct, pos + self.tp.offset_ifd_link(entry_count))
        return True

############################################################################
# Functions.

def list_all():
    # Call each item method with a dummy value to add it to the result.
    check = TifCheck(None, None)
    for a in dir(check):
        if a.split('_')[0] in list(ItemCategory.__members__):
            getattr(check, a)('')
    # Return all items added, sorted by number.
    return sorted(check.items, key=lambda i: i.code)

def _friendly_file_size(n):
    """
    Format n as a whole number from 0 to 999 followed by one of: byte, bytes, KB, MB, GB, or TB.
    This floors 999_999 to 999 KB instead of rounding 999_500 to 1 MB for simplicity.
    """
    unit = int(0 if n < 1000 else min(math.log(n, 1000), 4))
    suffix = 'byte' if n == 1 else ['bytes', 'KB', 'MB', 'GB', 'TB'][unit]
    return f'{int(n / 1000 ** unit)} {suffix}'

def _creation_time(os_stat):
    # http://stackoverflow.com/a/39501288/1709587
    if platform.system() == 'Windows':
        return os_stat.st_ctime
    else:
        try:
            return os_stat.st_birthtime
        except AttributeError:
            return os_stat.st_mtime  # It does not exist on some platforms.

def _read_pos(f, pos, size):
    f.seek(pos)
    return f.read(size)

def _write_pos(f, pos, b):
    f.seek(pos)
    f.write(b)

def _read_struct(f, st, pos):
    b = _read_pos(f, pos, st.size)
    vals = st.unpack(b)
    return vals[0] if len(vals) == 1 else vals

def _write_struct(f, st, pos, *vals):
    b = st.pack(*vals)
    _write_pos(f, pos, b)

def _rewrite_entries(f, tp, pos, src_indexes):
    base_pos = pos + tp.count_struct.size
    step = tp.entry_struct.size
    buffer = bytearray(len(src_indexes) * step)
    for i in range(len(src_indexes)):
        buffer[i * step:i * step + step] = _read_pos(f, base_pos + src_indexes[i] * step, step)
    _write_pos(f, base_pos, buffer)

def try_fix_tag_out_of_order(check, f, pos, ifd_index, entry_count, entries):
    msg = f'IFD #{ifd_index} at {check.zfill(pos)}: Tags are out of order.'
    item = check.error_tag_out_of_order(msg)

    if item.code not in check.repairs.enabled:
        return entries

    if entry_count > TAG_CUTOFF:
        print(f'Repairs are not supported on IFDs with tag count greater than {TAG_CUTOFF}.')
        return entries

    reorder = sorted(enumerate(entries), key=lambda _, entry: entry.tag)
    _rewrite_entries(f, check.tp, pos, [i for i, _ in reorder])

    check.repairs.repaired.append(check.items.pop())
    return [tag for _, tag in reorder]

def try_fix_tag_conflict(check, f, pos, ifd_index, entry_count, entries, tag, count):
    msg = f'IFD #{ifd_index} at {check.zfill(pos)}: Tag {tag} has {count} copies in conflict.'
    item = check.error_tag_conflict(msg)

    if item.code not in check.repairs.enabled:
        return entries, entry_count

    if entry_count > TAG_CUTOFF:
        print(f'Repairs are not supported on IFDs with tag count greater than {TAG_CUTOFF}.')
        return entries, entry_count

    args = check.repairs.enabled[item.code] or '0'
    if len(args) == 1 and args[0].isdecimal() and int(args[0]) < count:
        selected = int(args[0])
    else:
        print(f'Ignored invalid parameter for tag conflict repair: \'{args}\'')
        selected = 0

    # Send the non-selected copies to the back without otherwise reordering.
    keep, reject = [], []
    for i in enumerate(entries):
        (keep if i[1].tag != tag else reject).append(i)
    assert len(reject) == count
    (keep.append(reject.pop(selected)) or keep).sort()
    _rewrite_entries(f, check.tp, pos, [i for i, _ in keep + reject])

    # Update the IFD's count and link fields.
    link = _read_struct(f, check.tp.link_struct, pos + check.tp.offset_ifd_link(entry_count))
    _write_struct(f, check.tp.count_struct, pos, len(keep))
    _write_struct(f, check.tp.link_struct, pos + check.tp.offset_ifd_link(len(keep)), link)

    check.repairs.repaired.append(check.items.pop())
    return [entry for _, entry in keep], len(keep)


############################################################################
# Entry point.

def main(argv=None):
    def usage(path=None):
        print("Usage:   python tifcheck.py [-list] [-repair[SPEC]] [PATH]")
        print("Example: python tifcheck.py -repair-203-204(0) \"example.tif\"")
        if path:
            print('Path does not exist: ' + path)
        return 1

    print(f'tifcheck {__version__}\n')
    try:
        # Parse parameters and do non-analysis tasks.
        argv = argv or sys.argv[1:]
        args = argv.copy()  # Preserve original argv for reporting.
        repairs = RepairList()
        for i in args:
            if i == '-list':
                print(json.dumps([i.metadict() for i in list_all()], indent=2))
                return 0
            if i.startswith('-repair'):
                if repairs.command:
                    return usage()
                repairs = RepairList(i)

        if repairs.command:
            args.remove(repairs.command)

        if len(args) == 0:
            root = tkinter.Tk()
            root.withdraw()
            args.append(tkinter.filedialog.askopenfilename())

        if len(args) != 1:
            return usage()

        path = args[0]
        if not os.path.exists(path):
            return usage(path)

        # Analyze and repair.
        t = time()
        result = TifCheck(path, repairs)
        t = time() - t

        # Output results.
        maxcat = max((i.category for i in result.items))
        bits = result.info_tiff_bits()
        order = result.info_tiff_order()
        
        _, info, note, warn, error, fail = \
            [[i.valdict() for i in result.items if i.category == cat] for cat in ItemCategory]

        temp = {
            'application': {
                'version': __version__,
                'parameters': argv,
                'time': datetime.now(UTC).strftime(ISO_8601_UTC),
            },
            'summary': {
                'type': f'{order.value} {bits.value}-bit TIFF' if bits and order else 'Not a TIFF',
                'size': _friendly_file_size(os.path.getsize(path)),
                'conformance': maxcat.name if maxcat > ItemCategory.info else 'ok',
                'repairs': len(repairs.repaired),
            }
        }
        report = json.dumps(temp, indent=2)[:-2]  # Strip '\n}'.
        temp = {
            'item counts': {
                'fail': len(fail),
                'error': len(error),
                'warn': len(warn),
                'note': len(note),
                'info': len(info),
            }
        }
        report += ',\n  ' + json.dumps(temp, indent=None)[1:-1]  # Strip outermost braces.
        temp = {
            'item sets': {
                'fail': list({i['code'] for i in fail}),
                'error': list({i['code'] for i in error}),
                'warn': list({i['code'] for i in warn}),
                'note': list({i['code'] for i in note}),
                'info': list({i['code'] for i in info}),
            }
        }
        report += ',\n  ' + json.dumps(temp, indent=None)[1:-1]  # Strip outermost braces.
        temp = {
            'items': {
                'fail': fail,
                'error': error,
                'warn': warn,
                'note': note,
                'info': info,
            }
        }
        if repairs.repaired:
            temp['repaired'] = [i.valdict() for i in repairs.repaired]
        report += ',' + json.dumps(temp, indent=2)[1:]  # Strip '{' but leave the '\n'.
        print(report)
        print(f'{t:.2f}s')
        return 0

    except Exception:
        print('Unexpected error.')
        print(traceback.format_exc())
        return -1

if __name__== "__main__":
    sys.exit(main())
