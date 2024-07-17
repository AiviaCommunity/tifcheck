
# tifcheck

Validate and repair TIFF files.

This standalone Python 3.9 script produces a JSON formatted report listing
items that describe conformance to TIFF Version 6, BigTIFF, and related
formats, categorized by severity.

| Category | Description                                              |
|----------|:---------------------------------------------------------|
| Fail     | An unrecoverable condition.                              |
| Error    | A condition that is recoverable but disallowed.          |
| Warn     | A condition that is allowed but not expected.            |
| Note     | A condition that some implementations might not support. |
| Info     | Supplementary information.                               |

The set of conditions analyzed is not inteded to be exhaustive.  It will
grow over time as resources allow.  Use the list command to output a report
with the metadata of existing items.

The repair command attempts to rewrite the input file in place, in order to
clear selected item codes.  Repairs include:

| Code | Name             |
|------|:-----------------|
| 203  | Tag out of order |
| 204  | Tag conflict     |

The current design of this script prioritizes minimal assumptions about
input, minimal dependencies, and low memory use.  It does not prioritize
speed optimization or integrity checking of i/o.

## Usage

```
python tifcheck [-list] [-repair[SPEC]] [PATH]
```

## Example

```
python tifcheck -repair-203-204(0) "example.tif"
```

