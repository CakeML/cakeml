Changes since release v3400:

## Source language and front‑end

## Parser

The S-expression parser has been changed to use the simpler and more efficient mlsexp parser
instead of the PEG-based parser from HOL (simpleSexp) (#1365).

## Basis library

### TextIO

`TextIO.output`'s behavior is now linear in the size of the string
(previously quadratic -- oops!). This should allow users to output large strings
(as in: much larger than 2kB) without the program hanging (#1425).

## Compiler backend and runtime

### BVI

BVI now supports multi-arg calls/returns (with a separate constructor).

## Pancake

## Candle

## Examples

## Build infrastructure

## Proof engineering and tooling

### simp additions

The following simps have been added:

#### fsFFIProps

```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

## Miscellaneous 
