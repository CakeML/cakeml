Changes since release v3400:

## Source language and front‑end

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

### fsFFI

`openFile_truncate` has been updated to create files if they are not present,
better reflecting the implementation of `ffiopen_out` in `basis_ffi.c`.

### fsFFIProps

`get_mode_fsupdate` has been added and included as a simp:
```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

## Miscellaneous 
