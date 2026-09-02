Changes since release v3479:

## Source language and front‑end

## Basis library

## Compiler backend and runtime

## Pancake

Queryable feature tags (#1470).

## Candle

## Examples

The PB checker has been reorganized with minor fixes.

The RUP algorithm has been updated. 

## Build infrastructure

## Proof engineering and tooling

### fsFFI

`openFile_truncate` has been updated to create files if they are not present,
better reflecting the implementation of `ffiopen_out` in `basis_ffi.c`.

`get_file_content` has been renamed to `get_fd_content` to better reflect
its definition and to free up the name for a different definition.

`get_file_content` now defines a function that returns the contents of a file
(not a file descriptor).

### fsFFIProps

`get_mode_fsupdate` has been added and included as a simp:
```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

### TextIOProof

`raw_closeIn_STDIO_spec` and `closeOut_STDIO_spec` assumptions have been weakened.

## Miscellaneous
