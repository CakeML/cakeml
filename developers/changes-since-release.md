Changes since release v3479:

## Source language and front‑end

The CakeML source language now supports open and let open (#1482).

The CakeML source language now supports variable-length word shifts (#1500).

Operations for reading or writing a single bit of a byte array have also been added to the source language (#1497).

The monadic translator now targets CakeML's byte arrays for arrays of type word8 (#1494).

The monadic translator also has new support for space-efficient bool arrays represented as byte arrays (#1498).

## Basis library

The shift and rotate functions `<<`, `>>`, `~>>` and `ror` in the `Word8` and
`Word64` modules now take the shift amount as a word of the same size instead
of an int, e.g. `Word8.<< : Word8.word -> Word8.word -> Word8.word` (#1500).
Programs that call these functions with an int amount need to be updated.

## Compiler backend and runtime

The compiler handles dynamic installation of new code in new way (#1487). This
paves the way for supporting Eval on Arm.

Smallnums and nullary constructors have improved runtime representation (#1487).
This means, e.g., that smallnums can use 63 bits on 64-bit architectures.

## Pancake

Queryable feature tags (#1470).

## Candle

## Examples

The PB checker has been reorganized with minor fixes, and also supports solutions cubes (#1496).

The CNF checker(s) have various improvements, especially the RUP algorithm has been updated. Additionally, there is now a centralized and cleaned up basis FFI C file for the checkers (#1495).

## Build infrastructure

## Proof engineering and tooling

### fsFFI

`openFile_truncate` has been updated to create files if they are not present,
better reflecting the implementation of `ffiopen_out` in `basis_ffi.c`.

`get_file_content` has been renamed to `get_fd_content` to better reflect
its definition.

`file_content`, which returns the contents of a file by name (not a file
descriptor), is now defined here instead of in `TextIOProof`.

### fsFFIProps

`get_mode_fsupdate` has been added and included as a simp:
```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

### TextIOProof

`raw_closeIn_STDIO_spec` and `closeOut_STDIO_spec` assumptions have been weakened.

## Miscellaneous
