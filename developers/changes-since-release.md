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

There are new primitives for reading and updating a bit of a byte array (#1502):
```
Word8Array.subBit: byte_array -> int -> bool
Word8Array.updateBit: byte_array -> int -> bool -> unit
```
The supplied index `i` is used as follows: `i div 8` is the read/updated byte,
and, in that byte, bit `i mod 8` is read/updated.

## Compiler backend and runtime

The compiler handles dynamic installation of new code in new way (#1487). This
paves the way for supporting Eval on Arm.

Smallnums and nullary constructors have improved runtime representation (#1487).
This means, e.g., that smallnums can use 63 bits on 64-bit architectures.

The exported assembly marks the stack as non-executable on ELF platforms, so
`cake` and the programs it compiles no longer get an executable stack from the
linker (#1517).

## Pancake

Queryable feature tags (#1470).

## Candle

## Examples

The PB checker has been reorganized with minor fixes, and also supports solutions cubes (#1496).

The CNF checker(s) have various improvements, especially the RUP algorithm has been updated. Additionally, there is now a centralized and cleaned up basis FFI C file for the checkers (#1495).

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
