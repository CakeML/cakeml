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

### String

`String.Fast.compare` has been added.
Like the other operations in the `String.Fast` module, it orders strings by
length first and only compares contents when the lengths are equal, which is faster.

### Map

`Map.diff` has been added to basis. `Map.diff m1 m2` removes from `m1` every
key that occurs in `m2`. The inputs can have different value types.

### TextIO

`TextIO.inputAllFrom` has been added to basis. It reads all input from stdin
(on `None`) or from a named file (on `Some fname`), closing the stream
afterwards, and returns `None` if the file cannot be opened.

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

### Translation of HOL finite maps

The new `MapProgLib.add_fmap_for_cmp` teaches the translator to represent
HOL finite maps (`:'a |-> 'b`) by `mlmap` balanced binary trees. Given a
`TotOrd cmp` theorem for an already translated comparison `cmp`, it
registers translations of the following:
 - `FEMPTY`
 - `FLOOKUP`
 - `fmap_update` (a wrapper around `_ |+ (_, _)`)
 - `$\\`
 - `FUNION`
 - `fdiff_fdom` (a wrapper around `FDIFF _ (FDOM _)`)

## Miscellaneous
