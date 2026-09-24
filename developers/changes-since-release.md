Changes since release v3479:

## Source language and front‑end

The CakeML source language now supports open and let open (#1482).

Operations for reading or writing a single bit of a byte array have also been added to the source language (#1497).

## Basis library

## Compiler backend and runtime

The compiler handles dynamic installation of new code in new way (#1487). This
paves the way for supporting Eval on Arm.

Smallnums and nullary constructors have improved runtime representation (#1487).
This means, e.g., that smallnums can use 63 bits on 64-bit architectures.

## Pancake

Queryable feature tags (#1470).

## Candle

## Examples

The PB checker has been reorganized with minor fixes.

The RUP algorithm has been updated.

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
