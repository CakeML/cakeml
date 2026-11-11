Changes since release v3671:

## Source language and front‑end

The integer division and modulus primitives now take a rounding mode (#1583). Instead of `Div`, one now gets to choose between `Div RoundDown` and `Div TowardsZero`. Same for `Mod`. These are ignored for floats.

## Basis library

### Int

`Int.quot` and `Int.rem` have been added (#1583). They implement integer division and modulus rounding towards zero. Previously existing `Int.div` and `Int.mod` round down.

## Compiler backend and runtime

## Pancake

The Pancake compiler is now a standalone `pancake` executable, replacing `cake --pancake` (#1589). This splits the bootstrap translation into one CakeML path and one Pancake path. They share all translations up to from_wordProg. Command-line parsing helpers are shared between the two compilers.

We distribute native Pancake builds as self-contained archives with assembly (x64, Arm8 and RISC-V), FFI source and a Makefile for building the executable.

## Candle

## Examples

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
