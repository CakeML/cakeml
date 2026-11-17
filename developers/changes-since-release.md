Changes since release v3671:

## Source language and front‑end

The integer division and modulus primitives now take a rounding mode (#1583). Instead of `Div`, one now gets to choose between `Div RoundDown` and `Div TowardsZero`. Same for `Mod`. These are ignored for floats.

The semantics of floating-point operations in the source has been made more well defined in case of NaN results: all floating-point operations resulting in a NaN now return a specific NaN, the all-ones NaN (-1w:word64).

## Basis library

### Int

`Int.quot` and `Int.rem` have been added (#1583). They implement integer division and modulus rounding towards zero. Previously existing `Int.div` and `Int.mod` round down.

## Compiler backend and runtime

The CakeML compiler now supports compilation of floating-point operartions also for the Arm8 target (#1596).

## Pancake

The Pancake compiler is now a standalone `pancake` executable, replacing `cake --pancake` (#1589). This splits the bootstrap translation into one CakeML path and one Pancake path. They share all translations up to from_wordProg. Command-line parsing helpers are shared between the two compilers.

We distribute native Pancake builds as self-contained archives with assembly (x64, Arm8 and RISC-V), FFI source and a Makefile for building the executable.

## Candle

## Examples

A new LSR checker has been added, with some surrounding (beneficial) fallout cleanups in cnf (#1588).

A PB checker has gained substantial optimization passes, with some cleanup fallout to cnf/ (#1595).

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
