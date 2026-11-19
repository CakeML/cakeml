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

A new LSR checker has been added, with some surrounding (beneficial) fallout cleanups in cnf (#1588).

A PB checker has gained substantial optimization passes, with some cleanup fallout to cnf/ (#1595).

## Build infrastructure

## Proof engineering and tooling

The translator now accepts `if ptr_eq x1 y1 /\ ptr_eq x2 y2 /\ ... then t1 else t2`, i.e. conjunctions of pointer-equality tests (with an optional boolean suffix) as the guard. The side condition that both branches agree is only needed under the whole guard (#1603).

The monadic translator has a new opt-in library, `ml_monad_oracleLib`, for pointer equality (`Mptr_eq`) in global-state monads. A logical oracle field in the user's state models the source `PtrEq` oracle (#1603).

CF now supports `PtrEq` (#1603).

## Miscellaneous
