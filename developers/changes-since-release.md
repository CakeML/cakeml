Changes since release v3671:

## Source language and front‑end

The integer division and modulus primitives now take a rounding mode. Instead of `Div`, one now gets to choose between `Div RoundDown` and `Div TowardsZero`. Same for `Mod`. These are ignored for floats.

## Basis library

### Int

`Int.quot` and `Int.rem` have been added. They implement integer division and modulus rounding towards zero. Previously existing `Int.div` and `Int.mod` round down.

## Compiler backend and runtime

## Pancake

## Candle

## Examples

A new LSR checker has been added, with some surrounding (beneficial) fallout cleanups in cnf (#1588).

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
