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

## Build infrastructure

Added `buildInfoLib.sml`, which can be used to get build information
(version, commit hashes, commit dates, git tags) for CakeML, HOL4 and Poly/ML.
Changes in the build information cause files that depend on it to become out-of-date.
This behavior can be overridden by setting the environment variable
`CML_FREEZE_BUILD_INFO`.

## Proof engineering and tooling

## Miscellaneous

The format for printing build/version info for binaries has been changed.
Output of `cake --version`:
```
The CakeML compiler

Version details:
Commit date: 2026-10-26 03:01:43 UTC

CakeML: 239aca184c1321d6f5fcfb8b923b91af20558d2f
HOL4:   652d1f0aad5cd537ed1e5d470ba3444e70ba470e (trindemossen-2-v9)
PolyML: Poly/ML 5.9.2 Release
```
