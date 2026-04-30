Changes since release v3304:

## Source language and front‑end

## Basis library

`TextIO.inputAllFrom` has been added to the basis library. The CF theorem for `TextIO.inputAll` has been corrected (#1375, #1366).

## Compiler backend and runtime

FlatLang has been simplified slightly (#1380).

## Pancake

### Garbage collector always disabled

The Pancake compiler now unconditionally compiles with GC set to `none`; any `--gc=...` flag passed alongside `--pancake` is silently ignored. This removes the unused GC runtime that Zhewen Shen's BSc thesis (p. 35) noted was being linked into every Pancake binary.

## Candle

## Examples

## Build infrastructure

## Proof engineering and tooling

## Miscellaneous
