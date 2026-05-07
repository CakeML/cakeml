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

### mlstring
- HOL: `str` has been renamed to `chr_to_str`, freeing up `str` to be used for parameter names, for example. (#1307, #1372)
- HOL: Added `toString` overload for `chr_to_str` (#1307, #1372)
- HOL: Fuse strlit and implode (#491, #1376)
  - Incompatibilities
    - `implode_def` has been removed, so any references to it in tactics and automation need to be removed in user files.
    - A few proofs may break. In the cakeml repo the required fixes were relatively straightforward.
  - Deprecations
    - `strlit` has been added as an inferior overload for backwards compatibility, but may be removed in the future. It is recommended to use `implode` instead.
    - `strlit_tm`, `mk_strlit`, `dest_strlit` and `is_strlit` are still available but may be removed in the future. It is recommended to use `implode_tm`, `mk_implode`, `dest_implode` and `is_implode` instead.

## Miscellaneous
