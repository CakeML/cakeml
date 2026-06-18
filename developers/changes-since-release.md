Changes since release v3304:

## Source language and front‑end

`pat_bindings` and `pats_bindings` no longer take an accumulator argument (progress on #662).

A first-order version of CakeML's PEG parser now exists (#1407).

## Basis library

`TextIO.inputAllFrom` has been added to the basis library. The CF theorem for `TextIO.inputAll` has been corrected (#1375, #1366).

## Compiler backend and runtime

### perf-record --call-graph support (x64-only)

Passing `--perf_callgraph=T` to the CakeML compiler (x64-only) generates an unverified binary that can be profiled with `perf record --call-graph fp`.
The in-logic compiler uses the default config in `x64_config`.
Thus, to profile binaries such as checkers, the Dafny compiler, the Scheme compiler, etc., it is necessary to set `perf_calls:=T` in the configuration ultimately used by the compiler.

### FlatLang

FlatLang has been simplified slightly (#1380).

### DataLang

dataLang now supports multi-arg returns (#1416)

dataLang now avoid storing args in the cutsets unnecessarily (#1403)

### WordLang

word_cse has been reworked to match more aggresively (#1410)

word_copy pass now additionally correctly propagates store-reg equality (#1385).

WordLang now supports Loop, Break, Continue (#1389).

## Pancake

### __add_with_carry__ now available

It is now possible to use `__add_with_carry__(left, right, carry_in)`
in user code, which is compiled to wordLang's `AddCarry`.
Syntax example:

    fun {1,1} f() {
      var a = 1;
      var b = 2;
      var c = 0;
      var {1,1} r = __add_with_carry__(a, b, c);
      r = __add_with_carry__(a, b, c);
      return r;
    }

Permitted positions for `__add_with_carry__` are declaration RHS and assignment RHS;
standalone, handler-attached, and tail-return calls are not supported.

### LoopLang

LoopLang now supports multi-arg returns (#1391) and arbitrary depth Break/Continue (#1395).

LoopLang now compiles to WordLang Loops instead of tail calls, i.e., the old loop_remove pass is removed (#1391).

### Garbage collector always disabled

The Pancake compiler now unconditionally compiles with GC set to `none`; any `--gc=...` flag passed alongside `--pancake` is silently ignored. This removes the unused GC runtime that Zhewen Shen's BSc thesis (p. 35) noted was being linked into every Pancake binary.

## Candle

By optimizing the kernel Candle, we were able to achieve a 1.88x speedup on `make_complex.ml` (previously 56m49.502s, now 30m10.587s) (#1415).

A model of [Little Theories](https://web.cs.wpi.edu/~guttman/pubs/cade_little-theories.pdf) (Farmer et al., 1992) has been added to Candle (#1405). 

## Examples

A new example for distributed SAT proof checking (#1384)

The FloVer example -- a Certificate Checker for Roundoff Error Bounds -- has been repaired and added back into the build-sequence (#1297, #1404).

## Build infrastructure

`examples/compilation/{ag32,x64}` now make use of HOL's `LOCAL_PARALLELISM_LIMIT` instead of `CLINE_OPTIONS = -j1`, limiting parallelism only in that directory and not others (#1414).

## Proof engineering and tooling

### mlstring
- `str` has been renamed to `chr_to_str`, freeing up `str` to be used for parameter names, for example. (#1307, #1372)
- Added `toString` overload for `chr_to_str` (#1307, #1372).
- Fused strlit and implode (#491, #1376).
  - Incompatibilities
    - `implode_def` has been removed, so any references to it in tactics and automation need to be removed in user files.
    - A few proofs may break. In the cakeml repo the required fixes were relatively straightforward.
  - Deprecations
    - `strlit` has been added as an inferior overload for backwards compatibility, but may be removed in the future. It is recommended to use `implode` instead.
    - `strlit_tm`, `mk_strlit`, `dest_strlit` and `is_strlit` are still available but may be removed in the future. It is recommended to use `implode_tm`, `mk_implode`, `dest_implode` and `is_implode` instead.

## Miscellaneous
