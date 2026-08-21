Changes since release v3400:

## Source language and front‑end

No changes in source language or front-end since last release.

## Basis library

### List

`List.intersperse`,
which inserts a given element between every consecutive pair of elements in a list,
has been added to basis.

### Char

`isLower`, `isUpper`, `isDigit`, `isAlpha` and `isAlphaNum` have been added to the Char module.

### String

`String.concatWith` has been reimplemented using `concat` and `intersperse`,
avoiding potentially quadratic behavior due to left-associative concatenations (#1425).

### TextIO

`TextIO.output`'s behavior is now linear in the size of the string
(previously quadratic -- oops!). This should allow users to output large strings
(as in: much larger than 2kB) without the program hanging (#1425).

### FFI oracle

The `basis_ffi_oracle` has been redfined to have an extra parameter
meant to model "additional underspecified FFIs". (#1446)

## Compiler backend and runtime

### Compilation of pattern matching

The exhaustiveness checker for pattern-match rows has been replaced by a much better one:
the new function implements the exhaustiveness case of Maranget's usefulness algorithm
adapted to sibling annotations in place of a typing environment.

### BVI

BVI now supports multi-arg calls/returns (with a separate constructor).

A new pass, `bvi_tmc`, performs tail recursion modulo cons, turning
self-recursive calls under a constructor into tail calls. The compiler
pass is Ry Wiese's MSc thesis work.

Two new compiler flags/configs `--tmc=true/false` and `--tailrec=true/false`,
both default to true. They can be used to turn of `bvi_tmc` and `bvi_tailrec`.

### Thunks

The `data_to_word` invariants now allow thunks to be inlined (#1440).
The intention is that the GC will, in the future, inline evalated thunks.

### targetSem

targetSem is now more lax about the FFI/clear-cache havocs (#1458)

## Pancake

A parser bug related to field accesses has been fixed (#1438).

Exeception syntax has been improved (#1450)

Variable length shifts are now supported (#1460).

## Candle

### Parser

The parser now supports multi-line string literals.

### Soundness

The top-level soundness theorem is now more precise about the FFI (#1446).

Consistency is proved for the actual Candle context (#1445).

## Examples

The CakePB example now has a verified CP encoder frontend (#1436).

The distrup checker has minor fixes (#1441).

## Build infrastructure

## Proof engineering and tooling

### New function for proving whole program correctness theorems

The `basis_ffiLib.whole_prog_thm`, which is used to prove `semantics`
results, has been deleted and a new `basis_ffiLib.prove_sem_thm` is to
be used instead from now on. The old one used to be slow and clunky to
use; the new one runs within a few seconds at each call site.

### simp additions

The following simps have been added:

#### fsFFIProps

```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

### Finite map translation

The translator can now deal nicely with finite maps (#1442)

## Miscellaneous

`CONCAT_WITH` (misc) and `concatWith_CONCAT_WITH` (mlstring)
have been removed due to being unused.

inferScript.sml now uses the state-exception monad defined in
ml_monadBase instead of a locally defined version of it.

Some files have been refactored to use `monadsyntax.temp_enable_monad`
instead of manual overloads of constants such as `monad_bind`.

Some files have been refactored to use `st_ex_ignore_bind` instead of
a locally defined version using `st_ex_bind`.
