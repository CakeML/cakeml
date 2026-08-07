Changes since release v3400:

## Source language and front‑end

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

`String.Fast.compare` has been added.
Like the other operations in the `String.Fast` module, it orders strings by
length first and only compares contents when the lengths are equal, which is faster.

### Map

`Map.diff` has been added to basis. `Map.diff m1 m2` removes from `m1` every
key that occurs in `m2`. The inputs can have different value types.

### TextIO

`TextIO.output`'s behavior is now linear in the size of the string
(previously quadratic -- oops!). This should allow users to output large strings
(as in: much larger than 2kB) without the program hanging (#1425).

`TextIO.inputAllFrom` has been added to basis. It reads all input from stdin
(on `None`) or from a named file (on `Some fname`), closing the stream
afterwards, and returns `None` if the file cannot be opened.

## Compiler backend and runtime

### BVI

BVI now supports multi-arg calls/returns (with a separate constructor).

## Pancake

## Candle

### Parser

The parser now supports multi-line string literals.

## Examples

The CakePB example now has a verified CP encoder frontend.

## Build infrastructure

## Proof engineering and tooling

### New function for proving whole program correctness theorems

The `basis_ffiLib.whole_prog_thm`, which is used to prove `semantics`
results, has been deleted and a new `basis_ffiLib.prove_sem_thm` is to
be used instead from now on. The old one used to be slow and clunky to
use; the new one runs within a few seconds at each call site.

### Translation of HOL finite maps

The new `MapProgLib.add_fmap_for_cmp` teaches the translator to represent
HOL finite maps (`:'a |-> 'b`) by `mlmap` balanced binary trees. Given a
`TotOrd cmp` theorem for an already translated comparison `cmp`, it
registers translations of the following:
 - `FEMPTY`
 - `FLOOKUP`
 - `fmap_update` (a wrapper around `_ |+ (_, _)`)
 - `$\\`
 - `FUNION`
 - `fdiff_fdom` (a wrapper around `FDIFF _ (FDOM _)`)

### simp additions

The following simps have been added:

#### fsFFIProps

```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

## Miscellaneous

`CONCAT_WITH` (misc) and `concatWith_CONCAT_WITH` (mlstring)
have been removed due to being unused.

inferScript.sml now uses the state-exception monad defined in
ml_monadBase instead of a locally defined version of it.

Some files have been refactored to use `monadsyntax.temp_enable_monad`
instead of manual overloads of constants such as `monad_bind`.

Some files have been refactored to use `st_ex_ignore_bind` instead of
a locally defined version using `st_ex_bind`.
