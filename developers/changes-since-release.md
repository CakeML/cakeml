Changes since release v3400:

## Source language and front‑end

## Basis library

### TextIO

`TextIO.output`'s behavior is now linear in the size of the string
(previously quadratic -- oops!). This should allow users to output large strings
(as in: much larger than 2kB) without the program hanging (#1425).

## Compiler backend and runtime

### BVI

BVI now supports multi-arg calls/returns (with a separate constructor).

## Pancake

## Candle

## Examples

## Build infrastructure

## Proof engineering and tooling

### simp additions

The following simps have been added:

#### fsFFIProps

```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

## Miscellaneous 

inferScript.sml now uses the state-exception monad defined in
ml_monadBase instead of a locally defined version of it.

Some files have been refactored to use `monadsyntax.temp_enable_monad`
instead of manual overloads of constants such as `monad_bind`.

Some files have been refactored to use `st_ex_ignore_bind` instead of
a locally defined version using `st_ex_bind`.