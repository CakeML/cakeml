Changes since release v3479:

## Source language and front‑end

The CakeML source language now supports open and let open (#1482).

The CakeML source language now supports variable-length word shifts (#1500).

Operations for reading or writing a single bit of a byte array have also been added to the source language (#1497).

The monadic translator now targets CakeML's byte arrays for arrays of type word8 (#1494).

The monadic translator also has new support for space-efficient bool arrays represented as byte arrays (#1498).

## Basis library

The shift and rotate functions `<<`, `>>`, `~>>` and `ror` in the `Word8` and
`Word64` modules now take the shift amount as a word of the same size instead
of an int, e.g. `Word8.<< : Word8.word -> Word8.word -> Word8.word` (#1500).
Programs that call these functions with an int amount need to be updated.

There are new primitives for reading and updating a bit of a byte array (#1502):
```
Word8Array.subBit: byte_array -> int -> bool
Word8Array.updateBit: byte_array -> int -> bool -> unit
```
The supplied index `i` is used as follows: `i div 8` is the read/updated byte,
and, in that byte, bit `i mod 8` is read/updated.

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

The compiler handles dynamic installation of new code in new way (#1487). This
paves the way for supporting Eval on Arm.

Smallnums and nullary constructors have improved runtime representation (#1487).
This means, e.g., that smallnums can use 63 bits on 64-bit architectures.

## Pancake

Queryable feature tags (#1470).

## Candle

## Examples

The PB checker has been reorganized with minor fixes, and also supports solutions cubes (#1496).

The CNF checker(s) have various improvements, especially the RUP algorithm has been updated. Additionally, there is now a centralized and cleaned up basis FFI C file for the checkers (#1495).

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
