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

### List

`List.intersperse`,
which inserts a given element between every consecutive pair of elements in a list,
has been added to basis.

### Char

`isLower`, `isUpper`, `isDigit`, `isAlpha` and `isAlphaNum` have been added to the Char module.

### String

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

### Word8Array

There are new primitives for reading and updating a bit of a byte array (#1502):
```
Word8Array.subBit: byte_array -> int -> bool
Word8Array.updateBit: byte_array -> int -> bool -> unit
```
The supplied index `i` is used as follows: `i div 8` is the read/updated byte,
and, in that byte, bit `i mod 8` is read/updated.

## Compiler backend and runtime

The compiler handles dynamic installation of new code in new way (#1487). This
paves the way for supporting Eval on Arm.

Smallnums and nullary constructors have improved runtime representation (#1487).
This means, e.g., that smallnums can use 63 bits on 64-bit architectures.

The Eval/Install mechanism has been updated (#1507) so that it does a memcpy
instead of a byte-by-byte write. The new basis_ffi.c now has a function called
cml_install implementing this; the whole C file has also been cleaned up. This
is NOT backwards compatible. On the flip side, the REPL now runs on ARM8 + Mac
combinations which have W^X permissions.

The exported assembly marks the stack as non-executable on ELF platforms, so
`cake` and the programs it compiles no longer get an executable stack from the
linker (#1517).

The backend now supports IMul and IDiv instructions and optimizes to the
(#1533). Some further cleanup of the asm ops might be expected in the future.

The global dead code elimination pass has moved from flatLang to source,
specifically, `flat_elim` has been replaced by `source_dce` (#1508).

The compiler backend now attaches a bit of metadata to every function (#1535).
This is completely internal to the compiler.

## Pancake

Queryable feature tags (#1470).

The initial version of the decompiler-into-itree of Pancake---DecompIt (#1492).

## Candle

## Examples

The PB checker has been reorganized with minor fixes, and also supports solutions cubes (#1496).
Its backing representation and corresponding algorithms have been optimized heavily (#1528).

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

This replaces the old association-list translation of finite maps from the
`Alist` module in `ListProg`, which has been disabled. Finite maps can now
only be translated at key types for which `add_fmap_for_cmp` has been called,
so definitions that are polymorphic in the key type must be instantiated
before translation, e.g. with `INST_TYPE [alpha |-> “:mlstring”]`, and `|++`
must be rewritten into `FOLDL` over `|+`. The bootstrap translation calls
`add_fmap_for_cmp` for `mlstring`, `int` and `num` keys in `decProg`.

### simp additions

The following simps have been added:

#### fsFFIProps

```
Theorem get_mode_fsupdate[simp]:
  get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd
```

## Miscellaneous

Combined fix for some small issues (PR #1530 fixing #1313, #1373, #1449, #1480, #1503).

Combined fix for some small issues (PR #1536 fixing #1408, #1171, #1104).
