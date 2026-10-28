Changes since release v3479:

## Source language and front‑end

The CakeML source language now supports open and let open (#1482).

The CakeML source language now supports variable-length word shifts (#1500).

Operations for reading or writing a single bit of a byte array have also been added to the source language (#1497).

The monadic translator now targets CakeML's byte arrays for arrays of type word8 (#1494).

The monadic translator also has new support for space-efficient bool arrays represented as byte arrays (#1498).

The compiler now supports unsafe strsub (#1538).

New primitives `UnsafeIndexArith` and `UnsafeIndexTest` provide smallnum arithmetic and comparisons without runtime bignum checks (#1551). The smallnumness obligations are met by a witness (index a vector, array, byte array or string) or by proving the numbers are smallnums even on 32-bit architectures.

The S-expression representation of the AST was vastly simplified and **is not backwards-compatible**.
It now follows the AST as close as possible.
For example, `val (a, b) = (~1, 2)` is represented as
```
  ((Dlet NoLocs
     (Pcon NONE ((Pvar a) (Pvar b)))
     (Con NONE ((Lit (IntLit ~1)) (Lit (IntLit 2))))))
```

## Basis library

The shift and rotate functions `<<`, `>>`, `~>>` and `ror` in the `Word8` and
`Word64` modules now take the shift amount as a word of the same size instead
of an int, e.g. `Word8.<< : Word8.word -> Word8.word -> Word8.word` (#1500).
Programs that call these functions with an int amount need to be updated.

The modules Ast and AstSexp have been added.
These modules provide the CakeML AST and functions to convert an ast
to/from S-expression.

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

### SocketIO

A new module for socket I/O, `SocketIO`, has been added to basis.
`SocketIO` currently supports Unix domain sockets and Linux raw sockets.
Use of the module is demonstrated by two new examples.
CF specs and proofs are still TODO, for now.

### TextIO

`TextIO.output`'s behavior is now linear in the size of the string
(previously quadratic -- oops!). This should allow users to output large strings
(as in: much larger than 2kB) without the program hanging (#1425).

`TextIO.outputFile` has been added to basis.
It writes a string to a file, taking care of opening and closing.
It comes with a CF spec.

`TextIO.openOut` now has CF specs: `openOut_IOFS_spec` and `openOut_STDIO_spec`.

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

A new constant lifting pass has been added as a source-to-source pass to the
compiler backend (#1542).

The compiler backend now attaches a bit of metadata to every function (#1535).
This is completely internal to the compiler. Debug names for functions now come
from metadata rather than a separate mapping (#1539).

## Pancake

Queryable feature tags (#1470).

The initial version of the decompiler-into-itree of Pancake---DecompIt (#1492).

## Candle

The Candle parser has been moved out of HOL into user code (#1537).
One user-facing change is that CakeML itself in EVAL mode now starts with a
larger data buffer to accommodate the user code (Candle already patches to start
with an even larger one). Another is that a `(*CML ...*)` block in Candle input
is now only accepted where a phrase begins.

## Examples

The PB checker has been reorganized with minor fixes, and also supports solutions cubes (#1496).
Its backing representation and corresponding algorithms have been optimized heavily (#1528).

The CNF checker(s) have various improvements, especially the RUP algorithm has been updated. Additionally, there is now a centralized and cleaned up basis FFI C file for the checkers (#1495).

A further improvement to the CNF checker(s), API, format-wise, algorithmically, and using the new unsafe ops (#1557).

The new `socketEchoProg` contains a simple echo server meant for testing the Unix domain sockets from `SocketIO`.

Similarly, `rawBridgeProg` showcases `SocketIO`'s raw sockets.

The new unsafe index arithmetic primitives (`UnsafeIndexArith` and `UnsafeIndexTest`) are demoed in `examples/unsafe_arith_exampleScript.sml` (#1551).

The new `examples/hwmcc_checker` contains caketaiger, a verified checker for the
certificates used in the Hardware Model Checking Competition. It comes with a
formalization of And-Inverter Graphs and a parser for the binary AIGER 1.9 format.

## Build infrastructure

Added `buildInfoLib.sml`, which can be used to get build information
(version, commit hashes, commit dates, git tags) for CakeML, HOL4 and Poly/ML.
Changes in the build information cause files that depend on it to become out-of-date.
This behavior can be overridden by setting the environment variable
`CML_FREEZE_BUILD_INFO`.

## Proof engineering and tooling

Unused definitions and theorems were removed from misc. (#1499, #1489)

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

### fsFFI

`openFile_truncate` has been updated to create files if they are not present,
better reflecting the implementation of `ffiopen_out` in `basis_ffi.c`.

`ffi_open_out` no longer requires the new file descriptor to be at most 255,
in line with `ffi_open_in`.

`get_file_content` has been renamed to `get_fd_content` to better reflect
its definition. Theorems mentioning it have been renamed accordingly, e.g.
`stdin_get_file_content` is now `stdin_get_fd_content`.

`file_content`, which returns the contents of a file by name (not a file
descriptor), is now defined here instead of in `TextIOProof`.

### fsFFIProps

The following simps (among others) have been added: `get_mode_fsupdate`,
`NOT_MEM_nextFD`, `consistentFS_AFUPDKEY`, `liveFS_AFUPDKEY` and
`wfFS_updated_by`.

The simp `consistentFS_with_numchars` is now an equivalence:
`consistentFS (fs with numchars := ll) ⇔ consistentFS fs`.

### TextIOProof

`raw_closeIn_STDIO_spec` and `closeOut_STDIO_spec` no longer assume
`fd >= 3 ∧ fd <= fs.maxFD`.

### mlstringSyntax

`mlstring_from_file` has been added. It reads a file into an `mlstring` term.

## Miscellaneous

Combined fix for some small issues (PR #1530 fixing #1313, #1373, #1449, #1480, #1503).

Combined fix for some small issues (PR #1536 fixing #1408, #1171, #1104).

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
