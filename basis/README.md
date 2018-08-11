Contains the beginnings of a standard basis library for CakeML,
similar to the standard basis library of SML.

[basis.sml](basis.sml):
Convenience structure that re-exports all the libraries and theories of the
CakeML basis library.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[dependency-order](dependency-order):
This file records the current, linear dependency order between the
translation/CF theories making up the basis library verification.

[pure](pure):
HOL definitions of the pure functions used in the CakeML basis.
