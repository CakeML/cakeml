This directory contains files that create an unverified bootstrap of
the 64-bit compiler.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[extract_code.cml](extract_code.cml):
A CakeML program that extracts the indented code snippets from a
markdown file. This is used for checking the code in how-to.md.

[x64SexprScript.sml](x64SexprScript.sml):
Produces an sexp print-out of the bootstrap translated compiler
definition for the 64-bit version of the compiler.
