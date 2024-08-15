This directory contains scripts that compile the CakeML compiler
inside the logic to produce the verified machine code version of the
32-bit compiler.

[ag32BootstrapScript.sml](ag32BootstrapScript.sml):
Evaluate the final part of the 32-bit version of the compiler
into machine code for ag32, i.e. the Silver ISA.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[proofs](proofs):
This directory contains the end-to-end correctness theorem for the
32-bit version of the CakeML compiler.
