This directory contains scripts that compile the fused CakeML compiler
inside the logic to produce verified ag32 machine code.

[ag32BootstrapScript.sml](ag32BootstrapScript.sml):
Evaluate the AG32 batch entry point of the fused compiler
into machine code for ag32, i.e. the Silver ISA.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[proofs](proofs):
This directory contains the end-to-end correctness theorem for the
fused CakeML compiler compiled to ag32 machine code.
