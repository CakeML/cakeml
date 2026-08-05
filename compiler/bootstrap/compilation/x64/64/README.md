This directory contains scripts that compile the CakeML compiler
inside the logic to produce the verified machine code version of the
64-bit compiler.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[hello.cml](hello.cml):
A simple hello world program in CakeML

[proofs](proofs):
This directory contains the end-to-end correctness theorem for the
64-bit version of the CakeML compiler.

[repl_boot.cml](repl_boot.cml):
This file gives the CakeML REPL multi-line input and file loading
capabilities.

[sexprBootstrap32Script.sml](sexprBootstrap32Script.sml):
Produces an sexp print-out of the bootstrap translated compiler
definition for the 32-bit version of the compiler.

[sexprBootstrap64Script.sml](sexprBootstrap64Script.sml):
Produces an sexp print-out of the bootstrap translated compiler
definition for the 64-bit version of the compiler.

[test-hello.cml](test-hello.cml):
A hello world program used for testing that the bootstrapped
compiler was built successfully.

[x64BootstrapScript.sml](x64BootstrapScript.sml):
Evaluate the 64-bit version of the compiler into x64 machine code.
