Native x64 Pancake compiler.

Unpack `pancake-x64.tar.gz` and run `make pancake` on x64 Linux.
The archive includes assembly, FFI source, a standalone Makefile and this
README.
Set `CC` to use a cross compiler. Run `./pancake --help` for compiler options.

In a CakeML checkout, run `Holmake pancake-x64.tar.gz` to build the archive.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[pancake_x64BootstrapScript.sml](pancake_x64BootstrapScript.sml):
Evaluate the Pancake compiler into x64 machine code.
