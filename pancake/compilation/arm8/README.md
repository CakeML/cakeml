Native ARM8 Pancake compiler.

Unpack `pancake-arm8.tar.gz` and run `make pancake` on ARM8 Linux.
The archive includes assembly, FFI source, a standalone Makefile and this
README.
Set `CC` to use a cross compiler. Run `./pancake --help` for compiler options.

In a CakeML checkout, run `Holmake pancake-arm8.tar.gz` to build the archive.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[pancake_arm8BootstrapScript.sml](pancake_arm8BootstrapScript.sml):
Evaluation of the Pancake compiler into arm8 machine code.
