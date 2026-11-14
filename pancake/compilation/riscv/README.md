Native RISC-V64 Pancake compiler.

Unpack `pancake-riscv.tar.gz` and run `make pancake` on RISC-V64 Linux.
The archive includes assembly, FFI source, a standalone Makefile and this
README.
Set `CC` to use a cross compiler. Run `./pancake --help` for compiler options.

In a CakeML checkout, run `Holmake pancake-riscv.tar.gz` to build the archive.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[pancake_riscvBootstrapScript.sml](pancake_riscvBootstrapScript.sml):
Evaluation of the Pancake compiler into RISC-V64 machine code.
