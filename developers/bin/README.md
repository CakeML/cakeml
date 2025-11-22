This directory represents a stage in the build sequence where the latest
available cake binary is downloaded to perform testing and bootstrapping.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[hello.cml](hello.cml):
A simple hello world program in CakeML

[repl_boot.cml](repl_boot.cml):
This file gives the CakeML REPL multi-line input and file loading
capabilities.
