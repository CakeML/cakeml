A simple example of using eval, to help work out the development of the
bootstrapped compiler supporting eval.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls. This version
is modified to support eval.

[compile_code_to_evalScript.sml](compile_code_to_evalScript.sml):
Defines and compiles (using incremental compiler) the
code that gets eval'd by the eval example.

[eval_exampleCompileScript.sml](eval_exampleCompileScript.sml):
Compiles the eval example in the logic.

[eval_exampleProgScript.sml](eval_exampleProgScript.sml):
Defines abstract syntax for a simple program that calls eval.
The call is made to machine code read from a file.
