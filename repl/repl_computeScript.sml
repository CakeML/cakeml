open preamble repl_funTheory ASCIInumbersLib intLib
open AstTheory inferTheory CompilerTheory compilerTerminationTheory bytecodeEvalTheory

val _ = new_theory "repl_compute";

val C_main_loop_def = Define`C_main_loop i (s,bs) = main_loop (s,bs) i`


val _ = export_theory ();

