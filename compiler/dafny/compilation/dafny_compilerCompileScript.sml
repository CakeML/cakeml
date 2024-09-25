(*
 * Compiles the Dafny to CakeML compiler.
 *)

open preamble dafny_compilerProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "dafny_compilerCompile";

Theorem dafny_compiler_compiled =
        eval_cake_compile_x64 "" dafny_compiler_prog_def
                              "dafny_compiler.S";

val _ = export_theory ();
