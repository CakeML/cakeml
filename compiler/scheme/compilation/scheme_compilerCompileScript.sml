(*
  In-logic compilation of the Scheme-to-CakeML compiler
*)

open preamble scheme_compilerProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "scheme_compilerCompile";

Theorem scheme_compiler_compiled =
        eval_cake_compile_x64 "" scheme_compiler_prog_def
                                "scheme_compiler.S";

val _ = export_theory ();
