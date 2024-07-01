(*
  Compiles the grep example by evaluation inside the logic of HOL
*)
open preamble grepProgTheory eval_cake_compile_x64Lib

val _ = new_theory "grepCompile"

Theorem grep_compiled =
  eval_cake_compile_x64 "" grep_prog_def "grep.S";

val _ = export_theory ();
