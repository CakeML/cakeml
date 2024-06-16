(*
  Compiles the sort example by evaluation inside the logic of HOL
*)
open preamble sortProgTheory eval_cake_compile_x64Lib

val _ = new_theory "sortCompile"

Theorem sort_compiled =
  eval_cake_compile_x64 "" sort_prog_def "sort.S";

val _ = export_theory ();
