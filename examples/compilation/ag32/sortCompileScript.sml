(*
  Compiles the sort example by evaluation inside the logic of HOL
*)
open preamble sortProgTheory eval_cake_compile_ag32Lib

val _ = new_theory "sortCompile"

Theorem sort_compiled =
  eval_cake_compile_ag32 "" sort_prog_def "sort.S";

val _ = export_theory ();
