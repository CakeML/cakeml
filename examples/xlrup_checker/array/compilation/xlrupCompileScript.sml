(*
  Compiles the xlrup example by evaluation inside the logic of HOL
*)
open preamble xlrup_arrayFullProgTheory eval_cake_compile_x64Lib

val _ = new_theory "xlrupCompile"

Theorem xlrup_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_xlrup.S";

val _ = export_theory ();
