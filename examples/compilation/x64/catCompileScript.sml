(*
  Compiles the cat example by evaluation inside the logic of HOL
*)
open preamble catProgTheory eval_cake_compile_x64Lib

val _ = new_theory "catCompile"

Theorem cat_compiled =
  eval_cake_compile_x64 "" cat_prog_def "cat.S";

val _ = export_theory ();
