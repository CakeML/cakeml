(*
  Compiles the diff example by evaluation inside the logic of HOL
*)
open preamble diffProgTheory eval_cake_compile_x64Lib

val _ = new_theory "diffCompile"

Theorem diff_compiled =
  eval_cake_compile_x64 "" diff_prog_def "diff.S";

val _ = export_theory ();
