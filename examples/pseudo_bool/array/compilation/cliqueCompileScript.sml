(*
  Compiles the max clique + PB checker
*)
open preamble cliqueProgTheory eval_cake_compile_x64Lib

val _ = new_theory "cliqueCompile"

Theorem clique_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_clique.S";

val _ = export_theory ();
