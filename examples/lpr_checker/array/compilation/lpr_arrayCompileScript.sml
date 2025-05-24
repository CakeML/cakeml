(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble lpr_arrayFullProgTheory eval_cake_compile_x64Lib

val _ = new_theory "lpr_arrayCompile"

Theorem lpr_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lpr.S";

(*
val _ =
  eval_cake_compile_explore_x64 "explore_"
    check_unsat_prog_def "cake_lpr_explore.txt";
*)

val _ = export_theory ();
