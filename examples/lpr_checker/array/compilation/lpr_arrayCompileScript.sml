(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
Theory lpr_arrayCompile
Ancestors
  lpr_arrayFullProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem lpr_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lpr.S";

(*
val _ =
  eval_cake_compile_explore_x64 "explore_"
    check_unsat_prog_def "cake_lpr_explore.txt";
*)

