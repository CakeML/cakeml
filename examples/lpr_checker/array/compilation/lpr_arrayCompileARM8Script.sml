(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
Theory lpr_arrayCompileARM8
Ancestors
  lpr_arrayFullProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem lpr_array_compiled =
  eval_cake_compile_arm8 "" check_unsat_prog_def "cake_lpr_arm8.S";

