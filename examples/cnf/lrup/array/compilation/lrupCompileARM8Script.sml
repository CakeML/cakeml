(*
  Compiles the lrup example for ARM8 by evaluation inside the logic of HOL
*)
Theory lrupCompileARM8
Ancestors
  lrup_arrayFullProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem lrup_array_compiled =
  eval_cake_compile_arm8 "" check_unsat_prog_def "cake_lrup_arm8.S";
