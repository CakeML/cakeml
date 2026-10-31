(*
  Compiles the xlrup example for ARM8 by evaluation inside the logic of HOL
*)
Theory xlrupCompileARM8
Ancestors
  xlrup_arrayFullProg
Libs
  preamble eval_cake_compile_arm8Lib

Theorem xlrup_array_compiled =
  eval_cake_compile_arm8 "" check_unsat_prog_def "cake_xlrup_arm8.S";
