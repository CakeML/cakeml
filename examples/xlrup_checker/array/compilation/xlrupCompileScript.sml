(*
  Compiles the xlrup example by evaluation inside the logic of HOL
*)
Theory xlrupCompile
Ancestors
  xlrup_arrayFullProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem xlrup_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_xlrup.S";

