(*
  Compiles the lrup example by evaluation inside the logic of HOL
*)
Theory lrupCompile
Ancestors
  lrup_arrayFullProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem lrup_array_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lrup.S";
