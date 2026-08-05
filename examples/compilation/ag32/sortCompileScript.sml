(*
  Compiles the sort example by evaluation inside the logic of HOL
*)
Theory sortCompile
Ancestors
  sortProg
Libs
  preamble eval_cake_compile_ag32Lib

Theorem sort_compiled =
  eval_cake_compile_ag32 "" sort_prog_def "sort.S";

