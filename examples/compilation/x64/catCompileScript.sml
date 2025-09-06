(*
  Compiles the cat example by evaluation inside the logic of HOL
*)
Theory catCompile
Ancestors
  catProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem cat_compiled =
  eval_cake_compile_x64 "" cat_prog_def "cat.S";

