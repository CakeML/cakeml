(*
  Compiles the distrup example by evaluation inside the logic of HOL
*)
Theory distrup Compile
Ancestors
  distrup_arrayFullProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem distrup_array_compiled =
  eval_cake_compile_x64 "" distrup_prog_def "cake_distrup.S";

