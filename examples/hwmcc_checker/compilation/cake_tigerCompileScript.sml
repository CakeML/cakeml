(*
  Generates the cake_tiger binary.
*)
Theory cake_tigerCompile
Ancestors
  cake_tigerProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem cake_tiger_compiled =
  eval_cake_compile_x64 "" cake_tiger_prog_def "cake_tiger.S";
