(*
  Compiles the diff example by evaluation inside the logic of HOL
*)
Theory diffCompile
Ancestors
  diffProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem diff_compiled =
  eval_cake_compile_x64 "" diff_prog_def "diff.S";

