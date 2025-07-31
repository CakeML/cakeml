(*
  Compiles the grep example by evaluation inside the logic of HOL
*)
Theory grepCompile
Ancestors
  grepProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem grep_compiled =
  eval_cake_compile_x64 "" grep_prog_def "grep.S";

