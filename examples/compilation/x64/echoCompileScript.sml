(*
  Compiles the echo example by evaluation inside the logic of HOL
*)
Theory echoCompile
Ancestors
  echoProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem echo_compiled =
  eval_cake_compile_x64 "" echo_prog_def "echo.S";

