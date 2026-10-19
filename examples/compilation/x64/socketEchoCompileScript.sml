(*
  Compiles the socketEcho example by evaluation inside the logic of HOL
*)
Theory socketEchoCompile
Ancestors
  socketEchoProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem socketEcho_compiled =
  eval_cake_compile_x64 "" socketEcho_prog_def "socketEcho.S";
