(*
  Compiles the helloErr example by evaluation inside the logic of HOL
*)
Theory helloErrCompile
Ancestors
  helloErrProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem helloErr_compiled =
  eval_cake_compile_x64 "" helloErr_prog_def "helloErr.S";

