(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
Theory helloCompile
Ancestors
  helloProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem hello_compiled =
  eval_cake_compile_x64 "" hello_prog_def "hello.S";

