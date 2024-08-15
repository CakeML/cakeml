(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
open preamble helloProgTheory eval_cake_compile_ag32Lib

val _ = new_theory "helloCompile"

Theorem hello_compiled =
  eval_cake_compile_ag32 "" hello_prog_def "hello.S";

val _ = export_theory ();
