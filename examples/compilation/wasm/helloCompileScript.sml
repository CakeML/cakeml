(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
open preamble helloProgTheory eval_cake_compile_wasmLib

val _ = new_theory "helloCompile"

Theorem hello_compiled =
  eval_cake_compile_wasm "" hello_prog_def "hello.wasm";

val _ = export_theory ();
