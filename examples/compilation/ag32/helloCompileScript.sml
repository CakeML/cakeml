(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
open preamble compilationLib helloProgTheory

val _ = new_theory "helloCompile"

val hello_compiled = save_thm("hello_compiled",
  compile_ag32 "hello" hello_prog_def);

val _ = export_theory ();
