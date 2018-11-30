(*
  Compiles the echo example by evaluation inside the logic of HOL
*)
open preamble compilationLib echoProgTheory

val _ = new_theory "echoCompile"

val echo_compiled = save_thm("echo_compiled",
  compile_x64 500 500 "echo" echo_prog_def);

val _ = export_theory ();
