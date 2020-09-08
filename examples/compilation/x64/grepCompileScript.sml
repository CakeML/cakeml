(*
  Compiles the grep example by evaluation inside the logic of HOL
*)
open preamble compilationLib grepProgTheory

val _ = new_theory "grepCompile"

val grep_compiled = save_thm("grep_compiled",
  compile_x64 "grep" grep_prog_def);

val _ = export_theory ();
