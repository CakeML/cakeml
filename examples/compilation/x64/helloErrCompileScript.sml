(*
  Compiles the helloErr example by evaluation inside the logic of HOL
*)
open preamble compilationLib helloErrProgTheory

val _ = new_theory "helloErrCompile"

val helloErr_compiled = save_thm("helloErr_compiled",
  compile_x64 500 500 "helloErr" helloErr_prog_def);

val _ = export_theory ();
