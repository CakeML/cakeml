(*
  Compiles the iocat example by evaluation inside the logic of HOL
*)
open preamble compilationLib iocatProgTheory

val _ = new_theory "iocatCompile"

val cat_compiled = save_thm("iocat_compiled",
  compile_x64 500 500 "iocat" cat_prog_def);

val _ = export_theory ();
