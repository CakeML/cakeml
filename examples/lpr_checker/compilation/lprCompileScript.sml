(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble compilationLib lprProgTheory

val _ = new_theory "lprCompile"

val lpr_compiled = save_thm("lpr_compiled",
  compile_x64 1000 1000 "lpr" check_unsat_prog_def);

val _ = export_theory ();
