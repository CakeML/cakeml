(*
  Compiles the lrat example by evaluation inside the logic of HOL
*)
open preamble compilationLib lratProgTheory

val _ = new_theory "lratCompile"

val lrat_compiled = save_thm("lrat_compiled",
  compile_x64 1000 1000 "lrat" check_unsat_prog_def);

val _ = export_theory ();
