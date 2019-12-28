(*
  Compiles the lrat example by evaluation inside the logic of HOL
*)
open preamble compilationLib lrat_arrayProgTheory

val _ = new_theory "lrat_arrayCompile"

val lrat_array_compiled = save_thm("lrat_array_compiled",
  compile_x64 1000 1000 "lrat_array" check_unsat_prog_def);

val _ = export_theory ();
