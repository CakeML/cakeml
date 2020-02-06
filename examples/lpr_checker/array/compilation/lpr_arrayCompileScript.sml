(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble compilationLib lpr_arrayProgTheory

val _ = new_theory "lpr_arrayCompile"

val lpr_array_compiled = save_thm("lpr_array_compiled",
  compile_x64 1000 1000 "lpr_array" check_unsat_prog_def);

val _ = export_theory ();
