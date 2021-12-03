(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble compilationLib pb_checkProgTheory

val _ = new_theory "pb_checkCompile"

val pb_check_compiled = save_thm("pb_check_compiled",
  compile_x64 "pb_check" check_unsat_prog_def);

val _ = export_theory ();
