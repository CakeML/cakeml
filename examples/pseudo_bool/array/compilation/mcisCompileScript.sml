(*
  Compiles the MCIS + PB checker
*)
open preamble compilationLib mcisProgTheory

val _ = new_theory "mcisCompile"

val mcis_compiled = save_thm("mcis_compiled",
  compile_x64 "mcis" main_prog_def);

val _ = export_theory ();
