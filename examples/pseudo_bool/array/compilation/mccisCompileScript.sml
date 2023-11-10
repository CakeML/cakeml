(*
  Compiles the MCCIS + PB checker
*)
open preamble compilationLib mccisProgTheory

val _ = new_theory "mccisCompile"

val mccis_compiled = save_thm("mccis_compiled",
  compile_x64 "cake_pb_mccis" main_prog_def);

val _ = export_theory ();
