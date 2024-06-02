(*
  Compiles the MCIS + PB checker
*)
open preamble compilationLib mcisProgTheory

val _ = new_theory "mcisCompile"

val mcis_compiled = save_thm("mcis_compiled",
  compile_x64 "cake_pb_mcis" main_prog_def);

val _ = intermediate_prog_prefix := "arm8_"

val mcis_compiled_arm8 = save_thm("mcis_compiled_arm8",
  compile_arm8 "cake_pb_mcis_arm8" main_prog_def);

val _ = export_theory ();
