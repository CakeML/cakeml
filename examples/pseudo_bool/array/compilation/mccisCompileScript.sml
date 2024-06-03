(*
  Compiles the MCCIS + PB checker
*)
open preamble compilationLib mccisProgTheory

val _ = new_theory "mccisCompile"

val _ = intermediate_prog_prefix := "arm8_"

val mccis_compiled_arm8 = save_thm("mccis_compiled_arm8",
  compile_arm8 "cake_pb_mccis_arm8" main_prog_def);

(* Default has no prefix *)
val _ = intermediate_prog_prefix := ""

val mccis_compiled = save_thm("mccis_compiled",
  compile_x64 "cake_pb_mccis" main_prog_def);

val _ = export_theory ();
