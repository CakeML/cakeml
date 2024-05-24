(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble compilationLib npbc_fullProgTheory

val _ = new_theory "npbc_fullCompileARM8"

val pb_arrayFull_compiled = save_thm("npbc_full_compiled",
  compile_arm8 "cake_pb_arm8" main_prog_def);

val _ = export_theory ();
