(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble compilationLib npbc_fullProgTheory

val _ = new_theory "npbc_fullCompile"

val pb_arrayFull_compiled = save_thm("npbc_full_compiled",
  compile_x64 "cake_pb" main_prog_def);

val pb_arrayFull_compiled_arm8 = save_thm("npbc_full_compiled_arm8",
  compile_arm8 "cake_pb_arm8" main_prog_def);

val _ = export_theory ();
