(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble npbc_fullProgTheory eval_cake_compile_arm8Lib

val _ = new_theory "npbc_fullCompileARM8"

Theorem npbc_full_compiled =
  eval_cake_compile_arm8 "" main_prog_def "cake_pb_arm8.S";

val _ = export_theory ();
