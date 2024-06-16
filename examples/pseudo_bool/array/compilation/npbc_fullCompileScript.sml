(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble npbc_fullProgTheory eval_cake_compile_x64Lib

val _ = new_theory "npbc_fullCompile"

Theorem npbc_full_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb.S";

val _ = export_theory ();
