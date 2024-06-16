(*
  Compiles the MCCIS + PB checker
*)
open preamble mccisProgTheory eval_cake_compile_x64Lib

val _ = new_theory "mccisCompile"

Theorem mccis_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mccis.S";

val _ = export_theory ();
