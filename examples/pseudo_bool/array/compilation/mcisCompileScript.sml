(*
  Compiles the MCIS + PB checker
*)
open preamble mcisProgTheory eval_cake_compile_x64Lib

val _ = new_theory "mcisCompile"

Theorem mcis_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mcis.S";

val _ = export_theory ();
