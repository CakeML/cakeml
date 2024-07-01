(*
  Compile cake_vipr
*)
open preamble viprProgTheory eval_cake_compile_x64Lib

val _ = new_theory "viprCompile"

Theorem vipr_encoder_compiled =
  eval_cake_compile_x64 "" vipr_prog_def "cake_vipr.S";

val _ = export_theory ();
