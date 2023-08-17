(*
  Compile cake_vipr
*)

open preamble compilationLib viprProgTheory;

val _ = new_theory "viprCompile"

Theorem vipr_encoder_compiled =
  compile_x64 "cake_vipr" vipr_prog_def;

val _ = export_theory ();
