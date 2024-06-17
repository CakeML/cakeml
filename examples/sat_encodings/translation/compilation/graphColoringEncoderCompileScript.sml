(*
  Compiles the encoder for the graph coloring problem
*)
open preamble graphColoringEncoderProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "graphColoringEncoderCompile"

Theorem graphColoring_encoder_compiled =
  eval_cake_compile_x64 "" graphColoring_encoder_prog_def
                          "graphColoring_encoder.S";

val _ = export_theory ();
