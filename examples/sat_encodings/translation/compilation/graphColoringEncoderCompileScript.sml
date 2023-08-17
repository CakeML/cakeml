(*
  Compiles the encoder for the graph coloring problem
*)

open preamble compilationLib graphColoringEncoderProgTheory;

val _ = new_theory "graphColoringEncoderCompile"

Theorem graphColoring_encoder_compiled =
  compile_x64 "graphColoring_encoder" graphColoring_encoder_prog_def;

val _ = export_theory ();
