(*
  Compile the encoder for the n-queens problem
*)

open preamble compilationLib nQueensEncoderProgTheory;

val _ = new_theory "nQueensEncoderCompile"

Theorem nQueens_encoder_compiled =
  compile_x64 "nQueens_encoder" nQueens_encoder_prog_def;

val _ = export_theory ();
