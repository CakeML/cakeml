(*
  Compile the encoder for the n-queens problem
*)
open preamble nQueensEncoderProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "nQueensEncoderCompile"

Theorem nQueens_encoder_compiled =
  eval_cake_compile_x64 "" nQueens_encoder_prog_def
                          "nQueens_encoder.S";

val _ = export_theory ();
