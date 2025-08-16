(*
  Compile the encoder for the n-queens problem
*)
Theory nQueensEncoderCompile
Ancestors
  nQueensEncoderProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem nQueens_encoder_compiled =
  eval_cake_compile_x64 "" nQueens_encoder_prog_def
                          "nQueens_encoder.S";

