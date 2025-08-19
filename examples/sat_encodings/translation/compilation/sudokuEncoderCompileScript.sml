(*
  Compile the encoder for the sudoku puzzle
*)
Theory sudokuEncoderCompile
Ancestors
  sudokuEncoderProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem sudoku_encoder_compiled =
  eval_cake_compile_x64 "" sudoku_encoder_prog_def
                          "sudoku_encoder.S";

