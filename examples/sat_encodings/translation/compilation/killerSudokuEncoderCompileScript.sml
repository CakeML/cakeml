(*
  Compile the encoder for the killer sudoku puzzle
*)
Theory killerSudokuEncoderCompile
Ancestors
  killerSudokuEncoderProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem killerSudoku_encoder_compiled =
  eval_cake_compile_x64 "" killerSudoku_encoder_prog_def
                          "killerSudoku_encoder.S";

