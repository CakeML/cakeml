(*
  Compile the encoder for the sudoku puzzle
*)
open preamble sudokuEncoderProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "sudokuEncoderCompile"

Theorem sudoku_encoder_compiled =
  eval_cake_compile_x64 "" sudoku_encoder_prog_def
                          "sudoku_encoder.S";

val _ = export_theory ();
