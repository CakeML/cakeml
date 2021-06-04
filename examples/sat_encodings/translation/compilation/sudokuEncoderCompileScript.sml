(*
  Compile the encoder for the sudoku puzzle
*)

open preamble compilationLib sudokuEncoderProgTheory;

val _ = new_theory "sudokuEncoderCompile"

Theorem sudoku_encoder_compiled =
  compile_x64 "sudoku_encoder" sudoku_encoder_prog_def;

val _ = export_theory ();
