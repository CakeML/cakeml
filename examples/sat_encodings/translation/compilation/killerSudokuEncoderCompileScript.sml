(*
  Compile the encoder for the killer sudoku puzzle
*)

open preamble compilationLib killerSudokuEncoderProgTheory;

val _ = new_theory "killerSudokuEncoderCompile"

Theorem killerSudoku_encoder_compiled =
  compile_x64 "killerSudoku_encoder" killerSudoku_encoder_prog_def;

val _ = export_theory ();
