(*
  Compile the encoder for the killer sudoku puzzle
*)
open preamble killerSudokuEncoderProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "killerSudokuEncoderCompile"

Theorem killerSudoku_encoder_compiled =
  eval_cake_compile_x64 "" killerSudoku_encoder_prog_def
                          "killerSudoku_encoder.S";

val _ = export_theory ();
