(*
  Compiles the simple decompression schema
*)

open preamble compilationLib decompressionProgTheory;

val _ = new_theory "decompressionCompile"

Theorem decompression_compiled =
  compile_x64 "decompression" decompression_prog_def;

val _ = export_theory ();
