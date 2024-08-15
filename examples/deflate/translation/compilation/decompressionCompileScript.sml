(*
  Compiles the simple decompression schema
*)
open preamble decompressionProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "decompressionCompile"

Theorem decompression_compiled =
  eval_cake_compile_x64 "" decompression_prog_def "decompression.S";

val _ = export_theory ();
