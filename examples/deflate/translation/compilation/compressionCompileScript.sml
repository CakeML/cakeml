(*
  Compiles the simple compression schema
*)
open preamble compressionProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "compressionCompile"

Theorem compression_compiled =
  eval_cake_compile_x64 "" compression_prog_def "compression.S";

val _ = export_theory ();
