(*
  Compiles the simple compression schema
*)

open preamble compilationLib compressionProgTheory;

val _ = new_theory "compressionCompile"

Theorem compression_compiled =
  compile_x64 "compression" compression_prog_def;

val _ = export_theory ();
