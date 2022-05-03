(*
  Compiles the simple compression schema
*)

open preamble compilationLib deflateDecodeProgTheory;

val _ = new_theory "deflateDecodeCompile"

Theorem deflateDecode_compiled =
  compile_x64 "deflateDecode" deflateDecode_prog_def;

val _ = export_theory ();
