(*
  Compiles the binary for the Deflate Encoder
*)

open preamble compilationLib deflateEncodeProgTheory;

val _ = new_theory "deflateEncodeCompile"

Theorem deflateEncode_compiled =
  compile_x64 "deflateEncode" deflateEncode_prog_def;

val _ = export_theory ();
