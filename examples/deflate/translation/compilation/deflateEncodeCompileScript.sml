(*
  Compiles the binary for the Deflate Encoder
*)
open preamble deflateEncodeProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "deflateEncodeCompile"

Theorem deflateEncode_compiled =
  eval_cake_compile_x64 "" deflateEncode_prog_def "deflateEncode.S";

val _ = export_theory ();
