(*
  Compiles the binary for the Deflate decoder
*)
open preamble deflateDecodeProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "deflateDecodeCompile"

Theorem deflateDecode_compiled =
  eval_cake_compile_x64 "" deflateDecode_prog_def "deflateDecode.S";

val _ = export_theory ();
