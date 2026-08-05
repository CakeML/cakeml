(*
  Compiles the binary for the Deflate Encoder
*)
Theory deflateEncodeCompile
Ancestors
  deflateEncodeProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem deflateEncode_compiled =
  eval_cake_compile_x64 "" deflateEncode_prog_def "deflateEncode.S";

