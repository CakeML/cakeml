(*
  Compiles the binary for the Deflate decoder
*)
Theory deflateDecodeCompile
Ancestors
  deflateDecodeProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem deflateDecode_compiled =
  eval_cake_compile_x64 "" deflateDecode_prog_def "deflateDecode.S";

