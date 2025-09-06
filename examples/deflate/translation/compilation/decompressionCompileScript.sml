(*
  Compiles the simple decompression schema
*)
Theory decompressionCompile
Ancestors
  decompressionProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem decompression_compiled =
  eval_cake_compile_x64 "" decompression_prog_def "decompression.S";

