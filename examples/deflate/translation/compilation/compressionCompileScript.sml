(*
  Compiles the simple compression schema
*)
Theory compressionCompile
Ancestors
  compressionProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem compression_compiled =
  eval_cake_compile_x64 "" compression_prog_def "compression.S";

