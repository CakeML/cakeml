(*
  Compiles the encoder for the graph coloring problem
*)
Theory graphColoringEncoderCompile
Ancestors
  graphColoringEncoderProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem graphColoring_encoder_compiled =
  eval_cake_compile_x64 "" graphColoring_encoder_prog_def
                          "graphColoring_encoder.S";

