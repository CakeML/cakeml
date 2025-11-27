(*
  Compile the encoder for the numBoolRange datatype
*)
Theory numBoolRangeEncoderCompile
Ancestors
  numBoolRangeEncoderProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem numBoolRange_encoder_compiled =
  eval_cake_compile_x64 "" numBoolRange_encoder_prog_def
                          "numBoolRange_encoder.S";

