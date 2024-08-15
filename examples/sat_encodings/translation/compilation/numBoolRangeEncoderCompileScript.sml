(*
  Compile the encoder for the numBoolRange datatype
*)
open preamble numBoolRangeEncoderProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "numBoolRangeEncoderCompile"

Theorem numBoolRange_encoder_compiled =
  eval_cake_compile_x64 "" numBoolRange_encoder_prog_def
                          "numBoolRange_encoder.S";

val _ = export_theory ();
