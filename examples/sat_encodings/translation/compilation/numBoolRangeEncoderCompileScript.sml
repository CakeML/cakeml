(*
  Compile the encoder for the numBoolRange datatype
*)

open preamble compilationLib numBoolRangeEncoderProgTheory;

val _ = new_theory "numBoolRangeEncoderCompile"

Theorem numBoolRange_encoder_compiled =
  compile_x64 "numBoolRange_encoder" numBoolRange_encoder_prog_def;

val _ = export_theory ();
