(*
  Compiles the MCCIS + PB checker
*)
Theory mccisCompile
Ancestors
  mccisProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem mccis_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mccis.S";

Theorem mccis_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_mccis_arm8.S";

