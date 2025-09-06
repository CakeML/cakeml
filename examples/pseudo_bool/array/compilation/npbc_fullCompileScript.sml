(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
Theory npbc_fullCompile
Ancestors
  npbc_fullProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem npbc_full_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb.S";

Theorem npbc_full_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_arm8.S";

