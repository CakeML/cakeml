(*
  Compiles the MCIS + PB checker
*)
Theory mcisCompile
Ancestors
  mcisProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem mcis_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mcis.S";

Theorem mcis_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_mcis_arm8.S";

