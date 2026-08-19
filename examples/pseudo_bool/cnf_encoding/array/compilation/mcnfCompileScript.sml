(*
  Compiles the MCNF + PB checker
*)
Theory mcnfCompile
Ancestors
  mcnfProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem mcnf_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mcnf.S";

Theorem mcnf_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_mcnf_arm8.S";
