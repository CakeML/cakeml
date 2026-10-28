(*
  Compiles the CP encoder + PB checker
*)
Theory cpCompile
Ancestors
  cpProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem cp_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_cp.S";

Theorem cp_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_cp_arm8.S";
