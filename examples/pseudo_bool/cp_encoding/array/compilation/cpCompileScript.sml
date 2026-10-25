(*
  Compiles the CP encoder + PB checker
*)
Theory cpCompile
Ancestors
  cpProg npbc_compile_config
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem cp_compiled =
  eval_cake_compile_x64_with_conf "" x64_config_pb_def main_prog_def
    "cake_pb_cp.S";

Theorem cp_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config_pb_def main_prog_def
    "cake_pb_cp_arm8.S";
