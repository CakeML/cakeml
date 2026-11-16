(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
Theory npbc_fullCompile
Ancestors
  npbc_fullProg npbc_compile_config
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem npbc_full_compiled =
  eval_cake_compile_x64_with_conf "" x64_config_pb_def main_prog_def
    "cake_pb.S";

Theorem npbc_full_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config_pb_def main_prog_def
    "cake_pb_arm8.S";

