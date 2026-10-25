(*
  Compiles the MCIS + PB checker
*)
Theory mcisCompile
Ancestors
  mcisProg npbc_compile_config
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem mcis_compiled =
  eval_cake_compile_x64_with_conf "" x64_config_pb_def main_prog_def
    "cake_pb_mcis.S";

Theorem mcis_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config_pb_def main_prog_def
    "cake_pb_mcis_arm8.S";

