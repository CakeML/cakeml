(*
  Compiles the min colour + PB checker
*)
Theory colourCompile
Ancestors
  colourProg npbc_compile_config
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem colour_compiled =
  eval_cake_compile_x64_with_conf "" x64_config_pb_def main_prog_def
    "cake_pb_colour.S";

Theorem colour_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config_pb_def main_prog_def
    "cake_pb_colour_arm8.S";

