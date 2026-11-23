(*
  Compiles the encoder
*)
Theory subgraph_isoCompile
Ancestors
  subgraph_isoProg npbc_compile_config
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem subgraph_iso_compiled =
  eval_cake_compile_x64_with_conf "" x64_config_pb_def main_prog_def
    "cake_pb_iso.S";

Theorem subgraph_iso_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config_pb_def main_prog_def
    "cake_pb_iso_arm8.S";

