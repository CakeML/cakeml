(*
  Compiles the min color + PB checker
*)
Theory colorCompile
Ancestors
  colorProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem color_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_color.S";

Theorem color_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_color_arm8.S";

