(*
  Compiles the min colour + PB checker
*)
Theory colourCompile
Ancestors
  colourProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem colour_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_colour.S";

Theorem colour_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_colour_arm8.S";

