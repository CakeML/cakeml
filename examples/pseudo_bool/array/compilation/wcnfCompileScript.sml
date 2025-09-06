(*
  Compiles the WCNF + PB checker
*)
Theory wcnfCompile
Ancestors
  wcnfProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem wcnf_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_wcnf.S";

Theorem wcnf_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_wcnf_arm8.S";

