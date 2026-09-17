(*
  Compiles the CNF + PB checker
*)
Theory cnfCompile
Ancestors
  cnfProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem cnf_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_cnf.S";

Theorem cnf_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_cnf_arm8.S";

