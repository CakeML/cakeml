(*
  Compiles the max clique + PB checker
*)
Theory cliqueCompile
Ancestors
  cliqueProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem clique_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_clique.S";

Theorem clique_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_clique_arm8.S";

