(*
  Compiles the maximal clique + PB checker
*)
Theory mcliqueCompile
Ancestors
  mcliqueProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem mclique_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mclique.S";

Theorem mclique_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_mclique_arm8.S";

