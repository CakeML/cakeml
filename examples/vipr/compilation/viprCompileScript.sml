(*
  Compile cake_vipr
*)
Theory viprCompile
Ancestors
  viprProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem vipr_encoder_compiled =
  eval_cake_compile_x64 "" vipr_prog_def "cake_vipr.S";

