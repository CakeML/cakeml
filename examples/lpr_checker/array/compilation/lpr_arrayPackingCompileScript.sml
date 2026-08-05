(*
  Compiles the packing example by evaluation inside the logic of HOL
*)
Theory lpr_arrayPackingCompile
Ancestors
  lpr_arrayPackingProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem lpr_packing_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_direct.S";

