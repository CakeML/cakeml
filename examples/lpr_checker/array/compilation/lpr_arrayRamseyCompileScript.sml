(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
Theory lpr_arrayRamseyCompile
Ancestors
  lpr_arrayRamseyProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem lpr_ramsey_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lpr_ramsey.S";

