(*
  Evaluation of the 64-bit version of the compiler into arm8 machine code.
*)
Theory arm8Bootstrap
Ancestors
  compiler64Prog
Libs
  preamble eval_cake_compile_arm8Lib

Theorem compiler64_compiled =
  eval_cake_compile_arm8 "" compiler64_prog_def "cake.S";

