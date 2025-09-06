(*
  Evaluateof the 32-bit version of the compiler into x64 machine code.
*)
Theory x64Bootstrap
Ancestors
  compiler32Prog
Libs
  preamble eval_cake_compile_x64Lib

Theorem compiler32_compiled =
  eval_cake_compile_x64 "" compiler32_prog_def "cake.S";

