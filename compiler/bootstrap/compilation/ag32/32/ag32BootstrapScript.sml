(*
  Evaluate the final part of the 32-bit version of the compiler
  into machine code for ag32, i.e. the Silver ISA.
*)
Theory ag32Bootstrap
Ancestors
  compiler32Prog
Libs
  preamble eval_cake_compile_ag32Lib

Theorem compiler32_compiled =
  eval_cake_compile_ag32 "" compiler32_prog_def "cake.S";

