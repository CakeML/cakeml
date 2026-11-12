(*
  Evaluate the AG32 batch entry point of the CakeML compiler
  into machine code for ag32, i.e. the Silver ISA.
*)
Theory ag32Bootstrap
Ancestors
  compiler_ag32Prog
Libs
  preamble eval_cake_compile_ag32Lib

Theorem compiler_compiled =
  eval_cake_compile_ag32 "" compiler_ag32_prog_def "cake.S";
