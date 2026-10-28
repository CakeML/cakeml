(*
  Compile the wordfreq program to machine code by evaluation of the compiler in
  the logic.
*)
Theory wordfreqCompile
Ancestors
  wordfreqProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem wordfreq_compiled =
  eval_cake_compile_x64 "" wordfreq_prog_def "wordfreq.S";

