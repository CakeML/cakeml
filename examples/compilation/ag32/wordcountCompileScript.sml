(*
  Compile the wordcount program to machine code by evaluation of the compiler
  in the logic.
*)
Theory wordcountCompile
Ancestors
  wordcountProg
Libs
  preamble eval_cake_compile_ag32Lib

Theorem wordcount_compiled =
  eval_cake_compile_ag32 "" wordcount_prog_def "wordcount.S";

