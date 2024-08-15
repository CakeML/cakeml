(*
  Compile the wordcount program to machine code by evaluation of the compiler
  in the logic.
*)

open preamble wordcountProgTheory eval_cake_compile_x64Lib

val _ = new_theory"wordcountCompile";

Theorem wordcount_compiled =
  eval_cake_compile_x64 "" wordcount_prog_def "wordcount.S";

val _ = export_theory();
