(*
  Compile the wordfreq program to machine code by evaluation of the compiler in
  the logic.
*)
open preamble wordfreqProgTheory eval_cake_compile_x64Lib

val _ = new_theory"wordfreqCompile";

Theorem wordfreq_compiled =
  eval_cake_compile_x64 "" wordfreq_prog_def "wordfreq.S";

val _ = export_theory();
