(*
  Compile the wordfreq program to machine code by evaluation of the compiler in
  the logic.
*)

open preamble wordfreqProgTheory compilationLib

val _ = new_theory"wordfreqCompile";

val wordfreq_compiled = save_thm("wordfreq_compiled",
  compile_x64 "wordfreq" wordfreq_prog_def);

val _ = export_theory();
