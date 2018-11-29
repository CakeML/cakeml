(*
  Compile the wordfreq program to machine code by evaluation of the compiler in
  the logic.
*)

open preamble wordfreqProgTheory compilationLib

val _ = new_theory"wordfreqCompile";

val wordfreq_compiled = save_thm("wordfreq_compiled",
  compile_x64
    1000 (* stack size in MB *)
    1000 (* heap size in MB *)
    "wordfreq"
    wordfreq_prog_def);

val _ = export_theory();
