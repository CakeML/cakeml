(*
  Compile the wordcount program to machine code by evaluation of the compiler
  in the logic.
*)

open preamble wordcountProgTheory compilationLib

val _ = new_theory"wordcountCompile";

val wordcount_compiled = save_thm("wordcount_compiled",
  compile_x64
    1000 (* stack size in MB *)
    1000 (* heap size in MB *)
    "wordcount"
    wordcount_prog_def);

val _ = export_theory();
