(*
  Compiles the OpenTheory article checker in the logic.
*)
open preamble compilationLib readerProgTheory
open x64_configTheory

val _ = new_theory "readerCompile"

val reader_compiled = save_thm("reader_compiled",
  compile_x64 "reader" reader_prog_def);

val _ = export_theory ();
