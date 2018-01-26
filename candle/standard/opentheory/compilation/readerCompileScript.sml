open preamble compilationLib readerProgTheory

val _ = new_theory "readerCompile"

val reader_compiled = save_thm("reader_compiled",
  compile_x64 1000 1000 "reader" reader_prog_def);

val _ = export_theory ();

