(*
  Compiles the OpenTheory article checker in the logic.
*)
open preamble compilationLib readerIOProgTheory

val _ = new_theory "readerIOCompile"

val readerIO_compiled = save_thm("readerIO_compiled",
  compile_x64 1000 1000 "readerIO" readerIO_prog_def);

val _ = export_theory ();
