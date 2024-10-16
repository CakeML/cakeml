(*
  Compiles the OpenTheory article checker in the logic.
*)
open preamble compilationLib readerIOProgTheory

val _ = new_theory "readerIOCompile"

Theorem readerIO_compiled =
  compile_x64 "readerIO" readerIO_prog_def

val _ = export_theory ();
