(*
  In-logic compilation of the OPenTHeory article checker to the
  Silver ISA.
*)
open preamble readerProgTheory eval_cake_compile_ag32Lib

val _ = new_theory "readerCompile"

Theorem reader_compiled =
  eval_cake_compile_ag32 "" reader_prog_def "reader.S";

val _ = export_theory ();
