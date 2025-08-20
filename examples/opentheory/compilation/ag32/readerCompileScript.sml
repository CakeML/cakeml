(*
  In-logic compilation of the OPenTHeory article checker to the
  Silver ISA.
*)
Theory readerCompile
Ancestors
  readerProg
Libs
  preamble eval_cake_compile_ag32Lib

Theorem reader_compiled =
  eval_cake_compile_ag32 "" reader_prog_def "reader.S";

