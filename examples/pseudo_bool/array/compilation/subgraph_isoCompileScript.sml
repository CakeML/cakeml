(*
  Compiles the encoder
*)
open preamble subgraph_isoProgTheory eval_cake_compile_x64Lib

val _ = new_theory "subgraph_isoCompile"

Theorem subgraph_iso_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_iso.S";

val _ = export_theory ();
