(*
  Compiles the encoder
*)
open preamble compilationLib subgraph_isoProgTheory

val _ = new_theory "subgraph_isoCompile"

val subgraph_iso_compiled = save_thm("subgraph_iso_compiled",
  compile_x64 "cake_pb_iso" main_prog_def);

val _ = export_theory ();
