(*
  Compiles the encoder
*)
open preamble compilationLib max_common_induced_subgraphProgTheory

val _ = new_theory "max_common_induced_subgraphCompile"

val max_common_induced_subgraph_compiled = save_thm("max_common_induced_subgraph_compiled",
  compile_x64 "mcis" top_prog_def);

val _ = export_theory ();
