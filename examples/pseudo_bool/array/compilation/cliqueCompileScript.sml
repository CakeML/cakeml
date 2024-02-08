(*
  Compiles the max clique + PB checker
*)
open preamble compilationLib cliqueProgTheory

val _ = new_theory "cliqueCompile"

val clique_compiled = save_thm("clique_compiled",
  compile_x64 "cake_pb_clique" main_prog_def);

val _ = export_theory ();
