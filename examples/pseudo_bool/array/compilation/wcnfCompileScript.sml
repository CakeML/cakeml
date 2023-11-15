(*
  Compiles the WCNF + PB checker
*)
open preamble compilationLib wcnfProgTheory

val _ = new_theory "wcnfCompile"

val wcnf_compiled = save_thm("wcnf_compiled",
  compile_x64 "cake_pb_wcnf" main_prog_def);

val _ = export_theory ();
