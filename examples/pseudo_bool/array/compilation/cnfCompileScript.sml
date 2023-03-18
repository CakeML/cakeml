(*
  Compiles the CNF + PB checker
*)
open preamble compilationLib cnfProgTheory

val _ = new_theory "cnfCompile"

val cnf_compiled = save_thm("cnf_compiled",
  compile_x64 "cnf" main_prog_def);

val _ = export_theory ();
