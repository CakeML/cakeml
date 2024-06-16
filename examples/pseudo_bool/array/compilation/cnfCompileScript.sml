(*
  Compiles the CNF + PB checker
*)
open preamble cnfProgTheory eval_cake_compile_x64Lib

val _ = new_theory "cnfCompile"

Theorem cnf_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_cnf.S";

val _ = export_theory ();
