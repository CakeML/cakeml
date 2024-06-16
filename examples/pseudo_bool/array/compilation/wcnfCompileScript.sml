(*
  Compiles the WCNF + PB checker
*)
open preamble wcnfProgTheory eval_cake_compile_x64Lib

val _ = new_theory "wcnfCompile"

Theorem wcnf_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_wcnf.S";

val _ = export_theory ();
