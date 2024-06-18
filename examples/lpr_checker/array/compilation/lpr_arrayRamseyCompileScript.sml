(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble lpr_arrayRamseyProgTheory eval_cake_compile_x64Lib

val _ = new_theory "lpr_arrayRamseyCompile"

Theorem lpr_ramsey_compiled =
  eval_cake_compile_x64 "" check_unsat_prog_def "cake_lpr_ramsey.S";

val _ = export_theory ();
