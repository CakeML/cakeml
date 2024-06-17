(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble lpr_arrayFullProgTheory eval_cake_compile_arm8Lib

val _ = new_theory "lpr_arrayCompileARM8"

Theorem lpr_array_compiled =
  eval_cake_compile_arm8 "" check_unsat_prog_def "cake_lpr_arm8.S";

val _ = export_theory ();
