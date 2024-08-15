(*
  Compiles the packing example by evaluation inside the logic of HOL
*)
open preamble lpr_arrayPackingProgTheory eval_cake_compile_x64Lib

val _ = new_theory "lpr_arrayPackingCompile"

Theorem lpr_packing_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_direct.S";

val _ = export_theory ();
