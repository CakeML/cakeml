(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble compilationLib lpr_arrayFullProgTheory

val _ = new_theory "lpr_arrayCompileARM8"

val lpr_array_compiled = save_thm("lpr_array_compiled",
  compile_arm8 "cake_lpr_arm8" check_unsat_prog_def);

val _ = export_theory ();
