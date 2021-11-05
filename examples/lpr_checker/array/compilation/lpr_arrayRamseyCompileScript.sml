(*
  Compiles the lpr example by evaluation inside the logic of HOL
*)
open preamble compilationLib lpr_arrayRamseyProgTheory

val _ = new_theory "lpr_arrayRamseyCompile"

val lpr_array_compiled = save_thm("lpr_ramsey_compiled",
  compile_x64 "lpr_ramsey" check_unsat_prog_def);

val _ = export_theory ();
