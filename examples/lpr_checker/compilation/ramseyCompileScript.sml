(*
  Compiles the ramsey example by evaluation inside the logic of HOL
*)
open preamble compilationLib ramseyProgTheory

val _ = new_theory "ramseyCompile"

val ramsey_compiled = save_thm("ramsey_compiled",
  compile_x64 "ramsey" check_ramsey_prog_def);

val _ = export_theory ();
