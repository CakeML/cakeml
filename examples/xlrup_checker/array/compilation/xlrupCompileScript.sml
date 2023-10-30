(*
  Compiles the xlrup example by evaluation inside the logic of HOL
*)
open preamble compilationLib xlrup_arrayFullProgTheory

val _ = new_theory "xlrupCompile"

val xlrup_array_compiled = save_thm("xlrup_array_compiled",
  compile_x64 "cake_xlrup" check_unsat_prog_def);

val _ = export_theory ();
