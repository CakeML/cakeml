(*
  Compiles the PB checker example by evaluation inside the logic of HOL
*)
open preamble compilationLib pb_arrayFullProgTheory

val _ = new_theory "pb_arrayFullCompile"

val pb_arrayFull_compiled = save_thm("pb_arrayFull_compiled",
  compile_x64 "cake_pb" check_unsat_prog_def);

val _ = export_theory ();
