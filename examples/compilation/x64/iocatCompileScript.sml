(*
  Compiles the iocat example by evaluation inside the logic of HOL
*)
open preamble iocatProgTheory eval_cake_compile_x64Lib

val _ = new_theory "iocatCompile"

Theorem iocat_compiled =
  eval_cake_compile_x64 "" cat_prog_def "iocat.S";

val _ = export_theory ();
