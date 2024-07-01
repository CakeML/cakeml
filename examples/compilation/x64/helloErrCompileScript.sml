(*
  Compiles the helloErr example by evaluation inside the logic of HOL
*)
open preamble helloErrProgTheory eval_cake_compile_x64Lib

val _ = new_theory "helloErrCompile"

Theorem helloErr_compiled =
  eval_cake_compile_x64 "" helloErr_prog_def "helloErr.S";

val _ = export_theory ();
