(*
  Compiles the patch example by evaluation inside the logic of HOL
*)
open preamble patchProgTheory eval_cake_compile_x64Lib

val _ = new_theory "patchCompile"

Theorem patch_compiled =
  eval_cake_compile_x64 "" patch_prog_def "patch.S";

val _ = export_theory ();
