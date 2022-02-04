(*
  Compiles the test
*)

open preamble compilationLib testProgTheory;

val _ = new_theory "testCompile"

Theorem test_compiled =
  compile_x64 "testtest" test_prog_def;

val _ = export_theory ();
