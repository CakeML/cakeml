(*
  Compiles the echo example by evaluation inside the logic of HOL
*)
open preamble echoProgTheory eval_cake_compile_x64Lib

val _ = new_theory "echoCompile"

Theorem echo_compiled =
  eval_cake_compile_x64 "" echo_prog_def "echo.S";

val _ = export_theory ();
