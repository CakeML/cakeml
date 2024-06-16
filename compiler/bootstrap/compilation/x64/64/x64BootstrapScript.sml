(*
  Evaluateof the 64-bit version of the compiler into x64 machine code.
*)
open preamble compiler64ProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "x64Bootstrap"

Theorem compiler64_compiled =
  eval_cake_compile_x64 "" compiler64_prog_def "cake.S";

val _ = export_theory ();
