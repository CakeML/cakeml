(*
  Evaluateof the 32-bit version of the compiler into x64 machine code.
*)
open preamble compiler32ProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "x64Bootstrap"

Theorem compiler32_compiled =
  eval_cake_compile_x64 "" compiler32_prog_def "cake.S";

val _ = export_theory ();
