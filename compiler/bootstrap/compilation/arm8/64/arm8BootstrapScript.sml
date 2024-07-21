(*
  Evaluateof the 64-bit version of the compiler into arm8 machine code.
*)
open preamble compiler64ProgTheory eval_cake_compile_arm8Lib;

val _ = new_theory "arm8Bootstrap"

Theorem compiler64_compiled =
  eval_cake_compile_arm8 "" compiler64_prog_def "cake.S";

val _ = export_theory ();
