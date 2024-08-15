(*
  Evaluate the final part of the 32-bit version of the compiler
  into machine code for ag32, i.e. the Silver ISA.
*)
open preamble compiler32ProgTheory eval_cake_compile_ag32Lib;

val _ = new_theory "ag32Bootstrap";

Theorem compiler32_compiled =
  eval_cake_compile_ag32 "" compiler32_prog_def "cake.S";

val _ = export_theory();
