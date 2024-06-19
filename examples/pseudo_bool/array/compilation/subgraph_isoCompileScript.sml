(*
  Compiles the encoder
*)
open preamble subgraph_isoProgTheory eval_cake_compile_x64Lib
                                     eval_cake_compile_arm8Lib

val _ = new_theory "subgraph_isoCompile"

Theorem subgraph_iso_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_iso.S";

Theorem subgraph_iso_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_iso_arm8.S";

val _ = export_theory ();
