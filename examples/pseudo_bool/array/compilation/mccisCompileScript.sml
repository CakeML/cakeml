(*
  Compiles the MCCIS + PB checker
*)
open preamble mccisProgTheory eval_cake_compile_x64Lib
                              eval_cake_compile_arm8Lib

val _ = new_theory "mccisCompile"

Theorem mccis_compiled =
  eval_cake_compile_x64 "" main_prog_def "cake_pb_mccis.S";

Theorem mccis_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" main_prog_def "cake_pb_mccis_arm8.S";

val _ = export_theory ();
