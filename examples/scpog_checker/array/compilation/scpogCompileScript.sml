(*
  Compiles the scpog example by evaluation inside the logic of HOL
*)
open preamble scpog_arrayFullProgTheory
  eval_cake_compile_x64Lib eval_cake_compile_arm8Lib;

val _ = new_theory "scpogCompile"

Definition x64_config'_def:
  x64_config' =
  let x64_data_conf = x64_backend_config.data_conf with gc_kind := Generational [125000000] in
    x64_backend_config with <| data_conf := x64_data_conf |>
End

Definition arm8_config'_def:
  arm8_config' =
  let arm8_data_conf = arm8_backend_config.data_conf with gc_kind := Generational [125000000] in
    arm8_backend_config with <| data_conf := arm8_data_conf |>
End

Theorem scpog_compiled =
  eval_cake_compile_x64_with_conf "" x64_config'_def main_prog_def "cake_scpog.S";

Theorem scpog_compiled_arm8 =
  eval_cake_compile_arm8_with_conf "arm8_" arm8_config'_def main_prog_def "cake_scpog_arm8.S";

val _ = export_theory ();
