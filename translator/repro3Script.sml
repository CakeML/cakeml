(* Reproduce the ml_module_demo failure in a real theory. *)
Theory repro3
Libs
  ml_translatorLib ml_progLib

val _ = (use_full_type_names := false);

val _ = ml_prog_update (ml_progLib.open_module "Even");

Datatype:
  even = Even num
End

Definition zero_def:
  zero = Even 0
End
val r = translate zero_def;

val _ = ml_prog_update (ml_progLib.close_module NONE);
