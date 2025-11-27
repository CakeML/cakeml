(*
  Demonstration of using the translator to produce a CakeML module.
*)
Theory ml_module_demo
Libs
  ml_translatorLib ml_progLib

val _ = (use_full_type_names := false);

val _ = ml_prog_update (open_module "Even");

Datatype:
  even = Even num
End

Definition zero_def:
  zero = Even 0
End
val r = translate zero_def;

Definition two_def:
  two = Even 2
End
val r = translate two_def;

Definition add_def:
  add x y =
    case x of Even m => case y of Even n => Even (m + n)
End
val r = translate add_def;

val _ = ml_prog_update (close_module NONE);
