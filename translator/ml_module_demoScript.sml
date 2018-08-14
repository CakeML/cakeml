(*
  Demonstration of using the translator to produce a CakeML module.
*)
open HolKernel Parse boolLib bossLib;
open ml_translatorLib ml_progLib;

val _ = new_theory "ml_module_demo";

val _ = (use_full_type_names := false);

val _ = ml_prog_update (open_module "Even");

val _ = Datatype `
  even = Even num`;

val zero_def = mlDefine `
  zero = Even 0`;

val two_def = mlDefine `
  two = Even 2`;

val add_def = mlDefine `
  add x y =
    case x of Even m => case y of Even n => Even (m + n)`;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
