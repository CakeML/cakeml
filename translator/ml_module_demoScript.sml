open HolKernel Parse boolLib bossLib;
open ml_translatorLib;

val _ = new_theory "ml_module_demo";

val _ = (use_full_type_names := false);

val _ = translate_into_module "even";

val _ = Datatype `
  even = Even num`;

val zero_def = mlDefine `
  zero = Even 0`;

val two_def = mlDefine `
  two = Even 2`;

val add_def = mlDefine `
  add (Even m) (Even n) = Even (m + n)`;

val module_thm = finalise_module_translation ();

val _ = save_thm("module_thm", Q.SPEC `NONE` module_thm);

val _ = export_theory();
