open HolKernel Parse boolLib bossLib; val _ = new_theory "mini_prelude";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;

val _ = register_type ``:'a # 'b``;

val res = translate HD;
val res = translate TL;
val res = translate APPEND;
val res = translate REV_DEF;
val res = translate REVERSE_REV;

val HD_side_def = prove(
  ``!xs. HD_side xs = ~(xs = [])``,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "HD_side_def"])
  |> update_precondition;

val TL_side_def = prove(
  ``!xs. TL_side xs = ~(xs = [])``,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "TL_side_def"])
  |> update_precondition;

val _ = export_theory();

