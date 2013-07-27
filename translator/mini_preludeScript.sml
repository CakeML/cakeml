open HolKernel Parse boolLib bossLib; val _ = new_theory "mini_prelude";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;

val _ = register_type ``:'a # 'b``;

val res = translate HD;
val res = translate TL;
val res = translate APPEND;

val res = translate REV_DEF;
val res = translate REVERSE_REV;

val hd_side_def = prove(
  ``!xs. hd_side xs = ~(xs = [])``,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "hd_side_def"])
  |> update_precondition;

val tl_side_def = prove(
  ``!xs. tl_side xs = ~(xs = [])``,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "tl_side_def"])
  |> update_precondition;

val _ = (print_asts := true);

val _ = export_theory();
