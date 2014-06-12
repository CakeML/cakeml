structure mini_preludeLib =
struct

open HolKernel Parse boolLib bossLib;
open listTheory pairTheory ml_translatorLib ml_translatorTheory;

fun mini_prelude () = let

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

in () end;

end
