(*
  Module about the option tyoe.
*)
open preamble ml_translatorLib ml_progLib RuntimeProgTheory
     mloptionTheory

val _ = new_theory"OptionProg"

val _ = translation_extends "RuntimeProg"

val () = generate_sigs := true;

val _ = ml_prog_update (open_module "Option");

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a"] "option" (Atapp [Atvar "'a"] (Short "option"))`` I);

val () = next_ml_names := ["getOpt"];
val result = translate getOpt_def;

val () = next_ml_names := ["isSome"];
val result = translate IS_SOME_DEF;

val result = next_ml_names := ["valOf"];
val result = translate THE_DEF;
val the_side_def = Q.prove(
  `the_side = IS_SOME`,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "the_side_def"])
  |> update_precondition;

val result = next_ml_names := ["join"];
val result = translate OPTION_JOIN_DEF;

val result = next_ml_names := ["map"];
val result = translate OPTION_MAP_DEF;

val () = next_ml_names := ["mapPartial"];
val result = translate (OPTION_BIND_def |> REWRITE_RULE[GSYM mapPartial_def]);

val result = translate compose_def;

val () = next_ml_names := ["composePartial"];
val result = translate composePartial_def;

val () = next_ml_names := ["isNone"];
val res = translate IS_NONE_DEF;

val () = next_ml_names := ["map2"];
val res = translate OPTION_MAP2_DEF;

val sigs = module_signatures [
  "option", (* TODO: is this the right way to add a datatype? *)
  "getOpt",
  "isSome",
  "valOf",
  "join",
  "map",
  "mapPartial",
  "compose",
  "composePartial",
  "isNone",
  "map2"
];

val _ = ml_prog_update (close_module (SOME sigs));
val _ = export_theory();
