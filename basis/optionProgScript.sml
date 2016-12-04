open preamble ml_translatorLib ml_progLib
open optionTheory

(*this library depends on nothing *)
val _ = new_theory"optionProg"
val _ = ml_prog_update (open_module "Option");

val _ = append_dec ``Dtabbrev ["'a"] "option" (Tapp [Tvar "'a"] (TC_name (Short "option")))``;

val result = translate IS_SOME_DEF;

val result = translate getOpt_def;

val result = translate IS_SOME_DEF;

val result = next_ml_names := ["valOf"];
val result = translate THE_DEF;

val result = next_ml_names := ["join"];
val result = translate OPTION_JOIN_DEF;

val result = next_ml_names := ["map"];
val result = translate OPTION_MAP_DEF;

val result = translate (OPTION_BIND_def |> REWRITE_RULE[GSYM mapPartial_def]);

val result = translate compose_def;

val result = translate composePartial_def;

(*Functions declared in std_preludeLib *)
val result = translate IS_NONE_DEF;
val result = translate IS_OPTION_MAP2_DEF;

val res = translate THE_DEF;
val res = translate IS_NONE_DEF;
val res = translate IS_SOME_DEF;
val res = translate OPTION_MAP_DEF;
val res = translate OPTION_MAP2_DEF;

val the_side_def = Q.prove(
  `the_side = IS_SOME`,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "the_side_def"])
  |> update_precondition;

val option_map2_side_def = Q.prove(
  `!f x y. option_map2_side f x y = T`,
  FULL_SIMP_TAC (srw_ss()) [fetch "-" "option_map2_side_def",the_side_def])
  |> update_precondition;




val ml_prog_update (close_module NONE);
val _ = export_theory() 

