open preamble ml_translatorLib ml_progLib
open vectorTheory

val _ = new_theory"vectorProg"

val _ = translation_extends "listProg";

val _ = ml_prog_update (open_module "Vector");

val _ = append_dec ``Dtabbrev ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector)``;
val _ = trans "fromList" `Vector`
val _ = trans "length" `length`
val _ = trans "sub" `sub`



(*GENLIST_AUX and GENLIST_GENLIST_AUX should be translated in list *)
val result = translate tabulate_def;



val result = translate toList_aux_def;



val toList_aux_side_def = theorem"tolist_aux_side_def"

val toList_aux_side_thm = Q.prove(`∀vec n. tolist_aux_side vec n`,
  ho_match_mp_tac toList_aux_ind
  \\ metis_tac[GREATER_EQ,NOT_LESS_EQUAL,toList_aux_side_def])
  |> update_precondition

val result = translate toList_def;



val result = translate LUPDATE_def;
val result = translate update_def;



(*APPEND FLAT and MAP should be translated in list *)
val result = translate concat_def;



val result = translate map_def;
val map_1_side_def = definition"map_1_side_def";
val result = translate mapi_def;

val result = translate foldli_aux_def;
val result = translate foldli_def;

val result = translate foldl_aux_def;
val result = translate foldl_def;


val result = translate foldri_aux_def;
val result = translate foldri_def;

val result = translate foldr_aux_def;
val result = translate foldr_def;

val result = translate findi_aux_def;
val result = translate findi_def;

val result = translate find_aux_def;
val result = translate find_def;

val result = translate exists_aux_def;
val result = translate exists_def;

(*These have side conditions to do with sub and the definition may need to change *)
val result = translate all_aux_def;
val result = translate all_def;

val result = translate collate_aux_def;
val result = translate collate_def;



val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
