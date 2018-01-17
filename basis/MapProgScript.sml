open preamble
  ml_translatorLib ml_translatorTheory ml_progLib
  balanced_mapTheory CompareProgTheory basisFunctionsLib

val _ = new_theory "MapProg"

val _ = translation_extends "CompareProg";

val _ = ml_prog_update (open_module "Map");

val _ = translate null_def;
val _ = translate lookup_def;
val _ = translate member_def;
val _ = translate empty_def;
val _ = translate singleton_def;
val _ = translate ratio_def;
val _ = translate size_def;
val _ = translate delta_def;
val _ = translate balanceL_def;
val _ = translate balanceR_def;
val _ = translate insert_def;
val _ = translate deleteFindMax_def;
val _ = translate deleteFindMin_def;
val _ = translate glue_def;
val _ = translate delete_def;
val _ = translate trim_help_greater_def;
val _ = translate trim_help_lesser_def;
val _ = translate trim_help_middle_def;
val _ = translate trim_def;
val _ = translate insertMin_def;
val _ = translate insertMax_def;
val _ = translate bin_def;
val _ = translate link_def;
val _ = translate filterLt_help_def;
val _ = translate filterLt_def;
val _ = translate filterGt_help_def;
val _ = translate filterGt_def;
val _ = translate insertR_def;
val _ = translate hedgeUnion_def;
val _ = translate union_def;
val _ = translate foldrWithKey_def;
val _ = translate toAscList_def;
val _ = translate compare_def;
val _ = translate map_def;
val _ = translate splitLookup_def;
val _ = translate submap'_def;
val _ = translate isSubmapOfBy_def;
val _ = translate isSubmapOf_def;
val _ = translate fromList_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();


