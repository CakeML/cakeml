(*
  This module contains CakeML code implementing a functional map type
  using a self-balancing binary tree.
*)
open preamble
  ml_translatorLib ml_translatorTheory ml_progLib
  balanced_mapTheory ArrayProgTheory basisFunctionsLib

val _ = new_theory "MapProg"

val _ = translation_extends "ArrayProg";

val _ = (use_full_type_names := false);
val _ = register_type ``:('a,'b) balanced_map$balanced_map``;
val _ = (use_full_type_names := true);

val _ = ml_prog_update open_local_block;

val _ = (use_full_type_names := false);
val _ = register_type ``:('a,'b) mlmap$map``;
val _ = (use_full_type_names := true);

val _ = next_ml_names := ["size", "singleton"];
val _ = translate size_def;
val _ = translate singleton_def;

(* Helpers *)
val _ = translate ratio_def;
val _ = translate delta_def;
val _ = translate balanceL_def;
val _ = translate balanceR_def;
val _ = translate deleteFindMax_def;

val deleteFindmax_side_thm = Q.prove (
  `!m. m ≠ Tip ⇒ deletefindmax_side m`,
  ho_match_mp_tac deleteFindMax_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_side_def"] >>
  rw [] >>
  metis_tac []) |> update_precondition;

val _ = translate deleteFindMin_def;

val deleteFindmin_side_thm = Q.prove (
  `!m. m ≠ Tip ⇒ deletefindmin_side m`,
  ho_match_mp_tac deleteFindMin_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_side_def"] >>
  rw [] >>
  metis_tac []) |> update_precondition;

val _ = translate glue_def;

val glue_side_thm = Q.prove (
  `!m n. glue_side m n`,
  rw [fetch "-" "glue_side_def"] >>
  metis_tac [deleteFindmin_side_thm, deleteFindmax_side_thm, balanced_map_distinct]) |> update_precondition;

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
val _ = translate splitLookup_def;
val _ = translate submap'_def;

(* Exported functions *)
val _ = next_ml_names :=
  ["null", "lookup", "member", "empty", "insert", "delete",
            "union", "foldrWithKey", "toAscList", "compare", "map",
            "isSubmapOfBy", "isSubmapOf", "fromList"];
val _ = translate null_def;
val _ = translate lookup_def;
val _ = translate member_def;
val _ = translate empty_def;
val _ = translate insert_def;
val _ = translate delete_def;
val _ = translate union_def;
val _ = translate foldrWithKey_def;
val _ = translate toAscList_def;
val _ = translate compare_def;
val _ = translate map_def;
val _ = translate isSubmapOfBy_def;
val _ = translate isSubmapOf_def;
val _ = translate fromList_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (open_module "Map");

(* provides the Map.map name for the map type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a";"'b"] "map" (Atapp [Atvar "'a"; Atvar "'b"] (Short "map"))`` I);

val _ = next_ml_names := ["lookup"];
val _ = translate mlmapTheory.lookup_def;
val _ = next_ml_names := ["insert"];
val _ = translate mlmapTheory.insert_def;
val _ = next_ml_names := ["delete"];
val _ = translate mlmapTheory.delete_def;
val _ = next_ml_names := ["null"];
val _ = translate mlmapTheory.null_def;
val _ = next_ml_names := ["empty"];
val _ = translate mlmapTheory.empty_def;
val _ = next_ml_names := ["union"];
val _ = translate mlmapTheory.union_def;
val _ = next_ml_names := ["foldrWithKey"];
val _ = translate mlmapTheory.foldrWithKey_def;
val _ = next_ml_names := ["map"];
val _ = translate mlmapTheory.map_def;
val _ = next_ml_names := ["toAscList"];
val _ = translate mlmapTheory.toAscList_def;
val _ = next_ml_names := ["fromList"];
val _ = translate mlmapTheory.fromList_def;
val _ = next_ml_names := ["isSubmapBy"];
val _ = translate mlmapTheory.isSubmapBy_def;
val _ = next_ml_names := ["isSubmap"];
val _ = translate mlmapTheory.isSubmap_def;

val _ = ml_prog_update (close_module NONE);

(* this is here so that the type name is accessible without the full name *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a";"'b"] "map" (Atapp [Atvar "'a"; Atvar "'b"] (Short "map"))`` I);

val _ = ml_prog_update close_local_block;

val _ = export_theory ();
