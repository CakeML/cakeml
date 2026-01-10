(*
  This module contains CakeML code implementing a functional set type
  using a self-balancing binary tree.
*)
Theory SetProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib
Ancestors
  ml_translator balanced_map MapProg mlset[qualified]

val _ = translation_extends "MapProg";

val _ = ml_prog_update open_local_block;

val _ = (use_full_type_names := false);
val _ = register_type ``:'a mlset$mlset``;
val _ = (use_full_type_names := true);

val _ = next_ml_names := ["size", "singleton"];
val _ = translate size_def;
val _ = translate singleton_def;

(* Helpers *)

val _ = translate FOLDL;
val _ = translate ratio_def;
val _ = translate delta_def;
val _ = translate balanceL_def;
val _ = translate balanceR_def;
val _ = translate deleteFindMax_def;

Theorem deleteFindmax_side_thm[local]:
  !m. m ≠ Tip ⇒ deletefindmax_side m
Proof
  ho_match_mp_tac deleteFindMax_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_side_def"] >>
  rw [] >>
  metis_tac []
QED
val _ = update_precondition deleteFindmax_side_thm;

val _ = translate deleteFindMin_def;

Theorem deleteFindmin_side_thm[local]:
  !m. m ≠ Tip ⇒ deletefindmin_side m
Proof
  ho_match_mp_tac deleteFindMin_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_side_def"] >>
  rw [] >>
  metis_tac []
QED
val _ = update_precondition deleteFindmin_side_thm;

val _ = translate glue_def;

Theorem glue_side_thm[local]:
  !m n. glue_side m n
Proof
  rw [fetch "-" "glue_side_def"] >>
  metis_tac [deleteFindmin_side_thm, deleteFindmax_side_thm,
             balanced_map_distinct]
QED
val _ = update_precondition glue_side_thm;

val _ = translate trim_help_greater_def;
val _ = translate trim_help_lesser_def;
val _ = translate trim_help_middle_def;
val _ = translate trim_def;
val _ = translate insertMin_def;
val _ = translate insertMax_def;
val _ = translate bin_def;
val _ = translate link_def;
val _ = translate link2_def;
val _ = translate filterLt_help_def;
val _ = translate filterLt_def;
val _ = translate filterGt_help_def;
val _ = translate filterGt_def;
val _ = translate insertR_def;
val _ = translate hedgeUnion_def;
val _ = next_ml_names := ["lookup"];
val _ = translate lookup_def;
val _ = translate hedgeUnionWithKey_def;
val _ = translate splitLookup_def;
val _ = translate submap'_def;

(* Exported functions *)
val _ = next_ml_names :=
  ["null", "member", "empty", "insert", "delete", "union", "foldrWithKey",
   "toAscList", "compare", "isSubmapOfBy", "isSubmapOf", "fromList",
   "filterWithKey", "all", "exists"];
val _ = translate null_def;
val _ = translate member_def;
val _ = translate empty_def;
val _ = translate insert_def;
val _ = translate delete_def;
val _ = translate union_def;
val _ = translate foldrWithKey_def;
val _ = translate toAscList_def;
val _ = translate compare_def;
val _ = translate isSubmapOfBy_def;
val _ = translate isSubmapOf_def;
val _ = translate fromList_def;
val _ = translate filterWithKey_def;
val _ = translate every_def;
val _ = translate exists_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (open_module "Set");

(* provides the Set.set name for the set type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [«'a»] «set» (Atapp [Atvar «'a»] (Short «mlset»))`` I);

val _ = next_ml_names := ["singleton"];
val _ = translate mlsetTheory.singleton_def;
val _ = next_ml_names := ["member"];
val _ = translate mlsetTheory.member_def;
val _ = next_ml_names := ["delete"];
val _ = translate mlsetTheory.delete_def;
val _ = next_ml_names := ["union"];
val _ = translate mlsetTheory.union_def;
val _ = next_ml_names := ["isSubset"];
val _ = translate mlsetTheory.isSubset_def;
val _ = next_ml_names := ["compare"];
val _ = translate mlsetTheory.compare_def;
val _ = next_ml_names := ["all"];
val _ = translate mlsetTheory.all_def;
val _ = next_ml_names := ["exists"];
val _ = translate mlsetTheory.exists_def;
val _ = next_ml_names := ["translate"];
val _ = translate mlsetTheory.translate_def;
val _ = next_ml_names := ["map"];
val _ = translate mlsetTheory.map_def;
val _ = next_ml_names := ["filter"];
val _ = translate mlsetTheory.filter_def;
val _ = next_ml_names := ["fromList"];
val _ = translate mlsetTheory.fromList_def;
val _ = next_ml_names := ["toList"];
val _ = translate mlsetTheory.toList_def;
val _ = next_ml_names := ["null"];
val _ = translate mlsetTheory.null_def;
val _ = next_ml_names := ["size"];
val _ = translate mlsetTheory.size_def;
val _ = next_ml_names := ["fold"];
val _ = translate mlsetTheory.fold_def;
val _ = next_ml_names := ["empty"];
val _ = translate mlsetTheory.empty_def;
val _ = next_ml_names := ["insert"];
val _ = translate mlsetTheory.insert_def;

val _ = ml_prog_update (close_module NONE);

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [«'a»] «set» (Atapp [Atvar «'a»] (Short «mlset»))`` I);

val _ = ml_prog_update close_local_block;

(* Remove all overloads introduced by loading mlset: *)
val _ = List.app (fn tm => let val {Name, Thy,...} = dest_thy_const tm
                           in remove_ovl_mapping Name {Name = Name, Thy = Thy}
                           end)
                 (constants "mlset");
