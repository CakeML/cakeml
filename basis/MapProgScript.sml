(*
  This module contains CakeML code implementing a functional map type
  using a self-balancing binary tree.
*)
Theory MapProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib
Ancestors
  ml_translator balanced_map ArrayProg

val _ = translation_extends "ArrayProg";

val _ = (use_full_type_names := false);
val _ = register_type ``:('a,'b) balanced_map$balanced_map``;
val _ = (use_full_type_names := true);

val _ = (use_full_type_names := false);
val _ = register_type ``:('a,'b) mlmap$map``;
val _ = (use_full_type_names := true);

val _ = ml_prog_update open_local_block;

val _ = next_ml_names := ["size", "singleton"];
val _ = translate size_def;
val _ = translate singleton_def;

(* Helpers *)
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
  ["null", "member", "empty", "insert", "delete",
   "union", "unionWithKey", "unionWith", "foldrWithKey",
   "toAscList", "compare", "mapWithKey", "map", "isSubmapOfBy",
   "isSubmapOf", "fromList", "filterWithKey", "filter", "all",
   "exists"];
val _ = translate null_def;
val _ = translate member_def;
val _ = translate empty_def;
val _ = translate insert_def;
val _ = translate delete_def;
val _ = translate union_def;
val _ = translate unionWithKey_def;
val _ = translate unionWith_def;
val _ = translate foldrWithKey_def;
val _ = translate toAscList_def;
val _ = translate compare_def;
val _ = translate mapWithKey_def;
val _ = translate map_def;
val _ = translate isSubmapOfBy_def;
val _ = translate isSubmapOf_def;
val _ = translate fromList_def;
val _ = translate filterWithKey_def;
val _ = translate filter_def;
val _ = translate every_def;
val _ = translate exists_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (open_module "Map");

(* provides the Map.map name for the map type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [«'a»;«'b»] «map»
             (Atapp [Atvar «'a»; Atvar «'b»] (Short «map»))`` I);

val _ = next_ml_names := ["lookup"];
val mlmap_lookup_v_thm = translate mlmapTheory.lookup_def;
val _ = next_ml_names := ["member"];
val _ = translate mlmapTheory.member_def;
val _ = next_ml_names := ["insert"];
val mlmap_insert_v_thm = translate mlmapTheory.insert_def;
val _ = next_ml_names := ["delete"];
val mlmap_delete_v_thm = translate mlmapTheory.delete_def;
val _ = next_ml_names := ["null"];
val _ = translate mlmapTheory.null_def;
val _ = next_ml_names := ["size"];
val _ = translate mlmapTheory.size_def;
val _ = next_ml_names := ["empty"];
val _ = translate mlmapTheory.empty_def;
val _ = next_ml_names := ["singleton"];
val _ = translate mlmapTheory.singleton_def;
val _ = next_ml_names := ["union"];
val mlmap_union_v_thm = translate mlmapTheory.union_def;
val _ = next_ml_names := ["unionWith"];
val _ = translate mlmapTheory.unionWith_def;
val _ = next_ml_names := ["unionWithKey"];
val _ = translate mlmapTheory.unionWithKey_def;
val _ = next_ml_names := ["foldrWithKey"];
val _ = translate mlmapTheory.foldrWithKey_def;
val _ = next_ml_names := ["map"];
val _ = translate mlmapTheory.map_def;
val _ = next_ml_names := ["mapWithKey"];
val _ = translate mlmapTheory.mapWithKey_def;
val _ = next_ml_names := ["toAscList"];
val _ = translate mlmapTheory.toAscList_def;
val _ = next_ml_names := ["fromList"];
val _ = translate mlmapTheory.fromList_def;
val _ = next_ml_names := ["isSubmapBy"];
val _ = translate mlmapTheory.isSubmapBy_def;
val _ = next_ml_names := ["isSubmap"];
val _ = translate mlmapTheory.isSubmap_def;
val _ = next_ml_names := ["all"];
val _ = translate mlmapTheory.all_def;
val _ = next_ml_names := ["exists"];
val _ = translate mlmapTheory.exists_def;
val _ = next_ml_names := ["filterWithKey"];
val _ = translate mlmapTheory.filterWithKey_def;
val _ = next_ml_names := ["filter"];
val _ = translate mlmapTheory.filter_def;
val _ = next_ml_names := ["compare"];
val _ = translate mlmapTheory.compare_def;

val _ = ml_prog_update (close_module NONE);

(* this is here so that the type name is accessible without the full name *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [«'a»;«'b»] «map»
             (Atapp [Atvar «'a»; Atvar «'b»] (Short «map»))`` I);

val _ = ml_prog_update close_local_block;

(*----------------------------------------------------------------------*
   general tooling for adding mlmap support for fmaps
 *----------------------------------------------------------------------*)

Definition FMAP_TYPE_def:
  FMAP_TYPE cmp a b f v =
    ∃m. mlmap$map_ok m ∧ mlmap$to_fmap m = f ∧ MAP_TYPE a b m v ∧
        mlmap$cmp_of m = cmp
End

Theorem MAP_TYPE_empty_IMP_FMAP_TYPE[local]:
  MAP_TYPE a b (mlmap$empty cmp) v ∧ TotOrd cmp ⇒
  FMAP_TYPE cmp a b FEMPTY v
Proof
  rw [FMAP_TYPE_def]
  \\ last_x_assum $ irule_at Any
  \\ fs [mlmapTheory.empty_thm]
QED

Theorem IMP_FMAP_TYPE_FLOOKUP[local]:
  (MAP_TYPE b a --> b --> OPTION_TYPE a) mlmap$lookup v ⇒
  (FMAP_TYPE cmp b a --> b --> OPTION_TYPE a) FLOOKUP v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def]
  \\ rw [] \\ simp [GSYM (mlmapTheory.lookup_thm)]
QED

Theorem IMP_FMAP_TYPE_FUPDATE[local]:
  (MAP_TYPE b a --> (b:'a -> v -> bool) --> a --> MAP_TYPE b a) mlmap$insert v ⇒
  (FMAP_TYPE cmp b a --> b --> a --> FMAP_TYPE cmp b a) fmap_update v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ fs [fmap_update_def]
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.insert_thm]
QED

Theorem IMP_FMAP_TYPE_DOMSUB[local]:
  (MAP_TYPE b a --> (b:'a -> v -> bool) --> MAP_TYPE b a) mlmap$delete v ⇒
  (FMAP_TYPE cmp b a --> b --> FMAP_TYPE cmp b a) $\\ v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.delete_thm]
QED

Theorem IMP_FMAP_TYPE_FUNION[local]:
  (MAP_TYPE b a --> MAP_TYPE b a --> MAP_TYPE b a) mlmap$union v ⇒
  (FMAP_TYPE cmp b a --> FMAP_TYPE cmp b a --> FMAP_TYPE cmp b a) FUNION v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.union_thm]
QED

Theorem IMP_FMAP_TYPE_ops:
  MAP_TYPE (key:'k -> v -> bool) (a:'a -> v -> bool) (mlmap$empty cmp) v ∧ TotOrd cmp ⇒
  FMAP_TYPE cmp key a FEMPTY v ∧
  ((MAP_TYPE key a --> key --> OPTION_TYPE a) mlmap$lookup v1 ⇒
   (FMAP_TYPE cmp key a --> key --> OPTION_TYPE a) FLOOKUP v1) ∧
  ((MAP_TYPE key a --> key --> a --> MAP_TYPE key a) mlmap$insert v1 ⇒
   (FMAP_TYPE cmp key a --> key --> a --> FMAP_TYPE cmp key a) fmap_update v1) ∧
  ((MAP_TYPE key a --> key --> MAP_TYPE key a) mlmap$delete v1 ⇒
   (FMAP_TYPE cmp key a --> key --> FMAP_TYPE cmp key a) $\\ v1) ∧
  ((MAP_TYPE key a --> MAP_TYPE key a --> MAP_TYPE key a) mlmap$union v1 ⇒
   (FMAP_TYPE cmp key a --> FMAP_TYPE cmp key a --> FMAP_TYPE cmp key a) FUNION v1)
Proof
  rw []
  >- (irule MAP_TYPE_empty_IMP_FMAP_TYPE \\ simp [])
  >- (irule IMP_FMAP_TYPE_FLOOKUP \\ simp [])
  >- (irule IMP_FMAP_TYPE_FUPDATE \\ simp [])
  >- (irule IMP_FMAP_TYPE_DOMSUB \\ simp [])
  >- (irule IMP_FMAP_TYPE_FUNION \\ simp [])
QED

Theorem mlmap_op_v_thms =
  LIST_CONJ [mlmap_lookup_v_thm,
             mlmap_union_v_thm,
             mlmap_delete_v_thm,
             mlmap_insert_v_thm];
