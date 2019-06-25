(*
  Pure functions for the Map module.

  This file defines a wrapper around the balanced_map type. The new
  type is essentially a pair that carries the compare functions next
  to the tree so that users don't have to provide the compare function
  as an explicit argument everywhere.
*)
open preamble balanced_mapTheory

val _ = set_grammar_ancestry ["balanced_map"];
val _ = ParseExtras.tight_equality();

val _ = new_theory"mlmap"

(* implementation definitions *)

val _ = Datatype `
  map = Map ('a -> 'a -> ordering) (('a, 'b) balanced_map)`;

val lookup_def = Define `
  lookup (Map cmp t) k = balanced_map$lookup cmp k t`

val insert_def = Define `
  insert (Map cmp t) k v = Map cmp (balanced_map$insert cmp k v t)`

val delete_def = Define `
  delete (Map cmp t) k = Map cmp (balanced_map$delete cmp k t)`

val null_def = Define `
  null (Map cmp t) = balanced_map$null t`

val empty_def = Define `
  empty cmp = Map cmp balanced_map$empty`

val union_def = Define `
  union (Map cmp t1) (Map _ t2) = Map cmp (balanced_map$union cmp t1 t2)`

val foldrWithKey_def = Define `
  foldrWithKey f x (Map cmp t) = balanced_map$foldrWithKey f x t`;

val map_def = Define `
  map f (Map cmp t) = Map cmp (balanced_map$map f t)`;

val toAscList_def = Define `
  toAscList (Map cmp t) = balanced_map$toAscList t`;

val fromList_def = Define `
  fromList cmp l = Map cmp (balanced_map$fromList cmp l)`;

val isSubmapBy_def = Define `
  isSubmapBy f (Map cmp t1) (Map _ t2) = balanced_map$isSubmapOfBy cmp f t1 t2`

val isSubmap_def = Define `
  isSubmap m1 m2 = isSubmapBy (=) m1 m2`;

(* definitions for proofs *)

val map_ok_def = Define `
  map_ok (Map cmp t) <=> balanced_map$invariant cmp t /\ TotOrd cmp`;

val cmp_of_def = Define `
  cmp_of (Map cmp t) = cmp`;

val to_fmap_def = Define `
  to_fmap (Map cmp Tip) = FEMPTY /\
  to_fmap (Map cmp (Bin s k v l r)) =
    ((to_fmap (Map cmp l) ⊌ to_fmap (Map cmp r)) |+ (k,v))`;

(* theorems *)

Theorem lookup_insert:
   map_ok t ==>
   lookup (insert t k1 v) k2 = if k1 = k2 then SOME v else lookup t k2
Proof
 Cases_on `t`
  \\ fs [map_ok_def,balanced_mapTheory.lookup_insert,lookup_def,insert_def,
         comparisonTheory.TotOrder_imp_good_cmp]
  \\ metis_tac [totoTheory.TotOrd]
QED

Theorem cmp_of_insert[simp]:
   cmp_of (insert t k v) = cmp_of t
Proof
  Cases_on `t` \\ fs [insert_def,cmp_of_def]
QED

Theorem cmp_of_empty[simp]:
   cmp_of (empty cmp) = cmp
Proof
  fs [empty_def,cmp_of_def]
QED

val fmap_FLOOKUP_EQ = prove(
  ``f1 = f2 <=> FLOOKUP f1 = FLOOKUP f2``,
  fs [GSYM fmap_EQ_THM,FLOOKUP_DEF,FUN_EQ_THM]
  \\ eq_tac \\ rw []
  THEN1 metis_tac [SOME_11,NOT_NONE_SOME]
  \\ first_x_assum (qspec_then `x` mp_tac)
  \\ rw [] \\ fs [IN_DEF]);

Theorem TotOrd_key_set[simp]:
   TotOrd cmp ==> key_set cmp k = {k}
Proof
  rw[key_set_def,EXTENSION] \\ metis_tac [totoTheory.TotOrd]
QED

Theorem to_fmap_thm:
   !t cmp.
     TotOrd cmp ==>
     to_fmap cmp t = MAP_KEYS (\x. {x}) (to_fmap (Map cmp t))
Proof
  Induct \\ fs [to_fmap_def,balanced_mapTheory.to_fmap_def]
  \\ rw [] \\ rw [fmap_FLOOKUP_EQ,FUN_EQ_THM]
  \\ fs [FLOOKUP_UPDATE,FLOOKUP_FUNION]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ fs [FLOOKUP_MAP_KEYS]
  \\ fs [FLOOKUP_UPDATE,FLOOKUP_FUNION,Abbr `ff`]
  \\ IF_CASES_TAC \\ fs [] \\ rveq
  THEN1
   (qexists_tac `k` \\ fs []
    \\ fs [FLOOKUP_UPDATE,FLOOKUP_FUNION]
    \\ `!f1 f2 v. k = v /\ (v = k \/ f1 v \/ f2 v) <=> k = v` by metis_tac []
    \\ fs [])
  \\ Cases_on `?y. x = {y}` \\ fs [] \\ rveq \\ fs []
  \\ once_rewrite_tac [METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``]
  \\ simp []
  \\ rewrite_tac [GSYM (METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``)]
  \\ Cases_on `y ∈ FDOM (to_fmap (Map cmp t))` \\ fs []
  \\ Cases_on `y ∈ FDOM (to_fmap (Map cmp t'))` \\ fs []
  \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,FUNION_DEF]
QED

Theorem empty_thm:
   (map_ok (empty cmp) = TotOrd cmp) /\ to_fmap (empty cmp) = FEMPTY
Proof
  fs [empty_def,map_ok_def,balanced_mapTheory.empty_thm,
      to_fmap_def,balanced_mapTheory.empty_def,balanced_mapTheory.invariant_def]
QED

Theorem MAP_KEYS_sing_set:
   MAP_KEYS (λx. {x}) f1 = MAP_KEYS (λx. {x}) f2 <=> (f1 = f2)
Proof
  eq_tac \\ fs [] \\ fs [fmap_FLOOKUP_EQ]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS]
  \\ fs [Abbr `ff`] \\ rw []
  \\ first_x_assum (qspec_then `{x}` mp_tac) \\ fs []
  \\ `!f1 v. x = v /\ f1 v <=> x = v /\ f1 x` by metis_tac [] \\ fs []
  \\ Cases_on `x ∈ FDOM f1` \\ fs []
  \\ Cases_on `x ∈ FDOM f2` \\ fs [FLOOKUP_DEF]
QED

Theorem MAP_KEYS_sing_set_UPDATE:
   MAP_KEYS (λx. {x}) f |+ ({k},v) = MAP_KEYS (λx. {x}) (f |+ (k,v))
Proof
  fs [fmap_FLOOKUP_EQ]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS,FLOOKUP_UPDATE]
  \\ fs [Abbr `ff`] \\ rw [] \\ fs []
  \\ `!f1 v. k = v /\ f1 v <=> k = v /\ f1 k` by metis_tac [] \\ fs []
  \\ fs [FLOOKUP_UPDATE]
  \\ Cases_on `?y. x = {y}` \\ fs [] \\ rveq \\ fs []
  \\ pop_assum kall_tac
  \\ once_rewrite_tac [METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``]
  \\ simp []
  \\ rewrite_tac [GSYM (METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``)]
  \\ Cases_on `y ∈ FDOM f` \\ fs [FLOOKUP_UPDATE]
QED

Theorem insert_thm:
   map_ok t ==>
   map_ok (insert t k v) /\
   to_fmap (insert t k v) = (to_fmap t |+ (k, v))
Proof
  Cases_on `t`
  \\ strip_tac
  \\ conj_asm1_tac
  THEN1
   (fs [map_ok_def,insert_def]
    \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
    \\ fs [balanced_mapTheory.insert_thm])
  \\ fs [map_ok_def,insert_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ imp_res_tac balanced_mapTheory.insert_thm
  \\ rfs [to_fmap_thm,MAP_KEYS_sing_set_UPDATE,MAP_KEYS_sing_set]
QED

Theorem lookup_thm:
   map_ok t ==> lookup t k = FLOOKUP (to_fmap t) k
Proof
  Cases_on `t`
  \\ strip_tac
  \\ fs [map_ok_def,lookup_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ imp_res_tac balanced_mapTheory.lookup_thm \\ fs []
  \\ rfs [to_fmap_thm,MAP_KEYS_sing_set]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS]
  \\ fs [Abbr`ff`]
  \\ `!f1 v. k = v /\ f1 v <=> k = v /\ f1 k` by metis_tac [] \\ fs []
  \\ Cases_on `k ∈ FDOM (to_fmap (Map f b))` \\ fs []
  \\ fs [FLOOKUP_DEF]
QED

Theorem MAP_FST_toAscList:
   map_ok t ⇒
   SORTED (λx y. cmp_of t x y = Less) (MAP FST (toAscList t)) ∧
   FDOM (to_fmap t) = set (MAP FST (toAscList t))
Proof
  Cases_on `t` \\ fs [map_ok_def,lookup_def] \\ strip_tac
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ imp_res_tac balanced_mapTheory.MAP_FST_toAscList
  \\ rfs [cmp_of_def,toAscList_def,to_fmap_thm,MAP_KEYS_def]
  \\ `(λx. {x}) = key_set f` by fs [FUN_EQ_THM] \\ fs []
  \\ `(∀x y. key_set f x = key_set f y ⇔ x = y)` by fs []
  \\ drule (GEN_ALL pred_setTheory.IMAGE_11)
  \\ strip_tac \\ fs []
QED

Theorem MEM_toAscList:
   map_ok t /\ MEM (k,v) (toAscList t) ==> FLOOKUP (to_fmap t) k = SOME v
Proof
  Cases_on `t` \\ fs [map_ok_def,lookup_def,toAscList_def] \\ strip_tac
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ imp_res_tac balanced_mapTheory.MEM_toAscList
  \\ rfs [toAscList_def,to_fmap_thm]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS]
  \\ fs [Abbr`ff`]
  \\ `!f1 v. k = v /\ f1 v <=> k = v /\ f1 k` by metis_tac [] \\ fs []
  \\ Cases_on `k ∈ FDOM (to_fmap (Map f b))` \\ fs []
  \\ fs [FLOOKUP_DEF]
QED

val _ = export_theory()
