(*
  Pure functions for the Map module.
  This file defines a wrapper around the balanced_map type. The new
  type is essentially a pair that carries the compare functions next
  to the tree so that users don't have to provide the compare function
  as an explicit argument everywhere.
*)
Theory mlmap
Ancestors
  balanced_map
Libs
  preamble

val _ = ParseExtras.tight_equality();

val _ = temp_delsimps ["NORMEQ_CONV"]

(* implementation definitions *)

Datatype:
  map = Map ('a -> 'a -> ordering) (('a, 'b) balanced_map)
End

Definition lookup_def:
  lookup (Map cmp t) k = balanced_map$lookup cmp k t
End

Definition insert_def:
  insert (Map cmp t) k v = Map cmp (balanced_map$insert cmp k v t)
End

Definition delete_def:
  delete (Map cmp t) k = Map cmp (balanced_map$delete cmp k t)
End

Definition null_def:
  null (Map cmp t) = balanced_map$null t
End

Definition size_def:
  size (Map cmp t) = balanced_map$size t
End

Definition empty_def:
  empty cmp = Map cmp balanced_map$empty
End

Definition union_def:
  union (Map cmp t1) (Map _ t2) = Map cmp (balanced_map$union cmp t1 t2)
End

Definition unionWith_def:
  unionWith f (Map cmp t1) (Map _ t2) =
    Map cmp (balanced_map$unionWith cmp f t1 t2)
End

Definition unionWithKey_def:
  unionWithKey f (Map cmp t1) (Map _ t2) =
    Map cmp (balanced_map$unionWithKey cmp f t1 t2)
End

Definition foldrWithKey_def:
  foldrWithKey f x (Map cmp t) = balanced_map$foldrWithKey f x t
End

Definition filter_def:
  filter p (Map cmp t) = Map cmp (balanced_map$filter p t)
End

Definition filterWithKey_def:
  filterWithKey p (Map cmp t) = Map cmp (balanced_map$filterWithKey p t)
End

Definition map_def:
  map f (Map cmp t) = Map cmp (balanced_map$map f t)
End

Definition mapWithKey_def:
  mapWithKey f (Map cmp t) = Map cmp (balanced_map$mapWithKey f t)
End

Definition toAscList_def:
  toAscList (Map cmp t) = balanced_map$toAscList t
End

Definition fromList_def:
  fromList cmp l = Map cmp (balanced_map$fromList cmp l)
End

Definition isSubmapBy_def:
  isSubmapBy f (Map cmp t1) (Map _ t2) = balanced_map$isSubmapOfBy cmp f t1 t2
End

Definition isSubmap_def:
  isSubmap m1 m2 = isSubmapBy (=) m1 m2
End

Definition all_def:
  all f (Map cmp t) = balanced_map$every f t
End

Definition exists_def:
  exists f (Map cmp t) = balanced_map$exists f t
End

Definition member_def:
  member k (Map cmp t) = balanced_map$member cmp k t
End

Definition singleton_def:
  singleton cmp k v = Map cmp (balanced_map$singleton k v)
End

Definition compare_def:
  compare vcmp (Map cmp m1: ('a, 'b) map) (Map _ m2: ('a, 'b) map) =
    balanced_map$compare cmp vcmp m1 m2
End

(* definitions for proofs *)

Definition map_ok_def:
  map_ok (Map cmp t) <=> balanced_map$invariant cmp t /\ TotOrd cmp
End

Definition cmp_of_def:
  cmp_of (Map cmp t) = cmp
End

Definition to_fmap_def:
  to_fmap (Map cmp Tip) = FEMPTY /\
  to_fmap (Map cmp (Bin s k v l r)) =
    ((to_fmap (Map cmp l) ⊌ to_fmap (Map cmp r)) |+ (k,v))
End

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

Theorem lookup_delete:
  map_ok t ==>
  lookup (delete t k1) k2 = if k1 = k2 then NONE else lookup t k2
Proof
  Cases_on `t`
  \\ fs[delete_def, map_ok_def]
  \\ rpt strip_tac
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\SUBGOAL_THEN ``!cmp. good_cmp cmp ∧ invariant cmp b ⇒
                  balanced_map$lookup cmp k2 (balanced_map$delete cmp k1 b) =
                  if cmp k1 k2 = Equal then NONE else balanced_map$lookup cmp k2 b``
                      assume_tac
  >-(rw[]
    >-(imp_res_tac balanced_mapTheory.delete_thm
      \\fs[balanced_mapTheory.lookup_thm]
      \\ rfs[GSYM DRESTRICT_DOMSUB]
      \\ rfs[DRESTRICT_FDOM]
      \\ fs[DOMSUB_FLOOKUP_THM]
      \\ metis_tac[balanced_mapTheory.key_set_eq,comparisonTheory.cmp_thms])
    >-(imp_res_tac balanced_mapTheory.delete_thm
      \\fs[balanced_mapTheory.lookup_thm]
      \\ rfs[GSYM DRESTRICT_DOMSUB]
      \\ rfs[DRESTRICT_FDOM]
      \\ fs[DOMSUB_FLOOKUP_THM]
      \\ metis_tac[balanced_mapTheory.key_set_eq,comparisonTheory.cmp_thms]))
  \\ res_tac
  \\ fs [lookup_def]
  \\ metis_tac [totoTheory.TotOrd]
QED

Theorem cmp_of_insert[simp]:
  cmp_of (insert t k v) = cmp_of t
Proof
  Cases_on `t` \\ fs [insert_def,cmp_of_def]
QED

Theorem cmp_of_delete[simp]:
  cmp_of (delete t k) = cmp_of t
Proof
  Cases_on `t` \\ fs [delete_def,cmp_of_def]
QED

Theorem cmp_of_empty[simp]:
  cmp_of (empty cmp) = cmp
Proof
  fs [empty_def,cmp_of_def]
QED

Theorem fmap_FLOOKUP_EQ[local]:
    f1 = f2 <=> FLOOKUP f1 = FLOOKUP f2
Proof
  fs [GSYM fmap_EQ_THM,FLOOKUP_DEF,FUN_EQ_THM]
  \\ eq_tac \\ rw []
  THEN1 metis_tac [SOME_11,NOT_NONE_SOME]
  \\ first_x_assum (qspec_then `x` mp_tac)
  \\ rw [] \\ fs [IN_DEF]
QED

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

Theorem size_thm:
  map_ok t ⇒
    size t = FCARD (to_fmap t)
Proof
  Cases_on ‘t’
  \\ rw [map_ok_def, size_def]
  \\ drule_then assume_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ drule_all_then assume_tac balanced_mapTheory.size_thm \\ gs []
  \\ simp [to_fmap_thm, FCARD_DEF, MAP_KEYS_def]
  \\ irule INJ_CARD_IMAGE \\ gs []
  \\ qmatch_goalsub_abbrev_tac ‘INJ _ x’
  \\ qexists_tac ‘IMAGE (λx. {x}) x’
  \\ simp [INJ_DEF]
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

Theorem MAP_KEYS_sing_set_DOMSUB:
  MAP_KEYS (λx. {x}) f \\ {k} = MAP_KEYS (λx. {x}) (f \\ k)
Proof
  fs [finite_mapTheory.fmap_eq_flookup]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS,DOMSUB_FLOOKUP_THM]
  \\ fs [Abbr `ff`] \\ rw [] \\ fs []
  \\ `!f1 v. k = v /\ f1 v <=> k = v /\ f1 k` by metis_tac [] \\ fs []
  \\ Cases_on `?y. x = {y}` \\ fs [] \\ rveq \\ fs []
  \\ once_rewrite_tac [METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``]
  \\ simp []
  \\ rewrite_tac [GSYM (METIS_PROVE [] ``x = y /\ p <=> x = y /\ (y = x ==> p)``)]
  \\ Cases_on `y ∈ FDOM f` \\ fs [DOMSUB_FLOOKUP_THM]
QED

Theorem MAP_KEYS_sing_set_FUNION:
   MAP_KEYS (λx. {x}) f1 ⊌ MAP_KEYS (λx. {x}) f2 =
   MAP_KEYS (λx. {x}) (f1 ⊌ f2)
Proof
  fs [finite_mapTheory.fmap_eq_flookup]
  \\ qmatch_goalsub_abbrev_tac `MAP_KEYS ff`
  \\ `!x. INJ ff x UNIV` by fs [INJ_DEF,Abbr`ff`]
  \\ simp [FUN_EQ_THM] \\ simp [FLOOKUP_MAP_KEYS,FLOOKUP_FUNION]
  \\ fs [Abbr `ff`] \\ rw [] \\ fs []
  \\ Cases_on `x` \\ fs []
  \\ reverse (Cases_on `t`)
  THEN1 (`!y. x' INSERT x INSERT t' <> {y}` by
          (fs [EXTENSION,IN_INSERT] \\ metis_tac []) \\ fs [])
  \\ fs []
  \\ `!f1 v. x' = v /\ f1 v <=> x' = v /\ f1 x'` by metis_tac [] \\ fs []
  \\ Cases_on `x' ∈ FDOM f1` \\ fs []
  THEN1 fs [FLOOKUP_DEF,FUNION_DEF]
  \\ Cases_on `x' ∈ FDOM f2` \\ fs []
  THEN1 fs [FLOOKUP_DEF,FUNION_DEF]
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

Theorem delete_thm:
   map_ok t ==>
   map_ok (delete t k) /\
   to_fmap (delete t k) = (to_fmap t \\ k)
Proof
  Cases_on `t`
  \\ strip_tac
  \\ conj_asm1_tac
  THEN1
   (fs [map_ok_def,delete_def]
    \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
    \\ fs [balanced_mapTheory.delete_thm])
  \\ fs [map_ok_def,delete_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ imp_res_tac balanced_mapTheory.delete_thm
  \\ rfs[GSYM DRESTRICT_DOMSUB]
  \\ rfs[DRESTRICT_FDOM]
  \\ rfs [to_fmap_thm,MAP_KEYS_sing_set_DOMSUB,MAP_KEYS_sing_set]
QED

Theorem union_thm:
   map_ok t1 /\ map_ok t2 /\ cmp_of t1 = cmp_of t2 ==>
   map_ok (union t1 t2) /\
   cmp_of (union t1 t2) = cmp_of t1 /\
   to_fmap (union t1 t2) = to_fmap t1 ⊌ to_fmap t2
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ fs [cmp_of_def]
  \\ strip_tac \\ rveq
  \\ fs [union_def]
  \\ conj_asm1_tac
  THEN1
   (fs [map_ok_def]
    \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
    \\ fs [balanced_mapTheory.union_thm])
  \\ fs [map_ok_def,union_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ fs [to_fmap_thm]
  \\ rename [`invariant f (union f b1 b2)`]
  \\ `to_fmap f (union f b1 b2) = to_fmap f b1 ⊌ to_fmap f b2`
        by metis_tac [balanced_mapTheory.union_thm]
  \\ rfs [to_fmap_thm,MAP_KEYS_sing_set_FUNION,MAP_KEYS_sing_set]
  \\ simp[cmp_of_def]
QED

Theorem FMERGE_WITH_KEY_MAP_KEYS:
  FMERGE_WITH_KEY g (MAP_KEYS (λx. {x}) m1) (MAP_KEYS (λx. {x}) m2) =
  MAP_KEYS (λx. {x}) (FMERGE_WITH_KEY (λk x y. g {k} x y) m1 m2)
Proof
  rw [finite_mapTheory.fmap_eq_flookup]
  \\ qmatch_goalsub_abbrev_tac ‘MAP_KEYS ff’
  \\ ‘∀x. INJ ff x UNIV’
    by gs [INJ_DEF, Abbr ‘ff’]
  \\ gs [Abbr ‘ff’]
  \\ gs [FLOOKUP_FMERGE_WITH_KEY, FLOOKUP_MAP_KEYS]
  \\ Cases_on ‘x’ \\ gs []
  \\ reverse (Cases_on ‘t’) \\ gs []
  >- (
    ‘!y. x' INSERT x INSERT t' <> {y}’
      by (fs [EXTENSION,IN_INSERT] \\ metis_tac [])
    \\ gs [])
  \\ ‘∀f1 v. x' = v ∧ f1 v ⇔ x' = v ∧ f1 x'’
    by metis_tac []
  \\ DEEP_INTRO_TAC some_intro \\ gs []
  \\ DEEP_INTRO_TAC some_intro \\ gs []
  \\ simp [FMERGE_WITH_KEY_DEF, FLOOKUP_DEF]
  \\ rw [] \\ gs []
QED

Theorem unionWithKey_thm:
  map_ok t1 ∧ map_ok t2 ∧ cmp_of t1 = cmp_of t2 ⇒
  map_ok (unionWithKey f t1 t2) ∧
  cmp_of (unionWithKey f t1 t2) = cmp_of t1 ∧
  to_fmap (unionWithKey f t1 t2) =
  FMERGE_WITH_KEY f (to_fmap t1) (to_fmap t2)
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ fs [cmp_of_def]
  \\ strip_tac \\ rveq
  \\ fs [unionWithKey_def]
  \\ rename [‘map_ok (Map f (unionWithKey f g b1 b2))’]
  \\ ‘∀k1 k2 x y. f k1 k2 = Equal ⇒ g k1 x y = g k2 x y’
    by fs [map_ok_def, totoTheory.TotOrd]
  \\ conj_asm1_tac
  THEN1
   (fs [map_ok_def]
    \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
    \\ fs [balanced_mapTheory.unionWithKey_thm])
  \\ fs [map_ok_def,unionWith_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ fs [to_fmap_thm]
  \\ qspecl_then [‘f’,‘g’,‘b1’,‘b2’] mp_tac balanced_mapTheory.unionWithKey_thm
  \\ simp []
  \\ strip_tac
  \\ gs [to_fmap_thm, FMERGE_WITH_KEY_MAP_KEYS,MAP_KEYS_sing_set, SF ETA_ss]
  \\ simp [cmp_of_def]
QED

Theorem unionWith_lemma:
  unionWith f t1 t2 = unionWithKey (λk. f) t1 t2
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’
  \\ rw [unionWith_def, unionWithKey_def, balanced_mapTheory.unionWith_def,
         SF ETA_ss]
QED

Theorem unionWith_thm:
  map_ok t1 ∧ map_ok t2 ∧ cmp_of t1 = cmp_of t2 ⇒
  map_ok (unionWith f t1 t2) ∧
  cmp_of (unionWith f t1 t2) = cmp_of t1 ∧
  to_fmap (unionWith f t1 t2) =
  FMERGE_WITH_KEY (λk x y. f x y) (to_fmap t1) (to_fmap t2)
Proof
  simp [unionWith_lemma, unionWithKey_thm, SF ETA_ss]
QED

Theorem all_thm:
  map_ok t ⇒
    (all f t ⇔ ∀k v. lookup t k = SOME v ⇒ f k v)
Proof
  Cases_on ‘t’
  \\ rw [map_ok_def, all_def, lookup_def]
  \\ irule balanced_mapTheory.every_thm
  \\ irule_at Any comparisonTheory.TotOrder_imp_good_cmp
  \\ gs [comparisonTheory.resp_equiv_def, totoTheory.TotOrd, SF SFY_ss]
QED

Theorem exists_thm:
  map_ok t ⇒
    (exists f t ⇔ ∃k v. lookup t k = SOME v ∧ f k v)
Proof
  Cases_on ‘t’
  \\ rw [map_ok_def, exists_def, balanced_mapTheory.exists_def, lookup_def]
  \\ irule balanced_mapTheory.exists_thm
  \\ irule_at Any comparisonTheory.TotOrder_imp_good_cmp
  \\ gs [comparisonTheory.resp_equiv_def, totoTheory.TotOrd, SF SFY_ss]
QED

Theorem FDIFF_MAP_KEYS:
  (∀x. x ∈ ks ⇒ SING x) ⇒
  FDIFF (MAP_KEYS (λx. {x}) m) ks =
  MAP_KEYS (λx. {x}) (FDIFF m (BIGUNION ks))
Proof
  rw [finite_mapTheory.fmap_eq_flookup]
  \\ qmatch_goalsub_abbrev_tac ‘MAP_KEYS ff’
  \\ ‘∀x. INJ ff x UNIV’
    by gs [INJ_DEF, Abbr ‘ff’]
  \\ gs [Abbr ‘ff’]
  \\ gs [FLOOKUP_FDIFF, FLOOKUP_MAP_KEYS]
  \\ DEEP_INTRO_TAC some_intro \\ gs []
  \\ DEEP_INTRO_TAC some_intro \\ gs []
  \\ rw [PULL_EXISTS] \\ DEEP_INTRO_TAC some_intro \\ gs []
  \\ rw [FLOOKUP_FDIFF] \\ gs [flookup_thm, DISJ_EQ_IMP]
  \\ res_tac \\ fs [SING_DEF] \\ rveq \\ gs []
QED

Theorem filterWithKey_thm:
  map_ok t ⇒
    map_ok (filterWithKey f t) ∧
    to_fmap (filterWithKey f t) =
    FDIFF (to_fmap t)
          {k | (k,v) | FLOOKUP (to_fmap t) k = SOME v ∧ ¬f k v}
Proof
  Cases_on ‘t’
  \\ simp [filterWithKey_def]
  \\ strip_tac
  \\ rename [‘map_ok (Map f (filterWithKey g b))’]
  \\ ‘∀k1 k2 x. f k1 k2 = Equal ⇒ g k1 x = g k2 x’
    by fs [map_ok_def, totoTheory.TotOrd]
  \\ conj_asm1_tac
  THEN1
   (fs [map_ok_def]
    \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
    \\ fs [balanced_mapTheory.filterWithKey_thm])
  \\ fs [map_ok_def,filterWithKey_def]
  \\ imp_res_tac comparisonTheory.TotOrder_imp_good_cmp
  \\ fs [to_fmap_thm]
  \\ qspecl_then [‘g’,‘b’,‘f’] mp_tac balanced_mapTheory.filterWithKey_thm
  \\ simp [] \\ strip_tac
  \\ gs [to_fmap_thm, MAP_KEYS_sing_set]
  \\ qmatch_asmsub_abbrev_tac ‘FDIFF (MAP_KEYS _ _) ks’
  \\ ‘∀x. x ∈ ks ⇒ SING x’
    by (gs [Abbr ‘ks’]
        \\ qmatch_goalsub_abbrev_tac ‘MAP_KEYS ff’
        \\ ‘∀x. INJ ff x UNIV’
          by gs [INJ_DEF, Abbr ‘ff’]
        \\ gs [Abbr ‘ff’]
        \\ simp [FLOOKUP_MAP_KEYS, IN_DEF, LAMBDA_PROD, EXISTS_PROD,
                 PULL_EXISTS]
        \\ rpt gen_tac
        \\ DEEP_INTRO_TAC some_intro \\ gs [])
  \\ gs [FDIFF_MAP_KEYS,MAP_KEYS_sing_set,to_fmap_thm, Abbr ‘ks’]
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac ‘MAP_KEYS ff’
  \\ ‘∀x. INJ ff x UNIV’
    by gs [INJ_DEF, Abbr ‘ff’]
  \\ gs [Abbr ‘ff’]
  \\ simp [FLOOKUP_MAP_KEYS]
  \\ rw [EXTENSION]
  \\ eq_tac \\ rw [IN_DEF, LAMBDA_PROD, EXISTS_PROD]
  >- (
    qpat_x_assum ‘(some x. _) = _’ mp_tac
    \\ DEEP_INTRO_TAC some_intro \\ gs []
    \\ rw [] \\ gs []
    \\ gvs [flookup_thm]
    \\ ‘s ≠ {}’
      by (strip_tac \\ gvs [])
    \\ drule_then assume_tac CHOICE_DEF \\ gs [IN_DEF])
  \\ rw [PULL_EXISTS]
  \\ qexists_tac ‘{x}’ \\ simp []
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ gs [flookup_thm, IN_DEF]
  \\ first_assum (irule_at Any) \\ rw []
QED

Theorem filter_lemma:
  filter f t = filterWithKey (λk. f) t
Proof
  Cases_on ‘t’
  \\ rw [filter_def, filterWithKey_def]
  \\ rw [balanced_mapTheory.filter_def, SF ETA_ss]
QED

Theorem filter_thm:
  map_ok t ⇒
    map_ok (filter f t) ∧
    to_fmap (filter f t) =
    FDIFF (to_fmap t) {k | (k,v) | FLOOKUP (to_fmap t) k = SOME v ∧ ¬f v}
Proof
  simp [filter_lemma, filterWithKey_thm]
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

Theorem filterWithKey_all:
  map_ok t ⇒
    all f (filterWithKey f t)
Proof
  rw [all_thm, filterWithKey_thm, lookup_thm]
  \\ gs [FLOOKUP_FDIFF, IN_DEF, LAMBDA_PROD, EXISTS_PROD]
QED

Theorem MAP_FST_toAscList:
   map_ok t ⇒
   SORTED (λx y. cmp_of t x y = Less) (MAP FST (toAscList t)) ∧
   ALL_DISTINCT (MAP FST (toAscList t)) ∧
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
  \\ match_mp_tac (MP_CANON sortingTheory.SORTED_ALL_DISTINCT |> GEN_ALL)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [irreflexive_def,transitive_def]
  \\ metis_tac [totoTheory.TotOrd,EVAL ``Equal = Less``]
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

