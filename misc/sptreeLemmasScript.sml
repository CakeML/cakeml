(*
   General-purpose sptree lemmas (lookup, insert, delete, domain,
   toAList, fromAList, subspt, eq_shape, copy_shape, range, etc.)
   used throughout the CakeML development.
*)
Theory sptreeLemmas
Ancestors
  listLemmas setLemmas arithLemmas sptree
  list arithmetic rich_list sorting pred_set pair option alist relation
Libs
  boolSimps mp_then dep_rewrite BasicProvers

val _ = numLib.temp_prefer_num();

Definition lookup_any_def:
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m
End

Definition fromList2_def:
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)
End

Theorem EVEN_fromList2_lemma[local]:
  !l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x
Proof
  Induct \\ full_simp_tac(srw_ss())[FOLDL] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC
QED

Theorem EVEN_fromList2:
   !l n. n IN domain (fromList2 l) ==> EVEN n
Proof
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ full_simp_tac(srw_ss())[]
QED

Type num_set = ``:unit spt``
Type num_map = ``:'a spt``

Theorem toAList_domain:
    !x. MEM x (MAP FST (toAList t)) <=> x IN domain t
Proof
  full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup]
QED

Theorem domain_nat_set_from_list[simp]:
   !ls ns. domain (FOLDL (\s n. insert n () s) ns ls) = domain ns UNION set ls
Proof
  Induct >> simp[sptreeTheory.domain_insert] >>
  srw_tac[][EXTENSION] >> metis_tac[]
QED

Theorem wf_nat_set_from_list:
   !ls ns. wf ns ==> wf (FOLDL (\s n. insert n z s) ns ls)
Proof
  Induct >> simp[] >> srw_tac[][sptreeTheory.wf_insert]
QED

Theorem lookup_fromList2:
   !l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE
Proof
  recInduct SNOC_INDUCT \\ srw_tac[][]
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  \\ full_simp_tac(srw_ss())[fromList2_def,FOLDL_SNOC]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[GSYM fromList2_def,FOLDL_SNOC]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_fromList,DIV_LT_X]
  \\ `!k. FST (FOLDL (\(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ full_simp_tac(srw_ss())[FOLDL]
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM DIV_LT_X,EL_SNOC]
  \\ full_simp_tac(srw_ss())[MULT_DIV,SNOC_APPEND,EL_LENGTH_APPEND,EVEN_MOD2,MOD_EQ_0]
  \\ TRY decide_tac
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `n = LENGTH l * 2 + 1` by decide_tac
  \\ full_simp_tac(srw_ss())[MOD_TIMES]
QED

Theorem domain_fromList2:
   !q. domain(fromList2 q) = set(GENLIST (\x. 2n*x) (LENGTH q))
Proof
  rw[EXTENSION,domain_lookup,lookup_fromList2,MEM_GENLIST,
     lookup_fromList,EVEN_EXISTS, PULL_EXISTS, SF CONJ_ss] \\
  metis_tac[]
QED

(* TODO: move to sptreeTheory *)

Definition eq_shape_def:
  eq_shape LN LN = T /\
  eq_shape (LS _) (LS _) = T /\
  eq_shape (BN t1 t2) (BN u1 u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape (BS t1 _ t2) (BS u1 _ u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape _ _ = F
End

Theorem spt_eq:
   !t1 t2.
      t1 = t2 <=>
      (eq_shape t1 t2 /\ (!k v. lookup k t1 = SOME v ==> lookup k t2 = SOME v))
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,lookup_def]
  THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ rw [] \\ rw [] \\ fs []
  \\ first_assum (qspec_then `0` mp_tac)
  \\ first_assum (qspec_then `k * 2 + 1` mp_tac)
  \\ first_x_assum (qspec_then `k * 2 + 1 + 1` mp_tac)
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT,EVEN_ADD]
  \\ fs [GSYM ADD1,EVEN,EVEN_DOUBLE]
QED

Theorem eq_shape_map:
   !t1 t2 f. eq_shape (map f t1) t2 <=> eq_shape t1 t2
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,map_def]
QED

Theorem eq_shape_IMP_domain:
   !t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2
Proof
  ho_match_mp_tac (fetch "-" "eq_shape_ind")
  \\ rw [] \\ fs [eq_shape_def]
QED

Definition copy_shape_def:
  copy_shape LN LN = LN /\
  copy_shape LN (LS y) = LN /\
  copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN t2) /\
  copy_shape LN (BS t1 y t2) = LN /\
  copy_shape (LS x) LN = LS x /\
  copy_shape (LS x) (LS y) = LS x /\
  copy_shape (LS x) (BN t1 t2) = LS x /\
  copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x (copy_shape LN t2) /\
  copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN else BN u1 u2) /\
  copy_shape (BN u1 u2) (LS y) = BN u1 u2 /\
  copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1) (copy_shape u2 t2) /\
  copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2 /\
  copy_shape (BS u1 x u2) LN = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (LS y) =
     (if domain (BN u1 u2) = {} then LS x else BS u1 x u2) /\
  copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (BS t1 y t2) = BS (copy_shape u1 t1) x (copy_shape u2 t2)
End

Theorem eq_shape_copy_shape[local]:
    !s. domain s = {} ==> eq_shape (copy_shape LN s) s
Proof
  Induct \\ fs [copy_shape_def,eq_shape_def]
QED

Theorem num_lemma[local]:
    (!n. 0 <> 2 * n + 2 /\ 0 <> 2 * n + 1:num) /\
    (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
    (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
    (!n m. 2 * n + 2 <> 2 * m + 1n)
Proof
  rw [] \\ fs [] \\ Cases_on `m = n` \\ fs []
QED

Theorem shape_eq_copy_shape:
   !t1 t2. domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,copy_shape_def]
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac)
  \\ TRY (match_mp_tac eq_shape_copy_shape) \\ fs []
  \\ rw [] \\ pop_assum mp_tac
  \\ rewrite_tac [DE_MORGAN_THM] \\ strip_tac
  \\ fs [eq_shape_def] \\ fs [EXTENSION]
  \\ TRY (first_assum (qspec_then `0` mp_tac) \\ simp_tac std_ss [])
  \\ rw [] \\ first_assum (qspec_then `2 * x + 2` mp_tac)
  \\ first_x_assum (qspec_then `2 * x + 1` mp_tac)
  \\ fs [num_lemma]
QED

Theorem lookup_copy_shape_LN[local]:
    !s n. lookup n (copy_shape LN s) = NONE
Proof
  Induct \\ fs [copy_shape_def,lookup_def] \\ rw [] \\ fs []
QED

Theorem domain_EMPTY_lookup[local]:
    domain t = EMPTY ==> !x. lookup x t = NONE
Proof
  fs [domain_lookup,EXTENSION] \\ rw []
  \\ pop_assum (qspec_then `x` mp_tac)
  \\ Cases_on `lookup x t` \\ fs []
QED

Theorem lookup_copy_shape:
   !t1 t2 n. lookup n (copy_shape t1 t2) = lookup n t1
Proof
  Induct \\ Cases_on `t2` \\ fs [copy_shape_def,lookup_def] \\ rw []
  \\ fs [lookup_def,lookup_copy_shape_LN,domain_EMPTY_lookup]
QED

(* BEGIN TODO: move to sptreeTheory *)

Theorem lookup_zero:
   !n t x. (lookup n t = SOME x) ==> (size t <> 0)
Proof
   recInduct lookup_ind
   \\ rw[lookup_def]
QED

Theorem empty_sub:
     isEmpty(difference a b) /\ (subspt b a) ==> (domain a = domain b)
Proof
    fs[subspt_def] >>
    rw[] >>
    imp_res_tac difference_sub >>
    metis_tac[GSYM SUBSET_DEF, SUBSET_ANTISYM]
QED

Theorem subspt_delete:
     !a b x. subspt a b ==> subspt (delete x a) b
Proof
    rw[subspt_def, lookup_delete]
QED

Theorem inter_union_empty:
     !a b c. isEmpty (inter (union a b) c)
  <=> isEmpty (inter a c) /\ isEmpty (inter b c)
Proof
    rw[] >> EQ_TAC >> rw[] >>
    `wf (inter (union a b) c) /\ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >>
    TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> BasicProvers.EVERY_CASE_TAC >> fs[]
QED

Theorem inter_insert_empty:
     !n t1 t2. isEmpty (inter (insert n () t1) t2)
  ==> n NOTIN domain t2 /\ isEmpty(inter t1 t2)
Proof
    rw[] >>
    `!k. lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def]
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >>
        pop_assum (qspec_then `n` mp_tac) >>
        rw[] >> fs[] >> BasicProvers.EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >>
        fs[EXTENSION] >> rw[] >>
        pop_assum (qspec_then `x` mp_tac) >> rw[] >>
        first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >>
        Cases_on `x = n` >> fs[] >>
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
QED

Theorem fromList2_value:
     !e l t n. MEM e l <=>  ?n. lookup n (fromList2 l) = SOME e
Proof
    rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >>
        rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
QED

(* The range is the set of values taken on by an sptree. *)
Definition range_def:
  range s = {v | ?n. lookup n s = SOME v}
End

Theorem range_delete:
  range (delete h v) SUBSET range v
Proof
  simp[range_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem range_insert:
  n NOTIN domain fml ==>
  range (insert n l fml) = l INSERT range fml
Proof
  rw[range_def,EXTENSION,lookup_insert,domain_lookup]>>
  metis_tac[SOME_11]
QED

Theorem range_insert_2:
  C IN range (insert n l fml) ==> C IN range fml \/ C = l
Proof
  fs[range_def,lookup_insert]>>
  rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem range_insert_SUBSET:
  range (insert n l fml) SUBSET l INSERT range fml
Proof
  rw[SUBSET_DEF]>>
  metis_tac[range_insert_2]
QED

(* END TODO *)

Theorem TWOxDIV2:
   2 * x DIV 2 = x
Proof
  ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
QED

Theorem alist_insert_REVERSE:
   !xs ys s.
   ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
   alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s
Proof
  Induct \\ simp[alist_insert_def]
  \\ gen_tac \\ Cases \\ simp[alist_insert_def]
  \\ simp[alist_insert_append,alist_insert_def]
  \\ rw[] \\ simp[alist_insert_pull_insert]
QED

Theorem alist_insert_ALL_DISTINCT:
    !xs ys t ls.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH ys /\
  PERM (ZIP (xs,ys)) ls ==>
  alist_insert xs ys t = alist_insert (MAP FST ls) (MAP SND ls) t
Proof
  ho_match_mp_tac alist_insert_ind>>rw[]>>
  fs[LENGTH_NIL_SYM]>>rpt BasicProvers.VAR_EQ_TAC>>fs[ZIP]>>
  simp[alist_insert_def]>>
  fs[PERM_CONS_EQ_APPEND]>>
  simp[alist_insert_append,alist_insert_def]>>
  `~MEM xs (MAP FST M)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac PERM_MEM_EQ>>
    fs[FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
    res_tac>>
    imp_res_tac MEM_ZIP>>
    fs[EL_MEM])>>
  simp[alist_insert_pull_insert]>>
  simp[GSYM alist_insert_append]>>
  metis_tac[MAP_APPEND]
QED

Theorem size_fromAList: (* TODO: move to HOL *)
  !xs. ALL_DISTINCT (MAP FST xs) ==> size (fromAList xs) = LENGTH xs
Proof
  Induct THEN1 (fs [] \\ EVAL_TAC)
  \\ fs [FORALL_PROD]
  \\ fs [fromAList_def,size_insert,domain_lookup,lookup_fromAList,ADD1] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM \\ fs []
  \\ fs [MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  `SORTED $< (MAP FST (toSortedAList t))` by
    simp[SORTED_toSortedAList]>>
  pop_assum mp_tac>>
  match_mp_tac SORTED_ALL_DISTINCT>>
  simp[irreflexive_def]
QED
