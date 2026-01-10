(*
  Verification of `rename_apart`:
  `rename_apart r c` gives a function f, such that
  f(r) ∩ c = ∅ ,  f(r) ∩ r = ∅  and dom(f) = r ∩ c.
 *)
Theory holSyntaxRenaming
Ancestors
  mlstring holSyntaxLib
Libs
  preamble

Theorem ALL_DISTINCT_MAP_inj:
  !l f. (!x y. f x = f y <=> x = y) ==> ALL_DISTINCT l = ALL_DISTINCT (MAP f l)
Proof
  Induct
  >> rw[MEM_MAP]
  >> first_x_assum (qspec_then `f` assume_tac)
  >> fs[]
QED

Theorem REPLICATE_inj1:
  !x y z. REPLICATE x z = REPLICATE y z <=> x = y
Proof
  Induct
  >> fs[EQ_IMP_THM,REPLICATE,REPLICATE_NIL]
  >> Cases >> rw[REPLICATE]
  >> res_tac
QED

Theorem REPLICATE_inj:
  !n m x y. REPLICATE n x = REPLICATE m y <=> n = m ∧ (0 < m ⇒ x = y)
Proof
  Induct
  >> fs[EQ_IMP_THM,REPLICATE,REPLICATE_NIL]
  >> Cases >> rw[REPLICATE]
  >> res_tac
QED

Theorem MAX_LIST_APPEND:
  !xs ys. MAX_LIST (xs ++ ys) = MAX (MAX_LIST xs) (MAX_LIST ys)
Proof
  Induct
  >> fs[MAX_LIST_def,MAX_DEF]
QED

Theorem list_inter_set_comm:
  !xs ys. set (list_inter xs ys) = set (list_inter ys xs)
Proof
  rw[list_inter_def,LIST_TO_SET_FILTER,INTER_COMM]
QED

Theorem list_inter_set:
  !xs ys. set(list_inter xs ys) = ((set xs) ∩ (set ys))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> fs[INSERT_DEF,list_inter_def,INTER_DEF,LIST_TO_SET,LEFT_AND_OVER_OR]
  >> rw[SET_EQ_SUBSET,SUBSET_DEF]
  >> fs[]
QED

Theorem NULL_list_inter_COMM:
  !a b. NULL (list_inter a b) = NULL (list_inter b a)
Proof
  metis_tac[NULL_EQ,LIST_TO_SET_EQ_EMPTY,list_inter_set_comm]
QED

Theorem nub_FILTER:
  !P l. nub (FILTER P l) = FILTER P (nub l)
Proof
  gen_tac >> Induct >> rw[nub_def]
  >> fs[MEM_FILTER]
QED

Theorem LENGTH_nub_LEQ:
  !l. LENGTH (nub l) <= LENGTH l
Proof
  Induct >> rw[nub_def]
QED

Theorem MEM_UNIQUE_nub:
  !x l. MEM x l ==> UNIQUE x (nub l)
Proof
  CONV_TAC SWAP_FORALL_CONV >> gen_tac
  >> REWRITE_TAC[UNIQUE_FILTER,Once $ GSYM MEM_nub,GSYM ALL_DISTINCT_FILTER,all_distinct_nub]
QED

(* rename_apart_by *)
Definition rename_apart_by_def:
  rename_apart_by chr r c =
    let inter = nub(list_inter c r) in
    let m = SUC (MAX_LIST (MAP strlen c ++ MAP strlen r)) in
    ZIP (MAP (λn. implode $ REPLICATE (m+n) chr) (COUNT_LIST (LENGTH inter)), inter)
End

Theorem rename_apart_by_ALL_DISTINCT:
  !chr r c. ALL_DISTINCT (MAP SND (rename_apart_by chr r c))
  /\ ALL_DISTINCT (MAP FST (rename_apart_by chr r c))
Proof
  rw[rename_apart_by_def]
  >> qmatch_goalsub_abbrev_tac `ZIP (l1,l2)`
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> unabbrev_all_tac
  >> gs[MEM_ZIP,MAP_ZIP,all_distinct_nub]
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM ALL_DISTINCT_MAP_inj]
  >> fs[REPLICATE_inj1,all_distinct_count_list,implode_def]
QED

Theorem SUC_MAX:
  !a b. SUC (MAX a b) = MAX (SUC a) (SUC b)
Proof
  fs[MAX_DEF]
QED

Theorem rename_apart_by_MEM:
  !x y chr r c. MEM (y,x) (rename_apart_by chr r c) ==> (~MEM y c /\ MEM x (list_inter c r))
Proof
  rw[rename_apart_by_def,EQ_IMP_THM]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)` ORELSE
    qmatch_asmsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> unabbrev_all_tac
  >- (
    spose_not_then assume_tac
    >> gs[MEM_ZIP,MEM_MAP,EL_MAP,EL_COUNT_LIST,implode_def]
    >> drule_then (qspec_then `strlen` assume_tac) MEM_MAP_f
    >> fs[STRLEN_DEF]
    >> dxrule_then assume_tac $ REWRITE_RULE[EVERY_MEM] MAX_LIST_max
    >> fs[MAX_LIST_APPEND,SUC_MAX]
    >> dxrule $ Q.prove(`!a b c. (a:num) + b <= c ==> b <= c /\ a <= c`,rw[])
    >> fs[MAX_LE]
  )
  >> fs[Once $ GSYM MEM_nub,EL_MEM,MEM_ZIP,Excl"nub_set"]
QED

Theorem rename_apart_by_chr_FST:
  !chr r c. EVERY (λx. ?n. x = implode $ REPLICATE n chr) (MAP FST (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> rw[rename_apart_by_def]
  >> fs[MAP_ZIP,EVERY_MEM,LENGTH_MAP,LENGTH_COUNT_LIST]
  >> rw[MEM_MAP]
  >> irule_at Any EQ_REFL
QED

Theorem rename_apart_by_strlen_FST:
  !chr r c. EVERY (λx. MAX_LIST (MAP strlen (r++c)) < strlen x) (MAP FST (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> rw[rename_apart_by_def]
  >> fs[MAP_ZIP,EVERY_MEM,LENGTH_COUNT_LIST,LENGTH_MAP]
  >> rw[MEM_MAP,MEM_COUNT_LIST,strlen_def]
  >> ONCE_REWRITE_TAC[CONS_APPEND]
  >> rw[MAX_LIST_APPEND,MAX_DEF]
QED

(* dom(f) = r ∩ c *)
Theorem rename_apart_by_MEM_SND1:
  !chr r c x. MEM x (list_inter c r) = MEM x (MAP SND (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> fs[rename_apart_by_def,MAP_ZIP,LENGTH_MAP,LENGTH_COUNT_LIST]
QED

Theorem rename_apart_by_MEM_SND = ONCE_REWRITE_RULE[list_inter_set_comm] rename_apart_by_MEM_SND1

Theorem rename_apart_by_NULL:
  !chr r c. NULL (rename_apart_by chr r c) = NULL (list_inter c r)
Proof
  REWRITE_TAC[EQ_IMP_THM]
  >> rpt gen_tac >> strip_tac
  >> rw[Once MONO_NOT_EQ,NOT_NULL_MEM]
  >- (
    dxrule_then (qspec_then `chr` assume_tac) $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] rename_apart_by_MEM_SND1
    >> fs[MEM_MAP]
    >> goal_assum drule
  )
  >> imp_res_tac $ Q.ISPEC `SND` MEM_MAP_f
  >> dxrule_then (irule_at Any) $ cj 2 $ REWRITE_RULE[EQ_IMP_THM] rename_apart_by_MEM_SND1
QED

Theorem rename_apart_by_disj_dom_img:
  !chr r c. NULL (list_inter (MAP FST (rename_apart_by chr r c)) (MAP SND (rename_apart_by chr r c)))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> pop_assum (assume_tac o REWRITE_RULE[MEM_MAP])
  >> fs[]
  >> Cases_on `y'`
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[GSYM rename_apart_by_MEM_SND1]
  >> rw[rename_apart_by_def]
  >> qmatch_goalsub_abbrev_tac `ZIP (l1,l2)`
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> drule (REWRITE_RULE[EVERY_MAP,EVERY_MEM] rename_apart_by_strlen_FST)
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_assum (qspecl_then [`strlen`,`l1`,`r'`] assume_tac)
  >> first_x_assum (qspecl_then [`strlen`,`list_inter c r`,`r'`] assume_tac)
  >> fs[MAP_ZIP]
  >> rw[]
  >> CCONTR_TAC
  >> rfs[]
  >> qpat_x_assum `MEM _ _ ==> _` imp_res_tac
  >> unabbrev_all_tac
  >> qpat_x_assum `MEM (strlen _) _` (assume_tac o REWRITE_RULE[MAP_MAP_o,MEM_MAP])
  >> fs[]
  >> rveq
  >> fs[strlen_def]
  >> pop_assum (assume_tac o REWRITE_RULE[MEM_EL])
  >> fs[EL_COUNT_LIST,LENGTH_COUNT_LIST,MAX_LIST_APPEND,MAX_DEF]
  >> fs[MEM_MAP,list_inter_set]
  >> FULL_CASE_TAC
  >> rveq
  >> fs[strlen_def,STRLEN_DEF,EL_COUNT_LIST]
  >> `MAX_LIST (MAP strlen r) < strlen y` by (
    fs[]
  )
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] MAX_LIST_max)
  >> fs[]
QED

Theorem rename_apart_by_diff:
  !chr r c. EVERY (UNCURRY $<>) (rename_apart_by chr r c)
Proof
  rw[EVERY_MEM]
  >> pairarg_tac
  >> rveq
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
  >> imp_res_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] rename_apart_by_disj_dom_img)
  >> CCONTR_TAC
  >> fs[]
QED

(* f(r) ∩ r = ∅  *)
Theorem rename_apart_by_disj_img_r:
  !chr r c. NULL (list_inter (MAP FST (rename_apart_by chr r c)) r)
Proof
  rw[NULL_FILTER,list_inter_def]
  >> CCONTR_TAC
  >> fs[]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST)
  >> fs[MAX_LIST_APPEND,MAX_DEF]
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] MAX_LIST_max)
  >> fs[]
QED

(* f(r) ∩ c = ∅  *)
Theorem rename_apart_by_disj_img_c:
  !chr r c. NULL (list_inter (MAP FST (rename_apart_by chr r c)) c)
Proof
  rw[NULL_FILTER,list_inter_def]
  >> Cases_on `MEM y r`
  >- (
    assume_tac rename_apart_by_disj_dom_img
    >> fs[list_inter_def,NULL_FILTER]
    >> pop_assum match_mp_tac
    >> fs[GSYM rename_apart_by_MEM_SND,list_inter_set]
  )
  >> CCONTR_TAC
  >> fs[]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST)
  >> fs[MAX_LIST_APPEND,MAX_DEF]
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] MAX_LIST_max)
  >> fs[]
QED

Theorem MEM_MAP_SWAP:
  !x s. MEM (SWAP x) (MAP SWAP s) = MEM x s
Proof
  rw[EQ_IMP_THM,MEM_MAP,SWAP_def]
  >- (Cases_on `x` >> Cases_on `y` >> fs[PAIR])
  >> Cases_on `x`
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem rename_apart_by_ALOOKUP:
  !v x chr r c. MEM (v,x) (rename_apart_by chr r c)
    = (ALOOKUP (MAP SWAP (rename_apart_by chr r c)) x = SOME v)
Proof
  ONCE_REWRITE_TAC[GSYM MEM_MAP_SWAP]
  >> rw[SWAP_def]
  >> match_mp_tac MEM_ALOOKUP
  >> `FST o SWAP = SND:mlstring#mlstring->mlstring` by rw[FUN_EQ_THM,SWAP_def]
  >> fs[rename_apart_by_ALL_DISTINCT,MAP_MAP_o]
QED

Theorem rename_apart_by_ALOOKUP_NONE:
  !x chr r c. (!v. ~MEM (v,x) (rename_apart_by chr r c))
    = (ALOOKUP (MAP SWAP (rename_apart_by chr r c)) x = NONE)
Proof
  fs[EQ_IMP_THM]
  >> rpt strip_tac
  >> CCONTR_TAC
  >> fs[rename_apart_by_ALOOKUP]
  >> qmatch_asmsub_abbrev_tac `ALOOKUP s x`
  >> Cases_on `ALOOKUP s x`
  >> fs[]
QED

Theorem rename_apart_by_LIST_UNION:
  !chr r c1 c2. NULL (list_inter (MAP FST (rename_apart_by chr r (LIST_UNION c1 c2))) c1)
  /\ NULL (list_inter (MAP FST (rename_apart_by chr r (LIST_UNION c1 c2))) c2)
Proof
  rw[]
  >> qmatch_goalsub_abbrev_tac `rename_apart_by _ _ c`
  >> qspecl_then [`chr`,`r`,`c`] assume_tac rename_apart_by_disj_img_c
  >> unabbrev_all_tac
  >> fs[NULL_FILTER,list_inter_def,holSyntaxLibTheory.MEM_LIST_UNION]
QED

Definition list_complement_def:
  list_complement a b = FILTER (λx. ~MEM x b) a
End

Theorem list_complement_LENGTH:
  !a b. LENGTH (list_complement a b) <= LENGTH a
Proof
  fs[list_complement_def,LENGTH_FILTER_LEQ]
QED

Theorem list_complement_MEM:
  !a b x. MEM x (list_complement a b) = (MEM x a /\ ~MEM x b)
Proof
  fs[list_complement_def,MEM_FILTER,CONJ_COMM]
QED

Theorem list_complement_MAP:
  !f a b. list_subset (list_complement (MAP f a) (MAP f b)) (MAP f (list_complement a b))
Proof
  rw[list_subset_def,EVERY_MEM,list_complement_def,MEM_FILTER,MEM_MAP]
  >> first_x_assum (qspec_then `y` assume_tac)
  >> fs[]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> rfs[]
QED

Theorem MEM_f_MAP_f_INJ:
  !f l. (!x y. f x = f y ==> x = y)
  ==> !x. MEM (f x) (MAP f l) = MEM x l
Proof
  rw[EQ_IMP_THM,MEM_MAP]
  >- (qpat_x_assum `!x. _` imp_res_tac >> fs[])
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem list_complement_MAP_INJ:
  !f a b. (!x y. f x = f y ==> x = y) ==>
  MAP f (list_complement a b) = (list_complement (MAP f a) (MAP f b))
Proof
  strip_tac
  >> Induct
  >- fs[list_complement_def]
  >> fs[list_complement_def,MEM_f_MAP_f_INJ]
  >> rw[]
QED

Theorem rename_apart_by_list_complement:
  !chr r rc c. NULL (list_inter (MAP SND (rename_apart_by chr (list_complement r rc) c)) rc)
Proof
  ONCE_REWRITE_TAC[NULL_list_inter_COMM]
  >> rw[NULL_FILTER,list_inter_def]
  >> imp_res_tac rename_apart_by_MEM_SND
  >> fs[list_inter_set,list_complement_MEM]
QED

Theorem rename_apart_by_chrs:
!chr1 chr2 r1 r2 c1 c2.
  chr1 <> chr2
  ==> NULL (list_inter (MAP FST (rename_apart_by chr1 r1 c1)) (MAP FST (rename_apart_by chr2 r2 c2)))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> spose_not_then assume_tac
  >> imp_res_tac $ REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST
  >> imp_res_tac $ REWRITE_RULE[EVERY_MEM] rename_apart_by_chr_FST
  >> gvs[implode_def, REPLICATE_inj]
QED

