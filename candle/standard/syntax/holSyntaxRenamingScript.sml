(*
  Verification of `rename_apart`:
  `rename_apart r c` gives a function f, such that
  f(r) ∩ c = ∅ ,  f(r) ∩ r = ∅  and dom(f) = r ∩ c.
 *)
open preamble mlstringTheory holSyntaxLibTheory

val _ = new_theory"holSyntaxRenaming"

Theorem ALL_DISTINCT_MAP_inj:
  !l f. (!x y. f x = f y <=> x = y) ==> ALL_DISTINCT l = ALL_DISTINCT (MAP f l)
Proof
  Induct
  >> rw[MEM_MAP]
  >> first_x_assum (qspec_then `f` assume_tac)
  >> fs[]
QED

Theorem MEM_MAP_f:
  !f l a. MEM a l ==> MEM (f a) (MAP f l)
Proof
  rw[MEM_MAP] >> qexists_tac `a` >> fs[]
QED

Theorem REPLICATE_inj1:
  !x y z. REPLICATE x z = REPLICATE y z <=> x = y
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[EQ_IMP_THM,REPLICATE,REPLICATE_NIL]
  >> Cases_on `x`
  >> fs[REPLICATE]
  >> res_tac
QED

Theorem list_max_APPEND:
  !xs ys. list_max (xs ++ ys) = MAX (list_max xs) (list_max ys)
Proof
  Induct
  >> fs[list_max_def,MAX_DEF]
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
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[nub_def]
  >> fs[MEM_FILTER]
QED

Theorem MEM_nub_EQ:
  !x l. MEM x (nub l) = MEM x l
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[nub_def]
QED

Theorem LENGTH_nub_LEQ:
  !l. LENGTH (nub l) <= LENGTH l
Proof
  Induct >> rw[nub_def]
QED

Theorem MEM_UNIQUE_nub:
  !x l. MEM x l ==> UNIQUE x (nub l)
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[]
  >> fs[UNIQUE_FILTER,GSYM nub_FILTER,nub_def,MEM_FILTER]
  >> rw[]
  >- (
    qspecl_then [`$= h`,`l`]  assume_tac (REWRITE_RULE[NULL_EQ,EQ_IMP_THM] (GSYM NULL_FILTER))
    >> fs[EQ_IMP_THM,nub_def]
  )
  >> first_x_assum drule
  >> rw[]
  >> fs[nub_def,MEM_FILTER]
QED

(* rename_apart_by *)
Definition rename_apart_by_def:
  rename_apart_by chr r c =
    let inter = nub(list_inter c r) in
    let m = SUC (list_max (MAP strlen c ++ MAP strlen r)) in
    ZIP (MAP (λn. strlit(REPLICATE (m+n) chr)) (COUNT_LIST (LENGTH inter)), inter)
End

Theorem rename_apart_by_ALL_DISTINCT:
  !chr r c. ALL_DISTINCT (MAP SND (rename_apart_by chr r c))
  /\ ALL_DISTINCT (MAP FST (rename_apart_by chr r c))
Proof
  rw[rename_apart_by_def]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> Q.ISPECL_THEN [`l1`,`l2`] assume_tac MEM_ZIP
  >> rfs[]
  >> unabbrev_all_tac
  >- fs[MAP_ZIP,all_distinct_nub]
  >> fs[MAP_ZIP]
  >> qmatch_goalsub_abbrev_tac `MAP f ls`
  >> Q.ISPECL_THEN [`ls`,`f`] assume_tac (GSYM ALL_DISTINCT_MAP_inj)
  >> unabbrev_all_tac
  >> fs[ETA_THM,REPLICATE_inj1,all_distinct_count_list]
QED

Theorem rename_apart_by_MEM:
  !x y chr r c. MEM (y,x) (rename_apart_by chr r c) ==> (~MEM y c /\ MEM x (list_inter c r))
Proof
  rw[rename_apart_by_def,EQ_IMP_THM]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)` ORELSE
    qmatch_asmsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> Q.ISPECL_THEN [`l1`,`l2`] assume_tac MEM_ZIP
  >> rfs[]
  >> unabbrev_all_tac
  >- (
    fs[rename_apart_by_def,MEM_ZIP,MEM_MAP,EL_MAP,EL_COUNT_LIST]
    >> CCONTR_TAC
    >> fs[]
    >> imp_res_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
    >> first_x_assum (qspec_then `strlen` assume_tac)
    >> fs[STRLEN_DEF]
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] list_max_max)
    >> fs[list_max_APPEND]
    >> fs[Q.prove(`!a b. SUC (MAX a b) = MAX (SUC a) (SUC b)`,rw[MAX_DEF])]
    >> imp_res_tac (Q.prove(`!a b c. (a:num) + b <= c ==> b <= c /\ a <= c`,rw[]))
    >> fs[MAX_LE]
  )
  >- (
    fs[MEM_ZIP]
    >> imp_res_tac EL_MEM
    >> fs[MEM_nub_EQ]
  )
QED

Theorem rename_apart_by_chr_FST:
  !chr r c. EVERY (λx. ?n. x = strlit(REPLICATE n chr)) (MAP FST (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> rw[rename_apart_by_def]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)` ORELSE
    qmatch_asmsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> fs[MAP_ZIP,EVERY_MEM]
  >> qunabbrev_tac `l1`
  >> rw[MEM_MAP]
  >> qmatch_goalsub_abbrev_tac `REPLICATE m chr`
  >> qexists_tac `m`
  >> fs[]
QED

Theorem rename_apart_by_strlen_FST:
  !chr r c. EVERY (λx. list_max (MAP strlen (r++c)) < strlen x) (MAP FST (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> rw[rename_apart_by_def]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)` ORELSE
    qmatch_asmsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> fs[MAP_ZIP,EVERY_MEM]
  >> qunabbrev_tac `l1`
  >> rw[MEM_MAP,MEM_COUNT_LIST,strlen_def]
  >> ONCE_REWRITE_TAC[CONS_APPEND]
  >> rw[list_max_APPEND,list_max_def,MAX_DEF]
QED

(* dom(f) = r ∩ c *)
Theorem rename_apart_by_MEM_SND1:
  !chr r c x. MEM x (list_inter c r) = MEM x (MAP SND (rename_apart_by chr r c))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[rename_apart_by_def,list_inter_def,nub_def,COUNT_LIST_def]
  >> rw[rename_apart_by_def,EQ_IMP_THM]
  >> (qmatch_goalsub_abbrev_tac `ZIP (l1,l2)` ORELSE
    qmatch_asmsub_abbrev_tac `ZIP (l1,l2)`)
  >> `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac >> fs[LENGTH_MAP,LENGTH_COUNT_LIST])
  >> fs[MAP_ZIP,EVERY_MEM]
  >> unabbrev_all_tac
  >- fs[MEM_nub_EQ]
  >> fs[MAP_ZIP]
QED

Theorem rename_apart_by_MEM_SND = ONCE_REWRITE_RULE[list_inter_set_comm] rename_apart_by_MEM_SND1

Theorem NULL_MAP_INJ:
  !f l. (!x y. f x = f y ==> x = y) ==> NULL (MAP f l) = NULL l
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> fs[]
QED

Theorem rename_apart_by_NULL:
  !chr r c. NULL (rename_apart_by chr r c) = NULL (list_inter c r)
Proof
  rw[EQ_IMP_THM]
  >> qmatch_goalsub_abbrev_tac `NULL ls`
  >> Cases_on `ls`
  >> fs[]
  >> qspecl_then [`chr`,`r`,`c`] assume_tac rename_apart_by_MEM_SND1
  >> TRY (first_x_assum (qspec_then `h` assume_tac))
  >> TRY (first_x_assum (qspec_then `SND h` assume_tac))
  >> fs[markerTheory.Abbrev_def,NULL_EQ]
  >> qpat_x_assum `_::_ = _` (assume_tac o GSYM)
  >> rfs[]
  >> fs[]
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
  >> fs[EL_COUNT_LIST,LENGTH_COUNT_LIST,list_max_APPEND,MAX_DEF]
  >> fs[MEM_MAP,list_inter_set]
  >> FULL_CASE_TAC
  >> rveq
  >> fs[strlen_def,STRLEN_DEF,EL_COUNT_LIST]
  >> `list_max (MAP strlen r) < strlen y` by (
    fs[]
  )
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] list_max_max)
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
  >> fs[list_max_APPEND,MAX_DEF]
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] list_max_max)
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
  >> fs[list_max_APPEND,MAX_DEF]
  >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``,beta|->``:num``] MEM_MAP_f)
  >> first_x_assum (qspec_then `strlen` assume_tac)
  >> res_tac
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] list_max_max)
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

Theorem list_complement_MAP_INJ1:
  !f a b x. (!x y. (MEM x a \/ MEM x b) /\ (MEM y a \/ MEM y b) ==> f x = f y ==> x = y) ==>
  (MEM x (MAP f (list_complement a b))) = MEM x (list_complement (MAP f a) (MAP f b))
Proof
  rw[EQ_IMP_THM]
  >> rw[list_complement_def,EVERY_MEM]
  >> fs[MEM_MAP,MEM_FILTER,list_complement_def]
  >> rw[]
  >- (
    CCONTR_TAC
    >> fs[]
    >> last_x_assum imp_res_tac
    >> rveq
    >> rfs[]
  )
  >- (
    goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> CCONTR_TAC
  >> fs[]
  >> rpt (first_x_assum (qspec_then `y` assume_tac))
  >> fs[]
QED

(*
Theorem rename_apart_by_ALOOKUP_inj:
  !chr r s c x y. MEM x (list_inter r s) /\ MEM y (list_inter r s) ==>
  let f = λx. ALOOKUP (MAP SWAP (rename_apart_by chr (list_complement r s) (LIST_UNION s c))) x
  in  f x = f y ==> x = y
Proof
  rw[GSYM rename_apart_by_ALOOKUP]
  >> CCONTR_TAC
  >> qmatch_asmsub_abbrev_tac `ALOOKUP ss x`
  >> Cases_on `ALOOKUP ss x`
  >> qunabbrev_tac `ss`
  >> fs[GSYM rename_apart_by_ALOOKUP_NONE,GSYM rename_apart_by_ALOOKUP]
  >> qspecl_then [`chr`,`list_complement r s`,`LIST_UNION s c`] assume_tac rename_apart_by_MEM_SND
  >> fs[list_inter_set]
QED
*)

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
  >> CCONTR_TAC
  >> fs[]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST)
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_chr_FST)
  >> fs[]
  >> rveq
  >> Cases_on `n = 0`
  >> Cases_on `n' = 0` >> fs[]
  >> rveq
  >> fs[NOT_ZERO_LT_ZERO,REPLICATE_NIL]
  >> imp_res_tac (INST_TYPE [alpha |-> ``:char``] MEM_REPLICATE)
  >> qpat_x_assum `!x. MEM _ (REPLICATE n' _)` (qspec_then `chr2` assume_tac)
  >> rfs[]
  >> fs[MEM_REPLICATE_EQ]
QED

val _ = export_theory()

