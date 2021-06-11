(*
 Implementation of cyclicity check for function definitions
 based on [Kunčar, CPP 2015](https://doi.org/10.1145/2676724.2693175)
 *)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
     holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSyntaxRenamingTyvarTheory

val _ = new_theory"holSyntaxCyclicity"
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Overload is_instance = ``λty0 ty. ∃i. ty = TYPE_SUBST i ty0``
val _ = Parse.add_infix("#", 401, Parse.NONASSOC)
Overload "#" = ``$orth_ty``
Overload "#" = ``$orth_ci``

(* contraposition of an equivalence *)
(* TODO replace with REWRITE_RULE[Once MONO_NOT_EQ] *)
fun ccontr_equiv(x) =
  let val (a,b) = EQ_IMP_RULE (SPEC_ALL x)
  in GEN_ALL (IMP_ANTISYM_RULE (CONTRAPOS b) (CONTRAPOS a)) end;


Theorem WOP_eq[local]:
  ∀P. (∃(n:num). P n) <=> ∃n. P n ∧ ∀m. m < n ⇒ ¬P m
Proof
  rw[EQ_IMP_THM,WOP]
  >> goal_assum (first_assum o mp_then Any mp_tac)
QED


(* lemmata on lists *)

Theorem ALL_DISTINCT_MAP_PAIR_FILTER:
  (!s f. ALL_DISTINCT (MAP FST s) ==> ALL_DISTINCT (MAP FST (FILTER f s)))
  /\ !s f. ALL_DISTINCT (MAP SND s) ==> ALL_DISTINCT (MAP SND (FILTER f s))
Proof
  rw[ALL_DISTINCT_FILTER]
  >> fs[FILTER_MAP,MEM_MAP,MEM_FILTER,PULL_EXISTS]
  >> ((rename1`x = SND y`) ORELSE (rename1`x = FST y`))
  >> PairCases_on `y`
  >> first_x_assum $ drule_then strip_assume_tac
  >> gvs[MEM_SPLIT,FILTER_APPEND,APPEND_EQ_SING]
  >> rename1`x:'a#'b`
  >> ((rename1`(y0, SND x0)`) ORELSE (rename1`(FST x0,y1)`))
  >> PairCases_on `x0`
  >> conj_tac
  >> qmatch_goalsub_abbrev_tac `FILTER _ (FILTER _ ll)`
  >> qpat_x_assum `FILTER _ ll = []` mp_tac
  >> qspec_then `ll` mp_tac $ INST_TYPE [alpha |-> ``:'a#'b``] FILTER_F
  >> disch_then $ CONV_TAC o DEPTH_CONV o REWR_CONV o GSYM
  >> rw[FILTER_FILTER,FILTER_EQ,Excl"FILTER_F"]
QED

val MAP_SWAP = REWRITE_RULE[INVOL_DEF,SWAP_SWAP_INVOL]
  (SPEC ``SWAP:'a#'a->'a#'a`` (INST_TYPE [alpha |-> ``:'a#'a``] MAP_INVOL))

Theorem FST_SWAP_SND[local]:
  FST o SWAP = SND /\ SND o SWAP = FST
Proof
  rw[FUN_EQ_THM,EQ_IMP_THM,SWAP_def]
QED

Theorem EVERY_MAP_o:
  ∀P f l. EVERY P (MAP f l) ⇔ EVERY ((λx. P x) o f) l
Proof
  fs[o_DEF,EVERY_MAP]
QED

Theorem EVERY_MAP_PAIR:
  !f g s. EVERY (λ(x,y). f x /\ g y) s
    = (EVERY f (MAP FST s) /\ EVERY g (MAP SND s))
Proof
  rw[EVERY_MEM,EQ_IMP_THM,MEM_MAP,PULL_EXISTS,FORALL_AND_THM,IMP_CONJ_THM]
  >> rpt $ first_x_assum drule
  >> ONCE_REWRITE_TAC[GSYM PAIR]
  >> fs[]
QED

Theorem MEM_DROP_TAKE:
  !xs l. l <= LENGTH xs ==> !x k. MEM x (DROP k (TAKE l xs)) ==> MEM x (DROP k xs)
Proof
  Induct
  >> fs[DROP_def,TAKE_def]
  >> rpt strip_tac
  >> FULL_CASE_TAC
  >> fs[DROP_def,TAKE_def,PULL_FORALL]
  >- (
    FULL_CASE_TAC
    >> fs[MEM]
    >> first_x_assum (qspecl_then [`l-1`,`x`,`0`] assume_tac)
    >> rfs[DROP_def]
  )
  >> FULL_CASE_TAC
  >> fs[DROP_def]
  >> first_x_assum (qspecl_then [`l-1`,`x`,`k-1`] assume_tac)
  >> rfs[DROP_def]
QED

Theorem LAST_DROP:
  !l k. ~NULL (DROP k l) ==> LAST (DROP k l) = LAST l
Proof
  Induct
  >- fs[LAST,DROP_NIL,NULL_EQ]
  >> strip_tac
  >> Cases
  >- fs[LAST,DROP_NIL,NULL_EQ]
  >> first_x_assum (qspec_then `n` assume_tac)
  >> rw[DROP,LAST_DEF,DROP_NIL,NULL_EQ]
QED

Theorem DROP_TAKE_NIL:
  !ls k. NULL (DROP k (TAKE k ls))
Proof
  Induct >> rw[DROP_def,TAKE_def]
QED


(* lemmata on LR_TYPE_SUBST *)

Theorem LR_TYPE_SUBST_NIL:
  !x. is_const_or_type x ==> LR_TYPE_SUBST [] x = x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,TYPE_SUBST_NIL]
QED

Theorem LR_TYPE_SUBST_type_preserving:
  !t s. is_const_or_type t ==> is_const_or_type (LR_TYPE_SUBST s t)
Proof
  rw[is_const_or_type_eq] >> fs[LR_TYPE_SUBST_cases]
QED

Theorem FV_LR_TYPE_SUBST_mono:
  !x y s. is_const_or_type x /\ is_const_or_type y /\ set (FV x) ⊆ set (FV y)
  ==> set (FV (LR_TYPE_SUBST s x)) ⊆ set (FV (LR_TYPE_SUBST s y))
Proof
  rw[is_const_or_type_eq,FV_def,LR_TYPE_SUBST_cases]
  >> fs[LR_TYPE_SUBST_cases,tvars_def,tyvars_TYPE_SUBST_mono]
QED

Theorem TYPE_SUBST_wlog_eq =
  clean_tysubst_TYPE_SUBST_eq |>
  CONV_RULE $ ONCE_DEPTH_CONV $ RHS_CONV $
    ONCE_REWRITE_CONV $ single TYPE_SUBST_FILTER_SND_tyvars2'
  |> CONV_RULE SWAP_FORALL_CONV

Theorem LR_TYPE_SUBST_wlog_eq:
  !p s. is_const_or_type p
  ==> LR_TYPE_SUBST s p =
  LR_TYPE_SUBST (FILTER ((λx. MEM x (MAP Tyvar (FV p))) ∘ SND) (clean_tysubst s)) p
Proof
  rw[is_const_or_type_eq]
  >> rw[GSYM TYPE_SUBST_wlog_eq,LR_TYPE_SUBST_def,INST_def,INST_CORE_def,FV_def,sum_case_def,tvars_def]
QED

Theorem LR_TYPE_SUBST_wlog_eq':
  !p s. is_const_or_type p
  ==> ?s'. LR_TYPE_SUBST s p = LR_TYPE_SUBST s' p
    /\ ALL_DISTINCT (MAP SND s')
    /\ EVERY ((λx. MEM x (MAP Tyvar (FV p))) ∘ SND) s'
Proof
  rw[]
  >> drule_then (qspec_then `s` assume_tac) LR_TYPE_SUBST_wlog_eq
  >> goal_assum drule
  >> irule_at Any $ cj 2 ALL_DISTINCT_MAP_PAIR_FILTER
  >> fs[EVERY_FILTER,clean_tysubst_ALL_DISTINCT_MAP_SND]
QED

Theorem LR_TYPE_SUBST_wlog_eq'':
  !p s. is_const_or_type p
  ==> LR_TYPE_SUBST s p =
  LR_TYPE_SUBST (FILTER ((λx. MEM x (MAP Tyvar (FV p))) ∘ SND) s) p
Proof
  rw[is_const_or_type_eq]
  >> rw[GSYM TYPE_SUBST_FILTER_SND_tyvars2,o_DEF,LR_TYPE_SUBST_def,INST_def,INST_CORE_def,FV_def,sum_case_def,tvars_def]
QED

Theorem LR_tyvars_SUBSET:
  !t t' x. is_const_or_type t /\ is_const_or_type t'
  /\ MEM x (FV t) /\ list_subset (FV t) (FV t')
  ==> MEM x (FV t')
Proof
  rw[is_const_or_type_eq,sum_case_def,list_subset_set,FV_def,SUBSET_DEF]
  >> fs[INL,INR]
QED

Theorem FV_SUBSET_LR_TYPE_SUBST_id:
  MEM x (FV p) /\ TYPE_SUBST s (Tyvar x) = Tyvar x /\ is_const_or_type p
  ==> MEM x (FV (LR_TYPE_SUBST s p))
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,FV_def,sum_case_def,tvars_def,tyvars_TYPE_SUBST]
  >> goal_assum drule
  >> fs[tyvars_def]
QED


(* equivalence relations from section 3 *)

(* equal type substitutions; equal on a set of variables  *)
Definition equal_ts_on_def:
  equal_ts_on s s' vars =
    !x. MEM x vars ==> TYPE_SUBST s (Tyvar x) = TYPE_SUBST s' (Tyvar x)
End

(* equivalent type substitutions; equivalent on a set of variables  *)
Definition equiv_ts_on_def:
  equiv_ts_on s s' vars =
  ?η. var_renaming η /\ equal_ts_on s (MAP (TYPE_SUBST η ## I) s' ++ η) vars
End

Theorem equal_ts_on_tyvars:
  !s s' t. equal_ts_on s s' (tyvars t) <=> TYPE_SUBST s t = TYPE_SUBST s' t
Proof
  fs[equal_ts_on_def,TYPE_SUBST_tyvars,tyvars_def]
QED

Theorem equiv_ts_on_tyvars:
  !s s' t. equiv_ts_on s s' (tyvars t)
  <=> ?e. var_renaming e /\ TYPE_SUBST s t = TYPE_SUBST e (TYPE_SUBST s' t)
Proof
  fs[equiv_ts_on_def,equal_ts_on_tyvars,PULL_FORALL,TYPE_SUBST_tyvars,TYPE_SUBST_compose]
QED

Theorem equiv_ts_on_tyvars_Tyapp:
  !s s' m l. equiv_ts_on s s' (tyvars $ Tyapp m l)
  ==> EVERY (λx. equiv_ts_on s s' $ tyvars x) l
Proof
  rw[tyvars_Tyapp,equiv_ts_on_tyvars,MAP_MAP_o,MAP_EQ_f,EVERY_MEM]
  >> goal_assum drule
  >> res_tac
QED

Theorem equal_ts_on_FV:
  !s s' t. is_const_or_type t ==> (equal_ts_on s s' (FV t) <=> LR_TYPE_SUBST s t = LR_TYPE_SUBST s' t)
Proof
  rw[is_const_or_type_eq]
  >> fs[tyvars_def,tvars_def,FV_def,sum_case_def,LR_TYPE_SUBST_cases,equal_ts_on_tyvars]
QED

Theorem LR_TYPE_SUBST_tyvars:
  !t s s'. is_const_or_type t ==>
  (LR_TYPE_SUBST s t = LR_TYPE_SUBST s' t)
  = !x. MEM x (FV t) ==> (TYPE_SUBST s (Tyvar x) = TYPE_SUBST s' (Tyvar x))
Proof
  rw[is_const_or_type_eq,EQ_IMP_THM,FV_def]
  >> fs[TYPE_SUBST_tyvars,LR_TYPE_SUBST_cases,sum_case_def,tvars_def]
QED

Theorem equiv_ts_on_FV:
  !s s' t. is_const_or_type t ==> (equiv_ts_on s s' (FV t)
  <=> ?e. var_renaming e /\ LR_TYPE_SUBST s t = LR_TYPE_SUBST e (LR_TYPE_SUBST s' t))
Proof
  rw[equiv_ts_on_def,equal_ts_on_FV,LR_TYPE_SUBST_cases,is_const_or_type_eq,GSYM LR_TYPE_SUBST_compose]
QED

Theorem equal_ts_on_refl:
  !s vars. equal_ts_on s s vars
Proof
  fs[equal_ts_on_def]
QED

Theorem equiv_ts_on_refl:
  !s vars. equiv_ts_on s s vars
Proof
  rw[equiv_ts_on_def]
  >> qexists_tac `[]`
  >> fs[var_renaming_nil,TYPE_SUBST_NIL,GSYM TYPE_SUBST_compose,equal_ts_on_def,equal_ts_on_refl,Excl"TYPE_SUBST_def"]
QED

Theorem equal_ts_on_symm:
  !s' s vars. equal_ts_on s' s vars = equal_ts_on s s' vars
Proof
  fs[equal_ts_on_def,EQ_IMP_THM,Once EQ_SYM_EQ]
QED

Theorem var_renaming_SWAP_LR_id:
  !s t. var_renaming s /\ is_const_or_type t
  ==> LR_TYPE_SUBST (MAP SWAP s) (LR_TYPE_SUBST s t) = t
Proof
  rpt strip_tac
  >> drule LR_TYPE_SUBST_NIL
  >> disch_then $ CONV_TAC o RHS_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> rw[LR_TYPE_SUBST_tyvars,LR_TYPE_SUBST_compose,Excl"TYPE_SUBST_def"]
  >> fs[var_renaming_SWAP_id,GSYM TYPE_SUBST_compose]
QED

Theorem equiv_ts_on_symm:
  !s' s vars. equiv_ts_on s' s vars = equiv_ts_on s s' vars
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM]
  >> reverse conj_asm1_tac
  >- metis_tac[]
  >> rw[equiv_ts_on_def,equal_ts_on_def,Excl"TYPE_SUBST_def"]
  >> rename[`var_renaming e`]
  >> qexists_tac `MAP SWAP e`
  >> rw[var_renaming_SWAP_IMP,Excl"TYPE_SUBST_def"]
  >> fs[GSYM TYPE_SUBST_compose,var_renaming_SWAP_id]
QED

Theorem equal_ts_on_trans:
  !s1 s2 s3 vars. equal_ts_on s1 s2 vars /\ equal_ts_on s2 s3 vars
  ==> equal_ts_on s1 s3 vars
Proof
  fs[equal_ts_on_def]
QED

Theorem equiv_ts_on_trans:
  !s1 s2 s3 vars. equiv_ts_on s1 s2 vars /\ equiv_ts_on s2 s3 vars
  ==> equiv_ts_on s1 s3 vars
Proof
  rw[equiv_ts_on_def]
  >> qexists_tac `clean_tysubst (MAP (TYPE_SUBST η ## I) η' ++ η)`
  >> fs[var_renaming_compose,equal_ts_on_def,GSYM clean_tysubst_TYPE_SUBST_eq,GSYM TYPE_SUBST_compose]
QED

Theorem equal_ts_on_subset:
  !s s' vars vars'.  equal_ts_on s s' vars /\ set vars' ⊆ set vars
  ==> equal_ts_on s s' vars'
Proof
  fs[equal_ts_on_def,PULL_FORALL,SUBSET_DEF]
QED

Theorem equiv_ts_on_subset:
  !s s' vars vars'.  equiv_ts_on s s' vars /\ set vars' ⊆ set vars
  ==> equiv_ts_on s s' vars'
Proof
  rw[equiv_ts_on_def]
  >> goal_assum dxrule
  >> metis_tac[equal_ts_on_subset]
QED

Theorem equal_ts_on_FILTER:
  !s s' t. is_const_or_type t ==> equal_ts_on s s' (FV t)
  = equal_ts_on s (FILTER ((λx. MEM x (MAP Tyvar (FV t))) o SND) s') (FV t)
Proof
  rw[equal_ts_on_FV,GSYM LR_TYPE_SUBST_wlog_eq'']
QED

Theorem equiv_ts_on_FILTER:
  !s s' t. is_const_or_type t ==> equiv_ts_on s s' (FV t)
  = equiv_ts_on s (FILTER ((λx. MEM x (MAP Tyvar (FV t))) o SND) s') (FV t)
Proof
  ONCE_REWRITE_TAC[equiv_ts_on_symm]
  >> rw[equiv_ts_on_FV,GSYM equal_ts_on_FILTER,EQ_IMP_THM,GSYM LR_TYPE_SUBST_wlog_eq'']
QED

Theorem equal_ts_on_FV_LR_TYPE_SUBST:
  !p s s' r. is_const_or_type p ==>
  equal_ts_on s s' (FV (LR_TYPE_SUBST r p)) =
  equal_ts_on (MAP ((TYPE_SUBST s) ## I) r ++ s) (MAP ((TYPE_SUBST s') ## I) r ++ s')  (FV p)
Proof
  rpt strip_tac
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving]
  >> asm_rewrite_tac[]
QED

Theorem equal_ts_on_split:
  !s s' vars1 vars2 vars. (set vars1 ∪ set vars2) = set vars
    /\ equal_ts_on s s' vars1 /\ equal_ts_on s s' vars2
    ==> equal_ts_on s s' vars
Proof
  fs[equal_ts_on_def,EQ_SYM_EQ,FORALL_AND_THM,DISJ_IMP_THM]
QED

Theorem equal_ts_on_complement:
  !s s' vars vars'.  equal_ts_on s s' (list_complement vars vars')
    /\ equal_ts_on s s' (list_inter vars vars')
    ==> equal_ts_on s s' vars
Proof
  rpt strip_tac
  >> match_mp_tac equal_ts_on_split
  >> goal_assum $ drule_at Any
  >> goal_assum $ rev_drule_at Any
  >> fs[pred_setTheory.EXTENSION,GSYM LEFT_AND_OVER_OR,
      holSyntaxRenamingTheory.list_complement_MEM,holSyntaxRenamingTheory.list_inter_set]
QED

(* well-formed list of dependencies *)

Definition wf_pqs_def:
  wf_pqs = EVERY (UNCURRY $/\ o (is_const_or_type ## is_const_or_type))
End

(* Definition 5.3, Kunčar 2015
 * Solution to a sequence *)

Definition sol_seq_def:
  sol_seq rs pqs =
    (wf_pqs pqs
    /\ (LENGTH rs = LENGTH pqs
    /\ !i. SUC i < LENGTH rs ==>
    LR_TYPE_SUBST (EL i rs) (SND (EL i pqs))
    = LR_TYPE_SUBST (EL (SUC i) rs) (FST (EL (SUC i) pqs))))
End

(* most general solution to a sequence *)
Definition mg_sol_seq_def:
  mg_sol_seq rs pqs =
    (sol_seq rs pqs
    /\ !rs'. sol_seq rs' pqs ==>
    ?es. LENGTH es = LENGTH rs /\
    !i. i < LENGTH rs ==>
    equal_ts_on (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs) ++ (EL i es)) (EL i rs') (FV (FST (EL i pqs))))
End

Theorem sol_seq_is_const_or_type:
  !rs pqs i. sol_seq rs pqs /\ i < LENGTH pqs
  ==> is_const_or_type (FST (EL i pqs))
  /\ is_const_or_type (SND (EL i pqs))
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >> imp_res_tac EL_MEM
  >> res_tac
  >> fs[ELIM_UNCURRY]
QED

Theorem sol_seq_is_const_or_type_FST =
  cj 1 $ REWRITE_RULE[FORALL_AND_THM,AND_IMP_INTRO] sol_seq_is_const_or_type

Theorem sol_seq_is_const_or_type_SND =
  cj 2 $ REWRITE_RULE[FORALL_AND_THM,AND_IMP_INTRO] sol_seq_is_const_or_type

Theorem sol_seq_LENGTH:
  sol_seq rs pqs ==> LENGTH rs = LENGTH pqs
Proof
  fs[sol_seq_def]
QED

Theorem mg_sol_seq_LENGTH:
  mg_sol_seq rs pqs ==> LENGTH rs = LENGTH pqs
Proof
  fs[mg_sol_seq_def,sol_seq_def]
QED

Theorem sol_seq_TAKE:
  !rs pqs k. sol_seq rs pqs /\
  k <= LENGTH rs ==> sol_seq (TAKE k rs) (TAKE k pqs)
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >- (
    first_x_assum match_mp_tac
    >> imp_res_tac MEM_TAKE
  )
  >> dep_rewrite.DEP_REWRITE_TAC[EL_TAKE]
  >> fs[]
QED

Theorem sol_seq_DROP:
  !rs pqs k. sol_seq rs pqs /\ k <= LENGTH rs
  ==> sol_seq (DROP k rs) (DROP k pqs)
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >- (
    first_x_assum match_mp_tac
    >> imp_res_tac MEM_DROP_IMP
  )
  >> dep_rewrite.DEP_REWRITE_TAC[EL_DROP]
  >> fs[ADD_CLAUSES]
QED

Theorem mg_sol_seq_is_const_or_type:
  !rs pqs i. mg_sol_seq rs pqs /\ i < LENGTH pqs
  ==> is_const_or_type (FST (EL i pqs))
  /\ is_const_or_type (SND (EL i pqs))
Proof
  fs[mg_sol_seq_def]
  >> rpt gen_tac
  >> rpt disch_tac
  >> match_mp_tac sol_seq_is_const_or_type
  >> fs[]
  >> goal_assum drule
QED

Theorem sol_seq_TYPE_SUBST:
  !rs pqs s. sol_seq rs pqs
  ==> sol_seq (MAP (λx. MAP (TYPE_SUBST s ## I) x ++ s) rs) pqs
Proof
  fs[sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY,FORALL_AND_THM,IMP_CONJ_THM]
  >> rpt strip_tac
  >> rfs[]
  >> first_x_assum $ drule_then assume_tac
  >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,GSYM LR_TYPE_SUBST_compose]
  >> ntac 2 $ qpat_x_assum `!x. _` $ irule_at Any
  >> fs[EL_MEM]
QED

Theorem mg_sol_seq_var_renaming:
  !rs pqs s. mg_sol_seq rs pqs /\ var_renaming s
  ==> mg_sol_seq (MAP (λx. MAP (TYPE_SUBST s ## I) x ++ s) rs) pqs
Proof
  rw[mg_sol_seq_def,sol_seq_TYPE_SUBST]
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `MAP (λx. MAP (TYPE_SUBST x ## I) (MAP SWAP s) ++ x) es`
  >> rpt strip_tac >> fs[]
  >> first_x_assum $ drule
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> conj_asm1_tac
  >- (fs[] >> drule_all sol_seq_is_const_or_type >> fs[])
  >> fs[]
  >> disch_then $ REWRITE_TAC o single o GSYM
  >> AP_TERM_TAC
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[LR_TYPE_SUBST_compose]
  >> conj_asm1_tac
  >- fs[LR_TYPE_SUBST_type_preserving]
  >> drule LR_TYPE_SUBST_NIL
  >> disch_then $ CONV_TAC o RHS_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> rw[LR_TYPE_SUBST_tyvars,Excl"TYPE_SUBST_def",GSYM TYPE_SUBST_compose,var_renaming_SWAP_id]
QED

Theorem mg_sol_seq_var_renaming':
  !rs pqs s. mg_sol_seq (MAP (λx. MAP (TYPE_SUBST s ## I) x ++ s) rs) pqs
  /\ var_renaming s
  ==> mg_sol_seq rs pqs
Proof
  rw[]
  >> drule_then assume_tac var_renaming_SWAP_IMP
  >> dxrule_then (drule_then assume_tac) mg_sol_seq_var_renaming
  >> rw[mg_sol_seq_def]
  >- (
    fs[mg_sol_seq_def]
    >> qpat_x_assum `!x. _` kall_tac
    >> drule_then assume_tac sol_seq_is_const_or_type
    >> fs[sol_seq_def,IMP_CONJ_THM,FORALL_AND_THM]
    >> rpt strip_tac
    >> rfs[]
    >> last_x_assum drule
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP,var_renaming_SWAP_LR_id]
    >> fs[]
  )
  >> fs[mg_sol_seq_def]
  >> first_x_assum $ drule_then strip_assume_tac
  >> qexists_tac `es`
  >> rw[]
  >> first_x_assum drule
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP,var_renaming_SWAP_LR_id]
  >> imp_res_tac sol_seq_LENGTH
  >> drule_then assume_tac sol_seq_is_const_or_type_FST
  >> fs[]
QED

Theorem mg_sol_seq_TYPE_SUBST:
  !rs pqs r c. mg_sol_seq rs pqs
  ==> mg_sol_seq (MAP (λx. MAP (TYPE_SUBST (renn r c) ## I) x ++ (renn r c)) rs) pqs
Proof
  rpt strip_tac
  >> match_mp_tac mg_sol_seq_var_renaming
  >> fs[renn_var_renaming]
QED

Theorem sol_seq_FILTER:
  !rs pqs r p q.
  sol_seq (rs ++ [r]) (pqs ++ [(p,q)])
  = sol_seq (rs ++ [FILTER ((λx. MEM x (MAP Tyvar (FV p))) o SND) r]) (pqs ++ [(p,q)])
Proof
  rw[sol_seq_def,EQ_IMP_THM,GSYM LE_LT1,LESS_OR_EQ,FORALL_AND_THM,DISJ_IMP_THM]
  >> TRY (
    qmatch_assum_rename_tac `SUC i < LENGTH _`
    >> rfs[]
    >> first_x_assum drule
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1]
    >> fs[]
  )
  >> TRY (
    qmatch_assum_rename_tac `SUC i = LENGTH _`
    >> rfs[]
    >> first_x_assum drule
    >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1,EL_APPEND1,EL_APPEND2,EL_APPEND2,EL_APPEND1,EL_APPEND2]
    >> rw[]
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_FILTER_SND_tyvars,o_DEF]
    >> fs[wf_pqs_def]
  )
QED

Theorem mg_sol_seq_FILTER:
  !rs pqs r p q.
  mg_sol_seq (rs ++ [r]) (pqs ++ [(p,q)])
  = mg_sol_seq (rs ++ [FILTER ((λx. MEM x (MAP Tyvar (FV p))) o SND) r]) (pqs ++ [(p,q)])
Proof
  rw[mg_sol_seq_def,GSYM sol_seq_FILTER,EQ_IMP_THM]
  >> `LENGTH pqs = LENGTH rs` by fs[sol_seq_def]
  >> first_x_assum $ drule_then strip_assume_tac
  >> goal_assum drule
  >> rpt strip_tac
  >> first_x_assum drule
  >> dep_rewrite.DEP_REWRITE_TAC[o_DEF,equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
  >> irule_at Any sol_seq_is_const_or_type_FST >> goal_assum drule
  >> fs[GSYM LE_LT1,LESS_OR_EQ]
  >> TRY (
    qmatch_assum_rename_tac `i < LENGTH _`
    >> rfs[]
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1]
    >> fs[]
  )
  >> TRY (
    qmatch_assum_rename_tac `i = LENGTH _`
    >> rfs[]
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND2]
    >> fs[]
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_FILTER_SND_tyvars,o_DEF]
    >> fs[wf_pqs_def,sol_seq_def]
  )
QED


(* various monotony properties (Lemma 5.2) *)

Theorem sol_seq_FV_LR_TYPE_SUBST_SND_FST:
  !pqs rs ctxt i.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i < LENGTH pqs ==>
      set(FV (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))) ⊆ set(FV (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs))))
Proof
  rw[monotone_def,PAIR_MAP,ELIM_UNCURRY,o_DEF,EVERY_MEM,list_subset_set]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rpt $ first_x_assum $ irule_at Any
  >> imp_res_tac EL_MEM
  >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_FST_j_SND_i:
  !pqs rs ctxt i j.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i < j /\ j < LENGTH pqs
  ==> set(FV (LR_TYPE_SUBST (EL j rs) (FST (EL j pqs)))) ⊆ set(FV (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs))))
Proof
  ntac 4 gen_tac
  >> Induct
  >> rw[]
  >> fs[RIGHT_CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) (SPEC_ALL sol_seq_def),EVERY_MEM,monotone_def,ELIM_UNCURRY,list_subset_set,wf_pqs_def]
  >> qpat_x_assum `_ < SUC _` mp_tac
  >> rw[GSYM LESS_EQ_IFF_LESS_SUC,LESS_OR_EQ] >> fs[]
  >> match_mp_tac SUBSET_TRANS
  >> goal_assum $ drule_at Any
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rpt $ first_x_assum $ irule_at Any
  >> conj_asm1_tac >- fs[EL_MEM]
  >> fs[]
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_LR_TYPE_SUBST_FST_j_SND_i:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i < j /\ j < LENGTH pqs
  ==>
    set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (FST (EL j pqs)))))
    ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))))
Proof
  rw[]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_FST_j_SND_i
  >> rpt $ irule_at Any LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> fs[]
  >> rpt $ goal_assum drule
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_FST_j_FST_i:
  !pqs rs ctxt i j.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set(FV (LR_TYPE_SUBST (EL j rs) (FST (EL j pqs))))
    ⊆ set(FV (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs))))
Proof
  rw[LESS_OR_EQ] >> fs[SUBSET_REFL]
  >> match_mp_tac SUBSET_TRANS
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_FST_j_SND_i
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_FST
  >> fs[]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_LR_TYPE_SUBST_FST_j_FST_i:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (FST (EL j pqs)))))
    ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))))
Proof
  rw[]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_FST_j_FST_i
  >> ntac 2 $ irule_at Any LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> fs[]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_SND_j_SND_i:
  !pqs rs ctxt i j.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set(FV (LR_TYPE_SUBST (EL j rs) (SND (EL j pqs))))
    ⊆ set(FV (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs))))
Proof
  rw[LESS_OR_EQ]
  >> fs[SUBSET_REFL]
  >> match_mp_tac SUBSET_TRANS
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_FST_j_SND_i
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_FST
  >> fs[]
  >> rpt $ goal_assum drule
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_LR_TYPE_SUBST_SND_j_SND_i:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (SND (EL j pqs)))))
    ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))))
Proof
  rw[LESS_OR_EQ]
  >> fs[SUBSET_REFL]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_j_SND_i
  >> ntac 2 $ irule_at Any LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> fs[]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_SND_j_FST_i:
  !pqs rs ctxt i j.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set(FV (LR_TYPE_SUBST (EL j rs) (SND (EL j pqs))))
    ⊆ set(FV (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs))))
Proof
  rw[]
  >> match_mp_tac SUBSET_TRANS
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_j_SND_i
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_FST
  >> fs[]
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem sol_seq_FV_LR_TYPE_SUBST_LR_TYPE_SUBST_SND_j_FST_i:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs
  ==>
    set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (SND (EL j pqs)))))
    ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))))
Proof
  rw[]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> irule_at Any sol_seq_FV_LR_TYPE_SUBST_SND_j_FST_i
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> ntac 2 $ irule_at Any LR_TYPE_SUBST_type_preserving
  >> fs[]
  >> rpt $ goal_assum $ drule_at Any
QED

(* properties of bijections (which wlog are var_renamings) *)

Theorem bij_ALL_DISTINCT_FST:
  !e e' t t'.
  EVERY ((λx. MEM x (MAP Tyvar (tyvars t))) o SND) e
  /\ TYPE_SUBST e' t' = t
  /\ TYPE_SUBST (clean_tysubst e) t = t'
  ==> ALL_DISTINCT (MAP FST (clean_tysubst e))
Proof
  rw[]
  >> pop_assum mp_tac
  >> fs[TYPE_SUBST_compose]
  >> CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL])))
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def,Once EQ_SYM_EQ,EL_ALL_DISTINCT_EL_EQ,EQ_IMP_THM,EL_MAP]
  >> imp_res_tac EL_MEM
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] clean_tysubst_SND_Tyvar)
  >> fs[ELIM_UNCURRY,GSYM EVERY_MAP_o,EVERY_MEM]
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> rpt (dxrule_then assume_tac (REWRITE_RULE[SUBSET_DEF] (CONJUNCT2 clean_tysubst_FST_SND_SUBSET)))
  >> last_assum (dxrule_then assume_tac)
  >> last_x_assum (dxrule_then assume_tac)
  >> gvs[MEM_Tyvar_MAP_Tyvar]
  >> last_assum (dxrule_then assume_tac)
  >> last_x_assum (dxrule_then assume_tac)
  >> qspec_then `e` assume_tac (REWRITE_RULE[Once (GSYM FST_SWAP_SND),GSYM MAP_MAP_o] clean_tysubst_ALL_DISTINCT_MAP_SND)
  >> dxrule_then assume_tac ALOOKUP_ALL_DISTINCT_MEM
  >> fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,MEM_MAP_SWAP',SWAP_def]
  >> ntac 2 (qpat_x_assum `MEM (EL _ _) _` (assume_tac o ONCE_REWRITE_RULE[GSYM PAIR]))
  >> qpat_assum `!x. _` (dxrule_then assume_tac)
  >> qpat_x_assum `!x. _` (dxrule_then assume_tac)
  >> fs[GSYM SWAP_eq,o_DEF,SWAP_def,LAMBDA_PROD,ALOOKUP_MAP,
    Q.prove(`!f s. MAP SWAP (MAP f s) = MAP (SWAP o f o SWAP) (MAP SWAP s)`,
      fs[MAP_MAP_o,SWAP_eq,o_DEF,ELIM_UNCURRY])
  ]
  >> gvs[]
  >> qspec_then `e` mp_tac clean_tysubst_ALL_DISTINCT_MAP_SND
  >> disch_then (rw o single o GSYM o REWRITE_RULE[EL_ALL_DISTINCT_EL_EQ])
  >> fs[EL_MAP]
QED

Theorem bij_props:
  !t' t e e'.
  TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
  ==>
    ALL_DISTINCT (MAP FST (FILTER ((λx. MEM x (MAP Tyvar (tyvars t))) o SND) (clean_tysubst e)))
Proof
  rpt strip_tac
  >> REWRITE_TAC[GSYM clean_tysubst_FILTER_SND]
  >> match_mp_tac bij_ALL_DISTINCT_FST
  >> goal_assum $ drule_at Any
  >> fs[EVERY_FILTER,GSYM clean_tysubst_TYPE_SUBST_eq,o_DEF,GSYM TYPE_SUBST_FILTER_SND_tyvars2]
QED

Theorem bij_props_inj1:
  !t' t e e'.
  TYPE_SUBST e' t' = t /\ TYPE_SUBST e t = t'
  ==> !a. MEM a (tyvars t') ==> TYPE_SUBST e (TYPE_SUBST e' (Tyvar a)) = Tyvar a
Proof
  rpt strip_tac
  >> qmatch_goalsub_rename_tac `TYPE_SUBST e (TYPE_SUBST e' _)`
  >> qpat_x_assum `TYPE_SUBST e _ = _` mp_tac
  >> qpat_x_assum `TYPE_SUBST _ _ = _` $ ONCE_REWRITE_TAC o single o GSYM
  >> CONV_TAC $ LAND_CONV $ RAND_CONV $ ONCE_REWRITE_CONV $ single $ GSYM TYPE_SUBST_NIL
  >> REWRITE_TAC[TYPE_SUBST_compose,TYPE_SUBST_tyvars]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> fs[TYPE_SUBST_NIL]
QED

Theorem bij_props_all_Tyvar:
  !t' t e e'.
  TYPE_SUBST e' t' = t /\ TYPE_SUBST e t = t'
  ==> !a. MEM a (tyvars t') ==> ?b. TYPE_SUBST e' (Tyvar a) = Tyvar b
Proof
  rpt strip_tac
  >> qmatch_goalsub_rename_tac `TYPE_SUBST e' (Tyvar a)`
  >> qpat_x_assum `TYPE_SUBST e' _ = _` assume_tac
  >> drule_all bij_props_inj1
  >> qabbrev_tac `ty = TYPE_SUBST e' (Tyvar a)`
  >> Cases_on `ty` >> fs[]
QED

Theorem bij_props_inj:
  !t' t e e'.
  TYPE_SUBST e' t' = t /\ TYPE_SUBST e t = t'
  ==> !a b. MEM a (tyvars t') /\ MEM b (tyvars t') /\
    TYPE_SUBST e' (Tyvar a) = TYPE_SUBST e' (Tyvar b)
    ==> a = b
Proof
  rpt gen_tac >> strip_tac
  >> rev_drule_then drule bij_props_inj1
  >> rpt strip_tac
  >> first_assum drule
  >> first_x_assum $ rev_drule
  >> rw[]
QED

Theorem bij_props_restr_tyvars:
  !t t' e e'. TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
  /\ EVERY ((λx. MEM x (MAP Tyvar (tyvars t))) o SND) e
  /\ ALL_DISTINCT (MAP SND e)
  ==> EVERY ((λx. MEM x (MAP Tyvar (tyvars t'))) o FST) e
Proof
  rpt strip_tac
  >> fs[EVERY_MEM]
  >> rev_drule_then drule bij_props_all_Tyvar
  >> rpt strip_tac
  >> first_x_assum $ drule_then $ strip_assume_tac o REWRITE_RULE[MEM_MAP]
  >> first_x_assum $ drule_then $ strip_assume_tac
  >> fs[GSYM subtype_at_tyvars]
  >> dxrule_then (qspec_then `e` assume_tac) subtype_at_TYPE_SUBST
  >> qpat_x_assum `TYPE_SUBST e _ = _` $ (qspec_then `p` assume_tac) o ONCE_REWRITE_RULE[subtype_at_eq]
  >> fs[REV_ASSOCD_ALOOKUP,GSYM SWAP_eq]
  >> qpat_x_assum `ALL_DISTINCT _` $ assume_tac o (ONCE_REWRITE_RULE o single $ GSYM FST_SWAP_SND)
  >> rename1`MEM x e` >> PairCases_on `x`
  >> fs[GSYM MAP_MAP_o,Once $ GSYM MEM_MAP_SWAP,SWAP_def]
  >> FULL_CASE_TAC
  >- (
    drule $ Q.ISPEC `FST` MEM_MAP_f
    >> fs[ALOOKUP_NONE]
  )
  >> drule MEM_ALOOKUP
  >> disch_then $ gvs o single o GSYM
  >> metis_tac[ALL_DISTINCT_FST_MEMs,
    MEM_MAP,
    cj 1 $ Ho_Rewrite.REWRITE_RULE[PULL_EXISTS,EQ_IMP_THM]subtype_at_tyvars
  ]
QED

Theorem bij_props_wlog:
  !t t' e e'. TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
  ==> ?s. TYPE_SUBST s t = t' /\ ALL_DISTINCT (MAP SND s)
  /\ ALL_DISTINCT (MAP FST s)
  /\ EVERY (UNCURRY $<>) s
  /\ EVERY ((λx. MEM x (MAP Tyvar (tyvars t))) o SND) s
  /\ EVERY ((λx. MEM x (MAP Tyvar (tyvars t'))) o FST) s
  /\ EVERY (λx. ?a b. x = (Tyvar a,Tyvar b)) s
Proof
  rpt strip_tac
  >> rev_drule_then (drule_then assume_tac) bij_props
  >> qpat_x_assum `TYPE_SUBST e _ = _` $ assume_tac o ONCE_REWRITE_RULE[TYPE_SUBST_FILTER_SND_tyvars2] o ONCE_REWRITE_RULE[clean_tysubst_TYPE_SUBST_eq]
  >> drule_then drule bij_props_all_Tyvar
  >> rev_drule_then drule bij_props_all_Tyvar
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST ee`
  >> rpt strip_tac
  >> qexists_tac `ee`
  >> asm_rewrite_tac[]
  >> conj_asm1_tac
  >- (
    fs[EVERY_FILTER,Abbr`ee`]
    >> match_mp_tac $ cj 2 ALL_DISTINCT_MAP_PAIR_FILTER
    >> fs[clean_tysubst_ALL_DISTINCT_MAP_SND]
  )
  >> conj_tac >- fs[o_DEF]
  >> conj_tac
  >- (
    qspec_then `e` mp_tac clean_tysubst_ineq
    >> fs[Abbr`ee`,EVERY_FILTER]
    >> match_mp_tac (Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC)
    >> fs[ELIM_UNCURRY]
  )
  >> conj_asm1_tac
  >- fs[EVERY_FILTER,Abbr`ee`]
  >> conj_asm1_tac
  >- metis_tac[bij_props_restr_tyvars]
  >> fs[EVERY_MEM,MEM_MAP]
  >> metis_tac[PAIR]
QED

Theorem bij_props_var_renaming:
  !e e' t t'. TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
  ==> ?s. var_renaming s /\ TYPE_SUBST s t = TYPE_SUBST e t
Proof
  rpt strip_tac
  >> rev_drule_then drule bij_props_wlog
  >> rpt strip_tac
  >> qpat_x_assum `TYPE_SUBST e t = _` $ REWRITE_TAC o single
  >> Cases_on `set (MAP FST s) = set (MAP SND s)`
  >- (
    goal_assum $ drule_at Any
    >> fs[var_renaming_eq,rename_bij_def]
  )
  >> qexists_tac `ALOOKUP_bij s`
  >> rev_drule_all_then strip_assume_tac ALOOKUP_bij_prop
  >> conj_tac
  >- (
    fs[o_DEF,ELIM_UNCURRY,var_renaming_eq,rename_bij_def]
    >> qmatch_goalsub_abbrev_tac `EVERY f`
    >> qpat_x_assum `EVERY f s` mp_tac
    >> qunabbrev_tac `f`
    >> fs[LAMBDA_PROD,EVERY_MAP_PAIR,GSYM PULL_EXISTS]
    >> fs[EVERY_MEM,SUBSET_DEF]
  )
  >> qpat_assum `TYPE_SUBST s t = _` $ REWRITE_TAC o single o GSYM
  >> rfs[TYPE_SUBST_tyvars]
  >> rpt strip_tac
  >> Cases_on `MEM (Tyvar x) (MAP SND s)`
  >- (
    REWRITE_TAC[GSYM TYPE_SUBST_def]
    >> fs[TYPE_SUBST_drop_suffix]
  )
  >> `~MEM (Tyvar x) (MAP FST s)` by (
    drule_then (drule_at Any) clean_tysubst_id
    >> impl_tac
    >- fs[o_DEF,EVERY_MAP_PAIR,LAMBDA_PROD,GSYM PULL_EXISTS,EVERY_MAP]
    >> disch_then $ (fn x => fs $ single $ Once $ GSYM x >> assume_tac x)
    >> drule_then (drule_then assume_tac) bij_props_inj
    >> drule_then assume_tac TYPE_SUBST_drop_all
    >> disch_then $ strip_assume_tac o REWRITE_RULE[MEM_MAP]
    >> rename1`MEM y (clean_tysubst _)` >> PairCases_on `y`
    >> qpat_x_assum `clean_tysubst _ = _` (fn x => fs[x,Excl"TYPE_SUBST_def"])
    >> qpat_x_assum `EVERY (_ o SND) s` $ (drule_then assume_tac) o REWRITE_RULE[EVERY_MEM]
    >> qpat_x_assum `EVERY (λ(x,y). _ <> _) s` $ (drule_then assume_tac) o REWRITE_RULE[EVERY_MEM]
    >> gvs[MEM_MAP]
    >> first_x_assum $ drule_then $ rev_drule_then assume_tac
    >> drule_then (drule_then assume_tac) TYPE_SUBST_MEM'
    >> gvs[]
  )
  >> rpt $ first_x_assum $ drule_at Concl o REWRITE_RULE[SUBSET_DEF]
  >> fs[TYPE_SUBST_drop_prefix,TYPE_SUBST_drop_all,Excl"TYPE_SUBST_def",GSYM TYPE_SUBST_def]
QED

Theorem is_instance_NOT_is_instance_imp:
  !e t t'. TYPE_SUBST e t = t' /\ (!e'. TYPE_SUBST e' t' <> t)
  ==>
  ((?a m l. MEM a (tyvars t) /\ MEM (Tyvar a) (MAP SND e) /\ TYPE_SUBST e (Tyvar a) = Tyapp m l)
  \/ (?a b. a <> b /\ MEM a (tyvars t) /\ MEM b (tyvars t)
    /\ TYPE_SUBST e (Tyvar a) = TYPE_SUBST e (Tyvar b)))
Proof
  rpt gen_tac
  >> CONV_TAC $ LAND_CONV $ LAND_CONV $ ONCE_REWRITE_CONV $ single TYPE_SUBST_wlog_eq
  >> rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST ee`
  >> `set (MAP SND ee) ⊆ set (MAP Tyvar (tyvars t)) ∩ set (MAP SND e)` by (
    unabbrev_all_tac
    >> rw[SUBSET_DEF,GSYM FILTER_MAP,MEM_FILTER,INTER_DEF,
      REWRITE_RULE[SUBSET_DEF] clean_tysubst_FST_SND_SUBSET]
  )
  >> `ALL_DISTINCT (MAP SND ee)` by (
    unabbrev_all_tac
    >> match_mp_tac $ cj 2 $ ALL_DISTINCT_MAP_PAIR_FILTER
    >> fs[clean_tysubst_ALL_DISTINCT_MAP_SND]
  )
  >> `EVERY (UNCURRY $<>) ee /\ EVERY (λx. ∃a. SND x = Tyvar a) ee` by (
    unabbrev_all_tac
    >> dep_rewrite.DEP_REWRITE_TAC[EVERY_FILTER_IMP]
    >> fs[clean_tysubst_prop]
  )
  >> `!a. MEM a (tyvars t) ==> TYPE_SUBST e (Tyvar a) = TYPE_SUBST ee (Tyvar a)` by (
    rpt strip_tac
    >> unabbrev_all_tac
    >> drule_then (qspecl_then [`clean_tysubst e`,`[]`] mp_tac) TYPE_SUBST_FILTER_MEM1
    >> fs[Excl"TYPE_SUBST_def",o_DEF,GSYM clean_tysubst_TYPE_SUBST_eq]
  )
  >> qpat_x_assum `Abbrev _` kall_tac
  >> CCONTR_TAC
  >> fs[Excl"TYPE_SUBST_def",DISJ_EQ_IMP,AND_IMP_INTRO]
  >> `ALL_DISTINCT (MAP FST ee)` by (
    rw[EL_ALL_DISTINCT_EL_EQ,Excl"TYPE_SUBST_def",EQ_IMP_THM]
    >> `MEM (EL n1 ee) ee /\ MEM (EL n2 ee) ee` by fs[EL_MEM]
    >> qpat_assum `ALL_DISTINCT _` $ fs o single o GSYM o REWRITE_RULE[EL_ALL_DISTINCT_EL_EQ]
    >> imp_res_tac $ Q.ISPEC `SND` MEM_MAP_f
    >> ntac 2 $ qpat_x_assum `_ ⊆ _` $ imp_res_tac o REWRITE_RULE[SUBSET_DEF]
    >> ntac 2 $ qpat_x_assum `MEM _ (MAP Tyvar _)` $ strip_assume_tac o REWRITE_RULE[MEM_MAP]
    >> first_x_assum $ drule_at_then Any (rev_drule_at_then Any assume_tac)
    >> gs[]
    >> rw[EL_MAP]
    >> first_x_assum $ match_mp_tac o Ho_Rewrite.ONCE_REWRITE_RULE[GSYM MONO_NOT_EQ]
    >> qspec_then `ee` assume_tac TYPE_SUBST_MEM_MAP_SND
    >> first_assum $ drule_then strip_assume_tac
    >> first_x_assum $ rev_drule_then strip_assume_tac
    >> last_assum $ drule_then assume_tac
    >> last_x_assum $ rev_drule_then assume_tac
    >> gs[]
    >> ntac 2 $ qpat_x_assum `MEM (EL _ _) _` $ assume_tac o ONCE_REWRITE_RULE[GSYM PAIR]
    >> drule_then assume_tac ALL_DISTINCT_SND_MEMs
    >> first_assum $ dxrule_then mp_tac
    >> first_x_assum $ dxrule_then mp_tac
    >> asm_rewrite_tac[]
    >> ntac 2 $ disch_then imp_res_tac
    >> gs[EL_MAP]
  )
  >> `EVERY (λx. ?a b. x = (Tyvar a,Tyvar b)) ee` by (
    fs[LAMBDA_PROD,EVERY_MAP_PAIR,GSYM PULL_EXISTS]
    >> reverse conj_tac
    >- fs[EVERY_MAP_o,o_DEF,LAMBDA_PROD]
    >> fs[EVERY_MEM,ELIM_UNCURRY]
    >> REWRITE_TAC[MEM_MAP]
    >> ONCE_REWRITE_TAC[GSYM PAIR]
    >> rpt strip_tac
    >> first_assum $ drule_then strip_assume_tac
    >> drule_at_then Any (drule_at Any) TYPE_SUBST_MEM
    >> impl_tac
    >- (
      rw[EVERY_MEM,ELIM_UNCURRY]
      >> first_x_assum $ drule_then strip_assume_tac
      >> fs[]
    )
    >> drule_then assume_tac $ Q.ISPEC `SND` MEM_MAP_f
    >> ntac 2 $ qpat_x_assum `_ ⊆ _` $ imp_res_tac o REWRITE_RULE[SUBSET_DEF]
    >> qpat_x_assum `MEM _ (MAP Tyvar _)` $ strip_assume_tac o REWRITE_RULE[MEM_MAP]
    >> gvs[]
    >> qpat_x_assum `!a b c. _` $ drule_then drule
    >> Cases_on `FST y`
    >> fs[]
  )
  >> first_x_assum $ qspec_then `MAP SWAP ee` match_mp_tac
  >> rw[TYPE_SUBST_compose,Excl"TYPE_SUBST_def"]
  >> CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV o single $ GSYM TYPE_SUBST_NIL
  >> rw[TYPE_SUBST_tyvars,Excl"TYPE_SUBST_def",GSYM TYPE_SUBST_def,Once EQ_SYM_EQ,GSYM TYPE_SUBST_compose]
  >> Cases_on `MEM (Tyvar x) (MAP SND ee)`
  >- (
    drule_then strip_assume_tac TYPE_SUBST_MEM_MAP_SND
    >> qpat_x_assum `EVERY _ _` $ imp_res_tac o REWRITE_RULE[EVERY_MEM]
    >> gvs[]
    >> drule_then assume_tac $ Q.ISPEC `FST` MEM_MAP_f
    >> fs[Once $ GSYM FST_SWAP_SND,GSYM MAP_MAP_o]
    >> drule_then strip_assume_tac TYPE_SUBST_MEM_MAP_SND
    >> fs[MEM_MAP_SWAP',SWAP_def,MAP_MAP_o,FST_SWAP_SND]
    >> drule_then match_mp_tac ALL_DISTINCT_FST_MEMs
    >> rpt $ goal_assum drule
  )
  >> Cases_on `MEM (Tyvar x) (MAP SND (MAP SWAP ee))`
  >> fs[TYPE_SUBST_drop_all,Excl"TYPE_SUBST_def"]
  >> drule_then strip_assume_tac TYPE_SUBST_MEM_MAP_SND
  >> imp_res_tac TYPE_SUBST_drop_all
  >> fs[MEM_MAP_SWAP',SWAP_def,EVERY_MEM]
  >> drule_then assume_tac $ Q.ISPEC `SND` MEM_MAP_f
  >> ntac 2 $ qpat_x_assum `_ ⊆ _` $ imp_res_tac o REWRITE_RULE[SUBSET_DEF]
  >> qpat_x_assum `!x. MEM _ _ ==> _` $ imp_res_tac
  >> CCONTR_TAC
  >> gvs[MEM_Tyvar_MAP_Tyvar]
  >> ntac 3 $ qpat_x_assum `!x. MEM _ _ ==> _` $ imp_res_tac
  >> gvs[]
  >> first_x_assum $ rev_drule_at_then Any (drule_at Any)
  >> fs[]
  >> qspec_then `ee` mp_tac TYPE_SUBST_MEM_MAP_SND
  >> disch_then $ drule_then strip_assume_tac
  >> drule_then (rev_drule_then drule) ALL_DISTINCT_SND_MEMs
  >> fs[]
QED

Theorem renaming_CARD_LESS_OR_EQ:
  !s t. (!a. MEM a (tyvars t) ==> ?b. TYPE_SUBST s (Tyvar a) = Tyvar b)
  ==> CARD (set (tyvars (TYPE_SUBST s t))) <= CARD (set (tyvars t))
Proof
  rw[tyvars_TYPE_SUBST] >>
  qmatch_goalsub_abbrev_tac ‘CARD a1 ≤ _’ >>
  ‘a1 = IMAGE (λ a. @b. REV_ASSOCD (Tyvar a) s (Tyvar a) = Tyvar b) (set(tyvars t))’
    by(rw[Abbr ‘a1’,SET_EQ_SUBSET,SUBSET_DEF] >>
       res_tac >> fs[] >>
       first_x_assum(irule_at Any) >>
       gs[tyvars_def]) >>
  pop_assum SUBST_ALL_TAC >>
  pop_assum kall_tac >>
  match_mp_tac CARD_IMAGE >>
  rw[]
QED

Theorem renaming_CARD_LESS_OR_EQ':
  !t. (∀a m l.
            MEM a (tyvars t) ∧ MEM (Tyvar a) (MAP SND i) ∧
            Tyapp m l = REV_ASSOCD (Tyvar a) i (Tyvar a) ⇒
            l = [])
  ==> CARD (set (tyvars (TYPE_SUBST i t))) <= CARD (set (tyvars t))
Proof
  rw[tyvars_TYPE_SUBST] >>
  ‘∃UU V. (set(tyvars t) = (UU ∪ V)) ∧
         UU ⊆ set(tyvars t) ∧
         V ⊆ set(tyvars t) ∧
         (∀u. u ∈ UU ⇒ ∃b. TYPE_SUBST i (Tyvar u) = Tyvar b) ∧
         (∀v. v ∈ V ⇒ ∃m l. Tyapp m l = REV_ASSOCD (Tyvar v) i (Tyvar v))
  ’
  by(qexists_tac ‘{u | ∃x. TYPE_SUBST i (Tyvar u) = Tyvar x ∧ MEM u (tyvars t)}’ >>
     qexists_tac ‘{v | ∃m l. Tyapp m l = REV_ASSOCD (Tyvar v) i (Tyvar v) ∧ MEM v (tyvars t)}’ >>
     rw[SUBSET_DEF] >> gs[] >>
     rw[SET_EQ_SUBSET,SUBSET_DEF] >- (Cases_on ‘REV_ASSOCD (Tyvar x) i (Tyvar x)’ >> fs[]) >>
     metis_tac[]) >>
  qpat_x_assum ‘_ = _ ∪ _’ (rw o single) >>
  rw[RIGHT_AND_OVER_OR,EXISTS_OR_THM,GSPEC_OR] >>
  qmatch_goalsub_abbrev_tac ‘CARD(_ ∪ VV)’ >>
  ‘VV = ∅’
    by(ONCE_REWRITE_TAC[SET_EQ_SUBSET] >>
       reverse conj_tac >- simp[] >>
       ONCE_REWRITE_TAC[SUBSET_DEF] >>
       rpt strip_tac >>
       gs[Abbr ‘VV’] >>
       drule_all_then strip_assume_tac SUBSET_THM >>
       first_x_assum drule_all >> strip_tac >>
       first_x_assum drule >>
       disch_then(drule_at (Pos last)) >>
       reverse impl_tac >- (strip_tac >> rveq >> qpat_x_assum ‘Tyapp _ _ = _’ (assume_tac o GSYM) >> gs[tyvars_def]) >>
       qpat_x_assum ‘Tyapp _ _ = _’ (assume_tac o GSYM) >>
       fs[REV_ASSOCD_ALOOKUP,AllCaseEqs()] >>
       imp_res_tac ALOOKUP_MEM >>
       gs[MEM_MAP] >>
       pairarg_tac >> gs[] >>
       metis_tac[FST,SND,PAIR]) >>
  pop_assum SUBST_ALL_TAC >>
  pop_assum kall_tac >>
  gs[] >>
  match_mp_tac LESS_EQ_TRANS >>
  irule_at (Pos last) CARD_SUBSET >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (metis_tac[SUBSET_FINITE,FINITE_LIST_TO_SET]) >>
  irule_at (Pos hd) (SUBSET_UNION |> CONJUNCT1) >>
  qmatch_goalsub_abbrev_tac ‘CARD a1 ≤ _’ >>
  ‘a1 = IMAGE (λ a. @b. REV_ASSOCD (Tyvar a) i (Tyvar a) = Tyvar b) UU’
    by(rw[Abbr ‘a1’,SET_EQ_SUBSET,SUBSET_DEF] >>
       drule_all_then strip_assume_tac SUBSET_THM >>
       res_tac >> fs[] >>
       first_x_assum(irule_at Any) >>
       gs[tyvars_def]) >>
  pop_assum SUBST_ALL_TAC >>
  pop_assum kall_tac >>
  match_mp_tac CARD_IMAGE >>
  rw[] >>
  metis_tac[SUBSET_FINITE,FINITE_LIST_TO_SET]
QED

Theorem CARD_BIGUNION_BOUNDED_SETS:
  ∀n s.
    FINITE s ∧ (∀e. e ∈ s ⇒ FINITE e ∧ CARD e ≤ n) ⇒
    CARD (BIGUNION s) ≤ CARD s * n
Proof
  strip_tac >> simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[CARD_UNION_EQN,MULT_CLAUSES,DISJ_IMP_THM,FORALL_AND_THM] >>
  res_tac >>
  intLib.COOPER_TAC
QED

Theorem CARD_BIGUNION_BOUNDED_SETS_LESS:
  ∀n s.
    FINITE s ∧ (∀e. e ∈ s ⇒ FINITE e ∧ CARD e ≤ n) ∧
    e ∈ s ∧ CARD e < n
    ⇒
    CARD (BIGUNION s) < CARD s * n
Proof
  strip_tac >> simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[CARD_UNION_EQN,MULT_CLAUSES,DISJ_IMP_THM,FORALL_AND_THM] >>
  res_tac >>
  gvs[] >>
  drule_all CARD_BIGUNION_BOUNDED_SETS >>
  intLib.COOPER_TAC
QED

Theorem is_instance_NOT_is_instance_imp':
  !t t'. is_instance t t' /\ ~(is_instance t' t)
  ==> CARD (set (tyvars t')) < CARD (set (tyvars t))
    \/ type_size' t < type_size' t'
Proof
  rpt strip_tac
  >> fs[]
  >> drule_then dxrule $ GSYM is_instance_NOT_is_instance_imp
  >> qmatch_goalsub_abbrev_tac `not_tyvar_only \/ inj ==> _`
  >> rw[Once DISJ_EQ_IMP]
  >> Cases_on `∃a m l. MEM a (tyvars t) ∧ MEM (Tyvar a) (MAP SND i) ∧
      Tyapp m l = TYPE_SUBST i (Tyvar a) /\ 0 < LENGTH l`
  >- (
    disj2_tac
    >> match_mp_tac type_size_TYPE_SUBST_LESS
    >> rw[Once EQ_SYM_EQ]
    >> rpt $ goal_assum $ drule_at Any
  )
  >> fs[DISJ_EQ_IMP,AND_IMP_INTRO]
  >> rw[NOT_LESS]
  >> drule renaming_CARD_LESS_OR_EQ'
  >> strip_tac
  >> dxrule_all_then strip_assume_tac LESS_EQUAL_ANTISYM
  >> Cases_on ‘not_tyvar_only’
  >> gs[]
  >- (
     res_tac >> rveq >>
     gs[tyvars_TYPE_SUBST] >>
     pop_assum mp_tac >>
     qmatch_goalsub_abbrev_tac ‘CARD a1 = CARD _’ >>
     ‘a1 = {v | ∃x. MEM x (tyvars t) ∧ x ≠ a ∧
                    MEM v (tyvars (REV_ASSOCD (Tyvar x) i (Tyvar x)))}’
       by(rw[Abbr ‘a1’,SET_EQ_SUBSET,SUBSET_DEF] >>
          res_tac >> fs[] >-
            (Cases_on ‘a = x'’ >> rveq >>
             qpat_x_assum ‘Tyapp _ _ = REV_ASSOCD _ _ _’ (assume_tac o GSYM) >>
             gs[tyvars_def] >> metis_tac[]) >>
          metis_tac[]) >>
     pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
     strip_tac >>
     ‘∃b. MEM b (tyvars t) ∧ 1 < CARD(set(tyvars (REV_ASSOCD (Tyvar b) i (Tyvar b))))’
       by(spose_not_then strip_assume_tac >>
          gs[NOT_LESS] >>
          qmatch_asmsub_abbrev_tac ‘CARD a1 = CARD _’ >>
          ‘a1 = BIGUNION {set(tyvars (REV_ASSOCD (Tyvar x) i (Tyvar x))) | MEM x (tyvars t) ∧ x ≠ a}’
            by(rw[Abbr ‘a1’,SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[]) >>
          pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
          qmatch_asmsub_abbrev_tac ‘BIGUNION a1’ >>
          ‘CARD(BIGUNION a1) ≤ CARD a1 * 1’
            by(match_mp_tac CARD_BIGUNION_BOUNDED_SETS >>
               rw[Abbr ‘a1’] >> rw[] >>
               rw[GSPEC_IMAGE,o_DEF] >>
               match_mp_tac IMAGE_FINITE >>
               match_mp_tac(MP_CANON SUBSET_FINITE) >>
               qexists_tac ‘set(tyvars t)’ >> rw[SUBSET_DEF,IN_DEF]) >>
          gs[] >>
          ‘CARD a1 ≤ CARD(set(tyvars t)) - 1’
            by(rw[Abbr ‘a1’] >>
               match_mp_tac LESS_EQ_TRANS >>
               rw[GSPEC_IMAGE,o_DEF] >>
               irule_at (Pos hd) CARD_IMAGE >>
               conj_asm1_tac
               >- (match_mp_tac(MP_CANON SUBSET_FINITE) >>
                   qexists_tac ‘set(tyvars t)’ >> rw[SUBSET_DEF,IN_DEF]) >>
               ‘(λx. MEM x (tyvars t) ∧ x ≠ a) = set(tyvars t) DIFF {a}’
                 by(rw[SET_EQ_SUBSET,SUBSET_DEF] >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               simp[CARD_DIFF] >>
               ‘(set (tyvars t) ∩ {a}) = {a}’
                 by(rw[SET_EQ_SUBSET,SUBSET_DEF,INTER_DEF] >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               simp[]) >>
          dxrule_all_then strip_assume_tac LESS_EQ_TRANS >>
          ‘0 < CARD(set (tyvars t))’
            by(spose_not_then strip_assume_tac >>
               gs[]) >>
          intLib.COOPER_TAC) >>
     spose_not_then kall_tac >>
     Cases_on ‘REV_ASSOCD (Tyvar b) i (Tyvar b)’ >- gs[tyvars_def] >>
     first_x_assum drule >>
     disch_then (drule_at (Pos last) o GSYM) >>
     impl_tac
     >- (fs[REV_ASSOCD_ALOOKUP,AllCaseEqs()] >>
         imp_res_tac ALOOKUP_MEM >>
         gs[MEM_MAP] >>
         pairarg_tac >> gs[] >>
         rveq >> gs[] >>
         pairarg_tac >> gs[] >> rveq >> gs[] >>
         metis_tac[FST,SND,PAIR]) >>
     strip_tac >> rveq >> gs[tyvars_def]
  ) >>
  gs[Abbr ‘inj’] >>
  gs[DISJ_EQ_IMP] >>
  qmatch_asmsub_abbrev_tac ‘CARD a1 = _’ >>
  ‘a1 = IMAGE (λ a. @b. REV_ASSOCD (Tyvar a) i (Tyvar a) = Tyvar b) (set(tyvars t))’
    by(rw[Abbr ‘a1’,SET_EQ_SUBSET,SUBSET_DEF,tyvars_TYPE_SUBST] >-
         (first_assum(irule_at Any) >>
          Cases_on ‘REV_ASSOCD (Tyvar x') i (Tyvar x')’ >> (* TODO: generated names *)
          gs[tyvars_def,MEM_FOLDR_LIST_UNION] >>
          last_x_assum drule >>
          disch_then(qspecl_then [‘m’,‘l’] mp_tac) >>
          reverse impl_tac >- metis_tac[] >>
          fs[REV_ASSOCD_ALOOKUP,AllCaseEqs()] >>
          imp_res_tac ALOOKUP_MEM >>
          gs[MEM_MAP] >>
          pairarg_tac >> gs[] >>
          rveq >> gs[] >>
          pairarg_tac >> gs[] >> rveq >> gs[] >>
          metis_tac[FST,SND,PAIR]) >>
       first_assum(irule_at Any) >>
       Cases_on ‘REV_ASSOCD (Tyvar a') i (Tyvar a')’ >> gs[tyvars_def] >>  (* TODO: generated names *)
       gs[tyvars_def,MEM_FOLDR_LIST_UNION] >>
       last_x_assum drule >>
       disch_then(qspecl_then [‘m’,‘l’] mp_tac) >>
       reverse impl_tac >- metis_tac[] >>
       fs[REV_ASSOCD_ALOOKUP,AllCaseEqs()] >>
       imp_res_tac ALOOKUP_MEM >>
       gs[MEM_MAP] >>
       pairarg_tac >> gs[] >>
       rveq >> gs[] >>
       pairarg_tac >> gs[] >> rveq >> gs[] >>
       metis_tac[FST,SND,PAIR]) >>
  pop_assum SUBST_ALL_TAC >>
  pop_assum kall_tac >>
  drule_at (Pos last) CARD_IMAGE_EQ_BIJ >>
  impl_tac >- simp[] >>
  rw[BIJ_DEF,INJ_DEF] >>
  first_x_assum drule >>
  disch_then(qspec_then ‘b’ mp_tac) >>
  simp[]
QED

Theorem equiv_ts_on_mg_sol:
  !e e' t t' r r' p.
  TYPE_SUBST e (TYPE_SUBST r p) = TYPE_SUBST r' p
  /\ TYPE_SUBST e' (TYPE_SUBST r' p) = TYPE_SUBST r p
  ==> equiv_ts_on r r' (tyvars p)
Proof
  rpt strip_tac
  >> fs[equiv_ts_on_def,equal_ts_on_def,Excl"TYPE_SUBST_def"]
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST e t`
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST e' t'`
  >> fs o single $ REWRITE_RULE[GSYM TYPE_SUBST_def] $ GSYM TYPE_SUBST_tyvars
  >> fs[GSYM TYPE_SUBST_compose]
  >> dxrule_then (drule_then strip_assume_tac) bij_props_wlog
  >> drule_all_then strip_assume_tac bij_props_var_renaming
  >> metis_tac[TYPE_SUBST_instance_tyvars]
QED

(* Lemma 3.1 *)
Theorem var_renaming_type_size:
  !e ty. var_renaming e ==> type_size' (TYPE_SUBST e ty) =  type_size' ty
Proof
  gen_tac >> ho_match_mp_tac type_ind
  >> rw[Excl"TYPE_SUBST_def",type_size'_def]
  >- (
    rename[`TYPE_SUBST e (Tyvar m)`]
    >> Cases_on `MEM (Tyvar m) (MAP SND e)`
    >- (
      fs[MEM_MAP]
      >> rename[`MEM y e`] >> PairCases_on`y`
      >> drule_all_then assume_tac $ cj 3 var_renaming_Tyvar_imp
      >> gvs[]
      >> drule_all_then assume_tac var_renaming_MEM_REV_ASSOCD
      >> fs[type_size'_def]
    )
    >> drule_all_then assume_tac var_renaming_NOT_MEM_REV_ASSOCD_IMP
    >> fs[type_size'_def]
  )
  >> fs[EVERY_MEM,type_size'_def,type1_size'_SUM_MAP]
  >> AP_TERM_TAC
  >> match_mp_tac LIST_EQ
  >> rw[EL_MAP]
  >> first_x_assum match_mp_tac
  >> fs[EL_MEM]
QED

Theorem equiv_ts_on_type_size:
  !s' s vars. equiv_ts_on s s' vars
    ==> !a. MEM a vars ==> type_size' (TYPE_SUBST s (Tyvar a)) = type_size' (TYPE_SUBST s' (Tyvar a))
Proof
  rw[Excl"TYPE_SUBST_def",equiv_ts_on_def,equal_ts_on_def,GSYM TYPE_SUBST_compose]
  >> rw[Excl"TYPE_SUBST_def",var_renaming_type_size]
QED

Theorem equiv_ts_on_tyvars_type_size:
  !s' s p. equiv_ts_on s s' (tyvars p)
    ==> type_size' (TYPE_SUBST s p) = type_size' (TYPE_SUBST s' p)
Proof
  ntac 2 gen_tac
  >> ho_match_mp_tac type_ind
  >> rw[]
  >- (drule equiv_ts_on_type_size >> fs[tyvars_def])
  >> dxrule_then assume_tac equiv_ts_on_tyvars_Tyapp
  >> fs[tyvars_Tyapp,type1_size'_SUM_MAP,type_size'_def,EVERY_MEM,AND_IMP_INTRO]
  >> AP_TERM_TAC
  >> rw[EQ_LIST_EL,EL_MAP]
  >> dxrule_then assume_tac EL_MEM
  >> res_tac
QED

(* Lemma 3.2 *)
Theorem var_renaming_tyvars_comm:
  !e p. var_renaming e
  ==> set (MAP (TYPE_SUBST e) (MAP Tyvar (tyvars p))) = set (MAP Tyvar (tyvars (TYPE_SUBST e p)))
Proof
  rpt strip_tac
  >> CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV [LIST_TO_SET_MAP]
  >> rw[tyvars_TYPE_SUBST,pred_setTheory.EXTENSION,PULL_EXISTS,MAP_MAP_o,o_DEF,EQ_IMP_THM,MEM_MAP,Excl"TYPE_SUBST_def"]
  >> goal_assum $ drule_at Any
  >> rename[`TYPE_SUBST e (Tyvar a)`]
  >> Cases_on `MEM (Tyvar a) (MAP SND e)`
  >> TRY (
    qmatch_asmsub_abbrev_tac `~MEM (Tyvar _) _`
    >> drule_all_then assume_tac var_renaming_NOT_MEM_REV_ASSOCD_IMP
    >> fs[tyvars_def]
  )
  >> fs[MEM_MAP]
  >> rename[`MEM y _`] >> PairCases_on `y`
  >> drule_all_then assume_tac $ cj 3 var_renaming_Tyvar_imp
  >> gvs[]
  >> drule_all_then assume_tac var_renaming_MEM_REV_ASSOCD
  >> fs[tyvars_def]
QED

Theorem var_renaming_FV_comm:
  !e p. is_const_or_type p /\ var_renaming e
  ==> set (MAP (TYPE_SUBST e) (MAP Tyvar (FV p))) = set (MAP Tyvar (FV (LR_TYPE_SUBST e p)))
Proof
  fs[is_const_or_type_eq,PULL_EXISTS,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM,FV_def,tvars_def,LR_TYPE_SUBST_def,INST_def,INST_CORE_def,var_renaming_tyvars_comm]
QED

(* Comment to Definition 5.3, Kunčar 2015 *)
Theorem FV_SND_SUBSET_FST:
  !ctxt pqs i.
  EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ i < LENGTH pqs ==> set (FV (SND (EL i pqs))) ⊆ set (FV (FST (EL i pqs)))
Proof
  rw[monotone_def,EVERY_MEM,ELIM_UNCURRY,list_subset_set]
  >> rpt $ first_x_assum match_mp_tac
  >> fs[EL_MEM]
QED

(* Lemma 5.4, Kunčar 2015 *)
Theorem mg_solution:
  !rs rs' pqs.
    mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
    ==> !i. i < LENGTH rs ==>
    equiv_ts_on (EL i rs) (EL i rs') (FV (FST (EL i pqs)))
Proof
  rpt strip_tac
  >> imp_res_tac mg_sol_seq_LENGTH
  >> fs[]
  >> drule_all_then strip_assume_tac mg_sol_seq_is_const_or_type
  >> fs[mg_sol_seq_def,is_const_or_type_eq,FV_def,sum_case_def,tvars_def]
  >> match_mp_tac equiv_ts_on_mg_sol
  >> first_x_assum rev_drule
  >> first_x_assum drule
  >> rpt strip_tac
  >> ntac 2 $ first_x_assum $ drule_then assume_tac
  >> gvs[FV_def,sum_case_def,tvars_def,equal_ts_on_tyvars,TYPE_SUBST_compose]
  >> rpt $ goal_assum drule
QED

(* Lemma 5.4, Kunčar 2015 *)
Theorem mg_solutions:
  !rs rs' pqs. mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
  ==>
    ?es. LENGTH es = LENGTH pqs
    /\ EVERY var_renaming es
    /\ !i. i < LENGTH rs ==>
    equal_ts_on (EL i rs) (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs') ++ (EL i es)) (FV (FST (EL i pqs)))
Proof
  rpt strip_tac
  >> qabbrev_tac `Q = λi e.  equal_ts_on (EL i rs) (MAP (TYPE_SUBST e ## I) (EL i rs') ++ e) (FV (FST (EL i pqs)))`
  >> qabbrev_tac `P = λi e. var_renaming e /\ Q i e`
  >> qabbrev_tac `f = λi. @e. P i e`
  >> `!i. i < LENGTH rs ==> P i (f i)` by (
    rw[]
    >> rev_drule_then (drule_then assume_tac) mg_solution
    >> first_x_assum drule
    >> fs[GSYM SELECT_THM,Abbr`P`,equiv_ts_on_def]
  )
  >> qexists_tac `MAP f (COUNT_LIST (LENGTH pqs))`
  >> rw[LENGTH_COUNT_LIST,EVERY_MAP,EVERY_MEM,Abbr`Q`,MEM_COUNT_LIST]
  >> `LENGTH rs = LENGTH pqs` by fs[mg_sol_seq_def,sol_seq_def]
  >> fs[]
  >> first_x_assum drule
  >> fs[el_map_count,Abbr`P`]
QED

Theorem mg_solution''[local]:
  !rs rs' pqs es es' i ctxt. mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ SUC i < LENGTH pqs
  /\ equal_ts_on (EL i rs) (MAP (TYPE_SUBST es ## I) (EL i rs') ++ es) (FV (FST (EL i pqs)))
  /\ equal_ts_on (EL (SUC i) rs) (MAP (TYPE_SUBST es' ## I) (EL (SUC i) rs') ++ es') (FV (FST (EL (SUC i) pqs)))
  /\ var_renaming es /\ var_renaming es'
  ==> equal_ts_on es es' (FV (LR_TYPE_SUBST (EL (SUC i) rs') (FST (EL (SUC i) pqs))))
Proof
  rw[]
  >> imp_res_tac $ cj 1 $ REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] $
    cj 1 $ REWRITE_RULE[EQ_IMP_THM] mg_sol_seq_def
  >> gs[sol_seq_def]
  >> `i < LENGTH pqs` by fs[]
  >> imp_res_tac mg_sol_seq_is_const_or_type
  >> ntac 2 $ first_x_assum $ drule_then assume_tac
  >> drule_then (qspec_then `FV (SND (EL (SUC i) pqs))` mp_tac) equal_ts_on_subset
  >> impl_tac >- (rev_drule_all FV_SND_SUBSET_FST >> fs[])
  >> rev_drule_then (qspec_then `FV (SND (EL i pqs))` mp_tac) equal_ts_on_subset
  >> impl_tac >- (drule_all FV_SND_SUBSET_FST >> fs[])
  >> ntac 2 $ qpat_x_assum `equal_ts_on _ _ _` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV]
  >> gs[GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving]
QED

(* TODO replace uses of mg_solutions with mg_solution' *)
(* our stronger version of 5.4 *)
Theorem mg_solution':
  !rs rs' pqs ctxt.
    mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
    /\ EVERY (UNCURRY (dependency ctxt)) pqs
    /\ monotone (dependency ctxt)
    ==> ?es. var_renaming es /\
      !i. i < LENGTH rs ==>
      equal_ts_on (EL i rs) (MAP (TYPE_SUBST es ## I) (EL i rs') ++ es) (FV $ FST $ EL i pqs)
Proof
  rpt strip_tac
  >> drule_then assume_tac mg_sol_seq_is_const_or_type
  >> rev_drule_then (drule_then assume_tac) mg_solution
  >> imp_res_tac mg_sol_seq_LENGTH
  >> reverse $ Cases_on `0 < LENGTH pqs`
  >- (qexists_tac `[]` >> fs[var_renaming_nil])
  >> first_assum $ drule_then assume_tac
  >> fs[FORALL_AND_THM,IMP_CONJ_THM]
  >> first_assum $ drule
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[equiv_ts_on_FV]
  >> rw[]
  >> goal_assum drule
  >> Induct
  >- fs[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
  >> strip_tac
  >> first_x_assum drule
  >> rw[equiv_ts_on_FV]
  >> pop_assum mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose,GSYM equal_ts_on_FV]
  >> fs[]
  >> rw[]
  >> rev_drule_then drule mg_solution''
  >> rpt $ disch_then $ drule
  >> pop_assum mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV,LR_TYPE_SUBST_type_preserving]
  >> fs[]
QED

(* Definition 5.5, Kunčar 2015 *)
Definition path_starting_at_def:
  path_starting_at ctxt k rs pqs =
  (
    wf_pqs pqs
    /\ k < LENGTH rs
    /\ LENGTH rs = LENGTH pqs
    /\ EVERY (UNCURRY (dependency ctxt)) (DROP k pqs)
    /\ equiv_ts_on [] (EL k rs) (FV (FST (EL k pqs)))
    /\ sol_seq (DROP k rs) (DROP k pqs)
  )
End

Theorem path_starting_at_shorten:
  !k l rs pqs ctxt. k < l /\ l <= LENGTH pqs
  /\ path_starting_at ctxt k rs pqs ==>
  path_starting_at ctxt k (TAKE l rs) (TAKE l pqs)
Proof
  rw[path_starting_at_def,wf_pqs_def,EVERY_MEM,LENGTH_TAKE,TAKE_TAKE,EL_TAKE]
  >- (
    first_x_assum match_mp_tac
    >> drule MEM_TAKE
    >> fs[]
  )
  >- (
    imp_res_tac MEM_DROP_TAKE
    >> fs[]
  )
  >> fs[DROP_TAKE,sol_seq_TAKE]
QED

Theorem path_starting_at_0:
  !k rs pqs ctxt. path_starting_at ctxt k rs pqs ==>
  path_starting_at ctxt 0 (DROP k rs) (DROP k pqs)
Proof
  rw[path_starting_at_def,wf_pqs_def,HD_DROP,EVERY_MEM]
  >> first_x_assum match_mp_tac
  >> fs[EL_MEM,MEM_DROP]
QED

Definition instance_LR_compute_def:
  (instance_LR_compute ((INR c1):type+term) (INR c2) =
    case (c1,c2) of
      | (Const m ty1,Const n ty2) => if (m = n)
        then instance_subst [(ty2,ty1)] [] [] else NONE
      | (_,_) => NONE)
  /\ (instance_LR_compute (INL ty1) (INL ty2) = instance_subst [(ty2,ty1)] [] [])
  /\ (instance_LR_compute _ _ = NONE)
End

Definition is_instance_LR_compute_def:
  is_instance_LR_compute x y = IS_SOME (instance_LR_compute x y)
End

Definition is_instance_LR_def:
  (is_instance_LR (INR c1) (INR c2) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ is_instance ty1 ty2)
  /\ (is_instance_LR (INL ty1) (INL ty2) = is_instance ty1 ty2)
  /\ (is_instance_LR _ _ = F)
End

Theorem is_instance_LR_equiv:
  is_instance_LR = is_instance_LR_compute
Proof
  fs[FUN_EQ_THM]
  >> rpt Cases
  >> REWRITE_TAC[is_instance_LR_def,instance_LR_compute_def,is_instance_LR_compute_def,instance_subst_completeness,option_CLAUSES]
  >> rpt (FULL_CASE_TAC)
  >> fs[option_CLAUSES]
QED

Theorem is_instance_LR_eq:
  !t t'. is_instance_LR t' t =
  (is_const_or_type t /\ is_const_or_type t'
  /\ ?s. LR_TYPE_SUBST s t' = t)
Proof
  rpt Cases
  >> fs[EQ_IMP_THM,is_const_or_type_eq,is_instance_LR_def,LR_TYPE_SUBST_cases,LR_TYPE_SUBST_sides]
  >> rpt strip_tac
  >> rveq
  >> fs[LR_TYPE_SUBST_cases]
  >- (qexists_tac `i` >> fs[])
  >- (qexists_tac `s` >> fs[])
  >- (
    qmatch_abbrev_tac `A \/ B`
    >> Cases_on `A`
    >> fs[]
    >> unabbrev_all_tac
    >> rw[LR_TYPE_SUBST_cases]
    >> rw[LR_TYPE_SUBST_cases]
  )
  >- (qexists_tac `i` >> fs[])
  >- (qexists_tac `s` >> fs[])
QED

Theorem is_instance_LR_simps:
  !t i. is_const_or_type t ==> is_instance_LR t (LR_TYPE_SUBST i t)
Proof
  fs[is_instance_simps,LR_TYPE_SUBST_cases,is_const_or_type_eq,PULL_EXISTS,DISJ_IMP_THM,FORALL_AND_THM,is_instance_LR_eq]
  >> fs[is_instance_simps,Once EQ_SYM_EQ]
QED

(* Definition 5.6, Kunčar 2015 *)
Definition cyclic_dep_def:
  cyclic_dep ctxt =
  (?pqs rs.
    path_starting_at ctxt 0 rs pqs
    /\ is_instance_LR (FST (EL 0 pqs)) (LR_TYPE_SUBST (EL (PRE $ LENGTH rs) rs) (SND (EL (PRE $ LENGTH pqs) pqs))))
End

Definition has_common_instance_compute_def:
  (has_common_instance_compute ((INR c1):type+term) ((INR c2):type+term) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ IS_SOME (unify ty1 ty2))
  /\ (has_common_instance_compute (INL ty1) (INL ty2) = IS_SOME (unify ty1 ty2))
  /\ (has_common_instance_compute _ _ = F)
End

Definition has_common_instance_def:
  (has_common_instance (INR c1:type+term) (INR c2:type+term) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ ~(ty1 # ty2))
  /\ (has_common_instance (INL ty1) (INL ty2) = ~(ty1 # ty2))
  /\ (has_common_instance _ _ = F)
End

Theorem has_common_instance_equiv:
  !ty1 ty2. has_common_instance ty1 ty2 = has_common_instance_compute ty1 ty2
Proof
  rpt Cases
  >> REWRITE_TAC[has_common_instance_def,has_common_instance_compute_def,unify_complete]
QED

Theorem has_common_instance_is_instance_LR_equiv:
  !x y. is_const_or_type x /\ is_const_or_type y
  ==> has_common_instance x y = ?t. is_const_or_type t /\ is_instance_LR x t /\ is_instance_LR y t
Proof
  rw[EQ_IMP_THM,is_const_or_type_eq]
  >> fs[has_common_instance_def,is_instance_LR_def,orth_ty_def]
  >> rveq
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST s tt`
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance_LR (INR (Const c _)) _`
    >> qexists_tac `INR (Const c (TYPE_SUBST s tt))`
  )
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance_LR (INL ll) _`
    >> qexists_tac `INL (TYPE_SUBST s tt)`
  )
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance red _`
    >> qexists_tac `TYPE_SUBST s tt`
  )
  >> unabbrev_all_tac
  >> fs[is_instance_LR_def]
  >> rw[]
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance ty _`
    >> qexists_tac `i` >> fs[]
  )
  >> (qexists_tac `i'` >> fs[])
QED

(* Definition 5.7, Kunčar 2015 *)
Definition composable_dep_def:
  composable_dep ctxt =
  !pqs rs p q. dependency ctxt p q
  /\ path_starting_at ctxt 0 rs pqs
  ==>
    is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
    \/
    is_instance_LR (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
    \/
    ~has_common_instance (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
End

Theorem sol_mon_prop:
  !rs rs' pqs ctxt es.
  sol_seq rs' pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ sol_seq rs pqs
  /\ LENGTH es = LENGTH rs
  /\ (!i. i < LENGTH rs ==>
    equal_ts_on (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs) ++ (EL i es)) (EL i rs') (FV (FST (EL i pqs))))
  ==>
    !i. i < LENGTH rs ==>
    equal_ts_on (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs) ++ (EL i es)) (EL i rs') (FV (SND (EL i pqs)))
Proof
  rpt strip_tac
  >> first_x_assum $ drule_then assume_tac
  >> dxrule_then match_mp_tac equal_ts_on_subset
  >> dxrule_then match_mp_tac FV_SND_SUBSET_FST
  >> fs[sol_seq_def]
QED

Theorem sol_mon_prop':
  !i j rs rs' pqs ctxt es.
  sol_seq rs' pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ sol_seq rs pqs
  /\ LENGTH es = LENGTH rs
  /\ j < LENGTH pqs
  /\ i < j
  /\ (!i. i < j ==>
    equal_ts_on (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs) ++ (EL i es)) (EL i rs') (FV (FST (EL i pqs))))
  ==>
    equal_ts_on (MAP (TYPE_SUBST (EL i es) ## I) (EL i rs) ++ (EL i es)) (EL i rs') (FV (SND (EL i pqs)))
Proof
  rpt strip_tac
  >> qspecl_then [`TAKE j rs`,`TAKE j rs'`,`TAKE j pqs`,`ctxt`,`TAKE j es`] mp_tac sol_mon_prop
  >> `LENGTH rs = LENGTH pqs /\ LENGTH rs' = LENGTH pqs` by fs[sol_seq_def]
  >> fs[LENGTH_TAKE,EVERY_TAKE,sol_seq_TAKE,EL_TAKE]
QED

Theorem id_sol_mg_sol_equiv:
  !rs pqs ctxt.
  0 < LENGTH rs
  /\ equiv_ts_on [] (HD rs) (FV (FST (HD pqs)))
  /\ sol_seq rs pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  ==> mg_sol_seq rs pqs
Proof
  rw[equiv_ts_on_def,Excl"EL",Excl"EL_restricted",GSYM EL]
  >> match_mp_tac mg_sol_seq_var_renaming'
  >> goal_assum $ drule_at Any
  >> rw[mg_sol_seq_def,sol_seq_TYPE_SUBST]
  >> rename1`sol_seq rs' pqs`
  >> qabbrev_tac `es = REPLICATE (LENGTH rs) (HD rs')`
  >> qexists_tac `es`
  >> conj_asm1_tac >- fs[Abbr`es`]
  >> ho_match_mp_tac COMPLETE_INDUCTION
  >> rw[]
  >> Cases_on `i = 0`
  >- (
    drule_then assume_tac sol_seq_is_const_or_type_FST
    >> fs[Abbr`es`,EL_REPLICATE,sol_seq_def,equal_ts_on_refl]
    >> qpat_x_assum `equal_ts_on _ _ _` mp_tac
    >> REWRITE_TAC[GSYM EL]
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP,LR_TYPE_SUBST_NIL]
    >> rw[Once EQ_SYM_EQ]
  )
  >> rpt(qpat_x_assum `sol_seq _ _` (fn x => mp_tac x >>
    ((qspec_then `PRE i` mp_tac) ((GSYM o cj 3 o REWRITE_RULE[sol_seq_def]) x))))
  >> rw[]
  >> `i < LENGTH rs'` by fs[sol_seq_def]
  >> gs[NOT_ZERO_LT_ZERO,SUC_PRE]
  >> `EL i es = EL (PRE i) es` by fs[EL_REPLICATE,Abbr`es`]
  >> imp_res_tac sol_seq_LENGTH
  >> `PRE i < LENGTH pqs` by fs[]
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
  >> fs[FORALL_AND_THM,IMP_CONJ_THM]
  >> drule sol_mon_prop'
  >> ntac 2 $ disch_then drule
  >> disch_then rev_drule
  >> disch_then $ qspecl_then [`PRE i`,`i`] mp_tac
  >> disch_then $ qspec_then `REPLICATE (LENGTH rs) $ MAP (TYPE_SUBST (HD rs') ## I) η ++ (HD rs')` mp_tac
  >> impl_tac
  >- (
    rw[EL_REPLICATE,Abbr`es`]
    >> last_x_assum drule
    >> REWRITE_TAC[GSYM EL]
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,EL_REPLICATE,GSYM TYPE_SUBST_compose,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
    >> fs[]
    >> disch_then $ ONCE_REWRITE_TAC o single o GSYM
    >> dep_rewrite.DEP_REWRITE_TAC[TYPE_SUBST_compose,LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
    >> fs[]
  )
  >> fs[EL_REPLICATE,Abbr`es`]
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,EL_REPLICATE,TYPE_SUBST_compose,LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
  >> fs[]
QED

Theorem id_sol_mg_sol_equiv':
  !rs pqs ctxt i.
  0 < LENGTH rs /\ i < LENGTH rs
  /\ equiv_ts_on [] (EL i rs) (FV (FST (EL i pqs)))
  /\ sol_seq rs pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  ==> mg_sol_seq (DROP i rs) (DROP i pqs)
Proof
  rpt strip_tac
  >> imp_res_tac sol_seq_LENGTH
  >> match_mp_tac id_sol_mg_sol_equiv
  >> REWRITE_TAC[GSYM EL]
  >> goal_assum $ drule_at Any
  >> fs[EVERY_DROP,EL_DROP,sol_seq_DROP]
QED

(* Lemma 5.8, Kunčar 2015 *)
Theorem sol_ex_non_orth:
  !pqs rs rs' ctxt n k.
  sol_seq rs pqs
  /\ LENGTH rs = SUC n
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ composable_dep ctxt
  /\ monotone (dependency ctxt)
  /\ mg_sol_seq rs' (TAKE n pqs)
  /\ path_starting_at ctxt k rs' (TAKE n pqs)
  ==>
    is_instance_LR (LR_TYPE_SUBST (EL (PRE n) rs') (SND (EL (PRE n) pqs))) (FST (EL n pqs))
    \/
    is_instance_LR (FST (EL n pqs)) (LR_TYPE_SUBST (EL (PRE n) rs') (SND (EL (PRE n) pqs)))
Proof
  rw[EVERY_MEM,mg_sol_seq_def]
  >> `LENGTH rs' = n` by fs[mg_sol_seq_def,sol_seq_def,path_starting_at_def]
  >> `k <= n` by fs[mg_sol_seq_def,sol_seq_def,path_starting_at_def]
  >> first_x_assum (qspec_then `TAKE (LENGTH rs') rs` assume_tac)
  >> `~NULL rs' /\ LENGTH rs = LENGTH pqs /\ LENGTH rs' = n /\ n <= LENGTH pqs /\ n <= LENGTH rs /\ 0 < n` by (
    fs[mg_sol_seq_def,NULL_EQ,ADD1,sol_seq_def]
    >> CCONTR_TAC
    >> fs[sol_seq_def,path_starting_at_def]
    >> rveq >> fs[]
  )
  >> rev_drule_then (drule_then assume_tac) sol_seq_TAKE
  >> imp_res_tac LENGTH_TAKE
  >> `n < LENGTH pqs` by fs[prim_recTheory.LESS_SUC_REFL]
  >> drule_then assume_tac EL_MEM
  >> first_assum $ drule_then assume_tac o SIMP_RULE(srw_ss())[ELIM_UNCURRY]
  >> `EL (PRE n) (TAKE n pqs) = EL (PRE n) pqs /\ EL (PRE n) (TAKE n rs) = EL (PRE n) rs /\ LAST (DROP k (TAKE n rs)) = EL (PRE n) rs /\ LAST (DROP k (TAKE n pqs)) = EL (PRE n) pqs` by (
    `~NULL (DROP k (TAKE n rs)) /\ ~NULL (DROP k (TAKE n pqs))` by (
      CCONTR_TAC
      >> fs[DROP_NIL,DROP_TAKE_NIL,GREATER_EQ,NULL_EQ]
      >> rfs[]
      >> imp_res_tac (GSYM EQ_LESS_EQ)
      >> fs[path_starting_at_def,DROP_TAKE_NIL]
    )
    >> fs[LAST_DROP]
    >> `~NULL (TAKE n rs) /\ ~NULL(TAKE n pqs)` by (CCONTR_TAC >> fs[NULL_EQ,path_starting_at_def] >> rveq >> fs[])
    >> NTAC 2 (dxrule (REWRITE_RULE[GSYM NULL_EQ] LAST_EL))
    >> rw[]
    >> match_mp_tac EL_TAKE
    >> Cases_on `rs'`
    >> fs[prim_recTheory.PRE_DEF]
  )
  >> drule_then assume_tac path_starting_at_0
  >> qpat_x_assum `composable_dep _` $ dxrule_then (drule_then assume_tac) o REWRITE_RULE[composable_dep_def]
  >> `~NULL (DROP k rs')` by fs[NULL_EQ,path_starting_at_def,DROP_NIL]
  >> dxrule LAST_DROP
  >> dxrule (REWRITE_RULE[GSYM NULL_EQ] LAST_EL)
  >> rpt strip_tac
  >> gvs[]
  >> `LENGTH rs' <= LENGTH pqs` by fs[]
  >> qspecl_then [`rs'`,`TAKE (LENGTH rs') rs`,`TAKE (LENGTH rs') pqs`,`ctxt`,`es`] mp_tac sol_mon_prop
  >> fs[sol_seq_TAKE,EVERY_MEM,EVERY_TAKE,MEM_TAKE,ELIM_UNCURRY]
  >> strip_tac
  >> `PRE (LENGTH rs') < LENGTH rs'` by fs[prim_recTheory.LESS_SUC_REFL]
  >> ntac 2 $ first_x_assum $ drule_then assume_tac
  >> drule_then (fs o single) EL_TAKE
  >> `PRE (LENGTH rs') < LENGTH pqs` by fs[]
  >> rev_drule_then (dxrule_then strip_assume_tac) sol_seq_is_const_or_type
  >> qpat_assum `sol_seq rs _` $ qspec_then `PRE (LENGTH rs')` mp_tac o cj 3 o REWRITE_RULE[sol_seq_def]
  >> fs[GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV]
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `~has_common_instance fst snd`
  >> `is_const_or_type fst` by (
    unabbrev_all_tac
    >> match_mp_tac LR_TYPE_SUBST_type_preserving
    >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM]
  )
  >> `is_const_or_type snd` by (
    unabbrev_all_tac
    >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM,MEM_TAKE,ELIM_UNCURRY,FORALL_AND_THM,IMP_CONJ_THM]
  )
  >> qpat_x_assum `~(has_common_instance _ _)` mp_tac
  >> unabbrev_all_tac
  >> `0 < LENGTH rs'` by fs[]
  >> fs[SUC_PRE]
  >> gvs[]
  >> qmatch_goalsub_abbrev_tac `~has_common_instance fst snd`
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST sfst fst = LR_TYPE_SUBST ssnd snd`
  >> fs[has_common_instance_is_instance_LR_equiv,Once DISJ_EQ_IMP]
  >> disch_then $ qspec_then `LR_TYPE_SUBST ssnd snd` mp_tac
  >> fs[LR_TYPE_SUBST_type_preserving,is_instance_LR_simps]
  >> qpat_x_assum `LR_TYPE_SUBST sfst fst = _` $ REWRITE_TAC o single o GSYM
  >> fs[is_instance_LR_simps]
QED

Theorem mg_sol_ext_leq'[local]:
  !rs pqs p q s ctxt. mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ LR_TYPE_SUBST s p = LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))
  /\ wf_pqs [(p,q)]
  ==> sol_seq (rs++[s]) (pqs++[(p,q)])
Proof
  rw[mg_sol_seq_def,sol_seq_def]
  >> fs[wf_pqs_def,EVERY_APPEND]
  >> `i < LENGTH rs /\ i < LENGTH pqs` by fs[]
  >> ntac 2 $ dxrule_then (fs o single) EL_APPEND1
  >> Cases_on `SUC i < LENGTH pqs`
  >- (
    `SUC i < LENGTH rs` by fs[]
    >> ntac 2 $ dxrule_then (fs o single) EL_APPEND1
  )
  >> rfs[NOT_LESS,GSYM ADD1,LESS_OR_EQ]
  >> `rs <> []` by (CCONTR_TAC >> fs[])
  >> `pqs <> []` by (CCONTR_TAC >> fs[])
  >> imp_res_tac LAST_EL
  >> imp_res_tac (REWRITE_RULE[LESS_OR_EQ,FORALL_AND_THM,DISJ_IMP_THM] EL_APPEND2)
  >> gs[]
QED

(* Lemma 5.9 *)
Theorem mg_sol_ext_leq:
  !rs pqs p q s ctxt. mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ LR_TYPE_SUBST s p = LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))
  /\ wf_pqs [(p,q)]
  ==> mg_sol_seq (rs++[s]) (pqs++[(p,q)])
Proof
  rw[]
  >> drule_all_then assume_tac mg_sol_ext_leq'
  >> fs[mg_sol_seq_def]
  >> rpt strip_tac
  >> `LENGTH rs' = SUC (LENGTH rs)` by fs[sol_seq_def]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> `LENGTH rs <= LENGTH rs'` by fs[]
  >> drule_all_then assume_tac sol_seq_TAKE
  >> gs[TAKE_LENGTH_APPEND]
  >> first_x_assum $ drule_then strip_assume_tac
  >> qexists_tac `es++[LAST es]`
  >> rw[GSYM LE_LT1,LESS_OR_EQ]
  >- (
    `i < LENGTH es /\ i < LENGTH rs' /\ i < LENGTH rs` by fs[sol_seq_def]
    >> imp_res_tac EL_APPEND1
    >> first_x_assum drule
    >> rw[EL_TAKE]
  )
  >> drule_at (Pat `EVERY _`) sol_mon_prop
  >> ntac 2 $ disch_then drule >> disch_then rev_drule
  >> fs[LENGTH_TAKE]
  >> disch_then $ drule
  >> fs[] >> strip_tac
  >> ntac 2 $ first_x_assum $ qspec_then `PRE (LENGTH pqs)` mp_tac
  >> qpat_x_assum `sol_seq rs' (_ ++ _)` $ (qspec_then `PRE (LENGTH pqs)` mp_tac) o cj 3 o REWRITE_RULE[sol_seq_def]
  >> qpat_x_assum `sol_seq _ (_ ++ _)` assume_tac
  >> drule sol_seq_is_const_or_type
  >> disch_then $ (fn x => qspec_then `PRE (LENGTH pqs)` mp_tac x
    >> qspec_then `LENGTH pqs` mp_tac x)
  >> `rs <> [] /\ rs' <> [] /\ pqs <> [] /\ es <> []` by (CCONTR_TAC >> fs[] >> rveq >> fs[sol_seq_def] >> rveq >> fs[])
  >> `PRE (LENGTH rs) < LENGTH pqs /\ LENGTH rs <= LENGTH pqs /\ LENGTH es <= LENGTH pqs /\ LENGTH pqs <= LENGTH pqs /\ LENGTH pqs = LENGTH rs` by fs[sol_seq_def]
  >> imp_res_tac SUC_PRE
  >> fs[EL_APPEND2,EL_APPEND1,LAST_EL]
  >> rw[EL_TAKE]
  >> rw[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
  >> qpat_x_assum `_ = LR_TYPE_SUBST _ p` $ REWRITE_TAC o single o GSYM
  >> qpat_x_assum `equal_ts_on _ _ (FV (SND _))` mp_tac
  >> rw[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
QED

Theorem mg_sol_ext_geq'[local]:
  !rs pqs p q ρ' ctxt. (mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ EVERY (λx. MEM (SND x) (MAP Tyvar (FV (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs)))))) ρ'
  /\ p = LR_TYPE_SUBST ρ' (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs)))
  /\ wf_pqs [(p,q)])
  ==> ?r. mg_sol_seq ((MAP (λs. MAP (TYPE_SUBST r ## I) s ++ r) rs)++[[]]) (pqs++[(p,q)])
    /\ equal_ts_on r ρ' (FV (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs))))
Proof
  rw[]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def,mg_sol_seq_def]
  >> qmatch_asmsub_abbrev_tac `wf_pqs [(p,_)]`
  >> qmatch_asmsub_abbrev_tac `EVERY f`
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST ρ' rn_qn`
  >> qabbrev_tac `r0_p0 = LR_TYPE_SUBST (EL 0 rs) (FST (EL 0 pqs))`
  >> qabbrev_tac `qn = SND (EL (PRE (LENGTH pqs)) pqs)`
  >> qabbrev_tac `r = FV r0_p0`
  >> qabbrev_tac `t = FV rn_qn`
  >> qabbrev_tac `c = FV p`
  >> `sol_seq rs pqs` by fs[mg_sol_seq_def]
  >> dxrule mg_sol_seq_TYPE_SUBST
  >> disch_then (qspecl_then [`list_complement r t`,`LIST_UNION t c`] assume_tac)
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST σ`
  >> `PRE (LENGTH pqs) < LENGTH pqs` by fs[sol_seq_def]
  >> drule_then (dxrule_then strip_assume_tac) mg_sol_seq_is_const_or_type
  >> `is_const_or_type rn_qn` by (
    qunabbrev_tac `rn_qn`
    >> match_mp_tac LR_TYPE_SUBST_type_preserving
    >> fs[Abbr`qn`]
  )
  >> `is_const_or_type p` by fs[wf_pqs_def]
  >> qspecl_then [`r`,`t`,`c`,`rn_qn`] assume_tac renn_ID_LR_TYPE_SUBST
  >> rfs[list_subset_def,EVERY_MEM]
  (* ρ̃ = rt*)
  >> qmatch_asmsub_abbrev_tac `mg_sol_seq rt _`
  (* ρ̂  is a solution *)
  >> `sol_seq (MAP (λx. (MAP (TYPE_SUBST ρ' ## I) x) ++ ρ') rt ++[[]]) (pqs++[(p,q)])` by (
    rw[sol_seq_def]
    >- fs[wf_pqs_def,sol_seq_def]
    >- fs[Abbr`rt`]
    >> qmatch_goalsub_abbrev_tac `EL _ (MAP fs rt ++ _)`
    >> fs[GSYM LE_LT1,LESS_OR_EQ]
    (* SUC i < LENGTH rt *)
    >- (
      `sol_seq rt pqs /\ LENGTH rt = LENGTH pqs` by fs[sol_seq_TYPE_SUBST,mg_sol_seq_def,Abbr`rt`]
      >> qpat_x_assum `sol_seq rt _` $ drule o cj 3 o REWRITE_RULE[sol_seq_def]
      >> qunabbrev_tac `fs`
      >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1,EL_MAP,GSYM LR_TYPE_SUBST_compose]
      >> drule mg_sol_seq_is_const_or_type
      >> fs[]
    )
    (* SUC i = LENGTH rt *)
    >> `LENGTH rt = LENGTH pqs` by fs[sol_seq_TYPE_SUBST,mg_sol_seq_def,Abbr`rt`]
    >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1,EL_MAP,EL_APPEND1,EL_APPEND2,EL_APPEND2]
    >> fs[LR_TYPE_SUBST_NIL,Abbr`rt`,EL_MAP,Abbr`p`]
    >> qpat_x_assum `LR_TYPE_SUBST _ rn_qn = rn_qn` $ ONCE_REWRITE_TAC o single o GSYM
    >> qpat_x_assum `SUC _ = _` $ assume_tac o GSYM
    >> fs[LR_TYPE_SUBST_compose,Abbr`fs`,Abbr`rn_qn`]
    >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    >> fs[MAP_MAP_o,MAP_EQ_f,TYPE_SUBST_compose,o_DEF,PAIR_MAP]
  )
  >> qexists_tac `MAP (TYPE_SUBST ρ' ## I) σ ++ ρ'`
  >> qmatch_asmsub_abbrev_tac `sol_seq (rhat' ++ [[]]) _`
  >> qmatch_goalsub_abbrev_tac `mg_sol_seq (rhat ++ [[]]) _`
  >> `rhat = rhat'` by (
    map_every qunabbrev_tac [`rt`,`rhat'`,`rhat`]
    >> fs[MAP_MAP_o,o_DEF,TYPE_SUBST_compose,ETA_THM,MAP_EQ_f,TYPE_SUBST_compose,PAIR_MAP]
  )
  >> VAR_EQ_TAC
  >> qpat_x_assum `Abbrev (rhat = _)` kall_tac
  >> reverse conj_tac
  >- (
    map_every qunabbrev_tac [`p`,`t`]
    >> fs[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
    >> qspecl_then [`rn_qn`,`ρ'`] mp_tac LR_TYPE_SUBST_FILTER_SND_tyvars
    >> qspec_then `rn_qn` mp_tac $ GSYM LR_TYPE_SUBST_NIL
    >> asm_rewrite_tac[]
    >> qpat_x_assum `LR_TYPE_SUBST _ rn_qn = rn_qn` mp_tac
    >> disch_then $ CONV_TAC o LAND_CONV o LHS_CONV o ONCE_REWRITE_CONV o single o GSYM
    >> fs[ETA_THM]
  )
  >> rw[mg_sol_seq_def]
  >> `LENGTH rs' = SUC (LENGTH pqs)` by fs[sol_seq_def]
  >> drule_then (qspec_then `LENGTH pqs` assume_tac) sol_seq_TAKE
  >> rfs[TAKE_APPEND1,mg_sol_seq_def]
  >> `LENGTH rhat = LENGTH rs` by fs[LENGTH_MAP,Abbr`rhat`,Abbr`rt`]
  (* equation 6 *)
  >> first_x_assum $ drule_then strip_assume_tac
  >> qmatch_assum_rename_tac `LENGTH es = LENGTH rt`
  >> qexists_tac `(MAP (λi.
        (FILTER (λx. MEM (SND x) (MAP Tyvar (FV p))) (LAST rs'))
        ++ (FILTER (λx. ~MEM (SND x) (MAP Tyvar (FV p))) (EL i es))
    ) (COUNT_LIST (LENGTH pqs))) ++ [LAST rs']`
  >> qmatch_goalsub_abbrev_tac `LENGTH eta_bar`
  >> conj_tac >- fs[LENGTH_COUNT_LIST,Abbr`eta_bar`]
  >> `LENGTH rhat = LENGTH pqs` by fs[sol_seq_def]
  >> pop_assum $ REWRITE_TAC o single
  >> Induct_on `(LENGTH pqs) - i`
  >- (
    rw[LESS_OR_EQ] >> rfs[Abbr`eta_bar`]
    >> `rs' <> []` by (CCONTR_TAC >> fs[sol_seq_def])
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND2,LAST_EL]
    >> fs[LR_TYPE_SUBST_NIL,LENGTH_COUNT_LIST,equal_ts_on_refl]
  )
  >> rpt gen_tac
  >> first_x_assum (qspecl_then [`pqs`,`SUC i`] mp_tac)
  >> rpt strip_tac
  >> fs[GSYM ADD_EQ_SUB,Excl"TYPE_SUBST_def",AND_IMP_INTRO]
  >> `i < LENGTH pqs` by fs[]
  >> `LENGTH rt = LENGTH pqs` by fs[Abbr`rt`]
  >> `is_const_or_type (FST (EL i pqs)) /\ is_const_or_type (SND (EL i pqs))` by (
    drule_then match_mp_tac sol_seq_is_const_or_type >> fs[]
  )
  >> `equal_ts_on (MAP (TYPE_SUBST (EL i eta_bar) ## I) ρ' ++ (EL i eta_bar)) (EL i es) (FV (LR_TYPE_SUBST (EL i rt) (FST (EL i pqs))))`
  suffices_by (
    first_x_assum $ qspec_then `i` mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1,EL_MAP,EL_TAKE,equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving]
    >> fs[]
    >> disch_then kall_tac
    >> disch_then $ REWRITE_TAC o single o GSYM
    >> qunabbrev_tac `rhat`
    >> dep_rewrite.DEP_REWRITE_TAC[GSYM LR_TYPE_SUBST_compose,EL_MAP]
    >> fs[]
  )
  >> match_mp_tac equal_ts_on_complement
  >> qexists_tac `t`
  >> conj_tac
  >- (
    rw[equal_ts_on_def,holSyntaxRenamingTheory.list_complement_MEM]
    >> REWRITE_TAC[GSYM TYPE_SUBST_def,GSYM TYPE_SUBST_compose]
    >> `~MEM (Tyvar x) (MAP SND ρ')` by (
      qpat_x_assum `!x. MEM _ ρ' ==> _` (assume_tac o ONCE_REWRITE_RULE[MONO_NOT_EQ])
      >> rw[MEM_MAP,Abbr`f`,DISJ_EQ_IMP,EQ_SYM_EQ]
    )
    >> fs[Excl"TYPE_SUBST_def",TYPE_SUBST_drop_all,Abbr`eta_bar`]
    >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,EL_APPEND1,EL_COUNT_LIST,TYPE_SUBST_FILTER_MEM2]
    >> fs[Excl"TYPE_SUBST_def",LENGTH_COUNT_LIST,MEM_FILTER]
    (* `~MEM (Tyvar x) (MAP Tyvar c)` by ... *)
    >> map_every qunabbrev_tac [`rt`,`σ`]
    >> qpat_x_assum `MEM _ (FV (LR_TYPE_SUBST _ _))` mp_tac
    >> rw[EL_MAP,GSYM LR_TYPE_SUBST_compose]
    >> drule MEM_FV_LR_TYPE_SUBST_renn_imp
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_type_preserving]
    >> rw[Excl"TYPE_SUBST_def"]
    >> qspecl_then [`list_complement r t`,`LIST_UNION t c`,`Tyvar x`] mp_tac
      ((REWRITE_RULE[NULL_FILTER,list_inter_def] o ONCE_REWRITE_RULE[holSyntaxRenamingTheory.NULL_list_inter_COMM]) renn_disj_dom_img4)
    >> rw[MEM_Tyvar_MAP_Tyvar,MEM_LIST_UNION,MEM_MAP,Excl"TYPE_SUBST_def",Once EQ_SYM_EQ,holSyntaxRenamingTheory.list_complement_MEM]
    >> pop_assum match_mp_tac
    >> goal_assum $ drule
    >> conj_asm1_tac
    >- (
      map_every qunabbrev_tac [`r`,`r0_p0`]
      >> ONCE_REWRITE_TAC[GSYM EL]
      >> match_mp_tac $ Ho_Rewrite.REWRITE_RULE[EVERY_MEM,SUBSET_DEF,PULL_FORALL,AND_IMP_INTRO] sol_seq_FV_LR_TYPE_SUBST_FST_j_FST_i
      >> fs[GSYM PULL_FORALL,AC CONJ_ASSOC CONJ_COMM]
      >> rpt $ goal_assum $ drule_at Any
    )
    >> drule_then drule $ SIMP_RULE(bool_ss++LET_ss)[] renn_compl_union_TYPE_SUBST_s
    >> fs[MEM_Tyvar_MAP_Tyvar,o_DEF,MEM_MAP,DISJ_EQ_IMP]
  )
  >> `equal_ts_on (MAP (TYPE_SUBST (EL (SUC i) eta_bar) ## I) ρ' ++ (EL (SUC i) eta_bar)) (EL i es) (FV (LR_TYPE_SUBST (EL i rt) (SND (EL i pqs))))` by (
    `equal_ts_on (MAP ((TYPE_SUBST (EL i es)) ## I) (EL i rt) ++ (EL i es)) (EL i rs') (FV (SND (EL i pqs)))` by (
      drule_all_then assume_tac $ REWRITE_RULE[EVERY_MEM] FV_SND_SUBSET_FST
      >> match_mp_tac equal_ts_on_subset
      >> goal_assum $ drule_at Any
      >> fs[EL_TAKE]
    )
    >> pop_assum mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose]
    >> asm_rewrite_tac[]
    >> disch_then $ REWRITE_TAC o single
    >> qpat_assum `sol_seq _ (_ ++ [_])` $ qspec_then `i` mp_tac o cj 3 o REWRITE_RULE[sol_seq_def]
    >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1]
    >> fs[]
    >> disch_then $ REWRITE_TAC o single
    >> qpat_x_assum `equal_ts_on _ _ _` $ mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose]
    >> qpat_x_assum `sol_seq (_ ++ _) _` assume_tac
    >> drule_then (irule_at Any) sol_seq_is_const_or_type_FST
    >> fs[]
    >> disch_then $ REWRITE_TAC o single o GSYM
    >> AP_TERM_TAC
    >> qpat_assum `sol_seq _ (_ ++ _)` $ qspec_then `i` mp_tac o cj 3 o REWRITE_RULE[sol_seq_def]
    >> fs[]
    >> disch_then $ REWRITE_TAC o single o GSYM
    >> qunabbrev_tac `rhat`
    >> fs[GSYM LR_TYPE_SUBST_compose,EL_APPEND1,EL_MAP]
  )
  >> pop_assum mp_tac
  >> rw[equal_ts_on_def,holSyntaxRenamingTheory.list_inter_set,Excl"TYPE_SUBST_def"]
  >> qpat_x_assum `!x. _` $ dep_rewrite.DEP_REWRITE_TAC o single o GSYM
  >> conj_tac
  >- (
    qspecl_then [`r`,`t`,`c`,`Tyvar x`] mp_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s)
    >> rw[MEM_Tyvar_MAP_Tyvar]
    >> drule_then assume_tac TYPE_SUBST_drop_all
    >> `MEM x (FV (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs))))` by (
      map_every qunabbrev_tac [`t`,`rn_qn`,`qn`]
      >> match_mp_tac $ Ho_Rewrite.REWRITE_RULE[EVERY_MEM,SUBSET_DEF,PULL_FORALL,AND_IMP_INTRO] sol_seq_FV_LR_TYPE_SUBST_SND_j_SND_i
      >> fs[GSYM PULL_FORALL,GSYM CONJ_ASSOC]
      >> ntac 2 $ goal_assum $ drule
      >> goal_assum $ drule_at (Pos $ el 3)
      >> fs[]
    )
    >> qunabbrev_tac `rt`
    >> dep_rewrite.DEP_REWRITE_TAC[GSYM LR_TYPE_SUBST_compose,EL_MAP]
    >> asm_rewrite_tac[]
    >> match_mp_tac FV_SUBSET_LR_TYPE_SUBST_id
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_type_preserving]
    >> fs[]
  )
  >> qpat_x_assum `LR_TYPE_SUBST _ rn_qn = rn_qn` $ mp_tac o GSYM
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[GSYM LR_TYPE_SUBST_NIL]
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose,LR_TYPE_SUBST_tyvars]
  >> asm_rewrite_tac[]
  >> qunabbrev_tac `t`
  >> disch_then $ drule_then assume_tac o GSYM o REWRITE_RULE[TYPE_SUBST_NIL,GSYM TYPE_SUBST_compose]
  >> drule_all_then assume_tac FV_SUBSET_LR_TYPE_SUBST_id
  >> fs[GSYM TYPE_SUBST_compose,EL_MAP,Excl"TYPE_SUBST_def"]
  >> qmatch_goalsub_abbrev_tac `TYPE_SUBST _ ρ'x`
  >> `set (tyvars ρ'x) ⊆ set (FV p)` by (
    map_every qunabbrev_tac [`ρ'x`,`c`,`p`]
    >> qpat_x_assum `is_const_or_type rn_qn` (assume_tac o REWRITE_RULE[is_const_or_type_eq])
    >> fs[tyvars_TYPE_SUBST,LR_TYPE_SUBST_cases,tyvars_def,tvars_def,FV_def,sum_case_def,SUBSET_DEF]
    >> fs[sum_case_def,tyvars_def,tvars_def]
    >> rpt strip_tac
    >> rpt $ goal_assum drule
  )
  >> rw[TYPE_SUBST_tyvars,Abbr`eta_bar`,Once EQ_SYM_EQ]
  >> REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1,EL_MAP,EL_COUNT_LIST,TYPE_SUBST_FILTER_MEM1]
  >> fs[LENGTH_COUNT_LIST,SUBSET_DEF,Excl"TYPE_SUBST_def",Abbr`c`]
  >> Cases_on `LENGTH pqs <= SUC i`
  >- (
    dep_rewrite.DEP_REWRITE_TAC[EL_APPEND2,EL_MAP,EL_COUNT_LIST,TYPE_SUBST_FILTER_MEM2]
    >> fs[LENGTH_COUNT_LIST,SUBSET_DEF,Excl"TYPE_SUBST_def",LESS_OR_EQ,LE]
    >> rfs[]
  )
  >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1,EL_MAP,EL_COUNT_LIST,TYPE_SUBST_FILTER_MEM1]
  >> fs[NOT_LESS_EQUAL,LENGTH_COUNT_LIST]
QED

(* Lemma 5.10 *)
Theorem mg_sol_ext_geq:
  !rs pqs p q s ctxt. mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ p = LR_TYPE_SUBST s (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
  /\ wf_pqs [(p,q)]
  ==> ?r. mg_sol_seq ((MAP (λs. MAP (TYPE_SUBST r ## I) s ++ r) rs)++[[]]) (pqs++[(p,q)])
    /\ equal_ts_on r s (FV (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))))
Proof
  rw[]
  >> `LENGTH rs = LENGTH pqs` by fs[mg_sol_seq_def,sol_seq_def]
  >> `rs ≠ [] ∧ pqs ≠ []` by (rw[] >> CCONTR_TAC >> fs[])
  >> drule_then (qspec_then `PRE (LENGTH pqs)` assume_tac) mg_sol_seq_is_const_or_type
  >> drule mg_sol_ext_geq'
  >> qmatch_goalsub_abbrev_tac `EVERY f`
  >> rfs[]
  >> rpt $ disch_then drule
  >> disch_then $ qspecl_then [`q`,`FILTER f s`] mp_tac
  >> impl_keep_tac
  >- (
    rw[EVERY_FILTER,wf_pqs_def]
    >> fs[wf_pqs_def]
    >> rpt $ match_mp_tac LR_TYPE_SUBST_type_preserving
    >> fs[]
  )
  >> qunabbrev_tac `f`
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_FILTER_SND_tyvars,LR_TYPE_SUBST_type_preserving,LAST_EL]
  >> rw[]
  >> goal_assum drule
  >> qpat_x_assum `equal_ts_on _ _ _` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_FILTER_SND_tyvars,equal_ts_on_FV,LR_TYPE_SUBST_type_preserving]
  >> fs[]
QED

(* lift type_size' to constants and types *)

Definition type_size_LR_def:
  (type_size_LR (INL t) = type_size' t)
  /\ (type_size_LR (INR (Const m t)) = type_size' t)
End

Theorem var_renaming_type_size_LR:
  !e p. is_const_or_type p /\ var_renaming e
  ==> type_size_LR (LR_TYPE_SUBST e p) = type_size_LR p
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,type_size_LR_def,var_renaming_type_size]
QED

Theorem type_size_LR_TYPE_SUBST:
  !t s. is_const_or_type t ==> type_size_LR t <= type_size_LR (LR_TYPE_SUBST s t)
Proof
  rw[is_const_or_type_eq] >> fs[type_size_LR_def,LR_TYPE_SUBST_cases,type_size_TYPE_SUBST]
QED

Theorem equiv_ts_on_FV_type_size:
  !s' s p. equiv_ts_on s s' (FV p) /\ is_const_or_type p
    ==> type_size_LR (LR_TYPE_SUBST s p) = type_size_LR (LR_TYPE_SUBST s' p)
Proof
  rw[is_const_or_type_eq,FV_def]
  >> fs[LR_TYPE_SUBST_cases,sum_case_def,tvars_def,type_size_LR_def,equiv_ts_on_tyvars_type_size]
QED

(* property that holds at strict geq extensions of solutions *)

Definition sol_seq_measure_def:
  sol_seq_measure q p =
    (type_size_LR q <= type_size_LR p /\
    (LENGTH (FV p) < LENGTH (FV q) \/ type_size_LR q < type_size_LR p))
End

Theorem is_instance_LR_NOT_is_instance_LR:
  !t t'. is_instance_LR t t' /\ ~(is_instance_LR t' t)
  ==> sol_seq_measure t t'
Proof
  rw[is_instance_LR_eq,is_const_or_type_eq]
  >> fs[FV_def,LR_TYPE_SUBST_cases,tvars_def,type_size_LR_def,type_size_TYPE_SUBST,sol_seq_measure_def]
  >> qpat_x_assum `TYPE_SUBST _ _ = _` $ assume_tac o GSYM
  >> drule $ Ho_Rewrite.REWRITE_RULE[PULL_EXISTS] is_instance_NOT_is_instance_imp'
  >> dep_rewrite.DEP_REWRITE_TAC[ALL_DISTINCT_CARD_LIST_TO_SET]
  >> fs[type_size_TYPE_SUBST,tyvars_ALL_DISTINCT]
QED

Theorem SUM_MAP_same_LESS_eq:
  EVERY (λx. f x <= g x) xs
  /\ SUM (MAP f xs) < SUM (MAP g xs)
  ==> EXISTS (λx. f x < g x) xs
Proof
  rpt strip_tac
  >> qpat_x_assum `SUM _ < _` mp_tac
  >> rw[Once MONO_NOT_EQ,NOT_LESS,o_DEF,SUM_MAP_same_LE]
QED

Theorem type_size_TYPE_SUBST_LESS'':
  !t s. type_size' t < type_size' (TYPE_SUBST s t)
  <=> (?m. MEM m (tyvars t) /\ type_size' (Tyvar m) < type_size' (TYPE_SUBST s (Tyvar m)))
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM]
  >> reverse conj_tac
  >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac `_ < type_size' s_m`
    >> drule_then match_mp_tac type_size_TYPE_SUBST_LESS
    >> Cases_on `s_m`
    >> fs[type_size'_def]
    >> rename[`Tyapp mm l`]
    >> Cases_on `l`
    >> fs[type_size'_def]
  )
  >> ho_match_mp_tac type_ind
  >> rw[tyvars_Tyapp,MEM_FLAT,MEM_MAP,tyvars_def,PULL_EXISTS,type_size'_def,type1_size'_SUM_MAP,MAP_MAP_o,EVERY_MEM]
  >> drule_at Any SUM_MAP_same_LESS_eq
  >> impl_tac
  >- rw[EVERY_MEM,type_size_TYPE_SUBST]
  >> rw[EXISTS_MEM]
  >> first_x_assum drule
  >> disch_then $ drule_then strip_assume_tac
  >> rpt $ goal_assum $ drule_at Any
QED

Theorem type_size_LR_TYPE_SUBST_LESS:
  !t s. is_const_or_type t ==>
  (type_size_LR t < type_size_LR (LR_TYPE_SUBST s t)
  <=> (?m. MEM m (FV t) /\ type_size' (Tyvar m) < type_size' (TYPE_SUBST s (Tyvar m))))
Proof
  rw[FV_def,is_const_or_type_eq,Excl"TYPE_SUBST_def"]
  >> fs[Excl"TYPE_SUBST_def",GSYM type_size_TYPE_SUBST_LESS'',type_size_LR_def,tvars_def,sum_case_def,LR_TYPE_SUBST_cases]
QED

Theorem type_size_tyvars:
  !t t' s. type_size' t < type_size' (TYPE_SUBST s t)
  /\ set (tyvars t) ⊆ set (tyvars t')
  ==> type_size' t' < type_size' (TYPE_SUBST s t')
Proof
  rw[Once type_size_TYPE_SUBST_LESS'',SUBSET_DEF]
  >> res_tac
  >> rw[Once type_size_TYPE_SUBST_LESS'']
  >> rpt $ goal_assum drule
QED

Theorem type_size_LR_FV:
  !t t' s. is_const_or_type t /\ is_const_or_type t'
  /\ type_size_LR t < type_size_LR (LR_TYPE_SUBST s t)
  /\ set (FV t) ⊆ set (FV t')
  ==> type_size_LR t' < type_size_LR (LR_TYPE_SUBST s t')
Proof
  rw[is_const_or_type_eq,FV_def,type_size_LR_def]
  >> fs[type_size_LR_def,sum_case_def,tvars_def,LR_TYPE_SUBST_cases,type_size_tyvars]
  >> metis_tac[type_size_tyvars]
QED

Theorem FV_ALL_DISTINCT:
  !t. is_const_or_type t
  ==> ALL_DISTINCT (FV t)
Proof
  rw[is_const_or_type_eq,FV_def]
  >> fs[sum_case_def,tvars_def,tyvars_ALL_DISTINCT]
QED

Theorem FV_LR_TYPE_SUBST:
  !p s. is_const_or_type p ==>
  set (FV $ LR_TYPE_SUBST s p) = {v | ?x. MEM x (FV p) /\ MEM v (tyvars (TYPE_SUBST s (Tyvar x))) }
Proof
  rw[is_const_or_type_eq,FV_def]
  >> fs[sum_case_def,LR_TYPE_SUBST_cases,tvars_def,tyvars_TYPE_SUBST]
QED

Theorem mg_sol_ext_geq_tyvars_p0[local]:
  !rs pqs q ρ' ctxt.
  let qn = SND (EL (PRE (LENGTH pqs)) pqs) ;
      rn_qn = LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) qn ;
      p = LR_TYPE_SUBST ρ' rn_qn
  in
    mg_sol_seq rs pqs
    /\ 0 < LENGTH rs
    /\ EVERY (UNCURRY (dependency ctxt)) pqs
    /\ monotone (dependency ctxt)
    /\ wf_pqs [(p,q)]
    ==> ?rs'.
      mg_sol_seq rs' pqs
      /\ LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs))
        = LR_TYPE_SUBST (EL (PRE (LENGTH rs')) rs') (SND (EL (PRE (LENGTH pqs)) pqs))
      /\ let r' = FV (LR_TYPE_SUBST (EL 0 rs') (FST $ EL 0 pqs)) ;
          s' = FV (LR_TYPE_SUBST (EL (PRE $ LENGTH rs') rs') (SND $ EL (PRE $ LENGTH pqs) pqs)) ;
          c' = FV (LR_TYPE_SUBST ρ' $ LR_TYPE_SUBST (EL (PRE $ LENGTH rs') rs') (SND $ EL (PRE $ LENGTH pqs) pqs))
         in NULL $ list_inter (list_complement r' s') (LIST_UNION s' c')
Proof
  BasicProvers.LET_ELIM_TAC
  >> qabbrev_tac `p0 = FST (EL 0 pqs)`
  >> qabbrev_tac `r0_p0 = LR_TYPE_SUBST (EL 0 rs) p0`
  >> qabbrev_tac `t = FV rn_qn`
  >> qabbrev_tac `r = FV r0_p0`
  >> qabbrev_tac `c = FV p`
  >> qspecl_then [`r`,`t`,`c`] assume_tac renn_disj_dom_s
  >> qspecl_then [`r`,`t`,`c`] assume_tac renn_disj_dom_img2
  >> `is_const_or_type p0 /\ is_const_or_type r0_p0 /\ is_const_or_type qn /\ is_const_or_type rn_qn` by (
    unabbrev_all_tac
    >> ntac 2 $ irule_at Any LR_TYPE_SUBST_type_preserving
    >> imp_res_tac mg_sol_seq_LENGTH
    >> drule mg_sol_seq_is_const_or_type
    >> fs[]
  )
  >> qspecl_then [`r`,`t`,`c`,`rn_qn`] mp_tac renn_ID_LR_TYPE_SUBST
  >> impl_tac
  >- (qunabbrev_tac `t` >> fs[SUBSET_REFL,list_subset_set])
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST (renn R C) _`
  >> strip_tac
  >> drule_then (qspec_then `ρ'` assume_tac) $ GSYM LR_TYPE_SUBST_FILTER_SND_tyvars
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST _ _ = LR_TYPE_SUBST ρ'' _`
  >> drule_then (qspec_then `renn R C` assume_tac) mg_sol_seq_var_renaming
  >> rw[markerTheory.Abbrev_def]
  >> fs[renn_var_renaming]
  >> goal_assum drule
  >> ONCE_REWRITE_TAC[GSYM EL]
  >> fs[GSYM LR_TYPE_SUBST_compose,EL_MAP]
  >> rw[NULL_FILTER,list_inter_def,holSyntaxRenamingTheory.list_complement_MEM,DISJ_EQ_IMP]
  >> rfs[FV_LR_TYPE_SUBST]
  >> qspecl_then [`R`,`C`,`x`] assume_tac renn_Tyvars_TYPE_SUBST
  >> gvs[tyvars_def]
  >> Cases_on `MEM x t`
  >- (
    qspecl_then [`R`,`C`,`x`] mp_tac renn_ID
    >> map_every qunabbrev_tac [`R`,`C`]
    >> rw[holSyntaxRenamingTheory.list_complement_MEM]
  )
  >> `MEM x R` by fs[Abbr`R`,holSyntaxRenamingTheory.list_complement_MEM]
  >> Cases_on `MEM x C`
  >- (
    `MEM x c` by gs[Abbr`C`,Abbr`R`,holSyntaxRenamingTheory.list_complement_MEM]
    >> qspecl_then [`R`,`C`] mp_tac renn_disj_dom_img3
    >> ONCE_REWRITE_TAC[holSyntaxRenamingTheory.NULL_list_inter_COMM]
    >> REWRITE_TAC[NULL_FILTER,Once list_inter_def,holSyntaxRenamingTheory.list_inter_set]
    >> disch_then $ qspec_then `Tyvar a` mp_tac
    >> impl_tac
    >- (
      fs[o_DEF,MEM_MAP,holSyntaxRenamingTheory.list_inter_set]
      >> rpt $ goal_assum $ drule_at Any
      >> fs[]
    )
    >> fs[MEM_Tyvar_MAP_Tyvar]
  )
  >> qspecl_then [`R`,`C`,`x`] mp_tac renn_ID
  >> impl_tac
  >- (
    map_every qunabbrev_tac [`R`,`C`]
    >> rw[holSyntaxRenamingTheory.list_complement_MEM,set_LIST_UNION]
  )
  >> strip_tac
  >> gvs[]
QED

Theorem var_renaming_FV_LENGTH:
  !p s.  is_const_or_type p
  /\ var_renaming s
  ==> LENGTH (FV (LR_TYPE_SUBST s p)) = LENGTH (FV p)
Proof
  fs[is_const_or_type_eq,FV_def,LR_TYPE_SUBST_cases,tvars_def,sum_case_def,FORALL_AND_THM,DISJ_IMP_THM,GSYM AND_IMP_INTRO,PULL_EXISTS]
  >> rw[]
  >> qspecl_then [`_0`,`Tyvar`] (mp_tac o GSYM o GEN_ALL) LENGTH_MAP
  >> disch_then (fn x => CONV_TAC $ LHS_CONV $ ONCE_REWRITE_CONV $ single x)
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET,GSYM ALL_DISTINCT_MAP_inj]
  >> fs[tyvars_ALL_DISTINCT,GSYM var_renaming_tyvars_comm,LIST_TO_SET_MAP]
  >> dep_rewrite.DEP_REWRITE_TAC $ single $ REWRITE_RULE[AND_IMP_INTRO] $ GEN_ALL INJ_CARD_IMAGE
  >> fs[]
  >> conj_tac
  >- (
    qexists_tac `IMAGE Tyvar (set (tyvars ty)) ∪ set (MAP SND s)`
    >> drule var_renaming_inj
    >> rw[INJ_DEF]
    >> Cases_on `MEM (Tyvar x') (MAP SND s)`
    >- (
      fs[MEM_MAP]
      >> drule_all_then assume_tac $ cj 3 var_renaming_Tyvar_imp
      >> gvs[]
      >> drule_all_then assume_tac var_renaming_MEM_REV_ASSOCD
      >> fs[]
      >> imp_res_tac $ REWRITE_RULE[SET_EQ_SUBSET,SUBSET_DEF,AND_IMP_INTRO,IMP_CONJ_THM,FORALL_AND_THM]
        var_renaming_MAP_FST_SND
      >> imp_res_tac $ Q.ISPEC `FST` MEM_MAP_f
      >> first_x_assum $ drule_then assume_tac
      >> fs[MEM_MAP]
      >> disj2_tac
      >> goal_assum $ drule_at Any
      >> fs[]
    )
    >> imp_res_tac var_renaming_NOT_MEM_REV_ASSOCD_IMP
    >> fs[]
  )
  >> fs[INJ_DEF]
  >> qexists_tac `set $ MAP Tyvar $ tyvars ty`
  >> fs[MEM_Tyvar_MAP_Tyvar]
QED

Theorem var_renaming_sol_seq_measure:
  !s p p'. var_renaming s /\ is_const_or_type p
  /\ sol_seq_measure (LR_TYPE_SUBST s p) p'
  ==> sol_seq_measure p p'
Proof
  rpt strip_tac
  >> drule_all var_renaming_type_size_LR
  >> drule_all var_renaming_FV_LENGTH
  >> fs[sol_seq_measure_def]
QED

Theorem var_renaming_sol_seq_measure':
  !s p p'. var_renaming s /\ is_const_or_type p'
  /\ sol_seq_measure p p'
  ==> sol_seq_measure p (LR_TYPE_SUBST s p')
Proof
  rpt strip_tac
  >> drule_all var_renaming_type_size_LR
  >> drule_all var_renaming_FV_LENGTH
  >> fs[sol_seq_measure_def]
QED

Theorem mg_sol_seq_var_renaming:
  !rs pqs s. mg_sol_seq rs pqs /\ var_renaming s
  ==> mg_sol_seq (MAP (λx. MAP (TYPE_SUBST s ## I) x ++ s) rs) pqs
Proof
  rw[mg_sol_seq_def,sol_seq_TYPE_SUBST]
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `MAP (λx. MAP (TYPE_SUBST x ## I) (MAP SWAP s) ++ x) es`
  >> rpt strip_tac >> fs[]
  >> first_x_assum $ drule
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,EL_MAP]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> conj_asm1_tac
  >- (fs[] >> drule_all sol_seq_is_const_or_type >> fs[])
  >> fs[]
  >> disch_then $ REWRITE_TAC o single o GSYM
  >> AP_TERM_TAC
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[LR_TYPE_SUBST_compose]
  >> conj_asm1_tac
  >- fs[LR_TYPE_SUBST_type_preserving]
  >> drule LR_TYPE_SUBST_NIL
  >> disch_then $ CONV_TAC o RHS_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> rw[LR_TYPE_SUBST_tyvars,Excl"TYPE_SUBST_def",GSYM TYPE_SUBST_compose,var_renaming_SWAP_id]
QED

Theorem sol_seq_equal_ts_on:
  !rs rs' pqs ctxt. sol_seq rs pqs
  /\ monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ (!i. i < LENGTH pqs ==> equal_ts_on (EL i rs) (EL i rs') (FV (FST (EL i pqs))))
  /\ LENGTH rs' = LENGTH pqs
  ==> sol_seq rs' pqs
Proof
  rpt strip_tac
  >> drule_then drule FV_SND_SUBSET_FST
  >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY,FORALL_AND_THM,IMP_CONJ_THM]
  >> rw[]
  >> `i < LENGTH pqs` by fs[]
  >> last_assum $ dxrule_then assume_tac
  >> drule_then (qspec_then `FV (SND (EL i pqs))` mp_tac) equal_ts_on_subset
  >> pop_assum mp_tac
  >> last_x_assum $ drule_then assume_tac
  >> drule_then (qspec_then `FV (SND (EL (SUC i) pqs))` mp_tac) equal_ts_on_subset
  >> pop_assum mp_tac
  >> rfs[]
  >> last_x_assum $ drule_then assume_tac
  >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV]
  >> fs[EL_MEM]
QED

Theorem mg_sols_equal_ts_on:
  !rs rs' pqs ctxt. mg_sol_seq rs pqs
  /\ monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ (!i. i < LENGTH pqs ==> equal_ts_on (EL i rs) (EL i rs') (FV (FST (EL i pqs))))
  /\ LENGTH rs' = LENGTH pqs
  ==> mg_sol_seq rs' pqs
Proof
  rw[mg_sol_seq_def]
  >- (drule_all sol_seq_equal_ts_on >> fs[])
  >> imp_res_tac sol_seq_LENGTH
  >> first_x_assum $ drule_then strip_assume_tac
  >> rfs[]
  >> goal_assum drule
  >> rw[]
  >> ntac 2 $ first_x_assum $ drule
  >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV]
  >> imp_res_tac sol_seq_is_const_or_type_FST
  >> fs[]
QED

Theorem type1_size'_eqn:
  type1_size' l = LENGTH l + SUM (MAP type_size' l)
Proof
  Induct_on ‘l’ >>
  rw[type_size'_def]
QED

Theorem TYPE_SUBST_type_size_intr:
  ∀σ t.
  type_size' (TYPE_SUBST σ t) = type_size' t ⇒
  ∀x. MEM x (tyvars t) ⇒
      (∃z. TYPE_SUBST σ (Tyvar x) = Tyvar z) ∨
      (∃tc. TYPE_SUBST σ (Tyvar x) = Tyapp tc [])
Proof
  ho_match_mp_tac TYPE_SUBST_ind >>
  rw[tyvars_def,type_size'_def,MEM_FOLDR_LIST_UNION]
  >- (Cases_on ‘REV_ASSOCD (Tyvar σ') σ (Tyvar σ')’ >>
      gvs[] >> Cases_on ‘l’ >> gvs[type_size'_def])
  >- (‘∀z. MEM z tys ⇒ type_size' (TYPE_SUBST σ z) = type_size' z’
        by(qpat_x_assum ‘_ = _’ mp_tac >>
           rpt(pop_assum kall_tac) >>
           rw[type1_size'_eqn,MAP_MAP_o,o_DEF] >>
           rw[EQ_LESS_EQ,type_size_TYPE_SUBST] >>
           spose_not_then strip_assume_tac >>
           gvs[NOT_LESS_EQUAL] >>
           gvs[MEM_SPLIT,SUM_APPEND] >>
           ‘SUM (MAP type_size' l1) ≤ SUM (MAP (λa. type_size' (TYPE_SUBST σ a)) l1)’
             by(match_mp_tac SUM_MAP_same_LE >>
                rw[EVERY_MEM,type_size_TYPE_SUBST]) >>
           ‘SUM (MAP type_size' l2) ≤ SUM (MAP (λa. type_size' (TYPE_SUBST σ a)) l2)’
             by(match_mp_tac SUM_MAP_same_LE >>
                rw[EVERY_MEM,type_size_TYPE_SUBST]) >>
           DECIDE_TAC) >>
      pop_assum drule >>
      strip_tac >>
      res_tac >>
      gvs[])
QED

Theorem TYPE_SUBST_type_size_intr':
  ∀σ t.
  (∀x. MEM x (tyvars t) ⇒
      (∃z. TYPE_SUBST σ (Tyvar x) = Tyvar z) ∨
      (∃tc. TYPE_SUBST σ (Tyvar x) = Tyapp tc [])) ⇒
  type_size' (TYPE_SUBST σ t) = type_size' t
Proof
  ho_match_mp_tac TYPE_SUBST_ind >>
  rw[tyvars_def,type_size'_def,MEM_FOLDR_LIST_UNION] >>
  rw[type_size'_def] >>
  gvs[PULL_EXISTS] >>
  gvs[type1_size'_eqn,MAP_MAP_o,o_DEF] >>
  rw[EQ_LESS_EQ]
  >- (match_mp_tac SUM_MAP_same_LE >>
      rw[EVERY_MEM] >>
      res_tac >>
      simp[])
  >- (match_mp_tac SUM_MAP_same_LE >>
      rw[MEM_MAP,type_size_TYPE_SUBST])
QED

Theorem type_size_invariant_CARD_LESS_EQ:
  type_size' (TYPE_SUBST σ t) = type_size' t ⇒
  CARD(set(tyvars(TYPE_SUBST σ t))) ≤ CARD(set(tyvars t))
Proof
  rw[tyvars_TYPE_SUBST_alt] >>
  match_mp_tac LESS_EQ_TRANS >>
  irule_at (Pos hd) CARD_BIGUNION_BOUNDED_SETS >>
  simp[PULL_EXISTS] >>
  qexists_tac ‘1’ >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all TYPE_SUBST_type_size_intr >>
      rw[] >> rw[tyvars_def])
  >- (simp[] >>
      match_mp_tac CARD_IMAGE >>
      rw[])
QED

Theorem type_size_invariant_CARD_less_IFF:
  type_size' (TYPE_SUBST σ t) = type_size' t ⇒
  (CARD(set(tyvars(TYPE_SUBST σ t))) < CARD(set(tyvars t))
   ⇔
   (∃x m. MEM x (tyvars t) ∧ TYPE_SUBST σ (Tyvar x) = Tyapp m []) ∨
   (∃x y z. MEM x (tyvars t) ∧ MEM y (tyvars t) ∧ x ≠ y ∧
            TYPE_SUBST σ (Tyvar x) = TYPE_SUBST σ (Tyvar y)))
Proof
  rpt strip_tac >>
  rw[] >>
  drule type_size_invariant_CARD_LESS_EQ >>
  drule TYPE_SUBST_type_size_intr >>
  pop_assum kall_tac >>
  rpt strip_tac >>
  rw[EQ_IMP_THM]
  >- (rw[DISJ_EQ_IMP] >>
      gvs[tyvars_TYPE_SUBST_alt] >>
      qmatch_asmsub_abbrev_tac ‘IMAGE a1’ >>
      ‘CARD (BIGUNION (IMAGE a1 (set (tyvars t)))) =
       CARD (IMAGE a1 (set (tyvars t)))’
        by(match_mp_tac (CARD_BIGUNION_SAME_SIZED_SETS |> SPEC “SUC 0” |> SIMP_RULE std_ss []) >>
           simp[PULL_EXISTS] >>
           rw[Abbr ‘a1’] >>
           res_tac >> gvs[tyvars_def]) >>
      pop_assum SUBST_ALL_TAC >>
      ‘¬INJ a1 (set(tyvars t)) (𝕌(:mlstring set))’
        by(spose_not_then strip_assume_tac >>
           drule INJ_CARD_IMAGE_EQ >>
           simp[]) >>
      gvs[INJ_DEF,Abbr ‘a1’] >>
      res_tac >> gvs[tyvars_def] >>
      metis_tac[])
  >- (gvs[tyvars_TYPE_SUBST_alt] >>
      match_mp_tac LESS_LESS_EQ_TRANS >>
      irule_at (Pos hd) CARD_BIGUNION_BOUNDED_SETS_LESS >>
      simp[PULL_EXISTS] >>
      qexists_tac ‘1’ >>
      qexists_tac ‘x’ >>
      simp[] >>
      conj_tac >- (rw[] >> res_tac >> gvs[tyvars_def]) >>
      simp[tyvars_def] >>
      simp[CARD_IMAGE])
  >- (gvs[tyvars_TYPE_SUBST_alt] >>
      match_mp_tac LESS_EQ_LESS_TRANS >>
      irule_at (Pos hd) CARD_BIGUNION_BOUNDED_SETS >>
      simp[PULL_EXISTS] >>
      qexists_tac ‘1’ >>
      simp[] >>
      conj_tac >- (rw[] >> res_tac >> gvs[tyvars_def]) >>
      qmatch_goalsub_abbrev_tac ‘IMAGE a1’ >>
      ‘CARD (IMAGE a1 (set(tyvars t))) ≤ CARD(set(tyvars t)) ∧
       CARD (IMAGE a1 (set(tyvars t))) ≠ CARD(set(tyvars t))’
        suffices_by DECIDE_TAC >>
      simp[CARD_IMAGE] >>
      spose_not_then strip_assume_tac >>
      unabbrev_all_tac >>
      drule_at (Pos last) CARD_IMAGE_EQ_BIJ >>
      simp[BIJ_DEF,INJ_DEF] >>
      metis_tac[])
QED

Theorem mg_sol_ext_geq_NOT_leq:
  !rs pqs p q s ctxt. mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ p = LR_TYPE_SUBST s (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
  /\ ~is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
  /\ wf_pqs [(p,q)]
  /\ dependency ctxt p q
  ==>
  ?r. mg_sol_seq ((MAP (λs. MAP (TYPE_SUBST r ## I) s ++ r) rs)++[[]]) (pqs++[(p,q)])
  /\ sol_seq_measure (LR_TYPE_SUBST (EL 0 rs) (FST $ EL 0 pqs))
        (LR_TYPE_SUBST ((λs. MAP (TYPE_SUBST r ## I) s ++ r) (EL 0 rs)) (FST $ EL 0 pqs))
Proof
  rpt strip_tac
  >> VAR_EQ_TAC
  >> imp_res_tac mg_sol_seq_LENGTH
  >> drule $ ONCE_REWRITE_RULE[CONJ_COMM] mg_solution'
  >> ntac 2 $ disch_then drule
  >> dxrule $ SIMP_RULE(bool_ss++LET_ss) [] mg_sol_ext_geq_tyvars_p0
  >> `rs <> [] /\ pqs <> []` by (CCONTR_TAC >> gs[])
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM LAST_EL,LR_TYPE_SUBST_type_preserving]
  >> fs[]
  >> disch_then $ drule_all_then strip_assume_tac
  >> disch_then $ drule (* mg_solution' *)
  >> ntac 2 $ pop_assum mp_tac
  >> drule_then strip_assume_tac mg_sol_seq_LENGTH
  >> `rs' <> []` by (CCONTR_TAC >> fs[])
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM LAST_EL,LR_TYPE_SUBST_type_preserving]
  >> drule mg_sol_seq_is_const_or_type
  >> rw[IMP_CONJ_THM,FORALL_AND_THM]
  >> qmatch_asmsub_abbrev_tac `NULL $ list_inter (list_complement _ _) (LIST_UNION _ c')`
  >> dxrule_at Any is_instance_LR_NOT_is_instance_LR
  >> impl_tac
  >- (
    match_mp_tac is_instance_LR_simps
    >> match_mp_tac LR_TYPE_SUBST_type_preserving
    >> fs[LAST_EL]
  )
  >> drule mg_sol_ext_geq
  >> rpt $ disch_then $ drule_at Any
  >> disch_then $ qspec_then `s` mp_tac
  >> asm_rewrite_tac[]
  >> rpt strip_tac
  >> qexists_tac `(MAP (TYPE_SUBST r ## I) es ++ r)`
  >> conj_tac
  >- (
    rpt (PRED_ASSUM (exists (curry op = "LAST")
      o map (fst o dest_const) o find_terms is_const) mp_tac)
    >> dep_rewrite.DEP_REWRITE_TAC[LAST_EL,equal_ts_on_FV,LR_TYPE_SUBST_type_preserving]
    >> rw[]
    >> drule_then (drule_then match_mp_tac)  mg_sols_equal_ts_on
    >> fs[]
    >> rw[]
    >> Cases_on `i < LENGTH pqs`
    >- (
      first_x_assum drule
      >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,EL_APPEND1,equal_ts_on_FV,GSYM LR_TYPE_SUBST_compose]
      >> rw[]
      >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose,MAP_MAP_o,MAP_APPEND,o_DEF,LR_TYPE_SUBST_type_preserving]
      >> fs[]
    )
    >> dep_rewrite.DEP_REWRITE_TAC[EL_MAP,EL_APPEND2]
    >> gs[NOT_LESS,LESS_OR_EQ,equal_ts_on_refl]
  )
  >> first_assum $ qspec_then `0` $ mp_tac o ONCE_REWRITE_RULE[equal_ts_on_symm]
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM LR_TYPE_SUBST_compose,LR_TYPE_SUBST_type_preserving,equal_ts_on_FV]
  >> conj_asm1_tac
  >- (REWRITE_TAC[GSYM EL] >> fs[])
  >> rw[]
  >> drule_then match_mp_tac var_renaming_sol_seq_measure
  >> gs[LR_TYPE_SUBST_type_preserving]
  >> rpt (PRED_ASSUM (exists (curry op = "rs")
    o map (fst o dest_var) o find_terms is_var) kall_tac)
  >> rpt (PRED_ASSUM (exists (curry op = "LAST")
    o map (fst o dest_const) o find_terms is_const) mp_tac)
  >> ONCE_REWRITE_TAC[equal_ts_on_symm]
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,LAST_EL]
  >> rw[LR_TYPE_SUBST_type_preserving]
  >> qpat_x_assum `LR_TYPE_SUBST s _ = _` kall_tac
  >> qmatch_goalsub_abbrev_tac `sol_seq_measure r0_p0 _`
  >> qmatch_asmsub_abbrev_tac `sol_seq_measure rn_qn _`
  >> qmatch_asmsub_abbrev_tac `mg_sol_seq (rs'' ++ _) _`
  >> `set (FV rn_qn) ⊆ set (FV r0_p0)` by (
    map_every qunabbrev_tac [`rn_qn`,`r0_p0`]
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> match_mp_tac sol_seq_FV_LR_TYPE_SUBST_SND_j_FST_i
    >> rpt $ goal_assum $ drule_at Any
    >> fs[mg_sol_seq_def]
  )
  >> `is_const_or_type rn_qn /\ is_const_or_type r0_p0` by (
    map_every qunabbrev_tac [`rn_qn`,`r0_p0`]
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_type_preserving]
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> fs[]
  )
  >> drule_at Any $ Ho_Rewrite.REWRITE_RULE[AND_IMP_INTRO,PULL_FORALL] CARD_SUBSET
  >> strip_tac
  >> fs[sol_seq_measure_def,Once DISJ_COMM,type_size_LR_TYPE_SUBST]
  >> TRY (
    qmatch_asmsub_abbrev_tac `type_size_LR rn_qn < type_size_LR (LR_TYPE_SUBST r rn_qn)`
    >> drule_then (qspec_then `r` assume_tac) type_size_LR_TYPE_SUBST
    >> qspecl_then [`rn_qn`,`r0_p0`] mp_tac type_size_LR_FV
    >> fs[]
  )
  >> rw[DISJ_EQ_IMP]
  >> rfs[NOT_LESS]
  >> dxrule LESS_EQUAL_ANTISYM
  >> rw[type_size_LR_TYPE_SUBST]
  >> qpat_x_assum `LENGTH _ < LENGTH _` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET,FV_ALL_DISTINCT,LR_TYPE_SUBST_type_preserving]
  >> rw[]
  >> ntac 2 (qhdtm_x_assum ‘is_const_or_type’ mp_tac)
  >> rw[is_const_or_type_eq]
  >> gvs[LR_TYPE_SUBST_def,FV_def,INST_def,INST_CORE_def,tvars_def,type_size_LR_def]
  >> rename1 ‘set (tyvars ty) ⊆ set (tyvars ty')’
  >> rename1 ‘TYPE_SUBST σ ty'’
  >> ‘type_size' (TYPE_SUBST σ ty) = type_size' ty’
       by(match_mp_tac TYPE_SUBST_type_size_intr' >>
          drule TYPE_SUBST_type_size_intr >>
          metis_tac[SUBSET_THM])
  >> gvs[type_size_invariant_CARD_less_IFF]
  >> metis_tac[SUBSET_THM]
QED

(* Lemma 5.11, Kunčar 2015 *)
Theorem mg_sol_exists'[local]:
  !rs pqs r pq ctxt. (
  sol_seq (r::rs) (pq::pqs)
  /\ EVERY (UNCURRY (dependency ctxt)) (pq::pqs)
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt)
  ==> ?rs' k. mg_sol_seq rs' (pq::pqs)
    /\ path_starting_at ctxt k rs' (pq::pqs)
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> strip_tac
  >- (
    rw[]
    >> map_every qexists_tac [`[[]]`,`0`]
    >> fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def,ELIM_UNCURRY,path_starting_at_def,ELIM_UNCURRY,sol_seq_def,wf_pqs_def,equiv_ts_on_refl]
    >> rw[]
    >> goal_assum $ drule_at Any
    >> fs[equal_ts_on_refl]
  )
  >> rw[SNOC_APPEND]
  >> Q.ISPEC_THEN `pqs` assume_tac (REWRITE_RULE[SNOC_APPEND] SNOC_CASES)
  >> gvs[]
  >- fs[sol_seq_def]
  >> `LENGTH rs = LENGTH l` by fs[sol_seq_def]
  >> drule_then (qspec_then `LENGTH rs + 1` assume_tac) sol_seq_TAKE
  >> fs[TAKE_APPEND1]
  >> first_x_assum drule
  >> rpt $ disch_then $ drule_at Any
  >> rw[TAKE_APPEND1]
  >> `LENGTH rs' = SUC (LENGTH l)` by fs[sol_seq_def,mg_sol_seq_def]
  >> rev_drule sol_ex_non_orth
  >> rpt $ disch_then $ drule_at Any
  >> disch_then $ qspecl_then [`rs'`,`LENGTH rs'`,`k`] mp_tac
  >> `wf_pqs [x']` by fs[sol_seq_def,wf_pqs_def]
  >> `rs' <> []` by (CCONTR_TAC >> fs[sol_seq_def,wf_pqs_def])
  >> drule_then assume_tac LAST_EL
  >> fs[EVERY_APPEND,EL_APPEND2,TAKE_APPEND1,GSYM ADD1,is_instance_LR_eq]
  >> strip_tac
  (* mg_sol_ext_geq *)
  >- (
    drule mg_sol_ext_geq
    >> rpt $ disch_then $ drule_at Any
    >> disch_then $ qspecl_then [`FST x'`,`SND x'`,`s`] mp_tac
    >> impl_keep_tac
    >- (
      rfs[]
      >> qpat_x_assum `_ = FST x'` $ REWRITE_TAC o single o GSYM
      >> rpt AP_TERM_TAC
      >> dep_rewrite.DEP_REWRITE_TAC[LAST_EL]
      >> ONCE_REWRITE_TAC[GSYM APPEND]
      >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1]
      >> fs[]
    )
    >> qpat_x_assum `_ = FST x'` kall_tac
    >> rw[]
    >> goal_assum drule
    >> qexists_tac `SUC (LENGTH l)`
    >> rw[path_starting_at_def]
    >- fs[wf_pqs_def,EVERY_APPEND,sol_seq_def]
    >- fs[DROP_APPEND1,EVERY_DROP]
    >- (
      dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      >> fs[equiv_ts_on_refl]
    )
    >> qpat_x_assum `mg_sol_seq (_ ++_) _` $ strip_assume_tac o REWRITE_RULE[mg_sol_seq_def]
    >> drule_then (qspec_then `SUC (LENGTH l)` mp_tac) sol_seq_DROP
    >> fs[]
  )
  >> drule mg_sol_ext_leq
  >> rpt $ disch_then $ drule_at Any
  >> disch_then $ qspecl_then [`FST x'`,`SND x'`,`s`] mp_tac
  >> impl_keep_tac
  >- (
    rfs[]
    >> rpt AP_TERM_TAC
    >> dep_rewrite.DEP_REWRITE_TAC[LAST_EL]
    >> ONCE_REWRITE_TAC[GSYM APPEND]
    >> dep_rewrite.DEP_ONCE_REWRITE_TAC[EL_APPEND1]
    >> fs[]
  )
  >> strip_tac
  >> fs[]
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST _ (FST _) = del`
  >> qpat_x_assum `del = _` kall_tac
  >> qunabbrev_tac `del`
  >> goal_assum drule
  >> qexists_tac `k`
  >> fs[path_starting_at_def,wf_pqs_def,EVERY_APPEND,EVERY_DROP]
  >> conj_tac
  >- (
    ONCE_REWRITE_TAC[GSYM $ CONJUNCT2 APPEND]
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1]
    >> fs[]
  )
  >> match_mp_tac sol_seq_DROP
  >> fs[mg_sol_seq_def]
QED

(* Lemma 5.11, Kunčar 2015 *)
Theorem mg_sol_exists:
  !rs pqs ctxt. (
  0 < LENGTH rs
  /\ sol_seq rs pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt)
  ==> ?rs' k. mg_sol_seq rs' pqs
    /\ path_starting_at ctxt k rs' pqs
Proof
  rw[]
  >> `0 < LENGTH pqs` by fs[sol_seq_def]
  >> fs[GSYM NOT_NIL_EQ_LENGTH_NOT_0]
  >> qpat_x_assum `sol_seq _ _` mp_tac
  >> imp_res_tac (REWRITE_RULE[NULL_EQ] CONS)
  >> ntac 2 $ pop_assum $ PURE_ONCE_REWRITE_TAC o single o GSYM
  >> disch_then assume_tac
  >> dxrule mg_sol_exists'
  >> disch_then match_mp_tac
  >> asm_rewrite_tac[]
  >> drule_then (ONCE_REWRITE_TAC o single) $ REWRITE_RULE[NULL_EQ] CONS
  >> asm_rewrite_tac[]
QED

(* Definition 5.12 *)
Definition has_mg_sol_leq_def:
  has_mg_sol_leq pqs p =
  ?rs. mg_sol_seq rs pqs
    /\ is_const_or_type p
    /\ 0 < LENGTH rs
    /\ is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
End

Definition has_mg_sol_geq_def:
  has_mg_sol_geq pqs p =
  ?rs. mg_sol_seq rs pqs
    /\ is_const_or_type p
    /\ 0 < LENGTH rs
    /\ is_instance_LR (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
End

val _ = Parse.add_infix("≼", 401, Parse.NONASSOC)
Overload "≼" = ``λpqs p. has_mg_sol_leq pqs p``
val _ = Parse.add_infix("≽", 401, Parse.NONASSOC)
Overload "≽" = ``λpqs p. has_mg_sol_geq pqs p``

Theorem has_mg_sol_leq_imp:
  !pqs p rs ctxt. has_mg_sol_leq pqs p /\ mg_sol_seq rs pqs
  /\ monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  ==> is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
Proof
  rw[has_mg_sol_leq_def,is_instance_LR_eq,LR_TYPE_SUBST_type_preserving]
  >> fs[]
  >> imp_res_tac mg_sol_seq_is_const_or_type
  >> imp_res_tac mg_sol_seq_LENGTH
  >> qpat_x_assum `LR_TYPE_SUBST _ _ = _` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[LAST_EL]
  >> fs[NOT_NIL_EQ_LENGTH_NOT_0,LR_TYPE_SUBST_type_preserving]
  >> drule_then (rev_drule_then $ qspec_then `PRE (LENGTH pqs)` mp_tac) mg_solution
  >> `MEM (EL (PRE $ LENGTH pqs) pqs) pqs` by fs[EL_MEM]
  >> qpat_x_assum `EVERY _ _` $ dxrule_then assume_tac o REWRITE_RULE[EVERY_MEM]
  >> fs[ELIM_UNCURRY]
  >> qpat_x_assum `monotone _` $ (dxrule_then assume_tac) o REWRITE_RULE[monotone_def,list_subset_set]
  >> strip_tac
  >> dxrule_all equiv_ts_on_subset
  >> fs[equiv_ts_on_FV]
  >> strip_tac
  >> asm_rewrite_tac[]
  >> disch_then $ REWRITE_TAC o single o GSYM
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose]
  >> asm_rewrite_tac[]
  >> irule_at Any EQ_REFL
QED

Theorem has_mg_sol_geq_imp:
  !pqs p rs ctxt. has_mg_sol_geq pqs p /\ mg_sol_seq rs pqs
  /\ monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  ==> is_instance_LR (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
Proof
  rw[has_mg_sol_geq_def,is_instance_LR_eq,LR_TYPE_SUBST_type_preserving]
  >> fs[]
  >> imp_res_tac mg_sol_seq_is_const_or_type
  >> imp_res_tac mg_sol_seq_LENGTH
  >> dep_rewrite.DEP_REWRITE_TAC[LAST_EL]
  >> fs[NOT_NIL_EQ_LENGTH_NOT_0,LR_TYPE_SUBST_type_preserving]
  >> drule_then (rev_drule_then $ qspec_then `PRE (LENGTH pqs)` mp_tac) mg_solution
  >> `MEM (EL (PRE $ LENGTH pqs) pqs) pqs` by fs[EL_MEM]
  >> qpat_x_assum `EVERY _ _` $ dxrule_then assume_tac o REWRITE_RULE[EVERY_MEM]
  >> fs[ELIM_UNCURRY]
  >> qpat_x_assum `monotone _` $ (dxrule_then assume_tac) o REWRITE_RULE[monotone_def,list_subset_set]
  >> strip_tac
  >> dxrule_all equiv_ts_on_subset
  >> fs[equiv_ts_on_FV]
  >> strip_tac
  >> asm_rewrite_tac[]
  >> qexists_tac `MAP (TYPE_SUBST s ## I) (MAP SWAP e) ++ s`
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose,var_renaming_SWAP_LR_id]
  >> fs[]
QED

Triviality CONS_FRONT:
  !s. 1 < LENGTH s ==> HD s::TL (FRONT s) = FRONT s
Proof
  Induct >> rw[FRONT_DEF]
QED

Triviality EVERY_FRONT:
  !l P. ~NULL l /\ EVERY P l ==> EVERY P (FRONT l)
Proof
  Induct >> rw[FRONT_DEF,NULL_EQ]
QED

(* Corollary 5.13 *)
Theorem leq_geq_monotone_composable:
  !rs pqs ctxt.
  1 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ sol_seq rs pqs
  ==> has_mg_sol_leq (FRONT pqs) (FST (LAST pqs))
  \/ has_mg_sol_geq (FRONT pqs) (FST (LAST pqs))
Proof
  rw[]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> `1 < LENGTH pqs` by fs[]
  >> qspecl_then [`TL (FRONT rs)`,`TL (FRONT pqs)`,`HD rs`,`HD pqs`,`ctxt`] mp_tac mg_sol_exists'
  >> imp_res_tac CONS_FRONT
  >> ASM_REWRITE_TAC[]
  >> `~NULL pqs` by (CCONTR_TAC >> fs[NULL_EQ])
  >> `~NULL rs` by (CCONTR_TAC >> fs[NULL_EQ] >> rfs[])
  >> drule sol_seq_TAKE
  >> disch_then (qspec_then `PRE (LENGTH rs)` assume_tac)
  >> rfs[EVERY_FRONT,REWRITE_RULE[GSYM NULL_EQ] TAKE_PRE_LENGTH]
  >> rw[]
  >> qspecl_then [`pqs`,`rs`,`rs'`,`ctxt`,`PRE(LENGTH rs)`,`k`] mp_tac sol_ex_non_orth
  >> rw[REWRITE_RULE[GSYM NULL_EQ] TAKE_PRE_LENGTH,has_mg_sol_leq_def,has_mg_sol_geq_def]
  >- (
    DISJ2_TAC
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> imp_res_tac sol_seq_is_const_or_type
    >> `~NULL rs'` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def,NULL_EQ])
    >> `LENGTH rs' = PRE(LENGTH pqs)` by fs[mg_sol_seq_def,sol_seq_def,LENGTH_FRONT,NULL_EQ]
    >> `~NULL (FRONT pqs)` by (CCONTR_TAC >> Cases_on `pqs` >> fs[FRONT_CONS_EQ_NIL,NULL_EQ])
    >> `0 < PRE (LENGTH pqs)` by (CCONTR_TAC >> fs[])
    >> `PRE (LENGTH (FRONT pqs)) < LENGTH (FRONT pqs)` by (
      fs[REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
      >> fs[INV_PRE_LESS]
    )
    >> fs[REWRITE_RULE[GSYM NULL_EQ] LAST_EL,EL_FRONT,REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
  )
  >> DISJ1_TAC
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> imp_res_tac sol_seq_is_const_or_type
  >> `~NULL rs'` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def,NULL_EQ])
  >> `LENGTH rs' = PRE(LENGTH pqs)` by fs[mg_sol_seq_def,sol_seq_def,LENGTH_FRONT,NULL_EQ]
  >> `~NULL (FRONT pqs)` by (CCONTR_TAC >> Cases_on `pqs` >> fs[FRONT_CONS_EQ_NIL,NULL_EQ])
  >> `0 < PRE (LENGTH pqs)` by (CCONTR_TAC >> fs[])
  >> `PRE (LENGTH (FRONT pqs)) < LENGTH (FRONT pqs)` by (
    fs[REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
    >> fs[INV_PRE_LESS]
  )
  >> fs[REWRITE_RULE[GSYM NULL_EQ] LAST_EL,EL_FRONT,REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
QED

(* Definition 5.14 *)
Definition seq_asc_def:
  seq_asc pqs =
  (wf_pqs pqs /\ !i.
  0 < i /\ i < LENGTH pqs ==>
  has_mg_sol_leq (TAKE i pqs) (FST (EL i pqs)))
End

(* Corollary 5.15 *)
Theorem seq_asc_mg_sol_path:
  !pqs ctxt n.
  EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ seq_asc pqs
  /\ 0 < n /\ n < LENGTH pqs
  ==> ?rs. mg_sol_seq rs (TAKE n pqs)
  /\ path_starting_at ctxt 0 rs (TAKE n pqs)
Proof
  rw[seq_asc_def,has_mg_sol_leq_def]
  >> first_assum drule
  >> ASM_REWRITE_TAC[]
  >> strip_tac
  >> `LENGTH rs = n` by fs[mg_sol_seq_def,sol_seq_def]
  >> goal_assum drule
  >> `!i. i <= n ==> mg_sol_seq (TAKE i rs) (TAKE i pqs)` by (
    Induct_on `n - i`
    >> rw[ADD_EQ_SUB]
    >- (
      drule_all_then assume_tac LESS_EQUAL_ANTISYM
      >> fs[TAKE_LENGTH_ID]
    )
    >> fs[ADD_EQ_SUB,LESS_OR_EQ]
    >> Cases_on `i = 0`
    >- rw[mg_sol_seq_def,sol_seq_def,wf_pqs_def]
    >> fs[NOT_ZERO_LT_ZERO]
    >> qpat_x_assum `!i. _ ==> ?rs. _` $ qspec_then `i` mp_tac
    >> rw[is_instance_LR_eq,TAKE_LENGTH_ID]
    >> drule mg_sol_ext_leq
    >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST s (FST pq) = _`
    >> rpt $ disch_then $ drule_at Any
    >> disch_then $ qspec_then `SND pq` mp_tac
    >> `SUC i <= LENGTH rs` by fs[]
    >> impl_keep_tac
    >- (
      rev_drule mg_sol_seq_is_const_or_type
      >> fs[EVERY_TAKE,wf_pqs_def,Abbr`pq`,ELIM_UNCURRY,EL_TAKE]
    )
    >> `TAKE i pqs ++ [pq] = TAKE (SUC i) pqs` by fs[ADD1,TAKE_SUM,TAKE1_DROP]
    >> pop_assum $ REWRITE_TAC o single
    >> first_x_assum $ qspec_then `SUC i` mp_tac
    >> fs[ADD_EQ_SUB,GSYM LESS_OR_EQ]
    >> rpt strip_tac
    >> qspecl_then [`_1`,`_2`,`TAKE (SUC _) _`] (mp_tac o GEN_ALL) mg_solutions
    >> disch_then $ drule_then $ rev_drule_then strip_assume_tac
    >> rw[mg_sol_seq_def]
    >- (
      qpat_x_assum `mg_sol_seq (TAKE _ rs) (TAKE _ pqs)` $ assume_tac o cj 1 o REWRITE_RULE[mg_sol_seq_def]
      >> drule sol_seq_TAKE
      >> fs[TAKE_TAKE]
    )
    >> qpat_x_assum `mg_sol_seq _ (TAKE i _)` $ mp_tac o REWRITE_RULE[mg_sol_seq_def,Once CONJ_COMM]
    >> fs[GSYM AND_IMP_INTRO]
    >> disch_then drule
    >> rpt strip_tac
    >> qexists_tac `MAP (λi. MAP (TYPE_SUBST (EL i es') ## I) (EL i es) ++ (EL i es')) (COUNT_LIST i)`
    >> conj_tac
    >- fs[LENGTH_COUNT_LIST]
    >> rpt strip_tac
    >> `i' < LENGTH rs'` by fs[mg_sol_seq_def,sol_seq_def]
    >> `is_const_or_type (FST (EL i' pqs))` by (
      rev_drule mg_sol_seq_is_const_or_type
      >> fs[EVERY_TAKE,wf_pqs_def,ELIM_UNCURRY,EL_TAKE]
    )
    >> ntac 2 $ first_x_assum $ qspec_then `i'` mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV,EL_MAP,EL_TAKE,EL_COUNT_LIST,LR_TYPE_SUBST_type_preserving,EL_APPEND1]
    >> fs[LENGTH_COUNT_LIST]
  )
  >> rw[path_starting_at_def,EVERY_TAKE]
  >- fs[mg_sol_seq_def,sol_seq_def]
  >- (
    `rs <> [] /\ pqs <> []` by (strip_tac >> CCONTR_TAC >> fs[])
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> first_x_assum $ qspec_then `1` mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[TAKE1,EL_TAKE]
    >> fs[]
    >> strip_tac
    >> drule mg_sol_seq_is_const_or_type
    >> rw[]
    >> `mg_sol_seq [[]] [HD pqs]` by (
      rw[mg_sol_seq_def]
      >- fs[sol_seq_def,mg_sol_seq_def]
      >> qexists_tac `[HD rs']`
      >> fs[equal_ts_on_refl]
    )
    >> drule_then (rev_drule_then strip_assume_tac) mg_solutions
    >> Cases_on `es`
    >> fs[equiv_ts_on_def,EVERY_MEM]
    >> rpt $ goal_assum drule
  )
  >> fs[mg_sol_seq_def]
QED

(* various properties about llists *)

Theorem every_LTAKE_EVERY':
  !i P s. every P s /\ ~LFINITE s
  ==>  EVERY P (THE (LTAKE i s))
Proof
  rw[GSYM every_fromList_EVERY]
  >> match_mp_tac every_LAPPEND1
  >> imp_res_tac LTAKE_DROP
  >> qexists_tac `THE (LDROP i s)`
  >> fs[]
QED

Theorem NOT_LFINITE_LDROP:
  !ll k. ~LFINITE ll ==> ~LFINITE (THE (LDROP k ll))
Proof
  rw[LFINITE,infinite_lnth_some]
  >> first_assum (qspec_then `n+k` assume_tac)
  >> fs[]
  >> drule LNTH_LDROP
  >> first_x_assum (qspec_then `n` assume_tac)
  >> fs[LNTH_ADD]
QED

Theorem EL_LTAKE_LDROP_LNTH:
  !s i j k. ~LFINITE s /\ i < j
  ==>
  EL i (THE (LTAKE j (THE (LDROP k s)))) = THE (LNTH (k+i) s)
Proof
  rpt strip_tac
  >> fs[LNTH_ADD]
  >> `IS_SOME (LDROP k s)` by (
    fs[IS_SOME_EXISTS]
    >> match_mp_tac NOT_LFINITE_DROP
    >> ASM_REWRITE_TAC[]
  )
  >> `IS_SOME (LTAKE j (THE (LDROP k s)))` by (
    fs[IS_SOME_EXISTS]
    >> match_mp_tac NOT_LFINITE_TAKE
    >> match_mp_tac NOT_LFINITE_DROP_LFINITE
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> fs[IS_SOME_EXISTS]
  >> drule LTAKE_LNTH_EL
  >> disch_then imp_res_tac
  >> rfs[option_CLAUSES]
QED

Theorem FRONT_TAKE_PRE:
  !ls. ~NULL ls ==> FRONT ls = TAKE (PRE (LENGTH ls)) ls
Proof
  rw[NULL_EQ]
  >> qspecl_then [`PRE (LENGTH ls)`,`FRONT ls`] mp_tac TAKE_APPEND1
  >> drule LENGTH_FRONT
  >> disch_then (fn x => fs[GSYM x])
  >> disch_then (qspec_then `[LAST ls]` (mp_tac o GSYM))
  >> imp_res_tac APPEND_FRONT_LAST
  >> fs[]
QED

Theorem LDROP_LUNFOLD_LGENLIST[local]:
  !i:num. THE (LDROP i (LGENLIST I NONE))
  = LUNFOLD (λn. SOME (n+1,n)) i
Proof
  Induct
  >- fs[LGENLIST_def]
  >> fs[ADD1,LDROP_ADD]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac NOT_LFINITE_DROP
  >> first_x_assum (qspec_then `i` mp_tac)
  >> rw[]
  >> fs[option_CLAUSES]
  >> CONV_TAC (LHS_CONV (PURE_ONCE_REWRITE_CONV[LUNFOLD]))
  >> fs[]
QED

Theorem LGENLIST_num:
  !i. LNTH i (LGENLIST I NONE) = SOME i
Proof
  rw[]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> fs[infinite_lnth_some]
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
  >> imp_res_tac LNTH_LDROP
  >> qspec_then `i` assume_tac LDROP_LUNFOLD_LGENLIST
  >> fs[option_CLAUSES]
QED

Theorem LNTH_LFILTER1[local]:
  !k ll e. ~LFINITE ll /\ LNTH k ll = SOME e /\ P e
  ==> ?n. LNTH n (LFILTER P ll) = SOME e
Proof
  rw[]
  >> drule (CONJUNCT1 LTAKE_DROP)
  >> disch_then (qspec_then `k` (fn x => ONCE_REWRITE_TAC[GSYM x]))
  >> fs[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList]
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 _`
  >> qexists_tac `THE (LLENGTH ll1)`
  >> imp_res_tac LNTH_LDROP
  >> fs[Abbr`ll1`,LNTH_LAPPEND]
  >> qmatch_asmsub_abbrev_tac `LHD ll1`
  >> Cases_on `ll1`
  >> fs[]
QED

Theorem LFILTER_num_pred:
  !P e. P e = (?n. LNTH n (LFILTER P (LGENLIST I NONE)) = SOME e)
Proof
  rw[EQ_IMP_THM]
  >> qspecl_then [`LGENLIST I NONE`,`P`] assume_tac every_LFILTER
  >> imp_res_tac every_LNTH
  >> qspec_then `e` assume_tac LGENLIST_num
  >> match_mp_tac LNTH_LFILTER1
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[LFINITE_LGENLIST]
QED

Theorem LENGTH_num:
  !i. LENGTH (THE (LTAKE i (LGENLIST I NONE))) = i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac NOT_LFINITE_TAKE
  >> rw[]
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem LTAKE_GENLIST_num:
  !i f. THE (LTAKE i (LGENLIST I NONE)) = GENLIST I i
Proof
  Induct
  >> rw[LTAKE_SNOC_LNTH,GENLIST]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac infinite_lnth_some
  >> imp_res_tac NOT_LFINITE_TAKE
  >> rpt (first_x_assum (qspec_then `i` assume_tac))
  >> fs[LGENLIST_num,option_CLAUSES]
QED

Theorem LDROP_GENLIST_NOT_SOME:
  !n i. LNTH (SUC n) (THE (LDROP i (LGENLIST I NONE))) <> SOME i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> rw[]
  >> qspec_then `i + SUC n` assume_tac LGENLIST_num
  >> imp_res_tac NOT_LFINITE_DROP
  >> qspecl_then [`i`,`SUC n`,`LGENLIST I NONE`] mp_tac LNTH_ADD
  >> rw[]
  >> fs[]
QED

Theorem LDROP_SUC_LGENLIST_NOT_SOME:
  !n i. LNTH n (THE (LDROP (SUC i) (LGENLIST I NONE))) <> SOME i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> rw[]
  >> qspec_then `SUC i + n` assume_tac LGENLIST_num
  >> imp_res_tac NOT_LFINITE_DROP
  >> qspecl_then [`SUC i`,`n`,`LGENLIST I NONE`] mp_tac LNTH_ADD
  >> rw[]
  >> fs[]
QED

Theorem NOT_LFINITE_LFILTER:
  !P ll. ~LFINITE (LFILTER P ll) ==> ~LFINITE ll
Proof
  Induct_on `THE(LLENGTH ll)`
  >> rpt gen_tac
  >> strip_tac
  >> gen_tac
  >> match_mp_tac MONO_NOT
  >- (
    rw[LFINITE_LLENGTH]
    >> fs[option_CLAUSES]
    >> rveq
    >> imp_res_tac LLENGTH_0
    >> fs[]
  )
  >> Cases_on `ll`
  >> fs[]
  >> rw[]
  >> imp_res_tac LFINITE_LLENGTH
  >> first_x_assum (qspec_then `t` assume_tac)
  >> rfs[option_CLAUSES]
  >> fs[]
QED

Theorem NOT_LFINITE_LENGTH:
  !ll k. ~LFINITE ll ==> LENGTH (THE (LTAKE k ll)) = k
Proof
  rw[]
  >> drule NOT_LFINITE_TAKE
  >> disch_then (qspec_then `k` assume_tac)
  >> fs[]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem LFINITE_LFILTER:
  !P ll. LFINITE ll ==> LFINITE (LFILTER P ll)
Proof
  rw[]
  >> CCONTR_TAC
  >> imp_res_tac NOT_LFINITE_LFILTER
QED

Theorem LLENGTH_LFILTER_LEQ:
  !P ll. LFINITE ll ==>
  THE(LLENGTH (LFILTER P ll)) <= THE (LLENGTH ll)
Proof
  Induct_on `THE(LLENGTH ll)`
  >- (
    rw[LFINITE_LLENGTH]
    >> fs[option_CLAUSES]
    >> rveq
    >> imp_res_tac LLENGTH_0
    >> fs[]
  )
  >> Cases_on `ll`
  >> fs[]
  >> rw[]
  >> drule LFINITE_LFILTER
  >> disch_then (qspec_then `P` assume_tac)
  >> imp_res_tac LFINITE_LLENGTH
  >> rw[]
  >> first_x_assum (qspec_then `t` assume_tac)
  >> rfs[option_CLAUSES]
  >> fs[]
  >> rw[]
  >> first_x_assum (qspec_then `P` mp_tac)
  >> fs[option_CLAUSES]
QED

Definition infin_or_leq_def:
  infin_or_leq ll k P =
    (~LFINITE ll \/ (LFINITE ll /\ k <= THE (LLENGTH ll) /\ P))
End

Theorem LNTH_EL_LTAKE:
  !ll n k.
  infin_or_leq ll k T /\ n < k ==> LNTH n ll = SOME (EL n (THE (LTAKE k ll)))
Proof
  rw[infin_or_leq_def]
  >> match_mp_tac LTAKE_LNTH_EL
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >- (
    drule NOT_LFINITE_TAKE
    >> disch_then (qspec_then `k` mp_tac)
    >> rw[]
    >> fs[]
  )
  >> imp_res_tac LFINITE_TAKE
  >> fs[]
QED

Theorem LNTH_THE_DROP:
  !k l ll. infin_or_leq ll l T
  ==> LNTH k (THE (LDROP l ll)) = LNTH (k+l) ll
Proof
  rw[infin_or_leq_def]
  >> imp_res_tac LTAKE_DROP
  >> pop_assum mp_tac
  >> TRY (disch_then (qspec_then `l` mp_tac))
  >> disch_then (fn x => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV[GSYM x])))
  >> `IS_SOME(LTAKE l ll)` by (
    fs[IS_SOME_EXISTS,NOT_LFINITE_TAKE,LFINITE_TAKE]
  )
  >> fs[IS_SOME_EXISTS]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[LNTH_LAPPEND]
QED

Theorem LTAKE_CONS:
  !k ll. infin_or_leq ll (SUC k) T
  ==> THE (LTAKE (SUC k) ll) = THE (LTAKE k ll) ++ [THE (LNTH k ll)]
  /\ IS_SOME (LTAKE (SUC k) ll)
  /\ IS_SOME (LTAKE k ll)
  /\ IS_SOME (LNTH k ll)
Proof
  rw[LTAKE_SNOC_LNTH,infin_or_leq_def]
  >> TRY (drule NOT_LFINITE_TAKE >> disch_then (qspec_then `SUC (SUC k)` assume_tac)
    >> drule NOT_LFINITE_TAKE >> disch_then (qspec_then `k` assume_tac))
  >> TRY (drule LFINITE_TAKE >> disch_then (qspec_then `k` assume_tac)
    >> drule LFINITE_TAKE >> disch_then (qspec_then `SUC k` assume_tac))
  >> rfs[]
  >> imp_res_tac LTAKE_LNTH_EL
  >> fs[]
QED

Theorem less_opt_cases:
  !opt k. less_opt k opt =
    (opt = NONE \/ ?l. opt = SOME l /\ k < l)
Proof
  Cases >> fs[less_opt_def]
QED

Theorem NOT_LFINITE_LLENGTH_NONE:
  !ll. ~LFINITE ll <=> LLENGTH ll = NONE
Proof
  fs[NOT_LFINITE_NO_LENGTH,EQ_IMP_THM,LLENGTH]
QED

Theorem less_opt_LENGTH_THE_LTAKE:
  !n ll. less_opt n (LLENGTH ll) ==> LENGTH (THE (LTAKE n ll)) = n
Proof
  rw[less_opt_cases]
  >> qmatch_goalsub_rename_tac `LTAKE n ll`
  >- (
    fs[GSYM NOT_LFINITE_LLENGTH_NONE]
    >> drule_then (qspec_then `n` strip_assume_tac) NOT_LFINITE_TAKE
    >> imp_res_tac LTAKE_LENGTH
    >> fs[]
  )
  >> drule_then strip_assume_tac LTAKE_LLENGTH_SOME
  >> drule_then (qspec_then `n` assume_tac) LTAKE_TAKE_LESS
  >> rfs[]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem infin_or_leq_IS_SOME_LTAKE:
  !ll k. infin_or_leq ll k T ==> IS_SOME(LTAKE k ll)
Proof
  rw[infin_or_leq_def,IS_SOME_EXISTS]
  >> fs[NOT_LFINITE_TAKE,LFINITE_TAKE]
QED

Theorem infin_or_leq_LENGTH_LTAKE_EQ:
  !ll k. infin_or_leq ll k T ==> LENGTH (THE (LTAKE k ll)) = k
Proof
  rw[infin_or_leq_def]
  >> fs[NOT_LFINITE_LENGTH]
  >> imp_res_tac LFINITE_LLENGTH
  >> imp_res_tac LTAKE_LLENGTH_SOME
  >> fs[]
  >> drule LTAKE_TAKE_LESS
  >> disch_then (qspec_then `k` assume_tac)
  >> rfs[]
  >> match_mp_tac LENGTH_TAKE
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem DROP_LTAKE_EQ_LTAKE_LDROP:
  !ll k i. ~LFINITE ll
  ==> DROP k (THE (LTAKE (i + k) ll)) = THE (LTAKE i (THE (LDROP k ll)))
Proof
  rpt strip_tac
  >> qmatch_goalsub_rename_tac `LTAKE i $ THE $ LDROP k ll`
  >> drule_then (qspec_then `k` mp_tac) $ cj 1 $ LTAKE_DROP
  >> disch_then $ CONV_TAC o LHS_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> qspecl_then [`k`,`ll`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> qspecl_then [`THE $ LDROP k ll`,`THE $ LTAKE k ll`,`i`] mp_tac LTAKE_LAPPEND_fromList
  >> rfs[less_opt_cases,GSYM NOT_LFINITE_LLENGTH_NONE]
  >> disch_then kall_tac
  >> drule_then (qspec_then `k` strip_assume_tac) NOT_LFINITE_TAKE
  >> drule_then (qspec_then `k` strip_assume_tac) NOT_LFINITE_LDROP
  >> drule_then (qspec_then `i` strip_assume_tac) NOT_LFINITE_TAKE
  >> fs[OPTION_MAP_EQ_SOME,DROP_APPEND2]
QED

Theorem TAKE_LTAKE_EQ_LTAKE_LTAKE:
  !ll k l. ~LFINITE ll /\ k <= l
  ==> TAKE k (THE (LTAKE l ll)) = THE (LTAKE k ll)
Proof
  rpt strip_tac
  >> qmatch_goalsub_rename_tac `TAKE k`
  >> qmatch_goalsub_rename_tac `LTAKE l ll`
  >> drule_then (qspec_then `l` strip_assume_tac) NOT_LFINITE_TAKE
  >> drule_all LTAKE_TAKE_LESS
  >> fs[]
QED

Theorem FRONT_LAST_APPEND:
  !ls x. FRONT (ls ++ [x]) = ls /\ LAST (ls ++ [x]) = x
Proof
  rw[]
  >> qspec_then `ls++[x]` mp_tac APPEND_FRONT_LAST
  >> fs[]
QED

Theorem LTAKE_FRONT_LNTH_LAST:
  ∀pqs k. ~LFINITE pqs ==>
  FRONT (THE (LTAKE (SUC k) pqs)) = THE (LTAKE k pqs)
  /\ LAST (THE (LTAKE (SUC k) pqs)) = THE (LNTH k pqs)
Proof
  rw[]
  >> qspecl_then [`k`,`pqs`] assume_tac LTAKE_CONS
  >> rfs[infin_or_leq_def,FRONT_LAST_APPEND]
QED

Theorem every_THE_LDROP:
  !ll P k. ~LFINITE ll /\ every P ll ==> every P (THE (LDROP k ll))
Proof
  rw[]
  >> qpat_x_assum `every _ _` mp_tac
  >> drule_then (qspec_then `k` mp_tac) $ CONJUNCT1 LTAKE_DROP
  >> disch_then $ CONV_TAC o LAND_CONV o DEPTH_CONV o REWR_CONV o GSYM
  >> strip_tac
  >> drule_at Any every_LAPPEND2_LFINITE
  >> rw[LFINITE_fromList]
QED

(* wf_pqs_def for llists *)

Definition wf_pqs_inf_def:
  wf_pqs_inf (pqs:((type + term) # (type + term)) llist) =
  every (λx. is_const_or_type (FST x) /\ is_const_or_type (SND x)) pqs
End

Theorem wf_pqs_inf_wf_pqs_LTAKE:
  !pqs k. wf_pqs_inf pqs /\ ~LFINITE pqs ==> wf_pqs (THE (LTAKE k pqs))
Proof
  rw[wf_pqs_inf_def,wf_pqs_def,every_LTAKE_EVERY',LAMBDA_PROD,o_DEF]
QED

Theorem wf_pqs_inf_LDROP:
  !pqs k. wf_pqs_inf pqs /\ ~LFINITE pqs ==> wf_pqs_inf (THE (LDROP k pqs))
Proof
  rw[wf_pqs_inf_def,every_THE_LDROP,NOT_LFINITE_LDROP]
QED

(* k-ascending as 'ascending from k on' *)
Definition seq_k_asc_inf_def:
  seq_k_asc_inf k pqs =
  (wf_pqs_inf pqs /\ ~LFINITE pqs /\
  !i. k < i ==> has_mg_sol_leq (THE (LTAKE i pqs)) (FST (THE (LNTH i pqs))))
End

(* Definition 5.14, for llists *)
Definition seq_asc_inf_def:
  seq_asc_inf pqs = seq_k_asc_inf 0 pqs
End

Theorem seq_asc_inf_seq_asc_LTAKE:
  !pqs k. seq_asc_inf pqs ==> seq_asc (THE (LTAKE k pqs))
Proof
  rw[seq_k_asc_inf_def,seq_asc_inf_def,seq_asc_def,wf_pqs_inf_wf_pqs_LTAKE]
  >> `infin_or_leq pqs k T` by fs[infin_or_leq_def,wf_pqs_inf_def]
  >> fs[infin_or_leq_LENGTH_LTAKE_EQ]
  >> first_x_assum (qspec_then `i` assume_tac)
  >> drule_all_then assume_tac LNTH_EL_LTAKE
  >> drule_all_then strip_assume_tac $ REWRITE_RULE[IS_SOME_EXISTS] infin_or_leq_IS_SOME_LTAKE
  >> drule_then (qspec_then `i` assume_tac) LTAKE_TAKE_LESS
  >> gs[]
QED

(* sol_seq_def for llists *)
Definition sol_seq_inf_def:
  sol_seq_inf rs pqs =
    ((!i. LR_TYPE_SUBST (THE (LNTH i rs)) (SND (THE (LNTH i pqs)))
    = LR_TYPE_SUBST (THE (LNTH (SUC i) rs)) (FST (THE (LNTH (SUC i) pqs))))
    /\ ~LFINITE rs /\ ~LFINITE pqs
    /\ wf_pqs_inf pqs)
End

Theorem sol_seq_inf_sol_seq_LTAKE:
  !rs pqs k. sol_seq_inf rs pqs
  ==> sol_seq (THE (LTAKE k rs)) (THE (LTAKE k pqs))
Proof
  rw[sol_seq_inf_def,sol_seq_def,wf_pqs_inf_wf_pqs_LTAKE]
  >> `infin_or_leq pqs k T /\ infin_or_leq rs k T` by fs[infin_or_leq_def,wf_pqs_inf_def]
  >> drule_then assume_tac infin_or_leq_LENGTH_LTAKE_EQ
  >- fs[infin_or_leq_LENGTH_LTAKE_EQ]
  >> first_x_assum (qspec_then `i` mp_tac)
  >> rpt (dxrule_then assume_tac LNTH_EL_LTAKE)
  >> fs[]
QED

Theorem sol_seq_inf_is_const_or_type:
  !rs pqs i. sol_seq_inf rs pqs
  ==> is_const_or_type (FST (THE (LNTH i pqs))) /\ is_const_or_type (SND (THE (LNTH i pqs)))
Proof
  rpt gen_tac >> strip_tac
  >> `~LFINITE pqs` by fs[sol_seq_inf_def]
  >> dxrule_then (qspec_then `SUC i` assume_tac) sol_seq_inf_sol_seq_LTAKE
  >> drule_then (qspec_then `i` assume_tac) sol_seq_is_const_or_type
  >> qspecl_then [`SUC i`,`pqs`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> qspecl_then [`pqs`,`i`,`SUC i`] assume_tac LNTH_EL_LTAKE
  >> gs[less_opt_cases,infin_or_leq_def,GSYM NOT_LFINITE_LLENGTH_NONE]
QED

Theorem sol_seq_inf_LDROP:
  !rs pqs k. sol_seq_inf rs pqs
  ==> sol_seq_inf (THE (LDROP k rs)) (THE (LDROP k pqs))
Proof
  rw[sol_seq_inf_def,wf_pqs_inf_LDROP,NOT_LFINITE_LDROP]
  >> `infin_or_leq rs k T /\ infin_or_leq pqs k T` by fs[infin_or_leq_def,wf_pqs_inf_def]
  >> rpt (dxrule_then assume_tac LNTH_THE_DROP)
  >> fs[GSYM ADD]
QED

(* Lemma 5.13 for infinite case *)
Theorem leq_geq_monotone_composable_LTAKE[local]:
  !pqs rs k ctxt.
  monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ every (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq_inf rs pqs
  ==>
  has_mg_sol_leq (THE (LTAKE (SUC k) pqs)) (FST (THE (LNTH (SUC k) pqs))) \/
  has_mg_sol_geq (THE (LTAKE (SUC k) pqs)) (FST (THE (LNTH (SUC k) pqs)))
Proof
  rw[]
  >> qspecl_then [`THE (LTAKE (SUC (SUC k)) rs)`,`THE (LTAKE (SUC (SUC k)) pqs)`,`ctxt`] mp_tac (REWRITE_RULE[DISJ_EQ_IMP,AND_IMP_INTRO] leq_geq_monotone_composable)
  >> `infin_or_leq rs (SUC (SUC k)) T /\ ~LFINITE pqs /\ ~LFINITE rs` by fs[infin_or_leq_def,sol_seq_inf_def]
  >> dxrule_then strip_assume_tac infin_or_leq_LENGTH_LTAKE_EQ
  >> fs[LTAKE_FRONT_LNTH_LAST,sol_seq_inf_sol_seq_LTAKE,every_LTAKE_EVERY',DISJ_EQ_IMP]
QED

Theorem leq_geq_monotone_composable_LTAKE_LDROP[local]:
  !pqs rs k k' ctxt.
  monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ every (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq_inf rs pqs
  ==> has_mg_sol_leq (THE (LTAKE (SUC k') (THE (LDROP k pqs)))) (FST (THE (LNTH (SUC k') (THE (LDROP k pqs)))))
  \/ has_mg_sol_geq (THE (LTAKE (SUC k') (THE (LDROP k pqs)))) (FST (THE (LNTH (SUC k') (THE (LDROP k pqs)))))
Proof
  rw[]
  >> match_mp_tac leq_geq_monotone_composable_LTAKE
  >> rpt (goal_assum (first_assum o mp_then Any mp_tac))
  >> `~LFINITE pqs` by fs[sol_seq_inf_def]
  >> qexists_tac `THE (LDROP k rs)`
  >> fs[every_THE_LDROP,sol_seq_inf_LDROP]
QED

Theorem NOT_LFINITE_LNTH:
  !ll. ~LFINITE ll ==> !n. ?y. LNTH n ll = SOME y
Proof
  rw[]
  >> rename1`LNTH n _ = SOME _`
  >> drule_then (qspec_then `n+1` strip_assume_tac) NOT_LFINITE_TAKE
  >> drule LTAKE_LNTH_EL
  >> fs[]
QED

Theorem WOP_NOT_PRE_eq:
  ∀P. (∃n. P n) <=> ∃n. P n ∧ (0 < n ==> ~P (PRE n))
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM]
  >> conj_tac
  >- (
    rw[Once WOP_eq]
    >> goal_assum drule
    >> first_x_assum $ qspec_then `PRE n` mp_tac
    >> rw[]
  )
  >> rw[]
  >> goal_assum drule
QED

(* any extension of a mg_sol_seq with last step leq expansion
 * is equivalent to the shorter solution *)
Theorem mg_sol_seq_leq_SUC_equiv_ts_on:
  !pqs rs ctxt i.
  has_mg_sol_leq (TAKE i pqs) (FST (EL i pqs))
  /\ mg_sol_seq rs (TAKE i pqs)
  /\ LENGTH pqs = SUC i
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ wf_pqs pqs
  /\ monotone (dependency ctxt)
  ==>
  ?rs'. mg_sol_seq rs' pqs
    /\ !j. j < i ==> equiv_ts_on (EL j rs') (EL j rs) (FV (FST (EL j pqs)))
Proof
  rw[has_mg_sol_leq_def]
  >> `LENGTH rs' = i /\ LENGTH rs = i` by fs[mg_sol_seq_def,sol_seq_def,LENGTH_TAKE]
  >> rev_drule_then (drule_then assume_tac) mg_solution
  >> rev_dxrule mg_sol_ext_leq
  >> rfs[EL_TAKE,is_instance_LR_eq]
  >> rpt $ disch_then $ dxrule_at Any
  >> disch_then $ qspec_then `SND $ EL i pqs` mp_tac
  >> impl_tac
  >- (
    fs[wf_pqs_def,EVERY_TAKE,ELIM_UNCURRY,o_DEF,EVERY_MEM,IMP_CONJ_THM,FORALL_AND_THM]
    >> first_x_assum match_mp_tac
    >> fs[EL_MEM]
  )
  >> qmatch_goalsub_abbrev_tac `mg_sol_seq _ take_SUC`
  >> `take_SUC = pqs` by (
    CONV_TAC $ RHS_CONV $ ONCE_REWRITE_CONV $ single $ GSYM TAKE_LENGTH_ID
    >> asm_rewrite_tac[]
    >> fs[PAIR,Abbr`take_SUC`,ADD1,TAKE_SUM]
    >> dep_rewrite.DEP_REWRITE_TAC[TAKE1,EL_DROP]
    >> fs[NOT_NIL_EQ_LENGTH_NOT_0]
  )
  >> rw[]
  >> goal_assum drule
  >> rpt strip_tac
  >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1]
  >> fs[]
QED

(* unique extension of mg_sol_seq followed by leq,
 * up to equivalent type substitutions *)
Theorem mg_sol_seq_leq_equiv_ts_on:
  !pqs rs ctxt k.
  EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ wf_pqs pqs
  /\ 0 < LENGTH pqs /\ k <= LENGTH pqs
  /\ (∀i. k <= i /\ i < LENGTH pqs ==> has_mg_sol_leq (TAKE i pqs) (FST (EL i pqs)))
  /\ mg_sol_seq rs (TAKE k pqs)
  ==>
  ?rs'. mg_sol_seq rs' pqs
    /\ !i. i < k ==> equiv_ts_on (EL i rs') (EL i rs) (FV (FST (EL i pqs)))
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `mg_sol_seq rs _`
  >> qpat_x_assum `mg_sol_seq rs _` mp_tac
  >> qid_spec_tac `rs`
  >> qmatch_asmsub_rename_tac `k <= LENGTH pqs`
  >> Induct_on `LENGTH pqs - k`
  >- (
    rw[]
    >> rev_dxrule_all_then assume_tac LESS_EQUAL_ANTISYM
    >> VAR_EQ_TAC
    >> fs[TAKE_LENGTH_ID]
    >> goal_assum drule
    >> fs[equiv_ts_on_refl]
  )
  >> rw[]
  >> first_x_assum $ qspecl_then [`pqs`,`SUC k`] mp_tac
  >> qspec_then `TAKE (SUC k) pqs` mp_tac mg_sol_seq_leq_SUC_equiv_ts_on
  >> fs[LENGTH_TAKE,TAKE_TAKE,EL_TAKE]
  >> rpt $ disch_then $ drule_at Any
  >> impl_tac
  >- fs[wf_pqs_def,EVERY_TAKE]
  >> strip_tac
  >> disch_then $ drule_then strip_assume_tac
  >> goal_assum drule
  >> fs[AND_IMP_INTRO]
  >> rpt strip_tac
  >> match_mp_tac equiv_ts_on_trans
  >> ntac 2 $ first_x_assum $ irule_at Any
  >> fs[]
QED

Theorem mg_sol_seq_leq_equiv_ts_on':
  !pqs rs ctxt k.
  EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ wf_pqs pqs
  /\ 0 < LENGTH pqs /\ k <= LENGTH pqs
  /\ (∀i. k <= i /\ i < LENGTH pqs ==> has_mg_sol_leq (TAKE i pqs) (FST (EL i pqs)))
  /\ mg_sol_seq rs (TAKE k pqs)
  /\ 0 < k
  ==>
  ?rs'. mg_sol_seq rs' pqs
    /\ (!i. i < k ==> equiv_ts_on (EL i rs') (EL i rs) (FV (FST (EL i pqs))))
    /\ type_size_LR (LR_TYPE_SUBST (HD rs) (FST $ HD pqs))
     = type_size_LR (LR_TYPE_SUBST (HD rs') (FST $ HD pqs))
    /\ LENGTH (FV $ LR_TYPE_SUBST (HD rs) (FST $ HD pqs))
     = LENGTH (FV $ LR_TYPE_SUBST (HD rs') (FST $ HD pqs))
Proof
  rpt strip_tac
  >> drule_all_then strip_assume_tac mg_sol_seq_leq_equiv_ts_on
  >> ntac 2 $ goal_assum drule
  >> first_x_assum $ qspec_then `0` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[equiv_ts_on_FV]
  >> conj_asm1_tac
  >- (
    fs[wf_pqs_def,EVERY_MEM,ELIM_UNCURRY,IMP_CONJ_THM,FORALL_AND_THM]
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> fs[EL_MEM]
  )
  >> disch_then $ drule_then strip_assume_tac
  >> fs[var_renaming_type_size_LR,LR_TYPE_SUBST_type_preserving,var_renaming_FV_LENGTH]
QED

Theorem seq_k_asc_inf_seq_k_asc_inf_LDROP:
  !ctxt pqs rs. monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ sol_seq_inf rs pqs
  /\ every (UNCURRY (dependency ctxt)) pqs
  /\ (?k. seq_k_asc_inf k pqs)
    ==> ?k. seq_asc_inf (THE (LDROP k pqs))
Proof
  Ho_Rewrite.ONCE_REWRITE_TAC[WOP_NOT_PRE_eq]
  >> rpt strip_tac
  >> Ho_Rewrite.REWRITE_TAC[GSYM WOP_NOT_PRE_eq]
  >> qmatch_asmsub_rename_tac `0 < k`
  >> Cases_on `k`
  >- (qexists_tac `0` >> fs[seq_asc_inf_def])
  >> qmatch_asmsub_rename_tac `seq_k_asc_inf (SUC n) pqs`
  >> qabbrev_tac `k = SUC n`
  >> `0 < k` by fs[Abbr`k`]
  >> qpat_x_assum `Abbrev _` kall_tac
  >> gs[seq_asc_inf_def,seq_k_asc_inf_def,DISJ_EQ_IMP]
  >> qmatch_asmsub_rename_tac `PRE k < kk`
  >> `k = kk` by (
    Cases_on `k < kk`
    >- (first_x_assum $ drule_then assume_tac >> fs[])
    >> rfs[NOT_LESS,LESS_OR_EQ]
  )
  >> fs[] >> rveq
  >> drule_all_then (qspec_then `PRE k` mp_tac) leq_geq_monotone_composable_LTAKE
  >> dep_rewrite.DEP_ONCE_REWRITE_TAC[cj 1 $ REWRITE_RULE[EQ_IMP_THM] SUC_PRE]
  >> rw[]
  >> qpat_x_assum `~has_mg_sol_leq _ _` kall_tac
  >> qexists_tac `k`
  >> `wf_pqs [THE (LNTH k pqs)]` by (
    fs[wf_pqs_inf_def,wf_pqs_def]
    >> drule_then (qspec_then `k` strip_assume_tac) NOT_LFINITE_LNTH
    >> fs[ELIM_UNCURRY,every_LNTH]
    >> first_x_assum match_mp_tac
    >> goal_assum drule
  )
  >> rw[NOT_LFINITE_LDROP,wf_pqs_inf_LDROP,has_mg_sol_leq_def]
  >> fs[has_mg_sol_geq_def,is_instance_LR_eq]
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST s _ = FST pq`
  >> drule_then (qspecl_then [`FST pq`,`SND pq`,`s`] mp_tac) mg_sol_ext_geq
  >> rpt $ disch_then $ drule_at Any
  >> impl_tac
  >- (
    fs[Abbr`pq`]
    >> drule_then (qspec_then `k` strip_assume_tac) NOT_LFINITE_TAKE
    >> drule_all every_LTAKE_EVERY
    >> fs[]
  )
  >> rw[]
  >> `EVERY (UNCURRY (dependency ctxt)) (THE (LTAKE (k + i) pqs))` by (
    drule_then (qspec_then `k+i` strip_assume_tac) NOT_LFINITE_TAKE
    >> drule_all_then assume_tac every_LTAKE_EVERY
    >> fs[]
  )
  >> qmatch_asmsub_abbrev_tac `mg_sol_seq (rors' ++ _) ltake_suc_k`
  >> `ltake_suc_k = THE (LTAKE (SUC k) pqs)` by (
    unabbrev_all_tac
    >> match_mp_tac $ cj 1 $ REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] $ GSYM LTAKE_CONS
    >> fs[infin_or_leq_def]
  )
  >> VAR_EQ_TAC
  >> qpat_x_assum `_ = THE $ LTAKE _ _` kall_tac
  >> qspecl_then [`THE $ LTAKE (k + i) pqs`,`rors' ++ [[]]`,`ctxt`,`SUC k`] mp_tac mg_sol_seq_leq_equiv_ts_on
  >> impl_tac
  >- (
    drule_then (qspec_then `k+i` strip_assume_tac) NOT_LFINITE_TAKE
    >> drule_then (strip_assume_tac o GSYM) LTAKE_LENGTH
    >> asm_rewrite_tac[Once ADD_SYM]
    >> fs[]
    >> conj_tac
    >- (
      fs[wf_pqs_def,wf_pqs_inf_def,ELIM_UNCURRY,o_DEF]
      >> drule_all every_LTAKE_EVERY
      >> fs[]
    )
    >> conj_tac
    >- (
      rw[LESS_EQ_IFF_LESS_SUC]
      >> first_x_assum drule
      >> drule_all_then assume_tac LTAKE_LNTH_EL
      >> drule_then (qspec_then `i'` assume_tac) LTAKE_TAKE_LESS
      >> rfs[]
    )
    >> drule_then (qspec_then `SUC k` assume_tac) LTAKE_TAKE_LESS
    >> gs[]
  )
  >> strip_tac
  >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM,IMP_CONJ_THM] mg_sol_seq_def
  >> imp_res_tac mg_sol_seq_LENGTH
  >> qspecl_then [`i + k`,`pqs`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> qspecl_then [`k`,`pqs`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> qspecl_then [`SUC k`,`pqs`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> rfs[less_opt_cases,NOT_LFINITE_NO_LENGTH]
  >> dxrule_at Any id_sol_mg_sol_equiv'
  >> rpt $ disch_then $ drule_at Any
  >> disch_then $ qspec_then `k` mp_tac
  >> impl_tac
  >- (
    first_x_assum $ qspec_then `k` mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND2]
    >> gs[ADD1,equiv_ts_on_symm]
  )
  >> rw[GSYM DROP_LTAKE_EQ_LTAKE_LDROP]
  >> goal_assum drule
  >> drule_then assume_tac sol_seq_inf_is_const_or_type
  >> dep_rewrite.DEP_REWRITE_TAC[LNTH_THE_DROP,LAST_DROP,LR_TYPE_SUBST_type_preserving,LAST_EL]
  >> fs[DROP_NIL,NULL_EQ,infin_or_leq_def,FORALL_AND_THM,NOT_NIL_EQ_LENGTH_NOT_0,ADD1]
  >> conj_asm1_tac
  >- (
    drule_then (qspec_then `i+k` strip_assume_tac) NOT_LFINITE_TAKE
    >> drule_then (qspec_then `PRE $ i+k` mp_tac) sol_seq_inf_is_const_or_type
    >> drule_then (dep_rewrite.DEP_REWRITE_TAC o single) LTAKE_LNTH_EL
    >> fs[]
  )
  >> qspecl_then [`SUC $ i + k`,`pqs`] assume_tac less_opt_LENGTH_THE_LTAKE
  >> qspec_then `THE (LTAKE (SUC $ i + k) pqs)` mp_tac mg_sol_seq_leq_SUC_equiv_ts_on
  >> rfs[less_opt_cases,NOT_LFINITE_NO_LENGTH]
  >> drule_then (dep_rewrite.DEP_REWRITE_TAC o single) TAKE_LTAKE_EQ_LTAKE_LTAKE
  >> drule EL_LTAKE_LDROP_LNTH
  >> disch_then $ qspec_then `0` assume_tac o CONV_RULE (RESORT_FORALL_CONV rev)
  >> fs[wf_pqs_inf_wf_pqs_LTAKE]
  >> rpt $ disch_then $ drule_at Any
  >> impl_tac
  >- (
    drule_then (qspec_then `SUC $ i+k` strip_assume_tac) NOT_LFINITE_TAKE
    >> rev_drule_then drule every_LTAKE_EVERY
    >> fs[]
  )
  >> strip_tac
  >> fs[GSYM is_instance_LR_eq]
  >> drule_then assume_tac mg_sol_seq_LENGTH
  >> dxrule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM,IMP_CONJ_THM] mg_sol_seq_def
  >> dxrule_then (qspec_then `PRE $ i + k` mp_tac) $ cj 3 $ REWRITE_RULE[EQ_IMP_THM,IMP_CONJ_THM] sol_seq_def
  >> dep_rewrite.DEP_REWRITE_TAC $ single $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] SUC_PRE
  >> first_x_assum $ qspec_then `PRE $ i + k` assume_tac
  >> drule_then (qspec_then `PRE $ i + k` strip_assume_tac) NOT_LFINITE_LNTH
  >> imp_res_tac every_LNTH
  >> qpat_x_assum `!i. is_const_or_type (SND _)` $ qspec_then `PRE $ i+k` assume_tac
  >> gs[ELIM_UNCURRY]
  >> qpat_x_assum `monotone _` $ (dxrule_then assume_tac) o REWRITE_RULE[monotone_def,list_subset_set]
  >> dxrule_all equiv_ts_on_subset
  >> ONCE_REWRITE_TAC[equiv_ts_on_symm]
  >> dep_rewrite.DEP_REWRITE_TAC[equiv_ts_on_FV]
  >> asm_rewrite_tac[]
  >> rpt strip_tac
  >> fs[]
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose]
  >> fs[]
  >> irule_at Any EQ_REFL
QED

Theorem mg_sol_ext_geq_NOT_leq_measure:
  !rs pqs ctxt. mg_sol_seq rs (FRONT pqs)
    /\ wf_pqs pqs
    /\ monotone (dependency ctxt)
    /\ EVERY (UNCURRY (dependency ctxt)) pqs
    /\ has_mg_sol_geq (FRONT pqs) (FST (LAST pqs))
    /\ ~has_mg_sol_leq (FRONT pqs) (FST (LAST pqs))
    /\ 1 < LENGTH pqs
    ==> ?rs'. mg_sol_seq rs' pqs
      /\ sol_seq_measure (LR_TYPE_SUBST (HD rs) (FST $ EL 0 pqs)) (LR_TYPE_SUBST (HD rs') (FST $ HD pqs))
Proof
  rw[]
  >> dxrule has_mg_sol_geq_imp
  >> rpt $ disch_then $ drule_at Any
  >> dep_rewrite.DEP_REWRITE_TAC[EVERY_FRONT]
  >> conj_asm1_tac
  >- (fs[NULL_LENGTH] >> CCONTR_TAC >> fs[])
  >> rw[is_instance_LR_eq,Once EQ_SYM_EQ]
  >> fs[has_mg_sol_leq_def,DISJ_EQ_IMP]
  >> first_x_assum drule
  >> imp_res_tac mg_sol_seq_LENGTH
  >> impl_keep_tac
  >- (fs[LENGTH_FRONT] >> Cases_on `pqs` >> fs[])
  >> rw[]
  >> drule mg_sol_ext_geq_NOT_leq
  >> fs[]
  >> rpt $ disch_then $ drule_at Any
  >> qpat_x_assum `FST (LAST pqs) = _` $ assume_tac o GSYM
  >> fs[EVERY_FRONT]
  >> disch_then $ qspec_then `SND $ LAST pqs` mp_tac
  >> impl_tac
  >- (
    fs[LAST_EL,NULL_EQ,EVERY_MEM,ELIM_UNCURRY,wf_pqs_def,FORALL_AND_THM,IMP_CONJ_THM]
    >> ntac 2 $ first_x_assum $ irule_at Any
    >> fs[EL_MEM]
  )
  >> fs[APPEND_FRONT_LAST,NULL_EQ]
  >> ONCE_REWRITE_TAC[GSYM EL]
  >> dep_rewrite.DEP_REWRITE_TAC[EL_FRONT]
  >> rw[NULL_EQ]
  >> goal_assum drule
  >> ONCE_REWRITE_TAC[GSYM EL]
  >> dep_rewrite.DEP_REWRITE_TAC[EL_APPEND1]
  >> fs[EL_MAP]
QED

Theorem monotone_subsequence:
  !P. (!k:num. ?k':num. P k k')
  /\ (!k i. P k i ==> k < i)
  ==> ?g. P 0 (g 0) /\ 0 < g 0 /\
  !k. P (g k) (g (SUC k)) /\ (!j. j < g (SUC k) ==> ~P (g k) j)
Proof
  rpt strip_tac
  >> fs[Once WOP_eq]
  >> qabbrev_tac `Q = λk i. P k i /\ !j. j < i ==> ~P k j`
  >> `!i. ?k. Q i k` by (
    qunabbrev_tac `Q` >> fs[]
  )
  >> qpat_x_assum `!k. ?k'. _ /\ _` kall_tac
  >> qabbrev_tac `f = λi. @k. Q i k`
  >> qabbrev_tac `g = λi. FUNPOW f i (f 0)`
  >> `!i j k. Q k i /\ Q k j ==> i = j` by (
    rw[Abbr`Q`]
    >> first_x_assum $ qspec_then `i` assume_tac
    >> first_x_assum $ qspec_then `j` assume_tac
    >> CCONTR_TAC
    >> gs[LESS_OR_EQ,NOT_NUM_EQ]
  )
  >> `g 0 = @k. Q 0 k` by (
    map_every qunabbrev_tac [`g`,`f`]
    >> fs[FUNPOW]
  )
  >> `!i. g i < g (SUC i)` by (
    strip_tac
    >> fs[Abbr`g`,Abbr`f`]
    >> fs[FUNPOW_SUC]
    >> first_x_assum match_mp_tac
    >> ho_match_mp_tac SELECT_ELIM_THM
    >> fs[Abbr`Q`]
  )
  >> `!k. Q (g k) (g $ SUC k)` by (
    gen_tac
    >> qpat_x_assum `!k. ?k'. _` $ qspec_then `g k` mp_tac
    >> qspec_then `λk'. Q (g k) k'` mp_tac SELECT_THM
    >> fs[Abbr`f`,Abbr`g`,FUNPOW_SUC]
  )
  >> qexists_tac `g`
  >> ONCE_REWRITE_TAC[CONJ_ASSOC]
  >> conj_tac
  >- (
    asm_rewrite_tac[]
    >> first_x_assum $ irule_at Any
    >> ho_match_mp_tac SELECT_ELIM_THM
    >> fs[Abbr`Q`]
  )
  >> gen_tac
  >> fs[Abbr`Q`,FORALL_AND_THM,IMP_CONJ_THM]
QED

(* Lemma 5.16 *)
Theorem ascending_infinite_suffix:
  !rs pqs ctxt.
  monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ every (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq_inf rs pqs
  ==> ?k. seq_asc_inf (THE (LDROP k pqs))
Proof
  rw[]
  >> drule seq_k_asc_inf_seq_k_asc_inf_LDROP
  >> rpt $ disch_then drule
  >> disch_then match_mp_tac
  >> CCONTR_TAC
  >> qabbrev_tac `geq = λi.
    has_mg_sol_geq (THE (LTAKE i pqs)) (FST (THE (LNTH i pqs)))`
  >> qabbrev_tac `P = λk i. k < i
    /\ (!j. k < j /\ j < i ==> has_mg_sol_leq (THE (LTAKE j pqs)) (FST (THE (LNTH j pqs))))
    /\ ~has_mg_sol_leq (THE (LTAKE i pqs)) (FST (THE (LNTH i pqs)))`
  >> `~LFINITE rs /\ ~LFINITE pqs` by fs[sol_seq_inf_def]
  >> drule EL_LTAKE_LDROP_LNTH
  >> disch_then $ qspec_then `0` assume_tac o CONV_RULE (RESORT_FORALL_CONV rev)
  >> `!j. EVERY (UNCURRY (dependency ctxt)) $ THE $ LTAKE j pqs` by (
    strip_tac
    >> drule_then match_mp_tac every_LTAKE_EVERY
    >> drule_then (qspec_then `j` strip_assume_tac) NOT_LFINITE_TAKE
    >> fs[]
    >> goal_assum drule
  )
  >> fs[seq_asc_inf_def]
  >> `!k. ?k'. P k k'` by (
    rw[Abbr`P`]
    >> last_x_assum $ qspec_then `k` strip_assume_tac
    >> gs[seq_k_asc_inf_def,sol_seq_inf_def,Once WOP_eq]
    >> goal_assum drule
    >> fs[]
  )
  >> qpat_x_assum `!k. ~seq_k_asc_inf _ _` kall_tac
  >> `!k k'. P k k' ==> geq k'` by (
    rw[Abbr`P`,Abbr`geq`]
    >> rename[`k < kk`]
    >> drule $ REWRITE_RULE[DISJ_EQ_IMP,AND_IMP_INTRO] leq_geq_monotone_composable_LTAKE
    >> rpt $ disch_then $ drule_at Any
    >> disch_then $ qspec_then `PRE kk` mp_tac
    >> dep_rewrite.DEP_REWRITE_TAC $ single $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] SUC_PRE
    >> fs[]
  )
  >> drule monotone_subsequence
  >> impl_keep_tac >- fs[Abbr`P`]
  >> strip_tac
  >> qabbrev_tac `ρ = λj. @rs. mg_sol_seq rs (THE (LTAKE j pqs))`
  >> `!j. mg_sol_seq (ρ j) (THE (LTAKE j pqs))` by (
    rw[Abbr`ρ`]
    >> qspec_then `λrs. mg_sol_seq rs (THE (LTAKE j pqs))` mp_tac SELECT_THM
    >> fs[]
    >> disch_then kall_tac
    >> Cases_on `j = 0`
    >- (qexists_tac `[]` >> fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def])
    >> drule_then (qspec_then `j` assume_tac) sol_seq_inf_sol_seq_LTAKE
    >> dxrule_at Any mg_sol_exists
    >> rpt $ disch_then $ drule_at Any
    >> impl_tac
    >- (
      dep_rewrite.DEP_REWRITE_TAC[NOT_LFINITE_LENGTH]
      >> fs[]
    )
    >> strip_tac
    >> goal_assum drule
  )
  >> `!i.
    sol_seq_measure
    (LR_TYPE_SUBST (HD (ρ (g i))) (FST $ THE $ LHD pqs))
    (LR_TYPE_SUBST (HD (ρ (SUC $ g i))) (FST $ THE $ LHD pqs))
  ` by (
    gen_tac
    >> first_assum $ qspec_then `g i` assume_tac
    >> first_x_assum $ qspec_then `SUC $ g i` assume_tac
    >> drule mg_solution'
    >> imp_res_tac mg_sol_seq_LENGTH
    >> qspecl_then [`ρ $ g i`,`THE (LTAKE (SUC (g i)) pqs)`,`ctxt`] mp_tac mg_sol_ext_geq_NOT_leq_measure
    >> fs[LTAKE_FRONT_LNTH_LAST,NOT_LFINITE_LENGTH]
    >> impl_tac
    >- (
      conj_tac
      >- fs[sol_seq_inf_def,wf_pqs_inf_wf_pqs_LTAKE]
      >> Cases_on `i`
      >- (
        rpt strip_tac
        >- metis_tac[]
        >- metis_tac[]
        >> fs[IMP_CONJ_THM,FORALL_AND_THM]
      )
      >> first_assum $ qspec_then `n` assume_tac
      >> fs[IMP_CONJ_THM,FORALL_AND_THM]
      >> first_x_assum $ drule_then $ irule_at (Pos hd)
      >> `!i. 0 < g i` by (
        Induct
        >- fs[]
        >> match_mp_tac LESS_TRANS
        >> goal_assum drule
        >> fs[]
      )
      >> first_x_assum $ qspec_then `SUC n` mp_tac
      >> rw[]
      >> qpat_x_assum `P _ _` mp_tac
      >> qpat_x_assum `Abbrev (P = _)` mp_tac
      >> rpt $ pop_assum kall_tac
      >> rpt strip_tac
      >> fs[Abbr`P`]
    )
    >> strip_tac
    >> disch_then drule
    >> disch_then $ drule_at Any
    >> impl_tac
    >- (
      drule_then match_mp_tac every_LTAKE_EVERY
      >> qspecl_then [`pqs`,`SUC $ g i`] strip_assume_tac $
        Ho_Rewrite.REWRITE_RULE[PULL_FORALL] NOT_LFINITE_TAKE
      >> rfs[]
      >> goal_assum drule
    )
    >> strip_tac
    >> first_x_assum $ qspec_then `0` mp_tac
    >> ntac 3 $ first_x_assum $ qspec_then `i` assume_tac
    >> fs[LESS_TRANS]
    >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose,equal_ts_on_FV]
    >> conj_asm1_tac
    >- (
      fs[wf_pqs_inf_def,sol_seq_inf_def]
      >> qspecl_then [`pqs`,`0`] assume_tac $
        Ho_Rewrite.REWRITE_RULE[PULL_FORALL] NOT_LFINITE_LNTH
      >> rfs[]
      >> imp_res_tac every_LNTH
      >> fs[]
    )
    >> rw[LNTH]
    >> drule_then match_mp_tac var_renaming_sol_seq_measure'
    >> qspecl_then [`pqs`,`0`,`SUC $ g i`,`0`] mp_tac EL_LTAKE_LDROP_LNTH
    >> fs[LR_TYPE_SUBST_type_preserving,LNTH,LESS_TRANS]
    >> disch_then $ fs o single
  )
  >> `!i. type_size_LR (LR_TYPE_SUBST (HD (ρ (g $ SUC i))) (FST $ THE $ LHD pqs))
        = type_size_LR (LR_TYPE_SUBST (HD (ρ (SUC $ g i))) (FST $ THE $ LHD pqs))
      /\ LENGTH (FV $ LR_TYPE_SUBST (HD (ρ (g $ SUC i)))  (FST $ THE $ LHD pqs))
       = LENGTH (FV $ LR_TYPE_SUBST (HD (ρ (SUC $ g i)))  (FST $ THE $ LHD pqs))
  ` by (
    gen_tac
    >> `!i. 0 < g i` by (
      Induct
      >- fs[]
      >> match_mp_tac LESS_TRANS
      >> goal_assum drule
      >> fs[]
    )
    >> qpat_assum `!i. mg_sol_seq _ _` $ qspec_then `g $ SUC i` assume_tac
    >> qpat_x_assum `!i. mg_sol_seq _ _` $ qspec_then `SUC $ g i` assume_tac
    >> imp_res_tac mg_sol_seq_LENGTH
    >> qspecl_then [`THE $ LTAKE (g $ SUC i) pqs`,`ρ $ SUC $ g i`,`ctxt`,`SUC $ g i`] mp_tac mg_sol_seq_leq_equiv_ts_on'
    >> qspecl_then [`pqs`,`0`,`g $ SUC i`,`0`] mp_tac EL_LTAKE_LDROP_LNTH
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> fs[LESS_EQ,NOT_LFINITE_LENGTH,TAKE_LTAKE_EQ_LTAKE_LTAKE,LNTH]
    >> disch_then kall_tac
    >> impl_tac
    >- (
      conj_tac
      >- fs[sol_seq_inf_def,wf_pqs_inf_wf_pqs_LTAKE]
      >> metis_tac[]
    )
    >> strip_tac
    >> ntac 2 $ pop_assum $ fs o single
    >> drule_then rev_drule mg_solution'
    >> disch_then $ drule_at Any
    >> impl_tac
    >- (
      drule_then match_mp_tac every_LTAKE_EVERY
      >> qspecl_then [`pqs`,`g $ SUC i`] strip_assume_tac $
        Ho_Rewrite.REWRITE_RULE[PULL_FORALL] NOT_LFINITE_TAKE
      >> rfs[]
      >> goal_assum drule
    )
    >> strip_tac
    >> imp_res_tac mg_sol_seq_LENGTH
    >> first_x_assum $ qspec_then `0` mp_tac
    >> fs[LTAKE_FRONT_LNTH_LAST,NOT_LFINITE_LENGTH,LESS_EQ,LNTH]
    >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose]
    >> conj_asm1_tac
    >- (
      fs[wf_pqs_inf_def,sol_seq_inf_def]
      >> qspecl_then [`pqs`,`0`] assume_tac $
        Ho_Rewrite.REWRITE_RULE[PULL_FORALL] NOT_LFINITE_LNTH
      >> rfs[]
      >> imp_res_tac every_LNTH
      >> fs[LNTH]
    )
    >> fs[]
    >> drule $ ONCE_REWRITE_RULE[CONJ_COMM] var_renaming_type_size_LR
    >> disch_then $ dep_rewrite.DEP_REWRITE_TAC o single
    >> drule $ ONCE_REWRITE_RULE[CONJ_COMM] var_renaming_FV_LENGTH
    >> disch_then $ dep_rewrite.DEP_REWRITE_TAC o single
    >> fs[LR_TYPE_SUBST_type_preserving]
  )
  >> Cases_on `
    ?kk. !i. kk < i ==>
      type_size_LR (LR_TYPE_SUBST (HD (ρ (g i))) (FST (THE (LHD pqs))))
      = type_size_LR (LR_TYPE_SUBST (HD (ρ (SUC (g i)))) (FST (THE (LHD pqs))))
  `
  (* contradiction to finitely many type variables *)
  >- (
    fs[FORALL_AND_THM,IMP_CONJ_THM]
    >> `!i l. kk < i ==>
        LENGTH (FV (LR_TYPE_SUBST (HD (ρ (g $ i + l))) (FST (THE (LHD pqs))))) + l <=
        LENGTH (FV (LR_TYPE_SUBST (HD (ρ (g $ i))) (FST (THE (LHD pqs)))))
    ` by (
      gen_tac
      >> Induct
      >- (
        strip_tac
        >> first_x_assum drule
        >> qpat_x_assum `!i. sol_seq_measure _ _` $ qspec_then `i` mp_tac o REWRITE_RULE[sol_seq_measure_def]
        >> fs[]
      )
      >> strip_tac
      >> first_x_assum $ drule_then assume_tac
      >> match_mp_tac LESS_EQ_TRANS
      >> goal_assum $ dxrule_at Any
      >> REWRITE_TAC[Once ADD_COMM,GSYM SUC_ADD_SYM]
      >> REWRITE_TAC[GSYM LESS_EQ]
      >> qpat_assum `!i. sol_seq_measure _ _` $ qspec_then `i+l` mp_tac o REWRITE_RULE[sol_seq_measure_def]
      >> fs[]
      >> qpat_assum `!i. LENGTH _ = _` $ fs o single o GSYM
      >> strip_tac
      >> REWRITE_TAC[Once ADD_COMM,GSYM SUC_ADD_SYM]
      >> asm_rewrite_tac[]
    )
    >> first_x_assum $ qspec_then `SUC kk` mp_tac
    >> qmatch_goalsub_abbrev_tac `_ <= LENGTH b`
    >> disch_then $ qspec_then `SUC $ LENGTH b` mp_tac
    >> fs[]
  )
  >> qabbrev_tac `l = λi. type_size_LR (LR_TYPE_SUBST (HD (ρ (g i))) (FST (THE (LHD pqs))))`
  >> qabbrev_tac `r = λi. type_size_LR (LR_TYPE_SUBST (HD (ρ (SUC $ g i))) (FST (THE (LHD pqs))))`
  >> qabbrev_tac `Q = λk i. k < i /\ l i < r i /\ !i'. i' < i /\ k < i' ==> l i' = r i'`
  >> fs[Once WOP_eq]
  >> `!k. ?i. Q k i` by (
    rpt strip_tac
    >> first_x_assum $ qspec_then `k` strip_assume_tac
    >> qunabbrev_tac `Q`
    >> fs[AC CONJ_ASSOC CONJ_COMM]
    >> goal_assum drule
    >> rename[`k < i`]
    >> qpat_x_assum `!i. sol_seq_measure _ _` $ qspec_then `i` assume_tac o cj 1 o REWRITE_RULE[sol_seq_measure_def]
    >> map_every qunabbrev_tac [`r`,`l`]
    >> fs[]
  )
  >> qpat_x_assum `!x. ?y. _ /\ _` kall_tac
  >> qpat_x_assum `!i. sol_seq_measure _ _` kall_tac
  >> fs[FORALL_AND_THM,IMP_CONJ_THM]
  >> qpat_x_assum `!i. LENGTH _ = _` kall_tac
  >> drule monotone_subsequence
  >> impl_tac
  >- fs[Abbr`Q`]
  >> `!k i. Q k i ==> k < i /\ l i < r i /\ !i'. k < i' /\ i' < i ==> r i' = l i'` by fs[Abbr`Q`]
  >> strip_tac
  >> fs[FORALL_AND_THM,IMP_CONJ_THM]
  >> `!i. 0 < g' i` by (
    Induct
    >- fs[]
    >> match_mp_tac LESS_TRANS
    >> goal_assum drule
    >> fs[]
  )
  >> `!i j. l (g' $ SUC i) + j <= l (g' $ SUC i + j)` by (
    gen_tac
    >> Induct >- fs[]
    >> match_mp_tac LESS_EQ_TRANS
    >> qmatch_assum_abbrev_tac `_ <= b:num`
    >> qexists_tac `SUC b`
    >> fs[Abbr`b`,GSYM LESS_EQ]
    >> match_mp_tac LESS_LESS_EQ_TRANS
    >> first_x_assum $ irule_at $ Pos hd
    >> ONCE_REWRITE_TAC[ADD_COMM]
    >> qexists_tac `g' $ i + j`
    >> fs[GSYM SUC_ADD_SYM]
    >> qpat_x_assum `!k. Q _ _` $ qspec_then `SUC(i+j)` assume_tac
    >> qpat_x_assum `!k i. _ ==> _` $ drule_then mp_tac
    >> qpat_x_assum `!k i. _ ==> _` $ dxrule_then mp_tac
    >> qpat_x_assum `!i. l _ = r _` $ Ho_Rewrite.REWRITE_TAC o single o GSYM
    >> rpt $ pop_assum kall_tac
    (* SUB_LESS_0 *)
    >> qmatch_goalsub_rename_tac `a < b`
    >> Induct_on `b - a`
    >> fs[AND_IMP_INTRO]
    >> rw[]
    >> dxrule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM,Once LESS_OR_EQ] LESS_EQ
    >> fs[]
    >> match_mp_tac LESS_EQ_TRANS
    >> first_x_assum $ irule_at (Pos $ el 2)
    >> goal_assum $ drule_at Any
    >> fs[]
  )
  >> rpt (PRED_ASSUM (exists (curry op = "Q")
    o map (fst o dest_var) o find_terms is_var) kall_tac)
  >> qabbrev_tac `κ = type_size_LR (LR_TYPE_SUBST (THE (LHD rs)) (FST $ THE $ LHD pqs))`
  >> first_x_assum $ qspecl_then [`0`,`SUC κ`] mp_tac
  >> qunabbrev_tac `l`
  >> fs[NOT_LESS_EQUAL]
  >> qmatch_goalsub_abbrev_tac `type_size_LR (LR_TYPE_SUBST (HD (ρ $ g index)) _) < _`
  >> drule_then (qspec_then `g index` assume_tac) sol_seq_inf_sol_seq_LTAKE
  >> qpat_x_assum `!i. mg_sol_seq _ _` $ qspec_then `g index` assume_tac
  >> imp_res_tac mg_sol_seq_LENGTH
  >> drule_then (drule_then strip_assume_tac) $
    cj 2 $ REWRITE_RULE[FORALL_AND_THM,IMP_CONJ_THM,EQ_IMP_THM] mg_sol_seq_def
  >> first_x_assum $ qspec_then `0` mp_tac
  >> `!i. 0 < g i` by (
    Induct
    >- fs[]
    >> match_mp_tac LESS_TRANS
    >> goal_assum drule
    >> fs[]
  )
  >> impl_keep_tac
  >- fs[NOT_LFINITE_LENGTH]
  >> dep_rewrite.DEP_REWRITE_TAC[equal_ts_on_FV,LR_TYPE_SUBST_type_preserving,GSYM LR_TYPE_SUBST_compose]
  >> fs[LNTH]
  >> conj_asm1_tac
  >- (
    fs[wf_pqs_inf_def,sol_seq_inf_def]
    >> qspecl_then [`pqs`,`0`] assume_tac $
      Ho_Rewrite.REWRITE_RULE[PULL_FORALL] NOT_LFINITE_LNTH
    >> rfs[]
    >> imp_res_tac every_LNTH
    >> fs[LNTH]
  )
  >> REWRITE_TAC[GSYM EL]
  >> qspecl_then [`rs`,`0`] (mp_tac o CONV_RULE SWAP_FORALL_CONV) EL_LTAKE_LDROP_LNTH
  >> disch_then $ qspec_then `0` mp_tac
  >> fs[]
  >> disch_then kall_tac
  >> qunabbrev_tac `κ`
  >> fs[LNTH]
  >> disch_then $ REWRITE_TAC o single o GSYM
  >> qmatch_goalsub_abbrev_tac `type_size_LR b < _`
  >> match_mp_tac LESS_EQ_LESS_TRANS
  >> qexists_tac `type_size_LR $ LR_TYPE_SUBST (HD es) b`
  >> qunabbrev_tac `b`
  >> dep_rewrite.DEP_REWRITE_TAC[type_size_LR_TYPE_SUBST,LR_TYPE_SUBST_type_preserving]
  >> fs[]
QED

Theorem dependency_subst_clos_LR_TYPE_SUBST:
  !a b rho ctxt. is_const_or_type a /\ is_const_or_type b
  /\ dependency ctxt a b
  ==> subst_clos (dependency ctxt) (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
Proof
  rw[is_const_or_type_eq]
  >> fs[is_const_or_type_eq,subst_clos_def,LR_TYPE_SUBST_cases]
  >> goal_assum $ drule_at Any
  >> fs[INST_CORE_def,INST_def]
  >> rpt $ irule_at Any EQ_REFL
QED

Theorem list_max_mono_last:
  !ls. ~NULL ls /\ (!i j. EL i ls <= EL (SUC i) ls)
  ==> list_max ls = LAST ls
Proof
  Induct >> fs[]
  >> Cases_on `ls` >- rw[list_max_def]
  >> rpt strip_tac
  >> qpat_x_assum `_ ==> _` mp_tac
  >> impl_tac
  >- (rw[] >> first_x_assum $ qspec_then `SUC i` mp_tac >> fs[])
  >> first_x_assum $ qspec_then `0` mp_tac
  >> rw[]
  >> `h <= list_max (h::t)` by fs[list_max_def]
  >> ONCE_REWRITE_TAC[list_max_def]
  >> rw[]
QED

Theorem llist_mono_leq:
  !ll.
  (!i. less_opt (SUC i) (LLENGTH ll) ==> (THE (LNTH i ll)):num <= THE $ LNTH (SUC i) ll)
  <=> (!i j. i < j /\ less_opt j (LLENGTH ll) ==> THE (LNTH i ll) <= THE $ LNTH j ll)
Proof
  fs[EQ_IMP_THM]
  >> ntac 3 strip_tac
  >> Induct >> rw[]
  >> dxrule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM,Once LESS_OR_EQ] LESS_EQ
  >> fs[]
  >> irule LESS_EQ_TRANS
  >> ntac 3 $ first_x_assum $ irule_at Any
  >> fs[less_opt_cases]
QED

Theorem finite_repeats:
  !s ll. ~LFINITE ll
  /\ FINITE s
  /\ every s ll
  ==> ?k. !i. k < i ==> ?n. i < n /\ LNTH i ll = LNTH n ll
Proof
  rpt strip_tac >>
  qspec_then `ll` assume_tac fromList_fromSeq >>
  gvs[LFINITE_fromList] >>
  qexists_tac `LEAST k.
     ∀x. x ∈ s ∧ FINITE {i | f i = x} ⇒
         MAX_SET {i | f i = x} < k` >>
  strip_tac >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac
  >- (qexists_tac `SUC(MAX_SET{i | FINITE {i' | f i' = f i}})` >>
      rw[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
      match_mp_tac SUBSET_MAX_SET >>
      rw[SUBSET_DEF] >>
      match_mp_tac (MP_CANON SUBSET_FINITE) >>
      qexists_tac `BIGUNION(IMAGE (λx. if FINITE {i | f i = x} then {i | f i = x} else {}) s)` >>
      conj_tac >- (simp[FINITE_BIGUNION_EQ] >> rw[] >> rw[]) >>
      rw[SUBSET_DEF,PULL_EXISTS] >>
      qexists_tac `f x'` >> rw[] >>
      gvs[IN_DEF]) >>
  rw[] >>
  `INFINITE {n | f n = f i}`
    by(spose_not_then strip_assume_tac >>
       first_assum(qspec_then `f i` mp_tac) >>
       impl_tac >- (simp[IN_DEF,arithmeticTheory.NOT_LESS]) >>
       strip_tac >>
       drule in_max_set >>
       disch_then(qspec_then `i` mp_tac) >>
       impl_tac >- simp[] >>
       strip_tac >>
       DECIDE_TAC) >>
  drule IN_INFINITE_NOT_FINITE >>
  disch_then(qspec_then `count(SUC i)` mp_tac) >>
  simp[GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >>
  simp[arithmeticTheory.NOT_LESS_EQUAL] >>
  metis_tac[]
QED

Theorem dependency_props:
  dependency ctxt p q ==>
  is_const_or_type p /\ is_const_or_type q /\
  (ISR p ==> welltyped $ OUTR p) /\ (ISR q ==> welltyped $ OUTR q)
Proof
  rw[dependency_cases,is_const_or_type_eq]
  >> imp_res_tac allCInsts_is_Const
  >> fs[welltyped_def]
  >> irule_at Any $ cj 2 has_type_rules
QED

Theorem dependency_props':
  !p q. subst_clos (dependency ctxt) p q ==>
  is_const_or_type p /\ is_const_or_type q /\
  (ISR p ==> welltyped $ OUTR p) /\ (ISR q ==> welltyped $ OUTR q)
Proof
  ntac 2 Cases
  >> rw[subst_clos_def]
  >> imp_res_tac dependency_props
  >> fs[LR_TYPE_SUBST_type_preserving,INST_def,INST_CORE_def]
  >> rw[is_const_or_type_eq]
  >> gvs[is_const_or_type_eq,INST_def,INST_CORE_def]
QED

Theorem dependency_subst_clos_LR_TYPE_SUBST':
  !a b rho ctxt. subst_clos (dependency ctxt) a b
  ==> subst_clos (dependency ctxt) (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
Proof
  ntac 2 Cases
  >> rw[subst_clos_def,LR_TYPE_SUBST_cases]
  >> imp_res_tac dependency_props
  >> gvs[is_const_or_type_eq,TYPE_SUBST_compose,INST_def,INST_CORE_def,LR_TYPE_SUBST_cases,subst_clos_def]
  >> goal_assum $ drule_at Any
  >> fs[INST_CORE_def,INST_def]
  >> rpt $ irule_at Any EQ_REFL
QED

Theorem dependency_TC_subst_clos_LR_TYPE_SUBST:
  !rho ctxt a b. TC (subst_clos (dependency ctxt)) a b
  ==> TC (subst_clos (dependency ctxt)) (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
Proof
  ntac 2 gen_tac
  >> ho_match_mp_tac TC_INDUCT
  >> conj_tac >- fs[dependency_subst_clos_LR_TYPE_SUBST',TC_SUBSET]
  >> rpt strip_tac
  >> irule $ REWRITE_RULE[transitive_def]TC_TRANSITIVE
  >> rpt $ goal_assum drule
QED

(* Lemma 5.17 *)
Theorem cyclic_eq_not_terminating:
  !ctxt. monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ FINITE $ UNCURRY (dependency ctxt)
  ==>
  (~ (terminating $ TC $ subst_clos (dependency ctxt)) <=> cyclic_dep ctxt)
Proof
  rw[EQ_IMP_THM]
  >- (
    dxrule_then assume_tac $ ONCE_REWRITE_RULE[MONO_NOT_EQ] terminating_TC
    >> `?rs pqs. sol_seq_inf rs pqs /\ every (UNCURRY (dependency ctxt)) pqs
      /\ !i. ?n. i < n /\ LNTH i pqs = LNTH n pqs
    ` by (
      `?rs pqs. sol_seq_inf rs pqs /\ every (UNCURRY (dependency ctxt)) pqs` by (
        fs[prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def,terminating_def]
        >> qabbrev_tac `Q = λ(rs,pq) n.  dependency ctxt (FST pq) (SND pq)
            /\ LR_TYPE_SUBST rs (FST pq) = f n /\ LR_TYPE_SUBST rs (SND pq) = f $ SUC n
            /\ is_const_or_type (FST pq) /\ is_const_or_type (SND pq)`
        >> `!n. ?rspq. Q rspq n` by (
          rw[Abbr`Q`,EXISTS_PROD]
          >> rename[`SUC n`]
          >> first_x_assum $ qspec_then `n` assume_tac
          >> imp_res_tac dependency_props'
          >> gvs[is_const_or_type_eq,subst_clos_def]
          >> imp_res_tac dependency_props
          >> gvs[LR_TYPE_SUBST_cases,INST_def,INST_CORE_def,is_const_or_type_eq]
          >> goal_assum $ drule_at Any
          >> fs[LR_TYPE_SUBST_cases]
          >> rpt $ irule_at Any EQ_REFL
        )
        >> `!n. Q (@rspq. Q rspq n) n` by metis_tac[]
        >> qpat_x_assum `!n. ?rspq. _` kall_tac
        >> `!n pq rs. Q (@rspq. Q rspq n) n ==> pq = SND (@rspq. Q rspq n)
            ==> rs = FST (@rspq. Q rspq n) ==> dependency ctxt (FST pq) (SND pq)
            /\ LR_TYPE_SUBST rs (FST pq) = f n /\ LR_TYPE_SUBST rs (SND pq) = f $ SUC n
            /\ is_const_or_type (FST pq) /\ is_const_or_type (SND pq)` by (
            gvs[FORALL_AND_THM,IMP_CONJ_THM,AND_IMP_INTRO,ELIM_UNCURRY]
            >> rpt conj_tac
            >> gen_tac
            >> rename[`n:num`]
            >> first_x_assum $ qspec_then `n` mp_tac
            >> fs[Abbr`Q`,ELIM_UNCURRY]
        )
        >> qexists_tac `LMAP (λn. FST $ @rspq. Q rspq n) (LGENLIST I NONE)`
        >> qexists_tac `LMAP (λn. SND $ @rspq. Q rspq n) (LGENLIST I NONE)`
        >> conj_tac
        >- (
          rw[sol_seq_inf_def,LNTH_LMAP,LGENLIST_num,wf_pqs_inf_def,every_LNTH,LNTH_LMAP]
          >- (
            qmatch_goalsub_abbrev_tac `SUC _`
            >> rename[`SUC n:num`]
            >> first_assum $ qspec_then `n` mp_tac
            >> first_x_assum $ qspec_then `SUC n` mp_tac >> fs[]
          )
          >> fs[FORALL_AND_THM,AND_IMP_INTRO]
        )
        >> fs[every_LNTH,LNTH_LMAP,LGENLIST_num,ELIM_UNCURRY]
      )
      >> drule_at Any finite_repeats
      >> impl_keep_tac
      >- fs[sol_seq_inf_def]
      >> strip_tac
      >> drule_then (qspec_then `SUC k` assume_tac) sol_seq_inf_LDROP
      >> goal_assum drule
      >> drule_at_then Any (irule_at Any) every_THE_LDROP >> rw[]
      >> first_x_assum $ qspec_then `i+SUC k` strip_assume_tac >> fs[]
      >> qexists_tac `n - SUC k`
      >> dep_rewrite.DEP_REWRITE_TAC[LNTH_THE_DROP]
      >> fs[infin_or_leq_def]
    )
    >> drule_all_then strip_assume_tac ascending_infinite_suffix
    >> rename[`LDROP k`]
    >> first_x_assum $ qspec_then `k` strip_assume_tac
    >> rename[`k < n`]
    >> qabbrev_tac `l = n - k`
    >> `0 < l` by fs[Abbr`l`]
    >> drule_then (qspec_then `SUC l` assume_tac) seq_asc_inf_seq_asc_LTAKE
    >> qmatch_assum_abbrev_tac `seq_asc pqs'`
    >> qspecl_then [`pqs'`,`ctxt`,`PRE $ LENGTH pqs'`] mp_tac seq_asc_mg_sol_path
    >> `~LFINITE pqs /\ LENGTH pqs' = SUC l` by
      fs[sol_seq_inf_def,Abbr`pqs'`,NOT_LFINITE_LENGTH,NOT_LFINITE_LDROP]
    >> `!k'. EVERY (UNCURRY $ dependency ctxt) (THE (LTAKE k' (THE $ LDROP k pqs)))` by (
      strip_tac
      >> irule every_LTAKE_EVERY
      >> irule_at Any every_THE_LDROP
      >> goal_assum $ drule_at Any
      >> drule_then (qspec_then `k` assume_tac) NOT_LFINITE_LDROP
      >> drule_then (qspec_then `k'` strip_assume_tac) NOT_LFINITE_TAKE
      >> fs[]
      >> goal_assum drule
    )
    >> impl_keep_tac >> fs[Abbr`pqs'`]
    >> dep_rewrite.DEP_REWRITE_TAC[NOT_LFINITE_LENGTH,NOT_LFINITE_LDROP,TAKE_LTAKE_EQ_LTAKE_LTAKE]
    >> rw[cyclic_dep_def]
    >> imp_res_tac mg_sol_seq_LENGTH
    >> `LENGTH rs' = l` by fs[NOT_LFINITE_LENGTH,NOT_LFINITE_LDROP]
    >> qmatch_assum_abbrev_tac `seq_asc pqs'`
    >> goal_assum drule
    >> REWRITE_TAC[GSYM EL]
    >> dep_rewrite.DEP_REWRITE_TAC[EL_TAKE,GSYM LAST_EL]
    >> rw[NOT_LFINITE_LENGTH,NOT_LFINITE_LDROP,NOT_NIL_EQ_LENGTH_NOT_0]
    >> match_mp_tac has_mg_sol_leq_imp
    >> rpt $ goal_assum $ drule_at Any
    >> fs[seq_asc_def]
    >> first_x_assum drule_all
    >> qabbrev_tac `l = LENGTH pqs'`
    >> qunabbrev_tac `pqs'`
    >> fs[]
    >> REWRITE_TAC[GSYM EL]
    >> dep_rewrite.DEP_REWRITE_TAC[TAKE_LTAKE_EQ_LTAKE_LTAKE,EL_LTAKE_LDROP_LNTH]
    >> gvs[NOT_LFINITE_LDROP]
    >> qpat_x_assum `_ - _ = LENGTH _` $ fs o single o GSYM
  )
  >> fs[cyclic_dep_def,is_instance_LR_eq,path_starting_at_def]
  >> qhdtm_x_assum `equiv_ts_on` mp_tac
  >> dep_rewrite.DEP_REWRITE_TAC[equiv_ts_on_FV,LR_TYPE_SUBST_NIL]
  >> qhdtm_x_assum `wf_pqs` $ assume_tac o REWRITE_RULE[wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
  >> fs[FORALL_AND_THM,IMP_CONJ_THM]
  >> strip_tac
  >> rename[`var_renaming e`]
  >> dxrule_then (qspec_then `e` assume_tac) sol_seq_TYPE_SUBST
  >> qmatch_assum_abbrev_tac `sol_seq rs' _`
  >> qpat_x_assum `FST _ = LR_TYPE_SUBST _ _` mp_tac
  >> fs[LR_TYPE_SUBST_compose]
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST rs'0`
  >> `rs'0 = HD rs'` by (fs[Abbr`rs'0`,Abbr`rs'`] >> REWRITE_TAC[GSYM EL] >> fs[EL_MAP])
  >> qpat_x_assum `Abbrev (rs'0 = _)` kall_tac
  >> VAR_EQ_TAC
  >> `!x y. x = y ==> LR_TYPE_SUBST e x = LR_TYPE_SUBST e y` by rw[]
  >> pop_assum $ dxrule_then mp_tac
  >> imp_res_tac sol_seq_LENGTH
  >> dep_rewrite.DEP_REWRITE_TAC[LR_TYPE_SUBST_compose]
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST s' _ = LR_TYPE_SUBST rs'n _`
  >> `rs'n = EL (PRE $ LENGTH pqs) rs'` by (fs[Abbr`rs'n`,Abbr`rs'`,EL_MAP])
  >> qpat_x_assum `Abbrev (rs'n = _)` kall_tac
  >> VAR_EQ_TAC
  >> first_assum $ irule_at Any
  >> rw[EL_MEM]
  >> ntac 2 $ qhdtm_x_assum `Abbrev` kall_tac
  >> `(TC $ subst_clos (dependency ctxt)) (FST $ HD pqs) (LR_TYPE_SUBST s' (FST (HD pqs)))` by (
    `!i. i < LENGTH pqs ==>
      (TC $ subst_clos (dependency ctxt))
        (LR_TYPE_SUBST (EL i rs') (FST $ EL i pqs))
        (LR_TYPE_SUBST (EL i rs') (SND $ EL i pqs))` by (
      rpt strip_tac
      >> match_mp_tac TC_SUBSET
      >> rpt $ qpat_x_assum `is_const_or_type _` kall_tac
      >> fs[path_starting_at_def,EVERY_MEM,ELIM_UNCURRY,wf_pqs_def]
      >> drule_then assume_tac EL_MEM
      >> ntac 3 $ first_x_assum $ drule_then strip_assume_tac
      >> fs[is_const_or_type_eq,subst_clos_def,LR_TYPE_SUBST_cases]
      >> rfs[]
      >> goal_assum $ drule_at Any
      >> fs[INST_CORE_def,INST_def]
      >> rpt $ irule_at Any EQ_REFL
    )
    >> qpat_x_assum `LR_TYPE_SUBST s' _ = LR_TYPE_SUBST _ _` $ REWRITE_TAC o single
    >> qhdtm_x_assum `FST` $ ONCE_REWRITE_TAC o single
    >> drule $ cj 3 $ Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,IMP_CONJ_THM,FORALL_AND_THM] sol_seq_def
    >> dxrule $ cj 1 $ Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,IMP_CONJ_THM,FORALL_AND_THM] sol_seq_def
    >> qpat_x_assum `0n < _` mp_tac
    >> qpat_x_assum `!i. _ ==> TC _ _ _` mp_tac
    >> qhdtm_x_assum `EVERY` mp_tac
    >> asm_rewrite_tac[]
    >> POP_ASSUM_LIST $ map_every kall_tac
    >> Induct_on `LENGTH pqs`
    >> rw[]
    >> rename[`SUC v`]
    >> Cases_on `v` >> fs[]
    >- (
      match_mp_tac TC_SUBSET
      >> `0 < LENGTH pqs` by fs[]
      >> dxrule_then assume_tac EL_MEM
      >> fs[EVERY_MEM,ELIM_UNCURRY,wf_pqs_def]
      >> ntac 2 $ first_x_assum $ drule_then assume_tac
      >> fs[is_const_or_type_eq,subst_clos_def,LR_TYPE_SUBST_cases]
      >> rfs[]
      >> goal_assum $ drule_at Any
      >> fs[INST_CORE_def,INST_def]
      >> rpt $ irule_at Any EQ_REFL
    )
    >> first_x_assum $ qspec_then `FRONT pqs` mp_tac
    >> REWRITE_TAC[AND_IMP_INTRO]
    >> dep_rewrite.DEP_REWRITE_TAC[FRONT_TAKE_PRE]
    >> conj_asm1_tac >- (CCONTR_TAC >> fs[NULL_EQ])
    >> impl_tac
    >- (
      fs[EVERY_TAKE,wf_pqs_def]
      >> rpt strip_tac
      >> dep_rewrite.DEP_REWRITE_TAC[EL_TAKE]
      >> rpt $ first_assum $ irule_at Any
      >> fs[]
    )
    >> qhdtm_x_assum `SUC` $ assume_tac o GSYM >> fs[]
    >> REWRITE_TAC[GSYM EL]
    >> fs[EL_TAKE,SUC_PRE]
    >> strip_tac >> match_mp_tac $ cj 2 TC_RULES >> goal_assum dxrule
    >> fs[]
  )
  >> fs[prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def,terminating_def]
  >> map_every (fn x => qhdtm_x_assum x kall_tac) [`FST`,`LR_TYPE_SUBST`]
  >> qexists_tac `λn. FUNPOW (LR_TYPE_SUBST s') n (FST $ HD pqs)`
  >> Induct >> fs[FUNPOW_SUC,dependency_TC_subst_clos_LR_TYPE_SUBST]
QED

(* Definition 6.1 *)
Definition LR_orth_def:
  (LR_orth (INL p) (INL q) = orth_ty p q)
  /\ (LR_orth (INR (Const c ty1)) (INR (Const d ty2)) = orth_ci (Const c ty1) (Const d ty2))
  /\ (LR_orth _ _ = T)
End

Theorem LR_orth_SYM:
  !p q. LR_orth p q = LR_orth q p
Proof
  fs[FORALL_SUM,LR_orth_def,orth_ty_symm,orth_ci_def]
  >> rpt (conj_tac >> TRY Cases) >> TRY Cases
  >> fs[LR_orth_def,orth_ty_symm,orth_ci_def]
  >> fs[EQ_SYM_EQ,orth_ty_symm]
QED

Theorem LR_orth_simp:
  (!a b. LR_orth (INR a) (INL b) = T)
  /\ !a b. LR_orth (INL a) (INR b) = T
Proof
  fs[LR_orth_def] >> Cases >> fs[LR_orth_def]
QED

Theorem has_type_distinct:
  tm has_type ty ∧
  tm' has_type ty' ∧
  ty ≠ ty' ⇒
  tm ≠ tm'
Proof
  rpt strip_tac >> imp_res_tac WELLTYPED_LEMMA >> rveq >> fs[]
QED

Theorem orth_ctxt_orth_dependency_INR:
  !ctxt p q p' q' c c' tm tm' ov ov' cl cl' prop prop'.
    extends_init ctxt /\ orth_ctxt ctxt
    /\ dependency ctxt (INR p) q
    /\ dependency ctxt (INR p') q'
    /\ p = Const c (typeof tm)
    /\ p' = Const c' (typeof tm')
    /\ MEM (ConstSpec ov cl prop) ctxt
    /\ MEM (ConstSpec ov' cl' prop') ctxt
    /\ MEM (c,tm) cl /\ MEM (c',tm') cl'
    /\ (c,tm) <> (c',tm')
    /\ p <> p' /\ q <> q'
    ==> LR_orth (INR p) (INR p')
Proof
  rw[dependency_cases]
  >> rw[LR_orth_def,DISJ_EQ_IMP,orth_ci_def]
  >> drule (cj 1 (Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM] orth_ctxt_def)
    |> Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] |> cj 1)
  >> fs[orth_ci_def]
  >> TRY(rpt (disch_then dxrule)
         >> fs[]
         >> drule_at (Pos last) has_type_distinct
         >> rpt(disch_then drule)
         >> strip_tac >> simp[]
         >> imp_res_tac WELLTYPED_LEMMA
         >> rveq >> fs[orth_ty_symm] >> NO_TAC)
QED

Theorem TypeDefn_NewType_name_distinct:
  MEM (TypeDefn name pred abs rep) ctxt ∧
  MEM (NewType name' arity) ctxt ∧
  extends_init ctxt ⇒
  name ≠ name'
Proof
  rpt strip_tac >>
  fs[extends_init_def] >>
  dxrule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  rveq >>
  gs[MEM_SPLIT] >> rveq >>
  gs[APPEND_EQ_APPEND] >> rveq >> gs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> gs[] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  drule_then strip_assume_tac extends_APPEND_NIL >>
  fs[] >>
  imp_res_tac extends_NIL_CONS_updates >> fs[updates_cases]
QED

Theorem tyapp_distinct_orth:
  name ≠ name' ⇒
  Tyapp name tys # Tyapp name' tys'
Proof
  rw[orth_ty_def] >>
  Cases_on ‘ty’ >> rw[] >>
  spose_not_then strip_assume_tac >> fs[]
QED

Theorem GENLIST_ARG_EQ:
  ∀f n n'.
    GENLIST f n = GENLIST f n' ⇔ n = n'
Proof
  strip_tac >> Induct_on ‘n’ >> Cases >> rw[GENLIST] >> rw[EQ_IMP_THM]
QED

Theorem orth_ctxt_orth_dependency_INL:
  !ctxt p q p' q'. extends_init ctxt /\ orth_ctxt ctxt
    /\ dependency ctxt (INL p) q
    /\ dependency ctxt (INL p') q'
    /\ p <> p' /\ q <> q'
    ==> LR_orth (INL p) (INL p')
Proof
  rw[dependency_cases]
  >> rw[LR_orth_def,DISJ_EQ_IMP,orth_ci_def]
  >> drule (cj 1 (Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM] orth_ctxt_def)
    |> Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] |> cj 2)
  >> fs[orth_ci_def]
  >> TRY(rpt (disch_then dxrule) >> fs[orth_ty_symm] >>
         (impl_tac >- (spose_not_then strip_assume_tac >> gs[]) >>
          fs[orth_ty_symm]) >>
         NO_TAC)
  >> TRY(drule TypeDefn_NewType_name_distinct >> disch_then drule >> rpt(disch_then drule) >>
         gs[tyapp_distinct_orth] >> NO_TAC)
  >> TRY(gs[tyapp_distinct_orth] >> NO_TAC)
  >> TRY(disch_then kall_tac >>
         qpat_x_assum ‘MAP _ _ ≠ MAP _ _’ mp_tac >>
         dep_rewrite.DEP_ONCE_REWRITE_TAC[INJ_MAP_EQ_IFF] >>
         conj_tac >- rw[INJ_DEF] >>
         rw[GENLIST_ARG_EQ] >>
         rw[orth_ty_def] >> Cases_on ‘ty’ >> rw[] >>
         spose_not_then strip_assume_tac >> gs[] >> rveq >>
         gs[MAP_EQ_EVERY2])
QED

(* Algorithm 1, Kunčar 2015 *)
(* acyclicity check of transitive closure of a dependency relation *)
Definition is_acyclic_def:
  is_acyclic dep =
    ((!nx ny tx ty. MEM (INR (Const nx tx),INR (Const ny ty)) dep
     ==> ~is_instance tx ty)
    /\ (!tx ty. MEM (INL tx,INL ty) dep ==> ~is_instance tx ty))
End

Definition is_acyclic_computable_def:
  is_acyclic_computable dep =
    EVERY (λ(x:type+term,y:type+term).
      if (ISL x /\ ISL y)
      then ~IS_SOME (instance_subst [(OUTL y,OUTL x)] [] [])
      else if (ISR x /\ ISR y)
        then
          case (x,y) of
            | (INR (Const nx tx),INR (Const ny ty)) =>
              ~IS_SOME (instance_subst [(ty,tx)] [] [])
            | (_,_) => T
      else T
    ) dep
End

Theorem is_acyclic_computable_equiv:
  !dep. is_acyclic_computable dep = is_acyclic dep
Proof
  REWRITE_TAC[is_acyclic_computable_def,is_acyclic_def,instance_subst_completeness,EVERY_MEM]
  >> Cases >> fs[]
  >> rw[EQ_IMP_THM]
  >- fs[DISJ_IMP_THM,FORALL_AND_THM]
  >- (
    res_tac >> fs[ELIM_UNCURRY]
  )
  >- fs[DISJ_IMP_THM]
  >- (res_tac >> fs[ELIM_UNCURRY])
  >> (
    rename1 `_ e`
    >> Cases_on `e`
    >> rename1 `_ (q,r)`
    >> Cases_on `q`
    >> Cases_on `r`
    >> fs[DISJ_IMP_THM]
    >- (
      rpt(strip_tac)
      >> rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq)
      >> res_tac
    )
  )
QED

Definition is_orthogonal_def:
  is_orthogonal dep = EVERY (λ(x,y). EVERY (λ(z,_). ~has_common_instance x z) (FILTER (λz. z <> (x,y)) dep)) dep
End

(* TODO avoid double checking in computable version *)
Definition is_orthogonal_compute_def:
  is_orthogonal_compute dep = EVERY (λ(x,y). EVERY (λ(z,_). ~has_common_instance_compute x z) (FILTER (λz. z <> (x,y)) dep)) dep
End

Theorem is_orthogonal_equiv:
  !dep. is_orthogonal dep = is_orthogonal_compute dep
Proof
  REWRITE_TAC[is_orthogonal_compute_def,is_orthogonal_def,has_common_instance_equiv]
QED

Definition is_composable_compute_def:
  is_composable_compute q = EVERY (λ(x,(y:term+type)).
    has_common_instance_compute q x ==> is_instance_LR_compute q x)
End

Definition is_composable_def:
  is_composable q = EVERY (λ(x,(y:term+type)). has_common_instance q x ==> is_instance_LR q x)
End

Theorem is_composable_equiv:
  is_composable = is_composable_compute
Proof
  fs[FUN_EQ_THM]
  >> REWRITE_TAC[is_composable_def,is_composable_compute_def,is_instance_LR_equiv,has_common_instance_equiv]
QED

val _ = export_theory();
