(*
  Proves [model-theoretic conservative extension of
  HOL](https://doi.org/10.1016/j.entcs.2018.10.009), extending a model of a
  theory wrt a theory update. The model extension keeps those interpretations of
  the smaller model, for types and constants from the so-called *independent
  fragment*. In the independent fragment are all types and constants that are
  not depending on what is introduced by the update.
 *)
open preamble mlstringTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holAxiomsSyntaxTheory holBoolTheory
     holExtensionTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory"holModelConservativity"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

(* list functions *)

Theorem IS_SUFFIX_APPEND_NOT_MEM:
  !a b x c. IS_SUFFIX (a ++ [x] ++ b) c /\ ~MEM x c ==> IS_SUFFIX b c
Proof
  Induct
  >> rw[]
  >- (
    fs[IS_SUFFIX_APPEND]
    >> rename1`_ = l ++ c`
    >> Cases_on `l`
    >- (Cases_on `c` >> fs[])
    >> fs[]
  )
  >> first_x_assum match_mp_tac
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[IS_SUFFIX_APPEND]
  >> rename1`_ = l ++ c`
  >> Cases_on `l`
  >- (fs[] >> qpat_x_assum `_ = _` (assume_tac o GSYM) >> fs[])
  >> fs[]
QED

Triviality REPLICATE_inj:
  !x y a. REPLICATE x a = REPLICATE y a ==> x = y
Proof
  Induct >> fs[REPLICATE]
  >> Cases >> fs[REPLICATE]
  >> ASM_REWRITE_TAC[]
QED

(* trivial rewrites for is_instance overload *)

Theorem TYPE_SUBST_ZIP_ident:
  !ll l. ALL_DISTINCT ll /\ LENGTH l = LENGTH ll ==>
  TYPE_SUBST (ZIP (l,MAP Tyvar ll)) (Tyapp m (MAP Tyvar ll)) = Tyapp m l
Proof
  rw[EQ_LIST_EL,GSYM MAP_MAP_o]
  >> fs[GSYM TYPE_SUBST_EL,EL_MAP,REV_ASSOCD_ALOOKUP,ZIP_swap]
  >> qmatch_goalsub_abbrev_tac `ALOOKUP zipl _`
  >> qspecl_then [`zipl`,`n`] mp_tac ALOOKUP_ALL_DISTINCT_EL
  >> `ALL_DISTINCT (MAP FST zipl)` by (
    fs[Abbr`zipl`,MAP_ZIP]
    >> ((Q.ISPEC `Tyvar` (CONV_RULE SWAP_FORALL_CONV ALL_DISTINCT_MAP_inj))
      |> SIMP_RULE(srw_ss())[] |> GSYM |> ONCE_REWRITE_TAC o single)
    >> ASM_REWRITE_TAC[]
  )
  >> fs[Abbr`zipl`,MAP_ZIP,EL_ZIP,EL_MAP]
QED

Triviality LENGTH_mlstring_sort:
  LENGTH (mlstring_sort (tvars a)) = LENGTH (tvars a)
Proof
  fs[mlstring_sort_def]
QED

Theorem type_instantiations:
  (∀name l. ?σ.
    TYPE_SUBST σ (Tyapp name (MAP Tyvar (GENLIST (λx. implode (REPLICATE (SUC x) #"a")) (LENGTH l))))
    = Tyapp name l)
  ∧ (∀pred l name. LENGTH l = LENGTH (tvars pred) ⇒
      ?σ.
        TYPE_SUBST σ (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))) = Tyapp name l)
Proof
  rw[]
  >- (
    qmatch_goalsub_abbrev_tac `GENLIST f ` >>
    qexists_tac `ZIP (l,MAP Tyvar (GENLIST f (LENGTH l)))` >>
    `ALL_DISTINCT (GENLIST f (LENGTH l))` by (
      rw[ALL_DISTINCT_GENLIST,Abbr`f`,implode_def]
      >> imp_res_tac REPLICATE_inj
    ) >>
    drule TYPE_SUBST_ZIP_ident >> fs[]
  ) >>
  qexists_tac `ZIP (l,MAP Tyvar (mlstring_sort (tvars pred)))` >>
  `ALL_DISTINCT (mlstring_sort (tvars pred))` by (
    fs[ALL_DISTINCT_STRING_SORT,mlstring_sort_def]
  ) >>
  drule TYPE_SUBST_ZIP_ident >>
  fs[LENGTH_mlstring_sort,mlstring_sort_def]
QED

(* explain allTypes function by subtypes at a path of a type *)

Theorem allTypes_subtypes_at[local]:
  !ty x. MEM x (allTypes' ty)
  ==> ?p. subtype_at ty p = SOME x
  /\ !q. IS_PREFIX p q /\ p <> q ==>  (THE (subtype_at ty q)) ∉ nonbuiltin_types
Proof
  ho_match_mp_tac allTypes'_defn_ind
  >> rw[nonbuiltin_types_def,allTypes'_defn]
  >- (
    fs[MEM_MAP,MEM_FLAT,AND_IMP_INTRO,PULL_FORALL]
    >> rveq
    >> first_x_assum (drule_all_then strip_assume_tac)
    >> qpat_x_assum `MEM _ tys` (strip_assume_tac o REWRITE_RULE[MEM_EL])
    >> qexists_tac `(«fun»,n)::p`
    >> rw[subtype_at_def,IS_PREFIX_APPEND]
    >> Cases_on `q`
    >- fs[subtype_at_def,is_builtin_type_def]
    >> PairCases_on `h`
    >> fs[] >> rveq >> fs[]
    >> fs[subtype_at_def,GSYM PULL_FORALL]
  )
  >> qexists_tac `[]`
  >> rw[subtype_at_def]
QED

Theorem subtype_at_allTypes_eq:
  !ty x. MEM x (allTypes' ty)
  <=> x ∈ nonbuiltin_types
  /\ ?p. subtype_at ty p = SOME x
  /\ !q. IS_PREFIX p q /\ p <> q ==>  (THE (subtype_at ty q)) ∉ nonbuiltin_types
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM]
  >> conj_tac
  >- (
    fs[allTypes_subtypes_at]
    >> REWRITE_TAC[allTypes'_nonbuiltin]
  )
  >> ho_match_mp_tac type_ind
  >> rw[]
  >- (
    imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS]subtype_at_Tyvar)
    >> fs[allTypes'_defn,NULL_EQ,subtype_at_def]
  )
  >> fs[allTypes'_defn]
  >> rpt(FULL_CASE_TAC >> fs[])
  >- (
    Cases_on `p`
    >> fs[subtype_at_def,nonbuiltin_types_def]
    >> rveq
    >- fs[is_builtin_type_def]
    >> PairCases_on `h`
    >> fs[subtype_at_def]
  )
  >- (
    Cases_on `p`
    >- (
      fs[subtype_at_def,nonbuiltin_types_def]
      >> rveq >> fs[is_builtin_type_def]
    )
    >> PairCases_on `h`
    >> fs[subtype_at_def,EVERY_MEM,PULL_FORALL,AND_IMP_INTRO,MEM_FLAT,MEM_MAP]
    >> `MEM (EL h1 l) l` by fs[EL_MEM]
    >> first_x_assum drule
    >> disch_then (drule_then assume_tac)
    >> rw[PULL_EXISTS]
    >> goal_assum drule
    >> first_x_assum match_mp_tac
    >> fs[GSYM PULL_FORALL]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> first_x_assum (qspec_then `(«fun»,h1)::_` (assume_tac o GEN_ALL))
    >> rfs[subtype_at_def]
  )
  >- (
    first_x_assum (qspec_then `[]` assume_tac)
    >> Cases_on `p`
    >> rfs[subtype_at_def,nonbuiltin_types_def,is_builtin_type_def]
  )
  >- (
    first_x_assum (qspec_then `[]` assume_tac)
    >> Cases_on `p`
    >> rfs[subtype_at_def,nonbuiltin_types_def,is_builtin_type_def]
  )
  >- (
    Cases_on `p`
    >- (
      fs[subtype_at_def,nonbuiltin_types_def]
      >> rveq >> fs[is_builtin_type_def]
    )
    >> PairCases_on `h`
    >> fs[subtype_at_def,EVERY_MEM,PULL_FORALL,AND_IMP_INTRO,MEM_FLAT,MEM_MAP]
    >> `MEM (EL h1 l) l` by fs[EL_MEM]
    >> first_x_assum drule
    >> disch_then (drule_then assume_tac)
    >> rw[PULL_EXISTS]
    >> goal_assum drule
    >> first_x_assum match_mp_tac
    >> fs[GSYM PULL_FORALL]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> first_x_assum (qspec_then `(«fun»,h1)::_` (assume_tac o GEN_ALL))
    >> rfs[subtype_at_def]
  )
  >> (
    first_x_assum (qspec_then `[]` assume_tac)
    >> Cases_on `p`
    >> rfs[subtype_at_def,nonbuiltin_types_def,is_builtin_type_def]
  )
QED

(* nonbuiltin types and ground types *)

Theorem type_ok_TYPE_SUBST_eq:
  !sig sigma t. type_ok sig (TYPE_SUBST sigma t) <=>
  (type_ok sig t
  /\ ∀x. MEM x (tyvars t) ⇒ type_ok sig (TYPE_SUBST sigma (Tyvar x)))
Proof
  fs[FORALL_AND_THM,EQ_IMP_THM]
  >> conj_tac
  >- (
    fs[IMP_CONJ_THM,FORALL_AND_THM]
    >> reverse conj_tac
    >- (
      ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
      >> ACCEPT_TAC type_ok_TYPE_SUBST_imp
    )
    >> ntac 2 gen_tac
    >> ho_match_mp_tac type_ind
    >> rw[type_ok_def,EVERY_MAP,EVERY_MEM]
    >> res_tac
  )
  >> ntac 2 gen_tac
  >> ho_match_mp_tac type_ind
  >> rw[type_ok_def,tyvars_def,EVERY_MEM]
  >> fs[MEM_MAP,MEM_FOLDR_LIST_UNION]
  >> last_x_assum (drule_then match_mp_tac)
  >> rw[]
  >> res_tac
QED

Theorem TYPE_SUBST_nonbuiltin_types:
  !ty i. TYPE_SUBST i ty ∈ nonbuiltin_types
  ==> ty ∈ nonbuiltin_types
Proof
  Cases
  >> rw[nonbuiltin_types_def,IN_DEF,is_builtin_type_def]
  >> CCONTR_TAC
  >> fs[]
QED

Triviality nonbuiltin_types_TYPE_SUBST:
  !m l i. (Tyapp m l) ∈ nonbuiltin_types
  ==> TYPE_SUBST i (Tyapp m l) ∈ nonbuiltin_types
Proof
  fs[nonbuiltin_types_def,is_builtin_type_def]
QED

Theorem ground_types_allTypes:
  !x t. MEM x (allTypes' t)
  /\ t ∈ ground_types (sigof ctxt)
  ==> x ∈ ground_types (sigof ctxt)
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> ho_match_mp_tac allTypes'_defn_ind
  >> reverse conj_tac
  >- fs[allTypes'_defn]
  >> rw[]
  >> fs[allTypes'_defn]
  >> rpt(FULL_CASE_TAC >> fs[])
  >> fs[MEM_FLAT,MEM_MAP]
  >> first_x_assum drule
  >> disch_then match_mp_tac
  >> rveq
  >> fs[]
  >> fs[ground_types_def,tyvars_def,type_ok_def]
  >> imp_res_tac FOLDR_LIST_UNION_empty'
  >> fs[EVERY_MEM]
QED

Triviality nonbuiltin_types_allTypes:
  !ty. ty ∈ nonbuiltin_types ==> allTypes' ty = [ty]
Proof
  Cases
  >> rw[IN_DEF,nonbuiltin_types_def,is_builtin_type_def,allTypes'_defn]
QED

Theorem tyvars_allTypes_eq:
  ∀t x. MEM x (tyvars t) = MEM x (FLAT (MAP tyvars (allTypes' t)))
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM] >>
  reverse conj_tac
  >- (
    fs[MEM_MAP,MEM_FLAT,PULL_EXISTS,Once CONJ_COMM] >>
    ACCEPT_TAC MEM_tyvars_allTypes'
  ) >>
  ho_match_mp_tac allTypes'_defn_ind >>
  rw[tyvars_def,allTypes'_defn] >>
  fs[MEM_FOLDR_LIST_UNION,EVERY_MEM,PULL_FORALL,AND_IMP_INTRO] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  fs[PULL_EXISTS,MEM_FLAT,MEM_MAP] >>
  rpt (goal_assum (first_assum o mp_then Any mp_tac))
QED

Theorem tvars_tyvars_allTypes_eq:
  !pred x. MEM x (tvars pred) = MEM x (FLAT (MAP tyvars (allTypes pred)))
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM] >>
  conj_tac
  >- (
    Induct >> fs[tvars_def,tyvars_def,allTypes'_defn,allTypes_def,tyvars_allTypes_eq] >>
    rw[] >> rw[]
  ) >>
  Induct >> fs[tvars_def,tyvars_def,allTypes'_defn,allTypes_def,tyvars_allTypes_eq] >>
  rw[] >> rw[]
QED

Theorem bool_not_allTypes:
  (!t. ¬MEM Bool (allTypes' t))
  ∧ !tm. ¬MEM Bool (allTypes tm)
Proof
  conj_asm1_tac
  >- (
    ho_match_mp_tac type_ind >>
    rw[allTypes'_defn] >> rw[] >>
    CCONTR_TAC >>
    fs[MEM_FLAT,MEM_MAP,EVERY_MEM] >>
    first_x_assum (drule_then assume_tac) >> rfs[]
  ) >>
  Induct >> fs[allTypes_def]
QED

(* properties about context/theory extension *)

Theorem extends_IS_SUFFIX:
  !ctxt ctxt1. ctxt extends ctxt1 ==> IS_SUFFIX ctxt ctxt1
Proof
  fs[extends_def]
  >> ho_match_mp_tac RTC_INDUCT
  >> rw[] >> fs[IS_SUFFIX_APPEND]
QED

Theorem extends_LENGTH:
  !ctxt ctxt1. ctxt extends ctxt1 ==> LENGTH ctxt1 <= LENGTH ctxt
Proof
  rw[]
  >> imp_res_tac extends_IS_SUFFIX
  >> fs[IS_SUFFIX_APPEND]
QED

Theorem extends_init_LENGTH =
  CONV_RULE SWAP_FORALL_CONV extends_LENGTH |> Q.SPEC `init_ctxt`
  |> REWRITE_RULE [GSYM extends_init_def,EVAL ``LENGTH init_ctxt``]

Theorem extends_init_IS_SUFFIX =
  CONV_RULE SWAP_FORALL_CONV extends_IS_SUFFIX |> Q.SPEC `init_ctxt`
  |> REWRITE_RULE [GSYM extends_init_def]

Triviality extends_init_Fun:
  extends_init ctxt ==> MEM (NewType «fun» 2) ctxt
Proof
  rw[]
  >> drule extends_init_IS_SUFFIX
  >> rw[init_ctxt_def,IS_SUFFIX_APPEND]
  >> rw[MEM_APPEND]
QED

Triviality extends_init_Bool:
  extends_init ctxt ==> MEM (NewType «bool» 0) ctxt
Proof
  rw[]
  >> drule extends_init_IS_SUFFIX
  >> rw[init_ctxt_def,IS_SUFFIX_APPEND]
  >> rw[MEM_APPEND]
QED

Theorem extends_init_ctxt_is_std_sig:
  !ctxt. ctxt extends init_ctxt
  ==> is_std_sig (sigof ctxt)
Proof
  rpt strip_tac
  >> drule is_std_sig_extends
  >> disch_then match_mp_tac
  >> fs[is_std_sig_def,init_ctxt_def]
  >> EVAL_TAC
QED

Theorem extends_init_NIL_orth_ctxt:
  !ctxt. extends_init ctxt
  ==> ctxt extends [] /\ orth_ctxt ctxt
Proof
  gen_tac >> strip_tac
  >> conj_asm1_tac
  >- (
    match_mp_tac extends_trans
    >> fs[extends_init_def]
    >> goal_assum drule
    >> fs[init_ctxt_extends]
  )
  >> fs[extends_nil_orth]
QED

Theorem extends_init_APPEND_CONS_updates:
  extends_init (l1 ++ upd::l2)
  ⇒ upd updates l2
Proof
  rpt strip_tac >>
  dxrule_then strip_assume_tac extends_init_NIL_orth_ctxt >>
  dxrule_then strip_assume_tac extends_APPEND_NIL >>
  fs[extends_NIL_CONS_updates]
QED

(* properties about the dependency relation *)

Triviality dependency_INR_is_Const:
  (!a b. dependency ctxt a (INR b) ==> ?c ty. b = Const c ty)
  ∧ !a b. dependency ctxt (INR b) a ==> ?c ty. b = Const c ty
Proof
  rw[dependency_cases] >>
  imp_res_tac allCInsts_is_Const >>
  fs[]
QED

Theorem subst_clos_twice[simp]:
  !a b. subst_clos (subst_clos (dependency ctxt)) a b
    = subst_clos (dependency ctxt) a b
Proof
  ntac 2 Cases >>
  rw[EQ_IMP_THM,FORALL_AND_THM,subst_clos_def] >>
  fs[TYPE_SUBST_compose,INST_def,INST_CORE_def,PULL_EXISTS] >>
  map_every imp_res_tac (CONJUNCTS dependency_INR_is_Const) >>
  rveq >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  fs[TYPE_SUBST_compose,INST_def,INST_CORE_def] >>
  qmatch_goalsub_abbrev_tac `TYPE_SUBST s _` >>
  TRY (map_every qexists_tac [`s`,`[]`] >> fs[]) >>
  qexists_tac `s` >> fs[]
QED

Theorem dependency_FV_mono:
  ∀x y. ctxt extends [] /\ dependency ctxt x y
  ⇒ set (FV y) ⊆ set (FV x)
Proof
  rw[dependency_cases,FV_def,SUBSET_DEF]
  >> fs[]
  >> TRY (drule_then strip_assume_tac allCInsts_is_Const >> rveq)
  >> fs[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS]
  >> TRY (drule_all_then assume_tac allCInsts_tyvars
    ORELSE drule_all_then assume_tac MEM_tyvars_allTypes
    ORELSE drule_all_then assume_tac MEM_tyvars_allTypes')
  >> ASM_REWRITE_TAC[]
  >> qpat_x_assum `MEM (ConstSpec _ _ _) ctxt` (strip_assume_tac o ONCE_REWRITE_RULE[MEM_SPLIT])
  >> rveq
  >> dxrule_then assume_tac extends_APPEND_NIL
  >> dxrule_then assume_tac extends_NIL_CONS_updates
  >> fs[updates_cases]
  >> imp_res_tac (Q.ISPEC `SND:mlstring # term -> term ` MEM_MAP_f)
  >> qpat_x_assum `EVERY _ _` (drule_then strip_assume_tac o REWRITE_RULE[EVERY_MEM])
  >> imp_res_tac WELLTYPED_LEMMA
  >> fs[]
QED

Theorem bool_not_dependency:
  (!ctxt x. extends_init ctxt ==> ~(dependency ctxt) (INL Bool) x)
  ∧ !ctxt x. extends_init ctxt ==> ~(dependency ctxt) x (INL Bool)
Proof
  rw[dependency_cases,DISJ_EQ_IMP,bool_not_allTypes]
  >> TRY (qpat_x_assum `[] = _` (assume_tac o GSYM))
  >> fs[]
  >> qpat_x_assum `MEM _ ctxt` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> rveq
  >> drule_then strip_assume_tac extends_init_NIL_orth_ctxt
  >> dxrule_then assume_tac extends_APPEND_NIL
  >> dxrule_then assume_tac extends_NIL_CONS_updates
  >> `IS_SUFFIX l2 init_ctxt` by (
    dxrule_then strip_assume_tac extends_init_IS_SUFFIX
    >> match_mp_tac IS_SUFFIX_APPEND_NOT_MEM
    >> qpat_x_assum `IS_SUFFIX _ _` (assume_tac o REWRITE_RULE[APPEND_ASSOC] o ONCE_REWRITE_RULE[CONS_APPEND])
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[init_ctxt_def]
  )
  >> fs[IS_SUFFIX_APPEND,updates_cases,init_ctxt_def,types_of_upd_def]
  >> fs[]
QED

Theorem tyvar_not_dependency:
  !ctxt x. ~dependency ctxt (INL (Tyvar a)) x
Proof
  rw[dependency_cases]
QED

Theorem type_constructor_dependency:
  !x l m ctxt. MEM (NewType m (LENGTH l)) ctxt /\ MEM x l
  ==> (subst_clos (dependency ctxt)) (INL (Tyapp m l)) (INL x)
Proof
  rw[MEM_EL,subst_clos_def,dependency_cases,GSYM PULL_EXISTS]
  >> rename1 `k < LENGTH (l:type list)`
  >> qabbrev_tac `f = λx. implode (REPLICATE (SUC x) #"a")`
  >> qabbrev_tac `tynames_map = GENLIST (λx. (EL x l,(Tyvar o f) x)) (LENGTH l)`
  >> qabbrev_tac `tynames = GENLIST f (LENGTH l)`
  >> map_every qexists_tac [`Tyapp m (MAP Tyvar tynames)`,`Tyvar (EL k tynames)`,`tynames_map`]
  >> conj_asm1_tac
  >- (
    fs[]
    >> match_mp_tac LIST_EQ
    >> map_every qunabbrev_tac [`tynames`,`tynames_map`]
    >> rw[MAP_MAP_o,MAP_GENLIST,REV_ASSOCD_ALOOKUP,o_DEF]
    >> qmatch_goalsub_abbrev_tac `ALOOKUP al e`
    >> `ALOOKUP al e = SOME (EL x l)` by (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
      >> unabbrev_all_tac
      >> fs[MAP_GENLIST,MEM_GENLIST,o_DEF,ALL_DISTINCT_GENLIST]
      >> conj_tac
      >- (
        rw[REPLICATE_GENLIST,implode_def]
        >> qmatch_asmsub_abbrev_tac `GENLIST f`
        >> qspec_then `f` mp_tac LENGTH_GENLIST
        >> disch_then (fn x => ONCE_REWRITE_TAC[GSYM x])
        >> ASM_REWRITE_TAC[]
      )
      >> qexists_tac `x`
      >> fs[]
    )
    >> fs[]
  )
  >> conj_tac
  >- (
    qpat_x_assum `_:type = _` ((qspec_then `[(m,k)]` mp_tac) o ONCE_REWRITE_RULE[subtype_at_eq] o REWRITE_RULE[TYPE_SUBST_def])
    >> unabbrev_all_tac
    >> fs[subtype_at_def,EL_MAP]
  )
  >> disj2_tac
  >> map_every qexists_tac [`m`,`LENGTH l`]
  >> fs[]
  >> conj_tac
  >> rpt (goal_assum (first_assum o mp_then Any mp_tac))
  >> fs[]
QED

Theorem types_dependency:
  !a x ctxt. extends_init ctxt
  /\ MEM x (allTypes' a)
  ==> RTC (subst_clos (dependency ctxt)) (INL a) (INL x)
Proof
  ho_match_mp_tac allTypes'_defn_ind
  >> reverse(rw[])
  >- fs[allTypes'_defn]
  >> rename1`Tyapp s tys`
  >> reverse (Cases_on `s = «fun» /\ LENGTH tys = 2`)
  >> ntac 2 (
    fs[allTypes'_defn]
    >> rpt (FULL_CASE_TAC >> fs[])
    >> fs[]
  )
  >> fs[MEM_FLAT,MEM_MAP]
  >> rw[Once RTC_CASES1]
  >> disj2_tac
  >> rename1`MEM _ (allTypes' a)`
  >> qexists_tac `INL a`
  >> conj_tac
  >- (
    drule_then assume_tac extends_init_Fun
    >> match_mp_tac type_constructor_dependency
    >> fs[]
  )
  >> first_x_assum drule
  >> disch_then match_mp_tac
  >> fs[]
QED

Theorem constants_dependency':
  !ctxt c σ t. extends_init ctxt
  ∧ ALOOKUP (const_list ctxt) c = SOME σ
  ∧ MEM t (allTypes' σ)
  ==> dependency ctxt (INR (Const c σ)) (INL t)
Proof
  rw[]
  >> drule_then assume_tac extends_init_IS_SUFFIX
  >> dxrule_then strip_assume_tac extends_init_NIL_orth_ctxt
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_FLAT,MEM_MAP]
  >> rename1`consts_of_upd upd`
  >> qpat_x_assum `MEM upd ctxt` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> Cases_on`upd`
  >> rveq
  >> dxrule_then assume_tac extends_APPEND_NIL
  >> dxrule_then assume_tac extends_NIL_CONS_updates
  >- (
    rename1`(ConstSpec ov eqs prop)`
    >> fs[updates_cases]
    >> Cases_on `ov`
    >> fs[dependency_cases]
    >> disj1_tac
    >> qpat_x_assum `MEM (_,_) _` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
    >> pairarg_tac
    >> fs[PAIR,ETA_THM]
    >> rveq
    >> rename1`MEM (c,t') eqs`
    >> map_every qexists_tac [`t'`,`eqs`,`F`,`prop`]
    >> fs[]
    >> rename1`typeof defn`
    >> fs[GSYM WELLTYPED]
    >> conj_asm1_tac
    >- (
      drule_then (mp_tac o (REWRITE_RULE[EVERY_MEM]) o CONJUNCT2) proves_term_ok
      >> qmatch_goalsub_abbrev_tac `MAP f l'`
      >> Q.ISPEC_THEN `f` mp_tac MEM_MAP_f
      >> disch_then (dxrule_then assume_tac)
      >> rw[EVERY_MEM]
      >> res_tac
      >> unabbrev_all_tac
      >> imp_res_tac term_ok_welltyped
      >> fs[Once WELLTYPED_CLAUSES,equation_def]
    )
    >> drule allTypes_typeof
    >> Cases_on `typeof defn`
    >> fs[allTypes'_defn]
    >> rpt (FULL_CASE_TAC >> fs[SUBSET_DEF])
  )
  >- (
    rename1`TypeDefn name pred abs rep`
    >> `IS_SUFFIX l2 init_ctxt` by (
      match_mp_tac IS_SUFFIX_APPEND_NOT_MEM
      >> qpat_x_assum `IS_SUFFIX _ _` (assume_tac o REWRITE_RULE[APPEND_ASSOC] o ONCE_REWRITE_RULE[CONS_APPEND])
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[init_ctxt_def]
    )
    >> fs[updates_cases,consts_of_upd_def,dependency_cases]
    >> ntac 2 disj2_tac
    >> map_every qexists_tac [`name`,`pred`,`abs`,`rep`]
    >> fs[allTypes'_defn]
    >> rpt (FULL_CASE_TAC >> fs[])
    >> rveq
    >> qpat_x_assum `IS_SUFFIX _ init_ctxt` (strip_assume_tac o REWRITE_RULE[IS_SUFFIX_APPEND])
    >> fs[init_ctxt_def]
  )
  >> fs[consts_of_upd_def,updates_cases,dependency_cases]
QED

Theorem constants_dependency:
  !ctxt c ty0 ty i x. extends_init ctxt
  ∧ ALOOKUP (const_list ctxt) c = SOME ty0
  ∧ ty = TYPE_SUBST i ty0
  ∧ MEM x (allTypes' ty)
  ⇒ (subst_clos (dependency ctxt))⃰ (INR (Const c ty)) (INL x)
Proof
  rw[]
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_MAP,MEM_FLAT]
  >> rename1`TYPE_SUBST ρ σ`
  >> rveq
  >> drule_all_then strip_assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM]subtype_at_allTypes_eq))
  >> Cases_on `?q α. IS_PREFIX p q /\ subtype_at σ q = SOME (Tyvar α)`
  >> fs[]
  (* x subtype (Tyvar α) subtype σ *)
  >- (
    rename1`Tyvar α`
    >> qpat_x_assum `IS_PREFIX _ _` (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])
    >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
    >> rename1`p = q ++ l`
    >> dxrule_then (qspec_then `l` assume_tac) subtype_at_decomp_path
    >> Cases_on `NULL l`
    >- (
      fs[NULL_EQ,subtype_at_def]
      >> match_mp_tac RTC_SUBSET
      >> fs[subst_clos_def]
      >> map_every qexists_tac [`Tyvar α`,`Const c σ`,`ρ`]
      >> fs[INST_def,INST_CORE_def]
      >> match_mp_tac constants_dependency'
      >> rw[subtype_at_allTypes_eq]
      >- fs[nonbuiltin_types_def,is_builtin_type_def]
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> rw[]
      >> first_x_assum drule
      >> disch_then (drule_then assume_tac)
      >> fs[IS_PREFIX_APPEND]
      >> rveq
      >> drule subtype_at_parent
      >> impl_tac
      >- (CCONTR_TAC >> fs[])
      >> disch_then strip_assume_tac
      >> fs[]
      >> match_mp_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] nonbuiltin_types_TYPE_SUBST)
      >> dxrule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
      >> qexists_tac `ρ`
      >> fs[]
    )
    >> rw[Once RTC_CASES1]
    >> qexists_tac `INL (TYPE_SUBST ρ (Tyvar α))`
    >> conj_tac
    >- (
      fs[subst_clos_def]
      >> map_every qexists_tac [`Tyvar α`,`Const c σ`,`ρ`]
      >> simp[INST_def,INST_CORE_def]
      >> match_mp_tac constants_dependency'
      >> asm_rewrite_tac[]
      >> rw[subtype_at_allTypes_eq]
      >- fs[is_builtin_type_def,nonbuiltin_types_def]
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> rw[IS_PREFIX_APPEND]
      >> rename1`q' ++ l' ≠ _`
      >> `¬NULL l'` by (CCONTR_TAC >> fs[NULL_EQ])
      >> first_x_assum (qspec_then `q'` mp_tac)
      >> impl_tac
      >- fs[IS_PREFIX_APPEND,NULL_EQ]
      >> drule subtype_at_parent
      >> impl_tac >- fs[NULL_EQ]
      >> rw[]
      >> fs[]
      >> match_mp_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] nonbuiltin_types_TYPE_SUBST)
      >> dxrule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
      >> qexists_tac `ρ`
      >> fs[]
    )
    >> match_mp_tac types_dependency
    >> rw[subtype_at_allTypes_eq]
    >> fs[]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> first_x_assum (qspec_then `q++_` (assume_tac o GEN_ALL))
    >> `!s. subtype_at (TYPE_SUBST ρ (Tyvar α)) s = subtype_at (TYPE_SUBST ρ σ) (q ++ s)` by (
      rpt strip_tac
      >> PURE_REWRITE_TAC[Once EQ_SYM_EQ]
      >> match_mp_tac subtype_at_decomp_path
      >> fs[subtype_at_TYPE_SUBST]
    )
    >> fs[]
  )
  (* (Tyvar α) subtype x subtype σ *)
  >> `IS_SOME (subtype_at σ p)` by (
    fs[DISJ_EQ_IMP]
    >> match_mp_tac subtype_TYPE_SUBST_Tyvar
    >> rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
  )
  >> fs[IS_SOME_EXISTS,DISJ_EQ_IMP]
  >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
  >> rfs[]
  >> ONCE_REWRITE_TAC[RTC_CASES1]
  >> fs[]
  >> qexists_tac `INL x`
  >> rw[RTC_REFL,subst_clos_def]
  >> rename1`subtype_at σ p = SOME x'`
  >> map_every qexists_tac [`x'`,`Const c σ`,`ρ`]
  >> simp[INST_def,INST_CORE_def]
  >> match_mp_tac constants_dependency'
  >> rw[subtype_at_allTypes_eq]
  >- imp_res_tac TYPE_SUBST_nonbuiltin_types
  >> goal_assum (first_x_assum o mp_then Any mp_tac)
  >> rw[]
  >> `IS_SOME (subtype_at σ q)` by (
    match_mp_tac subtype_TYPE_SUBST_Tyvar
    >> fs[GSYM PULL_EXISTS]
    >> conj_tac
    >- (
      fs[IS_PREFIX_APPEND]
      >> rveq
      >> drule (Ho_Rewrite.REWRITE_RULE[IS_SOME_EXISTS,PULL_EXISTS] subtype_at_IS_SOME_parent)
      >> fs[]
    )
    >> rw[]
    >> fs[IS_PREFIX_APPEND]
    >> rveq
  )
  >> fs[IS_SOME_EXISTS]
  >> rename1`subtype_at σ q = SOME x`
  >> Cases_on `x`
  >- (first_x_assum drule >> fs[])
  >> match_mp_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] nonbuiltin_types_TYPE_SUBST)
  >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
  >> first_x_assum (drule_then drule)
  >> rw[]
  >> goal_assum drule
QED

(* independent fragment definition and properties *)

Definition indep_frag_def:
  indep_frag ctxt us (frag:(type -> bool) # (mlstring # type -> bool)) =
    let
      v = { x | ?s u. MEM u us
      /\ (RTC (subst_clos (dependency ctxt))) x (LR_TYPE_SUBST s u) };
      v_c = { (x,ty) | (INR (Const x ty)) ∈ v };
      v_t = { x | (INL x) ∈ v };
    in
      ((FST frag) DIFF v_t, (SND frag) DIFF v_c)
End

Triviality indep_frag_subset_frag:
  !ctxt u frag.
  (FST (indep_frag ctxt u frag)) ⊆ (FST (frag))
  /\ (SND (indep_frag ctxt u frag)) ⊆ (SND (frag))
Proof
  fs[indep_frag_def]
QED

(* the independent fragment is a fragment (even for arbitrary us) *)

Theorem independent_frag_is_frag:
  !ctxt us. extends_init ctxt
  ⇒ is_sig_fragment (sigof ctxt) (indep_frag ctxt us (total_fragment (sigof ctxt)))
Proof
  rw[is_sig_fragment_def,total_fragment_def,indep_frag_def]
  >- fs[INTER_DEF,DIFF_DEF,SUBSET_DEF]
  >- fs[INTER_DEF,DIFF_DEF,SUBSET_DEF]
  >- fs[INTER_DEF,DIFF_DEF,SUBSET_DEF]
  >- fs[INTER_DEF,DIFF_DEF,SUBSET_DEF]
  >> rw[Once IN_DEF]
  >> rw[Once builtin_closure_cases,DISJ_EQ_IMP]
  >> rfs[ground_consts_def]
  >> Cases_on`c ∈ nonbuiltin_types`
  >- (
    fs[nonbuiltin_constinsts_def,term_ok_def]
    >> `RTC (subst_clos (dependency ctxt)) (INR (Const s c)) (INL c)` by (
      match_mp_tac constants_dependency
      >> drule_then assume_tac nonbuiltin_types_allTypes
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[]
    )
    >> qpat_x_assum `!t. _` (assume_tac o SIMP_RULE(srw_ss())[DISJ_EQ_IMP] o ONCE_REWRITE_RULE[RTC_CASES_RTC_TWICE])
    >> res_tac
  )
  >> `?a b. c = Fun a b` by (
    Cases_on `c`
    >> fs[nonbuiltin_types_def,is_builtin_type_def]
    >> fs[]
    >> ntac 2 (rename1`LENGTH l` >> Cases_on `l` >> fs[])
  )
  >> rveq
  >> `!A b. builtin_closure A b <=> b ∈ builtin_closure A` by fs[IN_DEF]
  >> pop_assum (fs o single)
  >> conj_tac
  >> match_mp_tac builtin_closure_allTypes
  >> rpt strip_tac
  >> fs[]
  (* 2 subgoals *)
  >| List.tabulate (2, fn _ => (
    conj_asm1_tac
    >- (
      conj_tac
      >- (
        qmatch_asmsub_abbrev_tac `allTypes' σ`
        >> `σ ∈ ground_types (sigof ctxt)` by (
          fs[ground_types_def,tyvars_def,type_ok_def,LIST_UNION_EQ_NIL]
        )
        >> match_mp_tac ground_types_allTypes
        >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
      )
      >> imp_res_tac allTypes'_nonbuiltin
      >> fs[nonbuiltin_types_def]
    )
    >> fs[DISJ_EQ_IMP]
    >> rw[]
    >> CCONTR_TAC
    >> qpat_x_assum `!ρ. _` mp_tac
    >> fs[]
    >> rpt (goal_assum (first_assum o mp_then Any mp_tac))
    >> rename1`LR_TYPE_SUBST s'`
    >> qexists_tac `s'`
    >> rw[Once RTC_CASES_RTC_TWICE]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[term_ok_def]
    >> match_mp_tac constants_dependency
    >> rpt (goal_assum drule)
    >> rename1`TYPE_SUBST i ty0`
    >> qexists_tac `i`
    >> fs[]
    >> qpat_x_assum `Fun _ _ = _` (fs o single o GSYM)
    >> fs[allTypes'_defn]
  ))
QED

(* list symbols introduced by an update *)
Definition upd_introduces_def:
  (upd_introduces (ConstSpec ov eqs prop)
    = MAP (λ(s,t). INR (Const s (typeof t))) eqs)
  /\ (upd_introduces (TypeDefn name pred abs rep)
    = [INL (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred))))])
  /\ (upd_introduces (NewType name n)
    = [INL (Tyapp name (MAP Tyvar (GENLIST (λx. implode (REPLICATE (SUC x) #"a")) n)))])
  /\ (upd_introduces (NewConst name ty) = [INR (Const name ty)])
  /\ (upd_introduces (NewAxiom prop) = [])
End

Triviality upd_introduces_is_const_or_type:
  !upd u. MEM u (upd_introduces upd) ⇒ is_const_or_type u
Proof
  Cases >> rw[is_const_or_type_def,upd_introduces_def,MEM_MAP,PULL_EXISTS] >>
  imp_res_tac allCInsts_is_Const >> fs[] >>
  pairarg_tac >> fs[]
QED

(* independent fragment of an update *)
Definition indep_frag_upd_def:
  (indep_frag_upd ctxt upd frag = indep_frag ctxt (upd_introduces upd) frag)
End

Theorem indep_frag_upd_is_frag:
  !ctxt upd. extends_init ctxt
  ⇒ is_sig_fragment (sigof ctxt) (indep_frag_upd ctxt upd (total_fragment (sigof ctxt)))
Proof
  rw[indep_frag_upd_def] >> metis_tac[independent_frag_is_frag]
QED

Theorem indep_frag_upd_subst_clos:
  (!upd ctxt frag ty ty'. ty ∈ FST (indep_frag_upd ctxt upd frag)
  ∧ RTC (subst_clos (dependency ctxt)) (INL ty) (INL ty')
  ∧ ty' ∈ FST frag
  ==> ty' ∈ FST (indep_frag_upd ctxt upd frag))
  ∧ (!upd ctxt frag ty ty' c. ty ∈ FST (indep_frag_upd ctxt upd frag)
  ∧ RTC (subst_clos (dependency ctxt)) (INL ty) (INR (Const c ty'))
  ∧ (c,ty') ∈ SND frag
  ==> (c,ty') ∈ SND (indep_frag_upd ctxt upd frag))
  ∧ (!upd ctxt frag ty ty' c. (c,ty) ∈ SND (indep_frag_upd ctxt upd frag)
  ∧ RTC (subst_clos (dependency ctxt)) (INR (Const c ty)) (INL ty')
  ∧ ty' ∈ FST frag
  ==> ty' ∈ FST (indep_frag_upd ctxt upd frag))
  ∧ (!upd ctxt frag ty ty' c d. (c,ty) ∈ SND (indep_frag_upd ctxt upd frag)
  ∧ RTC (subst_clos (dependency ctxt)) (INR (Const c ty)) (INR (Const d ty'))
  ∧ (d,ty') ∈ SND frag
  ==> (d,ty') ∈ SND (indep_frag_upd ctxt upd frag))
Proof
  rw[indep_frag_upd_def,indep_frag_def,DISJ_EQ_IMP]
  >> rename1`LR_TYPE_SUBST s _`
  >> first_x_assum (dxrule_then (qspec_then `s` assume_tac))
  >> pop_assum (match_mp_tac o SIMP_RULE(srw_ss())[DISJ_EQ_IMP] o ONCE_REWRITE_RULE[RTC_CASES_RTC_TWICE])
  >> asm_rewrite_tac[]
QED

val indep_frag_upd_subst_clos_INL_INL = List.nth(CONJUNCTS indep_frag_upd_subst_clos,0)
val indep_frag_upd_subst_clos_INL_INR = List.nth(CONJUNCTS indep_frag_upd_subst_clos,1)
val indep_frag_upd_subst_clos_INR_INL = List.nth(CONJUNCTS indep_frag_upd_subst_clos,2)
val indep_frag_upd_subst_clos_INR_INR = List.nth(CONJUNCTS indep_frag_upd_subst_clos,3)

Theorem rep_abs_indep_frag_upd:
  ∀σ name pred l abs rep ctxt upd.
  MEM upd ctxt
  ∧ MEM (TypeDefn name pred abs rep) ctxt
  ∧ Tyapp name (MAP Tyvar (mlstring_sort (tvars pred))) ∈ nonbuiltin_types
  ∧ ((abs, (TYPE_SUBST σ (Fun (domain (typeof pred)) (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred))))))) ∈ (SND (indep_frag_upd ctxt upd (total_fragment (sigof ctxt))))
  ∨ (rep, (TYPE_SUBST σ (Fun (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))) (domain (typeof pred)))))
  ∈ SND (indep_frag_upd ctxt upd (total_fragment (sigof ctxt))))
  ⇒ (TYPE_SUBST σ (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))))
    ∈ FST (indep_frag_upd ctxt upd (total_fragment (sigof ctxt)))
Proof
  rw[indep_frag_upd_def,indep_frag_def]
  >> fs[DISJ_EQ_IMP]
  >> TRY (
    qmatch_goalsub_abbrev_tac `_ ∈ FST _`
    >> fs[total_fragment_def,ground_consts_def,ground_types_def,tyvars_def,type_ok_def,LIST_UNION_EQ_NIL]
    >> imp_res_tac FOLDR_LIST_UNION_empty'
    >> fs[nonbuiltin_types_def,is_builtin_type_def]
    >> fs[EVERY_MAP,tyvars_def]
  )
  >> strip_tac
  >> first_x_assum drule
  >> rename1`LR_TYPE_SUBST s u`
  >> disch_then (qspec_then `s` (fn x => CCONTR_TAC >> (mp_tac x)))
  >> rw[Once RTC_CASES1]
  >> disj2_tac
  >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
  >> fs[subst_clos_def]
  >> CONV_TAC (RESORT_EXISTS_CONV rev)
  >> rename1`TYPE_SUBST σ`
  >> qexists_tac `σ`
  >> TRY (
    qmatch_goalsub_abbrev_tac `Const abs _`
    >> qexists_tac `Const abs (Fun (domain (typeof pred)) (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))))`
  )
  >> TRY (
    qmatch_goalsub_abbrev_tac `Const rep _`
    >> qexists_tac `Const rep (Fun (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))) (domain (typeof pred)))`
  )
  >> qexists_tac `Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))`
  >> imp_res_tac nonbuiltin_types_allTypes
  >> fs[INST_CORE_def,INST_def]
  >> fs[dependency_cases]
  >> disj2_tac
  >> disj2_tac
  >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
  >> fs[mlstring_sort_def]
QED

Theorem extends_init_TypeDefn_nonbuiltin_types:
  !ctxt name pred abs rep l. extends_init ctxt
  /\ MEM (TypeDefn name pred abs rep) ctxt
  /\ LENGTH l = LENGTH (tvars pred)
  ==> Tyapp name l ∈ nonbuiltin_types
Proof
  rw[MEM_SPLIT]
  >> `IS_SUFFIX l2 init_ctxt` by (
    dxrule_then strip_assume_tac extends_init_IS_SUFFIX
    >> match_mp_tac IS_SUFFIX_APPEND_NOT_MEM
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[init_ctxt_def]
  )
  >> drule_then strip_assume_tac extends_init_NIL_orth_ctxt
  >> FULL_SIMP_TAC(bool_ss)[GSYM APPEND_ASSOC]
  >> dxrule_then assume_tac extends_APPEND_NIL
  >> fs[extends_NIL_CONS_extends,IS_SUFFIX_APPEND,updates_cases]
  >> rveq
  >> fs[nonbuiltin_types_def,is_builtin_type_def]
  >> rpt(qpat_x_assum `~MEM _ (MAP _ (const_list _))` kall_tac)
  >> conj_asm1_tac
  >> rw[DISJ_EQ_IMP]
  >> fs[init_ctxt_def]
QED

Theorem extends_init_NewType_nonbuiltin_types:
  !ctxt name l. extends_init ((NewType name (LENGTH l))::ctxt)
  ==> Tyapp name l ∈ nonbuiltin_types
Proof
  rw[] >>
  drule_then strip_assume_tac extends_init_IS_SUFFIX >>
  fs[extends_init_def,IS_SUFFIX_APPEND] >>
  rename1`ll ++ init_ctxt` >>
  CCONTR_TAC >>
  drule_then (strip_assume_tac o CONJUNCT1) (REWRITE_RULE[extends_init_def] extends_init_NIL_orth_ctxt) >>
  dxrule_then assume_tac extends_NIL_CONS_updates >>
  fs[IS_SUFFIX_APPEND,updates_cases,init_ctxt_def,types_of_upd_def] >>
  Cases_on `ll` >> fs[] >> rveq >>
  fs[is_builtin_type_def,is_builtin_type_def,nonbuiltin_types_def]
QED

Theorem type_ok_subtype_lemma:
  !ty0.
  type_ok (tysig |+ (name,arity)) ty0 /\
  ~type_ok tysig ty0 ==>
  ?args. subtype1⃰ (Tyapp name args) ty0 /\
          arity = LENGTH args /\
          EVERY (type_ok(tysig |+ (name,arity))) args
Proof
  ho_match_mp_tac type_ind >> conj_tac >- simp[type_ok_def] >>
  rw[EVERY_MEM] >>
  rename1 `Tyapp name1 args` >>
  Cases_on `name = name1` >-
    (rveq >>
     qexists_tac `args` >> simp[] >>
     fs[type_ok_def,FLOOKUP_UPDATE,EVERY_MEM]) >>
  `?ty. MEM ty args /\ ~type_ok tysig ty /\ type_ok (tysig |+ (name,arity)) ty`
    by(fs[type_ok_def,EVERY_MEM,FLOOKUP_UPDATE] >> rfs[] >>
       goal_assum drule >> res_tac >> simp[]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  goal_assum (fn thm => first_x_assum(mp_then (Pos last) match_mp_tac thm)) >>
  simp[] >>
  drule_then match_mp_tac RTC_RTC >>
  match_mp_tac RTC_SUBSET >>
  simp[subtype1_def]
QED

(* the independent fragment of an update's dependencies
 * is within the earlier total_fragment *)

Theorem indep_frag_upd_frag_reduce:
  !ctxt upd.
  let ext = upd::ctxt;
    idf = indep_frag_upd ext upd (total_fragment (sigof ext));
  in extends_init ext
  ⇒ FST idf ⊆ FST (total_fragment (sigof ctxt))
  /\ SND idf ⊆ SND (total_fragment (sigof ctxt))
Proof
  SIMP_TAC(bool_ss++LET_ss)[]
  >> rpt gen_tac
  >> strip_tac
  >> drule_then (assume_tac o CONJUNCT1) extends_init_NIL_orth_ctxt
  >> dxrule_then strip_assume_tac extends_NIL_CONS_updates
  >> fs[updates_cases,indep_frag_upd_def,indep_frag_def,upd_introduces_def,total_fragment_def,indep_frag_def,DIFF_DEF,SUBSET_DEF,Excl"REPLICATE"]
  (* NewConst *)
  >- (
    rw[ground_consts_def,ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE]
    >> EVERY_CASE_TAC
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> fs[is_instance_simps]
    >> rename1`TYPE_SUBST s _`
    >> first_x_assum (qspec_then `s` mp_tac)
    >> fs[LR_TYPE_SUBST_def,INST_CORE_def,INST_def]
  )
  (* ConstSpec *)
  >- (
    rw[ground_consts_def,ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION]
    >> EVERY_CASE_TAC
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> fs[is_instance_simps,DISJ_EQ_IMP]
    >> imp_res_tac ALOOKUP_MEM
    >> fs[MEM_MAP,PULL_EXISTS]
    >> first_x_assum drule
    >> rename1`TYPE_SUBST s _`
    >> disch_then (qspec_then `s` mp_tac)
    >> pairarg_tac
    >> fs[LR_TYPE_SUBST_def,INST_CORE_def,INST_def]
  )
  (* NewType *)
  >- (
    qmatch_goalsub_abbrev_tac `GENLIST f _` >>
    rw[ground_consts_def,ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,is_instance_simps] >>
    drule_then strip_assume_tac type_ok_type_ext >>
    rveq >>
    CCONTR_TAC >>
    qpat_x_assum `!s. _` mp_tac >>
    fs[Excl"REPLICATE"] >>
    Ho_Rewrite.REWRITE_TAC[LR_TYPE_SUBST_def,SUM_MAP,ISL,OUTL]
    >- (
      rename1`Tyapp name l` >>
      qspecl_then [`name`,`l`] strip_assume_tac (CONJUNCT1 type_instantiations) >>
      rename1`TYPE_SUBST σ _ = _` >>
      qexists_tac `σ` >>
      fs[Abbr`f`,Excl"REPLICATE"] >>
      qpat_x_assum `RTC subtype1 _ _` (assume_tac o REWRITE_RULE[RTC_CASES_TC]) >>
      fs[] >>
      match_mp_tac subtype_dependency_nonbuiltin >>
      drule_then strip_assume_tac extends_init_IS_SUFFIX >>
      fs[extends_init_def,IS_SUFFIX_APPEND] >>
      rename1`ll ++ init_ctxt` >>
      CCONTR_TAC >>
      drule_then strip_assume_tac (REWRITE_RULE[extends_init_def] extends_init_NIL_orth_ctxt) >>
      dxrule_then assume_tac extends_NIL_CONS_updates >>
      fs[IS_SUFFIX_APPEND,updates_cases,init_ctxt_def,types_of_upd_def] >>
      Cases_on `ll` >> fs[] >> rveq >>
      fs[is_builtin_type_def]
    ) >>
    qpat_x_assum `RTC subtype1 _ _` (assume_tac o REWRITE_RULE[RTC_CASES_TC]) >>
    fs[]
    >- (
      rename1`Tyapp name l` >>
      qspecl_then [`name`,`l`] strip_assume_tac (CONJUNCT1 type_instantiations) >>
      rename1`TYPE_SUBST σ _ = _` >>
      qexists_tac `σ` >>
      fs[Abbr`f`] >>
      pop_assum kall_tac >>
      match_mp_tac constants_dependency >>
      rename1`TYPE_SUBST i ty0` >>
      map_every qexists_tac [`ty0`,`i`] >>
      fs[Once EQ_SYM_EQ] >>
      `Tyapp name l ∈ nonbuiltin_types` by (
        drule extends_init_NewType_nonbuiltin_types >>
        fs[]
      ) >>
      imp_res_tac nonbuiltin_types_allTypes >> fs[]
    ) >>
    imp_res_tac extends_init_NewType_nonbuiltin_types >>
    fs[nonbuiltin_types_def] >>
    qexists_tac `GENLIST (λn. (EL n l,Tyvar(f n))) (LENGTH l)` >>
    simp[MAP_MAP_o,MAP_GENLIST,o_DEF,Abbr `f`,REV_ASSOCD_ALOOKUP,ALOOKUP_GENLIST_lemma,ALOOKUP_GENLIST] >>
    qmatch_goalsub_abbrev_tac `Tyapp _ ll` >>
    `ll = l` by(match_mp_tac LIST_EQ >> rw[Abbr `ll`]) >>
    qunabbrev_tac `ll` >>
    pop_assum SUBST_ALL_TAC >>
    drule_all_then strip_assume_tac subtype_nonbuiltin_through_allTypes >>
    drule constants_dependency >>
    simp[] >>
    disch_then drule >>
    disch_then drule >>
    strip_tac >>
    drule_then match_mp_tac RTC_RTC >>
    qpat_x_assum `_ subtype _` (strip_assume_tac o REWRITE_RULE[RTC_CASES_TC]) >- simp[] >>
    drule_then match_mp_tac subtype_dependency_nonbuiltin >>
    fs[extends_init_def] >>
    imp_res_tac allTypes'_type_ok
  )
  (* TypeDefn *)
  >- (
    Ho_Rewrite.REWRITE_TAC[GSYM mlstring_sort_def] >>
    rw[ground_consts_def,ground_types_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,is_instance_simps] >>
    CCONTR_TAC >>
    qpat_x_assum `!s. _` mp_tac >>
    fs[DISJ_EQ_IMP] >>
    Ho_Rewrite.REWRITE_TAC[LR_TYPE_SUBST_def,SUM_MAP,ISL,OUTL] >>
    qabbrev_tac `rep_type = domain (typeof pred)` >>
    qabbrev_tac `abs_type = Tyapp name (MAP Tyvar (mlstring_sort (tvars pred)))`
    >- (
      drule_then strip_assume_tac type_ok_type_ext >>
      rveq >>
      rename1`Tyapp name l` >>
      drule_then (qspec_then `name` strip_assume_tac) (CONJUNCT2 type_instantiations) >>
      rename1`TYPE_SUBST σ _ = _` >>
      qexists_tac `σ` >>
      fs[Excl"TYPE_SUBST_def",Abbr`abs_type`] >>
      qpat_x_assum `RTC subtype1 _ _` (assume_tac o REWRITE_RULE[RTC_CASES_TC]) >>
      fs[] >>
      `Tyapp name l ∈ nonbuiltin_types` by (
        drule_then match_mp_tac extends_init_TypeDefn_nonbuiltin_types >>
        rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
        map_every qexists_tac [`abs`,`rep`] >> fs[]
      ) >>
      imp_res_tac nonbuiltin_types_allTypes >>
      match_mp_tac subtype_dependency >>
      rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
      fs[extends_init_def]
    ) >>
    fs[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
    rpt (FULL_CASE_TAC >> fs[])
    (* rep *)
    >- (
      rename1`TYPE_SUBST i ty0` >>
      qexists_tac `i` >>
      match_mp_tac RTC_SUBSET >>
      simp[subst_clos_def] >>
      map_every qexists_tac [`abs_type`,`Const n ty0`,`i`] >>
      fs[INST_def,INST_CORE_def] >>
      match_mp_tac(last(CONJUNCTS dependency_rules)) >>
      simp[] >>
      map_every qexists_tac [`name`,`pred`,`abs`,`rep`] >>
      simp[] >>
      rveq >>
      simp[Abbr `abs_type`,mlstring_sort_def]
    )
    (* abs *)
    >- (
      qmatch_asmsub_abbrev_tac `Fun _ _ = ty0` >>
      qpat_x_assum `_ = ty0` (assume_tac o GSYM) >>
      rename1`TYPE_SUBST i ty0` >>
      qexists_tac `i` >>
      match_mp_tac RTC_SUBSET >>
      fs[subst_clos_def] >>
      map_every qexists_tac [`abs_type`,`Const n ty0`,`i`] >>
      fs[INST_def,INST_CORE_def,dependency_cases] >>
      rpt disj2_tac >>
      rveq >>
      rename1`TypeDefn name pred abs rep` >>
      map_every qexists_tac [`name`,`pred`,`abs`,`rep`] >>
      fs[GSYM mlstring_sort_def]
    ) >>
    Cases_on `type_ok (tysof ctxt) ty` >-
      (res_tac >>
       pop_assum(qspec_then `ty0` strip_assume_tac) >>
       fs[]) >>
    fs[] >>
    rveq >>
    drule_all_then strip_assume_tac type_ok_subtype_lemma >>
    qexists_tac `GENLIST (λx. (EL x args, EL x (MAP Tyvar (mlstring_sort (tvars pred))))) (LENGTH args)` >>
    `TYPE_SUBST (GENLIST (λx. (EL x args, EL x (MAP Tyvar (mlstring_sort (tvars pred))))) (LENGTH args)) abs_type
     = Tyapp name args` by
      (simp[Abbr `abs_type`] >>
       qpat_x_assum `LENGTH _ = LENGTH _` (assume_tac o GSYM) >>
       match_mp_tac LIST_EQ >>
       rw[REV_ASSOCD_ALOOKUP,MAP_GENLIST,ELIM_UNCURRY,o_DEF,ALOOKUP_GENLIST_lemma',EL_MAP,
             ALOOKUP_GENLIST,mlstring_sort_def]) >>
    pop_assum SUBST_ALL_TAC >>
    `Tyapp name args ∈ nonbuiltin_types`
      by(drule_then match_mp_tac extends_init_TypeDefn_nonbuiltin_types >>
         rw[RIGHT_AND_OVER_OR,EXISTS_OR_THM]) >>
    qpat_x_assum `_ subtype _` (strip_assume_tac o REWRITE_RULE[RTC_CASES_TC]) >-
      (drule constants_dependency >>
       disch_then(qspec_then `n` mp_tac) >>
       simp[] >>
       disch_then(qspec_then `i` match_mp_tac) >>
       pop_assum (assume_tac o GSYM) >> fs[allTypes'_defn,nonbuiltin_types_def,is_builtin_type_def]) >>
    fs[nonbuiltin_types_def] >>
    drule_all_then strip_assume_tac subtype_nonbuiltin_through_allTypes >>
    drule constants_dependency >>
    disch_then(qspec_then `n` mp_tac) >>
    simp[] >>
    disch_then drule >>
    strip_tac >>
    drule_then match_mp_tac RTC_RTC >>
    qpat_x_assum `_ subtype _` (strip_assume_tac o REWRITE_RULE[RTC_CASES_TC]) >- simp[] >>
    drule_then match_mp_tac subtype_dependency_nonbuiltin >>
    fs[extends_init_def] >>
    imp_res_tac allTypes'_type_ok
  )
QED

(* measure for wf_rel_tac within type_interpretation_ext_of_def *)

Definition subst_clos_term_ext_rel_def:
 subst_clos_term_ext_rel
 (a1: ('U -> 'U -> bool) # 'U # update # update list # (type -> 'U) # (mlstring # type -> 'U) # type
    + ('U -> 'U -> bool) # 'U # update # update list # (type -> 'U) # (mlstring # type -> 'U) # mlstring # type)
(a2: ('U -> 'U -> bool) # 'U # update # update list # (type -> 'U) # (mlstring # type -> 'U) # type
    + ('U -> 'U -> bool) # 'U # update # update list # (type -> 'U) # (mlstring # type -> 'U) # mlstring # type)
 =
 let
   upd1 = sum_CASE a1 (FST o SND o SND) (FST o SND o SND);
   upd2 = sum_CASE a2 (FST o SND o SND) (FST o SND o SND);
   ctxt1 = sum_CASE a1 (FST o SND o SND o SND) (FST o SND o SND o SND);
   ctxt2 = sum_CASE a2 (FST o SND o SND o SND) (FST o SND o SND o SND);
   mem1 = sum_CASE a1 FST FST;
   mem2 = sum_CASE a2 FST FST;
   ind1 = sum_CASE a1 (FST o SND) (FST o SND);
   ind2 = sum_CASE a2 (FST o SND) (FST o SND);
   Δ1 = sum_CASE a1 (FST o SND o SND o SND o SND) (FST o SND o SND o SND o SND);
   Δ2 = sum_CASE a2 (FST o SND o SND o SND o SND) (FST o SND o SND o SND o SND);
   Γ1 = sum_CASE a1 (FST o SND o SND o SND o SND o SND) (FST o SND o SND o SND o SND o SND);
   Γ2 = sum_CASE a2 (FST o SND o SND o SND o SND o SND) (FST o SND o SND o SND o SND o SND);
 in
   if ctxt1 = ctxt2 /\ upd1 = upd2
   /\ mem1 = mem2 /\ ind1 = ind2 /\ terminating(subst_clos(dependency (upd2::ctxt2)))
   /\ Δ1 = Δ2 /\ Γ1 = Γ2
   then
     case (a1,a2) of
     | (INL(_,_,_,_,_,_,typ1),INL(_,_,_,_,_,_,typ2)) => (subst_clos (dependency (upd2::ctxt2)))⁺ (INL typ2) (INL typ1)
     | (INL(_,_,_,_,_,_,typ1),INR(_,_,_,_,_,_,c2,typ2)) => (subst_clos (dependency (upd2::ctxt2)))⁺ (INR(Const c2 typ2)) (INL typ1)
     | (INR(_,_,_,_,_,_,c1,typ1),INL(_,_,_,_,_,_,typ2)) => (subst_clos (dependency (upd2::ctxt2)))⁺ (INL typ2) (INR(Const c1 typ1))
     | (INR(_,_,_,_,_,_,c1,typ1),INR(_,_,_,_,_,_,c2,typ2)) => (subst_clos (dependency (upd2::ctxt2)))⁺ (INR(Const c2 typ2)) (INR(Const c1 typ1))
   else F
End

val select_ax = EVAL ``HD(mk_select_ctxt ARB)`` |> concl |> rhs

val select_ty = EVAL ``HD(TL(mk_select_ctxt ARB))`` |> concl |> rhs |> rand

val infinity_ax = EVAL ``HD(mk_infinity_ctxt ARB)`` |> concl |> rhs

val onto_conext = EVAL ``conexts_of_upd(EL 2 (mk_infinity_ctxt ARB))`` |> concl |> rhs

val one_one_conext = EVAL ``conexts_of_upd(EL 3 (mk_infinity_ctxt ARB))`` |> concl |> rhs

(* construction of the model extension basing on the independent fragment *)

val type_interpretation_ext_of_def =
  tDefine "type_interpretation_ext_of0" `
  (type_interpretation_ext_of0
   ^mem ind upd ctxt Δ (Γ :mlstring # type -> 'U) ty =
   if ~terminating(subst_clos (dependency (upd::ctxt))) then
     One:'U
   else if ~(orth_ctxt (upd::ctxt) /\ extends_init (upd::ctxt)) then
     One:'U
   else if ty ∈ FST (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt)))) ∧
           (∀tm. upd ≠ NewAxiom tm) then
    Δ ty
   else
     case mapPartial (type_matches ty) (upd::ctxt) of
     | [] =>
       if ty = Tyapp (strlit "ind") [] then
         ind
       else
         One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let pty = domain(typeof pred);
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty).
                      if (c,ty) ∈ inst_consts then
                        term_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ c ty
                      else One);
                δ = (λty.
                       if MEM ty (allTypes' (TYPE_SUBST sigma pty)) then
                         type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty
                       else One);
                atys = MAP (TYPE_SUBST sigma) (allTypes pred);
                δ' = (λty.
                       if MEM ty(FLAT (MAP allTypes' atys)) then
                         type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty
                       else One);
                tst = termsem (ext_type_frag_builtins δ')
                              (ext_term_frag_builtins
                                (ext_type_frag_builtins δ')
                                γ)
                              empty_valuation
                              sigma'
                              pred
            in
              if ?tm.
                  tm ⋲
                  (ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)) then
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)
              else
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (term_interpretation_ext_of0
   ^mem ind upd ctxt Δ (Γ :mlstring # type -> 'U) (name:mlstring) ty =
   if ~terminating(subst_clos (dependency (upd::ctxt))) then
     One:'U
   else if ~(orth_ctxt (upd::ctxt) /\ extends_init (upd::ctxt)) then
     One:'U
   else if ((name,ty) ∈ SND (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt))))) ∧
           (∀tm. upd ≠ NewAxiom tm) then
     Γ (name,ty)
   else
     case FILTER ($<> []) (MAP (defn_matches name ty) (upd::ctxt)) of
       [] =>
       (case mapPartial (abs_or_rep_matches name ty) (upd::ctxt) of
        | [(is_abs,name0,abs_type,rep_type)] =>
          (let cty = if is_abs then Fun rep_type abs_type else Fun abs_type rep_type
           in
             case instance_subst [(ty, cty)] [] [] of
             | SOME(sigma,e) =>
               let
                 δ = (λty.
                         if MEM ty (allTypes' (TYPE_SUBST sigma cty)) then
                           type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty
                         else One);
                 sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
               in
                 if is_abs then
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (λv. if v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type) then
                                   v
                                 else
                                   @v. v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                 else
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            I
             | NONE => One (* cannot happen *))
        | _ =>
          (if term_ok (sigof (upd::ctxt)) (Const name ty) then
             let δ = (λty'.
                         if MEM ty' (allTypes' ty) then
                           type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty'
                         else One)
             in
               if name = strlit "@" /\ MEM ^select_ax (upd::ctxt) /\
                  FLOOKUP (tmsof (upd::ctxt)) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool)) /\
                  FLOOKUP (tmsof (upd::ctxt)) (strlit "@") = SOME(^select_ty)
                then
                 Abstract (ext_type_frag_builtins δ (domain ty))
                          (ext_type_frag_builtins δ (codomain ty))
                          (λp.
                            case some x. x <: (ext_type_frag_builtins δ (codomain ty)) ∧
                                         p ' x = True of
                              NONE => (@x. x <: ext_type_frag_builtins δ (codomain ty))
                            | SOME v => v
                          )
               else
                 @v. v <: ext_type_frag_builtins δ ty
           else One
          )
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let
             pty = domain(typeof trm0);
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty).
                   if (c,ty) ∈ inst_consts then
                     term_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ c ty
                   else One);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = (λty.
                    if MEM ty(FLAT (MAP allTypes' atys)) then
                      type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty
                    else One)
           in
             termsem (ext_type_frag_builtins δ)
                       (ext_term_frag_builtins
                         (ext_type_frag_builtins δ)
                         γ)
                       empty_valuation
                       sigma'
                       trm0
         | NONE => One (* cannot happen *)
  )`
(
  wf_rel_tac `subst_clos_term_ext_rel`
  >- (
    rw[wellorderTheory.WF_IND,subst_clos_term_ext_rel_def,WF_TC_EQN] >>
    reverse(Cases_on `x`)
    >- (
      rename1 `INR args` >> PairCases_on `args`
      >> rename1 `(mem,ind,upd,ctxt,Δ,Γ,c,ty)`
      >> reverse(Cases_on `terminating(subst_clos(dependency (upd::ctxt)))`)
      >- (first_x_assum match_mp_tac >> simp[])
      >> drule terminating_IMP_wellfounded_INV
      >> strip_tac >> dxrule WF_TC
      >> simp[wellorderTheory.WF_IND]
      >> disch_then(qspec_then `λx. case x of INL ty => P(INL(mem,ind,upd,ctxt,Δ,Γ,ty))
                                          | INR(Const c ty) => P(INR(mem,ind,upd,ctxt,Δ,Γ,c,ty))
                                          | _ => T` mp_tac)
      >>  simp[]
      >> impl_tac
      >- (
          Cases >> rw[]
          >- (first_x_assum match_mp_tac >>
              Cases >> simp[] >>
              rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
              first_x_assum drule >> simp[]) >>
          TOP_CASE_TAC >> rw[] >>
          first_x_assum match_mp_tac >> Cases >> simp[] >>
          rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
          first_x_assum drule >> simp[]
      )
      >> disch_then(qspec_then `INR(Const c ty)` mp_tac)
      >> simp[]
    )
    >> rename1 `INL args` >> PairCases_on `args`
    >> rename1 `(mem,ind,upd,ctxt,Δ,Γ,ty)`
    >> reverse(Cases_on `terminating(subst_clos(dependency (upd::ctxt)))`)
    >- (first_x_assum match_mp_tac >> simp[]) >>
    drule terminating_IMP_wellfounded_INV >>
    strip_tac >> dxrule WF_TC >>
    simp[wellorderTheory.WF_IND] >>
    disch_then(qspec_then `λx. case x of INL ty => P(INL(mem,ind,upd,ctxt,Δ,Γ,ty))
                                      | INR(Const c ty) => P(INR(mem,ind,upd,ctxt,Δ,Γ,c,ty))
                                      | _ => T` mp_tac) >>
    simp[] >>
    impl_tac >-
      (Cases >> rw[] >-
          (first_x_assum match_mp_tac >>
          Cases >> simp[] >>
          rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
          first_x_assum drule >> simp[]) >>
        TOP_CASE_TAC >> rw[] >>
        first_x_assum match_mp_tac >> Cases >> simp[] >>
        rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
        first_x_assum drule >> simp[]) >>
    disch_then(qspec_then `INL ty` mp_tac) >>
    simp[]
  ) >>
    rpt conj_tac >> rpt gen_tac >>
    rpt(disch_then (MAP_EVERY assume_tac o CONJUNCTS))
    (* protect ext *)
    >> qabbrev_tac `ext = upd::ctxt`
    >- (
      qpat_x_assum ‘_ ∨ _’ kall_tac >>
      fs[subst_clos_term_ext_rel_def,subst_clos_def] >>
      drule instance_subst_soundness >> strip_tac >>
      rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
      rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
        fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
        rename1 `MEM ty1 (allTypes pred)` >>
        rename1 `MEM ty2 (allTypes' _)` >>
        Cases_on `ty2 = TYPE_SUBST sigma ty1` >-
          (
          match_mp_tac TC_SUBSET >>
            simp[subst_clos_def] >>
            CONV_TAC(RESORT_EXISTS_CONV rev) >>
            qexists_tac `sigma` >>
            qexists_tac `ty1` >>
            qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
            simp[] >>
            match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
            fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
            rveq >>
            fs[IS_SOME_EXISTS] >>
            fs[type_matches_def,CaseEq"update"] >>
            rveq >> fs[] >>
            reverse FULL_CASE_TAC >- metis_tac[] >>
            pop_assum kall_tac >>
            fs[] >>
            simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
            rveq >> simp[]) >>
        fs[extends_init_def] >>
        imp_res_tac allTypes'_subst_clos_dependency >>
        match_mp_tac(CONJUNCT2 (SPEC_ALL TC_RULES)) >>
        HINT_EXISTS_TAC >> simp[] >>
        match_mp_tac TC_SUBSET >>
        simp[subst_clos_def] >>
        CONV_TAC(RESORT_EXISTS_CONV rev) >>
        qexists_tac `sigma` >>
        qexists_tac `ty1` >>
        qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
        simp[] >>
        match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
        fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
        rveq >>
        fs[IS_SOME_EXISTS] >>
        fs[type_matches_def,CaseEq"update"] >>
        rveq >> fs[] >>
        reverse FULL_CASE_TAC >- metis_tac[] >>
        pop_assum kall_tac >>
        fs[] >>
        simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
        rveq >> simp[]
    )
    >- (
      qpat_x_assum ‘_ ∨ _’ kall_tac >>
      fs[subst_clos_term_ext_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       drule MEM_allTypes'_TYPE_SUBST_decompose >> strip_tac >>
       `MEM ty1 (allTypes pred)` by
         (fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
          rveq >>
          fs[IS_SOME_EXISTS] >>
          fs[type_matches_def,CaseEq"update"] >>
          rveq >> fs[] >>
          reverse FULL_CASE_TAC >- metis_tac[] >>
          pop_assum kall_tac >>
          fs[] >>
          rveq >>
          fs[extends_init_def] >>
          FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
          drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          dxrule extends_APPEND_NIL >> rw[] >>
          dxrule extends_NIL_CONS_updates >>
          rw[updates_cases] >>
          drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          rw[] >> dxrule extends_NIL_APPEND_extends >>
          strip_tac >>
          dxrule_then drule extends_proves >> strip_tac >>
          drule proves_term_ok >>
          drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
          PURE_REWRITE_TAC[APPEND_ASSOC] >>
          simp[] >>
          rw[term_ok_clauses] >>
          drule_then match_mp_tac (allTypes_typeof |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
          fs[allTypes'_defn]) >>
       Cases_on `ty'' = TYPE_SUBST sigma ty1` >-
         (match_mp_tac TC_SUBSET >>
          simp[subst_clos_def] >>
          CONV_TAC(RESORT_EXISTS_CONV rev) >>
          qexists_tac `sigma` >>
          qexists_tac `ty1` >>
          qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
          simp[] >>
          match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
          fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
          rveq >>
          fs[IS_SOME_EXISTS] >>
          fs[type_matches_def,CaseEq"update"] >>
          rveq >> fs[] >>
          reverse FULL_CASE_TAC >- metis_tac[] >>
          pop_assum kall_tac >>
          fs[] >>
          simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
          rveq >> simp[]) >>
       fs[extends_init_def] >>
       imp_res_tac allTypes'_subst_clos_dependency >>
       match_mp_tac(CONJUNCT2 (SPEC_ALL TC_RULES)) >>
       HINT_EXISTS_TAC >> simp[] >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       CONV_TAC(RESORT_EXISTS_CONV rev) >>
       qexists_tac `sigma` >>
       qexists_tac `ty1` >>
       qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
       simp[] >>
       match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[type_matches_def,CaseEq"update"] >>
       rveq >> fs[] >>
       reverse FULL_CASE_TAC >- metis_tac[] >>
       pop_assum kall_tac >>
       fs[] >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       rveq >> simp[]
      )
    >- (
      qpat_x_assum ‘_ ∨ _’ kall_tac >>
      fs[subst_clos_term_ext_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       `term_ok (sigof ext) pred`
         by(fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
            rveq >>
            fs[IS_SOME_EXISTS] >>
            fs[type_matches_def,CaseEq"update"] >>
            rveq >> fs[] >>
            reverse FULL_CASE_TAC >- metis_tac[] >>
            pop_assum kall_tac >>
            fs[] >>
            rveq >>
            fs[extends_init_def] >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            dxrule extends_APPEND_NIL >> rw[] >>
            dxrule extends_NIL_CONS_updates >>
            rw[updates_cases] >>
            drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            rw[] >> dxrule extends_NIL_APPEND_extends >>
            strip_tac >>
            dxrule_then drule extends_proves >> strip_tac >>
            drule proves_term_ok >>
            drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            PURE_REWRITE_TAC[APPEND_ASSOC] >>
            simp[] >>
            rw[term_ok_clauses]) >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
       qexists_tac `Const c ty'` >>
       qexists_tac `sigma` >>
       conj_tac >- simp[] >>
       conj_tac >- simp[INST_def,INST_CORE_def] >>
       match_mp_tac(List.nth(CONJUNCTS dependency_rules,3)) >>
       qexists_tac `name` >>
       qexists_tac `pred` >>
       imp_res_tac consts_of_term_nonbuiltin_allCInsts >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[type_matches_def,CaseEq"update"] >>
       rveq >> fs[] >>
       reverse FULL_CASE_TAC >- metis_tac[] >>
       pop_assum kall_tac >>
       fs[] >>
       rveq >>
       metis_tac[]
    )
    >- (
      qpat_x_assum ‘_ ∨ _’ kall_tac >>
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       fs[subst_clos_term_ext_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `MEM ty0 (allTypes _)` >>
       rename1 `MEM ty1 (allTypes' _)` >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND] >>
       rveq >> fs[] >>
       fs[defn_matches_def] >> FULL_CASE_TAC >> fs[] >>
       fs[FILTER_EQ_NIL,EXISTS_MEM] >>
       pairarg_tac >> rveq >> fs[] >> rveq >>
       `(name0,trm0) = (name,trm)`
         by(fs[orth_ctxt_def] >>
            first_x_assum(qspecl_then [`b`,`b`,`l`,`l`,`t`,`t`,`name0`,`name`,`trm0`,`trm`] mp_tac) >>
            simp[] >>
            qmatch_goalsub_abbrev_tac `FILTER af al` >>
            Cases_on `FILTER af al` >>
            fs[Abbr `af`,Abbr `al`,FILTER_EQ_NIL,FILTER_EQ_CONS,EVERY_MEM] >-
              (res_tac >> fs[] >> metis_tac[]) >>
            rveq >> fs[] >> fs[orth_ty_def,orth_ci_def] >> metis_tac[]) >>
       fs[] >> rveq >>
       `welltyped trm`
         by(fs[extends_init_def] >>
          FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
          drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          dxrule extends_APPEND_NIL >> rw[] >>
          dxrule extends_NIL_CONS_updates >>
          rw[updates_cases] >>
          drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          rw[] >> dxrule extends_NIL_APPEND_extends >>
          strip_tac >>
          dxrule_then drule extends_proves >> strip_tac >>
          drule proves_term_ok >>
          drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
          PURE_REWRITE_TAC[APPEND_ASSOC] >>
          simp[] >>
          fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
          rpt strip_tac >>
          first_x_assum dxrule >>
          simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL]) >>
       Cases_on `ty1 = TYPE_SUBST sigma ty0` >-
         (match_mp_tac TC_SUBSET >>
          simp[subst_clos_def] >>
          qexists_tac `ty0` >>
          qexists_tac `Const name (typeof trm)` >>
          qexists_tac `sigma` >>
          simp[INST_def,INST_CORE_def] >>
          qmatch_goalsub_abbrev_tac `Const name aty` >>
          match_mp_tac (List.nth(CONJUNCTS dependency_rules,1)) >>
          simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
          qunabbrev_tac `aty` >> metis_tac[welltyped_def,WELLTYPED_LEMMA]) >>
       match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
       qexists_tac `INL(TYPE_SUBST sigma ty0)` >>
       reverse conj_tac >-
         (match_mp_tac allTypes'_subst_clos_dependency >> fs[extends_init_def]) >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `ty0` >>
       qexists_tac `Const name (typeof trm)` >>
       qexists_tac `sigma` >>
       simp[INST_def,INST_CORE_def] >>
       qmatch_goalsub_abbrev_tac `Const name aty` >>
       match_mp_tac (List.nth(CONJUNCTS dependency_rules,1)) >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       qunabbrev_tac `aty` >> metis_tac[welltyped_def,WELLTYPED_LEMMA]
    )
    >- (qpat_x_assum ‘_ ∨ _’ kall_tac >>
       fs[subst_clos_term_ext_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `(c,ty0)` >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND] >>
       rveq >> fs[] >>
       fs[defn_matches_def] >> FULL_CASE_TAC >> fs[] >>
       fs[FILTER_EQ_NIL,EXISTS_MEM] >>
       pairarg_tac >> rveq >> fs[] >> rveq >>
       `(name0,trm0) = (name,trm)`
         by(fs[orth_ctxt_def] >>
            first_x_assum(qspecl_then [`b`,`b`,`l`,`l`,`t`,`t`,`name0`,`name`,`trm0`,`trm`] mp_tac) >>
            simp[] >>
            qmatch_goalsub_abbrev_tac `FILTER af al` >>
            Cases_on `FILTER af al` >>
            fs[Abbr `af`,Abbr `al`,FILTER_EQ_NIL,FILTER_EQ_CONS,EVERY_MEM] >-
              (res_tac >> fs[] >> metis_tac[]) >>
            rveq >> fs[] >> fs[orth_ty_def,orth_ci_def] >> metis_tac[]) >>
       fs[] >> rveq >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `Const name (typeof trm)` >>
       qexists_tac `Const c (ty0)` >>
       qexists_tac `sigma` >>
       simp[INST_def,INST_CORE_def] >>
       qmatch_goalsub_abbrev_tac `Const name ty1` >>
       qmatch_goalsub_abbrev_tac `Const c ty2` >>
       qmatch_asmsub_abbrev_tac `extends_init ctxt'` >>
       `term_ok (sigof ctxt') trm`
         by(fs[Abbr`ctxt'`,extends_init_def] >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            dxrule extends_APPEND_NIL >> rw[] >>
            dxrule extends_NIL_CONS_updates >>
            rw[updates_cases] >>
            drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            rw[] >> dxrule extends_NIL_APPEND_extends >>
            strip_tac >>
            dxrule_then drule extends_proves >> strip_tac >>
            drule proves_term_ok >>
            drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            PURE_REWRITE_TAC[APPEND_ASSOC] >>
            simp[] >>
            rw[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
            first_x_assum drule >> simp[term_ok_clauses]) >>
       qunabbrev_tac `ctxt'` >>
       imp_res_tac consts_of_term_nonbuiltin_allCInsts >>
       match_mp_tac(CONJUNCT1 dependency_rules) >>
       MAP_EVERY qunabbrev_tac [`ty1`,`ty2`] >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       metis_tac[term_ok_welltyped,WELLTYPED_LEMMA,welltyped_def]
    )
    >- (
    (* abs/rep case *)
       qpat_x_assum ‘_ ∨ _’ kall_tac >>
       simp[subst_clos_term_ext_rel_def] >>
       FULL_CASE_TAC >>
       fs[allTypes'_defn] >>
       drule MEM_allTypes'_TYPE_SUBST_decompose >> strip_tac >>
       imp_res_tac instance_subst_soundness >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `[(_,name0,abs_type,rep_type)]` >>
       fs[extends_init_def] >>
       imp_res_tac abs_or_rep_matches_abstype >>
       fs[] >> rveq >>
       qmatch_asmsub_abbrev_tac `MEM ty' (allTypes' aty)` >>
       ((* Same proof for 4 subcases (whether LHS is abs or rep, whether RHS is from abs or rep) *)
        Cases_on `ty' = aty` >>
        qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >-
          (match_mp_tac TC_SUBSET >>
           simp[subst_clos_def] >>
           qunabbrev_tac `aty` >>
           qmatch_goalsub_abbrev_tac `a1 = _` >>
           assume_tac (Q.REFL `a1:type`) >>
           qunabbrev_tac `a1` >>
           goal_assum dxrule >>
           Q.REFINE_EXISTS_TAC `Const name (Fun _ _)` >>
           simp[INST_def,INST_CORE_def] >>
           assume_tac (Q.REFL `absreptype:type`) >>
           qunabbrev_tac `absreptype` >>
           goal_assum dxrule >>
           qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >>
           match_mp_tac(List.nth(CONJUNCTS dependency_rules,6)) >>
           fs[Abbr `absreptype`] >>
           fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
           rveq >>
           fs[IS_SOME_EXISTS] >>
           fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
              rep_matches_def,CaseEq "update"] >> rveq >> fs[] >>
           rveq >> fs[] >> rfs[] >>
           FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           dxrule extends_APPEND_NIL >> rw[] >>
           dxrule extends_NIL_CONS_updates >>
           rw[updates_cases] >>
           fs[] >>
           (reverse FULL_CASE_TAC >- metis_tac[]) >>
           pop_assum kall_tac >>
           fs[] >>
           simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
           rveq >> fs[]) >>
        match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
        qexists_tac `INL aty` >>
        reverse conj_tac >-
          (match_mp_tac allTypes'_subst_clos_dependency >> simp[]) >>
        match_mp_tac TC_SUBSET >>
        simp[subst_clos_def] >>
        qunabbrev_tac `aty` >>
        qmatch_goalsub_abbrev_tac `a1 = _` >>
        assume_tac (Q.REFL `a1:type`) >>
        qunabbrev_tac `a1` >>
        goal_assum dxrule >>
        Q.REFINE_EXISTS_TAC `Const name (Fun _ _)` >>
        simp[INST_def,INST_CORE_def] >>
        assume_tac (Q.REFL `absreptype:type`) >>
        qunabbrev_tac `absreptype` >>
        goal_assum dxrule >>
        qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >>
        match_mp_tac(List.nth(CONJUNCTS dependency_rules,6)) >>
        fs[Abbr `absreptype`] >>
        fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
        rveq >>
        fs[IS_SOME_EXISTS] >>
        fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
           rep_matches_def,CaseEq "update"] >> rveq >> fs[] >>
        rveq >> fs[] >> rfs[] >>
        FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
        drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
        dxrule extends_APPEND_NIL >> rw[] >>
        dxrule extends_NIL_CONS_updates >>
        rw[updates_cases] >>
        fs[] >>
        (reverse FULL_CASE_TAC >- metis_tac[]) >>
        pop_assum kall_tac >>
        fs[] >>
        simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
        rveq >> fs[])) >-
      ((* abs or rep matches two distinct typedefs (impossible) *)
       qpat_x_assum ‘_ ∨ _’ kall_tac >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND,MAP_EQ_CONS] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
          rep_matches_def,CaseEq "update",CaseEq"bool"] >> rveq >> fs[] >>
       rveq >> fs[] >> rfs[] >>
       (rpt(reverse FULL_CASE_TAC >- metis_tac[])) >>
       rpt(PRED_ASSUM is_exists kall_tac) >>
       fs[] >> rveq >>
       fs[extends_init_def] >>
       qpat_x_assum `_ extends init_ctxt` assume_tac >>
       FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
       drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
       drule extends_APPEND_NIL >>
       rw[] >>
       dxrule extends_NIL_CONS_updates >>
       rw[updates_cases]
      ) >-
      ((* No definition matches (hence constant must have been declared with NewConst) *)
       qpat_x_assum ‘_ ∨ _’ kall_tac >>
       fs[term_ok_def] >>
       drule ALOOKUP_MEM >>
       rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       rename1 `consts_of_upd upd'` >>
       Cases_on `upd'` >> fs[] >-
         ((* upd is ConstSpec (impossible) *)
          ntac 2 (pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT])) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[FILTER_APPEND,CaseEq "bool",defn_matches_def] >>
          metis_tac[]) >-
         ((* upd is TypeDefn, const is abs (impossible) *)
          rveq >>
          pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT]) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[mllistTheory.mapPartial_thm,FILTER_APPEND,CaseEq "bool",abs_or_rep_matches_def,
             abs_matches_def,CaseEq"option",CaseEq"prod"] >>
          metis_tac[]) >-
         ((* upd is TypeDefn, const is rep (impossible) *)
          rveq >>
          pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT]) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[mllistTheory.mapPartial_thm,FILTER_APPEND,CaseEq "bool",abs_or_rep_matches_def,
             abs_matches_def,rep_matches_def,CaseEq"option",CaseEq"prod"] >>
          metis_tac[]
         ) >-
         ((* upd is NewConst (possible) *)
          rveq >>
          simp[subst_clos_term_ext_rel_def] >>
          rename1 `MEM ty0 (allTypes' (TYPE_SUBST i ty))` >>
          drule_then strip_assume_tac MEM_allTypes'_TYPE_SUBST_decompose >>
          `(subst_clos (dependency ext))⁺ (INR (Const m (TYPE_SUBST i ty)))
                                           (INL (TYPE_SUBST i ty1))`
            by(match_mp_tac TC_SUBSET >>
               simp[subst_clos_def] >>
               qexists_tac `ty1` >>
               qexists_tac `Const m ty` >>
               qexists_tac `i` >>
               simp[INST_def,INST_CORE_def] >>
               match_mp_tac(List.nth(CONJUNCTS dependency_rules,4)) >>
               simp[]) >>
          Cases_on `ty0 = TYPE_SUBST i ty1` >> simp[] >>
          match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
          goal_assum drule >>
          match_mp_tac allTypes'_subst_clos_dependency >>
          fs[extends_init_def]
         )
      )
  )

Overload type_interpretation_ext_of = ``type_interpretation_ext_of0 ^mem``
Overload term_interpretation_ext_of = ``term_interpretation_ext_of0 ^mem``

val type_interpretation_ext_of_ind = fetch "-" "type_interpretation_ext_of0_ind";

(* symbols from the independent fragment keeps their earlier interpretation *)

Theorem model_conservative_extension_prop:
  is_set_theory ^mem ⇒
    ∀ctxt upd Δ Γ ind. extends_init (upd::ctxt)
    ∧ inhabited ind
    ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
    ⇒
      (!c ty. (c,ty) ∈ SND (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt)))) ∧
          (∀tm. upd ≠ NewAxiom tm)
        ⇒ term_interpretation_ext_of ind upd ctxt Δ Γ c ty = Γ (c,ty))
      ∧
      (!ty. ty ∈ FST (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt)))) ∧
          (∀tm. upd ≠ NewAxiom tm)
        ⇒ type_interpretation_ext_of ind upd ctxt Δ Γ ty = Δ ty)
Proof
  rpt strip_tac
  >> fs[Once type_interpretation_ext_of_def]
  >> drule_then strip_assume_tac extends_init_NIL_orth_ctxt
  >> fs[extends_init_def]
  >> drule_then assume_tac extends_init_ctxt_terminating
  >> fs[]
QED

Theorem dependency_LHS_const:
  dependency ctxt (INR c) u ==>
  ?cn ty. c = Const cn ty
Proof
  rw[dependency_cases]
QED

(* This lemma could say more *)
Theorem MEM_ConstSpec_NewConst:
  ctxt extends [] /\ MEM (ConstSpec T cl prop) ctxt /\
  MEM (name,trm) cl ==>
  ∃ty'. MEM (NewConst name ty') ctxt
Proof
  rw[Once MEM_SPLIT] >> reverse(rw[MEM_MAP,PULL_EXISTS]) >>
  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
  dxrule extends_APPEND_NIL >> rw[] >>
  dxrule extends_NIL_CONS_updates >>
  rw[updates_cases,constspec_ok_def] >>
  res_tac >>
  metis_tac[]
QED

Theorem TypeDefn_NewConst_non_overlapping:
  MEM (TypeDefn tyname pred abs cn) ctxt
  /\ MEM (NewConst cn ty) ctxt
  /\ ctxt extends [] ==>
  F
Proof
  rpt strip_tac >>
  fs[MEM_SPLIT] >> rveq >> fs[APPEND_EQ_APPEND_MID] >> rveq >>
  fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
  qmatch_asmsub_abbrev_tac `a1 ++ a2 ++ a3` >>
  `a1 ++ a2 ++ a3 = a1 ++ (a2 ++ a3)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  unabbrev_all_tac >>
  drule extends_NIL_DISJOINT >>
  rw[]
QED

Theorem TypeDefn_ConstSpec_non_overlapping:
  MEM (ConstSpec ov cl prop) ctxt
  /\ MEM (cn,cdefn) cl
  /\ MEM (TypeDefn tyname pred abs cn) ctxt
  /\ ctxt extends [] ==>
  F
Proof
  rpt strip_tac >>
  Cases_on `ov` >-
    (drule_all_then strip_assume_tac MEM_ConstSpec_NewConst >>
     imp_res_tac TypeDefn_NewConst_non_overlapping) >>
  fs[MEM_SPLIT] >> rveq >> fs[APPEND_EQ_APPEND_MID] >> rveq >>
  fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
  qmatch_asmsub_abbrev_tac `a1 ++ a2 ++ a3` >>
  `a1 ++ a2 ++ a3 = a1 ++ (a2 ++ a3)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  unabbrev_all_tac >>
  drule extends_NIL_DISJOINT >>
  rw[]
QED

Theorem TypeDefn_unique:
  MEM (TypeDefn tyname pred abs cn) ctxt /\
  MEM (TypeDefn tyname pred' abs' cn') ctxt /\
  ctxt extends [] ==>
  pred = pred' /\ abs = abs' /\ cn = cn'
Proof
  rw[MEM_SPLIT] >>
  fs[APPEND_EQ_APPEND_MID] >> rveq >>
  fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
  qmatch_asmsub_abbrev_tac `a1 ++ a2 ++ a3` >>
  `a1 ++ a2 ++ a3 = a1 ++ (a2 ++ a3)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  unabbrev_all_tac >>
  drule extends_NIL_DISJOINT >>
  rw[]
QED

Theorem rep_dependency_through_abs_type:
  extends_init ctxt
  ∧ (subst_clos (dependency ctxt))⁺ (INR (Const rep (TYPE_SUBST sigma (Fun abs_type rep_type)))) u
  ∧ MEM (TypeDefn tyname pred abs rep) ctxt
  ∧ abs_type = Tyapp tyname (MAP Tyvar (mlstring_sort (tvars pred)))
  ∧ rep_type = domain (typeof pred)
  ==> (subst_clos (dependency ctxt))⃰ (INL (TYPE_SUBST sigma abs_type)) u
Proof
  rw[extends_init_def] >>
  fs[EXTEND_RTC_TC_EQN] >>
  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  rename1 `subst_clos _ (INR _) v` >>
  reverse(Cases_on `v`) >-
    (fs[subst_clos_def] >>
     rveq >>
     drule_then strip_assume_tac dependency_LHS_const >> rveq >>
     fs[EVAL ``INST sigma (Const a b)``] >>
     rveq >>
     fs[dependency_cases] >>
     imp_res_tac TypeDefn_ConstSpec_non_overlapping) >>
  fs[subst_clos_def] >>
  drule_then strip_assume_tac dependency_LHS_const >> rveq >>
  fs[EVAL ``INST sigma (Const a b)``] >>
  rveq >>
  fs[dependency_cases] >>
  TRY (imp_res_tac TypeDefn_ConstSpec_non_overlapping >> NO_TAC) >>
  TRY (imp_res_tac TypeDefn_NewConst_non_overlapping >> NO_TAC) >>
  rveq >> fs[] >-
    (Cases_on `name = tyname` >-
       (rveq >> imp_res_tac TypeDefn_unique >> rveq >> fs[] >>
        qpat_x_assum `MEM _ ctxt` mp_tac >>
        rw[MEM_SPLIT] >>
        FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
        drule_then strip_assume_tac extends_APPEND_NIL >>
        fs[] >>
        drule extends_NIL_CONS_updates >>
        rw[updates_cases]) >>
     rpt(qpat_x_assum `MEM _ ctxt` mp_tac) >>
     qpat_x_assum `_ <> _` mp_tac >>
     qpat_x_assum `_ extends []` mp_tac >>
     rpt(pop_assum kall_tac) >>
     rpt strip_tac >>
     spose_not_then kall_tac >>
     fs[MEM_SPLIT] >>
     fs[APPEND_EQ_APPEND_MID] >> rveq >>
     fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
     qmatch_asmsub_abbrev_tac `a1 ++ a2 ++ a3` >>
     `a1 ++ a2 ++ a3 = a1 ++ (a2 ++ a3)` by simp[] >>
     pop_assum SUBST_ALL_TAC >>
     unabbrev_all_tac >>
     drule extends_NIL_DISJOINT >>
     rw[]) >-
    (Cases_on `name = tyname` >-
       (rveq >> imp_res_tac TypeDefn_unique >> rveq >> fs[] >>
        qpat_x_assum `MEM _ ctxt` mp_tac >>
        rw[MEM_SPLIT] >>
        FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
        drule_then strip_assume_tac extends_APPEND_NIL >>
        fs[] >>
        drule extends_NIL_CONS_updates >>
        rw[updates_cases]) >>
     rpt(qpat_x_assum `MEM _ ctxt` mp_tac) >>
     qpat_x_assum `_ <> _` mp_tac >>
     qpat_x_assum `_ extends []` mp_tac >>
     rpt(pop_assum kall_tac) >>
     rpt strip_tac >>
     spose_not_then kall_tac >>
     fs[MEM_SPLIT] >>
     fs[APPEND_EQ_APPEND_MID] >> rveq >>
     fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
     qmatch_asmsub_abbrev_tac `a1 ++ a2 ++ a3` >>
     `a1 ++ a2 ++ a3 = a1 ++ (a2 ++ a3)` by simp[] >>
     pop_assum SUBST_ALL_TAC >>
     unabbrev_all_tac >>
     drule extends_NIL_DISJOINT >>
     rw[]
    ) >-
    (rveq >>
     imp_res_tac TypeDefn_unique >> rveq >> fs[] >>
     rename1 `MEM t (allTypes' _)` >>
     `welltyped pred /\
      typeof pred = Fun (domain(typeof pred)) Bool`
       by(qpat_x_assum `MEM _ ctxt` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
          rveq >>
          FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
          drule_then strip_assume_tac extends_APPEND_NIL >>
          fs[] >>
          drule extends_NIL_CONS_updates >>
          rw[updates_cases] >>
          imp_res_tac proves_term_ok >> fs[] >>
          fs[Once has_type_cases] >>
          fs[welltyped_def] >>
          TRY(goal_assum drule) >>
          imp_res_tac WELLTYPED_LEMMA >>
          rw[]) >>
     `MEM t (allTypes' (typeof pred))` by(pop_assum(ONCE_REWRITE_TAC o single) >> fs[allTypes'_defn]) >>
     simp[Once RTC_CASES1] >> disj2_tac >>
     HINT_EXISTS_TAC >> simp[] >>
     simp[subst_clos_def] >>
     CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
     qexists_tac `sigma'` >>
     qexists_tac `t` >> simp[] >>
     qexists_tac `Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))` >>
     simp[] >>
     imp_res_tac(allTypes_typeof |> REWRITE_RULE[SUBSET_DEF]) >>
     match_mp_tac(List.nth(CONJUNCTS dependency_rules,2)) >>
     rpt(goal_assum drule) >>
     simp[])
QED

Theorem upd_introduces_introduced_before:
  MEM (INR (Const c ty)) (upd_introduces upd)
  ∧ extends_init (upd::ctxt)
  ∧ MEM (TypeDefn tyname pred abs c) ctxt
  ⇒ F
Proof
  rpt strip_tac >>
  `upd updates ctxt` by (
    drule_then assume_tac extends_init_NIL_orth_ctxt >>
    fs[extends_NIL_CONS_extends]
  ) >>
  `extends_init ctxt` by (
    fs[extends_init_def,extends_def] >>
    qpat_x_assum `RTC _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
    fs[] >>
    fs[init_ctxt_def]
  ) >>
  qpat_x_assum `MEM _ ctxt` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >>
  `IS_SUFFIX l2 init_ctxt` by (
    dxrule_then strip_assume_tac extends_init_IS_SUFFIX >>
    match_mp_tac IS_SUFFIX_APPEND_NOT_MEM >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM CONS_APPEND] >>
    goal_assum (first_assum o mp_then Any mp_tac) >>
    fs[init_ctxt_def]
  ) >>
  fs[updates_cases] >> rveq >>
  qpat_x_assum `MEM _ (upd_introduces _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP,upd_introduces_def]) >>
  fs[constspec_ok_def] >> pairarg_tac >>
  FULL_CASE_TAC >> fs[]
  >- (
    dxrule_then (assume_tac o CONJUNCT1) extends_init_NIL_orth_ctxt >>
    match_mp_tac (GEN_ALL TypeDefn_NewConst_non_overlapping) >>
    goal_assum (first_assum o mp_then Any mp_tac) >>
    res_tac >> rveq >>
    rename1`NewConst c typ` >>
    map_every qexists_tac [`tyname`,`typ`,`pred`,`c`,`abs`] >>
    fs[]
  ) >>
  imp_res_tac (Q.ISPEC `FST :mlstring # term -> mlstring ` MEM_MAP_f) >>
  res_tac >>
  fs[]
QED

Theorem interpretation_is_total_frag_interpretation_lemma:
  (∀^mem ind upd ctxt Δ Γ ty.
      is_set_theory ^mem ⇒
        orth_ctxt (upd::ctxt) /\ terminating(subst_clos (dependency (upd::ctxt)))
        ∧ ctxt extends [] /\ ctxt extends init_ctxt
        ∧ upd updates ctxt
        ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
        ∧ ty ∈ ground_types (sigof (upd::ctxt)) /\ inhabited ind /\
        ty ∈ nonbuiltin_types
    ⇒
        inhabited (type_interpretation_ext_of ind upd ctxt Δ Γ ty)) /\
  (∀^mem ind upd ctxt Δ Γ c ty.
     is_set_theory ^mem ⇒
        orth_ctxt (upd::ctxt) /\ terminating(subst_clos (dependency (upd::ctxt)))
        ∧ ctxt extends [] /\ ctxt extends init_ctxt
        ∧ upd updates ctxt
        ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
        ∧ (c,ty) ∈ ground_consts (sigof (upd::ctxt)) /\ inhabited ind
        /\ (c,ty) ∈ nonbuiltin_constinsts ⇒
        term_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ c ty ⋲
        ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt Δ Γ) ty
  )
Proof
  ho_match_mp_tac type_interpretation_ext_of_ind >> rpt strip_tac >>
  rename1 `elem ⋲ ind`
  >- (`upd::ctxt extends []` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                       simp[GSYM extends_def]) >>
      `upd::ctxt extends init_ctxt` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                       simp[GSYM extends_def]) >>
      FULL_SIMP_TAC std_ss [] >>
      rpt(qpat_x_assum `ctxt extends _` kall_tac) >>
      PURE_REWRITE_TAC[Once type_interpretation_ext_of_def] >>
      qmatch_asmsub_abbrev_tac `actxt extends []` >>
      simp[] >>
      IF_CASES_TAC >- rw[mem_one] >>
      TOP_CASE_TAC >-
        (unabbrev_all_tac >>
         drule_then strip_assume_tac (indep_frag_upd_frag_reduce |> SIMP_RULE std_ss [LET_THM]) >>
         fs[] >>
         dxrule_all_then strip_assume_tac SUBSET_IMP >>
         fs[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def]) >>
      TOP_CASE_TAC >- metis_tac[mem_one] >>
      reverse TOP_CASE_TAC >- rw[mem_one] >>
      qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “a1 = ^(concl thm)”) >>
      PairCases_on `h` >> rename1 `pred,ty',tvs` >>
      simp[] >>
      drule type_matches_is_instance' >>
      disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
      FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
      rveq >>
      fs[IS_SOME_EXISTS] >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
      drule_then assume_tac instance_subst_soundness >>
      fs[] >>
      rw[mem_sub] >>
      drule_then match_mp_tac inhabited_ext >>
      qexists_tac `set(allTypes' (TYPE_SUBST sigma (domain (typeof pred))))` >>
      conj_tac >- (match_mp_tac builtin_closure_allTypes >- rw[]) >>
      conj_tac >- (rw[SUBSET_DEF] >> imp_res_tac allTypes'_nonbuiltin) >>
      rw[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      reverse(rpt conj_tac) >- (imp_res_tac allTypes'_nonbuiltin) >- metis_tac[] >>
      match_mp_tac(TYPE_SUBST_allTypes'_ground_types' |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
      HINT_EXISTS_TAC >> rw[] >>
      fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >> rveq >> rfs[] >>
      fs[type_matches_def,CaseEq "update"] >> rveq >> fs[] >> rveq >>
      FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
      drule extends_APPEND_NIL >> rw[] >>
      dxrule extends_NIL_CONS_updates >>
      rw[updates_cases] >> rveq >> fs[] >>
      imp_res_tac proves_term_ok >>
      fs[] >>
      drule extends_append_MID >>
      impl_tac >- rw[init_ctxt_def] >>
      strip_tac >>
      dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
      fs[term_ok_clauses] >>
      simp[ground_types_def] >>
      reverse conj_tac >-
        (match_mp_tac type_ok_TYPE_SUBST_strong >>
         conj_tac
         >- (match_mp_tac type_ok_extend >>
             imp_res_tac term_ok_type_ok >>
             PURE_ONCE_REWRITE_TAC[CONJ_SYM] >>
             goal_assum drule >>
             rw[] >>
             match_mp_tac(CONJUNCT2 SUBMAP_FUNION_ID) >>
             drule extends_NIL_DISJOINT >>
             fs[])
         >- (rw[] >> fs[ground_types_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MAP_EQ_f] >>
             `MEM x (tvars pred)`
               by(match_mp_tac (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
                  fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
                  goal_assum drule >> fs[tyvars_def]) >>
             res_tac >>
             rfs[])) >>
      `!x. MEM x (tyvars (TYPE_SUBST sigma (typeof witness))) ==> F`
        suffices_by(Cases_on `tyvars(TYPE_SUBST sigma (typeof witness))` >>
                    fs[DISJ_IMP_THM,FORALL_AND_THM]) >>
      rpt strip_tac >>
      `MEM x (tyvars (TYPE_SUBST sigma (typeof pred)))`
        by(fs[tyvars_def]) >>
      fs[ground_types_def,tyvars_def] >>
      imp_res_tac FOLDR_LIST_UNION_empty' >>
      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
      fs[tyvars_TYPE_SUBST] >>
      fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
      qpat_x_assum `pred has_type typeof pred` assume_tac >>
      drule_all_then assume_tac (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
      res_tac >>
      fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      res_tac >> fs[]
     )
  >- (`upd::ctxt extends []` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                       simp[GSYM extends_def]) >>
      `upd::ctxt extends init_ctxt` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                       simp[GSYM extends_def]) >>
      FULL_SIMP_TAC std_ss [] >>
      rpt(qpat_x_assum `ctxt extends _` kall_tac) >>
      PURE_REWRITE_TAC[Once type_interpretation_ext_of_def] >>
      qmatch_asmsub_abbrev_tac `actxt extends []` >>
      simp[] >>
      IF_CASES_TAC >- fs[extends_init_def] >>
      TOP_CASE_TAC >-
        (
          qspecl_then [`ty`,`type_interpretation_ext_of ind upd ctxt Δ Γ`,`Δ`] mp_tac ext_type_frag_mono_eq >>
          impl_tac
          >- (
            rw[] >>
            unabbrev_all_tac >>
            drule (CONJUNCT2 (Ho_Rewrite.REWRITE_RULE[extends_init_def,PULL_EXISTS,FORALL_AND_THM,IMP_CONJ_THM] model_conservative_extension_prop)) >>
            SIMP_TAC(bool_ss)[AC CONJ_ASSOC CONJ_COMM] >>
            rpt (disch_then drule) >>
            disch_then match_mp_tac >>
            match_mp_tac indep_frag_upd_subst_clos_INR_INL >>
            goal_assum drule >>
            reverse conj_asm2_tac
            >- (
              fs[indep_frag_upd_def,indep_frag_def,total_fragment_def,ground_consts_def] >>
              reverse conj_tac
              >- imp_res_tac allTypes'_nonbuiltin >>
              drule ground_types_allTypes >>
              disch_then (qspec_then `upd::ctxt` assume_tac) >>
              fs[]
            ) >>
            drule constants_dependency >>
            disch_then match_mp_tac >>
            ONCE_REWRITE_TAC[GSYM ALOOKUP_EQ_FLOOKUP] >>
            fs[indep_frag_upd_def,indep_frag_def,total_fragment_def,term_ok_def,ground_consts_def,fmap_to_alist_to_fmap,Excl"ALOOKUP_EQ_FLOOKUP",is_instance_simps]
          ) >>
          unabbrev_all_tac >>
          drule_then strip_assume_tac (indep_frag_upd_frag_reduce |> SIMP_RULE std_ss [LET_THM]) >>
          fs[] >>
          dxrule_all_then strip_assume_tac SUBSET_IMP >>
          qpat_x_assum `FST _ ⊆ FST _` kall_tac >>
          fs[is_frag_interpretation_def,total_fragment_def,GSYM PFORALL_THM]
        ) >>
      reverse IF_CASES_TAC >- fs[ground_consts_def] >>
      TOP_CASE_TAC >-
        (TOP_CASE_TAC >-
           (reverse IF_CASES_TAC >-
              ((* Uninterpreted constant *)
               qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
               `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt Δ Γ) ty`
                 by(match_mp_tac ext_type_frag_mono_eq >>
                    rw[Abbr `σ`]) >>
               fs[] >>
               rpt(first_x_assum(drule_then assume_tac)) >>
               fs[ground_consts_def] >>
               `inhabited(ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt Δ Γ) ty)`
                 suffices_by metis_tac[] >>
               drule_then match_mp_tac (MP_CANON ext_inhabited_frag_inhabited') >>
               metis_tac[]) >>
            qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”) >>
            (* Hilbert choice *)
            fs[] >>
            fs[term_ok_def] >>
            simp[ext_type_frag_builtins_Fun] >>
            drule_then match_mp_tac abstract_in_funspace_matchable >>
            simp[] >>
            reverse CONJ_TAC >-
              (simp[allTypes'_defn] >>
               qmatch_goalsub_abbrev_tac `Funspace (Funspace a1 _) _ = Funspace (Funspace a2 _) _` >>
               `a1 = a2`
                 by(qunabbrev_tac `a1` >> qunabbrev_tac `a2` >>
                    match_mp_tac ext_type_frag_mono_eq >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[]
              ) >>
            rpt strip_tac >>
            drule_then drule in_funspace_abstract >>
            strip_tac >> rveq >>
            rw[some_def] >-
              (SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
            SELECT_ELIM_TAC >> simp[] >>
            drule_then match_mp_tac ext_inhabited_frag_inhabited >>
            qexists_tac `sigof actxt` >>
            conj_asm1_tac >-
              (fs[ground_types_def,ground_consts_def,tyvars_def,tvars_def,LIST_UNION_EQ_NIL] >>
               drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
               qpat_x_assum `type_ok _ _` mp_tac >>
               fs[type_ok_def]) >>
            rw[mem_one,allTypes'_defn] >>
            first_x_assum(match_mp_tac o MP_CANON) >>
            simp[allTypes'_defn] >>
            metis_tac[]) >>
         reverse TOP_CASE_TAC >-
           (reverse IF_CASES_TAC >-
              ((* Uninterpreted constant *)
               qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
               `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt Δ Γ) ty`
                 by(match_mp_tac ext_type_frag_mono_eq >>
                    rw[Abbr `σ`]) >>
               fs[] >>
               rpt(first_x_assum(drule_then assume_tac)) >>
               fs[ground_consts_def] >>
               `inhabited(ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt Δ Γ) ty)`
                 suffices_by metis_tac[] >>
               drule_then match_mp_tac (MP_CANON ext_inhabited_frag_inhabited') >>
               metis_tac[]) >>
            (* Hilbert choice *)
            qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”) >>
            fs[] >>
            fs[term_ok_def] >>
            simp[ext_type_frag_builtins_Fun] >>
            drule_then match_mp_tac abstract_in_funspace_matchable >>
            simp[] >>
            reverse CONJ_TAC >-
              (simp[allTypes'_defn] >>
               qmatch_goalsub_abbrev_tac `Funspace (Funspace a1 _) _ = Funspace (Funspace a2 _) _` >>
               `a1 = a2`
                 by(qunabbrev_tac `a1` >> qunabbrev_tac `a2` >>
                    match_mp_tac ext_type_frag_mono_eq >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[]
              ) >>
            rpt strip_tac >>
            drule_then drule in_funspace_abstract >>
            strip_tac >> rveq >>
            rw[some_def] >-
              (SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
            SELECT_ELIM_TAC >> simp[] >>
            drule_then match_mp_tac ext_inhabited_frag_inhabited >>
            qexists_tac `sigof actxt` >>
            conj_asm1_tac >-
              (fs[ground_types_def,ground_consts_def,tyvars_def,tvars_def,LIST_UNION_EQ_NIL] >>
               drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
               qpat_x_assum `type_ok _ _` mp_tac >>
               fs[type_ok_def]) >>
            rw[mem_one,allTypes'_defn] >>
            first_x_assum(match_mp_tac o MP_CANON) >>
            simp[allTypes'_defn] >>
            metis_tac[]) >>
         (* abs and rep *)
         PairCases_on `h` >>
         rename1 `(is_abs,name0,abs_type,rep_type)` >>
         rw[] >>
         MAP_FIRST drule [rep_matches_is_instance,abs_matches_is_instance] >>
         disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
         qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”) >>
         FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
         rveq >>
         fs[IS_SOME_EXISTS] >>
         rename1 `instance_subst _ _ _ = SOME result` >>
         Cases_on `result` >>
         rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
         drule_then assume_tac instance_subst_soundness >>
         fs[] >>
         simp[ext_type_frag_builtins_Fun] >>
         rveq >>
         qabbrev_tac `tyfrag = set(allTypes' (TYPE_SUBST sigma cty))` >>
         qmatch_goalsub_abbrev_tac `Abstract (ext_type_frag_builtins σ _) _ _ ⋲ Funspace (ext_type_frag_builtins σ' _) _` >>
         `ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = ext_type_frag_builtins σ' (TYPE_SUBST sigma abs_type)`
           by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`,Abbr`σ'`,allTypes'_defn] >> fs[]) >>
         `ext_type_frag_builtins σ (TYPE_SUBST sigma rep_type) = ext_type_frag_builtins σ' (TYPE_SUBST sigma rep_type)`
           by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`,Abbr`σ'`,allTypes'_defn] >> fs[]) >>
         ntac 2 (pop_assum(fn thm => SUBST_ALL_TAC thm >> mp_tac thm)) >>
         ntac 2 strip_tac >>
         drule_then match_mp_tac abstract_in_funspace
         >- ((* abs *)
             rw[] >>
             `inhabited(ext_type_frag_builtins σ' (TYPE_SUBST sigma abs_type))`
               suffices_by metis_tac[] >>
             drule_then match_mp_tac inhabited_ext >>
             qexists_tac `set(allTypes'(TYPE_SUBST sigma abs_type))` >>
             conj_tac >- (match_mp_tac builtin_closure_allTypes >> rw[]) >>
             conj_tac >- (rw[SUBSET_DEF] >> imp_res_tac allTypes'_nonbuiltin) >>
             rpt strip_tac >>
             first_x_assum(match_mp_tac o MP_CANON) >>
             simp[allTypes'_defn] >>
             reverse(rpt conj_tac) >- imp_res_tac allTypes'_nonbuiltin >- metis_tac[] >>
             fs[ground_consts_def] >>
             fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
             reverse conj_tac >- imp_res_tac allTypes'_type_ok >>
             imp_res_tac allTypes'_no_tyvars) >>
         (* rep *)
         rw[] >>
         drule abs_or_rep_matches_ext_type_frag_builtins >>
         disch_then drule >>
         disch_then(qspecl_then [`σ'`,`sigma`,`^mem`] SUBST_ALL_TAC) >>
         qunabbrev_tac `σ'` >>
         Cases_on `TYPE_SUBST sigma abs_type ∈
                   FST (indep_frag_upd actxt upd (total_fragment (sigof actxt))) ∧
                   ∀tm. upd ≠ NewAxiom tm
                  ` >-
           (
            CCONTR_TAC >>
            (* What wrecked the abbreviation? *)
            reverse(qpat_x_assum ‘Abbrev (_ ∨ _)’ (strip_assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])) >-
              (rveq >> fs[]) >>
            qpat_x_assum ‘_ ∧ _’ strip_assume_tac >>
            qpat_x_assum `_ ∈ FST _` mp_tac >>
            fs[indep_frag_upd_def,indep_frag_def,DISJ_EQ_IMP] >>
            rw[] >>
            rfs[total_fragment_def] >>
            goal_assum drule >>
            `∃tyname abs pred. MEM (TypeDefn tyname pred abs c) actxt
              ∧ abs_type = Tyapp tyname (MAP Tyvar (mlstring_sort (tvars pred)))
              ∧ rep_type = domain (typeof pred) ` by (
                qpat_x_assum `mapPartial _ _ = _` (fn x => rpt (pop_assum kall_tac) >> assume_tac x) >>
                fs[abs_matches_def,abs_or_rep_matches_def,mllistTheory.mapPartial_thm,
                  FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
                fs[CaseEq"prod",CaseEq"option",CaseEq "update",rep_matches_def,mlstring_sort_def] >>
                rveq >> fs[] >> rveq >>
                map_every qexists_tac [`tyname`,`abs'`,`pred`] >> fs[]
            ) >>
            qpat_x_assum `RTC _ _ (LR_TYPE_SUBST _ _)` (assume_tac o REWRITE_RULE[RTC_CASES_TC]) >>
            fs[]
            >- (
              fs[Abbr`actxt`]
              >- (rveq >> fs[upd_introduces_def] >> rveq >> fs[LR_TYPE_SUBST_def]) >>
              Cases_on `u` >> fs[LR_TYPE_SUBST_def] >>
              rename1`Const c _ = INST s u` >>
              imp_res_tac upd_introduces_is_const_or_type >>
              fs[is_const_or_type_eq] >>
              rveq >> fs[INST_def,INST_CORE_def] >> rveq >>
              rename1`_ = TYPE_SUBST s ty` >>
              drule upd_introduces_introduced_before >>
              fs[DISJ_EQ_IMP] >>
              disch_then drule >>
              rw[] >>
              fs[]
            ) >>
            qspecl_then [`LR_TYPE_SUBST s u`,`tyname`,`sigma`,`rep_type`,`c`,`pred`,`actxt`,`abs_type`,`abs`] assume_tac
              (GEN_ALL rep_dependency_through_abs_type) >>
            rfs[] >>
            goal_assum drule
           ) >>
         qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”) >>
         qpat_x_assum `_ ⋲ _` (assume_tac o REWRITE_RULE[Once type_interpretation_ext_of_def]) >>
         Q.SUBGOAL_THEN `upd::ctxt = actxt` SUBST_ALL_TAC >- rw[Abbr`actxt`] >>
         rfs[] >>
         fs[] >> rfs[] >>
         drule_then (drule_then strip_assume_tac) abs_or_rep_matches_type_matches >>
         rveq >>
         qmatch_asmsub_abbrev_tac ‘if aaa then _ else _’ >>
         ‘~aaa’ by(fs[markerTheory.Abbrev_def]) >>
         qunabbrev_tac ‘aaa’ >>
         fs[IS_SOME_EXISTS] >>
         fs[mapPartial_APPEND,mllistTheory.mapPartial_def] >>
         rename1 `type_matches _ _ = SOME tymtch` >>
         PairCases_on `tymtch` >>
         fs[] >>
         drule type_matches_is_instance >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
         rveq >>
         fs[IS_SOME_EXISTS] >>
         rename1 `instance_subst _ _ _ = SOME result2` >>
         Cases_on `result2` >>
         rename1 `instance_subst _ _ _ = SOME(sigma',result2)` >>
         drule_then assume_tac instance_subst_soundness >>
         fs[] >>
         qpat_x_assum `x ⋲ if _ then _ else _` mp_tac >>
         IF_CASES_TAC >>
         rw[mem_sub] >>
         drule_all_then (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS) abs_or_rep_matches_type_matches' >>
         qpat_x_assum `x ⋲ ext_type_frag_builtins _ _` mp_tac >>
         simp[Abbr `σ`] >>
         `TYPE_SUBST sigma (domain (typeof tymtch0)) =
          TYPE_SUBST sigma' (domain (typeof tymtch0))
         `
           by(imp_res_tac instance_subst_soundness >>
              fs[] >>
              fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
              rw[TYPE_SUBST_tyvars] >>
              first_x_assum match_mp_tac >>
              match_mp_tac(tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
              FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
              drule extends_APPEND_NIL >>
              rw[] >>
              dxrule extends_NIL_CONS_updates >>
              rw[] >> fs[updates_cases,type_matches_def] >>
              rveq >> fs[] >>
              imp_res_tac proves_term_ok >>
              fs[] >>
              drule extends_append_MID >> (impl_tac >- rw[init_ctxt_def] >> strip_tac >>
              drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
              fs[term_ok_clauses] >>
              rveq >>
              fs[welltyped_def] >>
              asm_exists_tac >>
              imp_res_tac WELLTYPED_LEMMA >> rveq >>
              fs[tyvars_def])
             ) >>
         fs[] >>
         qmatch_goalsub_abbrev_tac `_ ⋲ ext_type_frag_builtins σ tt ==> _ ⋲ ext_type_frag_builtins σ' tt` >>
         `ext_type_frag_builtins σ tt = ext_type_frag_builtins σ' tt`
           suffices_by simp[] >>
         unabbrev_all_tac >>
         match_mp_tac ext_type_frag_mono_eq >>
         rw[MEM_MAP,MEM_FLAT,PULL_EXISTS]) >>
      qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”) >>
      fs[FILTER_EQ_CONS] >>
      rpt(pairarg_tac >> fs[] >> rveq) >>
      rename1 `HD ll` >> Cases_on `ll` >> fs[] >> rveq >>
      fs[MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >> fs[] >>
      qpat_x_assum `_ = defn_matches _ _ _` (assume_tac o GSYM) >>
      drule defn_matches_is_instance >>
      disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
      FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
      rveq >>
      fs[IS_SOME_EXISTS] >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
      drule_then assume_tac instance_subst_soundness >>
      fs[] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      drule_then (strip_assume_tac o REWRITE_RULE[APPEND]) extends_APPEND_NIL >>
      dxrule_then strip_assume_tac extends_NIL_CONS_updates >>
      drule_then (dxrule_then strip_assume_tac) defn_matches_wf >>
      fs[] >>
      dxrule_then (drule_then strip_assume_tac) term_ok_extends_APPEND >>
      rw[] >>
      simp[TYPE_SUBST_eq_TYPE_SUBSTf] >>
      qmatch_goalsub_abbrev_tac `termsem (ext_type_frag_builtins σ) (ext_term_frag_builtins (ext_type_frag_builtins σ) γ) _ _ _ ⋲ ext_type_frag_builtins σ' _` >>
      qabbrev_tac `tyfrag = set(FLAT(MAP allTypes' (MAP (TYPE_SUBST sigma) (allTypes trm0))))` >>
      qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                              ty' =
                              TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                              ty'' ∧ (c',ty'') ∈ consts_of_term trm0 ∧
                              (c',ty') ∈ nonbuiltin_constinsts}` >>
      qmatch_asmsub_abbrev_tac `orth_ctxt actxt` >>
      `is_sig_fragment (sigof actxt) (tyfrag,tmfrag)`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[is_sig_fragment_def]
           >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
               rw[ground_types_def] >-
                 (fs[ground_consts_def,ground_types_def] >>
                  drule allTypes_TYPE_SUBST_no_tyvars >>
                  rpt(disch_then drule) >> strip_tac >>
                  `!tv. MEM tv (tyvars x) ==> F`
                    suffices_by(Cases_on `tyvars x` >> fs[FORALL_AND_THM]) >>
                  rpt strip_tac >>
                  drule_all_then assume_tac MEM_tyvars_allTypes' >>
                  rfs[]) >>
               match_mp_tac allTypes'_type_ok >>
               goal_assum drule >>
               drule_all_then assume_tac allTypes_type_ok >>
               match_mp_tac type_ok_TYPE_SUBST_strong >>
               fs[] >> rw[] >>
               `type_ok (tysof actxt) (TYPE_SUBST sigma (typeof trm0))`
                 by(qunabbrev_tac `actxt` >> fs[ground_consts_def,term_ok_def] >> metis_tac[]) >>
               drule type_ok_TYPE_SUBST_imp >>
               drule_then (drule_then assume_tac) MEM_tyvars_allTypes >>
               rw[TYPE_SUBST_eq_TYPE_SUBSTf])
           >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
           >- (rw[SUBSET_DEF] >>
               simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
               match_mp_tac ground_consts_TYPE_SUBST_lemma >>
               rw[Abbr `actxt`])
           >- (rw[SUBSET_DEF] >> simp[])
           >- (
               match_mp_tac builtin_closure_allTypes''' >>
               rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
               drule_then (drule_then assume_tac) allTypes'_consts_of_term_IMP >>
               goal_assum drule >>
               rw[TYPE_SUBST_eq_TYPE_SUBSTf])
           ) >>
      `trm0 ∈ terms_of_frag_uninst (tyfrag,tmfrag) (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP]
           >- (rename1 `SND pp` >>
               qexists_tac `SND pp` >>
               rw[])
           >- rw[TYPE_SUBST_eq_TYPE_SUBSTf |> Q.GEN `ty` |> REWRITE_RULE[GSYM FUN_EQ_THM]]) >>
      `is_frag_interpretation (tyfrag,tmfrag) σ γ`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[is_frag_interpretation_def]
           >- (rw[is_type_frag_interpretation_def,Abbr `σ`,Abbr `σ'`,Abbr `actxt`] >>
               rfs[] >>
               first_x_assum(match_mp_tac o MP_CANON) >>
               simp[] >>
               reverse(rpt conj_tac) >-
                 (fs[MEM_FLAT,MEM_MAP] >> rveq >> imp_res_tac allTypes'_nonbuiltin) >-
                 (metis_tac[]) >>
               fs[ground_types_def] >>
               reverse conj_tac >-
                 (fs[MEM_FLAT,MEM_MAP] >> rveq >>
                  match_mp_tac allTypes'_type_ok >>
                  goal_assum drule >>
                  fs[ground_consts_def] >>
                  match_mp_tac type_ok_TYPE_SUBST_strong >>
                  conj_tac >-
                    (drule_then drule allTypes_type_ok >> rw[]) >>
                  fs[term_ok_def] >>
                  rpt strip_tac >>
                  drule_all_then strip_assume_tac MEM_tyvars_allTypes >>
                  first_x_assum(drule_then strip_assume_tac) >>
                  drule_then drule type_ok_TYPE_SUBST_imp >>
                  simp[]) >>
               fs[MEM_FLAT,MEM_MAP] >> rveq >>
               match_mp_tac allTypes'_no_tyvars >> goal_assum drule >>
               fs[ground_consts_def,ground_types_def] >>
               match_mp_tac allTypes_TYPE_SUBST_no_tyvars >>
               goal_assum drule >> goal_assum drule >>
               first_x_assum MATCH_ACCEPT_TAC
               ) >>
           rw[GSYM PFORALL_THM,Abbr `γ`] >>
           reverse IF_CASES_TAC >-
             (fs[] >>
              pop_assum(qspec_then `ty''` assume_tac) >>
              rfs[] >>
              imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
           `ext_type_frag_builtins σ (TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) ty'')
            = ext_type_frag_builtins σ' (TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) ty'')`
              by(pop_assum kall_tac >>
                 match_mp_tac ext_type_frag_mono_eq'' >>
                 rw[Abbr `σ`] >>
                 fs[MEM_FLAT,MEM_MAP,PULL_FORALL] >> rveq >>
                 fs[GSYM(IMP_DISJ_THM |> ONCE_REWRITE_RULE[DISJ_SYM]),PULL_FORALL] >>
                 fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                 drule_then(drule_then assume_tac) allTypes'_consts_of_term_IMP >>
                 first_assum drule >> rw[]) >>
           pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
           first_x_assum(match_mp_tac o MP_CANON) >>
           simp[] >>
           conj_tac >- metis_tac[nonbuiltin_constinsts_TYPE_SUBSTf,TYPE_SUBST_eq_TYPE_SUBSTf] >>
           simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
           reverse conj_tac >- metis_tac[] >>
           match_mp_tac(ground_consts_TYPE_SUBST_lemma) >>
           rw[] >>
           fs[Abbr `actxt`]
           ) >>
      `is_frag_interpretation (tyfrag,tmfrag) σ' γ`
        by(fs[Abbr `σ`] >> metis_tac[is_frag_intepretation_ifE]) >>
      `termsem (ext_type_frag_builtins σ)
          (ext_term_frag_builtins (ext_type_frag_builtins σ) γ)
          empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) trm0 =
       termsem (ext_type_frag_builtins σ')
          (ext_term_frag_builtins (ext_type_frag_builtins σ') γ)
          empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) trm0
      `
       by(match_mp_tac fleq_term_interp_le_closed >>
          ntac 2 (qexists_tac `(tyfrag,tmfrag)`) >>
          qexists_tac `sigof actxt` >>
          conj_tac >- rw[fleq_def,Abbr `σ`,Abbr `σ'`] >>
          rw[]) >>
      pop_assum SUBST_ALL_TAC >>
      match_mp_tac termsem_in_type_ext >>
      MAP_EVERY qexists_tac [`tyfrag`,`tmfrag`,`sigof actxt`] >>
      rw[] >> rfs[CLOSED_def])
QED

(* type_interpretation_ext_of_def gives a model *)

Theorem model_conservative_extension:
  is_set_theory ^mem ⇒
    ∀ctxt upd Δ Γ ind. ctxt extends init_ctxt /\ inhabited ind
    ∧ upd updates ctxt
    ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
    ⇒
        is_frag_interpretation (total_fragment (sigof (upd::ctxt)))
          (type_interpretation_ext_of ind upd ctxt Δ Γ)
          (UNCURRY (term_interpretation_ext_of ind upd ctxt Δ Γ))
Proof
  rw[]
  >> ‘ctxt extends []’ by(drule_then match_mp_tac extends_trans >> simp[init_ctxt_extends])
  >> ‘orth_ctxt (upd::ctxt)’
    by(match_mp_tac update_ctxt_orth >> simp[] >>
       imp_res_tac(extends_init_NIL_orth_ctxt |> REWRITE_RULE[extends_init_def]))
  >> ‘terminating(subst_clos (dependency (upd::ctxt)))’
    by(match_mp_tac updates_preserves_terminating >> simp[] >>
       conj_tac >- (metis_tac[is_std_sig_extends,is_std_sig_init]) >>
       match_mp_tac extends_init_ctxt_terminating >> simp[extends_init_def])
  >> rw[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def,GSYM PFORALL_THM]
  >- (
    drule (CONJUNCT1 interpretation_is_total_frag_interpretation_lemma)
    >> rpt(disch_then drule)
    >> fs[]
    >> rpt(disch_then drule)
    >> disch_then match_mp_tac
    >> asm_rewrite_tac[]
    >> goal_assum drule
  )
  >> drule (CONJUNCT2 interpretation_is_total_frag_interpretation_lemma)
  >> rpt(disch_then drule)
  >> fs[]
  >> rpt(disch_then drule)
  >> disch_then match_mp_tac
  >> asm_rewrite_tac[]
  >> goal_assum drule
QED

Theorem interpretation_is_total_frag_interpretation:
  is_set_theory ^mem ⇒
    ∀ctxt. orth_ctxt(upd::ctxt) /\ terminating(subst_clos (dependency(upd::ctxt))) /\ ctxt extends [] /\ ctxt extends init_ctxt /\ inhabited ind ∧ upd updates ctxt ∧
        is_frag_interpretation (total_fragment (sigof ctxt))
          Δ Γ
    ⇒
        is_frag_interpretation (total_fragment (sigof(upd::ctxt)))
          (type_interpretation_ext_of ind upd ctxt Δ Γ)
          (UNCURRY (term_interpretation_ext_of ind upd ctxt Δ Γ))
Proof
  rw[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def,
     GSYM PFORALL_THM] >>
  MAP_FIRST (match_mp_tac o MP_CANON) (CONJUNCTS interpretation_is_total_frag_interpretation_lemma) >>
  rw[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def,
     GSYM PFORALL_THM] >>
  metis_tac[]
QED

(* TODO: can we state this with less typing? *)
Theorem type_interpretation_ext_of_alt:
  (!^mem ind ctxt ty Δ Γ. is_set_theory ^mem /\ ctxt extends init_ctxt /\
                  is_frag_interpretation (total_fragment(sigof ctxt))
                   (type_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)
                   (UNCURRY (term_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)) /\
                  ty ∈ ground_types (sigof ctxt) /\
                  ty ∈ nonbuiltin_types ∧ ctxt ≠ []
   ==> type_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else if ty ∈ FST (indep_frag_upd ctxt (HD ctxt) (total_fragment (sigof ctxt))) ∧
           (∀tm. HD ctxt ≠ NewAxiom tm) then
     Δ ty
   else
     case mapPartial (type_matches ty) ctxt of
     | [] =>
       if ty = Tyapp (strlit "ind") [] then
         ind
       else
         One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let pty = domain(typeof pred);
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty). term_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ c ty);
                δ = type_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ;
                tst = termsem (ext_type_frag_builtins δ)
                              (ext_term_frag_builtins
                                (ext_type_frag_builtins δ)
                                γ)
                              empty_valuation
                              sigma'
                              pred
            in
              if ?tm.
                  tm ⋲
                  (ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)) then
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)
              else
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (!^mem ind ctxt name ty Δ Γ.
   is_set_theory ^mem /\ ctxt extends init_ctxt /\
   (name,ty) ∈ ground_consts (sigof ctxt) /\
   (name,ty) ∈ nonbuiltin_constinsts /\
   inhabited ind ∧ ctxt ≠ [] ∧
   is_frag_interpretation (total_fragment(sigof ctxt))
     (type_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)
     (UNCURRY (term_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)) ==>
   term_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ (name:mlstring) ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else if (name,ty) ∈ SND (indep_frag_upd ctxt (HD ctxt) (total_fragment (sigof ctxt))) ∧
           (∀tm. HD ctxt ≠ NewAxiom tm) then
     Γ (name,ty)
   else
     case FILTER ($<> []) (MAP (defn_matches name ty) ctxt) of
       [] =>
       (case mapPartial (abs_or_rep_matches name ty) ctxt of
        | [(is_abs,name0,abs_type,rep_type)] =>
          (let cty = if is_abs then Fun rep_type abs_type else Fun abs_type rep_type
           in
             case instance_subst [(ty, cty)] [] [] of
             | SOME(sigma,e) =>
               let
                 δ = type_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ;
                 sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
               in
                 if is_abs then
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (λv. if v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type) then
                                   v
                                 else
                                   @v. v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                 else
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            I
             | NONE => One (* cannot happen *))
        | _ =>
          let δ = type_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ in
            if name = strlit "@" /\ MEM ^select_ax ctxt /\
               FLOOKUP (tmsof ctxt) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool)) /\
               FLOOKUP (tmsof ctxt) (strlit "@") = SOME(^select_ty)
             then
              Abstract (ext_type_frag_builtins δ (domain ty))
                       (ext_type_frag_builtins δ (codomain ty))
                       (λp.
                         case some x. x <: (ext_type_frag_builtins δ (codomain ty)) ∧
                                      p ' x = True of
                           NONE => (@x. x <: ext_type_frag_builtins δ (codomain ty))
                         | SOME v => v
                       )
            else
              @v. v <: ext_type_frag_builtins δ ty
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let
             pty = domain(typeof trm0);
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty). term_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ c ty);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = type_interpretation_ext_of0 ^mem ind (HD ctxt) (TL ctxt) Δ Γ
           in
             termsem (ext_type_frag_builtins δ)
                       (ext_term_frag_builtins
                         (ext_type_frag_builtins δ)
                         γ)
                       empty_valuation
                       sigma'
                       trm0
         | NONE => One (* cannot happen *)
  )
Proof
  rpt strip_tac >>
  (Cases_on ‘ctxt’ >- rw[]) >>
  PURE_REWRITE_TAC[HD,TL] >>
  rename1 ‘type_interpretation_ext_of ind upd ctxt’ >>
  CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV[type_interpretation_ext_of_def])) >>
  (IF_CASES_TAC >- rw[]) >>
  (IF_CASES_TAC >- (fs[extends_init_def,ground_consts_def] >> fs[])) >>
  (IF_CASES_TAC >- rw[]) >>
  qpat_assum ‘~(_ ∧ (∀tm. upd ≠ NewAxiom tm))’ (fn thm => ABBREV_TAC “aaa = ^(concl thm)”)
  >-
    ((* type interpretation *)
     qpat_abbrev_tac ‘a1 = upd::ctxt’ >>
     rename1 ‘a1 = upd::ctxt'’ >>
     rename1 ‘ctxt = upd::ctxt'’ >>
     ntac 6 (TOP_CASE_TAC >> fs[] >> rveq) >>
     drule_then assume_tac instance_subst_soundness >>
     simp[mem_sub] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins σ') γ` >>
     rename1 `TYPE_SUBST sigma (domain (typeof pred))` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma (domain (typeof pred))) =
      ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ) (TYPE_SUBST sigma (domain (typeof pred)))
     `
       by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`]) >>
     simp[] >>
     `termsem (ext_type_frag_builtins σ')
                 (ext_term_frag_builtins (ext_type_frag_builtins σ') γ)
                 empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                 pred =
      termsem (ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ))
                 (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ))
                                         (UNCURRY(term_interpretation_ext_of ind upd ctxt' Δ Γ)))
                 empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                 pred
     `
      by(match_mp_tac fleq_term_interp_le_closed >>
         qabbrev_tac `tyfrag = set(FLAT (MAP allTypes'(MAP (TYPE_SUBST sigma) (allTypes pred))))` >>
         qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                                 ty' = TYPE_SUBST sigma ty'' ∧ (c',ty'') ∈ consts_of_term pred ∧
                                 (c',ty') ∈ nonbuiltin_constinsts}` >>
         ntac 2(qexists_tac `(tyfrag,tmfrag)`) >>
         qexists_tac `sigof ctxt` >>
         conj_tac >- (rw[fleq_def,Abbr `σ'`,Abbr`tmfrag`,Abbr `γ`] >> rw[] >>
                      goal_assum kall_tac >>
                      fs[] >>
                      first_x_assum(qspec_then `ty''` mp_tac) >>
                      simp[] >>
                      fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                      imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
         conj_asm1_tac >-
           (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
            rw[is_sig_fragment_def] >>
            fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
            rveq >> fs[] >> rveq >> fs[] >>
            fs[type_matches_def] >>
            qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
            fs[CaseEq "update"] >> rveq >> fs[] >>
            fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
            drule extends_append_MID >>
            (impl_tac >- rw[init_ctxt_def]) >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            drule extends_APPEND_NIL >> simp[] >> strip_tac >>
            dxrule extends_NIL_CONS_updates >>
            simp[updates_cases] >> rpt strip_tac >> rveq >> fs[] >>
            `q' <> strlit "fun"`
              by(drule_then strip_assume_tac extends_appends >>
                 CCONTR_TAC >> fs[init_ctxt_def]) >>
            `q' <> strlit "bool"`
              by(drule_then strip_assume_tac extends_appends >>
                 CCONTR_TAC >> fs[init_ctxt_def]) >>
            simp[allTypes'_defn] >>
            imp_res_tac proves_term_ok >>
            fs[] >>
            drule extends_NIL_APPEND_extends >> strip_tac >>
            dxrule_then drule term_ok_extends >> strip_tac >>
            dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            fs[term_ok_clauses]
            >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
                rw[ground_types_def]
                >- (match_mp_tac allTypes'_no_tyvars >>
                    goal_assum drule >>
                    `!ty. MEM ty (tyvars (TYPE_SUBST sigma y')) ==> F`
                      suffices_by(Cases_on `tyvars (TYPE_SUBST sigma y')` >> fs[DISJ_IMP_THM,FORALL_AND_THM] >> fs[]) >>
                    rpt strip_tac >>
                    fs[tyvars_TYPE_SUBST] >>
                    drule_all_then assume_tac MEM_tyvars_allTypes >>
                    first_x_assum drule >> strip_tac >>
                    fs[ground_types_def,tyvars_def] >>
                    drule FOLDR_LIST_UNION_empty' >>
                    strip_tac >>
                    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
                drule_then match_mp_tac allTypes'_type_ok >>
                match_mp_tac type_ok_TYPE_SUBST_strong >>
                fs[term_ok_clauses] >>
                conj_tac >- (drule_then drule allTypes_type_ok >> simp[]) >>
                qpat_x_assum `_ ∈ ground_types _` assume_tac >>
                rpt strip_tac >>
                fs[ground_types_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                drule_then drule MEM_tyvars_allTypes >> strip_tac >>
                first_x_assum drule >>
                first_x_assum drule >>
                rw[])
            >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
            >- (rw[SUBSET_DEF] >>
                fs[ground_consts_def] >>
                conj_tac >-
                  (simp[ground_types_def] >>
                   conj_tac >-
                     (`!ty. MEM ty (tyvars (TYPE_SUBST sigma ty'')) ==> F`
                      suffices_by(Cases_on `tyvars (TYPE_SUBST sigma ty'')` >> fs[DISJ_IMP_THM,FORALL_AND_THM] >> fs[]) >>
                      rpt strip_tac >>
                      fs[tyvars_TYPE_SUBST] >>
                      drule_then drule consts_of_term_tyvars_tvars >>
                      fs[ground_types_def,tyvars_def] >>
                      drule FOLDR_LIST_UNION_empty' >>
                      strip_tac >>
                      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                      spose_not_then strip_assume_tac >>
                      ntac 2(first_x_assum drule) >> rpt strip_tac >>
                      fs[]) >>
                   drule_then drule consts_of_term_term_ok >>
                   strip_tac >>
                   drule (ONCE_REWRITE_RULE[CONJ_SYM] term_ok_type_ok) >>
                   impl_tac >- rfs[] >>
                   simp[] >>
                   strip_tac >>
                   drule_then match_mp_tac type_ok_TYPE_SUBST_strong >>
                   rpt strip_tac >>
                   drule_then drule consts_of_term_tyvars_tvars >>
                   strip_tac >>
                   fs[ground_types_def] >>
                   qpat_x_assum `type_ok _ (Tyapp _ _)` mp_tac >>
                   rw[type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
                drule_then drule consts_of_term_term_ok >>
                strip_tac >>
                fs[term_ok_def] >>
                reverse conj_tac >- (metis_tac[TYPE_SUBST_compose]) >>
                pop_assum(SUBST_ALL_TAC o GSYM) >>
                drule_then match_mp_tac type_ok_TYPE_SUBST_strong >>
                rpt strip_tac >>
                drule_then drule consts_of_term_tyvars_tvars >>
                strip_tac >>
                fs[ground_types_def] >>
                qpat_x_assum `type_ok _ (Tyapp _ _)` mp_tac >>
                rw[type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS])
            >- (rw[SUBSET_DEF] >> rw[])
            >- (simp[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                match_mp_tac builtin_closure_allTypes''' >>
                rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
                drule_then drule allTypes'_consts_of_term_IMP >>
                metis_tac[TYPE_SUBST_eq_TYPE_SUBSTf])) >>
         conj_tac >-
           (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
            rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP,TYPE_SUBST_eq_TYPE_SUBSTf]
            >- (rename1 `SND pp` >> qexists_tac `SND pp` >> rw[])
            >- (fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,TYPE_SUBST_eq_TYPE_SUBSTf] >> metis_tac[])
            >- (fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
                rveq >> fs[] >> rveq >> fs[] >>
                fs[type_matches_def] >>
                qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
                fs[CaseEq "update"] >> rveq >> fs[] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                drule extends_append_MID >>
                (impl_tac >- rw[init_ctxt_def]) >>
                FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                drule extends_APPEND_NIL >> simp[] >> strip_tac >>
                dxrule extends_NIL_CONS_updates >>
                simp[updates_cases] >> rpt strip_tac >> rveq >> fs[] >>
                imp_res_tac proves_term_ok >>
                fs[] >>
                drule extends_NIL_APPEND_extends >> strip_tac >>
                dxrule_then drule term_ok_extends >> strip_tac >>
                dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
                drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
                fs[term_ok_clauses])) >>
           conj_tac >- simp[] >>
           conj_tac >-
             (qunabbrev_tac `σ'` >> qunabbrev_tac `γ` >>
              qmatch_goalsub_abbrev_tac `is_frag_interpretation _ _ γ'` >>
              `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_ext_of ind upd ctxt' Δ Γ c ty' else whatevz c ty')`
                by(qexists_tac `CURRY γ'` >>
                   rw[Abbr `γ'`] >> simp[FUN_EQ_THM] >> rpt strip_tac >>
                   IF_CASES_TAC >- rw[] >>
                   rw[Abbr `tmfrag`] >>
                   fs[] >>
                   rename1 `(_,tya) ∈ consts_of_term _` >>
                   goal_assum kall_tac >>
                   first_x_assum(qspec_then `tya` mp_tac) >>
                   rw[] >>
                   fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                   imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
              pop_assum SUBST_ALL_TAC >>
              pop_assum kall_tac >>
              match_mp_tac(GEN_ALL is_frag_intepretation_ifI) >>
              HINT_EXISTS_TAC >> simp[] >>
              Q.SUBGOAL_THEN ‘HD ctxt = upd’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
              Q.SUBGOAL_THEN ‘TL ctxt = ctxt'’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
              drule_then match_mp_tac is_frag_interpretation_mono >>
              strip_tac >> imp_res_tac total_fragment_is_top_fragment) >>
           fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
           rveq >> fs[] >> rveq >> fs[] >>
           fs[type_matches_def] >>
           qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
           fs[CaseEq "update"] >> rveq >> fs[] >>
           fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
           drule extends_append_MID >>
           (impl_tac >- rw[init_ctxt_def]) >>
           FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_APPEND_NIL >> simp[] >> strip_tac >>
           dxrule extends_NIL_CONS_updates >>
           simp[updates_cases] >> rpt strip_tac >> rveq >> fs[]) >>
     ntac 2 (pop_assum SUBST_ALL_TAC) >>
     simp[ELIM_UNCURRY]) >>
  qpat_abbrev_tac ‘a1 = upd::ctxt’ >>
  rename1 ‘a1 = upd::ctxt'’ >>
  rename1 ‘ctxt = upd::ctxt'’ >>
  TOP_CASE_TAC >-
    ((* Type definition matches (so const is abs/rep) *)
     TOP_CASE_TAC >-
       (reverse IF_CASES_TAC >- fs[ground_consts_def] >>
        simp[] >>
        reverse IF_CASES_TAC >-
         (simp[] >>
          qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
          `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ) ty`
            by(match_mp_tac ext_type_frag_mono_eq >>
               rw[Abbr `σ`]) >>
          simp[]) >>
        (* Hilbert choice *)
        fs[term_ok_def] >>
        simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
        qmatch_goalsub_abbrev_tac `ext_type_frag_builtins δ` >>
        `ext_type_frag_builtins δ (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» )) =
         ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ)
                                (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» ))`
          by(match_mp_tac ext_type_frag_mono_eq >> rw[allTypes'_defn,Abbr`δ`]) >>
        pop_assum SUBST_ALL_TAC >>
        drule_then match_mp_tac abstract_eq >>
        rw[] >>
        rw[some_def] >> SELECT_ELIM_TAC >> simp[] >- metis_tac[] >>
        drule_then match_mp_tac ext_inhabited_frag_inhabited >>
        qexists_tac `sigof ctxt` >>
        conj_asm1_tac >-
          (fs[ground_consts_def,ground_types_def,LIST_UNION_EQ_NIL,
              term_ok_def,tyvars_def,type_ok_def] >>
           metis_tac[]) >>
        rw[] >>
        Q.SUBGOAL_THEN ‘HD ctxt = upd’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
        Q.SUBGOAL_THEN ‘TL ctxt = ctxt'’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
        fs[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def]) >>
     reverse TOP_CASE_TAC >-
       (reverse IF_CASES_TAC >- fs[ground_consts_def] >>
        simp[] >>
        reverse IF_CASES_TAC >-
         (simp[] >>
          qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
          `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ) ty`
            by(match_mp_tac ext_type_frag_mono_eq >>
               rw[Abbr `σ`]) >>
          simp[]) >>
        (* Hilbert choice *)
        fs[term_ok_def] >>
        simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
        qmatch_goalsub_abbrev_tac `ext_type_frag_builtins δ` >>
        `ext_type_frag_builtins δ (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» )) =
         ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ)
                                (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» ))`
          by(match_mp_tac ext_type_frag_mono_eq >> rw[allTypes'_defn,Abbr`δ`]) >>
        pop_assum SUBST_ALL_TAC >>
        drule_then match_mp_tac abstract_eq >>
        rw[] >>
        rw[some_def] >> SELECT_ELIM_TAC >> simp[] >- metis_tac[] >>
        drule_then match_mp_tac ext_inhabited_frag_inhabited >>
        qexists_tac `sigof ctxt` >>
        conj_asm1_tac >-
          (fs[ground_consts_def,ground_types_def,LIST_UNION_EQ_NIL,
              term_ok_def,tyvars_def,type_ok_def] >>
           metis_tac[]) >>
        rw[] >>
        Q.SUBGOAL_THEN ‘HD ctxt = upd’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
        Q.SUBGOAL_THEN ‘TL ctxt = ctxt'’ SUBST_ALL_TAC >- rw[Abbr ‘ctxt’] >>
        fs[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def]) >>
     simp[] >>
     ntac 5 TOP_CASE_TAC >>
     simp[allTypes'_defn] >>
     rename1 `TYPE_SUBST sigma` >>
     rename1 `(is_abs,_,abs_type,rep_type)` >> rw[] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma rep_type) = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ) (TYPE_SUBST sigma rep_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = ext_type_frag_builtins (type_interpretation_ext_of ind upd ctxt' Δ Γ) (TYPE_SUBST sigma abs_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     ntac 2 (pop_assum SUBST_ALL_TAC) >> simp[]) >>
  (* Definition matches *)
  rename1 `elem ⋲ ind` >>
  fs[FILTER_EQ_CONS] >>
  rpt(pairarg_tac >> fs[] >> rveq) >>
  rename1 `HD ll` >> Cases_on `ll` >> fs[] >> rveq >>
  fs[MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >> fs[] >>
  qpat_x_assum `_ = defn_matches _ _ _` (assume_tac o GSYM) >>
  drule defn_matches_is_instance >>
  disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
  FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
  rveq >>
  fs[IS_SOME_EXISTS] >>
  rename1 `instance_subst _ _ _ = SOME result` >>
  Cases_on `result` >>
  rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
  drule_then assume_tac instance_subst_soundness >>
  fs[] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  drule_then (strip_assume_tac o REWRITE_RULE[APPEND]) extends_APPEND_NIL >>
  dxrule_then strip_assume_tac extends_NIL_CONS_updates >>
  drule_then (dxrule_then strip_assume_tac) defn_matches_wf >>
  fs[] >>
  dxrule_then (drule_then strip_assume_tac) term_ok_extends_APPEND >>
  rw[] >>
  qmatch_goalsub_abbrev_tac `termsem (ext_type_frag_builtins σ) (ext_term_frag_builtins (ext_type_frag_builtins σ) γ)` >>
  qabbrev_tac `tyfrag = set(FLAT(MAP allTypes' (MAP (TYPE_SUBST sigma) (allTypes trm0))))` >>
  qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                              ty' =
                              TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                              ty'' ∧ (c',ty'') ∈ consts_of_term trm0 ∧
                              (c',ty') ∈ nonbuiltin_constinsts}` >>
  drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
  match_mp_tac fleq_term_interp_le_closed >>
  ntac 2 (qexists_tac `(tyfrag,tmfrag)`) >>
  rename1 ‘type_interpretation_ext_of _ upd'’ >>
  rename1 `ctxt1 ++ [upd] ++ ctxt2` >>
  qexists_tac `sigof(ctxt1 ++ [upd] ++ ctxt2)` >>
  conj_tac >- (rw[fleq_def,Abbr `σ`,Abbr`tmfrag`,Abbr `γ`] >> rw[] >>
               goal_assum kall_tac >>
               fs[] >>
               first_x_assum(qspec_then `ty''` mp_tac) >>
               simp[] >>
               fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
               imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
  conj_asm1_tac >-
    (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
     rw[is_sig_fragment_def]
     >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
         rw[ground_types_def] >-
           (fs[ground_consts_def,ground_types_def] >>
            drule allTypes_TYPE_SUBST_no_tyvars >>
            rpt(disch_then drule) >> strip_tac >>
            `!tv. MEM tv (tyvars x) ==> F`
              suffices_by(Cases_on `tyvars x` >> fs[FORALL_AND_THM]) >>
            rpt strip_tac >>
            drule_all_then assume_tac MEM_tyvars_allTypes' >>
            rfs[]) >>
         match_mp_tac allTypes'_type_ok >>
         goal_assum drule >>
         drule_all_then assume_tac allTypes_type_ok >>
         match_mp_tac type_ok_TYPE_SUBST_strong >>
         fs[] >> rw[] >>
         fs[ground_consts_def] >>
         drule_then dxrule term_ok_type_ok >>
         drule_then dxrule term_ok_type_ok >>
         rw[] >>
         drule type_ok_TYPE_SUBST_imp >>
         simp[] >>
         disch_then match_mp_tac >>
         drule_then (drule_then assume_tac) MEM_tyvars_allTypes >>
         res_tac)
     >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
     >- (rw[SUBSET_DEF] >>
         simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
         match_mp_tac(GEN_ALL ground_consts_TYPE_SUBST_lemma) >>
         simp[] >>
         goal_assum drule >>
         simp[] >>
         rfs[])
     >- (rw[SUBSET_DEF] >> simp[])
     >- (
         match_mp_tac builtin_closure_allTypes''' >>
         rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
         drule_then (drule_then assume_tac) allTypes'_consts_of_term_IMP >>
         goal_assum drule >>
         rw[TYPE_SUBST_eq_TYPE_SUBSTf])) >>
  conj_tac >-
    (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
     rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP]
     >- (rename1 `SND pp` >>
         qexists_tac `SND pp` >>
         rw[])
     >- rw[TYPE_SUBST_eq_TYPE_SUBSTf |> Q.GEN `ty` |> REWRITE_RULE[GSYM FUN_EQ_THM]]) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qunabbrev_tac `σ` >> qunabbrev_tac `γ` >>
     qmatch_goalsub_abbrev_tac `is_frag_interpretation _ _ γ'` >>
     `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_ext_of ind upd' ctxt' Δ Γ c ty' else whatevz c ty')`
       by(qexists_tac `CURRY γ'` >>
          rw[Abbr `γ'`] >> simp[FUN_EQ_THM] >> rpt strip_tac >>
          IF_CASES_TAC >- rw[] >>
          rw[Abbr `tmfrag`] >>
          fs[] >>
          rename1 `(_,tya) ∈ consts_of_term _` >>
          goal_assum kall_tac >>
          first_x_assum(qspec_then `tya` mp_tac) >>
          rw[] >>
          fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
          imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
     pop_assum SUBST_ALL_TAC >>
     pop_assum kall_tac >>
     match_mp_tac(GEN_ALL is_frag_intepretation_ifI) >>
     HINT_EXISTS_TAC >> simp[] >>
     fs[markerTheory.Abbrev_def] >>
     rveq >>
     drule_then match_mp_tac is_frag_interpretation_mono >>
     strip_tac >> imp_res_tac total_fragment_is_top_fragment >> fs[] >>
     rveq >> fs[]
     ) >>
  fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
  rveq >> fs[] >> rveq >> fs[] >>
  fs[type_matches_def] >>
  fs[CaseEq "update"] >> rveq >> fs[] >>
  fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
  drule extends_append_MID >>
  (impl_tac >- rw[init_ctxt_def]) >>
  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  drule extends_APPEND_NIL >> simp[] >> strip_tac >>
  dxrule extends_NIL_CONS_updates >>
  simp[updates_cases] >> rpt strip_tac >> rveq >> fs[]
QED

Theorem is_sig_fragment_const_in_type_frag:
  ∀sig frag c ty ty'.
    is_sig_fragment sig frag ∧ (c,ty) ∈ SND frag ∧
    MEM ty' (allTypes' ty) ⇒
    ty' ∈ (FST frag)
Proof
  Cases_on ‘frag’ >> rw[is_sig_fragment_def,ground_consts_def] >> res_tac >>
  imp_res_tac allTypes'_builtin_closure_IMP
QED

val models_ConstSpec_witnesses_def = xDefine "models_ConstSpec_witnesses"`
  models_ConstSpec_witnesses0 ^mem (Δ:type->'U) (Γ :mlstring # type -> 'U) ctxt =
    ∀ov cl prop c cdefn ty sigma. MEM (ConstSpec ov cl prop) ctxt
    ∧ MEM (c,cdefn) cl
    ∧ ty = typeof cdefn
    ∧ (c, TYPE_SUBST sigma ty) ∈ ground_consts (sigof ctxt)
    ∧ (c, TYPE_SUBST sigma ty) ∈ nonbuiltin_constinsts
    ==> Γ (c, TYPE_SUBST sigma ty)
      = termsem (ext_type_frag_builtins Δ)
                (ext_term_frag_builtins (ext_type_frag_builtins Δ) Γ)
                empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) cdefn
`
Overload models_ConstSpec_witnesses = ``models_ConstSpec_witnesses0 ^mem``

Theorem models_ConstSpec_witnesses_model_ext:
  is_set_theory ^mem ⇒
    ∀ctxt. orth_ctxt(upd::ctxt)
      ∧ terminating(subst_clos (dependency(upd::ctxt)))
      ∧ ctxt extends [] /\ ctxt extends init_ctxt /\ inhabited ind ∧ upd updates ctxt
      ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
      ∧ models_ConstSpec_witnesses Δ Γ ctxt
    ⇒
      models_ConstSpec_witnesses
        (type_interpretation_ext_of ind upd ctxt Δ Γ)
        (UNCURRY (term_interpretation_ext_of ind upd ctxt Δ Γ))
        (upd::ctxt)
Proof
  rw[]
  >> drule model_conservative_extension
  >> rpt (disch_then drule)
  >> disch_then imp_res_tac
  >> rename1 `orth_ctxt (upd::ctxt)`
  >> `(upd::ctxt) extends init_ctxt` by (
    fs[extends_def] >> rw[Once RTC_CASES1]
  )
  >> qmatch_asmsub_abbrev_tac `orth_ctxt ctxt_ext`
  >> REWRITE_TAC[models_ConstSpec_witnesses_def]
  >> rw[]
  >> qmatch_goalsub_abbrev_tac `term_interpretation_ext_of _ _ _ _ _ c ty`
  >> drule (CONJUNCT2 type_interpretation_ext_of_alt)
  >> rpt(disch_then drule)
  >> `¬NULL ctxt_ext ∧ HD ctxt_ext = upd ∧ TL ctxt_ext = ctxt` by fs[Abbr`ctxt_ext`]
  >> ASM_REWRITE_TAC[GSYM NULL_EQ]
  >> disch_then imp_res_tac
  >> pop_assum (fn x => ONCE_REWRITE_TAC[x])
  >> TOP_CASE_TAC
  (* (c,ty) ∈ SND (indep_frag_upd _ _ _)*)
  >- (
    qunabbrev_tac `ctxt_ext` >> fs[]
    >- (
      fs[indep_frag_upd_def,indep_frag_def,DISJ_EQ_IMP]
      >> qpat_x_assum `!s u. MEM _ _ ⇒ _` (qspecl_then [`sigma`,`INR (Const c (typeof cdefn))`] assume_tac)
      >> rfs[LR_TYPE_SUBST_cases,upd_introduces_def]
      >> rveq
      >> fs[upd_introduces_def,MEM_MAP,DISJ_EQ_IMP]
    )
    >> drule_then (assume_tac o CONJUNCT2) (indep_frag_upd_frag_reduce |> SIMP_RULE std_ss [LET_THM,extends_init_def])
    >> dxrule SUBSET_IMP >> fs[] >> disch_then drule >> rw[total_fragment_def]
    >> qpat_x_assum `models_ConstSpec_witnesses _ _ _` (drule o REWRITE_RULE[models_ConstSpec_witnesses_def])
    >> unabbrev_all_tac
    >> disch_then drule >> rw[]
    >> cheat
  )
  >> cheat
QED

Theorem interpretation_models_axioms_lemma:
  is_set_theory ^mem ⇒
  ∀ctxt1 upd ctxt2 p Δ Γ.
    upd updates ctxt2 /\ theory_ok(thyof(ctxt1 ++ upd::ctxt2)) /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ upd::ctxt2)))
      (type_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ)
      (UNCURRY (term_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ)) /\
    is_sig_fragment (sigof (ctxt1 ++ upd::ctxt2)) (total_fragment (sigof (ctxt1 ++ upd::ctxt2))) /\
    ctxt2 extends init_ctxt /\
    ctxt1 ++ upd::ctxt2 extends init_ctxt /\
    is_std_sig (sigof(ctxt1 ++ upd::ctxt2)) /\
    is_std_sig (sigof(ctxt2)) /\
    inhabited ind /\
    (∀p. MEM (NewAxiom p) (upd::ctxt2) ⇒
          MEM (NewAxiom p) ctxt2 \/
          admissible_axiom mem ind upd ctxt2
    ) /\
    orth_ctxt (ctxt1 ++ upd::ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ upd::ctxt2))) /\
    (∀p. MEM p (axiom_list ctxt2) ==>
          satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))
             (UNCURRY (term_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))) ([],p)) /\
    models Δ Γ (thyof(TL((ctxt1 ++ upd::ctxt2)))) ∧
    models_ConstSpec_witnesses Δ Γ (ctxt1 ++ upd::ctxt2) ∧
    MEM p (axioms_of_upd upd)
    ==>
    satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_ext_of ind  (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))
             (UNCURRY (term_interpretation_ext_of ind (HD (ctxt1 ++ upd::ctxt2)) (TL (ctxt1 ++ upd::ctxt2)) Δ Γ))) ([],p)
Proof
  rw[updates_cases,axexts_of_upd_def,DISJ_IMP_THM] >>
  fs[axexts_of_upd_def] >> rveq
  >- ((* pre-existing axiom *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[])
  >- ((* new axiom *)
      rw[satisfies_t_def,satisfies_def] >>
      qmatch_goalsub_abbrev_tac ‘HD ctxt’ >>
      Cases_on ‘(∀c ty. MEM (Const c ty) (allCInsts p) ⇒ (c,TYPE_SUBSTf sigma ty) ∈ SND (indep_frag_upd ctxt (HD ctxt) (total_fragment (sigof ctxt)))) ∧
                (∀ty ty'. MEM ty (allTypes p) ∧ MEM ty' (allTypes'(TYPE_SUBSTf sigma ty)) ⇒ ty' ∈ FST (indep_frag_upd ctxt (HD ctxt) (total_fragment (sigof ctxt))))
               ∧ ∀tm. HD ctxt ≠ NewAxiom tm’
      >- (imp_res_tac terms_of_frag_uninst_welltyped >>
          qabbrev_tac ‘v2 = (λ(n,ty). if VFREE_IN (Var n ty) p then v(n,ty) else True)’ >>
          drule termsem_frees >>
          disch_then(qspecl_then [‘sigma’,‘mem’,‘δ’,‘γ’,‘v’,‘v2’] (dep_rewrite.DEP_ONCE_REWRITE_TAC o single)) >>
          conj_asm1_tac >- rw[Abbr ‘v2’] >>
          qabbrev_tac ‘sigma2 = (λn. if MEM n (tvars p) then sigma n else Bool)’ >>
          drule termsem_subst >>
          disch_then(qspec_then ‘sigma2’ mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
          disch_then(dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
          conj_asm1_tac >- rw[Abbr ‘sigma2’] >>
          qmatch_goalsub_abbrev_tac ‘ext_term_frag_builtins (ext_type_frag_builtins δ2) γ2’ >>
          ‘fleq (total_fragment(sigof(TL ctxt)),Δ,Γ) (total_fragment(sigof(ctxt)),δ2,γ2)’
            by(simp[fleq_def,total_fragment_def] >> cheat (*non-trivial*)) >>
          drule(GSYM fleq_term_interp_le) >>
          disch_then(dep_rewrite.DEP_REWRITE_TAC o single) >>
          conj_tac >- cheat >>
          fs[models_def,satisfies_t_def,satisfies_def] >>
          first_x_assum(match_mp_tac o MP_CANON) >>
          cheat
         ) >>
      qunabbrev_tac ‘ctxt’ >>
      first_assum (fn thm => qabbrev_tac ‘aaa = ^(concl thm)’) >>
      fs[admissible_axiom_def]
      >- ((* ETA axiom*)
          fs[mk_eta_ctxt_def] >> rveq >> fs[] >>
          rw[termsem_def] >>
          dep_rewrite.DEP_REWRITE_TAC[termsem_ext_equation |> REWRITE_RULE[termsem_ext_def]] >>
          simp[] >>
          conj_tac >-
            (goal_assum drule >>
             fs[valuates_frag_builtins] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >- (simp[welltyped_equation]) >>
             rw[] >>
             simp[term_ok_equation] >>
             simp[term_ok_clauses]) >>
          simp[boolean_eq_true] >>
          simp[termsem_def] >>
          simp[UPDATE_def] >>
          qmatch_goalsub_abbrev_tac `type_interpretation_ext_of _ (HD ctxt)` >>
          `v («f» ,Fun (Tyvar «A» ) (Tyvar «B» )) ⋲
             ext_type_frag_builtins (type_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)
                                    (TYPE_SUBSTf sigma (Fun (Tyvar «A» ) (Tyvar «B» )))`
            by(FULL_SIMP_TAC bool_ss [valuates_frag_builtins] >>
               FULL_SIMP_TAC bool_ss [valuates_frag_def] >>
               first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               qexists_tac `Var ARB (Fun (Tyvar «A» ) (Tyvar «B» ))` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               simp[] >>
               simp[term_ok_def] >>
               metis_tac[term_ok_clauses,FST]) >>
          fs[ext_type_frag_builtins_Fun] >>
          drule_then drule in_funspace_abstract >>
          rw[] >> rw[] >>
          drule_then match_mp_tac abstract_eq >>
          simp[] >>
          rw[] >> simp[apply_abstract])
      >- ((* Axiom of choice *)
          fs[mk_select_ctxt_def] >> rveq >>
          `ALOOKUP (const_list ctxt1) (strlit "@") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE]) >>
          `ALOOKUP (const_list ctxt1) (strlit "==>") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,holBoolSyntaxTheory.mk_bool_ctxt_def]) >>
          rename1 `mk_bool_ctxt ctxt3` >>
          qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins δ) γ` >>
          qmatch_asmsub_abbrev_tac `ctxt extends init_ctxt` >>
          `is_bool_interpretation_ext (sigof ctxt) δ γ`
            by(drule_then match_mp_tac extends_is_bool_interpretation >>
               qexists_tac `ctxt3` >>
               qexists_tac `axsof (mk_bool_ctxt ctxt3)` >>
               conj_tac >-
                 (qpat_x_assum `NewConst _ _ :: _ extends _` assume_tac >>
                  drule extends_appends >>
                  strip_tac >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rveq >>
                  drule(extends_append_MID |> Q.INST [`a`|->`[]`] |> REWRITE_RULE [APPEND]) >>
                  impl_tac >- rw[init_ctxt_def] >>
                  strip_tac >>
                  drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
                  fs[]) >>
               `ctxt extends mk_bool_ctxt ctxt3`
                 by(qunabbrev_tac `ctxt` >>
                    `mk_bool_ctxt ctxt3 = [] ++ mk_bool_ctxt ctxt3` by simp[] >>
                    pop_assum(fn thm => PURE_ONCE_REWRITE_TAC[Once thm]) >>
                    PURE_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] >>
                    PURE_REWRITE_TAC[APPEND_ASSOC] >>
                    match_mp_tac extends_NIL_APPEND_extends >>
                    drule_then(assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                    PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >> simp[]) >>
               drule extends_sub >>
               rw[] >>
               simp[models_def] >>
               fs[Abbr `ctxt`]) >>
          fs[is_bool_interpretation_ext_def,is_bool_interpretation_def,
             is_implies_interpretation_def] >>
          simp[termsem_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_boolrel_rw] >> simp[] >>
          fs[valuates_frag_builtins] >> fs[valuates_frag_def] >>
          `v («P» ,Fun (Tyvar «A» ) Bool) ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (Fun (Tyvar «A» ) Bool))`
            by(first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               Q.REFINE_EXISTS_TAC `Var _ _` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               qexists_tac `ARB` >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               conj_tac >- (rw[term_ok_def] >> metis_tac[term_ok_clauses,FST]) >>
               simp[]) >>
          `v («x» ,Tyvar «A») ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (Tyvar «A»))`
            by(first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               Q.REFINE_EXISTS_TAC `Var _ _` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               qexists_tac `ARB` >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               conj_tac >- (rw[term_ok_def] >> metis_tac[term_ok_clauses,FST]) >>
               simp[]) >>
          fs[ext_type_frag_builtins_Bool,ext_type_frag_builtins_Fun] >>
          drule_then drule in_funspace_abstract >>
          strip_tac >> rveq >>
          simp[] >>
          simp[ext_term_frag_builtins_def] >>
          `γ (strlit "@",Fun (Fun (sigma(strlit "A")) Bool) (sigma(strlit "A"))) =
           Abstract (ext_type_frag_builtins δ (Fun (sigma(strlit "A")) Bool))
                          (ext_type_frag_builtins δ (sigma(strlit "A")))
                          (λp.
                            case some x. (^mem x (ext_type_frag_builtins δ (sigma(strlit "A"))) ∧
                                         p ' x = True) of
                              NONE => (@x. ^mem x (ext_type_frag_builtins δ (sigma(strlit "A"))))
                            | SOME x => x)`
            by(rw[Abbr `γ`,Abbr `δ`] >>
               dep_rewrite.DEP_ONCE_REWRITE_TAC[CONJUNCT2 type_interpretation_ext_of_alt] >>
               simp[] >>
               conj_tac >-
                 (simp[Abbr `ctxt`] >>
                  simp[nonbuiltin_constinsts_def,builtin_consts_def,ground_consts_def,ground_types_def,tyvars_def] >>
                  fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
                  reverse conj_tac >- metis_tac[] >>
                  conj_asm1_tac >- (metis_tac[term_ok_clauses,FST]) >>
                  simp[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
                  qexists_tac `[(sigma «A»,Tyvar «A»)]` >>
                  EVAL_TAC) >>
               IF_CASES_TAC >-
                 ((* it should be possible to prove a contradiction here *)
                  spose_not_then kall_tac >>
                  qpat_x_assum ‘Abbrev(_ ∨ _)’ (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                  fs[] >>
                  simp[allCInsts_def,allTypes_def,allTypes'_defn,builtin_const_def,init_ctxt_def] >>
                  simp[Once DISJ_EQ_IMP] >>
                  simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                  drule(indep_frag_upd_is_frag |> REWRITE_RULE[extends_init_def]) >>
                  disch_then(qspec_then ‘HD ctxt’ strip_assume_tac) >>
                  drule is_sig_fragment_const_in_type_frag >>
                  disch_then drule >>
                  simp[allTypes'_defn] >>
                  simp[GSYM IMP_DISJ_THM] >>
                  strip_tac >>
                  reverse conj_tac >-
                    (rw[] >> first_x_assum drule >>
                     simp[Abbr‘ctxt’] >>
                     simp[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
                  cheat
                 ) >>
               pop_assum kall_tac >>
               reverse TOP_CASE_TAC >-
                 (goal_assum kall_tac >>
                  pop_assum mp_tac >> simp[] >>
                  qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
                  `FILTER fff lll = []` suffices_by simp[] >>
                  MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
                  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                  fs[Abbr `ctxt`,defn_matches_NewAxiom,defn_matches_NewConst] >-
                    (simp[defn_matches_def] >>
                     TOP_CASE_TAC >> simp[] >>
                     CONV_TAC SYM_CONV >>
                     rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                     pairarg_tac >> rw[] >>
                     imp_res_tac ALOOKUP_NONE >>
                     qpat_x_assum `MEM _ ctxt1` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                     rveq >> fs[] >>
                     qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                     rveq >> fs[] >>
                     FULL_CASE_TAC >> fs[] >>
                     qpat_x_assum `_ extends _` assume_tac >>
                     drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                     FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                     dxrule extends_APPEND_NIL >>
                     simp[extends_NIL_CONS_extends,updates_cases,constspec_ok_def,is_reserved_name_def] >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                     rw[] >> simp[]) >>
                  simp[defn_matches_def] >>
                  TOP_CASE_TAC >> simp[] >>
                  CONV_TAC SYM_CONV >>
                  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                  pairarg_tac >> rw[] >>
                  qpat_x_assum `_ :: _ extends _` assume_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  fs[extends_NIL_CONS_extends,updates_cases] >>
                  qpat_x_assum `MEM _ (mk_bool_ctxt _)` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                  rveq >> fs[] >>
                  Cases_on `b` >-
                    (FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                     dxrule extends_APPEND_NIL >>
                     simp[extends_NIL_CONS_extends,updates_cases,constspec_ok_def,is_reserved_name_def] >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                     rw[] >> res_tac >>
                     simp[]) >>
                  fs[] >>
                  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                  rveq >> fs[]) >>
               reverse TOP_CASE_TAC >-
                 (goal_assum kall_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  drule NewConst_no_abs_rep >>
                  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
                  disch_then(qspecl_then[`strlit "@"`,`^select_ty`] mp_tac) >>
                  impl_tac >- rw[Abbr `ctxt`] >>
                  strip_tac >> fs[]) >>
               simp[Abbr `ctxt`,ALOOKUP_APPEND] >>
               simp[Once holBoolSyntaxTheory.mk_bool_ctxt_def,holBoolSyntaxTheory.ImpliesDef_def] >>
               simp[typeof_def,equation_def]) >>
          simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
          simp[GSYM CONJ_ASSOC] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >> simp[]) >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[] >>
             rename1 `elem ⋲ ind` >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
             rw[some_def] >>
             SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
          rw[boolean_eq_true] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          rename1 `elem ⋲ ind` >>
          dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
          rw[some_def] >>
          SELECT_ELIM_TAC >> simp[] >> metis_tac[apply_abstract])
      >- ((* Axiom of infinity *)
          `NewAxiom p = (^infinity_ax)` by
            (qpat_x_assum `NewAxiom _ :: _ = _` (mp_tac o REWRITE_RULE[mk_infinity_ctxt_def]) >>
             simp[]) >>
          fs[] >> rveq >>
          rw[satisfies_t_def,satisfies_def] >>
          `ALOOKUP (type_list ctxt1) (strlit "ind") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "ONE_ONE") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "ONTO") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "!") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "?") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "==>") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          rename1 `mk_bool_ctxt ctxt3` >>
          qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins δ) γ` >>
          qmatch_asmsub_abbrev_tac `ctxt extends init_ctxt` >>
          `is_std_sig(sigof ctxt)`
            by(rpt(qpat_x_assum `is_std_sig _` mp_tac) >>
               fs[Abbr `ctxt`,mk_infinity_ctxt_def,mk_select_ctxt_def]) >>
          `is_bool_interpretation_ext (sigof ctxt) δ γ`
            by(drule_then match_mp_tac extends_is_bool_interpretation >>
               qexists_tac `ctxt3` >>
               qexists_tac `axsof (mk_bool_ctxt ctxt3)` >>
               conj_tac >-
                 (qpat_x_assum `ctxt2 extends _` mp_tac >>
                  fs[mk_infinity_ctxt_def,mk_select_ctxt_def] >>
                  strip_tac >>
                  drule extends_appends >>
                  strip_tac >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rveq >>
                  drule(extends_append_MID |> Q.INST [`a`|->`[x;y;z;å]`] |> REWRITE_RULE [APPEND]) >>
                  impl_tac >- rw[init_ctxt_def] >>
                  strip_tac >>
                  drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
                  fs[]) >>
               `ctxt extends mk_bool_ctxt ctxt3`
                 by(qunabbrev_tac `ctxt` >>
                    rw[mk_infinity_ctxt_def,mk_select_ctxt_def] >>
                    `mk_bool_ctxt ctxt3 = [] ++ mk_bool_ctxt ctxt3` by simp[] >>
                    pop_assum(fn thm => PURE_ONCE_REWRITE_TAC[Once thm]) >>
                    PURE_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] >>
                    PURE_REWRITE_TAC[APPEND_ASSOC] >>
                    match_mp_tac extends_NIL_APPEND_extends >>
                    drule_then(assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                    PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >> simp[] >>
                    pop_assum MP_TAC >> EVAL_TAC) >>
               drule extends_sub >>
               rw[] >>
               simp[models_def] >>
               fs[Abbr `ctxt`] >>
               fs[mk_infinity_ctxt_def,mk_select_ctxt_def]
              ) >>
          fs[is_bool_interpretation_ext_def,is_bool_interpretation_def,
             is_implies_interpretation_def,is_exists_interpretation_def,
             is_and_interpretation_def,is_not_interpretation_def
            ] >>
          simp[termsem_def] >>
          qpat_assum `!ty. ty ∈ ground_types (sigof ctxt) ==> _ = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          conj_tac >-
            (rw[ground_types_def,tyvars_def] >>
             fs[type_ok_def,is_std_sig_def] >>
             rw[Abbr `ctxt`] >>
             simp[ALOOKUP_APPEND] >>
             EVAL_TAC) >>
          simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool,UPDATE_def] >>
          `ext_type_frag_builtins δ Ind = ind`
            by(simp[ext_type_frag_builtins_def,Abbr `δ`] >>
               dep_rewrite.DEP_ONCE_REWRITE_TAC[CONJUNCT1 type_interpretation_ext_of_alt] >>
               simp[] >>
               conj_asm1_tac >-
                 (simp[ground_types_def,nonbuiltin_types_def,tyvars_def,is_builtin_type_def] >>
                  reverse conj_tac >-
                    (rw[Abbr `ctxt`,type_ok_def,ALOOKUP_APPEND] >> EVAL_TAC) >>
                  fs[Abbr `ctxt`,mk_infinity_ctxt_def]) >>
               IF_CASES_TAC >-
                 (spose_not_then kall_tac >>
                  qpat_x_assum ‘Abbrev(_ ∨ _)’ (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                  fs[] >>
                  simp[allCInsts_def,allTypes_def,allTypes'_defn,builtin_const_def,init_ctxt_def] >>
                  simp[Once DISJ_EQ_IMP] >>
                  simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                  reverse conj_tac >-
                    (rw[] >> qpat_x_assum ‘Ind ∈ FST _’ mp_tac >>
                     simp[Abbr‘ctxt’] >>
                     simp[GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
                     qpat_x_assum ‘NewAxiom _::_ = _’ (assume_tac o GSYM) >> simp[]) >>
                  cheat
                 ) >>
               pop_assum kall_tac >>
               drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule NewType_no_type_match >>
               disch_then(qspecl_then [`[]`,`strlit "ind"`,`0`] mp_tac) >>
               impl_tac >- (rw[Abbr `ctxt`] >> EVAL_TAC) >>
               disch_then SUBST_ALL_TAC >>
               simp[]) >>
          simp[] >>
          simp[ext_term_frag_builtins_def] >>
          (* Fish out ONTO's defining equation from the conexts ---
             this way we don't need to unfold the model construction *)
          first_assum(qspec_then `HD(^onto_conext)` mp_tac) >>
          impl_tac >-
            (qpat_x_assum `_ :: _ = _` mp_tac >>
             EVAL_TAC >> strip_tac >> rveq >> EVAL_TAC) >>
          simp[] >>
          simp[satisfies_t_def] >>
          disch_then(qspec_then `(K Ind)` mp_tac) >>
          impl_keep_tac >-
            (simp[tyvars_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `_ :: _ = _` (mp_tac o EVAL_RULE) >>
                strip_tac >> rveq >>
                simp[type_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION]) >>
             simp[ground_terms_uninst_def] >>
             qmatch_goalsub_abbrev_tac `a1 has_type _` >>
             qexists_tac `typeof a1` >>
             qunabbrev_tac `a1` >>
             simp[typeof_def] >>
             conj_tac >-
               (rpt(rw[Once has_type_cases,PULL_EXISTS])) >>
             rw[ground_types_def,tyvars_def] >>
             metis_tac[term_ok_clauses,FST]) >>
          simp[satisfies_def] >>
          drule_then drule exists_valuation >>
          disch_then(qspec_then `K Ind` mp_tac) >>
          simp[] >>
          fs[] >>
          strip_tac >> simp[valuates_frag_builtins] >>
          disch_then drule >>
          impl_tac >-
            (match_mp_tac terms_of_frag_uninst_term_ok >>
             rw[term_ok_clauses] >>
             simp[term_ok_def] >>
             fs[mk_infinity_ctxt_def,mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                FLOOKUP_FUNION,FLOOKUP_UPDATE]
             >- metis_tac[term_ok_clauses,FST]
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ExistsDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])) >>
          simp[termsem_def,UPDATE_def] >>
          simp[Once ext_term_frag_builtins_def] >>
          simp[ext_type_frag_builtins_def] >>
          fs[is_forall_interpretation_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (simp[ext_term_frag_builtins_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `is_frag_interpretation _ _ _` mp_tac >>
                rw[is_frag_interpretation_def,total_fragment_def,GSYM PFORALL_THM] >>
                pop_assum(qspecl_then [`strlit"ONTO"`,`Fun (Fun Ind Ind) Bool`] mp_tac) >>
                simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
                disch_then match_mp_tac >>
                rw[ground_consts_def,nonbuiltin_constinsts_def,ground_types_def,tyvars_def,
                   builtin_consts_def,term_ok_def,FLOOKUP_FUNION] >-
                  metis_tac[term_ok_clauses,FST] >>
                fs[mk_infinity_ctxt_def] >>
                rveq >> fs[] >>
                conj_tac >- metis_tac[term_ok_clauses,FST] >>
                qexists_tac `[(Ind,Tyvar «A»);(Ind,Tyvar «B»)]` >>
                EVAL_TAC) >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[] >> rw[boolean_in_boolset]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (conj_asm1_tac >-
               (dep_rewrite.DEP_ONCE_REWRITE_TAC[abstract_in_funspace] >>
                simp[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
                rw[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                rw[] >>
                simp[ext_term_frag_builtins_def] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                rw[]) >>
             simp[boolean_in_boolset]) >>
          simp[boolean_eq_true,Once ext_term_frag_builtins_def] >>
          disch_then kall_tac >>
          (* Fish out ONE_ONE's defining equation from the conexts ---
             this way we don't need to unfold the model construction *)
          first_assum(qspec_then `HD(^one_one_conext)` mp_tac) >>
          impl_tac >-
            (qpat_x_assum `_ :: _ = _` mp_tac >>
             EVAL_TAC >> strip_tac >> rveq >> EVAL_TAC) >>
          simp[] >>
          simp[satisfies_t_def] >>
          disch_then(qspec_then `(K Ind)` mp_tac) >>
          simp[] >>
          impl_keep_tac >-
            (simp[ground_terms_uninst_def] >>
             qmatch_goalsub_abbrev_tac `a1 has_type _` >>
             qexists_tac `typeof a1` >>
             qunabbrev_tac `a1` >>
             simp[typeof_def] >>
             conj_tac >-
               (rpt(rw[Once has_type_cases,PULL_EXISTS])) >>
             rw[ground_types_def,tyvars_def] >>
             metis_tac[term_ok_clauses,FST]) >>
          simp[satisfies_def] >>
          simp[valuates_frag_builtins] >>
          disch_then drule >>
          impl_tac >-
            (match_mp_tac terms_of_frag_uninst_term_ok >>
             rw[term_ok_clauses] >>
             simp[term_ok_def] >>
             fs[mk_infinity_ctxt_def,mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                FLOOKUP_FUNION,FLOOKUP_UPDATE]
             >- metis_tac[term_ok_clauses,FST]
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ImpliesDef_def] >>
                 rw[equation_def] >>
                 metis_tac[term_ok_clauses,FST])
            ) >>
          simp[termsem_def,UPDATE_def] >>
          simp[Once ext_term_frag_builtins_def] >>
          simp[ext_type_frag_builtins_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (simp[ext_term_frag_builtins_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `is_frag_interpretation _ _ _` mp_tac >>
                disch_then(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[is_frag_interpretation_def,total_fragment_def,GSYM PFORALL_THM]) >>
                pop_assum(qspecl_then [`strlit"ONE_ONE"`,`Fun (Fun Ind Ind) Bool`] mp_tac) >>
                simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
                disch_then match_mp_tac >>
                rw[ground_consts_def,nonbuiltin_constinsts_def,ground_types_def,tyvars_def,
                   builtin_consts_def,term_ok_def,FLOOKUP_FUNION] >-
                  metis_tac[term_ok_clauses,FST] >>
                fs[mk_infinity_ctxt_def] >>
                rveq >> fs[] >>
                conj_tac >- metis_tac[term_ok_clauses,FST] >>
                qexists_tac `[(Ind,Tyvar «A»);(Ind,Tyvar «B»)]` >>
                EVAL_TAC) >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[] >> rw[boolean_in_boolset]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (conj_asm1_tac >-
               (dep_rewrite.DEP_ONCE_REWRITE_TAC[abstract_in_funspace] >>
                simp[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
                rw[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                rw[] >>
                simp[ext_term_frag_builtins_def] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> rw[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset]) >>
             simp[boolean_in_boolset]) >>
          simp[boolean_eq_true,Once ext_term_frag_builtins_def] >>
          disch_then kall_tac >>
          qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          simp[ground_types_def] >>
          conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
          rw[] >>
          qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          simp[ground_types_def] >>
          simp[ext_term_frag_builtins_def] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             conj_tac >-
               (rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                strip_tac >> simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset]) >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qpat_x_assum `m <: Funspace _ _` assume_tac >>
             drule_then drule in_funspace_abstract >>
             strip_tac >> simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[]) >>
          qpat_x_assum `is_infinite _ _` mp_tac >>
          simp[is_infinite_def] >>
          simp[INFINITE_INJ_NOT_SURJ] >>
          strip_tac >>
          rename1 `INJ f` >>
          qexists_tac`Abstract (ext_type_frag_builtins δ Ind) (ext_type_frag_builtins δ Ind) f` >>
          fs[] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
             ntac 2 (pop_assum mp_tac) >> simp[INJ_DEF]) >>
          simp[holds_def] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          simp[] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          conj_tac >-
            (rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             conj_tac >-
               (rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
                simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset]) >>
             rw[boolean_eq_true] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             simp[boolean_eq_true] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset,boolean_eq_true] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset,boolean_eq_true] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          simp[] >>
          qpat_x_assum`¬(SURJ f X Y)`mp_tac >>
          simp[SURJ_DEF] >>
          strip_tac >-
            (qpat_x_assum`INJ f X Y`mp_tac >>
             simp[INJ_DEF] >>
             PROVE_TAC[]) >>
          rename1 `w <: ext_type_frag_builtins _ Ind` >>
          qexists_tac `w` >>
          simp[] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          fs[GSYM IMP_DISJ_THM] >>
          dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          ntac 2 strip_tac >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset] >>
          simp[boolean_def,true_neq_false] >>
          qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF])
      )
  >- ((* conexts of new axiom (vacuous) *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[conexts_of_upd_def])
  >- ((* NewConst *)
      fs[conexts_of_upd_def])
  >- ((* NewConst *)
      fs[conexts_of_upd_def])
  >- ((* ConstSpec *)
      fs[conexts_of_upd_def] >>
      rw[satisfies_t_def,satisfies_def] >>
      `!name. MEM name (MAP FST eqs) ==> ~MEM name (MAP FST (const_list ctxt1))`
        by(rw[] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           fs[DISJOINT_DEF,INTER_DEF,FUN_EQ_THM,GSYM IMP_DISJ_THM,map_fst] >>
           TRY(rename1 `ConstSpec F` >> metis_tac[]) >>
           fs[constspec_ok_def] >>
           qpat_x_assum `MEM _ (MAP FST _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
           rveq >>
           rename1 `MEM pp eqs` >>
           Cases_on `pp` >>
           rename1 `MEM (name,typ) eqs` >>
           res_tac >>
           qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
           rw[IMP_CONJ_THM,FORALL_AND_THM]) >>
      TRY(rename1 `ConstSpec T` >> (* overloads case *)
          drule proves_theory_mono >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                                   `tyenv`,`tmenv`] mp_tac) >>
          simp[] >>
          MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
          impl_tac >-
            (rw[] >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >> NO_TAC) >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
                drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                drule extends_NIL_DISJOINT >>
                simp[] >> NO_TAC) >>
             qhdtm_x_assum `theory_ok` mp_tac >>
             rw[theory_ok_def]) >>
          strip_tac >>
          drule_then assume_tac proves_term_ok >>
          fs[] >>
          drule_then assume_tac term_ok_welltyped >>
          drule termsem_VSUBST >>
          disch_then(qspec_then `^mem` mp_tac) >>
          qmatch_goalsub_abbrev_tac `VSUBST ilist` >>
          disch_then(qspec_then `ilist` mp_tac) >>
          impl_tac >-
            (rw[Abbr `ilist`,MEM_MAP,ELIM_UNCURRY] >> metis_tac[has_type_rules]) >>
          simp[] >>
          disch_then kall_tac >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          `models (type_interpretation_ext_of ind (HD (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) (TL (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) Δ Γ)
                  (UNCURRY (term_interpretation_ext_of ind (HD (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) (TL (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) Δ Γ)) ((tyenv,tmenv),axsof ctxt2)`
            by(rw[models_def]) >>
          drule_then drule proves_sound >>
          simp[entails_def] >>
          strip_tac >>
          first_x_assum drule >>
          simp[satisfies_t_def] >>
          ntac 2 (disch_then drule) >>
          impl_keep_tac >-
            (rw[ground_terms_uninst_def,EVERY_MEM,MEM_MAP] >>
             qexists_tac `Bool` >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             res_tac >>
             fs[ELIM_UNCURRY] >>
             simp[ground_types_def,tyvars_def] >>
             imp_res_tac theory_ok_sig >>
             metis_tac[FST,term_ok_clauses]) >>
          simp[satisfies_def] >>
          fs[valuates_frag_builtins] >>
          qmatch_goalsub_abbrev_tac `termsem _ _ vv sigma prop = True` >>
          disch_then(qspec_then `vv` mp_tac) >>
          impl_tac >-
            (conj_asm1_tac >-
               (rw[valuates_frag_def,Abbr `vv`] >>
                simp[MAP_REVERSE,APPLY_UPDATE_LIST_ALOOKUP,ALOOKUP_MAP] >>
                TOP_CASE_TAC >- metis_tac[valuates_frag_def] >>
                fs[ALOOKUP_SOME_EQ] >>
                fs[MAP_EQ_APPEND] >> rveq >>
                pairarg_tac >> fs[] >> rveq >>
                qpat_x_assum `Abbrev (_ ++ _ ++ _ = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                fs[MAP_EQ_APPEND |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
                pairarg_tac >> fs[] >> rveq >>
                fs[] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
                rename1 `Const name` >>
                drule_then(drule_then drule) termsem_in_type_ext2 >>
                disch_then(qspecl_then [`v`,`sigma`,`Const name (typeof t)`] mp_tac) >>
                impl_tac >-
                  (conj_tac >-
                     (match_mp_tac terms_of_frag_uninst_term_ok >>
                      simp[term_ok_def] >>
                      rw[Abbr `tmenv`,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
                      fs[DISJ_IMP_THM,FORALL_AND_THM] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      fs[constspec_ok_def,ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,ALOOKUP_MAP] >>
                      reverse conj_tac >- metis_tac[] >>
                      rfs[term_ok_clauses]) >>
                   simp[VFREE_IN_def]) >>
                simp[typeof_def] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) >>
             conj_asm1_tac >- (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             conj_asm1_tac >-
               (rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
                fs[EVERY_MEM,MEM_MAP] >> res_tac >> fs[] >>
                match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
             drule_then (drule_then(drule_then drule)) termsem_ext_equation >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             first_x_assum(drule_then strip_assume_tac) >>
             fs[] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[welltyped_equation]) >>
             disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
             disch_then dxrule >>
             disch_then dxrule >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[term_ok_clauses]) >>
             simp[termsem_ext_def] >>
             disch_then kall_tac >>
             simp[boolean_eq_true] >>
             simp[termsem_def,Abbr `vv`] >>
             simp[APPLY_UPDATE_LIST_ALOOKUP,Abbr `ilist`,MAP_REVERSE] >>
             simp[GSYM MAP_MAP_o] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP (MAP _ ll)` >>
             `EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ll)`
               by(fs[Abbr`ll`,EVERY_MEM,MEM_MAP,PULL_EXISTS] >> Cases >> rw[]) >>
             simp[ALOOKUP_MAP_dest_var] >>
             simp[Abbr `ll`,MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
             drule_then(drule_then (fn thm => simp[thm])) orth_ctxt_ALOOKUP_eqs >>
             simp[termsem_def] >>
             `s <> strlit "="`
               by(fs[constspec_ok_def,is_builtin_name_def,is_reserved_name_def] >> metis_tac[]) >>
             simp[SimpL``$=``,ext_term_frag_builtins_def] >>
             qmatch_goalsub_abbrev_tac `type_interpretation_ext_of ind (HD ctxt)` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ)
                (UNCURRY (term_interpretation_ext_of ind (HD ctxt) (TL ctxt) Δ Γ))`
               by(fs[Abbr `ctxt`]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ ground_consts (sigof ctxt)`
               by(rw[Abbr`ctxt`] >>
                  simp[ground_consts_def] >>
                  conj_tac >-
                    (rw[ground_types_def,tyvars_TYPE_SUBSTf_eq_NIL] >>
                     match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  fs[constspec_ok_def] >> res_tac >>
                  rw[term_ok_def,Abbr`tmenv`,FLOOKUP_FUNION] >>
                  reverse(Cases_on `ALOOKUP (const_list ctxt1) s`) >-
                    (imp_res_tac ALOOKUP_MEM >>
                     res_tac >> metis_tac[FST]) >>
                  simp[] >>
                  reverse conj_tac >-
                    (metis_tac[TYPE_SUBSTf_TYPE_SUBST_compose,TYPE_SUBSTf_eq_TYPE_SUBST]) >>
                  match_mp_tac type_ok_TYPE_SUBSTf >>
                  simp[] >>
                  fs[] >>
                  rfs[term_ok_clauses]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ nonbuiltin_constinsts`
               by(rw[nonbuiltin_constinsts_def,builtin_consts_def]) >>
             Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
             (* TODO: figure this out *)
             ‘ctxt ≠ []’ by(simp[Abbr ‘ctxt’]) >>
             simp[type_interpretation_ext_of_alt] >>
             IF_CASES_TAC >-
               (cheat (* ??? *)) >>
             pop_assum kall_tac >>
             drule orth_ctxt_FILTER_ctxt >>
             disch_then(drule o ONCE_REWRITE_RULE[CONJ_SYM]) >>
             disch_then(qspecl_then [`sigma`,`prop`,`T`] mp_tac) >>
             impl_tac >- rw[Abbr`ctxt`] >>
             strip_tac >> simp[] >> pop_assum kall_tac >>
             TOP_CASE_TAC >-
               (goal_assum kall_tac >>
                Q.SUBGOAL_THEN `is_instance (typeof t) (TYPE_SUBSTf sigma (typeof t))` assume_tac >-
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                metis_tac[instance_subst_completeness,IS_SOME_DEF]) >>
             rename1 `instance_subst _ _ _ = SOME result` >>
             Cases_on `result` >>
             rename1 `instance_subst _ _ _ = SOME(sigma',e)` >>
             drule_then (assume_tac o GSYM) instance_subst_soundness >>
             simp[ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4 t = termsem _ _ a5 _ _` >>
             `termsem a1 a2 a3 a4 t = termsem a1 a2 a5 a4 t`
               by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                  match_mp_tac termsem_frees >>
                  res_tac >> fs[CLOSED_def] >>
                  rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             pop_assum SUBST_ALL_TAC >>
             match_mp_tac termsem_subst >>
             conj_tac >-
               (MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                res_tac >> fs[] >> rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
             fs[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
             metis_tac[SND]) >>
          simp[]) >>
      TRY(rename1 `ConstSpec F` >> (* fresh constants case *)
          drule proves_theory_mono >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                                   `tyenv`,`tmenv`] mp_tac) >>
          simp[] >>
          MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
          impl_tac >-
            (rw[] >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >> NO_TAC) >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >- metis_tac[DISJOINT_SYM] >>
                 disch_then kall_tac >>
                 fs[constspec_ok_def,map_fst] >>
                 fs[DISJOINT_DEF,FUN_EQ_THM] >> metis_tac[]) >>
             qhdtm_x_assum `theory_ok` mp_tac >>
             rw[theory_ok_def]) >>
          strip_tac >>
          drule_then assume_tac proves_term_ok >>
          fs[] >>
          drule_then assume_tac term_ok_welltyped >>
          drule termsem_VSUBST >>
          disch_then(qspec_then `^mem` mp_tac) >>
          qmatch_goalsub_abbrev_tac `VSUBST ilist` >>
          disch_then(qspec_then `ilist` mp_tac) >>
          impl_tac >-
            (rw[Abbr `ilist`,MEM_MAP,ELIM_UNCURRY] >> metis_tac[has_type_rules]) >>
          simp[] >>
          disch_then kall_tac >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          `models (type_interpretation_of ind (ctxt1 ++ ConstSpec F eqs prop::ctxt2)) (UNCURRY (term_interpretation_of ind (ctxt1 ++ ConstSpec F eqs prop::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
            by(rw[models_def]) >>
          drule_then drule proves_sound >>
          simp[entails_def] >>
          strip_tac >>
          first_x_assum drule >>
          simp[satisfies_t_def] >>
          ntac 2 (disch_then drule) >>
          impl_keep_tac >-
            (rw[ground_terms_uninst_def,EVERY_MEM,MEM_MAP] >>
             qexists_tac `Bool` >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             res_tac >>
             fs[ELIM_UNCURRY] >>
             simp[ground_types_def,tyvars_def] >>
             imp_res_tac theory_ok_sig >>
             metis_tac[FST,term_ok_clauses]) >>
          simp[satisfies_def] >>
          fs[valuates_frag_builtins] >>
          qmatch_goalsub_abbrev_tac `termsem _ _ vv sigma prop = True` >>
          disch_then(qspec_then `vv` mp_tac) >>
          impl_tac >-
            (conj_asm1_tac >-
               (rw[valuates_frag_def,Abbr `vv`] >>
                simp[MAP_REVERSE,APPLY_UPDATE_LIST_ALOOKUP,ALOOKUP_MAP] >>
                TOP_CASE_TAC >- metis_tac[valuates_frag_def] >>
                fs[ALOOKUP_SOME_EQ] >>
                fs[MAP_EQ_APPEND] >> rveq >>
                pairarg_tac >> fs[] >> rveq >>
                qpat_x_assum `Abbrev (_ ++ _ ++ _ = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                fs[MAP_EQ_APPEND |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
                pairarg_tac >> fs[] >> rveq >>
                fs[] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
                rename1 `Const name` >>
                drule_then(drule_then drule) termsem_in_type_ext2 >>
                disch_then(qspecl_then [`v`,`sigma`,`Const name (typeof t)`] mp_tac) >>
                impl_tac >-
                  (conj_tac >-
                     (match_mp_tac terms_of_frag_uninst_term_ok >>
                      simp[term_ok_def] >>
                      rw[Abbr `tmenv`,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
                      fs[DISJ_IMP_THM,FORALL_AND_THM] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      fs[constspec_ok_def,ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,ALOOKUP_MAP] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      rfs[term_ok_clauses]) >>
                   simp[VFREE_IN_def]) >>
                simp[typeof_def] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) >>
             conj_asm1_tac >- (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             conj_asm1_tac >-
               (rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
                fs[EVERY_MEM,MEM_MAP] >> res_tac >> fs[] >>
                match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
             drule_then (drule_then(drule_then drule)) termsem_ext_equation >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             first_x_assum(drule_then strip_assume_tac) >>
             fs[] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[welltyped_equation]) >>
             disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
             disch_then dxrule >>
             disch_then dxrule >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[term_ok_clauses]) >>
             simp[termsem_ext_def] >>
             disch_then kall_tac >>
             simp[boolean_eq_true] >>
             simp[termsem_def,Abbr `vv`] >>
             simp[APPLY_UPDATE_LIST_ALOOKUP,Abbr `ilist`,MAP_REVERSE] >>
             simp[GSYM MAP_MAP_o] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP (MAP _ ll)` >>
             `EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ll)`
               by(fs[Abbr`ll`,EVERY_MEM,MEM_MAP,PULL_EXISTS] >> Cases >> rw[]) >>
             simp[ALOOKUP_MAP_dest_var] >>
             simp[Abbr `ll`,MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP ll` >>
             `ALL_DISTINCT(MAP FST ll)`
               by(rw[Abbr `ll`,ALL_DISTINCT_MAP] >>
                  fs[constspec_ok_def] >>
                  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
                  rpt(pop_assum kall_tac) >>
                  Induct_on `eqs` >- rw[] >>
                  Cases >> rw[] >>
                  rw[MEM_MAP,GSYM IMP_DISJ_THM] >>
                  Cases_on `x` >> fs[] >>
                  rveq >>
                  fs[MEM_MAP,GSYM IMP_DISJ_THM]) >>
             `MEM (Var s (typeof t),Const s (typeof t)) ll`
               by(rw[Abbr `ll`,MEM_MAP,PULL_EXISTS] >> metis_tac[FST,SND]) >>
             drule_then drule ALOOKUP_ALL_DISTINCT_MEM >>
             simp[] >> disch_then kall_tac >>
             simp[termsem_def] >>
             `s <> strlit "="`
               by(fs[constspec_ok_def] >>
                  qpat_x_assum `ctxt2 extends init_ctxt` assume_tac >>
                  drule_then strip_assume_tac extends_appends >>
                  rveq >> fs[init_ctxt_def] >>
                  fs[MEM_MAP,PULL_EXISTS] >> res_tac >>
                  fs[]) >>
             simp[SimpL``$=``,ext_term_frag_builtins_def] >>
             qmatch_goalsub_abbrev_tac `type_interpretation_of ind ctxt` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_of ind ctxt)
                (UNCURRY (term_interpretation_of ind ctxt))`
               by(fs[Abbr `ctxt`]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ ground_consts (sigof ctxt)`
               by(rw[Abbr`ctxt`] >>
                  simp[ground_consts_def] >>
                  conj_tac >-
                    (rw[ground_types_def,tyvars_TYPE_SUBSTf_eq_NIL] >>
                     match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  rw[term_ok_def,Abbr`tmenv`,FLOOKUP_FUNION] >>
                  reverse(Cases_on `ALOOKUP (const_list ctxt1) s`) >-
                    (imp_res_tac ALOOKUP_MEM >>
                     res_tac >> metis_tac[FST]) >>
                  simp[] >>
                  simp[ALOOKUP_MAP] >>
                  fs[constspec_ok_def] >>
                  dxrule_then dxrule ALOOKUP_ALL_DISTINCT_MEM >>
                  drule_then drule ALOOKUP_ALL_DISTINCT_MEM >>
                  simp[] >> ntac 2 (disch_then kall_tac) >>
                  conj_tac >-
                    (match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ nonbuiltin_constinsts`
               by(rw[nonbuiltin_constinsts_def,builtin_consts_def]) >>
             Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
             simp[type_interpretation_of_alt] >>
             simp[Abbr `ctxt`,FILTER_APPEND] >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = []`
               by(fs[Abbr `fff`,Abbr `lll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                  strip_tac >>
                  disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  rename1` defn_matches _ _ aaa` >> Cases_on `aaa` >> fs[defn_matches_def] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  dxrule_then assume_tac extends_APPEND_NIL >>
                  fs[] >>
                  dxrule_then assume_tac extends_NIL_CONS_updates >>
                  Cases >> strip_tac >>
                  fs[updates_cases,constspec_ok_def] >>
                  reverse(Cases_on `b`) >-
                    (fs[MEM_MAP,PULL_EXISTS] >>
                     first_x_assum drule >>
                     qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                     first_x_assum drule >>
                     rpt strip_tac >>
                     spose_not_then strip_assume_tac >>
                     rveq >>
                     first_x_assum(qspec_then `(q,t)` mp_tac) >>
                     simp[]) >>
                  fs[] >>
                  first_x_assum drule >>
                  strip_tac
                  >- (qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                      rveq >>
                      qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                      first_x_assum drule >>
                      rpt strip_tac >>
                      fs[] >> metis_tac[FST]) >>
                  qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                  rveq >> fs[MEM_MAP,PULL_EXISTS] >>
                  qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                  first_x_assum drule >>
                  rpt strip_tac >>
                  fs[] >> metis_tac[FST]) >>
             pop_assum SUBST_ALL_TAC >>
             qunabbrev_tac `lll` >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = []`
               by(fs[Abbr `fff`,Abbr `lll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                  strip_tac >>
                  disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  rename1` defn_matches _ _ aaa` >> Cases_on `aaa` >> fs[defn_matches_def] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  fs[constspec_ok_def] >>
                  Cases >> disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  reverse(Cases_on `b`) >-
                    (fs[MEM_MAP,PULL_EXISTS] >>
                     qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                     first_x_assum drule >>
                     rpt strip_tac >>
                     fs[] >> metis_tac[FST]) >>
                  fs[] >>
                  qpat_x_assum `_ ++ ConstSpec T _ _::_ extends _` assume_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  dxrule_then assume_tac extends_APPEND_NIL >>
                  fs[] >>
                  dxrule_then assume_tac extends_NIL_CONS_updates >>
                  fs[updates_cases,constspec_ok_def,DISJ_IMP_THM,FORALL_AND_THM] >>
                  qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                  rveq >> fs[] >>
                  metis_tac[MEM_MAP,FST]) >>
             pop_assum SUBST_ALL_TAC >>
             simp[] >>
             MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
             simp[defn_matches_def] >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = [(s,t)]`
               by(MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
                  qpat_x_assum `MEM _ eqs` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  fs[FILTER_APPEND] >>
                  reverse IF_CASES_TAC >- metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                  simp[APPEND_EQ_CONS] >>
                  fs[constspec_ok_def,ALL_DISTINCT_APPEND,IMP_CONJ_THM,FORALL_AND_THM,DISJ_IMP_THM] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  conj_tac >> Cases >> fs[MEM_MAP,PULL_EXISTS] >> metis_tac[FST]) >>
             pop_assum SUBST_ALL_TAC >> simp[] >>
             fs[Abbr `fff`,Abbr `lll`] >>
             TOP_CASE_TAC >-
               (goal_assum kall_tac >>
                Q.SUBGOAL_THEN `is_instance (typeof t) (TYPE_SUBSTf sigma (typeof t))` assume_tac >-
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                metis_tac[instance_subst_completeness,IS_SOME_DEF]) >>
             rename1 `instance_subst _ _ _ = SOME result` >>
             Cases_on `result` >>
             rename1 `instance_subst _ _ _ = SOME(sigma',e)` >>
             drule_then (assume_tac o GSYM) instance_subst_soundness >>
             simp[ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4 t = termsem _ _ a5 _ _` >>
             `termsem a1 a2 a3 a4 t = termsem a1 a2 a5 a4 t`
               by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                  match_mp_tac termsem_frees >>
                  res_tac >> fs[CLOSED_def] >>
                  rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             pop_assum SUBST_ALL_TAC >>
             match_mp_tac termsem_subst >>
             conj_tac >-
               (MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                res_tac >> fs[] >> rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
             fs[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
             metis_tac[SND]) >>
            simp[])
     )
  >- ((* NewType *)
      fs[conexts_of_upd_def])
  >- ((* TypeDefn *)
      rename1 `elem ⋲ ind` >>
      fs[conexts_of_upd_def] >>
      rw[satisfies_t_def,satisfies_def,termsem_def] >>
      `~MEM name (MAP FST (type_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `~MEM abs (MAP FST (const_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `~MEM rep (MAP FST (const_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `ALOOKUP (type_list ctxt1) name = NONE`
        by rw[ALOOKUP_NONE] >>
       `ALOOKUP (const_list ctxt1) abs = NONE`
        by rw[ALOOKUP_NONE] >>
      `ALOOKUP (const_list ctxt1) rep = NONE`
        by rw[ALOOKUP_NONE]
      >- ((* First abs/rep axiom *)
       drule proves_theory_mono >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
       disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                               `tyenv`,`tmenv`] mp_tac) >>
       simp[] >>
       MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
       impl_tac >-
         (rw[] >>
          TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
              drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
              drule extends_NIL_DISJOINT >>
              simp[] >> NO_TAC) >>
          qhdtm_x_assum `theory_ok` mp_tac >>
          rw[theory_ok_def]) >>
      strip_tac >>
      drule_then drule (MP_CANON termsem_ext_equation) >>
      disch_then drule >>
      fs[valuates_frag_builtins] >>
      disch_then drule >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_keep_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
      disch_then (MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      ntac 2 (disch_then dxrule) >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[]) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      `~MEM (strlit "=") (MAP FST (const_list ctxt1))`
        by(drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def] >>
           rveq >> fs[] >>
           fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           drule_then(assume_tac o C MATCH_MP (REWRITE_RULE[init_ctxt_def] init_ctxt_extends))
                     extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `MEM (strlit "=") (MAP FST (const_list ctxt2))`
        by(imp_res_tac extends_appends >> rw[init_ctxt_def]) >>
      `abs <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      `rep <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      simp[ext_term_frag_builtins_def] >>
      qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
      `models (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
              (UNCURRY (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              ((tyenv,tmenv),axsof ctxt2)`
        by(rw[models_def]) >>
      drule_then drule proves_sound >>
      simp[entails_def] >>
      strip_tac >>
      first_x_assum drule >>
      simp[satisfies_t_def] >>
      ntac 2 (disch_then drule) >>
      impl_keep_tac >-
        (rw[ground_terms_uninst_def] >>
         goal_assum drule >>
         rw[ground_types_def,tyvars_def] >>
         imp_res_tac term_ok_type_ok >>
         qpat_x_assum `is_std_sig (tyenv,tmenv)` mp_tac >>
         rw[is_std_sig_def,type_ok_def]) >>
      simp[satisfies_def] >>
      simp[valuates_frag_builtins] >>
      disch_then drule >>
      impl_tac >-
        (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
      simp[termsem_def] >> strip_tac >>
      `termsem
           (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (TYPE_SUBSTf sigma (typeof witness))
      `
        by(match_mp_tac termsem_in_type_ext2 >>
           rpt(goal_assum drule) >>
           conj_tac >-
             (match_mp_tac terms_of_frag_uninst_term_ok >>
              simp[] >>
              drule proves_term_ok >>
              rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
           rpt strip_tac >>
           qpat_x_assum `valuates_frag _ _ _ _` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then match_mp_tac >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           goal_assum drule >>
           goal_assum drule >>
           match_mp_tac terms_of_frag_uninst_term_ok >>
           simp[] >>
           drule proves_term_ok >> rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ rep reptype` >>
      `(abs,abstype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(fs[Abbr `abstype`,ground_consts_def,ground_types_def] >>
           conj_tac >-
             (simp[tyvars_def,LIST_UNION_EQ_NIL,tyvars_TYPE_SUBSTf_eq_NIL] >>
              match_mp_tac FOLDR_LIST_UNION_empty >>
              rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
           conj_asm1_tac >-
             (qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
              `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
              pop_assum SUBST_ALL_TAC >>
              simp[term_ok_clauses] >>
              conj_tac >-
                (match_mp_tac type_ok_TYPE_SUBSTf >> simp[] >>
                 qpat_x_assum `term_ok _ (Comb _ _)` mp_tac >>
                 simp[term_ok_clauses] >>
                 rpt strip_tac >>
                 simp[] >> metis_tac[term_ok_type_ok,FST]) >>
              simp[type_ok_def,EVERY_MAP,MEM_MAP,PULL_EXISTS] >>
              rw[Abbr `tyenv`,FLOOKUP_FUNION,FLOOKUP_UPDATE]) >>
           rw[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           qexists_tac `(MAP (λx. (sigma x,Tyvar x)) (tvars pred))` >>
           simp[TYPE_SUBST_eq_TYPE_SUBSTf,MAP_EQ_f,MEM_MAP,PULL_EXISTS,
                REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF,ALOOKUP_Tyvar,ALOOKUP_MAPf] >>
           simp[TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
           rfs[term_ok_clauses] >>
           rpt strip_tac >>
           IF_CASES_TAC >> simp[] >>
           fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
           drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
           drule_then (mp_tac o REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) tyvars_typeof_subset_tvars >>
           disch_then drule >>
           simp[tyvars_def]) >>
      `(abs,abstype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `(rep,reptype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qpat_x_assum `(abs,abstype) ∈ ground_consts _` mp_tac >>
           fs[Abbr `reptype`,Abbr `abstype`,ground_consts_def,ground_types_def] >>
           qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
           `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
           pop_assum SUBST_ALL_TAC >>
           simp[term_ok_clauses] >>
           simp[tyvars_def,LIST_UNION_EQ_NIL] >>
           rw[term_ok_def,term_ok_clauses,FLOOKUP_FUNION,FLOOKUP_UPDATE,MAP_EQ_f] >>
           fs[type_ok_def] >>
           metis_tac[]) >>
      `(rep,reptype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `is_frag_interpretation (total_fragment (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
          (type_interpretation_of ind
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of ind
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
      simp[type_interpretation_of_alt] >>
      qpat_x_assum `inhabited ind` kall_tac >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      Cases_on `[] ≠
              defn_matches rep
                (Fun
                   (Tyapp name
                      (MAP (λa. TYPE_SUBSTf sigma a)
                         (MAP Tyvar
                            (MAP implode
                               (STRING_SORT (MAP explode (tvars pred)))))))
                   (TYPE_SUBSTf sigma (domain (typeof pred))))
                (TypeDefn name pred abs rep)` >-
        (fs[defn_matches_def]) >>
      simp[] >>
      ntac 2 (pop_assum kall_tac) >>
      ntac 2 (
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             fs[] >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`] >>
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac (extends_APPEND_NIL |> Q.SPEC `[e]` |> REWRITE_RULE[APPEND]) >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[])
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`]) >>
      simp[] >>
      simp[mllistTheory.mapPartial_def,mapPartial_APPEND] >>
      rpt
        (qmatch_goalsub_abbrev_tac `mapPartial a1 a2` >>
        `mapPartial a1 a2 = []`
          by(rw[Abbr `a1`,Abbr `a2`,mllistTheory.mapPartial_thm,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,
                PULL_EXISTS] >>
             simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
             ntac 3 (PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
             fs[pair_case_eq] >>
             PURE_FULL_CASE_TAC >> fs[] >> rveq >>
             qpat_x_assum `MEM (TypeDefn _ _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             fs[updates_cases]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`a1`,`a2`]) >>
      simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `if a1 then SOME _ else NONE` >>
      reverse(first_assum (fn thm =>
                              qunabbrev_tac `a1` >>
                              Cases_on [ANTIQUOTE (rhs(rand(concl thm)))])) >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> pop_assum kall_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         reverse conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma',stuff)` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      qmatch_goalsub_abbrev_tac `instance_subst [ty0,ty1]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma'',stuff')` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      ntac 2 (PRED_ASSUM is_exists kall_tac) >>
      rpt(qpat_x_assum `Fun _ _ = TYPE_SUBST _ _` (mp_tac o GSYM)) >>
      rw[] >> fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac `ext_type_frag_builtins _ (Tyapp name ntys)` >>
      `Tyapp name ntys ∈ nonbuiltin_types`
        by(simp[Abbr`ntys`] >>
           drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def,
              APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           last_assum(qspec_then `(name,0)` mp_tac) >>
           last_x_assum(qspec_then `(name,2)` mp_tac) >>
           simp[] >>
           rw[nonbuiltin_types_def,is_builtin_type_def]) >>
      qunabbrev_tac `ntys` >>
      simp[ext_type_frag_builtins_nonbuiltin] >>
      qmatch_goalsub_abbrev_tac `v (vname,vty)` >>
      `v (vname,vty) ⋲ (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
        by(qhdtm_x_assum `valuates_frag0` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then(qspecl_then [`vname`,`vty`] mp_tac) >>
           simp[Abbr `vty`,ext_type_frag_builtins_nonbuiltin] >>
           disch_then match_mp_tac >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- simp[welltyped_equation] >>
           strip_tac >>
           PURE_REWRITE_TAC[GSYM TYPE_SUBSTf_def] >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           Q.REFINE_EXISTS_TAC `Var _ _` >>
           simp[] >>
           metis_tac[]) >>
      `TYPE_SUBSTf sigma vty ∈ ground_types (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qunabbrev_tac `vty` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      `v (vname,vty) ⋲ ext_type_frag_builtins(type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma (domain(typeof pred)))`
        by(qpat_x_assum `_ ⋲ type_interpretation_of ind _ _` mp_tac >>
           fs[Abbr `vty`] >>
           Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
           simp[type_interpretation_of_alt] >>
           qpat_x_assum `inhabited ind` kall_tac >>
           simp[mllistTheory.mapPartial_thm,FILTER_APPEND] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           simp[type_matches_def] >>
           qmatch_goalsub_abbrev_tac `if predd then SOME _ else NONE` >>
           Q.SUBGOAL_THEN `predd` assume_tac >-
             (qunabbrev_tac `predd` >>
              simp[MAP_EQ_f,MEM_MAP,PULL_EXISTS,REV_ASSOCD_ALOOKUP] >>
              qexists_tac `MAP (λx. (sigma x, Tyvar x)) (tvars pred)` >>
              simp[ALOOKUP_Tyvar,MAP_MAP_o,o_DEF,ALOOKUP_MAPf]) >>
           qunabbrev_tac `predd` >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
           Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
             (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
           disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
           rename1 `instance_subst _ _ _ = SOME result` >>
           Cases_on `result` >>
           rename1 `SOME(sigma''',stuff'')` >>
           simp[] >>
           drule_then assume_tac instance_subst_soundness >>
           MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
           qpat_x_assum `Tyapp _ _ = TYPE_SUBST _ _` (assume_tac o GSYM) >>
           simp[] >>
           `TYPE_SUBST sigma'³' (domain (typeof pred)) =
            TYPE_SUBSTf sigma (domain (typeof pred))
           `
             by(simp[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                rpt strip_tac >> first_x_assum match_mp_tac >>
                rfs[term_ok_clauses] >>
                fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
                drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
                drule_then (match_mp_tac o REWRITE_RULE[SUBSET_DEF]) tyvars_typeof_subset_tvars >>
                rfs[tyvars_def] >>
                disch_then drule) >>
           rw[mem_sub]) >>
      MAP_EVERY qunabbrev_tac [`vname`,`vty`] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >-
             (qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
              `Abstract a1 a2 a3 ' a4 = a3 a4`
                by(drule_then match_mp_tac apply_abstract >>
                   MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                   simp[] >> fs[]) >>
              MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
              pop_assum SUBST_ALL_TAC >>
              simp[]) >>
           rw[] >>
           SELECT_ELIM_TAC >>
           simp[] >>
           qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def] >>
           strip_tac >>
           first_x_assum match_mp_tac >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           simp[] >> fs[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      pop_assum SUBST_ALL_TAC >>
      simp[] >>
      fs[]) >>
      (* Second abs/rep axiom *)
       drule proves_theory_mono >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
       disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                               `tyenv`,`tmenv`] mp_tac) >>
       simp[] >>
       MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
       impl_tac >-
         (rw[] >>
          TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
              drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
              drule extends_NIL_DISJOINT >>
              simp[] >> NO_TAC) >>
          qhdtm_x_assum `theory_ok` mp_tac >>
          rw[theory_ok_def]) >>
      strip_tac >>
      drule_then drule (MP_CANON termsem_ext_equation) >>
      disch_then drule >>
      fs[valuates_frag_builtins] >>
      disch_then drule >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_keep_tac >-
        (rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
         imp_res_tac proves_term_ok >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]) >>
      disch_then (MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      ntac 2 (disch_then dxrule) >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[] >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]
        ) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_tac >- rw[welltyped_equation] >>
      strip_tac >>
      drule_then dxrule terms_of_frag_uninst_equationE >>
      impl_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
      disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      drule_then drule termsem_ext_equation >>
      disch_then drule >> disch_then drule >>
      disch_then dxrule >> disch_then dxrule >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[] >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      `~MEM (strlit "=") (MAP FST (const_list ctxt1))`
        by(drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def] >>
           rveq >> fs[] >>
           fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           drule_then(assume_tac o C MATCH_MP (REWRITE_RULE[init_ctxt_def] init_ctxt_extends))
                     extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `MEM (strlit "=") (MAP FST (const_list ctxt2))`
        by(imp_res_tac extends_appends >> rw[init_ctxt_def]) >>
      `abs <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      `rep <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      simp[ext_term_frag_builtins_def] >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
      `models (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
              (UNCURRY (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              ((tyenv,tmenv),axsof ctxt2)`
        by(rw[models_def]) >>
      drule_then drule proves_sound >>
      simp[entails_def] >>
      strip_tac >>
      first_x_assum drule >>
      simp[satisfies_t_def] >>
      ntac 2 (disch_then drule) >>
      impl_keep_tac >-
        (rw[ground_terms_uninst_def] >>
         goal_assum drule >>
         rw[ground_types_def,tyvars_def] >>
         imp_res_tac term_ok_type_ok >>
         qpat_x_assum `is_std_sig (tyenv,tmenv)` mp_tac >>
         rw[is_std_sig_def,type_ok_def]) >>
      simp[satisfies_def] >>
      simp[valuates_frag_builtins] >>
      disch_then drule >>
      impl_tac >-
        (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
      simp[termsem_def] >> strip_tac >>
      `termsem
           (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (TYPE_SUBSTf sigma (typeof witness))
      `
        by(match_mp_tac termsem_in_type_ext2 >>
           rpt(goal_assum drule) >>
           conj_tac >-
             (match_mp_tac terms_of_frag_uninst_term_ok >>
              simp[] >>
              drule proves_term_ok >>
              rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
           rpt strip_tac >>
           qpat_x_assum `valuates_frag _ _ _ _` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then match_mp_tac >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           goal_assum drule >>
           goal_assum drule >>
           match_mp_tac terms_of_frag_uninst_term_ok >>
           simp[] >>
           drule proves_term_ok >> rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ rep reptype` >>
      `(abs,abstype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(fs[Abbr `abstype`,ground_consts_def,ground_types_def] >>
           conj_tac >-
             (simp[tyvars_def,LIST_UNION_EQ_NIL,tyvars_TYPE_SUBSTf_eq_NIL] >>
              match_mp_tac FOLDR_LIST_UNION_empty >>
              rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
           conj_asm1_tac >-
             (qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
              `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
              pop_assum SUBST_ALL_TAC >>
              simp[term_ok_clauses] >>
              conj_tac >-
                (match_mp_tac type_ok_TYPE_SUBSTf >> simp[] >>
                 qpat_x_assum `term_ok _ (Comb _ _)` mp_tac >>
                 simp[term_ok_clauses] >>
                 rpt strip_tac >>
                 simp[] >> metis_tac[term_ok_type_ok,FST]) >>
              simp[type_ok_def,EVERY_MAP,MEM_MAP,PULL_EXISTS] >>
              rw[Abbr `tyenv`,FLOOKUP_FUNION,FLOOKUP_UPDATE]) >>
           rw[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           qexists_tac `(MAP (λx. (sigma x,Tyvar x)) (tvars pred))` >>
           simp[TYPE_SUBST_eq_TYPE_SUBSTf,MAP_EQ_f,MEM_MAP,PULL_EXISTS,
                REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF,ALOOKUP_Tyvar,ALOOKUP_MAPf] >>
           simp[TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
           rfs[term_ok_clauses] >>
           rpt strip_tac >>
           IF_CASES_TAC >> simp[] >>
           fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
           drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
           drule_then (mp_tac o REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) tyvars_typeof_subset_tvars >>
           disch_then drule >>
           simp[tyvars_def]) >>
      `(abs,abstype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `(rep,reptype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qpat_x_assum `(abs,abstype) ∈ ground_consts _` mp_tac >>
           fs[Abbr `reptype`,Abbr `abstype`,ground_consts_def,ground_types_def] >>
           qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
           `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
           pop_assum SUBST_ALL_TAC >>
           simp[term_ok_clauses] >>
           simp[tyvars_def,LIST_UNION_EQ_NIL] >>
           rw[term_ok_def,term_ok_clauses,FLOOKUP_FUNION,FLOOKUP_UPDATE,MAP_EQ_f] >>
           fs[type_ok_def] >>
           metis_tac[]) >>
      `(rep,reptype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `is_frag_interpretation (total_fragment (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
          (type_interpretation_of ind
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of ind
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
      simp[type_interpretation_of_alt] >>
      qpat_x_assum `inhabited ind` kall_tac >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      Cases_on `[] ≠
                 defn_matches abs
                   (Fun (TYPE_SUBSTf sigma (domain (typeof pred)))
                      (Tyapp name
                         (MAP (λa. TYPE_SUBSTf sigma a)
                            (MAP Tyvar
                               (MAP implode
                                  (STRING_SORT (MAP explode (tvars pred))))))))
                   (TypeDefn name pred abs rep)` >-
        fs[defn_matches_def] >>
      simp[] >>
      ntac 2 (pop_assum kall_tac) >>
      ntac 2 (
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             fs[] >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`] >>
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac (extends_APPEND_NIL |> Q.SPEC `[e]` |> REWRITE_RULE[APPEND]) >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[])
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`]) >>
      simp[] >>
      simp[mllistTheory.mapPartial_def,mapPartial_APPEND] >>
      rpt
        (qmatch_goalsub_abbrev_tac `mapPartial a1 a2` >>
        `mapPartial a1 a2 = []`
          by(rw[Abbr `a1`,Abbr `a2`,mllistTheory.mapPartial_thm,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,
                PULL_EXISTS] >>
             simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
             ntac 3 (PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
             fs[pair_case_eq] >>
             PURE_FULL_CASE_TAC >> fs[] >> rveq >>
             qpat_x_assum `MEM (TypeDefn _ _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             fs[updates_cases]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`a1`,`a2`]) >>
      simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> pop_assum kall_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         reverse conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> simp[] >>
         fs[] >>
         metis_tac[]) >>
      CONV_TAC(SIMP_CONV (srw_ss())[]) >>
      qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma',stuff)` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      qmatch_goalsub_abbrev_tac `instance_subst [ty0,ty1]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma'',stuff')` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      ntac 2 (PRED_ASSUM is_exists kall_tac) >>
      rpt(qpat_x_assum `Fun _ _ = TYPE_SUBST _ _` (mp_tac o GSYM)) >>
      rw[] >> fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac `ext_type_frag_builtins _ (Tyapp name ntys)` >>
      `Tyapp name ntys ∈ nonbuiltin_types`
        by(simp[Abbr`ntys`] >>
           drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def,
              APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           last_assum(qspec_then `(name,0)` mp_tac) >>
           last_x_assum(qspec_then `(name,2)` mp_tac) >>
           simp[] >>
           rw[nonbuiltin_types_def,is_builtin_type_def]) >>
      qunabbrev_tac `ntys` >>
      simp[ext_type_frag_builtins_nonbuiltin] >>
      qmatch_goalsub_abbrev_tac `v (vname,vty)` >>
      `v (vname,vty) ⋲ ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
        by(qhdtm_x_assum `valuates_frag0` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then(qspecl_then [`vname`,`vty`] mp_tac) >>
           simp[Abbr `vty`,ext_type_frag_builtins_nonbuiltin] >>
           disch_then match_mp_tac >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- simp[welltyped_equation] >>
           strip_tac >>
           PURE_REWRITE_TAC[GSYM TYPE_SUBSTf_def] >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           Q.REFINE_EXISTS_TAC `Var _ _` >>
           simp[] >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
           strip_tac >>
           metis_tac[]) >>
      `TYPE_SUBSTf sigma vty ∈ ground_types (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qunabbrev_tac `vty` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           simp[tyvars_TYPE_SUBSTf_eq_NIL] >>
           match_mp_tac type_ok_TYPE_SUBSTf >>
           simp[] >>
           rfs[term_ok_clauses]) >>
      qmatch_goalsub_abbrev_tac `Abstract (type_interpretation_of ind ctxt vty')` >>
      `vty' ∈ ground_types (sigof ctxt)`
        by(qunabbrev_tac `vty'` >> qunabbrev_tac `ctxt` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      `type_interpretation_of ind ctxt vty'
       =
       (ext_type_frag_builtins (type_interpretation_of ind ctxt)
         (TYPE_SUBSTf sigma vty) suchthat
        (λtm. termsem
          (ext_type_frag_builtins (type_interpretation_of ind ctxt))
          (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_of ind ctxt))
                                 (UNCURRY (term_interpretation_of ind ctxt))) v sigma
          pred ' tm = True))`
        by(`is_frag_interpretation (total_fragment(sigof ctxt)) (type_interpretation_of ind ctxt)
                                   (UNCURRY (term_interpretation_of ind ctxt))`
             by(simp[Abbr`ctxt`]) >>
           Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
           simp[type_interpretation_of_alt] >>
           qpat_x_assum `inhabited ind` kall_tac >>
           fs[Abbr `vty`,Abbr `vty'`,Abbr `ctxt`] >>
           simp[mllistTheory.mapPartial_thm,FILTER_APPEND] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           simp[type_matches_def] >>
           qmatch_goalsub_abbrev_tac `if predd then SOME _ else NONE` >>
           Q.SUBGOAL_THEN `predd` assume_tac >-
             (qunabbrev_tac `predd` >>
              simp[MAP_EQ_f,MEM_MAP,PULL_EXISTS,REV_ASSOCD_ALOOKUP] >>
              qexists_tac `MAP (λx. (sigma x, Tyvar x)) (tvars pred)` >>
              simp[ALOOKUP_Tyvar,MAP_MAP_o,o_DEF,ALOOKUP_MAPf]) >>
           qunabbrev_tac `predd` >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
           Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
             (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
           disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
           rename1 `instance_subst _ _ _ = SOME result` >>
           Cases_on `result` >>
           rename1 `SOME(sigma''',stuff'')` >>
           simp[] >>
           drule_then assume_tac instance_subst_soundness >>
           MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
           qpat_x_assum `Tyapp _ _ = TYPE_SUBST _ _` (assume_tac o GSYM) >>
           simp[] >>
           `TYPE_SUBST sigma'³' (domain (typeof pred)) =
            TYPE_SUBSTf sigma (domain (typeof pred))
           `
             by(simp[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                rpt strip_tac >> first_x_assum match_mp_tac >>
                rfs[term_ok_clauses] >>
                fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
                drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
                drule_then (match_mp_tac o REWRITE_RULE[SUBSET_DEF]) tyvars_typeof_subset_tvars >>
                rfs[tyvars_def] >>
                disch_then drule) >>
           simp[] >>
           simp[mem_sub] >>
           simp[ELIM_UNCURRY] >>
           qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4` >>
           `termsem a1 a2 a3 a4 pred =
            termsem a1 a2 v a4 pred`
             by(match_mp_tac(GEN_ALL termsem_frees) >>
                fs[CLOSED_def] >>
                rfs[term_ok_clauses]) >>
           pop_assum SUBST_ALL_TAC >>
           `termsem a1 a2 v a4 pred =
            termsem a1 a2 v sigma pred`
             by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                match_mp_tac termsem_subst >>
                rfs[term_ok_clauses] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS]) >>
           pop_assum SUBST_ALL_TAC >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           reverse IF_CASES_TAC
           >- (goal_assum kall_tac >>
               pop_assum mp_tac >> simp[] >>
               fs[ELIM_UNCURRY] >>
               rfs[term_ok_clauses] >> metis_tac[]) >>
           pop_assum kall_tac >>
           rw[]) >>
      MAP_EVERY qunabbrev_tac [`vname`,`vty`] >>
      MAP_EVERY qunabbrev_tac [`ctxt`,`vty'`] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >-
             (qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
              `Abstract a1 a2 a3 ' a4 = a3 a4`
                by(drule_then match_mp_tac apply_abstract >>
                   MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                   simp[] >> rw[] >>
                   SELECT_ELIM_TAC >>
                   simp[] >>
                   simp[mem_sub] >>
                   rfs[term_ok_clauses] >>
                   metis_tac[]) >>
              MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
              simp[] >>
              rw[] >>
              SELECT_ELIM_TAC >>
              simp[] >>
              simp[mem_sub] >>
              rfs[term_ok_clauses] >>
              metis_tac[]) >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
           `Abstract a1 a2 a3 ' a4 = a3 a4`
             by(drule_then match_mp_tac apply_abstract >>
                MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                simp[] >>
                rw[] >>
                SELECT_ELIM_TAC >> simp[] >>
                simp[mem_sub] >>
                rfs[term_ok_clauses] >>
                metis_tac[]) >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           simp[] >>
           rw[] >>
           SELECT_ELIM_TAC >> simp[] >>
           simp[mem_sub] >>
           rfs[term_ok_clauses] >>
           metis_tac[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >- simp[] >>
           simp[] >>
           rw[] >>
           SELECT_ELIM_TAC >>
           simp[] >>
           simp[mem_sub] >>
           rfs[term_ok_clauses] >>
           metis_tac[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      IF_CASES_TAC >- rfs[mem_sub,boolean_def] >>
      rfs[mem_sub] >>
      SELECT_ELIM_TAC >>
      conj_tac >- (rfs[term_ok_clauses] >> metis_tac[]) >>
      rpt strip_tac >>
      `x <> v («r» ,domain (typeof pred))` by
        (spose_not_then strip_assume_tac >>
         rveq >> fs[]) >>
      simp[boolean_def] >>
      qmatch_goalsub_abbrev_tac `a1 ' a2 = False` >>
      `a1 ' a2 ⋲ boolset`
        by(MAP_EVERY qunabbrev_tac [`a1`,`a2`] >>
           drule_then match_mp_tac apply_in_rng >>
           goal_assum drule >>
           qmatch_goalsub_abbrev_tac `_ ⋲ a1` >>
           `a1 = ext_type_frag_builtins
                   (type_interpretation_of ind
                      (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
                   (TYPE_SUBSTf sigma(typeof pred))`
             by(rfs[Abbr `a1`,term_ok_clauses] >>
                simp[ext_type_frag_builtins_Fun] >>
                qpat_x_assum `Comb pred witness has_type Bool` (strip_assume_tac o REWRITE_RULE[Once has_type_cases]) >>
                pop_assum mp_tac >> simp[] >>
                pop_assum mp_tac >> simp[] >>
                pop_assum mp_tac >> simp[] >>
                strip_tac >> rveq >>
                ntac 2 strip_tac >>
                ntac 2(dxrule WELLTYPED_LEMMA) >>
                ntac 2 strip_tac >>
                rveq >>
                rfs[] >>
                CONV_TAC(RHS_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV[ext_type_frag_builtins_def]))) >>
                simp[]) >>
           simp[] >>
           match_mp_tac termsem_in_type_ext2 >>
           simp[] >>
           goal_assum drule >>
           simp[] >>
           fs[CLOSED_def] >>
           qpat_x_assum `Comb pred _ ∈ terms_of_frag_uninst _ _` assume_tac >>
           drule_then drule terms_of_frag_uninst_combE >>
           rw[]) >>
      metis_tac[mem_boolset,true_neq_false])
QED

Theorem interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀upd ctxt Δ Γ. ctxt extends init_ctxt ∧ inhabited ind ∧ upd updates ctxt
            ∧ (axioms_admissible mem ind (upd::ctxt))
            ∧ (models Δ Γ (thyof ctxt))
    ⇒
        models (type_interpretation_ext_of ind upd ctxt Δ Γ) (UNCURRY (term_interpretation_ext_of ind upd ctxt Δ Γ))
               (thyof ((upd::ctxt)))
Proof
  rpt strip_tac >>
  ‘upd::ctxt extends init_ctxt’ by(fs[extends_def] >> rw[Once RTC_CASES1]) >>
  drule_then (assume_tac o MATCH_MP extends_nil_orth o C MATCH_MP init_ctxt_extends) extends_trans >>
  imp_res_tac extends_init_ctxt_terminating >>
  ‘ctxt extends []’ by(drule_then match_mp_tac extends_trans >> simp[init_ctxt_extends]) >>
  SIMP_TAC std_ss [models_def] >>
  conj_asm1_tac >-
   (drule_then match_mp_tac interpretation_is_total_frag_interpretation >>
    fs[models_def] >>
    metis_tac[]) >>
  rw[] >>
  qpat_x_assum `_ extends init_ctxt` assume_tac >>
  `!ctxt2. ctxt2 extends init_ctxt ==>
    !ctxt1 p.
    orth_ctxt (ctxt1 ++ ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ ctxt2))) /\
    (axioms_admissible mem ind (ctxt1 ++ ctxt2)) /\ inhabited ind /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ ctxt2)))
      (type_interpretation_ext_of ind (HD(ctxt1 ++ ctxt2)) (TL(ctxt1 ++ ctxt2)) Δ Γ)
      (UNCURRY (term_interpretation_ext_of ind (HD(ctxt1 ++ ctxt2)) (TL(ctxt1 ++ ctxt2)) Δ Γ)) /\
    MEM p (axiom_list ctxt2) /\ models Δ Γ (thyof (TL (ctxt1 ++ ctxt2))) ∧
    ctxt1 ++ ctxt2 extends init_ctxt ==>
    satisfies_t (sigof (ctxt1 ++ ctxt2))
      (ext_type_frag_builtins (type_interpretation_ext_of ind (HD(ctxt1 ++ ctxt2)) (TL(ctxt1 ++ ctxt2)) Δ Γ))
      (ext_term_frag_builtins
         (ext_type_frag_builtins (type_interpretation_ext_of ind (HD(ctxt1 ++ ctxt2)) (TL(ctxt1 ++ ctxt2)) Δ Γ))
         (UNCURRY (term_interpretation_ext_of ind (HD(ctxt1 ++ ctxt2)) (TL(ctxt1 ++ ctxt2)) Δ Γ))) ([],p)`
    by(qhdtm_x_assum `is_set_theory` (fn thm => rpt(pop_assum kall_tac) >> assume_tac thm) >>
       ntac 2 strip_tac >>
       drule_then ho_match_mp_tac extends_init_ind >>
       rpt strip_tac
       >- ((* init ctxt axioms*)
           fs[init_ctxt_def,conexts_of_upd_def])
       >- (rename1 `ctxt0 ++ upd::ctxt1` >>
           first_x_assum(qspec_then `ctxt0 ++ [upd]` mp_tac) >>
           PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
           strip_tac >>
           qpat_x_assum `MEM _ _` (strip_assume_tac o SIMP_RULE bool_ss [FLAT,MAP,MEM_APPEND])
           >- (* Axiom in update *)
              (drule_then match_mp_tac interpretation_models_axioms_lemma >>
               rfs[total_fragment_is_fragment] >>
               drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >>
               rw[DISJ_IMP_THM,FORALL_AND_THM] >>
               imp_res_tac extends_appends >>
               rveq >> simp[] >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >-
                 metis_tac[] >-
                 (imp_res_tac axioms_admissibleE >> simp[]) >>
               metis_tac[APPEND_ASSOC,APPEND]
              )
           >- (* Axiom in update (again) *)
              (drule_then match_mp_tac interpretation_models_axioms_lemma >>
               rfs[total_fragment_is_fragment] >>
               drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >>
               rw[DISJ_IMP_THM,FORALL_AND_THM] >>
               imp_res_tac extends_appends >>
               rveq >> simp[] >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >-
                 metis_tac[] >-
                 (imp_res_tac axioms_admissibleE >> simp[]) >>
               metis_tac[APPEND_ASSOC,APPEND]
              )
           >- (* Axiom not in update *)
              (fs[] >> metis_tac[])
          )
      ) >>
  first_x_assum (drule_then (qspec_then `[]` mp_tac)) >>
  rw[] >> pop_assum match_mp_tac >>
  fs[] >> metis_tac[]
QED

val _ = export_theory()
