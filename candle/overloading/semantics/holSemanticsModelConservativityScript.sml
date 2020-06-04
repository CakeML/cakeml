(*
  Proves soundness of the context extension rules: any model of a context can
  be extended to a model of the context obtained by applying one of the
  non-axiomatic context updates.
*)
open preamble mlstringTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holAxiomsSyntaxTheory holBoolTheory
     holExtensionTheory

val _ = new_theory"holSemanticsModelConservativity"

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
  >- (Cases >> fs[REPLICATE])
  >> Cases
  >> fs[REPLICATE]
  >> ASM_REWRITE_TAC[]
QED

(* trivial rewrites for is_instance overload *)

Triviality is_instance_simps:
  (!t i. is_instance t (TYPE_SUBST i t))
  /\ (!t a. is_instance (Tyvar a) t)
Proof
  rw[] >- (qexists_tac `i` >> fs[])
  >> qexists_tac `[(t,Tyvar a)]` >> fs[REV_ASSOCD_def]
QED

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

(* properties about the dependency relation *)

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
  !ctxt x. extends_init ctxt ==> ~(dependency ctxt) (INL Bool) x
Proof
  rw[dependency_cases,DISJ_EQ_IMP]
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

(* dependency relation for declarations *)

Triviality declaration_eq_dependency:
     ((dependency (NewConst name ty::ctxt)) (INL x) (INL y) = (dependency ctxt) (INL x) (INL y))
  /\ ((dependency (NewConst name ty::ctxt)) (INL x) (INR c) = (dependency ctxt) (INL x) (INR c))
  /\ ((dependency (NewConst name ty::ctxt)) (INR c) (INR d) = (dependency ctxt) (INR c) (INR d))
  /\  ((dependency (NewType name ar::ctxt)) (INL x) (INR c) = (dependency ctxt) (INL x) (INR c))
  /\  ((dependency (NewType name ar::ctxt)) (INR c) (INL x) = (dependency ctxt) (INR c) (INL x))
  /\  ((dependency (NewType name ar::ctxt)) (INR c) (INR d) = (dependency ctxt) (INR c) (INR d))
Proof
  fs[dependency_cases]
QED

Theorem type_sig_reduce_dependency_INL_INL[local]:
  !x y ctxt name n. type_ok (tysof ctxt) x
  /\ extends_init (NewType name n::ctxt)
  /\ (dependency (NewType name n::ctxt)) (INL x) (INL y)
  ==> type_ok (tysof ctxt) y /\ (dependency ctxt) (INL x) (INL y)
Proof
  Cases >> Cases
  >> rw[term_ok_def,type_ok_def]
  >> qpat_x_assum `(dependency _) _ _` (assume_tac o REWRITE_RULE[dependency_cases])
  >> fs[]
  >> drule_then assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] extends_init_NIL_orth_ctxt))
  >> drule extends_NIL_CONS_updates
  >> rw[updates_cases]
  >- (
    fs[dependency_cases]
    >> disj1_tac
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> fs[]
  )
  >- (
    imp_res_tac ALOOKUP_MEM
    >> imp_res_tac (Q.ISPEC `FST :mlstring # num -> mlstring ` MEM_MAP_f)
    >> imp_res_tac (Q.ISPEC `FST :mlstring # type -> mlstring ` MEM_MAP_f)
    >> fs[]
  )
  >- (
    fs[dependency_cases]
    >> disj2_tac
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> fs[]
  )
  >- (
    fs[extends_NIL_CONS_extends]
    >> drule_all_then assume_tac extends_update_ok_TypeDefn
    >> dxrule_all allTypes_type_ok
    >> fs[type_ok_def]
  )
  >- (
    fs[extends_NIL_CONS_extends]
    >> drule_all_then assume_tac extends_update_ok_TypeDefn
    >> dxrule_all allTypes_type_ok
    >> fs[type_ok_def]
  )
  >- (
    fs[dependency_cases]
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> fs[]
  )
QED

Theorem type_sig_reduce_dependency:
  !x y ctxt name n. (dependency (NewType name n::ctxt)) x y
  /\ extends_init (NewType name n::ctxt)
  /\ sum_CASE x (type_ok (tysof ctxt)) (term_ok (sigof ctxt))
  ==> sum_CASE y (type_ok (tysof ctxt)) (term_ok (sigof ctxt))
  /\ (dependency ctxt) x y
Proof
  Cases >> Cases
  >> fs[declaration_eq_dependency]
  >> TRY (
    qmatch_goalsub_abbrev_tac `dependency (_::_) _ _`
    >> rpt gen_tac
    >> disch_then strip_assume_tac
    >> drule_all type_sig_reduce_dependency_INL_INL
    >> fs[]
  )
  >> qmatch_goalsub_abbrev_tac `dependency _ (f a) (g b)`
  >> Cases_on `a` >> Cases_on `b`
  >> fs[markerTheory.Abbrev_def]
  >> rveq
  >> TRY (qmatch_goalsub_abbrev_tac `Tyvar xx` >> fs[term_ok_def,type_ok_def,tyvar_not_dependency ])
  >> rw[dependency_cases]
  >> drule_then assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] extends_init_NIL_orth_ctxt))
  >> fs[extends_NIL_CONS_extends]
  >> TRY (
    (((drule_all_then strip_assume_tac extends_update_ok_ConstSpec)
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_TypeDefn))
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_NewConst))
    >> (((dxrule_all allTypes'_type_ok)
      ORELSE (dxrule_all allTypes_type_ok))
      ORELSE (dxrule_all allCInsts_term_ok))
      >> fs[term_ok_def,type_ok_def]
    >> fs[]
  )
  >> `is_std_sig (sigof ctxt)` by (
    match_mp_tac extends_init_ctxt_is_std_sig
    >> fs[extends_init_def,extends_def]
    >> qpat_x_assum `_ (_::_) _` (assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
    >> fs[]
    >> fs[init_ctxt_def]
  )
  >> drule_then drule type_ok_types_in
  >> fs[types_in_def,type_ok_def]
  >> rw[]
  >> dxrule_all allTypes'_type_ok
  >> fs[type_ok_def]
QED

Theorem const_sig_reduce_dependency_INR_INL[local]:
  !c x ctxt name ty. term_ok (sigof ctxt) c
  /\ extends_init (NewConst name ty::ctxt)
  /\ (dependency (NewConst name ty::ctxt)) (INR c) (INL x)
  ==> type_ok (tysof ctxt) x /\ (dependency ctxt) (INR c) (INL x)
Proof
  rpt gen_tac
  >> CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV dependency_cases)))
  >> disch_then strip_assume_tac
  >> drule_then assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] extends_init_NIL_orth_ctxt))
  >> drule extends_NIL_CONS_updates
  >> fs[updates_cases]
  >> disch_tac
  >> conj_asm1_tac
  >> fs[type_ok_def,term_ok_def]
  >> rveq
  >> TRY (
    qmatch_abbrev_tac `type_ok _ _`
    >> fs[extends_NIL_CONS_extends]
    >> (((drule_all_then strip_assume_tac extends_update_ok_ConstSpec)
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_TypeDefn))
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_NewConst))
    >> ((dxrule_all allTypes'_type_ok)
      ORELSE (dxrule_all allTypes_type_ok))
    >> fs[type_ok_def]
  )
  >> TRY (
    qmatch_asmsub_abbrev_tac `NewConst name ty::_ extends []`
    >> qmatch_asmsub_abbrev_tac `ALOOKUP (const_list ctxt) name = _`
    >> imp_res_tac ALOOKUP_MEM
    >> imp_res_tac (Q.ISPEC `FST :mlstring # num -> mlstring ` MEM_MAP_f)
    >> imp_res_tac (Q.ISPEC `FST :mlstring # type -> mlstring ` MEM_MAP_f)
    >> fs[]
  )
  (* 6 subgoals *)
  >- (
    fs[dependency_cases]
    >> disj1_tac
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> rfs[]
  )
  >- (fs[dependency_cases] >> rfs[])
  >> (
    fs[dependency_cases]
    >> ntac 2 disj2_tac
    >> rpt(goal_assum (first_assum o mp_then Any mp_tac))
    >> rfs[]
  )
QED

Theorem const_sig_reduce_dependency:
  !x y ctxt name ty. (dependency (NewConst name ty::ctxt)) x y
  /\ extends_init (NewConst name ty::ctxt)
  /\ sum_CASE x (type_ok (tysof ctxt)) (term_ok (sigof ctxt))
  ==> sum_CASE y (type_ok (tysof ctxt)) (term_ok (sigof ctxt))
  /\ (dependency ctxt) x y
Proof
  Cases >> Cases
  >> fs[declaration_eq_dependency]
  >> TRY (
    qmatch_goalsub_abbrev_tac `dependency (_::_) _ _`
    >> rpt gen_tac
    >> disch_then strip_assume_tac
    >> drule_all const_sig_reduce_dependency_INR_INL
    >> fs[]
  )
  >> (
    qmatch_goalsub_abbrev_tac `dependency _ (f a) (g b)`
    >> Cases_on `a` >> Cases_on `b`
    >> fs[markerTheory.Abbrev_def]
    >> rveq
    >> fs[term_ok_def,type_ok_def,tyvar_not_dependency]
    >> rw[dependency_cases]
    >> drule_then assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] extends_init_NIL_orth_ctxt))
    >> fs[extends_NIL_CONS_extends]
    >> (((drule_all_then strip_assume_tac extends_update_ok_ConstSpec)
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_TypeDefn))
      ORELSE (drule_all_then strip_assume_tac extends_update_ok_NewConst))
    >> (((dxrule_all allTypes'_type_ok)
      ORELSE (dxrule_all allTypes_type_ok))
      ORELSE (dxrule_all allCInsts_term_ok))
    >> fs[term_ok_def,type_ok_def]
  )
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
  (* builtin_types  *)
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

(* construct list symbols introduced by an update *)
Definition upd_introduces_def:
  (upd_introduces (ConstSpec ov eqs prop)
    = MAP (λ(s,t). INR (Const s (typeof t))) eqs)
  /\ (upd_introduces (TypeDefn name pred abs rep)
    = [INL (Tyapp name (MAP Tyvar (mlstring_sort (tvars pred))))])
  /\ (upd_introduces (NewType name n)
    = [INL (Tyapp name (MAP Tyvar (GENLIST (λx. implode (REPLICATE (SUC x) #"a")) n)))])
  /\ (upd_introduces (NewConst name ty) = [INR (Const name ty)])
  /\ (upd_introduces (NewAxiom prop) = MAP INR (allCInsts prop))
End

(* independent fragment of an update *)
Definition indep_frag_upd_def:
  (indep_frag_upd ctxt upd frag = indep_frag ctxt (upd_introduces upd) frag)
End

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

(* conservativity *)
(* TODO Work in progress *)

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
  >> dxrule_then (assume_tac o CONJUNCT1) extends_init_NIL_orth_ctxt
  >> dxrule_then strip_assume_tac extends_NIL_CONS_updates
  >> fs[updates_cases,indep_frag_upd_def,indep_frag_def,upd_introduces_def,total_fragment_def,indep_frag_def,DIFF_DEF,SUBSET_DEF]
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
    qmatch_goalsub_abbrev_tac `GENLIST f arity`
    >> rw[ground_consts_def,ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,is_instance_simps]
    >> drule_then strip_assume_tac type_ok_type_ext
    >- (
      rename1`type_ok _ x`
      >> Cases_on `x`
      >> fs[type_ok_def,FLOOKUP_UPDATE]
      >> EVERY_CASE_TAC
      >- (
        rename1`Tyapp m l' ∈ nonbuiltin_types`
        >> first_x_assum (qspec_then `ZIP (l',MAP Tyvar (GENLIST f (LENGTH l')))` assume_tac)
        >> `ALL_DISTINCT (GENLIST f (LENGTH l'))` by (
          rw[ALL_DISTINCT_GENLIST,Abbr`f`,implode_def]
          >> imp_res_tac REPLICATE_inj
        )
        >> drule TYPE_SUBST_ZIP_ident
        >> fs[LR_TYPE_SUBST_def]
        >> disch_then (qspec_then `l'` (mp_tac o SIMP_RULE(srw_ss())[]))
        >> rveq
        >> disch_then (fs o single)
      )
      >> cheat
    )
    >> cheat
  )
  (* TypeDefn *)
  >- (
    qmatch_goalsub_abbrev_tac `MAP Tyvar mlstring_sort_pred`
    >> rw[ground_consts_def,ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION,is_instance_simps]
    >- (
      qpat_x_assum `_ ∈ _` kall_tac
      >> rpt (PRED_ASSUM (exists (curry op = "x")
        o map (fst o dest_var) o find_terms is_var) mp_tac)
      >> qid_spec_tac `x`
      >> ho_match_mp_tac type_ind
      >> conj_tac
      >- fs[type_ok_def]
      >> rw[]
      >> fs[type_ok_def,FLOOKUP_UPDATE]
      >> FULL_CASE_TAC
      >- (
        rename1`Tyapp m l`
        >> first_x_assum (qspec_then `ZIP (l,MAP Tyvar (mlstring_sort (tvars pred)))` assume_tac)
        >> `ALL_DISTINCT mlstring_sort_pred` by (
          fs[ALL_DISTINCT_STRING_SORT,mlstring_sort_def,Abbr`mlstring_sort_pred`]
        )
        >> drule TYPE_SUBST_ZIP_ident
        >> fs[LR_TYPE_SUBST_def,LENGTH_mlstring_sort,mlstring_sort_def]
        >> disch_then (qspec_then `l` (mp_tac o SIMP_RULE(srw_ss())[]))
        >> unabbrev_all_tac
        >> rfs[GSYM mlstring_sort_def,LENGTH_mlstring_sort]
        >> disch_then (fs o single)
      )
      >> fs[EVERY_MEM]
      >> cheat
    )
    >> cheat
  )
QED

(* TODO Work in progress *)
Theorem model_theoretic_conservativity:
  (!^mem ind ctxt ty upd. is_set_theory ^mem
    /\ extends_init (upd::ctxt)
    /\ ty ∈ FST (indep_frag_upd ctxt upd (total_fragment (sigof (upd::ctxt))))
    ⇒ type_interpretation_of0 ^mem ind (upd::ctxt) ty
      = type_interpretation_of0 ^mem ind ctxt ty
  ) /\
  !^mem ind ctxt c ty upd. is_set_theory ^mem
  /\ extends_init (upd::ctxt)
  /\ (c,ty) ∈ (SND (indep_frag_upd ctxt upd (total_fragment (sigof (upd::ctxt)))))
    ⇒ term_interpretation_of0 ^mem ind (upd::ctxt) c ty
    = term_interpretation_of0 ^mem ind ctxt c ty
Proof
  ho_match_mp_tac type_interpretation_of_ind
  >> rw[]
  >> drule_then assume_tac (CONJUNCT1 (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM] extends_init_NIL_orth_ctxt))
  >> fs[extends_NIL_CONS_extends,updates_cases,extends_init_NIL_orth_ctxt]
  >> cheat
QED

Overload ConstDef = ``λx t. ConstSpec F [(x,t)] (Var x (typeof t) === t)``

Theorem const_update_indep_frag:
  !frag frag1 ctxt cdefn x ty.
  extends_init ctxt
  /\ ConstDef x cdefn updates ctxt
  /\ term_ok (sigof ctxt) (Const x ty)
  /\ cdefn has_type ty
  /\ frag = indep_frag (ConstDef x cdefn::ctxt) [INR (Const x ty)] (total_fragment (sigof (ConstDef x cdefn::ctxt)))
  /\ frag1 = total_fragment (sigof ctxt)
  ==> (FST frag) ⊆ (FST frag1) /\ (SND frag) ⊆ (SND frag1)
Proof
  rw[indep_frag_def,total_fragment_def,DIFF_DEF,SUBSET_DEF,ground_consts_def,type_ok_def,updates_cases]
  >> fs[ground_types_def,type_ok_def,term_ok_def,FLOOKUP_UPDATE]
  >> EVERY_CASE_TAC
  >- (
    imp_res_tac WELLTYPED_LEMMA
    >> fs[]
    >> fs[is_instance_simps,TYPE_SUBST_compose]
  )
  >> fs[is_instance_simps]
QED

(* measure for wf_rel_tac *)

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

val type_interpretation_ext_of_def =
  tDefine "type_interpretation_ext_of0" `
  (type_interpretation_ext_of0
   ^mem ind upd ctxt Δ (Γ :mlstring # type -> 'U) ty =
   if ~terminating(subst_clos (dependency (upd::ctxt))) then
     One:'U
   else if ~(orth_ctxt (upd::ctxt) /\ extends_init (upd::ctxt)) then
     One:'U
   else if ty ∈ FST (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt))))  then
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
   else if (name,ty) ∈ SND (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt))))  then
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
    rpt strip_tac
    (* protect ext *)
    >> qabbrev_tac `ext = upd::ctxt`
    >- (
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
    >- (
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
        inhabited (type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ ty)) /\
  (∀^mem ind upd ctxt Δ Γ c ty.
     is_set_theory ^mem ⇒
        orth_ctxt (upd::ctxt) /\ terminating(subst_clos (dependency (upd::ctxt)))
        ∧ ctxt extends [] /\ ctxt extends init_ctxt
        ∧ upd updates ctxt
        ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
        ∧ (c,ty) ∈ ground_consts (sigof (upd::ctxt)) /\ inhabited ind
        /\ (c,ty) ∈ nonbuiltin_constinsts ⇒
        term_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ c ty ⋲
        ext_type_frag_builtins (type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ) ty
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
        (cheat (* Arve *)) >>
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
         qpat_x_assum `_ ⋲ _` (assume_tac o REWRITE_RULE[Once type_interpretation_ext_of_def]) >>
         Q.SUBGOAL_THEN `upd::ctxt = actxt` SUBST_ALL_TAC >- rw[Abbr`actxt`] >>
         rfs[] >>
         Cases_on `TYPE_SUBST sigma abs_type ∈
                   FST (indep_frag_upd actxt upd (total_fragment (sigof actxt)))` >-
           (cheat (* Arve *)) >>
         fs[] >> rfs[] >>
         drule_then (drule_then strip_assume_tac) abs_or_rep_matches_type_matches >>
         rveq >>
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
               first_x_assum MATCH_ACCEPT_TAC) >>
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
           fs[Abbr `actxt`]) >>
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

Theorem model_conservative_extension:
  is_set_theory ^mem ⇒
    ∀ctxt upd Δ Γ ind. orth_ctxt (upd::ctxt) /\ terminating(subst_clos (dependency (upd::ctxt)))
    /\ ctxt extends [] /\ ctxt extends init_ctxt /\ inhabited ind
    ∧ upd updates ctxt
    ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
    ⇒
        is_frag_interpretation (total_fragment (sigof (upd::ctxt)))
          (type_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ)
          (UNCURRY (term_interpretation_ext_of0 ^mem ind upd ctxt Δ Γ))
Proof
  rw[]
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

Theorem model_conservative_extension_prop:
  is_set_theory ^mem ⇒
    ∀ctxt upd Δ Γ ind. orth_ctxt (upd::ctxt) /\ terminating(subst_clos (dependency (upd::ctxt)))
    /\ ctxt extends [] /\ ctxt extends init_ctxt /\ inhabited ind
    ∧ upd updates ctxt
    ∧ is_frag_interpretation (total_fragment (sigof ctxt)) Δ Γ
    ⇒
      (!c ty. (c,ty) ∈ SND (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt))))
        ⇒ term_interpretation_ext_of ind upd ctxt Δ Γ c ty = Γ (c,ty))
      ∧
      (!ty. ty ∈ FST (indep_frag_upd (upd::ctxt) upd (total_fragment (sigof (upd::ctxt))))
        ⇒ type_interpretation_ext_of ind upd ctxt Δ Γ ty = Δ ty)
Proof
  rpt strip_tac
  >> `upd::ctxt extends []` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                    simp[GSYM extends_def])
  >> `upd::ctxt extends init_ctxt` by(rw[extends_def] >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
                                    simp[GSYM extends_def])
  >> fs[Once type_interpretation_ext_of_def,extends_init_def]
QED

(* example of a definitional theory *)

Definition example_thy_def:
  example_thy =
  let p = Var «a» Bool;
    t = Abs p p === Abs p p;
  in
    (ConstSpec T [(«d»,t)] (Var «d» (typeof t) === t))
    ::(ConstSpec T [(«c»,Const «d» (Tyvar «a»))] (Var «c» (Tyvar «a») === Const «d» (Tyvar «a»)))
    ::(NewConst «d» (Tyvar «a»))
    ::(NewConst «c» (Tyvar «a»))
    ::init_ctxt
End

(* termination of the depenency relation is skipped in the following *)
Triviality example_thy:
  extends_init example_thy /\ example_thy extends []
Proof
  reverse (conj_asm1_tac)
  >- imp_res_tac extends_init_NIL_orth_ctxt
  >> fs[extends_init_def]
  >> `is_std_sig (sigof example_thy)` by (
    fs[example_thy_def,init_ctxt_def,is_std_sig_def,FLOOKUP_UPDATE]
  )
  >> `orth_ctxt example_thy` by (
    fs[orth_ctxt_def,example_thy_def,init_ctxt_def]
    >> rw[]
    >> rfs[orth_ci_def,typeof_def,equation_def,orth_ty_def]
  )
  >> rw[extends_def,extends_init_def,example_thy_def]
  >> rpt (reverse (simp[Once RTC_CASES1] >> CONJ_ASM2_TAC))
  >- (
    simp[Once RTC_CASES1]
    >> rw[updates_cases,init_ctxt_def,type_ok_def]
  )
  >- rw[updates_cases,init_ctxt_def,type_ok_def]
  >- (
    rw[updates_cases,CLOSED_def,tyvars_def,tvars_def,VFREE_IN_def]
    >- (
      match_mp_tac (List.nth (CONJUNCTS proves_rules, 1))
      >> `theory_ok (thyof (TL (TL example_thy)))` by (
        pop_assum mp_tac
        >> rpt(CHANGED_TAC(simp[Once RTC_CASES1]))
        >> rpt strip_tac
        >> PURE_REWRITE_TAC[example_thy_def,LET_THM]
        >> CONV_TAC (DEPTH_CONV BETA_CONV)
        >> PURE_REWRITE_TAC[TL]
        >> ntac 2 (match_mp_tac (MP_CANON updates_theory_ok)
          >> conj_tac >- fs[])
        >> ACCEPT_TAC init_theory_ok
      )
      >> conj_tac
      >- fs[example_thy_def]
      >> conj_asm1_tac
      >- fs[equation_def,EQUATION_HAS_TYPE_BOOL]
      >> rw[term_ok_def,equation_def,FLOOKUP_UPDATE,type_ok_def,init_ctxt_def]
      >- (qexists_tac `[(Tyvar «a»,Tyvar «A»)]` >> fs[REV_ASSOCD_def])
    )
    >- fs[VFREE_IN_def,equation_def]
    >- fs[VFREE_IN_def,equation_def]
    >> fs[constspec_ok_def]
    >> conj_tac
    (* skipping termination for now *)
    >- cheat
    >> conj_tac
    >- (
      fs[example_thy_def]
      >> imp_res_tac orth_ctxt_CONS
    )
    >> fs[is_reserved_name_def]
  )
  >- (
    rw[updates_cases,CLOSED_def,tyvars_def,tvars_def,VFREE_IN_def]
    >- (
      match_mp_tac (List.nth (CONJUNCTS proves_rules, 1))
      >> `theory_ok (thyof (TL example_thy))` by (
        pop_assum mp_tac
        >> rpt(CHANGED_TAC(simp[Once RTC_CASES1]))
        >> rpt strip_tac
        >> PURE_REWRITE_TAC[example_thy_def,LET_THM]
        >> CONV_TAC (DEPTH_CONV BETA_CONV)
        >> PURE_REWRITE_TAC[TL]
        >> ntac 3 (match_mp_tac (MP_CANON updates_theory_ok)
          >> conj_tac >- fs[])
        >> ACCEPT_TAC init_theory_ok
      )
      >> conj_tac
      >- fs[example_thy_def]
      >> conj_asm1_tac
      >- fs[equation_def,EQUATION_HAS_TYPE_BOOL]
      >> rw[term_ok_def,equation_def,FLOOKUP_UPDATE,type_ok_def,init_ctxt_def]
      >- (qexists_tac `[(Bool,Tyvar «A»)]` >> fs[REV_ASSOCD_def])
      >> (qexists_tac `[(Fun Bool Bool,Tyvar «A»)]` >> fs[REV_ASSOCD_def])
    )
    >- (fs[VFREE_IN_def,equation_def] >> rw[DISJ_EQ_IMP])
    >- fs[tyvars_def,tvars_def,equation_def]
    >- (fs[tyvars_def,EQUATION_HAS_TYPE_BOOL,equation_def] >> fs[])
    >- (fs[tyvars_def,EQUATION_HAS_TYPE_BOOL,equation_def] >> fs[])
    >> fs[constspec_ok_def]
    >> conj_tac
    (* skipping termination for now *)
    >- cheat
    >> conj_tac
    >- fs[example_thy_def]
    >> conj_tac
    >- (qexists_tac `[(Bool,Tyvar «a»)]` >> fs[REV_ASSOCD_def,EQUATION_HAS_TYPE_BOOL,equation_def])
    >> fs[is_reserved_name_def]
  )
QED

Theorem example_dependencies:
  frag = SND (indep_frag example_thy [INR (Const «d» Bool)] (total_fragment (sigof example_thy)))
  ==> ~((«c»,Bool) ∈ frag) /\ («c»,Fun Bool Bool) ∈ frag
Proof
  `(RTC (subst_clos (dependency example_thy))) (INR (Const «c» Bool)) (INR (Const «d» Bool))` by (
    match_mp_tac TC_RTC
    >> fs[Once TC_CASES1]
    >> disj1_tac
    >> fs[subst_clos_def]
    >> map_every qexists_tac [`Const «c» (Tyvar «a»)`,`Const «d» (Tyvar «a»)`,`[(Bool,Tyvar «a»)]`]
    >> simp[INST_CORE_def,INST_def,REV_ASSOCD_def]
    >> fs[GSYM DEPENDENCY_EQUIV]
    >> EVAL_TAC
    >> fs[]
  )
  >> strip_tac
  >> conj_tac
  >- (
    rw[indep_frag_def]
    >> disj2_tac
    >> qexists_tac `[]`
    >> fs[LR_TYPE_SUBST_def,INST_def,INST_CORE_def]
  )
  >> fs[indep_frag_def]
  >> conj_asm1_tac
  >- (
    EVAL_TAC
    >> fs[FLOOKUP_UPDATE,tyvars_def,type_ok_def]
    >> fs[REWRITE_RULE[TYPE_SUBST_def] is_instance_simps]
  )
  >> rw[LR_TYPE_SUBST_def,LR_TYPE_SUBST_def,INST_CORE_def,INST_def]
  >> cheat
  (* dependency: Const c (Fun Bool Bool) -> Const d (Fun Bool Bool) -/-> Const d Bool  *)
(*
EVAL ``dependency example_thy x y``
|> (CONV_RULE (RHS_CONV (REWR_CONV (GSYM DEPENDENCY_EQUIV))))
|> EVAL_RULE
|> SIMP_RULE(srw_ss() ++ ETA_ss)[dependency_compute_def,MAP,TYPE_SUBST_def,REWRITE_RULE[TYPE_SUBST_def] is_instance_simps]
*)
QED

val _ = export_theory()
