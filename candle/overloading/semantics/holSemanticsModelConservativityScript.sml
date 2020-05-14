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

Triviality nonbuiltin_types_allTypes:
  !ty. ty ∈ nonbuiltin_types ==> allTypes' ty = [ty]
Proof
  Cases
  >> rw[IN_DEF,nonbuiltin_types_def,is_builtin_type_def,allTypes'_defn]
QED

Theorem extends_NIL_orth_ctxt:
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

Theorem bool_not_dependency:
  !ctxt x. extends_init ctxt ==> ~(dependency ctxt) (INL Bool) x
Proof
  rw[dependency_cases,DISJ_EQ_IMP]
  >> TRY (qpat_x_assum `[] = _` (assume_tac o GSYM))
  >> fs[]
  >> qpat_x_assum `MEM _ ctxt` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> rveq
  >> drule_then strip_assume_tac extends_NIL_orth_ctxt
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

Theorem constants_dependency:
  !ctxt c σ t. extends_init ctxt
  ∧ ALOOKUP (const_list ctxt) c = SOME σ
  ∧ MEM t (allTypes' σ)
  ==> dependency ctxt (INR (Const c σ)) (INL t)
Proof
  rw[]
  >> drule_then assume_tac extends_init_IS_SUFFIX
  >> dxrule_then strip_assume_tac extends_NIL_orth_ctxt
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

Theorem types_dependency:
  !a x ctxt. extends_init ctxt
  /\ MEM x (allTypes' a)
  ==> RTC (subst_clos (dependency ctxt)) (INL a) (INL x)
Proof
  ho_match_mp_tac allTypes'_defn_ind
  >> rw[]
  >> fs[allTypes'_defn]
  >> rpt (FULL_CASE_TAC >> fs[])
  >> fs[MEM_FLAT,MEM_MAP]
  >> rw[Once RTC_CASES1]
  >> disj2_tac
  >> qexists_tac `INL a`
  >> conj_tac
  >- (
    drule_then assume_tac extends_init_Fun
    >> match_mp_tac type_constructor_dependency
    >> fs[]
  )
  >- (
    first_x_assum drule
    >> disch_then match_mp_tac
    >> fs[]
  )
  >- (
    drule_then assume_tac extends_init_Fun
    >> match_mp_tac type_constructor_dependency
    >> fs[]
  )
  >> first_x_assum drule
  >> disch_then match_mp_tac
  >> fs[]
QED

(* independent fragment definition and properties *)

Definition indep_frag_def:
  indep_frag ctxt u (frag:(type -> bool) # (mlstring # type -> bool)) =
    let
      v = { x | ?s. (RTC (subst_clos (dependency ctxt))) x (LR_TYPE_SUBST s u) };
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
  !ctxt u. extends_init ctxt
  ⇒ is_sig_fragment (sigof ctxt) (indep_frag ctxt u (total_fragment (sigof ctxt)))
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
    >> `subst_clos (dependency ctxt) (INR (Const s c)) (INL c)` by (
      drule constants_dependency
      >> rpt (disch_then drule)
      >> disch_then assume_tac
      >> Cases_on `ty0`
      >- (
        fs[allTypes'_defn]
        >> fs[subst_clos_def]
        >> goal_assum (first_assum o mp_then Any mp_tac)
        >> qexists_tac `i`
        >> simp[INST_def,INST_CORE_def]
      )
      >> rveq
      >> pop_assum mp_tac
      >> imp_res_tac TYPE_SUBST_nonbuiltin_types
      >> rw[nonbuiltin_types_allTypes,subst_clos_def]
      >> map_every qexists_tac [`Tyapp m l`,`Const s (Tyapp m l)`,`i`]
      >> simp[INST_def,INST_CORE_def]
    )
    >> qpat_x_assum `!t. ~_` (assume_tac o SIMP_RULE(srw_ss())[] o ONCE_REWRITE_RULE[RTC_CASES_RTC_TWICE])
    >> fs[DISJ_EQ_IMP]
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
    >> rename1 `Const c (Fun a b)`
    >> ((
        qmatch_asmsub_abbrev_tac `MEM x (allTypes' a)`
        >> qabbrev_tac `nn = 0:num`
        >> `a <> Bool` by (CCONTR_TAC >> fs[is_builtin_type_def,allTypes'_defn])
        >> `a ∈ ground_types (sigof ctxt)` by fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def]
      ) ORELSE (
        qmatch_asmsub_abbrev_tac `MEM x (allTypes' b)`
        >> qabbrev_tac `nn = 1:num`
        >> `b <> Bool` by (CCONTR_TAC >> fs[is_builtin_type_def,allTypes'_defn])
        >> `b ∈ ground_types (sigof ctxt)` by fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def]
      ))
    >> CCONTR_TAC
    >> qpat_x_assum `!ρ. _` mp_tac
    >> fs[]
    >> rpt (goal_assum (first_assum o mp_then Any mp_tac))
    >> rw[Once RTC_CASES_RTC_TWICE]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[term_ok_def]
    >> imp_res_tac ALOOKUP_MEM
    >> fs[MEM_FLAT,MEM_MAP]
    >> rename1`TYPE_SUBST ρ σ`
    >> Cases_on `σ`
    >- (
      rw[Once RTC_CASES1]
      >> qexists_tac `INL (Fun a b)`
      >> conj_tac
      >- (
        drule_then drule constants_dependency
        >> rw[allTypes'_defn,subst_clos_def]
        >> goal_assum (first_assum o mp_then Any mp_tac)
        >> qexists_tac `ρ`
        >> simp[INST_def,INST_CORE_def]
      )
      >> match_mp_tac types_dependency
      >> fs[allTypes'_defn]
    )
    >> fs[]
    >> rpt (rename1`_ = MAP _ ll:type list` >> Cases_on `ll` >> fs[])
    >> rveq
    >> drule_all_then strip_assume_tac (CONJUNCT1 (SIMP_RULE(srw_ss())[EQ_IMP_THM,FORALL_AND_THM]subtype_at_allTypes_eq))
    >> qmatch_asmsub_abbrev_tac`subtype_at (TYPE_SUBST ρ aa) p = SOME x`
    >> Cases_on `?q α. IS_PREFIX p q /\ subtype_at aa q = SOME (Tyvar α)`
    (* x subtype (Tyvar α) subtype aa *)
    >- (
      fs[]
      >> rename1`Tyvar α`
      >> qpat_x_assum `IS_PREFIX _ _` (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])
      >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
      >> rename1`p = q ++ l`
      >> dxrule_then (qspec_then `l` assume_tac) subtype_at_decomp_path
      >> rw[Once RTC_CASES1]
      >> qexists_tac `INL (TYPE_SUBST ρ (Tyvar α))`
      >> conj_tac
      >- (
        fs[subst_clos_def]
        >> qmatch_asmsub_abbrev_tac`ALOOKUP _ c = SOME typ`
        >> map_every qexists_tac [`Tyvar α`,`Const c typ`,`ρ`]
        >> simp[INST_def,INST_CORE_def,Abbr`typ`]
        >> match_mp_tac constants_dependency
        >> ASM_REWRITE_TAC[]
        >> match_mp_tac (CONJUNCT2 (SIMP_RULE(srw_ss())[EQ_IMP_THM,FORALL_AND_THM]subtype_at_allTypes_eq))
        >> conj_tac
        >- fs[is_builtin_type_def,nonbuiltin_types_def]
        >> qexists_tac `(«fun»,nn)::q`
        >> rw[IS_PREFIX_APPEND,subtype_at_def,Abbr`nn`]
        >> rename1`_ = q' ++ l'`
        >> Cases_on `q'`
        >- fs[subtype_at_def,is_builtin_type_def,nonbuiltin_types_def]
        >> fs[] >> rveq >> fs[subtype_at_def]
        >> drule_all_then strip_assume_tac subtype_at_parent
        >> fs[]
        >> match_mp_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] nonbuiltin_types_TYPE_SUBST)
        >> dxrule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
        >> rename1`subtype_at (TYPE_SUBST _ _) tt = _`
        >> first_x_assum (qspec_then `tt` assume_tac)
        >> rfs[IS_PREFIX_APPEND]
        >> goal_assum drule
      )
      >> match_mp_tac types_dependency
      >> fs[]
      >> match_mp_tac (CONJUNCT2 (SIMP_RULE(srw_ss())[EQ_IMP_THM,FORALL_AND_THM]subtype_at_allTypes_eq))
      >> ASM_REWRITE_TAC[]
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> first_x_assum (qspec_then `q++_` (assume_tac o GEN_ALL))
      >> `!s. subtype_at (TYPE_SUBST ρ (Tyvar α)) s = subtype_at (TYPE_SUBST ρ aa) (q ++ s)` by (
        rpt strip_tac
        >> PURE_REWRITE_TAC[Once EQ_SYM_EQ]
        >> match_mp_tac subtype_at_decomp_path
        >> fs[subtype_at_TYPE_SUBST]
      )
      >> fs[]
    )
    (* (Tyvar α) subtype x subtype aa *)
    >> `IS_SOME (subtype_at aa p)` by (
      fs[DISJ_EQ_IMP]
      >> match_mp_tac subtype_TYPE_SUBST_Tyvar
      >> rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
    )
    >> fs[IS_SOME_EXISTS]
    >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
    >> rfs[]
    >> ONCE_REWRITE_TAC[RTC_CASES1]
    >> fs[]
    >> qexists_tac `INL x`
    >> rw[RTC_REFL,subst_clos_def]
    >> qmatch_asmsub_abbrev_tac `ALOOKUP _ _ = SOME typ`
    >> rename1`subtype_at aa p = SOME x'`
    >> map_every qexists_tac [`x'`,`Const c typ`,`ρ`]
    >> simp[Abbr`typ`,INST_def,INST_CORE_def]
    >> match_mp_tac constants_dependency
    >> ASM_REWRITE_TAC[]
    >> fs[subtype_at_allTypes_eq]
    >> conj_tac
    >- imp_res_tac TYPE_SUBST_nonbuiltin_types
    >> Q.REFINE_EXISTS_TAC `(«fun»,nn)::_`
    >> fs[subtype_at_def,Abbr`nn`]
    >> goal_assum (first_x_assum o mp_then Any mp_tac)
    >> rw[]
    >> Cases_on`q`
    >- fs[nonbuiltin_types_def,is_builtin_type_def,subtype_at_def]
    >> fs[] >> rveq >> fs[subtype_at_def]
    >> `IS_SOME (subtype_at aa p)` by (
      fs[DISJ_EQ_IMP]
      >> match_mp_tac subtype_TYPE_SUBST_Tyvar
      >> rpt (goal_assum (first_x_assum o mp_then Any mp_tac))
    )
    >> rename1`IS_PREFIX p tt`
    >> `IS_SOME (subtype_at aa tt)` by (
      fs[IS_PREFIX_APPEND]
      >> match_mp_tac subtype_at_IS_SOME_parent
      >> rfs[IS_SOME_EXISTS]
      >> goal_assum drule
    )
    >> fs[IS_SOME_EXISTS]
    >> drule_then (qspec_then `ρ` assume_tac) subtype_at_TYPE_SUBST
    >> fs[]
    >> rename1`~(xx ∈ nonbuiltin_types)`
    >> Cases_on`xx`
    >- rfs[DISJ_EQ_IMP]
    >> match_mp_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] nonbuiltin_types_TYPE_SUBST)
    >> qpat_x_assum `!q. _ ==> _` drule
    >> rw[]
    >> goal_assum drule
  ))
QED

val _ = export_theory()

