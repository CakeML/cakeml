(*
  Some lemmas about the semantics.
*)
open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory

val _ = new_theory"holSemanticsExtra"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val consts_of_term_RACONV = Q.prove(
  `!env tt.
     RACONV env tt /\ welltyped(FST tt) /\ welltyped(SND tt)
     /\ (!x y. MEM (x,y) env ==> ?n ty n' ty'. x = Var n ty /\ y = Var n' ty')
     ==> consts_of_term (FST tt) = consts_of_term (SND tt)`,
  simp[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac RACONV_strongind >> rpt strip_tac
  >> fs[consts_of_term_def,DISJ_IMP_THM]
  >> fs[DISJ_IMP_THM]);

Theorem consts_of_term_ACONV:
  ACONV a1 a2 /\ welltyped a1 /\ welltyped a2 ==> consts_of_term a1 = consts_of_term a2
Proof
  rw[ACONV_def] >> drule consts_of_term_RACONV >> simp[]
QED

val allTypes_RACONV = Q.prove(
  `!env tt.
     RACONV env tt /\ welltyped(FST tt) /\ welltyped(SND tt)
     /\ (!x y. MEM (x,y) env ==> ?n ty n'. x = Var n ty /\ y = Var n' ty)
     ==> allTypes (FST tt) = allTypes (SND tt)`,
  simp[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac RACONV_strongind >> rpt strip_tac
  >> fs[allTypes_def]
  >- (imp_res_tac ALPHAVARS_MEM >> fs[] >> first_x_assum drule >> simp[])
  >- fs[DISJ_IMP_THM]);

Theorem allTypes_ACONV:
  !t1 t2.
     ACONV t1 t2 /\ welltyped t1 /\ welltyped t2
     ==> allTypes t1 = allTypes t2
Proof
  rw[ACONV_def] >> drule allTypes_RACONV >> simp[]
QED

Theorem terms_of_frag_uninst_ACONV:
  !t1 t2 frag sigma. ACONV t1 t2 /\ welltyped t1 /\ welltyped t2 ==>
    (t1 ∈ terms_of_frag_uninst frag sigma <=> t2 ∈ terms_of_frag_uninst frag sigma)
Proof
  Cases_on `frag` >> rw[terms_of_frag_uninst_def]
  >> drule consts_of_term_ACONV >> simp[] >> disch_then kall_tac
  >> drule allTypes_ACONV >> simp[] >> disch_then kall_tac
QED

Theorem termsem_ext_equation:
  is_set_theory ^mem ⇒
    ∀sig frag δ γ v s t.
    is_sig_fragment sig frag ∧
    is_frag_interpretation frag δ γ ∧
    valuates_frag frag δ v sigma ∧
    s ∈ terms_of_frag_uninst frag sigma ∧ t ∈ terms_of_frag_uninst frag sigma ∧
    term_ok sig (s === t)
    ⇒ termsem_ext δ γ v sigma (s === t) = Boolean (termsem_ext δ γ v sigma s = termsem_ext δ γ v sigma t)
Proof
  rw[termsem_ext_def,termsem_def,equation_def,ext_term_frag_builtins_def]
  \\ qmatch_goalsub_abbrev_tac `Abstract s1 t1 f1 ' x1`
  \\ drule apply_abstract \\ disch_then (qspecl_then [`f1`,`x1`,`s1`,`t1`] mp_tac)
  \\ impl_tac
  >- (unabbrev_all_tac \\ simp[]
      \\ reverse conj_tac
      >- (drule abstract_in_funspace_matchable \\ disch_then match_mp_tac
          \\ metis_tac[boolean_in_boolset])
      \\ match_mp_tac termsem_in_type_ext \\ Cases_on `frag`
      \\ simp[] \\ asm_exists_tac \\ fs[valuates_frag_def]
      \\ rw[] \\ first_x_assum match_mp_tac
      \\ imp_res_tac VFREE_IN_subterm
      \\ imp_res_tac subterm_in_term_frag_uninst
      \\ imp_res_tac term_frag_uninst_in_type_frag
      \\ fs[]
     )
  \\ strip_tac \\ simp[]
  \\ unabbrev_all_tac \\ simp[]
  \\ qmatch_goalsub_abbrev_tac `Abstract s1 t1 f1 ' x1`
  \\ drule apply_abstract \\ disch_then (qspecl_then [`f1`,`x1`,`s1`,`t1`] mp_tac)
  \\ impl_tac
  >- (unabbrev_all_tac \\ simp[]
      \\ reverse conj_tac
      >- metis_tac[boolean_in_boolset]
      \\ fs[term_ok_def]
      \\ match_mp_tac termsem_in_type_ext \\ Cases_on `frag`
      \\ simp[] \\ asm_exists_tac \\ fs[valuates_frag_def]
      \\ rw[] \\ first_x_assum match_mp_tac
      \\ imp_res_tac VFREE_IN_subterm
      \\ imp_res_tac subterm_in_term_frag_uninst
      \\ imp_res_tac term_frag_uninst_in_type_frag
      \\ fs[]
     )
  \\ simp[]
QED

Theorem valuates_frag_builtins:
  valuates_frag frag (ext_type_frag_builtins δ) v sigma = valuates_frag frag δ v sigma
Proof
  rw[valuates_frag_def,ext_type_frag_idem]
QED

Theorem allTypes_typeof:
  !a. welltyped a ==> set(allTypes'(typeof a)) ⊆ set(allTypes a)
Proof
  Induct >> rw[allTypes_def] >> fs[allTypes'_defn] >> rw[]
  >> match_mp_tac SUBSET_TRANS
  >> asm_exists_tac >> simp[]
QED

Theorem terms_of_frag_equation:
  !frag sig a b. is_sig_fragment sig frag /\ welltyped (a === b) ==> (a === b ∈ terms_of_frag frag <=> a ∈ terms_of_frag frag /\ b ∈ terms_of_frag frag)
Proof
  rw[equation_def,EQ_IMP_THM]
  >> rpt(match_mp_tac terms_of_frag_combI >> asm_exists_tac >> rw[])
  >> drule terms_of_frag_combE \\ strip_tac
  >> rpt(first_assum dxrule \\ rpt(disch_then drule) \\ strip_tac)
  >> Cases_on `frag` >> FULL_SIMP_TAC std_ss [is_sig_fragment_def,terms_of_frag_def]
  >> rw[consts_of_term_def,allTypes_def,allTypes'_defn,INTER_DEF,
        nonbuiltin_constinsts_def,builtin_consts_def]
  >- (rw[PULL_FORALL,SUBSET_DEF] >> metis_tac[])
  >> match_mp_tac SUBSET_TRANS
  >> drule allTypes_typeof
  >> strip_tac >> asm_exists_tac
  >> fs[]
QED

Theorem terms_of_frag_uninst_equation:
  !frag sig sigma a b. is_sig_fragment sig frag /\ welltyped (a === b)
   ==> (a === b ∈ terms_of_frag_uninst frag sigma <=> a ∈ terms_of_frag_uninst frag sigma /\ b ∈ terms_of_frag_uninst frag sigma)
Proof
  rw[equation_def,EQ_IMP_THM]
  >> rpt(match_mp_tac terms_of_frag_uninst_combI >> asm_exists_tac >> rw[])
  >> drule terms_of_frag_uninst_combE \\ strip_tac
  >> rpt(first_assum dxrule \\ rpt(disch_then drule) \\ strip_tac)
  >> Cases_on `frag` >> FULL_SIMP_TAC std_ss [is_sig_fragment_def,terms_of_frag_uninst_def]
  >> rw[consts_of_term_def,allTypes_def,allTypes'_defn,INTER_DEF,
        nonbuiltin_constinsts_def,builtin_consts_def]
  >- (rw[PULL_FORALL,SUBSET_DEF] >> metis_tac[])
  >> qpat_x_assum `b ∈ _` mp_tac
  >> simp[IN_GSPEC_IFF] >> strip_tac
  >> match_mp_tac SUBSET_TRANS
  >> PURE_ONCE_REWRITE_TAC[CONJ_SYM] >> asm_exists_tac
  >> simp[]
  >> `set(allTypes' (typeof b)) ⊆ set(allTypes b)` by metis_tac[allTypes_typeof]
  >> pop_assum mp_tac
  >> rpt(pop_assum kall_tac)
  >> rw[SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  >> metis_tac[]
QED

val typeof_VSUBST = Q.prove(
  `!l a. EVERY (\(x,y). typeof x = typeof y) l /\ welltyped a
    ==> typeof (VSUBST l a) = typeof a`,
  Induct_on `a` >> rw[VSUBST_def]
  >- (rw[REV_ASSOCD_ALOOKUP] >> EVERY_CASE_TAC >> fs[] >> imp_res_tac ALOOKUP_MEM
      >> fs[EVERY_MEM,MEM_MAP] >> first_x_assum drule >> pairarg_tac >> fs[]
      >> rveq >> fs[])
  >> fs[dest_var_def]
  >> first_x_assum match_mp_tac >> fs[EVERY_FILTER_IMP])

val TYPE_SUBST_tyvars = Q.prove(`!sigma ty. tyvars ty = [] ==> TYPE_SUBST sigma ty = ty`,
  ho_match_mp_tac TYPE_SUBST_ind >> rpt strip_tac
  >> fs[tyvars_def]
  >> match_mp_tac LIST_EQ >> rw[]
  >> drule EL_MEM >> strip_tac
  >> first_x_assum drule
  >> impl_tac
  >> qmatch_asmsub_abbrev_tac `a1 = a2`
  >> `!x. MEM x a1 = MEM x a2` by simp[]
  >> unabbrev_all_tac >> fs[MEM_FOLDR_LIST_UNION]
  >> pop_assum(mp_tac o CONV_RULE(SWAP_FORALL_CONV))
  >> disch_then(qspec_then `EL x tys` mp_tac)
  >> simp[] >> simp[MEM_SPLIT]
  >> disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  >> disch_then(mp_tac o CONV_RULE(SWAP_FORALL_CONV))
  >> disch_then(qspec_then `[]` mp_tac)
  >> simp[] >> metis_tac[list_CASES,EL_MAP]);

val TYPE_SUBST_2 = Q.prove(
  `!sigma ty. EVERY (λty. tyvars ty = []) (MAP FST sigma)
    ==> TYPE_SUBST sigma (TYPE_SUBST sigma ty) = TYPE_SUBST sigma ty`,
  ho_match_mp_tac TYPE_SUBST_ind >> rpt strip_tac
  >- (fs[TYPE_SUBST_def] >> fs[REV_ASSOCD_ALOOKUP]
      >> PURE_TOP_CASE_TAC >> fs[]
      >> imp_res_tac ALOOKUP_MEM
      >> imp_res_tac ALOOKUP_NONE
      >> fs[MEM_MAP,EVERY_MEM] >> TRY(pairarg_tac >> rveq >> fs[])
      >> fs[] >> fs[REV_ASSOCD_ALOOKUP]
      >> every_case_tac >> fs[]
      >> match_mp_tac TYPE_SUBST_tyvars >> first_assum match_mp_tac >> simp[]
      >> Q.REFINE_EXISTS_TAC `(_,_)` >> simp[] >> metis_tac[])
  >> fs[TYPE_SUBST_def] >> match_mp_tac LIST_EQ
  >> rw[EL_MAP] >> drule EL_MEM
  >> metis_tac[]);

Theorem fresh_vsubst:
  !t x ty tm. ~VFREE_IN (Var x ty) t ==> VSUBST [(tm,Var x ty)] t = t
Proof
  Induct >> rpt strip_tac >> fs[VSUBST_def,VFREE_IN_def,REV_ASSOCD]
  >> first_assum drule >> strip_tac >> fs[] >> rw[] >> fs[]
QED

Theorem ALOOKUP_SOME_EQ:
  !l x y. ALOOKUP l x = SOME y <=> (?l1 l2.
    l = l1 ++ (x,y)::l2 /\ ALOOKUP l1 x = NONE)
Proof
  Induct >- fs[ALOOKUP_def]
  >> Cases >> rw[ALOOKUP_def,EQ_IMP_THM]
  >- (qexists_tac `[]` >> fs[])
  >- (Cases_on `l1` >> fs[] >> rveq >> fs[ALOOKUP_def])
  >- (Q.REFINE_EXISTS_TAC `(_,_)::l1`
      >> simp[])
  >- (Cases_on `l1` >> fs[] >> rveq >> fs[ALOOKUP_def] >> rfs[]
      >> HINT_EXISTS_TAC >> simp[])
QED

val VSUBST_id_lemma = Q.prove(
  `!tm ilist v. welltyped tm ==> VSUBST (ilist ++ [(Var x ty,Var x ty)]) tm = VSUBST ilist tm`,
  Induct >> rpt strip_tac
  >> fs[VSUBST_def,REV_ASSOCD_ALOOKUP]
  >- (rpt(PURE_TOP_CASE_TAC >> fs[]) >> fs[ALOOKUP_APPEND] >> rveq)
  >> Cases_on `Var x ty = Var n ty'`
  >> fs[FILTER_APPEND]
  >> PURE_ONCE_REWRITE_TAC [CONS_APPEND] >> PURE_ONCE_REWRITE_TAC [APPEND_ASSOC]
  >> fs[]);

Theorem RACONV_TRANS_matchable:
  !env env2 env3 t1 t2 t3. RACONV env2 (t1,t2) /\ RACONV env3 (t2,t3) /\
   MAP FST env2 = MAP FST env /\ MAP SND env2 = MAP FST env3 /\
   MAP SND env3 = MAP SND env /\ LENGTH env = LENGTH env2
   ==>
   RACONV env (t1,t3)
Proof
  rpt strip_tac
  >> qpat_x_assum `RACONV env2 _` assume_tac >> drule RACONV_TRANS
  >> disch_then(qspecl_then [`MAP SND env`,`t3`] mp_tac)
  >> simp[ZIP_MAP_FST_SND_EQ] >> disch_then match_mp_tac
  >> qpat_x_assum `MAP SND env3 = _` (assume_tac o GSYM)
  >> simp[ZIP_MAP_FST_SND_EQ]
QED

Theorem RACONV_TRANS_matchable2:
  !env vs t1 t2 t3. RACONV (ZIP (MAP FST env, vs)) (t1,t2)
   /\ RACONV (ZIP (vs, MAP SND env)) (t2,t3) /\
   LENGTH env = LENGTH vs
   ==>
   RACONV env (t1,t3)
Proof
  rpt strip_tac
  >> last_x_assum assume_tac >> drule RACONV_TRANS
  >> disch_then(qspecl_then [`MAP SND env`,`t3`] mp_tac)
  >> simp[MAP_ZIP,ZIP_MAP_FST_SND_EQ]
QED

val VSUBST_id =
  VSUBST_id_lemma
  |> CONV_RULE(SWAP_FORALL_CONV)
  |> Q.SPEC `[]` |> SIMP_RULE list_ss [VSUBST_NIL]
  |> curry save_thm "VSUBST_id"

Theorem NOT_VFREE_IN_VSUBST:
  !x ty v tm. ~VFREE_IN (Var x ty) tm /\ welltyped tm ==> VSUBST [(v,Var x ty)] tm = tm
Proof
  Induct_on `tm`
  >> rw[VSUBST_def,REV_ASSOCD]
  >> fs[]
QED

Theorem termsem_raconv:
  ∀env tp. RACONV env tp ⇒
      ∀δ γ sigma v1 v2.
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2)
          /\ VFREE_IN (Var x1 ty1) (FST tp) /\ VFREE_IN (Var x2 ty2) (SND tp) ⇒
            (termsem δ γ v1 sigma (Var x1 ty1) =
             termsem δ γ v2 sigma (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem δ γ v1 sigma (FST tp) = termsem δ γ v2 sigma (SND tp)
Proof
  ho_match_mp_tac RACONV_strongind >>
  rpt conj_tac >> simp[termsem_def] >>
  TRY (metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`RACONV env1 p1` >>
  qspecl_then[`env1`,`p1`]mp_tac RACONV_TYPE >>
  simp[Abbr`env1`,Abbr`p1`] >> strip_tac >>
  rw[termsem_def] >> fs[] >> rw[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[ALPHAVARS_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> fs[]
QED

Theorem termsem_aconv:
  ∀δ γ v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒
                 termsem δ γ v sigma t1 = termsem δ γ v sigma t2
Proof
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_def]
QED

Theorem termsem_frees:
  ∀δ γ t v1 v2.
      welltyped t ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ v1 (x,ty) = v2 (x,ty))
      ⇒ termsem δ γ v1 sigma t = termsem δ γ v2 sigma t
Proof
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[] >> rw[termsem_def] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[]
QED

Theorem TYPE_SUBSTf_TYPE_SUBST_compose:
  !ty sigma sigma2.
    TYPE_SUBSTf sigma (TYPE_SUBST sigma2 ty) =
    TYPE_SUBSTf (λx. TYPE_SUBSTf sigma (REV_ASSOCD (Tyvar x) sigma2 (Tyvar x))) ty
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >> rw[]
  >> simp[MAP_MAP_o,o_DEF,MAP_EQ_f] >> rw[]
  >> fs[EVERY_MEM]
QED

Theorem termsem_simple_inst:
  ∀δ γ sig sigma tm tyin tmenv.
      welltyped tm ∧ term_ok sig tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
      ⇒
      ∀v.
        termsem δ γ v sigma (simple_inst tyin tm) =
        termsem δ
          γ
          ((λ(x,ty). v (x, TYPE_SUBST tyin ty)))
          (λx. TYPE_SUBSTf sigma (REV_ASSOCD (Tyvar x) tyin (Tyvar x)))
          tm
Proof
  Induct_on `tm` >> simp[termsem_def,term_ok_def]
  >- rw[TYPE_SUBSTf_TYPE_SUBST_compose]
  >- (rw[]
      >> fs[ALL_DISTINCT_APPEND,IN_DISJOINT]
      >> metis_tac[]) >>
  rw[] >> rw[] >> rw[termsem_def,TYPE_SUBST_compose,TYPE_SUBSTf_TYPE_SUBST_compose] >>
  qmatch_abbrev_tac`Abstract _ r1 f1 = Abstract _ r2 f2` >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `r2 = r1` by (
    unabbrev_all_tac >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[TYPE_SUBSTf_TYPE_SUBST_compose]) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM] >>
  first_x_assum(qspecl_then[`δ`,`γ`,`sig`,`sigma`,`tyin`]mp_tac) >> simp[] >>
  impl_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac termsem_frees >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem termsem_INST:
  ∀δ γ sig sigma tm tyin.
      term_ok sig tm ⇒
      ∀v.
        termsem δ γ v sigma (INST tyin tm) =
        termsem δ γ
          ((λ(x,ty). v (x, TYPE_SUBST tyin ty)))
          (λx. TYPE_SUBSTf sigma (REV_ASSOCD (Tyvar x) tyin (Tyvar x)))
          tm
Proof
  rw[] >> imp_res_tac term_ok_welltyped >>
  Q.ISPECL_THEN[`{x | ∃ty. VFREE_IN (Var x ty) tm}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (INST tyin tm) (INST tyin fm)` by (
    match_mp_tac ACONV_INST >> metis_tac[] ) >>
  `welltyped (INST tyin tm)` by metis_tac[INST_WELLTYPED] >>
  `welltyped (INST tyin fm)` by metis_tac[INST_WELLTYPED] >>
  `termsem δ γ v sigma (INST tyin tm) = termsem δ γ v sigma (INST tyin fm)` by
    metis_tac[termsem_aconv] >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm} = {x | ∃ty. VFREE_IN (Var x ty) fm}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `INST tyin fm = simple_inst tyin fm` by
    metis_tac[INST_simple_inst] >>
  rw[] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv]
QED

Theorem terms_of_frag_uninst_equationE:
  !f a b sig sigma. is_sig_fragment sig f /\ a === b ∈ terms_of_frag_uninst f sigma
           /\ welltyped(a === b)==>
   a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma
Proof
  Cases >> simp[equation_def] >> rpt gen_tac >> rpt(disch_then strip_assume_tac)
  >> drule terms_of_frag_uninst_combE
  >> disch_then drule >> simp[] >> strip_tac
  >> drule terms_of_frag_uninst_combE
  >> disch_then drule
  >> simp[]
QED

Theorem terms_of_frag_uninst_welltyped:
  !t frag sigma. t ∈ terms_of_frag_uninst frag sigma ==> welltyped t
Proof
  Cases_on `frag` >> rw[terms_of_frag_uninst_def]
QED

Theorem allTypes'_nonbuiltin:
  !x y. MEM x (allTypes' y)
   ==> x ∈ nonbuiltin_types
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> ho_match_mp_tac allTypes'_defn_ind >> rpt strip_tac
  >> fs[allTypes'_defn,nonbuiltin_types_def,is_builtin_type_def]
  >> every_case_tac >> fs[is_builtin_type_def,EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  >> fs[quantHeuristicsTheory.LIST_LENGTH_2,is_builtin_name_def]
  >- metis_tac[]
QED

Theorem ground_TYPE_SUBSTf:
  ∀ty. (∀ty. tyvars (sigma ty) = []) ==> tyvars (TYPE_SUBSTf sigma ty) = []
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac >>
  rw[tyvars_def,TYPE_SUBSTf_def] >> fs[EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `a1 = a2` >>
  `set a1 = set a2` suffices_by (unabbrev_all_tac >> fs[]) >>
  unabbrev_all_tac >> PURE_ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  strip_tac >> PURE_ONCE_REWRITE_TAC[SIMP_RULE std_ss [IN_DEF] MEM_FOLDR_LIST_UNION] >>
  rw[GSYM IMP_DISJ_THM] >> fs[LIST_TO_SET_MAP]
QED

Theorem type_ok_TYPE_SUBSTf:
 !r sig sigma. (∀ty. tyvars (sigma ty) = []) /\
  (∀ty. type_ok sig (sigma ty)) /\
  type_ok sig r ==>
  type_ok sig (TYPE_SUBSTf sigma r)
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- simp[type_ok_def]
  >> fs[EVERY_MEM,type_ok_def,MEM_MAP,PULL_EXISTS]
QED

Theorem consts_of_term_ok:
  !tm q r. term_ok sig tm /\ (q,r) ∈ consts_of_term tm ==> type_ok (tysof sig) r
Proof
  Induct >> rw[term_ok_def,type_ok_def,consts_of_term_def] >> fs[consts_of_term_def]
  >> metis_tac[]
QED

Theorem consts_of_term_term_ok:
  !tm q r sig. term_ok sig tm /\ (q,r) ∈ consts_of_term tm ==> term_ok sig (Const q r)
Proof
  Induct >> rw[term_ok_def,type_ok_def,consts_of_term_def] >> fs[consts_of_term_def]
  >> metis_tac[term_ok_def]
QED

val TYPE_SUBSTf_lemma = Q.prove(
  `!ty sigma sigma'. (!tv. MEM tv (tyvars ty) ==> REV_ASSOCD (Tyvar tv) sigma' (Tyvar tv) = sigma tv) ==>
  TYPE_SUBSTf sigma ty = TYPE_SUBST sigma' ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- fs[tyvars_def]
  >> fs[tyvars_def,MEM_FOLDR_LIST_UNION,PULL_EXISTS]
  >> rw[MAP_EQ_f]
  >> fs[EVERY_MEM] >> rpt(first_x_assum drule) >> rpt strip_tac
  >> metis_tac[]);

Theorem TYPE_SUBSTf_TYPE_SUBST:
  !ty sigma. ?sigma'. TYPE_SUBSTf sigma ty = TYPE_SUBST sigma' ty
Proof
  rpt strip_tac
  >> qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tyvars ty)`
  >> match_mp_tac TYPE_SUBSTf_lemma
  >> rw[] >> fs[REV_ASSOCD_ALOOKUP,o_DEF]
  >> CASE_TAC
  >- fs[ALOOKUP_NONE,MEM_MAP,PULL_FORALL,GSYM RIGHT_FORALL_OR_THM]
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_MAP] >> rveq >> fs[]
QED

Theorem type_ok_TYPE_SUBSTf:
  ∀s sigma ty.
      type_ok s ty ∧
      (∀ty. type_ok s (sigma ty))
    ⇒ type_ok s (TYPE_SUBSTf sigma ty)
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBSTf_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM]
QED

Theorem FOLDR_LIST_UNION_empty:
  EVERY (λx. tyvars x = []) tys ==> (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys = [])
Proof
  Induct_on `tys` >> fs[]
QED

Theorem FOLDR_LIST_UNION_empty':
  (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys = []) ==> EVERY (λx. tyvars x = []) tys
Proof
  rw[] >> fs[EVERY_MEM] >>
  `!z. MEM z (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys) = F`
    by rw[] >>
  last_x_assum kall_tac >>
  fs[MEM_FOLDR_LIST_UNION] >> rw[] >>
  rename1 `MEM ty tys` >>
  fs[GSYM IMP_DISJ_THM] >>
  first_x_assum(assume_tac o CONV_RULE SWAP_FORALL_CONV) >>
  fs[GSYM PULL_FORALL] >>
  first_x_assum drule >>
  pop_assum kall_tac >>
  rename1 `l = []` >>
  Induct_on `l` >> simp[] >>
  metis_tac[]
QED

Theorem allTypes'_no_tyvars:
  !ty x. MEM x (allTypes' ty) /\ tyvars ty = [] ==> tyvars x = []
Proof
  ho_match_mp_tac allTypes'_defn_ind >> rw[tyvars_def]
  >> `!x. ~MEM x (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys)` by fs[]
  >> qpat_x_assum `_ = _` kall_tac
  >> fs[MEM_FOLDR_LIST_UNION,allTypes'_defn]
  >> EVERY_CASE_TAC >> fs[]
  >> fs[quantHeuristicsTheory.LIST_LENGTH_2] >> rveq >> fs[]
  >> fs[DISJ_IMP_THM,FORALL_AND_THM]
  >- (`tyvars e1 = []`
      by(CCONTR_TAC >> `?z. MEM z (tyvars e1)` by(Cases_on `tyvars e1` >> fs[] >> metis_tac[])
         >> metis_tac[]) >> metis_tac[])
  >- (`tyvars e2 = []`
      by(CCONTR_TAC >> `?z. MEM z (tyvars e2)` by(Cases_on `tyvars e2` >> fs[] >> metis_tac[])
         >> metis_tac[]) >> metis_tac[])
  >> fs[Once DISJ_SYM]
  >> fs[GSYM IMP_DISJ_THM]
  >> fs[tyvars_def]
  >> match_mp_tac FOLDR_LIST_UNION_empty >> fs[EVERY_MEM]
  >> rw[]
  >> CCONTR_TAC
  >> Cases_on `tyvars x` >> fs[]
  >> last_x_assum(qspecl_then [`h`,`x`] assume_tac)
  >> fs[]
QED

Theorem allTypes'_TYPE_SUBSTf_no_tyvars:
  ∀sigma y x. MEM x (allTypes' (TYPE_SUBSTf sigma y)) /\ (!ty. tyvars (sigma ty) = []) ==> tyvars x = []
Proof
  ho_match_mp_tac TYPE_SUBSTf_ind >> rpt strip_tac
  >- (fs[allTypes'_defn] >> match_mp_tac allTypes'_no_tyvars >> metis_tac[])
  >> fs[allTypes'_defn]
  >> PURE_FULL_CASE_TAC
  >- fs[]
  >> qpat_x_assum `MEM _ _` mp_tac
  >> simp[]
  >> PURE_FULL_CASE_TAC
  >- (fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,PULL_FORALL])
  >> simp[]
  >> rw[tyvars_def]
  >> match_mp_tac FOLDR_LIST_UNION_empty
  >> simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> rw[]
  >> metis_tac[ground_TYPE_SUBSTf]
QED

Theorem terms_of_frag_uninst_term_ok:
  !tm. term_ok sig tm /\ (∀ty. tyvars (sigma ty) = []) /\ (∀ty. type_ok (tysof sig) (sigma ty))
   ==> tm ∈ terms_of_frag_uninst (total_fragment sig) sigma
Proof
  rw[total_fragment_def,terms_of_frag_uninst_def]
  >> imp_res_tac term_ok_welltyped
  >> rw[consts_of_term_def,INTER_DEF,SUBSET_DEF]
  >> fs[MEM_MAP,MEM_FLAT,PULL_EXISTS,term_ok_def,ground_types_def]
  >> imp_res_tac allTypes'_nonbuiltin
  >- (fs[nonbuiltin_constinsts_def,ground_consts_def,builtin_consts_def,PULL_FORALL]
      >> Cases_on `x'` >> fs[ground_types_def,consts_of_term_def,ground_TYPE_SUBSTf]
      >> imp_res_tac consts_of_term_ok >> fs[type_ok_TYPE_SUBSTf]
      >> imp_res_tac consts_of_term_term_ok
      >> fs[term_ok_def]
      >> rveq
      >> fs[type_ok_TYPE_SUBSTf]
      >> Q.REFINE_EXISTS_TAC `MAP (TYPE_SUBST v ## I) i ++ v`
      >> fs[GSYM TYPE_SUBST_compose] >> metis_tac[TYPE_SUBSTf_TYPE_SUBST])
  >> drule allTypes'_TYPE_SUBSTf_no_tyvars
  >> disch_then drule >> simp[] >> strip_tac
  >> imp_res_tac allTypes_type_ok
  >> imp_res_tac type_ok_TYPE_SUBSTf
  >> imp_res_tac allTypes'_type_ok
QED

Theorem termsem_simple_subst:
  ∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀δ γ v sigma.
        termsem δ γ v sigma (simple_subst ilist tm) =
        termsem δ γ
                (v =++ MAP ((dest_var ## termsem δ γ v sigma) o (λ(s',s). (s,s')))
                           (REVERSE ilist))
                sigma tm
Proof
  Induct >> simp[termsem_def] >- (
    simp[REV_ASSOCD_ALOOKUP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> rw[termsem_def] >- (
      imp_res_tac ALOOKUP_FAILS >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >> metis_tac[] ) >>
    rw[GSYM MAP_MAP_o] >>
    qmatch_assum_abbrev_tac`ALOOKUP ls (Var s ty) = SOME x` >>
    Q.ISPECL_THEN[`ls`,`termsem δ γ v sigma`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[]) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`il = FILTER X ilist` >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `simple_subst il tm has_type typeof tm` by (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    imp_res_tac WELLTYPED >>
    fs[Abbr`il`,EVERY_MEM,EVERY_FILTER,FORALL_PROD] >>
    rw[] >> res_tac >> rw[] ) >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  simp[termsem_def] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM] >> rw[] >>
  qmatch_abbrev_tac `termsem δ γ vv sigma xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  impl_tac >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`δ`,`γ`,`vv`,`sigma`]mp_tac) >>
  rw[Abbr`vv`,Abbr`yy`] >>
  rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
  simp[FUN_EQ_THM,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  Cases >>
  simp[GSYM MAP_MAP_o] >>
  BasicProvers.CASE_TAC >>
  qmatch_assum_abbrev_tac`ALOOKUP (MAP (dest_var ## f) ls) (z,tyr) = X` >>
  qunabbrev_tac`X` >>
  Q.ISPECL_THEN[`ls`,`f`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`,Abbr`il`,MEM_FILTER] >> metis_tac[])) >>
  qmatch_assum_abbrev_tac`Abbrev(il = FILTER P ilist)` >>
  qmatch_assum_abbrev_tac`Abbrev(ls = MAP sw il)` >>
  `ls = FILTER (P o sw) (MAP sw ilist)` by (
    simp[Abbr`ls`,Abbr`il`] >>
    simp[rich_listTheory.FILTER_MAP] >>
    simp[Abbr`P`,Abbr`sw`,combinTheory.o_DEF,UNCURRY,LAMBDA_PROD] ) >>
  qunabbrev_tac`ls` >>
  simp[ALOOKUP_FILTER,Abbr`P`,Abbr`sw`,combinTheory.o_DEF,LAMBDA_PROD] >- (
    rw[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
    qmatch_assum_abbrev_tac`P ⇒ ALOOKUP ls vv = NONE` >>
    Q.ISPECL_THEN[`ls`,`termsem δ γ v sigma`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem δ γ v sigma`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[welltyped_def]
QED

Theorem termsem_VSUBST:
   ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀δ γ v sigma.
       termsem δ γ v sigma (VSUBST ilist tm) =
        termsem δ γ
                (v =++ MAP ((dest_var ## termsem δ γ v sigma) o (λ(s',s). (s,s')))
                           (REVERSE ilist))
                sigma tm
Proof
  rw[] >>
  Q.ISPECL_THEN[`{y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` by (
    match_mp_tac ACONV_VSUBST >> metis_tac[] ) >>
  `welltyped (VSUBST ilist tm)` by metis_tac[VSUBST_WELLTYPED] >>
  `welltyped (VSUBST ilist fm)` by metis_tac[VSUBST_WELLTYPED] >>
  `termsem δ γ v sigma (VSUBST ilist tm) = termsem δ γ v sigma (VSUBST ilist fm)` by
    metis_tac[termsem_aconv] >>
  `VSUBST ilist fm = simple_subst ilist fm` by
    metis_tac[VSUBST_simple_subst] >>
  rw[] >>
  metis_tac[termsem_simple_subst,termsem_aconv]
QED

Theorem is_interpretation_reduce:
  ∀δ γ tyenv tmenv tyenv' tmenv'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
     is_frag_interpretation (total_fragment (tyenv',tmenv')) δ γ ⇒
     is_frag_interpretation (total_fragment (tyenv,tmenv)) δ γ
Proof
  rw[total_fragment_def,is_frag_interpretation_def,is_type_frag_interpretation_def,GSYM PFORALL_THM]
  >- (first_x_assum match_mp_tac >> fs[ground_types_def,tyvars_def] >> metis_tac[type_ok_extend])
  >> first_x_assum match_mp_tac
  >> fs[ground_consts_def,ground_types_def] >> metis_tac[type_ok_extend,term_ok_extend]
QED

Theorem inhabited_ext:
  !tyfrag ty δ. is_set_theory ^mem ==> ty ∈ builtin_closure tyfrag
   /\ tyfrag ⊆ nonbuiltin_types
   /\ (∀ty. ty ∈ tyfrag ⇒ inhabited (δ ty))
   ==> inhabited (ext_type_frag_builtins δ ty)
Proof
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,IN_DEF] >> strip_tac
  >> ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >- (simp[Once ext_type_frag_builtins_def] >>
      rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
      fs[nonbuiltin_types_def,SUBSET_DEF,IN_DEF] >>
      rpt(first_x_assum drule) >> fs[is_builtin_type_def])
  >- (simp[Once ext_type_frag_builtins_def] >>
      metis_tac[boolean_in_boolset])
  >- (simp[Once ext_type_frag_builtins_def] >>
      metis_tac[funspace_inhabited])
QED

Theorem exists_valuation:
  !frag sig δ γ ty. is_set_theory ^mem ==>
    is_frag_interpretation frag δ γ
    /\ is_sig_fragment sig frag
    /\ ty ∈ ground_types sig
    ==> ?v:'U valuation. valuates_frag frag δ v (K ty)
Proof
  Cases
  >> rw[is_frag_interpretation_def,is_type_frag_interpretation_def,valuates_frag_def,
        types_of_frag_def,is_sig_fragment_def]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [PFORALL_THM]
  >> simp[ELIM_UNCURRY]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [GSYM SKOLEM_THM]
  >> Cases >> rw[RIGHT_EXISTS_IMP_THM]
  >> metis_tac[inhabited_ext]
QED

Theorem exists_sigma_valuation:
  !frag sig δ γ sigma. is_set_theory ^mem ==>
    is_frag_interpretation frag δ γ
    /\ is_sig_fragment sig frag
    /\ (!ty. sigma ty ∈ ground_types sig)
    ==> ?v:'U valuation. valuates_frag frag δ v sigma
Proof
  Cases
  >> rw[is_frag_interpretation_def,is_type_frag_interpretation_def,valuates_frag_def,
        types_of_frag_def,is_sig_fragment_def]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [PFORALL_THM]
  >> simp[ELIM_UNCURRY]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [GSYM SKOLEM_THM]
  >> Cases >> rw[RIGHT_EXISTS_IMP_THM]
  >> metis_tac[inhabited_ext]
QED

Theorem exists_valuation_bool:
  !frag sig δ γ. is_set_theory ^mem ==>
    is_frag_interpretation frag δ γ
    /\ is_sig_fragment sig frag
    ==> ?v:'U valuation. valuates_frag frag δ v (K Bool)
Proof
  Cases
  >> rw[is_frag_interpretation_def,is_type_frag_interpretation_def,valuates_frag_def,
        types_of_frag_def,is_sig_fragment_def]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [PFORALL_THM]
  >> simp[ELIM_UNCURRY]
  >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC [GSYM SKOLEM_THM]
  >> Cases >> rw[RIGHT_EXISTS_IMP_THM]
  >> metis_tac[inhabited_ext]
QED

Theorem satisfies_reduce:
  is_set_theory ^mem ⇒
    ∀δ γ tyenv tmenv tyenv' tmenv' h c.
      is_std_sig (tyenv,tmenv) ∧
      tyenv ⊑ tyenv' ∧
      tmenv ⊑ tmenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      is_frag_interpretation (total_fragment(tyenv',tmenv')) δ γ ∧
      satisfies_t (tyenv',tmenv') δ γ (h,c) ⇒
      satisfies_t (tyenv,tmenv) δ γ (h,c)
Proof
  rw[satisfies_t_def,satisfies_def] >>
  drule exists_sigma_valuation >>
  qspec_then `(tyenv',tmenv')` assume_tac total_fragment_is_fragment >>
  rpt(disch_then drule) >> disch_then(qspec_then `sigma` mp_tac) >>
  impl_tac >- (rw[ground_types_def] >> metis_tac[type_ok_extend]) >>
  strip_tac >> rename1 `valuates_frag _ _ v2` >>
  `valuates_frag
    (total_fragment (tyenv',tmenv')) δ
    (λ(x,ty). if TYPE_SUBSTf sigma ty ∈ types_of_frag(total_fragment(tyenv,tmenv)) then
                v(x,ty)
              else v2(x,ty)) sigma`
    by(fs[valuates_frag_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `valuates_frag _ _ v3` >>
  imp_res_tac term_ok_welltyped >>
  drule_then(qspecl_then [`sigma`,`^mem`] mp_tac) termsem_frees >>
  disch_then(qspecl_then [`δ`,`γ`,`v`,`v3`] mp_tac) >>
  impl_tac >-
    (rw[] >> imp_res_tac VFREE_IN_subterm >>
     qspec_then `(tyenv,tmenv)` assume_tac total_fragment_is_fragment >>
     drule subterm_in_term_frag_uninst >> rpt(disch_then drule) >>
     strip_tac >>
     drule term_frag_uninst_in_type_frag >> rpt(disch_then drule) >>
     rw[Abbr `v3`]) >>
  simp[] >> disch_then kall_tac >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  rpt conj_tac
  >- metis_tac[type_ok_extend]
  >- (fs[EVERY_MEM,ground_terms_uninst_def] >> rw[] >>
      rpt(first_x_assum drule) >> rpt strip_tac >>
      asm_exists_tac >> fs[ground_types_def] >>
      metis_tac[type_ok_extend])
  >- (fs[ground_terms_uninst_def,ground_types_def] >>
      asm_exists_tac >> fs[] >> metis_tac[type_ok_extend])
  >- (fs[terms_of_frag_uninst_def,total_fragment_def,SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS,
         ground_consts_def,ground_types_def] >>
      metis_tac[type_ok_extend,term_ok_extend])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      fs[terms_of_frag_uninst_def,total_fragment_def,SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS,
         ground_consts_def,ground_types_def] >>
      metis_tac[type_ok_extend,term_ok_extend])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      imp_res_tac term_ok_welltyped >>
      drule_then(qspecl_then [`sigma`,`^mem`] mp_tac) termsem_frees >>
      disch_then(qspecl_then [`δ`,`γ`,`v`,`v3`] mp_tac) >>
      impl_tac >-
        (rw[] >> imp_res_tac VFREE_IN_subterm >>
         qspec_then `(tyenv,tmenv)` assume_tac total_fragment_is_fragment >>
         drule subterm_in_term_frag_uninst >> rpt(disch_then drule) >>
         strip_tac >>
         drule term_frag_uninst_in_type_frag >> rpt(disch_then drule) >>
         rw[Abbr `v3`]) >>
      simp[])
QED

Theorem models_reduce:
  is_set_theory ^mem ⇒
    ∀δ γ tyenv tmenv axs tyenv' tmenv' axs'.
     is_std_sig (tyenv,tmenv) ∧
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧ (axs ⊆ axs') ∧
     models δ γ ((tyenv',tmenv'),axs') ∧
     (∀p. p ∈ axs ⇒ (term_ok (tyenv,tmenv)) p)
     ⇒
     models δ γ ((tyenv,tmenv),axs)
Proof
  rw[models_def]
  >- imp_res_tac is_interpretation_reduce
  >> match_mp_tac (MP_CANON satisfies_reduce)
  >> simp[]
  >> rpt(asm_exists_tac >> simp[])
  >> conj_tac
  >- (qspec_then `(tyenv',tmenv')` assume_tac total_fragment_is_fragment
      >> fs[total_fragment_def] >> drule is_frag_interpretation_ext
      >> disch_then drule >> disch_then drule >> strip_tac
      >> fs[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def,
            ext_type_frag_idem]
      >> rw[]
      >- (first_x_assum match_mp_tac
          >> fs[IN_DEF,builtin_closure_rules,INTER_DEF])
      >> fs[ELIM_UNCURRY])
  >> metis_tac[SUBSET_DEF]
QED

val equal_on_def = Define`
  equal_on (sig:sig) i i' ⇔
  fleq (total_fragment sig,i) (total_fragment sig, i')`

val _ = export_theory()
