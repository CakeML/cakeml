open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory

val _ = new_theory"holSemanticsExtra"

val mem = ``mem:'U->'U->bool``

(* TODO: change definition in holSyntaxScript *)
val is_builtin_type_def = Q.prove(
  `(∀v0. is_builtin_type (Tyvar v0) ⇔ F) ∧
     ∀m ty. is_builtin_type (Tyapp m ty) ⇔
        ((m = strlit "fun" /\ LENGTH ty = 2) \/
         (m = strlit "bool" /\ LENGTH ty = 0))`,
  cheat);

val consts_of_term_RACONV = Q.prove(
  `!env tt.
     RACONV env tt /\ welltyped(FST tt) /\ welltyped(SND tt)
     /\ (!x y. MEM (x,y) env ==> ?n ty n' ty'. x = Var n ty /\ y = Var n' ty')
     ==> consts_of_term (FST tt) = consts_of_term (SND tt)`,
  simp[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac RACONV_strongind >> rpt strip_tac
  >> fs[consts_of_term_def,DISJ_IMP_THM]
  >> fs[DISJ_IMP_THM]);

val consts_of_term_ACONV = Q.store_thm("consts_of_term_ACONV",
  `ACONV a1 a2 /\ welltyped a1 /\ welltyped a2 ==> consts_of_term a1 = consts_of_term a2`,
  rw[ACONV_def] >> drule consts_of_term_RACONV >> simp[]);

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

val allTypes_ACONV = Q.store_thm("allTypes_ACONV",
  `!t1 t2.
     ACONV t1 t2 /\ welltyped t1 /\ welltyped t2
     ==> allTypes t1 = allTypes t2`,
  rw[ACONV_def] >> drule allTypes_RACONV >> simp[]);

val terms_of_frag_uninst_ACONV = Q.store_thm("terms_of_frag_uninst_ACONV",
  `!t1 t2 frag sigma. ACONV t1 t2 /\ welltyped t1 /\ welltyped t2 ==>
    (t1 ∈ terms_of_frag_uninst frag sigma <=> t2 ∈ terms_of_frag_uninst frag sigma)`,
  Cases_on `frag` >> rw[terms_of_frag_uninst_def]
  >> drule consts_of_term_ACONV >> simp[] >> disch_then kall_tac
  >> drule allTypes_ACONV >> simp[] >> disch_then kall_tac);

val termsem_ext_equation = Q.store_thm("termsem_ext_equation",
  `is_set_theory ^mem ⇒
    ∀sig frag δ γ v s t.
    is_sig_fragment sig frag ∧
    is_frag_interpretation frag δ γ ∧
    valuates_frag δ v sigma ∧
    s ∈ terms_of_frag_uninst frag sigma ∧ t ∈ terms_of_frag_uninst frag sigma ∧
    term_ok sig (s === t)
    ⇒ termsem_ext δ γ v sigma (s === t) = Boolean (termsem_ext δ γ v sigma s = termsem_ext δ γ v sigma t)`,
  rw[termsem_ext_def,termsem_def,equation_def,ext_term_frag_builtins_def]
  \\ qmatch_goalsub_abbrev_tac `Abstract s1 t1 f1 ' x1`
  \\ drule apply_abstract \\ disch_then (qspecl_then [`f1`,`x1`,`s1`,`t1`] mp_tac)
  \\ impl_tac
  >- (unabbrev_all_tac \\ simp[]
      \\ reverse conj_tac
      >- (drule abstract_in_funspace_matchable \\ disch_then match_mp_tac
          \\ metis_tac[boolean_in_boolset])
      \\ match_mp_tac termsem_in_type_ext \\ Cases_on `frag`
      \\ simp[] \\ asm_exists_tac \\ fs[valuates_frag_def])
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
      \\ simp[] \\ asm_exists_tac \\ fs[valuates_frag_def])
  \\ simp[]);

val valuates_frag_builtins = Q.store_thm("valuates_frag_builtins",
  `valuates_frag (ext_type_frag_builtins δ) v sigma = valuates_frag δ v sigma`,
  rw[valuates_frag_def,ext_type_frag_idem]);

val allTypes_typeof = Q.store_thm("allTypes_typeof",
  `!a. welltyped a ==> set(allTypes'(typeof a)) ⊆ set(allTypes a)`,
  Induct >> rw[allTypes_def] >> fs[allTypes'_def] >> rw[]
  >> match_mp_tac SUBSET_TRANS
  >> asm_exists_tac >> simp[]);

val terms_of_frag_equation = Q.store_thm("terms_of_frag_equation",
  `!frag sig a b. is_sig_fragment sig frag /\ welltyped (a === b) ==> (a === b ∈ terms_of_frag frag <=> a ∈ terms_of_frag frag /\ b ∈ terms_of_frag frag)`,
  rw[equation_def,EQ_IMP_THM]
  >> rpt(match_mp_tac terms_of_frag_combI >> asm_exists_tac >> rw[])
  >> drule terms_of_frag_combE \\ strip_tac
  >> rpt(first_assum dxrule \\ rpt(disch_then drule) \\ strip_tac)
  >> Cases_on `frag` >> FULL_SIMP_TAC std_ss [is_sig_fragment_def,terms_of_frag_def]
  >> rw[consts_of_term_def,allTypes_def,allTypes'_def,INTER_DEF,
        nonbuiltin_constinsts_def,builtin_consts_def]
  >- (rw[PULL_FORALL,SUBSET_DEF] >> metis_tac[])
  >> match_mp_tac SUBSET_TRANS
  >> drule allTypes_typeof
  >> strip_tac >> asm_exists_tac
  >> fs[]);    

val terms_of_frag_uninst_equation = Q.store_thm("terms_of_frag_uninst_equation",
  `!frag sig sigma a b. is_sig_fragment sig frag /\ welltyped (a === b) ==> (a === b ∈ terms_of_frag_uninst frag sigma <=> a ∈ terms_of_frag_uninst frag sigma /\ b ∈ terms_of_frag_uninst frag sigma)`,
  rw[equation_def,EQ_IMP_THM]
  >> rpt(match_mp_tac terms_of_frag_uninst_combI >> asm_exists_tac >> rw[])
  >> drule terms_of_frag_uninst_combE \\ strip_tac
  >> rpt(first_assum dxrule \\ rpt(disch_then drule) \\ strip_tac)
  >> Cases_on `frag` >> FULL_SIMP_TAC std_ss [is_sig_fragment_def,terms_of_frag_uninst_def]
  >> rw[consts_of_term_def,allTypes_def,allTypes'_def,INTER_DEF,
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
  >> metis_tac[]);

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

val fresh_vsubst = Q.store_thm("fresh_vsubst",
  `!t x ty tm. ~VFREE_IN (Var x ty) t ==> VSUBST [(tm,Var x ty)] t = t`,
  Induct >> rpt strip_tac >> fs[VSUBST_def,VFREE_IN_def,REV_ASSOCD]
  >> first_assum drule >> strip_tac >> fs[] >> rw[] >> fs[]);

val ALOOKUP_SOME_EQ = Q.store_thm("ALOOKUP_SOME_EQ",
  `!l x y. ALOOKUP l x = SOME y <=> (?l1 l2.
    l = l1 ++ (x,y)::l2 /\ ALOOKUP l1 x = NONE)`,
  Induct >- fs[ALOOKUP_def]
  >> Cases >> rw[ALOOKUP_def,EQ_IMP_THM]
  >- (qexists_tac `[]` >> fs[])
  >- (Cases_on `l1` >> fs[] >> rveq >> fs[ALOOKUP_def])
  >- (Q.REFINE_EXISTS_TAC `(_,_)::l1`
      >> simp[])
  >- (Cases_on `l1` >> fs[] >> rveq >> fs[ALOOKUP_def] >> rfs[]
      >> HINT_EXISTS_TAC >> simp[]));

val VSUBST_id_lemma = Q.prove(
  `!tm ilist v. welltyped tm ==> VSUBST (ilist ++ [(Var x ty,Var x ty)]) tm = VSUBST ilist tm`,
  Induct >> rpt strip_tac
  >> fs[VSUBST_def,REV_ASSOCD_ALOOKUP]
  >- (rpt(PURE_TOP_CASE_TAC >> fs[]) >> fs[ALOOKUP_APPEND] >> rveq)
  >> Cases_on `Var x ty = Var n ty'`
  >> fs[FILTER_APPEND]
  >> PURE_ONCE_REWRITE_TAC [CONS_APPEND] >> PURE_ONCE_REWRITE_TAC [APPEND_ASSOC]
  >> fs[]);

val RACONV_TRANS_matchable = Q.store_thm("RACONV_TRANS_matchable",
  `!env env2 env3 t1 t2 t3. RACONV env2 (t1,t2) /\ RACONV env3 (t2,t3) /\
   MAP FST env2 = MAP FST env /\ MAP SND env2 = MAP FST env3 /\
   MAP SND env3 = MAP SND env /\ LENGTH env = LENGTH env2
   ==>
   RACONV env (t1,t3)`,
  rpt strip_tac
  >> qpat_x_assum `RACONV env2 _` assume_tac >> drule RACONV_TRANS
  >> disch_then(qspecl_then [`MAP SND env`,`t3`] mp_tac)
  >> simp[ZIP_MAP_FST_SND_EQ] >> disch_then match_mp_tac
  >> qpat_x_assum `MAP SND env3 = _` (assume_tac o GSYM)
  >> simp[ZIP_MAP_FST_SND_EQ]);

val RACONV_TRANS_matchable2 = Q.store_thm("RACONV_TRANS_matchable2",
  `!env vs t1 t2 t3. RACONV (ZIP (MAP FST env, vs)) (t1,t2)
   /\ RACONV (ZIP (vs, MAP SND env)) (t2,t3) /\
   LENGTH env = LENGTH vs
   ==>
   RACONV env (t1,t3)`,
  rpt strip_tac
  >> last_x_assum assume_tac >> drule RACONV_TRANS
  >> disch_then(qspecl_then [`MAP SND env`,`t3`] mp_tac)
  >> simp[MAP_ZIP,ZIP_MAP_FST_SND_EQ]);

val VSUBST_id =
  VSUBST_id_lemma
  |> CONV_RULE(SWAP_FORALL_CONV)
  |> Q.SPEC `[]` |> SIMP_RULE list_ss [VSUBST_NIL]
  |> curry save_thm "VSUBST_id"

val NOT_VFREE_IN_VSUBST = Q.store_thm("NOT_VFREE_IN_VSUBST",
  `!x ty v tm. ~VFREE_IN (Var x ty) tm /\ welltyped tm ==> VSUBST [(v,Var x ty)] tm = tm`,
  Induct_on `tm`
  >> rw[VSUBST_def,REV_ASSOCD]
  >> fs[]);

val termsem_raconv = Q.store_thm("termsem_raconv",
  `∀env tp. RACONV env tp ⇒
      ∀δ γ sigma v1 v2.
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2)
          /\ VFREE_IN (Var x1 ty1) (FST tp) /\ VFREE_IN (Var x2 ty2) (SND tp) ⇒
            (termsem δ γ v1 sigma (Var x1 ty1) =
             termsem δ γ v2 sigma (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem δ γ v1 sigma (FST tp) = termsem δ γ v2 sigma (SND tp)`,
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
  rw[] >> fs[])

val termsem_aconv = Q.store_thm("termsem_aconv",
  `∀δ γ v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒
                 termsem δ γ v sigma t1 = termsem δ γ v sigma t2`,
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_def])

val termsem_frees = Q.store_thm("termsem_frees",
  `∀δ γ t v1 v2.
      welltyped t ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ v1 (x,ty) = v2 (x,ty))
      ⇒ termsem δ γ v1 sigma t = termsem δ γ v2 sigma t`,
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[] >> rw[termsem_def] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[])

val TYPE_SUBSTf_TYPE_SUBST_compose = Q.store_thm("TYPE_SUBSTf_TYPE_SUBST_compose",
  `!ty sigma sigma2.
    TYPE_SUBSTf sigma (TYPE_SUBST sigma2 ty) =
    TYPE_SUBSTf (λx. TYPE_SUBSTf sigma (REV_ASSOCD (Tyvar x) sigma2 (Tyvar x))) ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >> rw[]
  >> simp[MAP_MAP_o,o_DEF,MAP_EQ_f] >> rw[]
  >> fs[EVERY_MEM]);

val termsem_simple_inst = Q.store_thm("termsem_simple_inst",
  `∀δ γ sig sigma tm tyin tmenv.
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
          tm`,
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
  metis_tac[]);

val termsem_INST = Q.store_thm("termsem_INST",
  `∀δ γ sig sigma tm tyin.
      term_ok sig tm ⇒
      ∀v.
        termsem δ γ v sigma (INST tyin tm) =
        termsem δ γ
          ((λ(x,ty). v (x, TYPE_SUBST tyin ty)))
          (λx. TYPE_SUBSTf sigma (REV_ASSOCD (Tyvar x) tyin (Tyvar x)))
          tm`,
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
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv]);

val terms_of_frag_uninst_equationE = Q.store_thm("terms_of_frag_uninst_equationE",
  `!f a b sig sigma. is_sig_fragment sig f /\ a === b ∈ terms_of_frag_uninst f sigma
           /\ welltyped(a === b)==> 
   a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma`,
  Cases >> simp[equation_def] >> rpt gen_tac >> rpt(disch_then strip_assume_tac)
  >> drule terms_of_frag_uninst_combE
  >> disch_then drule >> simp[] >> strip_tac
  >> drule terms_of_frag_uninst_combE
  >> disch_then drule
  >> simp[]);                               

val terms_of_frag_uninst_welltyped = Q.store_thm("terms_of_frag_uninst_welltyped",
  `!t frag sigma. t ∈ terms_of_frag_uninst frag sigma ==> welltyped t`,
  Cases_on `frag` >> rw[terms_of_frag_uninst_def]);

val allTypes'_nonbuiltin = Q.store_thm("allTypes'_nonbuiltin",
  `!x y. MEM x (allTypes' y)
   ==> x ∈ nonbuiltin_types`,
  CONV_TAC SWAP_FORALL_CONV
  >> ho_match_mp_tac allTypes'_ind >> rpt strip_tac
  >> fs[allTypes'_def,nonbuiltin_types_def,is_builtin_type_def]
  >> every_case_tac >> fs[is_builtin_type_def,EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  >> fs[quantHeuristicsTheory.LIST_LENGTH_2,is_builtin_name_def]
  >- metis_tac[]);

val ground_TYPE_SUBSTf = Q.store_thm("ground_TYPE_SUBSTf",
  `∀ty. (∀ty. tyvars (sigma ty) = []) ==> tyvars (TYPE_SUBSTf sigma ty) = []`,
  ho_match_mp_tac type_ind >> rpt strip_tac >>
  rw[tyvars_def,TYPE_SUBSTf_def] >> fs[EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `a1 = a2` >>
  `set a1 = set a2` suffices_by (unabbrev_all_tac >> fs[]) >>
  unabbrev_all_tac >> PURE_ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  strip_tac >> PURE_ONCE_REWRITE_TAC[SIMP_RULE std_ss [IN_DEF] MEM_FOLDR_LIST_UNION] >>
  rw[GSYM IMP_DISJ_THM] >> fs[LIST_TO_SET_MAP]);

val type_ok_TYPE_SUBSTf = Q.store_thm("type_ok_TYPE_SUBSTf",
 `!r sig sigma. (∀ty. tyvars (sigma ty) = []) /\
  (∀ty. type_ok sig (sigma ty)) /\
  type_ok sig r ==>
  type_ok sig (TYPE_SUBSTf sigma r)`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- simp[type_ok_def]
  >> fs[EVERY_MEM,type_ok_def,MEM_MAP,PULL_EXISTS]);

val consts_of_term_ok = Q.store_thm("consts_of_term_ok",
  `!tm q r. term_ok sig tm /\ (q,r) ∈ consts_of_term tm ==> type_ok (tysof sig) r`,
  Induct >> rw[term_ok_def,type_ok_def,consts_of_term_def] >> fs[consts_of_term_def]
  >> metis_tac[])

val consts_of_term_term_ok = Q.store_thm("consts_of_term_term_ok",
  `!tm q r sig. term_ok sig tm /\ (q,r) ∈ consts_of_term tm ==> term_ok sig (Const q r)`,
  Induct >> rw[term_ok_def,type_ok_def,consts_of_term_def] >> fs[consts_of_term_def]
  >> metis_tac[term_ok_def]);
                                   
val TYPE_SUBSTf_lemma = Q.prove(
  `!ty sigma sigma'. (!tv. MEM tv (tyvars ty) ==> REV_ASSOCD (Tyvar tv) sigma' (Tyvar tv) = sigma tv) ==>
  TYPE_SUBSTf sigma ty = TYPE_SUBST sigma' ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- fs[tyvars_def]
  >> fs[tyvars_def,MEM_FOLDR_LIST_UNION,PULL_EXISTS]
  >> rw[MAP_EQ_f]
  >> fs[EVERY_MEM] >> rpt(first_x_assum drule) >> rpt strip_tac
  >> metis_tac[]);

val TYPE_SUBSTf_TYPE_SUBST = Q.store_thm("TYPE_SUBSTf_TYPE_SUBST",
  `!ty sigma. ?sigma'. TYPE_SUBSTf sigma ty = TYPE_SUBST sigma' ty`,
  rpt strip_tac
  >> qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tyvars ty)`
  >> match_mp_tac TYPE_SUBSTf_lemma
  >> rw[] >> fs[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP_gen,o_DEF]
  >> CASE_TAC
  >- fs[ALOOKUP_NONE,MEM_MAP,PULL_FORALL,GSYM RIGHT_FORALL_OR_THM]
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_MAP] >> rveq >> fs[]);

val type_ok_TYPE_SUBSTf = Q.store_thm("type_ok_TYPE_SUBSTf",
  `∀s sigma ty.
      type_ok s ty ∧
      (∀ty. type_ok s (sigma ty))
    ⇒ type_ok s (TYPE_SUBSTf sigma ty)`,
  gen_tac >> ho_match_mp_tac TYPE_SUBSTf_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM]);

val FOLDR_LIST_UNION_empty = Q.prove(
  `EVERY (λx. tyvars x = []) tys ==> (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys = [])`,
  Induct_on `tys` >> fs[]);

val allTypes'_no_tyvars = Q.store_thm("allTypes'_no_tyvars",
  `!ty x. MEM x (allTypes' ty) /\ tyvars ty = [] ==> tyvars x = []`,
  ho_match_mp_tac allTypes'_ind >> rw[tyvars_def]
  >> `!x. ~MEM x (FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys)` by fs[]
  >> qpat_x_assum `_ = _` kall_tac
  >> fs[MEM_FOLDR_LIST_UNION,allTypes'_def]
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
  >> fs[]);

val allTypes'_TYPE_SUBSTf_no_tyvars = Q.store_thm("allTypes'_TYPE_SUBSTf_no_tyvars",
  `∀sigma y x. MEM x (allTypes' (TYPE_SUBSTf sigma y)) /\ (!ty. tyvars (sigma ty) = []) ==> tyvars x = []`,
  ho_match_mp_tac TYPE_SUBSTf_ind >> rpt strip_tac
  >- (fs[allTypes'_def] >> match_mp_tac allTypes'_no_tyvars >> metis_tac[])
  >> fs[allTypes'_def]
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
  >> metis_tac[ground_TYPE_SUBSTf]);

val allTypes'_type_ok = Q.store_thm("allTypes'_type_ok",
  `!t x sig. MEM x (allTypes' t) /\ type_ok sig t ==> type_ok sig x`,
  ho_match_mp_tac allTypes'_ind >> rpt strip_tac
  >> fs[type_ok_def,allTypes'_def]
  >> PURE_FULL_CASE_TAC
  >- fs[]
  >> qpat_x_assum `MEM _ _` mp_tac >> simp[]
  >> PURE_FULL_CASE_TAC
  >- (fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,PULL_FORALL,EVERY_MEM] >> metis_tac[])
  >> simp[]
  >> strip_tac
  >> fs[type_ok_def]);
  
val allTypes_type_ok = Q.store_thm("allTypes_type_ok",
  `!tm x sig. MEM x (allTypes tm) /\ term_ok sig tm
   ==> type_ok (tysof sig) x
  `,
  Induct >> rw[allTypes_def]
  >> fs[term_ok_def] >> metis_tac[allTypes'_type_ok]);

val terms_of_frag_uninst_term_ok = Q.store_thm("terms_of_frag_uninst_term_ok",
  `!tm. term_ok sig tm /\ (∀ty. tyvars (sigma ty) = []) /\ (∀ty. type_ok (tysof sig) (sigma ty))
   ==> tm ∈ terms_of_frag_uninst (total_fragment sig) sigma`,
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
  >> imp_res_tac allTypes'_type_ok);

val termsem_simple_subst = Q.store_thm("termsem_simple_subst",
  `∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀δ γ v sigma.
        termsem δ γ v sigma (simple_subst ilist tm) =
        termsem δ γ
                (v =++ MAP ((dest_var ## termsem δ γ v sigma) o (λ(s',s). (s,s')))
                           (REVERSE ilist))
                sigma tm`,
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
  metis_tac[welltyped_def]);

val termsem_VSUBST = Q.store_thm("termsem_VSUBST",
  ` ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀δ γ v sigma.
       termsem δ γ v sigma (VSUBST ilist tm) =
        termsem δ γ
                (v =++ MAP ((dest_var ## termsem δ γ v sigma) o (λ(s',s). (s,s')))
                           (REVERSE ilist))
                sigma tm`,
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
  metis_tac[termsem_simple_subst,termsem_aconv]);

(*
val is_std_interpretation_is_type = Q.store_thm("is_std_interpretation_is_type",
  `is_std_interpretation i ⇒ is_std_type_assignment (FST i)`,
  Cases_on`i` >> simp[is_std_interpretation_def])

(* typesem *)

val typesem_inhabited = Q.store_thm("typesem_inhabited",
  `is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)`,
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def,FLOOKUP_DEF] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then match_mp_tac >>
  simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[])

val typesem_Fun = Q.store_thm("typesem_Fun",
  `∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)`,
  rw[is_std_type_assignment_def,typesem_def])

val typesem_Bool = Q.store_thm("typesem_Bool",
  `∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset`,
  rw[is_std_type_assignment_def,typesem_def])

val typesem_TYPE_SUBST = Q.store_thm("typesem_TYPE_SUBST",
  `∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty`,
  ho_match_mp_tac TYPE_SUBST_ind >> simp[typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >>
  simp[MAP_MAP_o,MAP_EQ_f])

val typesem_tyvars = Q.store_thm("typesem_tyvars",
  `∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty`,
  ho_match_mp_tac typesem_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >> rw[MAP_EQ_f] >>
  metis_tac[])

val typesem_consts = Q.store_thm("typesem_consts",
  `∀δ τ ty δ'.
    (∀name args. (Tyapp name args) subtype ty ⇒
      δ' name = δ name ∨
      ∃vars. args = MAP Tyvar vars ∧
             δ' name (MAP τ vars) = δ name (MAP τ vars))
    ⇒ typesem δ' τ ty = typesem δ τ ty`,
  ho_match_mp_tac typesem_ind >>
  conj_tac >- simp[typesem_def] >>
  rw[] >> simp[typesem_def] >>
  fs[subtype_Tyapp] >>
  first_assum(qspecl_then[`name`,`args`]mp_tac) >>
  impl_tac >- rw[] >> strip_tac >- (
    rw[] >> AP_TERM_TAC >> simp[MAP_EQ_f] >> metis_tac[] ) >>
  simp[MAP_MAP_o,combinTheory.o_DEF,typesem_def,ETA_AX])

(* termsem *)

val termsem_typesem = Q.store_thm("termsem_typesem",
  `is_set_theory ^mem ⇒
    ∀sig i tm v δ τ tmenv.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      ⇒
      termsem tmenv i v tm <: typesem δ τ (typeof tm)`,
  strip_tac >> ntac 2 Cases >> Induct
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_term_valuation_def,term_ok_def] )
  >- (
    Cases_on`v`>>
    simp[termsem_def,term_ok_def] >> rw[] >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: X` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    rw[Abbr`ty`,Abbr`ii`,Abbr`sig`] >>
    simp[Once typesem_TYPE_SUBST,Abbr`X`,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`X <: typesem δ τi ty0` >>
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    first_x_assum (qspecl_then[`name`,`ty0`]mp_tac) >>
    simp[] >> disch_then(qspec_then`λx. if MEM x (tyvars ty0) then τi x else boolset`mp_tac) >>
    simp[Abbr`X`,Abbr`τi`] >>
    impl_tac >- (
      fs[is_type_valuation_def] >>
      reverse(rw[])>-metis_tac[mem_boolset]>>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[is_valuation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`a <: b ⇒ a' <: b'` >>
    `a' = a` by (
      unabbrev_all_tac >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
      simp[MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode]) >>
    `b' = b` by (
      unabbrev_all_tac >>
      match_mp_tac typesem_tyvars >> rw[] ) >>
    rw[] )
  >- (
    simp[termsem_def,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    metis_tac[]) >>
  simp[termsem_def,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  simp[termsem_def] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  first_x_assum (qspec_then`vv`mp_tac) >>
  simp[Abbr`vv`] >> disch_then match_mp_tac >>
  Cases_on`v`>> fs[is_valuation_def,is_term_valuation_def] >>
  rw[combinTheory.APPLY_UPDATE_THM] >> rw[])

val termsem_typesem_matchable = Q.store_thm("termsem_typesem_matchable",
  `is_set_theory ^mem ⇒
     ∀sig i tm v δ τ tmenv ty.
       δ = tyaof i ∧ τ = tyvof v ∧ is_valuation (tysof sig) δ v ∧
       is_interpretation sig i ∧ is_std_type_assignment δ ∧
       term_ok sig tm ∧ tmenv = tmsof sig ∧
       ty = typesem δ τ (typeof tm) ⇒
       termsem tmenv i v tm <: ty`,
  PROVE_TAC[termsem_typesem])

val termsem_consts = Q.store_thm("termsem_consts",
  `∀tmsig i v tm i'.
      welltyped tm ∧
      (∀name ty. VFREE_IN (Const name ty) tm ⇒
                 instance tmsig i' name ty (tyvof v) =
                 instance tmsig i name ty (tyvof v)) ∧
      (∀t. t subterm tm ⇒
         typesem (tyaof i') (tyvof v) (typeof t) =
         typesem (tyaof i ) (tyvof v) (typeof t))
      ⇒
      termsem tmsig i' v tm = termsem tmsig i v tm`,
  Induct_on`tm` >> simp[termsem_def] >> rw[]
  >- (
    fs[subterm_Comb] >>
    metis_tac[]) >>
  simp[termsem_def] >>
  fsrw_tac[boolSimps.DNF_ss][subterm_Abs] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM])

val Equalsem =
  is_std_interpretation_def
  |> SPEC_ALL |> concl |> rhs
  |> strip_conj |> last
  |> strip_comb |> snd |> last

val termsem_Equal = Q.store_thm("termsem_Equal",
  `is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]`,
  rw[termsem_def,LET_THM] >> fs[is_structure_def] >>
  qspecl_then[`tmsof Γ`,`i`,`(strlit "=")`]mp_tac instance_def >> fs[is_std_sig_def]>>
  disch_then(qspec_then`[(ty,Tyvar(strlit "A"))]`mp_tac)>>
  simp[REV_ASSOCD] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`aa = tyvars X` >>
  `aa = [(strlit "A")]` by simp[tyvars_def,Abbr`aa`,LIST_UNION_def,LIST_INSERT_def] >>
  Q.PAT_ABBREV_TAC`tt = typesem (tyaof i) Y o TYPE_SUBST Z o Tyvar` >>
  `is_type_valuation tt` by (
    simp[Abbr`tt`,is_type_valuation_def] >>
    rw[REV_ASSOCD,typesem_def] >- (
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_valuation_def,is_interpretation_def] >>
      metis_tac[] ) >>
    fs[is_valuation_def,is_type_valuation_def] ) >>
  qunabbrev_tac`aa` >>
  fs[is_std_interpretation_def,interprets_def] >>
  `MAP implode (STRING_SORT ["A"]) = [strlit "A"]` by
    simp[STRING_SORT_def,INORDER_INSERT_def,mlstringTheory.implode_def] >>
  simp[] >> simp[Abbr`tt`,REV_ASSOCD])

(* equations *)

val termsem_equation = Q.store_thm("termsem_equation",
  `is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)`,
  rw[] >>
  `is_std_sig sig ∧ is_std_interpretation i` by fs[is_structure_def] >>
  fs[term_ok_equation] >>
  imp_res_tac term_ok_type_ok >>
  simp[equation_def,termsem_def,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[is_structure_def,termsem_typesem] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset,is_structure_def] ) >>
  unabbrev_all_tac >> simp[])

(* aconv *)

val termsem_raconv = Q.store_thm("termsem_raconv",
  `∀env tp. RACONV env tp ⇒
      ∀Γ i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem Γ i v1 (Var x1 ty1) =
             termsem Γ i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp)`,
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
  rw[] >> fs[])

val termsem_aconv = Q.store_thm("termsem_aconv",
  `∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2`,
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_def])

(* semantics only depends on valuation of free variables *)

val termsem_frees = Q.store_thm("termsem_frees",
  `∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t`,
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[] >> rw[termsem_def] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[])

val typesem_frees = Q.store_thm("typesem_frees",
  `∀ty τ1 τ2 δ.
      (∀a. MEM a (tyvars ty) ⇒ τ1 a = τ2 a) ⇒
      typesem δ τ1 ty = typesem δ τ2 ty`,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def,PULL_EXISTS] >>
  rw[] >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
  fs[EVERY_MEM] >> metis_tac[])

val termsem_tyfrees = Q.store_thm("termsem_tyfrees",
  `∀Γ i t v1 v2 tmenv.
      term_ok Γ t ∧
      SND v1 = SND v2 ∧
      (∀a. MEM a (tvars t) ⇒ FST v1 a = FST v2 a) ∧
      tmenv = tmsof Γ
      ⇒ termsem tmenv i v1 t = termsem tmenv i v2 t`,
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def,tvars_def,term_ok_def] >- (
    rw[] >>
    qmatch_abbrev_tac`instance (tmsof Γ) i name ty τ = X` >>
    qspecl_then[`tmsof Γ`,`i`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`ty`,Abbr`X`] >> disch_then kall_tac >>
    rpt AP_TERM_TAC >> simp[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    match_mp_tac typesem_frees >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[tyvars_TYPE_SUBST] >>
    fs[MEM_MAP] >>
    metis_tac[mlstringTheory.implode_explode] ) >>
  rw[] >- (res_tac >> PROVE_TAC[]) >>
  rw[termsem_def] >> fs[tvars_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[]  >>
    match_mp_tac typesem_tyvars >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF,term_ok_welltyped,WELLTYPED] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM])

(* semantics of substitution *)

val termsem_simple_subst = Q.store_thm("termsem_simple_subst",
  `∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀Γ i v.
        termsem Γ i v (simple_subst ilist tm) =
        termsem Γ i
          (FST v, SND v =++
                  MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist))
          tm`,
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
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
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
  qmatch_abbrev_tac `termsem Γ i vv xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  impl_tac >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`Γ`,`i`,`vv`]mp_tac) >>
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
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[welltyped_def])

val termsem_VSUBST = Q.store_thm("termsem_VSUBST",
  ` ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm`,
  rw[] >>
  Q.ISPECL_THEN[`{y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` by (
    match_mp_tac ACONV_VSUBST >> metis_tac[] ) >>
  `welltyped (VSUBST ilist tm)` by metis_tac[VSUBST_WELLTYPED] >>
  `welltyped (VSUBST ilist fm)` by metis_tac[VSUBST_WELLTYPED] >>
  `termsem Γ i v (VSUBST ilist tm) = termsem Γ i v (VSUBST ilist fm)` by
    metis_tac[termsem_aconv] >>
  `VSUBST ilist fm = simple_subst ilist fm` by
    metis_tac[VSUBST_simple_subst] >>
  rw[] >>
  metis_tac[termsem_simple_subst,termsem_aconv])

(* semantics of instantiation *)

val termsem_simple_inst = Q.store_thm("termsem_simple_inst",
  `∀Γ tm tyin tmenv.
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      tmenv = tmsof Γ
      ⇒
      ∀i v.
        termsem tmenv i v (simple_inst tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm`,
  Cases >> Induct >> simp[termsem_def,term_ok_def] >- (
    rw[] >> rw[TYPE_SUBST_compose] >>
    qmatch_abbrev_tac`instance sig int name (TYPE_SUBST i2 ty0) t1 =
                      instance sig int name (TYPE_SUBST i1 ty0) t2` >>
    qspecl_then[`sig`,`int`,`name`]mp_tac instance_def >> simp[Abbr`sig`,Abbr`t2`] >>
    disch_then kall_tac >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    rw[Once REV_ASSOCD_ALOOKUP,Abbr`i2`,ALOOKUP_APPEND,MAP_MAP_o,swap_ff] >>
    rw[ff_def,GSYM MAP_MAP_o,ALOOKUP_MAP] >>
    rw[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >> fs[typesem_def] >>
    rw[Once typesem_TYPE_SUBST,REV_ASSOCD_ALOOKUP] )
  >- (
    rw[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    metis_tac[] ) >>
  rw[] >> rw[] >> rw[termsem_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d2 = d1` by (
    unabbrev_all_tac >>
    simp[Once typesem_TYPE_SUBST] ) >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `r2 = r1` by (
    unabbrev_all_tac >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    simp[Once typesem_TYPE_SUBST] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM] >>
  first_x_assum(qspec_then`tyin`mp_tac) >> simp[] >>
  impl_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac termsem_frees >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[])

val termsem_INST = Q.store_thm("termsem_INST",
  `∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm`,
  rw[] >> imp_res_tac term_ok_welltyped >>
  Q.ISPECL_THEN[`{x | ∃ty. VFREE_IN (Var x ty) tm}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (INST tyin tm) (INST tyin fm)` by (
    match_mp_tac ACONV_INST >> metis_tac[] ) >>
  `welltyped (INST tyin tm)` by metis_tac[INST_WELLTYPED] >>
  `welltyped (INST tyin fm)` by metis_tac[INST_WELLTYPED] >>
  `termsem tmenv i v (INST tyin tm) = termsem tmenv i v (INST tyin fm)` by
    metis_tac[termsem_aconv] >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm} = {x | ∃ty. VFREE_IN (Var x ty) fm}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `INST tyin fm = simple_inst tyin fm` by
    metis_tac[INST_simple_inst] >>
  rw[] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv])

(* extending the context doesn't change the semantics *)

val termsem_extend = Q.store_thm("termsem_extend",
  `∀tyenv tmenv tyenv' tmenv' tm.
      tmenv ⊑ tmenv' ∧
      term_ok (tyenv,tmenv) tm ⇒
      ∀i v. termsem tmenv' i v tm =
            termsem tmenv i v tm`,
  ntac 4 gen_tac >> Induct >> simp[termsem_def,term_ok_def] >>
  rw[] >> simp[termsem_def] >>
  qmatch_abbrev_tac`X = instance sig int name ty t` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  fs[Abbr`sig`,Abbr`ty`,Abbr`X`] >>
  disch_then kall_tac >>
  qmatch_abbrev_tac`instance sig int name ty t = X` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  imp_res_tac FLOOKUP_SUBMAP >>
  fs[Abbr`sig`,Abbr`ty`])

val is_valuation_reduce = Q.store_thm("is_valuation_reduce",
  `∀tyenv tyenv' δ v. tyenv ⊑ tyenv' ∧ is_valuation tyenv' δ v ⇒
    is_valuation tyenv δ v`,
  rw[is_valuation_def,is_term_valuation_def] >>
  metis_tac[type_ok_extend])

val satisfies_extend = Q.store_thm("satisfies_extend",
  `∀tyenv tmenv tyenv' tmenv' tm i h c.
      tmenv ⊑ tmenv' ∧ tyenv ⊑ tyenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      i satisfies ((tyenv,tmenv),h,c) ⇒
      i satisfies ((tyenv',tmenv'),h,c)`,
  rw[satisfies_def] >> fs[EVERY_MEM] >>
  metis_tac[term_ok_extend,termsem_extend,is_valuation_reduce])

(* one interpretation being compatible with another in a signature *)

val equal_on_def = Define`
  equal_on (sig:sig) i i' ⇔
  (∀name. name ∈ FDOM (tysof sig) ⇒ tyaof i' name = tyaof i name) ∧
  (∀name. name ∈ FDOM (tmsof sig) ⇒ tmaof i' name = tmaof i name)`

val equal_on_refl = Q.store_thm("equal_on_refl",
  `∀sig i. equal_on sig i i`,
  rw[equal_on_def])

val equal_on_sym = Q.store_thm("equal_on_sym",
  `∀sig i i'. equal_on sig i i' ⇒ equal_on sig i' i`,
  rw[equal_on_def] >> PROVE_TAC[])

val equal_on_trans = Q.store_thm("equal_on_trans",
  `∀sig i1 i2 i3. equal_on sig i1 i2 ∧ equal_on sig i2 i3
    ⇒ equal_on sig i1 i3`,
  rw[equal_on_def] >> metis_tac[])

val equal_on_interprets = Q.store_thm("equal_on_interprets",
  `∀sig i1 i2 name args ty m.
      equal_on sig i1 i2 ∧
      tmaof i1 interprets name on args as m ∧
      (FLOOKUP (tmsof sig) name = SOME ty) ∧
      type_ok (tysof sig) ty ∧
      (set (tyvars ty) = set args) ⇒
      tmaof i2 interprets name on args as m`,
  rw[equal_on_def,interprets_def] >>
  qsuff_tac`tmaof i2 name = tmaof i1 name` >- metis_tac[] >>
  first_x_assum match_mp_tac >>
  fs[FLOOKUP_DEF])

val equal_on_reduce = Q.store_thm("equal_on_reduce",
  `∀ls ctxt i i'. equal_on (sigof (ls++ctxt)) i i' ∧
                 DISJOINT (FDOM (tysof ls)) (FDOM (tysof ctxt)) ∧
                 DISJOINT (FDOM (tmsof ls)) (FDOM (tmsof ctxt))
    ⇒ equal_on (sigof ctxt) i i'`,
  rw[equal_on_def])

(* semantics only depends on interpretation of things in the term's signature *)

val typesem_sig = Q.store_thm("typesem_sig",
  `∀ty τ δ δ' tyenv. type_ok tyenv ty ∧ (∀name. name ∈ FDOM tyenv ⇒ δ' name = δ name) ⇒
                    typesem δ' τ ty = typesem δ τ ty`,
  ho_match_mp_tac type_ind >> simp[typesem_def,type_ok_def] >> rw[] >>
  qmatch_abbrev_tac`δ' name args1 = δ name args2` >>
  `args1 = args2` by (
    unabbrev_all_tac >>
    simp[MAP_EQ_f] >>
    fs[EVERY_MEM] >>
    metis_tac[] ) >>
  simp[] >> AP_THM_TAC >>
  first_x_assum match_mp_tac >>
  fs[FLOOKUP_DEF])

val termsem_sig = Q.store_thm("termsem_sig",
  `∀tm Γ i v i' tmenv.
      is_std_sig Γ ∧ term_ok Γ tm ∧ tmenv = tmsof Γ ∧ equal_on Γ i i'
      ⇒
      termsem tmenv i' v tm = termsem tmenv i v tm`,
  REWRITE_TAC[equal_on_def] >>
  Induct >> simp[termsem_def] >- (
    rw[term_ok_def] >>
    imp_res_tac instance_def >>
    qmatch_abbrev_tac`instance tmenv i' s ty τ = X` >>
    qmatch_assum_abbrev_tac`Abbrev(ty = TYPE_SUBST tyin ty0)` >>
    first_x_assum(qspecl_then[`tyin`,`ty`]mp_tac) >>
    simp[Abbr`X`,Abbr`ty`] >> disch_then kall_tac >>
    qmatch_abbrev_tac`f1 x1 = f2 x2` >>
    `x1 = x2` by (
      unabbrev_all_tac >>
      simp[FUN_EQ_THM,MAP_EQ_f] >>
      rw[] >>
      match_mp_tac typesem_sig >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[MEM_MAP,mlstringTheory.implode_explode,FLOOKUP_DEF] >>
      metis_tac[] ) >>
    simp[] >> AP_THM_TAC >>
    unabbrev_all_tac >>
    fs[FLOOKUP_DEF]) >>
  fs[term_ok_def] >- (fs[FORALL_PROD] >> rw[] >> res_tac >> PROVE_TAC[]) >>
  rw[term_ok_def] >>
  simp[termsem_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[] >>
    match_mp_tac typesem_sig >>
    metis_tac[term_ok_type_ok] ) >>
  simp[] >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM] >>
  unabbrev_all_tac >> fs[] >>
  fs[FORALL_PROD] >> res_tac >> fs[])

val satisfies_sig = Q.store_thm("satisfies_sig",
  `∀i i' sig h c.
    is_std_sig sig ∧
    EVERY (term_ok sig) (c::h) ∧
    equal_on sig i i' ∧
    i satisfies (sig,h,c)
    ⇒
    i' satisfies (sig,h,c)`,
  rw[satisfies_def] >>
  qsuff_tac`termsem (tmsof sig) i v c = True` >- metis_tac[termsem_sig] >>
  first_x_assum match_mp_tac >>
  reverse conj_tac >- ( fs[EVERY_MEM] >> metis_tac[termsem_sig] ) >>
  fs[is_valuation_def] >>
  fs[is_term_valuation_def] >>
  metis_tac[typesem_sig,equal_on_def])

(* valuations exist *)

val term_valuation_exists = Q.store_thm("term_valuation_exists",
  `is_set_theory ^mem ⇒
    ∀tyenv δ τ. is_type_valuation τ ∧ is_type_assignment tyenv δ ⇒
      ∃σ. is_valuation tyenv δ (τ,σ)`,
  rw[is_valuation_def,is_term_valuation_def] >>
  qexists_tac`λ(x,ty). @v. v <: typesem δ τ ty` >> rw[] >>
  metis_tac[typesem_inhabited])

val is_type_valuation_exists = Q.prove(
  `is_set_theory ^mem ⇒ is_type_valuation (K boolset)`,
  simp[is_type_valuation_def] >> metis_tac[boolean_in_boolset]) |> UNDISCH

val valuation_exists = Q.store_thm("valuation_exists",
  `is_set_theory ^mem ⇒
    ∀tyenv δ. is_type_assignment tyenv δ ⇒
      ∃v. is_valuation tyenv δ v`,
  rw[is_valuation_def] >>
  qexists_tac`K boolset, λ(x,ty). @v. v <: typesem δ (K boolset) ty` >>
  conj_asm1_tac >- simp[is_type_valuation_exists] >>
  fs[is_term_valuation_def] >> metis_tac[typesem_inhabited])

val extend_valuation_exists = Q.store_thm("extend_valuation_exists",
  `is_set_theory ^mem ⇒
    ∀tysig δ v tysig'.
    is_valuation tysig δ v ∧ tysig ⊑ tysig' ∧
    is_type_assignment tysig' δ ⇒
    ∃v'. is_valuation tysig' δ v' ∧
         (tyvof v' = tyvof v) ∧
         (∀x ty. type_ok tysig ty ⇒ (tmvof v (x,ty) = tmvof v' (x,ty)))`,
  rw[] >> simp[EXISTS_PROD] >>
  fs[is_valuation_def,is_term_valuation_def] >>
  qexists_tac`λ(x,ty).
    if type_ok tysig ty then tmvof v (x,ty)
    else @m. m <: typesem δ (tyvof v) ty` >>
  rw[] >> metis_tac[typesem_inhabited])

val is_type_valuation_UPDATE_LIST = Q.store_thm("is_type_valuation_UPDATE_LIST",
  `∀t ls. is_type_valuation t ∧ EVERY (inhabited o SND) ls ⇒
           is_type_valuation (t =++ ls)`,
  rw[is_type_valuation_def,APPLY_UPDATE_LIST_ALOOKUP] >>
  BasicProvers.CASE_TAC >> rw[] >> imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,FORALL_PROD] >> metis_tac[])

(* identity instance *)

val identity_instance = Q.store_thm("identity_instance",
  `∀tmenv (i:'U interpretation) name ty τ. FLOOKUP tmenv name = SOME ty ⇒
      instance tmenv i name ty = λτ. tmaof i name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty)))))`,
  rw[] >>
  qspecl_then[`tmenv`,`i`,`name`,`ty`,`ty`,`[]`]mp_tac instance_def >>
  rw[FUN_EQ_THM,typesem_def,combinTheory.o_DEF,ETA_AX])

(* special cases of interprets *)

val rwt = MATCH_MP (PROVE[]``P x ⇒ ((∀x. P x ⇒ Q) ⇔ Q)``) is_type_valuation_exists
val interprets_nil = save_thm("interprets_nil",
  interprets_def |> SPEC_ALL |> Q.GEN`vs` |> Q.SPEC`[]`
  |> SIMP_RULE (std_ss++listSimps.LIST_ss) [rwt] |> GEN_ALL)

val interprets_one = Q.store_thm("interprets_one",
  `i interprets name on [v] as f ⇔
    (∀x. inhabited x ⇒ (i name [x] = f [x]))`,
  rw[interprets_def,EQ_IMP_THM] >>
  TRY (
    first_x_assum match_mp_tac >>
    fs[is_type_valuation_def] ) >>
  first_x_assum(qspec_then`K x`mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  rw[is_type_valuation_def] >> metis_tac[])

(* for models, reducing the context *)

val is_type_assignment_reduce = Q.store_thm("is_type_assignment_reduce",
  `∀tyenv tyenv' δ.
     tyenv ⊑ tyenv' ∧
     is_type_assignment tyenv' δ ⇒
     is_type_assignment tyenv δ`,
  rw[is_type_assignment_def] >>
  imp_res_tac FEVERY_SUBMAP)

val is_term_assignment_reduce = Q.store_thm("is_term_assignment_reduce",
  `∀tmenv tmenv' δ γ.
     tmenv ⊑ tmenv' ∧
     is_term_assignment tmenv' δ γ ⇒
     is_term_assignment tmenv δ γ`,
   rw[is_term_assignment_def] >>
   imp_res_tac FEVERY_SUBMAP)

val is_interpretation_reduce = Q.store_thm("is_interpretation_reduce",
  `∀i tyenv tmenv tyenv' tmenv'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
     is_interpretation (tyenv',tmenv') i ⇒
     is_interpretation (tyenv,tmenv) i`,
  Cases >> rw[is_interpretation_def] >>
  imp_res_tac is_type_assignment_reduce >>
  imp_res_tac is_term_assignment_reduce)

val is_valuation_extend_sig = Q.store_thm("is_valuation_extend_sig",
  `is_set_theory ^mem ⇒
    ∀tyenv tyenv' tyass v.
    is_valuation tyenv tyass v ∧
    is_type_assignment tyenv' tyass ∧
    tyenv ⊑ tyenv' ⇒
    ∃v'.
      (tyvof v' = tyvof v) ∧
      (∀ty. type_ok tyenv ty ⇒ ∀x. tmvof v' (x,ty) = tmvof v (x,ty)) ∧
      is_valuation tyenv' tyass v'`,
  rw[is_valuation_def] >>
  fs[is_term_valuation_def] >>
  simp[EXISTS_PROD] >>
  qexists_tac`λp. if type_ok tyenv (SND p) then tmvof v p else @m. m <: typesem tyass (tyvof v) (SND p)` >>
  simp[] >> rw[] >>
  SELECT_ELIM_TAC >> simp[] >>
  match_mp_tac (UNDISCH typesem_inhabited) >>
  metis_tac[])

val satisfies_reduce = Q.store_thm("satisfies_reduce",
  `is_set_theory ^mem ⇒
    ∀i tyenv tmenv tyenv' tmenv' h c.
      is_std_sig (tyenv,tmenv) ∧
      tyenv ⊑ tyenv' ∧
      tmenv ⊑ tmenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      is_type_assignment tyenv' (tyaof i) ∧
      i satisfies ((tyenv',tmenv'),h,c) ⇒
      i satisfies ((tyenv,tmenv),h,c)`,
  rw[satisfies_def] >>
  qspecl_then[`tyenv`,`tyenv'`,`tyaof i`,`v`]mp_tac (UNDISCH is_valuation_extend_sig) >>
  simp[] >> strip_tac >>
  first_x_assum(qspec_then`v'`mp_tac) >> simp[] >>
  `∀tm. term_ok (tyenv,tmenv) tm ⇒
     termsem tmenv' i v' tm = termsem tmenv i v tm` by (
    rw[] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac`termsem tmenv' i v tm` >>
    reverse conj_tac >- metis_tac[termsem_extend] >>
    match_mp_tac termsem_frees >>
    imp_res_tac term_ok_welltyped >>
    simp[] >> rw[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac type_ok_types_in >> fs[] >>
    last_x_assum match_mp_tac >>
    imp_res_tac VFREE_IN_types_in >>
    fs[] ) >>
  impl_tac >- ( fs[EVERY_MEM] ) >>
  simp[])

val models_reduce = Q.store_thm("models_reduce",
  `is_set_theory ^mem ⇒
    ∀i tyenv tmenv axs tyenv' tmenv' axs'.
     is_std_sig (tyenv,tmenv) ∧
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧ (axs ⊆ axs') ∧
     i models ((tyenv',tmenv'),axs') ∧
     (∀p. p ∈ axs ⇒ (term_ok (tyenv,tmenv)) p)
     ⇒
     i models ((tyenv,tmenv),axs)`,
  strip_tac >>
  Cases >> rw[models_def] >>
  imp_res_tac is_interpretation_reduce >>
  fs[SUBSET_DEF] >>
  match_mp_tac(MP_CANON satisfies_reduce) >>
  simp[] >> fs[is_interpretation_def] >>
  metis_tac[])
*)

val _ = export_theory()
