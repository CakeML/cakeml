open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory (*holSemanticsExtraTheory*)

val _ = new_theory"holSoundness"

val mem = ``mem:'U->'U-> bool``

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

val binary_inference_rule = Q.store_thm("binary_inference_rule",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀δ γ v sigma. is_frag_interpretation (total_fragment (sigof thy)) δ γ ∧
           valuates_frag δ v sigma ∧
           (∀ty. tyvars (sigma ty) = []) ∧
           (∀ty. type_ok (tysof (sigof thy)) (sigma ty)) ∧
           p1 ∈ ground_terms_uninst (sigof thy) sigma ∧
           p2 ∈ ground_terms_uninst (sigof thy) sigma ∧
           termsem_ext δ γ v sigma p1 = True ∧
           termsem_ext δ γ v sigma p2 = True ⇒
           termsem_ext δ γ v sigma q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, term_union h1 h2) |= q`,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def,EVERY_term_union] >> rw[] >>
  rpt (first_x_assum(qspecl_then[`δ`,`γ`]mp_tac)>>rw[]) >>
  fs[satisfies_t_def,satisfies_def,termsem_ext_def,EVERY_term_union] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- fs[models_def] >>
  conj_tac >- fs[valuates_frag_builtins] >>
  fs[PULL_FORALL,AND_IMP_INTRO] >>
  `∀x y ls. hypset_ok ls ⇒
         (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
    metis_tac[MEM_term_remove,MEM_term_remove_imp] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  `is_frag_interpretation (total_fragment (sigof thy)) δ γ` by fs[models_def] >>
  qpat_x_assum `hypset_ok h1` assume_tac >> drule MEM_term_union >>
  qpat_x_assum `hypset_ok h2` assume_tac >> disch_then drule >>
  simp [DISJ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
  `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h1`
    by(fs[EVERY_MEM] >> rw[]
       >> first_x_assum drule >> strip_tac
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> drule terms_of_frag_uninst_ACONV
       >> simp[GSYM PULL_FORALL]
       >> impl_tac
       >- (rpt(first_x_assum drule) >> fs[ground_terms_uninst_def,welltyped_def]
           >> metis_tac[])
       >> simp[]) >>
  `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h2`
    by(fs[EVERY_MEM] >> rw[]
       >> first_x_assum drule >> strip_tac
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> drule terms_of_frag_uninst_ACONV
       >> simp[GSYM PULL_FORALL]
       >> impl_tac
       >- (rpt(first_x_assum drule) >> fs[ground_terms_uninst_def,welltyped_def]
           >> metis_tac[])
       >> simp[]) >>
  `EVERY (λt. t ∈ ground_terms_uninst (sigof thy) sigma) h1`
    by(fs[EVERY_MEM] >> rw[] >>
       fs[ground_terms_uninst_def] >>
       metis_tac[WELLTYPED_LEMMA]) >>
  `EVERY (λt. t ∈ ground_terms_uninst (sigof thy) sigma) h2`
    by(fs[EVERY_MEM] >> rw[] >>
       fs[ground_terms_uninst_def] >>
       metis_tac[WELLTYPED_LEMMA]) >>
  `p1 ∈ ground_terms_uninst (sigof thy) sigma`
    by(fs[ground_terms_uninst_def] >> asm_exists_tac >> metis_tac[WELLTYPED_LEMMA]) >>
  `p2 ∈ ground_terms_uninst (sigof thy) sigma`
    by(fs[ground_terms_uninst_def] >> asm_exists_tac >> metis_tac[WELLTYPED_LEMMA]) >>
  rpt conj_tac >> TRY(first_x_assum ACCEPT_TAC) >> first_x_assum match_mp_tac >> rw[]
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> metis_tac[])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      rpt(first_x_assum drule) >> rpt strip_tac >>
      `welltyped t` by metis_tac[welltyped_def] >>
      `welltyped y` by metis_tac[terms_of_frag_uninst_welltyped] >>
      metis_tac[termsem_aconv])
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> metis_tac[])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      rpt(first_x_assum drule) >> rpt strip_tac >>
      `welltyped t` by metis_tac[welltyped_def] >>
      `welltyped y` by metis_tac[terms_of_frag_uninst_welltyped] >>
      metis_tac[termsem_aconv]));

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

val ABS_correct = Q.store_thm("ABS_correct",
  `is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs (Var x ty) l === Abs (Var x ty) r`,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- fs[term_ok_equation,term_ok_def] >>
  conj_asm1_tac >- fs[EQUATION_HAS_TYPE_BOOL] >> rw[] >>
  fs[satisfies_t_def,satisfies_def] >> rw[] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  `is_frag_interpretation (total_fragment (sigof thy)) δ γ` by(fs[models_def]) >>
  `Abs (Var x ty) l ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_equation >> simp[welltyped_equation] >> disch_then drule >>
       metis_tac[]) >>
  `Abs (Var x ty) r ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_equation >> simp[welltyped_equation] >> disch_then drule >>
       metis_tac[]) >>
  `l ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_AbsE >> disch_then(qspecl_then [`Var x ty`,`l`,`sigma`] mp_tac) >>
       simp[]) >>
  `r ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_AbsE >> disch_then(qspecl_then [`Var x ty`,`r`,`sigma`] mp_tac) >>
       simp[]) >>
  drule termsem_ext_equation >> simp[termsem_ext_def] >>
  fs[valuates_frag_builtins] >>
  ntac 3 (disch_then drule) >>
  disch_then(qspecl_then [`Abs (Var x ty) l`,`Abs (Var x ty) r`] mp_tac) >>
  impl_tac >- fs[term_ok_equation] >>
  simp[] >> disch_then kall_tac >>
  simp[boolean_eq_true] >>
  simp[termsem_def] >>
  `typeof l = typeof r`
      by(fs[GSYM welltyped_equation] >> qpat_x_assum `welltyped _` mp_tac
         >> simp[equation_def]) >>
  simp[] >>
  drule abstract_eq >> disch_then match_mp_tac >>
  ntac 2 strip_tac >>
  simp[] >>
  conj_tac >-
   (qpat_x_assum `typeof _ = typeof_` (assume_tac o GSYM) >>
    simp[] >> match_mp_tac termsem_in_type_ext2 >>
    simp[] >> asm_exists_tac >> simp[] >> rw[combinTheory.UPDATE_def] >>
    fs[valuates_frag_def]) >>
  conj_tac >-
   (match_mp_tac termsem_in_type_ext2 >>
    simp[] >> asm_exists_tac >> simp[] >> rw[combinTheory.UPDATE_def] >>
    fs[valuates_frag_def]) >>
  rename1 `_ =+ x2` >>
  first_x_assum drule >>
  disch_then(qspecl_then [`sigma`,`((x,ty) =+ x2) v`] mp_tac) >>
  impl_tac >-
    (fs[] >>
     conj_tac >-
       (fs[ground_terms_uninst_def] >> imp_res_tac WELLTYPED_LEMMA >>
        qexists_tac `Bool` >> simp[EQUATION_HAS_TYPE_BOOL]
        >> simp[ground_types_def,tyvars_def,type_ok_def] >> fs[is_std_sig_def]) >>
     conj_tac >-
       (fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >> simp[]) >>
     conj_tac >-
       (drule terms_of_frag_uninst_equation >>
        disch_then(qspecl_then [`sigma`,`l`,`r`] mp_tac) >>
        rw[welltyped_equation]) >>
     fs[EVERY_MEM] >> rw[] >>
     `welltyped t` by(metis_tac[welltyped_def]) >>
     drule termsem_frees >>
     disch_then(qspecl_then [`ext_type_frag_builtins δ`,`ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,`v`,`((x,ty) =+ x2) v`] mp_tac) >>
     impl_tac >- (rw[combinTheory.UPDATE_def] >> metis_tac[]) >>
     simp[]) >>
  drule termsem_ext_equation >> ntac 2 (disch_then drule) >>
  disch_then(qspecl_then [`((x,ty) =+ x2) v`,`l`,`r`] mp_tac) >>
  impl_tac >-
    (rw[valuates_frag_def,combinTheory.UPDATE_def] >> rw[] >> simp[] >> fs[valuates_frag_def]) >>
  simp[termsem_ext_def,boolean_eq_true]);

val ASSUME_correct = Q.store_thm("ASSUME_correct",
  `∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p`,
  rw[entails_def,satisfies_t_def,satisfies_def])
                                
val BETA_correct = Q.store_thm("BETA_correct",
  `is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs (Var x ty) t) (Var x ty) === t`,
  rw[] >> simp[entails_def] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- ( simp[term_ok_equation,term_ok_def] ) >>
  conj_asm1_tac >- ( simp[EQUATION_HAS_TYPE_BOOL] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_ext_equation >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  disch_then drule >> fs[models_def] >> disch_then drule >>
  disch_then(qspecl_then [`v`,`Comb (Abs (Var x ty) t) (Var x ty)`,`t`] mp_tac) >>
  fs[valuates_frag_builtins] >> simp[] >> drule terms_of_frag_uninst_equationE
  >> disch_then drule >> simp[welltyped_equation]
  >> strip_tac >> simp[termsem_ext_def] >> disch_then kall_tac
  >> simp[boolean_eq_true]
  >> simp[termsem_def]
  >> match_mp_tac apply_abstract_matchable
  >> conj_tac
  >- fs[valuates_frag_def]
  >> conj_tac
  >- (fs[APPLY_UPDATE_ID] >> match_mp_tac termsem_in_type_ext2
      >> simp[] >> asm_exists_tac >> fs[valuates_frag_def])
  >> conj_tac >- simp[]
  >> simp[APPLY_UPDATE_ID]);

val DEDUCT_ANTISYM_correct = Q.store_thm("DEDUCT_ANTISYM_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2))
      |= p1 === p2`,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    simp[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM] ) >>
  conj_asm1_tac >- (
    simp[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[WELLTYPED] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_ext_equation >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  disch_then drule >> fs[models_def] >>
  disch_then drule >> fs[valuates_frag_builtins] >> disch_then drule >>
  disch_then(qspecl_then [`p1`,`p2`] mp_tac) >>
  impl_tac >-
    (metis_tac[terms_of_frag_uninst_equationE,welltyped_equation])
  >> simp[termsem_ext_def] >> disch_then kall_tac
  >> simp[boolean_eq_true]
  >> `∀x y ls. hypset_ok ls ⇒
         (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
           metis_tac[MEM_term_remove,MEM_term_remove_imp]
  >> `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h1`
    by(fs[valuates_frag_builtins]
       >> drule terms_of_frag_uninst_equationE >> disch_then drule
       >> simp[welltyped_equation] >> strip_tac
       >> fs[EVERY_MEM]
       >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
       >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
       >> strip_tac
       >> rw[]
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> `welltyped p2` by metis_tac[welltyped_def]
       >> Cases_on `ACONV t p2`
       >> rveq
       >- metis_tac[terms_of_frag_uninst_ACONV]
       >> `~ACONV p2 t` by(metis_tac[ACONV_SYM])
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> imp_res_tac hypset_ok_term_remove
       >> first_x_assum(qspec_then `p2` assume_tac)
       >> drule MEM_term_union
       >> first_x_assum(qspec_then `p1` assume_tac)
       >> disch_then drule
       >> disch_then(qspec_then `t` mp_tac) >> simp[]
       >> strip_tac
       >> metis_tac[terms_of_frag_uninst_ACONV,welltyped_def])
  >> `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h2`
    by(fs[valuates_frag_builtins]
       >> drule terms_of_frag_uninst_equationE >> disch_then drule
       >> simp[welltyped_equation] >> strip_tac
       >> fs[EVERY_MEM]
       >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
       >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
       >> strip_tac
       >> rw[]
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> `welltyped p1` by metis_tac[welltyped_def]
       >> Cases_on `ACONV t p1`
       >> rveq
       >- metis_tac[terms_of_frag_uninst_ACONV]
       >> `~ACONV p1 t` by(metis_tac[ACONV_SYM])
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> imp_res_tac hypset_ok_term_remove
       >> first_x_assum(qspec_then `p2` assume_tac)
       >> drule MEM_term_union
       >> first_x_assum(qspec_then `p1` assume_tac)
       >> disch_then drule
       >> disch_then(qspec_then `t` mp_tac) >> simp[]
       >> strip_tac
       >> metis_tac[terms_of_frag_uninst_ACONV,welltyped_def])
  >> qpat_x_assum `!x y z. hypset_ok _ ==> _` kall_tac
  >> qmatch_goalsub_abbrev_tac `a1 = a2`
  >> Cases_on `a2 = True`
  >- (`a1 = True` suffices_by simp[]
      >> unabbrev_all_tac
      >> ntac 2(first_x_assum drule
                >> impl_tac >- rw[]
                >> strip_tac)
      >> ntac 2 (pop_assum mp_tac)
      >> simp[satisfies_t_def]
      >> ntac 2 (disch_then drule
                 >> impl_tac
                 >- (fs[ground_terms_uninst_def,EVERY_MEM,PULL_EXISTS,PULL_FORALL]
                     >> rw[] >> simp[AC CONJ_ASSOC CONJ_SYM] >> asm_exists_tac
                     >> simp[ground_types_def,tyvars_def,type_ok_def]
                     >> fs[is_std_sig_def]
                     >> rw[]
                     >> rpt(first_x_assum drule >> strip_tac)
                     >> asm_exists_tac >> simp[tyvars_def,type_ok_def])
                 >> strip_tac)
      >> fs[satisfies_def]
      >> first_x_assum match_mp_tac
      >> fs[valuates_frag_builtins]
      >> drule terms_of_frag_uninst_equationE >> disch_then drule
      >> simp[welltyped_equation] >> strip_tac
      >> fs[EVERY_MEM]
      >> `∀x y ls. hypset_ok ls ⇒
             (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
              metis_tac[MEM_term_remove,MEM_term_remove_imp]
      >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
      >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
      >> strip_tac
      >> rw[]
      >> `welltyped t` by metis_tac[term_ok_welltyped]
      >> `welltyped p2` by metis_tac[welltyped_def]
      >> Cases_on `ACONV t p2`
      >> rveq
      >- (drule termsem_aconv
          >> rpt(disch_then drule) >> simp[])
      >> `~ACONV p2 t` by(metis_tac[ACONV_SYM])
      >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
      >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
      >> imp_res_tac hypset_ok_term_remove
      >> first_x_assum(qspec_then `p2` assume_tac)
      >> drule MEM_term_union
      >> first_x_assum(qspec_then `p1` assume_tac)
      >> disch_then drule
      >> disch_then(qspec_then `t` mp_tac) >> simp[]
      >> strip_tac
      >> metis_tac[termsem_aconv,term_ok_welltyped])
  >> `a2 = False`
    by(`a2 ⋲ boolset` suffices_by metis_tac[mem_boolset,true_neq_false]
       >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule)
       >> disch_then(qspecl_then [`v`,`sigma`,`p2`] mp_tac)
       >> `typeof p2 = Bool` by metis_tac[WELLTYPED_LEMMA]
       >> simp[]
       >> impl_tac
       >- (conj_tac >- metis_tac[terms_of_frag_uninst_equationE,welltyped_equation]
           >> fs[valuates_frag_def])
       >> rw[ext_type_frag_builtins_def])
  >> `a1 <> True ==> a1 = False`
    by(`a1 ⋲ boolset` suffices_by metis_tac[mem_boolset,true_neq_false]
       >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule)
       >> disch_then(qspecl_then [`v`,`sigma`,`p1`] mp_tac)
       >> `typeof p1 = Bool` by metis_tac[WELLTYPED_LEMMA]
       >> simp[]
       >> impl_tac
       >- (conj_tac >- metis_tac[terms_of_frag_uninst_equationE,welltyped_equation]
           >> fs[valuates_frag_def])
       >> rw[ext_type_frag_builtins_def])
  >> simp[]
  >> first_x_assum match_mp_tac
  >> unabbrev_all_tac
  >> ntac 2(first_x_assum drule
            >> impl_tac >- rw[]
            >> strip_tac)
  >> ntac 2 (pop_assum mp_tac)
  >> simp[satisfies_t_def]
  >> ntac 2 (disch_then drule
             >> impl_tac
             >- (fs[ground_terms_uninst_def,EVERY_MEM,PULL_EXISTS,PULL_FORALL]
                 >> rw[] >> simp[AC CONJ_ASSOC CONJ_SYM] >> asm_exists_tac
                 >> simp[ground_types_def,tyvars_def,type_ok_def]
                 >> fs[is_std_sig_def]
                 >> rw[]
                 >> rpt(first_x_assum drule >> strip_tac)
                 >> asm_exists_tac >> simp[tyvars_def,type_ok_def])
             >> strip_tac)
  >> fs[satisfies_def]
  >> qpat_x_assum `_ = False` mp_tac
  >> ntac 2 (first_x_assum(qspec_then `v` mp_tac))
  >> fs[valuates_frag_builtins]
  >> drule terms_of_frag_uninst_equationE
  >> disch_then drule
  >> simp[welltyped_equation]
  >> strip_tac
  >> rpt strip_tac >> fs[]
  >> rfs[]
  >> fs[EXISTS_MEM]
  >> fs[EVERY_MEM]
  >> `∀x y ls. hypset_ok ls ⇒
             (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
              metis_tac[MEM_term_remove,MEM_term_remove_imp]
  >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
  >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
  >> strip_tac
  >> rw[]
  >> `welltyped e` by metis_tac[term_ok_welltyped]
  >> `welltyped p1` by metis_tac[welltyped_def]
  >> Cases_on `ACONV e p1`
  >> rveq
  >- metis_tac[termsem_aconv]
  >> `~ACONV p1 e` by(metis_tac[ACONV_SYM])
  >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
  >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
  >> imp_res_tac hypset_ok_term_remove
  >> first_x_assum(qspec_then `p2` assume_tac)
  >> drule MEM_term_union
  >> first_x_assum(qspec_then `p1` assume_tac)
  >> disch_then drule
  >> disch_then(qspec_then `e` mp_tac) >> simp[]
  >> strip_tac
  >> metis_tac[termsem_aconv,term_ok_welltyped]);

val EQ_MP_correct = Q.store_thm("EQ_MP_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,term_union h1 h2) |= q`,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>    
  map_every qexists_tac[`p === q`,`p'`] >>
  fs[entails_def] >> fs[EQUATION_HAS_TYPE_BOOL] >>
  fs[theory_ok_def] >>
  drule(GEN_ALL term_ok_equation) >> rpt(disch_then drule) >>
  disch_then(qspecl_then [`q`,`p`] assume_tac) >> fs[] >>
  conj_asm1_tac >- metis_tac[ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >> rw[] >>  
  `term_ok (sigof thy) (p === q)` by metis_tac[term_ok_equation] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`p`,`q`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >> fs[]) >>
  rfs[boolean_eq_true] >>
  metis_tac[termsem_aconv,term_ok_welltyped,termsem_ext_def]);

val INST_correct = Q.store_thm("INST_correct",
  `is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, term_image (VSUBST ilist) h) |= VSUBST ilist c`,
  rw[entails_def,EVERY_MEM,satisfies_t_def] >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_VSUBST >> metis_tac[] ) >>
  TRY ( match_mp_tac VSUBST_HAS_TYPE >> metis_tac[] ) >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  rw[satisfies_def,satisfies_t_def] >>  
  qspecl_then[`c`,`ilist`]mp_tac termsem_VSUBST >>
  impl_tac >- metis_tac[welltyped_def] >>  
  disch_then(qspecl_then[`ext_type_frag_builtins δ`,
                         `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                         `v`,`sigma`]SUBST1_TAC) >>
  first_x_assum drule >> simp[satisfies_def,satisfies_t_def] >>
  disch_then(match_mp_tac o MP_CANON) >>
  simp[] >>
  rpt conj_tac
  >- (rw[ground_terms_uninst_def] >> qexists_tac `Bool`
      >> conj_tac >- metis_tac[]
      >> fs[ground_types_def,tyvars_def,theory_ok_def,is_std_sig_def,type_ok_def])
  >- (rw[ground_terms_uninst_def] >> asm_exists_tac
      >> fs[ground_types_def,tyvars_def,theory_ok_def,is_std_sig_def,type_ok_def])
  >- (fs[valuates_frag_builtins] >> fs[valuates_frag_def] >> rw[]
      >> fs[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE]
      >> BasicProvers.CASE_TAC >- metis_tac[]
      >> imp_res_tac ALOOKUP_MEM
      >> fs[MEM_MAP,UNCURRY,EXISTS_PROD]
      >> res_tac >> imp_res_tac WELLTYPED_LEMMA >> fs[]
      >> rpt BasicProvers.VAR_EQ_TAC
      >> match_mp_tac termsem_in_type_ext2
      >> simp[]
      >> qspec_then `sigof thy` assume_tac total_fragment_is_fragment
      >> asm_exists_tac
      >> fs[]
      >> conj_tac >- fs[models_def]
      >> match_mp_tac terms_of_frag_uninst_term_ok
      >> fs[])
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> fs[])
  >- (rw[EVERY_MEM] >> match_mp_tac terms_of_frag_uninst_term_ok >> fs[]) >>
  rw[EVERY_MEM] >>
  qspecl_then[`h`,`VSUBST ilist`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  drule MEM_term_image_imp >> strip_tac >> rveq >>
  `term_ok (sigof thy) x` by metis_tac[] >>
  `term_ok (sigof thy) t` by metis_tac[] >>
  `welltyped x` by metis_tac[term_ok_welltyped] >>
  `welltyped t` by metis_tac[term_ok_welltyped] >>
  drule termsem_VSUBST >>
  disch_then(qspecl_then [`ilist`,
                          `ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `v`,`sigma`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  disch_then (SUBST1_TAC o GSYM) >>
  drule termsem_aconv >> simp[GSYM PULL_FORALL] >>
  impl_tac >- metis_tac[welltyped_def,VSUBST_WELLTYPED] >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `v`] SUBST1_TAC) >>
  fs[EVERY_MEM]);

val INST_TYPE_correct = Q.store_thm("INST_TYPE_correct",
  `is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, term_image (INST tyin) h) |= INST tyin c`,
  rw[entails_def,EVERY_MAP,EVERY_MEM] >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_INST >> fs[EVERY_MAP,EVERY_MEM] >> metis_tac[] ) >>
  TRY ( match_mp_tac INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_INST >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `sigma`,`tyin`,`v`] mp_tac) >>
  simp[] >> disch_then kall_tac >>
  first_x_assum drule >> simp[satisfies_t_def,satisfies_def] >>
  simp[PULL_FORALL,AND_IMP_INTRO] >> disch_then match_mp_tac >>
  simp[GSYM PULL_FORALL] >>
  rpt conj_tac
  >- rw[ground_TYPE_SUBSTf]
  >- (rw[] >> match_mp_tac type_ok_TYPE_SUBSTf >>
      rw[] >> `type_ok (tysof (sigof thy)) (Tyvar ty')`by simp[type_ok_def] >>
      drule type_ok_TYPE_SUBST >>
      simp[EVERY_MEM,MEM_MAP,PULL_EXISTS])
  >- (rw[EVERY_MEM] >> fs[ground_terms_uninst_def] >>
      qexists_tac `Bool` >> conj_tac >- metis_tac[] >>
      rw[ground_types_def,tyvars_def] >>
      fs[theory_ok_def,is_std_sig_def,type_ok_def])
  >- (rw[EVERY_MEM] >> fs[ground_terms_uninst_def] >>
      qexists_tac `Bool` >> conj_tac >- metis_tac[] >>
      rw[ground_types_def,tyvars_def] >>
      fs[theory_ok_def,is_std_sig_def,type_ok_def])
  >- (fs[valuates_frag_builtins] >> fs[valuates_frag_def]
      >> rw[] >> simp[GSYM TYPE_SUBSTf_TYPE_SUBST_compose])
  >- (match_mp_tac terms_of_frag_uninst_term_ok
      >> simp[]
      >> conj_tac
      >- (rw[] >> metis_tac[ground_TYPE_SUBSTf])
      >> rw[]
      >> match_mp_tac type_ok_TYPE_SUBSTf
      >> simp[]
      >> `type_ok (tysof (sigof thy)) (Tyvar ty)`by simp[type_ok_def]
      >> drule type_ok_TYPE_SUBST
      >> simp[EVERY_MEM,MEM_MAP,PULL_EXISTS])
  >- (rw[EVERY_MEM] >> match_mp_tac terms_of_frag_uninst_term_ok
      >> simp[]
      >> conj_tac >- (rw[] >> metis_tac[ground_TYPE_SUBSTf])
      >> rw[]
      >> match_mp_tac type_ok_TYPE_SUBSTf
      >> simp[]
      >> `type_ok (tysof (sigof thy)) (Tyvar ty)`by simp[type_ok_def]
      >> drule type_ok_TYPE_SUBST
      >> simp[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
  rw[EVERY_MEM] >>
  qspecl_then[`h`,`INST tyin`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  fs[EVERY_MEM] >>
  drule MEM_term_image_imp >> strip_tac >> rveq >>
  `term_ok (sigof thy) x` by metis_tac[] >>
  `term_ok (sigof thy) t` by metis_tac[] >>
  drule termsem_INST >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `sigma`,`tyin`,`v`] (mp_tac o GSYM)) >>
  simp[] >> disch_then kall_tac >>
  drule termsem_aconv >> simp[GSYM PULL_FORALL] >>
  impl_tac >- metis_tac[welltyped_def,INST_WELLTYPED] >>
  metis_tac[]);

val MK_COMB_correct = Q.store_thm("MK_COMB_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,term_union h1 h2) |= Comb l1 l2 === Comb r1 r2`,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l1 === r1`,`l2 === r2`] >>
  fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    fs[EQUATION_HAS_TYPE_BOOL,term_ok_equation] >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    fs[term_ok_equation,term_ok_def,EQUATION_HAS_TYPE_BOOL] ) >>
  rw[] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`l1`,`r1`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >>
      match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[term_ok_equation]) >>
  strip_tac >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`l2`,`r2`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >>
      match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[term_ok_equation]) >>
  strip_tac >> fs[] >>
  drule termsem_ext_equation >> rpt(disch_then drule) >>
  disch_then(qspecl_then [`Comb l1 l2`,`Comb r1 r2`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               fs[term_ok_equation] >> fs[term_ok_def] >> metis_tac[term_ok_welltyped]) >>
  simp[] >> rpt strip_tac >>
  rfs[boolean_eq_true] >>
  fs[termsem_def,termsem_ext_def]);

val REFL_correct = Q.store_thm("REFL_correct",
  `is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t`,
  rw[] >>
  simp[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- rw[term_ok_equation] >>
  rw[satisfies_def,satisfies_t_def] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> fs[models_def,valuates_frag_builtins] >>
  ntac 3(disch_then drule) >>
  disch_then(qspecl_then [`t`,`t`] mp_tac) >>
  impl_tac
  >- (fs[] >> drule terms_of_frag_uninst_equationE >> disch_then drule >>
      fs[] >> disch_then match_mp_tac >>
      simp[welltyped_equation,EQUATION_HAS_TYPE_BOOL]) >>
  rw[termsem_ext_def] >> simp[boolean_eq_true]);

val proves_sound = Q.store_thm("proves_sound",
  `is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c`,
  strip_tac >> match_mp_tac proves_ind >>
  conj_tac >- metis_tac[ABS_correct] >>
  conj_tac >- metis_tac[ASSUME_correct] >>
  conj_tac >- metis_tac[BETA_correct] >>
  conj_tac >- metis_tac[DEDUCT_ANTISYM_correct] >>
  conj_tac >- metis_tac[EQ_MP_correct] >>
  conj_tac >- metis_tac[INST_correct] >>
  conj_tac >- metis_tac[INST_TYPE_correct] >>
  conj_tac >- metis_tac[MK_COMB_correct] >>
  conj_tac >- metis_tac[REFL_correct] >>
  rw[entails_def,theory_ok_def,models_def])

val _ = export_theory()
