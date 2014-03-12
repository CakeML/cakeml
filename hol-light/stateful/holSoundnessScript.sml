open HolKernel boolLib bossLib lcsymtacs listTheory finite_mapTheory alistTheory pred_setTheory pairTheory
open miscLib miscTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holSoundness"

val mem = ``mem:'U->'U-> bool``

val binary_inference_rule = store_thm("binary_inference_rule",
  ``is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀i v. is_structure (sigof thy) i v ∧
           termsem (sigof thy) i v p1 = True ∧
           termsem (sigof thy) i v p2 = True ⇒
           termsem (sigof thy) i v q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, TERM_UNION h1 h2) |= q``,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def,EVERY_TERM_UNION] >> rw[] >>
  rpt (first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def,EVERY_TERM_UNION] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- ( rw[is_structure_def] >> Cases_on`thy` >> fs[models_def,theory_ok_def] ) >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[EVERY_MEM] >>
  metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,termsem_aconv,welltyped_def])

val ABS_correct = store_thm("ABS_correct",
  ``is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs x ty l === Abs x ty r``,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- fs[term_ok_equation,term_ok_def] >>
  conj_asm1_tac >- fs[EQUATION_HAS_TYPE_BOOL] >> rw[] >>
  fs[satisfies_def] >> rw[] >>
  `is_structure (sigof thy) i v` by (
    fs[models_def,is_structure_def] ) >>
  imp_res_tac termsem_equation >>
  rw[boolean_eq_true,termsem_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  qx_gen_tac`m` >> strip_tac >> simp[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  `is_valuation (tysof thy) (FST i) vv` by (
    Cases_on`v`>>
    fs[is_valuation_def,Abbr`vv`,is_term_valuation_def] >>
    rw[combinTheory.APPLY_UPDATE_THM] >> rw[]) >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    fs[is_structure_def] >>
    metis_tac[termsem_typesem,is_std_interpretation_is_type
             ,pairTheory.FST,term_ok_equation]) >>
  first_x_assum(qspec_then`i`mp_tac) >> simp[] >>
  disch_then(qspec_then`vv`mp_tac) >> simp[] >>
  `is_structure (sigof thy) i vv` by (
    fs[is_structure_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  simp[boolean_eq_true] >> disch_then match_mp_tac >>
  fs[EVERY_MEM] >> rw[] >>
  qsuff_tac`termsem (sigof thy) i vv t = termsem (sigof thy) i v t`>-metis_tac[] >>
  match_mp_tac termsem_frees >>
  simp[Abbr`vv`,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[])

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p``,
  rw[entails_def,satisfies_def])

val BETA_correct = store_thm("BETA_correct",
  ``is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs x ty t) (Var x ty) === t``,
  rw[] >> simp[entails_def] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- ( simp[term_ok_equation,term_ok_def] ) >>
  conj_asm1_tac >- ( simp[EQUATION_HAS_TYPE_BOOL] ) >>
  rw[satisfies_def] >>
  `is_structure (sigof thy) i v` by (
    rw[is_structure_def] >> fs[models_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  rw[boolean_eq_true,termsem_def] >>
  qmatch_abbrev_tac`(Abstract mty mtyb f ' e) = termsem Γ i v τ` >>
  `Abstract mty mtyb f ' e = f e` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`f`,Abbr`e`] >>
    conj_tac >- (
      Cases_on`v`>>
      fs[is_valuation_def,is_term_valuation_def,Abbr`mty`]) >>
    simp[Abbr`mtyb`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[is_structure_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    Cases_on`v`>>
    fs[is_valuation_def,is_term_valuation_def] >>
    rw[combinTheory.APPLY_UPDATE_THM]) >>
  simp[Abbr`f`,Abbr`e`] >>
  rw[combinTheory.APPLY_UPDATE_ID])

val DEDUCT_ANTISYM_correct = store_thm("DEDUCT_ANTISYM_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       TERM_UNION (FILTER ($~ o ACONV p2) h1)
                  (FILTER ($~ o ACONV p1) h2))
      |= p1 === p2``,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    simp[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    match_mp_tac EVERY_TERM_UNION >>
    fs[EVERY_MEM,MEM_FILTER] ) >>
  conj_asm1_tac >- (
    simp[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[WELLTYPED] >>
    match_mp_tac EVERY_TERM_UNION >>
    fs[EVERY_MEM,MEM_FILTER] ) >>
  rw[satisfies_def] >>
  `is_structure (sigof thy) i v` by (
    fs[models_def,is_structure_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  simp[boolean_eq_true] >>
  rpt(first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def] >>
  rpt(first_x_assum(qspec_then`v`mp_tac)>>rw[]) >>
  fs[EVERY_MEM] >>
  ntac 2 (pop_assum mp_tac) >>
  `∀x y ls. MEM x (FILTER ($~ o ACONV y) ls) ⇔ ¬ACONV y x ∧ MEM x ls` by simp[MEM_FILTER] >>
  qmatch_abbrev_tac`(a ⇒ b) ⇒ (c ⇒ d) ⇒ e` >>
  `d ⇒ a` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[TERM_UNION_THM,termsem_aconv,welltyped_def] ) >>
  `b ⇒ c` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[TERM_UNION_THM,termsem_aconv,welltyped_def] ) >>
  `termsem (sigof thy) i v p1 <: boolset ∧
   termsem (sigof thy) i v p2 <: boolset` by (
    fs[is_structure_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac termsem_typesem >>
    imp_res_tac WELLTYPED_LEMMA >>
    metis_tac[typesem_Bool]) >>
  metis_tac[mem_boolset])

val EQ_MP_correct = store_thm("EQ_MP_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,TERM_UNION h1 h2) |= q``,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`p === q`,`p'`] >>
  fs[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  fs[term_ok_equation] >>
  conj_asm1_tac >- metis_tac[ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >> rw[] >>
  `term_ok (sigof thy) (p === q)` by metis_tac[term_ok_equation] >>
  imp_res_tac (UNDISCH termsem_equation) >> rfs[boolean_eq_true] >>
  metis_tac[termsem_aconv])

val INST_correct = store_thm("INST_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, MAP (VSUBST ilist) h) |= VSUBST ilist c``,
  rw[entails_def,EVERY_MAP,EVERY_MEM,satisfies_def] >>
  TRY ( match_mp_tac term_ok_VSUBST >> metis_tac[] ) >>
  TRY ( match_mp_tac VSUBST_HAS_TYPE >> metis_tac[] ) >>
  qspecl_then[`c`,`ilist`]mp_tac termsem_VSUBST >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  disch_then(qspecl_then[`sigof thy`,`i`,`v`]SUBST1_TAC) >>
  first_x_assum(qspec_then`i`mp_tac) >> rw[] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  conj_tac >- (
    fs[is_valuation_def] >>
    fs[is_term_valuation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,UNCURRY,EXISTS_PROD] >>
    res_tac >> imp_res_tac WELLTYPED_LEMMA >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    rw[is_valuation_def,is_term_valuation_def] >>
    fs[models_def] >> metis_tac[is_std_interpretation_is_type] ) >>
  fs[EVERY_MAP,EVERY_MEM] >>
  metis_tac[termsem_VSUBST,welltyped_def])

val INST_TYPE_correct = store_thm("INST_TYPE_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, MAP (INST tyin) h) |= INST tyin c``,
  rw[entails_def,EVERY_MAP,EVERY_MEM,satisfies_def] >>
  TRY ( match_mp_tac term_ok_INST >> fs[EVERY_MAP,EVERY_MEM] >> metis_tac[] ) >>
  TRY ( match_mp_tac INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool] ) >>
  qspecl_then[`sigof thy`,`c`,`tyin`]mp_tac termsem_INST >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  disch_then(qspecl_then[`i`,`v`]SUBST1_TAC) >>
  first_x_assum(qspec_then`i`mp_tac)>>rw[]>>
  first_x_assum(match_mp_tac o MP_CANON) >>
  conj_tac >- (
    fs[is_valuation_def] >>
    conj_tac >- (
      fs[is_type_valuation_def] >> rw[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      Cases_on`i`>>fs[models_def,is_interpretation_def] >>
      qexists_tac`tysof thy` >> simp[is_type_valuation_def] >>
      fs[FORALL_PROD] >>
      metis_tac[holSyntaxLibTheory.REV_ASSOCD_MEM,type_ok_def] ) >>
    fs[is_term_valuation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    simp[Once (typesem_TYPE_SUBST |> SIMP_RULE(srw_ss())[] |> GSYM)] >>
    metis_tac[type_ok_TYPE_SUBST |> SIMP_RULE(srw_ss())[EVERY_MAP,EVERY_MEM]]) >>
  fs[EVERY_MAP,EVERY_MEM] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_INST,welltyped_def])

val MK_COMB_correct = store_thm("MK_COMB_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,TERM_UNION h1 h2) |= Comb l1 l2 === Comb r1 r2``,
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
  imp_res_tac (UNDISCH termsem_equation) >>
  rfs[boolean_eq_true] >>
  rw[termsem_def])

val REFL_correct = store_thm("REFL_correct",
  ``is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t``,
  rw[] >>
  simp[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- rw[term_ok_equation] >>
  rw[satisfies_def] >>
  `is_structure (sigof thy) i v` by (
    rw[is_structure_def] >> fs[models_def] ) >>
  imp_res_tac termsem_equation >>
  rw[boolean_def])

val TRANS_correct = store_thm("TRANS_correct",
  ``is_set_theory ^mem ⇒
    ∀thy h1 h2 l m1 m2 r.
      (thy,h1) |= l === m1 ∧ (thy,h2) |= m2 === r ∧ ACONV m1 m2
      ⇒ (thy,TERM_UNION h1 h2) |= l === r``,
  strip_tac >>
  rw[] >> match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l === m1`,`m2 === r`] >>
  fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    fs[EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[ACONV_TYPE] ) >>
  conj_asm1_tac >- (
    fs[term_ok_equation,EQUATION_HAS_TYPE_BOOL] ) >>
  rw[] >>
  imp_res_tac termsem_equation >>
  rfs[boolean_eq_true] >> fs[term_ok_equation] >>
  metis_tac[termsem_aconv,ACONV_SYM,term_ok_welltyped])

val proves_sound = store_thm("proves_sound",
  ``is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c``,
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
  conj_tac >- metis_tac[TRANS_correct] >>
  rw[entails_def,theory_ok_def,models_def])

val proves_consistent = store_thm("proves_consistent",
  ``is_set_theory ^mem ⇒
    ∀ctxt. theory_ok (thyof ctxt) ∧ (∃i. i models (thyof ctxt)) ⇒
      (thyof ctxt,[]) |- (Var "x" Bool === Var "x" Bool) ∧
      ¬((thyof ctxt,[]) |- (Var "x" Bool === Var "y" Bool))``,
  rw[] >- (
    match_mp_tac (List.nth(CONJUNCTS proves_rules,8)) >>
    simp[term_ok_def,type_ok_def] >>
    imp_res_tac theory_ok_sig >>
    fs[is_std_sig_def] ) >>
  spose_not_then strip_assume_tac >>
  imp_res_tac proves_sound >>
  fs[entails_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  simp[satisfies_def] >>
  qexists_tac`(K boolset),
              λ(x,ty). if (x,ty) = ("x",Bool) then True else
                       if (x,ty) = ("y",Bool) then False else
                       @v. v <: typesem (tyaof i) (K boolset) ty` >>
  conj_asm1_tac >- (
    simp[is_valuation_def] >>
    conj_asm1_tac >- (simp[is_type_valuation_def,mem_boolset] >> PROVE_TAC[]) >>
    fs[models_def,is_term_valuation_def,is_interpretation_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >>
    rw[mem_boolset] >>
    metis_tac[typesem_inhabited] ) >>
  qmatch_abbrev_tac`termsem sig i v (s === t) ≠ True` >>
  qspecl_then[`sig`,`i`,`v`,`s`,`t`]mp_tac(UNDISCH termsem_equation) >>
  discharge_hyps >- (
    simp[term_ok_equation,is_structure_def] >>
    fs[models_def,Abbr`sig`,theory_ok_def] ) >>
  simp[Abbr`s`,Abbr`t`,termsem_def,boolean_eq_true,Abbr`v`,true_neq_false])

val init_ctxt_has_model = store_thm("init_ctxt_has_model",
  ``is_set_theory ^mem ⇒ ∃i. i models (thyof init_ctxt)``,
  rw[models_def,init_ctxt_def,conexts_of_upd_def] >>
  rw[is_std_interpretation_def,is_std_type_assignment_def,EXISTS_PROD] >>
  qho_match_abbrev_tac`∃f g. P f g ∧ (f x1 = y1 ∧ f x2 = y2) ∧ (g x3 = y3)` >>
  qexists_tac`λx. if x = x1 then y1 else if x = x2 then y2 else ARB` >>
  qexists_tac`K y3` >>
  rw[Abbr`x1`,Abbr`x2`,Abbr`P`] >>
  rw[is_interpretation_def,is_type_assignment_def,is_term_assignment_def] >>
  rw[FEVERY_FUPDATE,Abbr`y2`,Abbr`y1`,Abbr`y3`,FEVERY_FEMPTY] >>
  rw[typesem_def,tyvars_def] >>
  TRY (
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] ) >>
  BasicProvers.CASE_TAC >> fs[] >- metis_tac[boolean_in_boolset] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac (UNDISCH funspace_inhabited) >>
  metis_tac[])

val new_constant_correct = store_thm("new_constant_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt name ty.
     theory_ok (thyof ctxt) ∧
     name ∉ (FDOM (tmsof ctxt)) ∧
     type_ok (tysof ctxt) ty ⇒
      ∀i. i models (thyof ctxt) ⇒
        ∃i'. i' models (thyof (NewConst name ty::ctxt))``,
  rw[models_def] >>
  qexists_tac`(tyaof i, (name =+ λτ. @v. v <: typesem (tyaof i) τ ty) (tmaof i))` >>
  simp[conexts_of_upd_def] >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
    simp[combinTheory.APPLY_UPDATE_THM] >> rw[] >>
    qmatch_abbrev_tac`(@v. v <: (typesem δ τ' ty)) <: x` >>
    `typesem δ τ' ty = typesem δ τ ty` by (
      match_mp_tac typesem_tyvars >> simp[Abbr`τ'`] ) >>
    metis_tac[typesem_inhabited] ) >>
  conj_tac >- (
    imp_res_tac theory_ok_sig >>
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >> rw[] >>
    fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac satisfies_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  rw[] >- fs[theory_ok_def] >>
  match_mp_tac satisfies_consts >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  rw[term_ok_def,combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[])

val new_specification_correct = store_thm("new_specification_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt eqs prop.
     theory_ok (thyof ctxt) ∧
     (thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
     EVERY
       (λt. CLOSED t ∧
            (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
       (MAP SND eqs) ∧
     (∀x ty. VFREE_IN (Var x ty) prop ⇒
               MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
     (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
     ALL_DISTINCT (MAP FST eqs) ⇒
    ∀i. i models (thyof ctxt) ⇒
      ∃i'. i' models (thyof (ConstSpec eqs prop::ctxt))``,
  rw[models_def] >>
  qexists_tac`(tyaof i, (tmaof i) =++ MAP (λ(s,t). (s, λτ. termsem (sigof ctxt) i (τ,ARB) t)) (REVERSE eqs))` >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_FUNION] >>
    simp[ALOOKUP_MAP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> fs[] >> rw[] >>
    qmatch_abbrev_tac`termsem sig i t1 t <: x` >>
    imp_res_tac theory_ok_sig >>
    `termsem sig i t1 t = termsem sig i (τ,SND t1) t` by (
      match_mp_tac termsem_tyfrees >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac proves_term_ok >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] >>
      rfs[term_ok_equation] >>
      conj_tac >- metis_tac[] >>
      rw[Abbr`t1`] >> metis_tac[] ) >>
    `is_valuation (tysof sig) (tyaof i) (τ,λ(x,ty). @v. v <: typesem (tyaof i) τ ty)` by (
      fs[is_valuation_def,is_term_valuation_def] >> rw[] >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[Abbr`sig`] >> metis_tac[] ) >>
    qmatch_assum_abbrev_tac`is_valuation tyenv δ v` >>
    `termsem sig i (τ,tmvof t1) t = termsem sig i v t` by (
      match_mp_tac termsem_frees >>
      simp[Abbr`v`] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,CLOSED_def] >>
      metis_tac[] ) >>
    rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    unabbrev_all_tac >> simp[] >>
    fs[is_interpretation_def] >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    imp_res_tac is_std_interpretation_is_type >> simp[] >>
    imp_res_tac proves_term_ok >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] >>
    rfs[term_ok_equation] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[] ) >>
  conj_tac >- (
    fs[is_std_interpretation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac theory_ok_sig  >>
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  simp[conexts_of_upd_def] >>
  gen_tac >> reverse strip_tac >- (
    match_mp_tac satisfies_extend >>
    imp_res_tac proves_sound >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    discharge_hyps >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      match_mp_tac SUBMAP_FUNION >>
      fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,ETA_AX,UNCURRY] >>
      metis_tac[] ) >>
    match_mp_tac satisfies_consts >>
    qexists_tac`i` >> simp[] >>
    simp[term_ok_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac proves_sound >> pop_assum mp_tac >>
  rw[entails_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  discharge_hyps >- fs[models_def] >>
  rw[satisfies_def] >>
  qmatch_abbrev_tac`termsem sig ii v (VSUBST ilist tm) = True` >>
  qspecl_then[`tm`,`ilist`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    simp[welltyped_def,Abbr`ilist`,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    metis_tac[has_type_rules] ) >>
  simp[] >> disch_then kall_tac >>
  qmatch_abbrev_tac`termsem sig ii vv tm = True` >>
  `tmsof ctxt ⊑ tmsof sig` by (
    simp[Abbr`sig`] >>
    match_mp_tac SUBMAP_FUNION >>
    fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    metis_tac[] ) >>
  `termsem sig ii vv tm = termsem (sigof ctxt) ii vv tm` by (
    fs[Abbr`sig`] >> metis_tac[termsem_extend] ) >>
  `termsem (sigof ctxt) ii vv tm = termsem (sigof ctxt) i vv tm` by (
    match_mp_tac termsem_consts >>
    simp[Abbr`ii`] >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_def] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  rw[] >>
  first_x_assum match_mp_tac >>
  conj_asm1_tac >- (
    fs[Abbr`vv`,is_valuation_def,is_term_valuation_def] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[termsem_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rpt (qpat_assum `termsem X Y Z tm = A`kall_tac) >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: x` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`sig`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    simp[] >>
    disch_then(qspec_then`[]`mp_tac) >>
    simp[] >> disch_then kall_tac >>
    simp[Abbr`ii`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    `is_valuation (tysof ctxt) (tyaof i) (τ,λ(x,ty). @v. v <: typesem (tyaof i) τ ty)` by (
      fs[is_valuation_def,is_term_valuation_def] >> rw[] >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_interpretation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`termsem sig i (v1,v2) tt <: tysem` >>
    qmatch_assum_abbrev_tac`is_valuation (tysof ctxt) (tyaof i) (τ,σ)` >>
    `termsem sig i (v1,v2) tt = termsem sig i (τ,v2) tt` by (
      match_mp_tac termsem_tyfrees >>
      simp[Abbr`v1`,REV_ASSOCD,typesem_def,Abbr`sig`] >>
      imp_res_tac theory_ok_sig >>
      fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      rw[] >> metis_tac[] ) >>
    `termsem sig i (τ,v2) tt = termsem sig i (τ,σ) tt` by (
       match_mp_tac termsem_frees >>
       fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,CLOSED_def] >>
       metis_tac[] ) >>
    rw[Abbr`tysem`,Abbr`ty`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[Abbr`sig`] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
    metis_tac[] ) >>
  imp_res_tac theory_ok_sig >>
  `is_structure (sigof ctxt) i vv` by (
    fs[is_structure_def] ) >>
  simp[EVERY_MAP,EVERY_MEM,FORALL_PROD] >> rw[] >>
  fs[EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
  simp[termsem_equation,boolean_eq_true,termsem_def] >>
  simp[Abbr`vv`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
  simp[termsem_def] >>
  qmatch_abbrev_tac`instance sig ii name ty τ = X` >>
  qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
  simp[Abbr`sig`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`ii`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
  qmatch_abbrev_tac`termsem sig i (v1,v2) tt = termsem sig i (v3,v4) tt` >>
  `termsem sig i (v1,v2) tt = termsem sig i (v3,v2) tt` by (
    match_mp_tac termsem_tyfrees >>
    simp[Abbr`sig`,Abbr`v1`,REV_ASSOCD,typesem_def] >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    rw[] >> metis_tac[] ) >>
  `termsem sig i (v3,v2) tt = termsem sig i (v3,v4) tt` by (
    match_mp_tac termsem_frees >> simp[] >>
    fs[EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD,CLOSED_def] >>
    metis_tac[] ) >>
  rw[Abbr`v4`])

val new_type_correct = store_thm("new_type_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt name arity.
     theory_ok (thyof ctxt) ∧
     name ∉ FDOM (tysof ctxt) ⇒
     ∀i. i models (thyof ctxt) ⇒
       ∃i'. i' models (thyof (NewType name arity::ctxt))``,
  rw[models_def] >>
  qexists_tac`((name =+ (K boolset)) (tyaof i),tmaof i)` >>
  simp[conexts_of_upd_def] >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,is_type_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
    simp[combinTheory.APPLY_UPDATE_THM] >> rw[] >- metis_tac[boolean_in_boolset] >>
    qmatch_abbrev_tac`x <: typesem δ' τ ty` >>
    `typesem δ' τ ty = typesem (tyaof i) τ ty` by (
      match_mp_tac typesem_consts >>
      rw[Abbr`δ'`,combinTheory.APPLY_UPDATE_THM] >>
      qexists_tac`tysof ctxt` >>
      conj_asm1_tac >- (
        fs[theory_ok_def] >>
        first_x_assum match_mp_tac >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
        simp[IN_FRANGE,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
        metis_tac[] ) >>
      rw[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    rw[Abbr`x`] ) >>
  conj_tac >- (
    imp_res_tac theory_ok_sig >>
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,is_std_sig_def] >>
    fs[is_std_type_assignment_def,combinTheory.APPLY_UPDATE_THM] >>
    imp_res_tac ALOOKUP_MEM >> rw[] >>
    fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac satisfies_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  rw[] >- fs[theory_ok_def] >>
  match_mp_tac satisfies_consts >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  rw[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[])

val new_type_definition_correct = store_thm("new_type_definition_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h c name pred abs rep rep_type witness.
    (thyof ctxt,[]) |- Comb pred witness ∧
    CLOSED pred ∧ pred has_type (Fun rep_type Bool) ∧
    name ∉ (FDOM (tysof ctxt)) ∧
    abs ∉ (FDOM (tmsof ctxt)) ∧
    rep ∉ (FDOM (tmsof ctxt)) ∧
    abs ≠ rep ⇒
    ∀i. i models (thyof ctxt) ⇒
      ∃i'. i' models (thyof (TypeDefn name pred abs rep::ctxt))``,
  rw[models_def,LET_THM] >>
  Q.PAT_ABBREV_TAC`tys' = tysof ctxt |+ X` >>
  Q.PAT_ABBREV_TAC`tms' = tmsof ctxt |+ X |+ Y` >>
  imp_res_tac WELLTYPED_LEMMA >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac theory_ok_sig >> fs[] >>
  `name ∉ {"fun";"bool"} ∧ abs ≠ "=" ∧ rep ≠ "="` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >> fs[] >>
  qmatch_assum_abbrev_tac`Abbrev(tms' = tmsof ctxt |+ (rep, Fun abs_type rep_type) |+ Y)` >>
  qunabbrev_tac`Y` >>
  qabbrev_tac`argv = STRING_SORT (tvars pred)` >>
  qabbrev_tac`tv:'U list -> 'U tyval = λargs a.
      (case find_index a (STRING_SORT (tvars pred)) 0 of
       | SOME n => EL n args
       | NONE => boolset)` >>
  qabbrev_tac`δ = tyaof i` >>
  qabbrev_tac`sv:'U tyval->'U tmval = λτ (x,ty). @v. v <: typesem δ τ ty` >>
  qabbrev_tac`mpred = λτ. termsem (sigof ctxt) i (τ, sv τ) pred` >>
  qabbrev_tac`mty = λargs. typesem δ (tv args) rep_type suchthat Holds (mpred (tv args))` >>
  qabbrev_tac`mrep = λτ. Abstract (mty (MAP τ argv)) (typesem δ τ rep_type)  I` >>
  qabbrev_tac`mabs = λτ. Abstract (typesem δ τ rep_type) (mty (MAP τ argv))
                           (λv. if Holds (mpred τ) v then v else @v. v <: mty (MAP τ argv))` >>
  imp_res_tac proves_sound >>
  imp_res_tac proves_term_ok >>
  fs[term_ok_def] >>
  imp_res_tac term_ok_type_ok >>
  rfs[type_ok_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac is_std_interpretation_is_type >>
  `∀ls. EVERY inhabited ls ∧ LENGTH ls = LENGTH (tvars pred)
    ⇒ is_type_valuation (tv ls)` by (
    simp[is_type_valuation_def,Abbr`tv`] >> rw[] >>
    BasicProvers.CASE_TAC >- metis_tac[boolean_in_boolset] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS,Abbr`argv`] >>
    imp_res_tac find_index_LESS_LENGTH >> fs[] >> NO_TAC ) >>
  `is_std_type_assignment ((name =+ mty) δ)` by (
    fs[is_std_type_assignment_def,combinTheory.APPLY_UPDATE_THM,Abbr`δ`] ) >>
  `∀τ. is_type_valuation τ ⇒ is_term_valuation (tysof ctxt) δ τ (sv τ)` by (
    rw[is_term_valuation_def,Abbr`sv`] >>
    fs[is_interpretation_def,Abbr`δ`] >>
    metis_tac[typesem_inhabited] ) >>
  `∀ls. EVERY inhabited ls ∧ LENGTH ls = LENGTH argv ⇒ ∃v. v <: mty ls` by (
    gen_tac >> strip_tac >>
    simp[Abbr`mty`,mem_sub] >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    simp[models_def] >>
    fs[satisfies_def] >>
    qabbrev_tac`tt = tv ls` >>
    `is_valuation (tysof ctxt) δ (tt, sv tt)` by (
      simp[Abbr`tt`,is_valuation_def] >>
      conj_asm1_tac >- (
        first_x_assum match_mp_tac >>
        fs[Abbr`argv`] ) >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    disch_then(qspec_then`tt, sv tt`mp_tac)>>simp[] >>
    simp[termsem_def] >> strip_tac >>
    qexists_tac`termsem (sigof ctxt) i (tt, sv tt) witness` >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem) >>
      simp[Abbr`δ`] ) >>
    simp[holds_def] ) >>
  `∀τ. typesem ((name =+ mty) δ) τ (typeof witness) = typesem δ τ (typeof witness)` by (
    gen_tac >>
    match_mp_tac typesem_consts >>
    qexists_tac`tysof ctxt` >>
    rw[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
  `∀x. MEM x (tyvars (typeof witness)) ∨ MEM x (tvars pred) ⇔ MEM x (tvars pred)` by (
    rw[] >> imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF,tyvars_def] >>
    metis_tac[]) >>
  `∀τ y. typesem δ (λx. if MEM x (tvars pred) then τ x else y) (typeof witness) =
         typesem δ τ (typeof witness)` by (
    rpt gen_tac >> match_mp_tac typesem_tyvars >> rw[] >> metis_tac[]) >>
  `∀τ y. mpred (λx. if MEM x (tvars pred) then τ x else y) =
         mpred τ` by (
    rpt gen_tac >> simp[Abbr`mpred`] >>
    qmatch_abbrev_tac`termsem sig i (v1,v2) pred = termsem sig i (v3,v4) pred` >>
    `termsem sig i (v1,v2) pred = termsem sig i (v3,v2) pred` by (
      match_mp_tac termsem_tyfrees >>
      fs[Abbr`sig`,Abbr`v1`] ) >>
    `termsem sig i (v3,v2) pred = termsem sig i (v3,v4) pred` by (
      match_mp_tac termsem_frees >>
      fs[CLOSED_def] ) >>
    unabbrev_all_tac >> simp[] ) >>
  `∀τ. tv (MAP τ argv) = (λx. if MEM x (tvars pred) then τ x else boolset)` by (
    simp[Abbr`tv`,FUN_EQ_THM] >> rw[] >- (
      `MEM x argv` by simp[Abbr`argv`] >>
      imp_res_tac find_index_MEM >>
      rpt(first_x_assum(qspec_then`0`strip_assume_tac)) >>
      simp[EL_MAP] ) >>
    `¬MEM x argv` by simp[Abbr`argv`] >>
    `find_index x argv 0 = NONE` by metis_tac[find_index_NOT_MEM] >>
    simp[] ) >>
  qexists_tac`(name =+ mty) δ,
              (abs =+ mabs) ((rep =+ mrep) (tmaof i))` >>
  conj_asm1_tac >- (
    fs[is_interpretation_def] >>
    conj_asm1_tac >- (
      fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP,Abbr`tys'`,FLOOKUP_UPDATE] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      rw[Abbr`mty`] >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[Abbr`argv`] ) >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP,Abbr`tms'`,FLOOKUP_UPDATE] >>
    rw[combinTheory.APPLY_UPDATE_THM] >- (
      mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
      simp[Abbr`mabs`] >>
      qmatch_abbrev_tac`Abstract a b f <: Funspace c d` >>
      `a = c` by (
        simp[Abbr`a`,Abbr`c`] >>
        match_mp_tac typesem_frees >>
        simp[tyvars_def] ) >>
      `b = d` by (
        simp[Abbr`b`,Abbr`d`,Abbr`mty`,Abbr`abs_type`,typesem_def
            ,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
        simp[tyvars_def,MEM_FOLDR_LIST_UNION] >>
        simp[MEM_MAP,PULL_EXISTS,tyvars_def,Abbr`argv`] ) >>
      simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[Abbr`f`,Abbr`c`,Abbr`d`,Abbr`a`,Abbr`b`] >>
      gen_tac >> strip_tac >> BasicProvers.CASE_TAC >- (
        rw[Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF,Abbr`mty`] >>
        simp[mem_sub] >>
        rfs[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,Abbr`argv`] ) >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      qexists_tac`tys'` >> simp[] >>
      simp[Abbr`abs_type`,type_ok_def,Abbr`tys'`,FLOOKUP_UPDATE,Abbr`argv`,EVERY_MAP] )
    >- (
      mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
      simp[Abbr`mrep`] >>
      qmatch_abbrev_tac`Abstract a b f <: Funspace c d` >>
      `a = c` by (
        simp[Abbr`a`,Abbr`c`,Abbr`mty`,Abbr`b`,Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM] >>
        simp[MAP_MAP_o,typesem_def,Abbr`d`,tyvars_def,MEM_FOLDR_LIST_UNION,PULL_EXISTS,MEM_MAP,Abbr`argv`] >>
        fs[DISJ_COMM] ) >>
      `b = d` by (
        simp[Abbr`b`,Abbr`d`,Abbr`mty`,Abbr`abs_type`,typesem_def
            ,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
        simp[tyvars_def,MEM_FOLDR_LIST_UNION] >>
        simp[MEM_MAP,PULL_EXISTS,tyvars_def,Abbr`argv`] >>
        fs[DISJ_COMM]) >>
      simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[Abbr`f`,Abbr`c`,Abbr`d`,Abbr`a`,Abbr`b`] >>
      simp[Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
      simp[Abbr`mty`,mem_sub] ) >>
    first_x_assum(qspecl_then[`k`,`v`]mp_tac) >>
    simp[] >> disch_then(qspec_then`τ`mp_tac) >>
    simp[] >>
    `typesem ((name =+ mty) δ) τ v = typesem δ τ v` by (
      match_mp_tac typesem_consts >>
      qexists_tac`tysof ctxt` >>
      simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
      fs[theory_ok_def] >>
      reverse(rw[]) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >-
      metis_tac[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
      simp[IN_FRANGE,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    simp[] ) >>
  conj_asm1_tac >- (
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM] ) >>
  `is_std_sig (tys',tms')` by (
    fs[is_std_sig_def,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] ) >>
  gen_tac >> reverse strip_tac >- (
    match_mp_tac satisfies_extend >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    discharge_hyps >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      simp[Abbr`tms'`,SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    conj_tac >- simp[Abbr`tys'`] >>
    match_mp_tac satisfies_consts >>
    qexists_tac`i` >> simp[] >>
    simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    simp[term_ok_def] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  pop_assum mp_tac >>
  simp[conexts_of_upd_def] >>
  strip_tac >- (
    simp[satisfies_def] >>
    gen_tac >> strip_tac >>
    qmatch_abbrev_tac`termsem sig ii v (l1 === l2) = True` >>
    `is_structure sig ii v` by (
      simp[is_structure_def,Abbr`sig`,Abbr`ii`] ) >>
    `term_ok sig (l1 === l2)` by (
      simp[term_ok_equation,Abbr`l1`,Abbr`l2`,term_ok_def] >>
      simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
      simp[Abbr`abs_type`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,Abbr`argv`] >>
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >>
      simp[] ) >>
    simp[termsem_equation,boolean_eq_true] >>
    simp[Abbr`l2`,Abbr`l1`,termsem_def] >>
    qspecl_then[`sig`,`ii`,`abs`]mp_tac instance_def >>
    qspecl_then[`sig`,`ii`,`rep`]mp_tac instance_def >>
    simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
    disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
    disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
    simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
    simp[REV_ASSOCD,typesem_def] >>
    simp[Abbr`mrep`,tyvars_def,Abbr`abs_type`,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,Abbr`argv`,Abbr`mty`] >>
    fs[DISJ_COMM] >>
    PairCases_on`v` >>
    simp[Abbr`mabs`,ETA_AX] >>
    qmatch_abbrev_tac`Abstract a b f ' (Abstract b a I ' c) = c` >> rfs[] >>
    `c <: b` by (
      fs[is_valuation_def,is_term_valuation_def] >>
      qmatch_assum_abbrev_tac`Abbrev(c = v1 (x,ty))` >>
      first_x_assum(qspecl_then[`x`,`ty`]mp_tac) >>
      simp[Abbr`ty`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,typesem_def,combinTheory.APPLY_UPDATE_THM] >>
      simp[MAP_MAP_o,typesem_def] ) >>
    `c <: a` by rfs[Abbr`b`,mem_sub] >>
    `Abstract b a I ' c = I c` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[] ) >>
    `f c = c` by (
      simp[Abbr`f`] >>
      rfs[Abbr`b`,mem_sub] ) >>
    simp[ETA_AX] >>
    metis_tac[apply_abstract] ) >>
  simp[satisfies_def] >>
  gen_tac >> strip_tac >>
  qmatch_abbrev_tac`termsem sig ii v (l1 === l2) = True` >>
  `is_structure sig ii v` by (
    simp[is_structure_def,Abbr`sig`,Abbr`ii`] ) >>
  qmatch_assum_abbrev_tac`Abbrev(l2 = l3 === l4)` >>
  `term_ok sig (l3 === l4)` by (
    simp[term_ok_equation,Abbr`l3`,Abbr`l4`,term_ok_def] >>
    simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
    simp[Abbr`abs_type`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,Abbr`argv`] >>
    match_mp_tac type_ok_extend >>
    qexists_tac`tysof ctxt` >>
    simp[] ) >>
  `l2 has_type Bool` by (
    simp[Abbr`l2`,EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    rfs[term_ok_equation] >>
    imp_res_tac term_ok_welltyped >> fs[] ) >>
  `term_ok sig (l1 === l2)` by (
    simp[term_ok_equation] >> rfs[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    simp[Abbr`l1`,term_ok_def,Abbr`l4`,Abbr`sig`] >>
    conj_tac >- (
      match_mp_tac term_ok_extend >>
      map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
      simp[Abbr`tms'`,Abbr`tys'`] >>
      simp[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    match_mp_tac type_ok_extend >>
    qexists_tac`tysof ctxt` >>
    simp[Abbr`tys'`] ) >>
  simp[termsem_equation,boolean_eq_true] >>
  imp_res_tac term_ok_welltyped >>
  simp[Abbr`l2`,Abbr`l1`,termsem_def,termsem_equation,Abbr`l4`] >>
  simp[Abbr`l3`,termsem_def] >>
  qspecl_then[`sig`,`ii`,`abs`]mp_tac instance_def >>
  qspecl_then[`sig`,`ii`,`rep`]mp_tac instance_def >>
  simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
  simp[REV_ASSOCD,typesem_def] >>
  Q.PAT_ABBREV_TAC`mpred' = termsem X Y v pred` >>
  `mpred' = mpred (tyvof v)` by (
    simp[Abbr`mpred`,Abbr`mpred'`] >>
    qmatch_abbrev_tac`termsem sig ii v pred = x` >>
    `termsem sig ii v pred = termsem (sigof ctxt) ii v pred` by (
      simp[Abbr`sig`] >>
      match_mp_tac termsem_extend >>
      simp[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    `termsem (sigof ctxt) ii v pred = termsem (sigof ctxt) i v pred` by (
      match_mp_tac termsem_consts >>
      simp[type_ok_def,term_ok_def,Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    simp[Abbr`x`] >>
    match_mp_tac termsem_frees >>
    fs[CLOSED_def] ) >>
  simp[Abbr`mrep`,tyvars_def,Abbr`abs_type`,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,Abbr`argv`,Abbr`mty`] >>
  fs[DISJ_COMM] >>
  PairCases_on`v` >>
  simp[Abbr`mabs`,ETA_AX] >>
  qmatch_abbrev_tac`f ' x = Boolean (Abstract a b I ' (Abstract b a g ' x) = x)` >>
  rfs[ETA_AX] >>
  `f <: typesem (tyaof i) v0 (typeof pred)` by (
    simp_tac std_ss [Abbr`f`,Abbr`mpred`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[Abbr`δ`,is_valuation_def] ) >>
  pop_assum mp_tac >>
  mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
  strip_tac >>
  `x <: b` by (
    simp[Abbr`x`,Abbr`b`] >>
    fs[is_valuation_def,is_term_valuation_def] >>
    first_x_assum (qspecl_then[`"r"`,`typeof witness`]mp_tac) >>
    discharge_hyps >- (
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >> simp[] ) >>
    simp[] ) >>
  `f ' x <: boolset` by (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`b` >>
    metis_tac[typesem_Bool] ) >>
  `inhabited a` by (
    simp[Abbr`a`] >>
    first_x_assum(qspec_then`MAP v0 (STRING_SORT (tvars pred))`mp_tac) >>
    discharge_hyps >- (
      simp[EVERY_MAP,EVERY_MEM] >>
      fs[is_valuation_def,is_type_valuation_def] ) >>
    simp[] ) >>
  `Abstract b a g ' x = g x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    simp[Abbr`g`] >> rw[] >- simp[Abbr`a`,mem_sub] >>
    SELECT_ELIM_TAC >> simp[] >>
    metis_tac[] ) >>
  simp[Abbr`g`] >>
  Cases_on`f ' x = True` >- (
    simp[holds_def,boolean_eq_true] >>
    `Abstract a b I ' x = I x` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[Abbr`a`,mem_sub,holds_def] ) >>
    simp[] ) >>
  simp[holds_def,boolean_def] >>
  `Abstract a b I ' (@v. v <: a) = I (@v. v <: a)` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[] >>
    simp[Abbr`a`,mem_sub] ) >>
  simp[] >>
  `f ' (@v. v <: a) = True` by (
    SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
    simp[Abbr`a`,mem_sub,holds_def] ) >>
  metis_tac[mem_boolset])

val _ = export_theory()
