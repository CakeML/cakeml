(*
  Proves soundness of the inference system: any provable sequent is valid.
*)
open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory

val _ = new_theory"holSoundness"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U-> bool``

Theorem binary_inference_rule:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀i v. is_structure (sigof thy) i v ∧
           termsem (tmsof thy) i v p1 = True ∧
           termsem (tmsof thy) i v p2 = True ⇒
           termsem (tmsof thy) i v q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, term_union h1 h2) |= q
Proof
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def,EVERY_term_union] >> rw[] >>
  rpt (first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def,EVERY_term_union] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- ( rw[is_structure_def] >> Cases_on`thy` >> fs[models_def,theory_ok_def] ) >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[EVERY_MEM] >> rw[] >>
  qmatch_assum_abbrev_tac`MEM t h` >>
  qspecl_then[`h1`,`h2`,`t`]mp_tac MEM_term_union >> simp[] >> strip_tac >>
  metis_tac[MEM_term_union_imp,termsem_aconv,term_ok_welltyped]
QED

Theorem ABS_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs (Var x ty) l === Abs (Var x ty) r
Proof
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
  qsuff_tac`termsem (tmsof (sigof thy)) i vv t = termsem (tmsof (sigof thy)) i v t`>-metis_tac[] >>
  match_mp_tac termsem_frees >>
  simp[Abbr`vv`,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[term_ok_welltyped]
QED

Theorem ASSUME_correct:
   ∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p
Proof
  rw[entails_def,satisfies_def]
QED

Theorem BETA_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs (Var x ty) t) (Var x ty) === t
Proof
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
    rw[combinTheory.APPLY_UPDATE_THM] >>
    metis_tac[]) >>
  simp[Abbr`f`,Abbr`e`] >>
  rw[combinTheory.APPLY_UPDATE_ID]
QED

Theorem DEDUCT_ANTISYM_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2))
      |= p1 === p2
Proof
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
  rw[satisfies_def] >>
  `is_structure (sigof thy) i v` by (
    fs[models_def,is_structure_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  simp[boolean_eq_true] >>
  rpt(first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def] >>
  rpt(first_x_assum(qspec_then`v`mp_tac)>>rw[]) >>
  fs[EVERY_MEM] >>
  pop_assum kall_tac >>
  ntac 2 (pop_assum mp_tac) >>
  `∀x y ls. hypset_ok ls ⇒
    (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
      metis_tac[MEM_term_remove,MEM_term_remove_imp] >>
  qmatch_abbrev_tac`(a ⇒ b) ⇒ (c ⇒ d) ⇒ e` >>
  `d ⇒ a` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[MEM_term_union,termsem_aconv,welltyped_def,hypset_ok_term_remove] ) >>
  `b ⇒ c` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[MEM_term_union,termsem_aconv,welltyped_def,hypset_ok_term_remove] ) >>
  `termsem (tmsof (sigof thy)) i v p1 <: boolset ∧
   termsem (tmsof (sigof thy)) i v p2 <: boolset` by (
    fs[is_structure_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac termsem_typesem >>
    imp_res_tac WELLTYPED_LEMMA >>
    metis_tac[typesem_Bool]) >>
  metis_tac[mem_boolset]
QED

Theorem EQ_MP_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,term_union h1 h2) |= q
Proof
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`p === q`,`p'`] >>
  fs[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  fs[term_ok_equation] >>
  conj_asm1_tac >- metis_tac[ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >> rw[] >>
  `term_ok (sigof thy) (p === q)` by metis_tac[term_ok_equation] >>
  imp_res_tac (UNDISCH termsem_equation) >> rfs[boolean_eq_true] >>
  metis_tac[termsem_aconv,term_ok_welltyped]
QED

Theorem INST_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, term_image (VSUBST ilist) h) |= VSUBST ilist c
Proof
  rw[entails_def,EVERY_MEM,satisfies_def] >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_VSUBST >> metis_tac[] ) >>
  TRY ( match_mp_tac VSUBST_HAS_TYPE >> metis_tac[] ) >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  qspecl_then[`c`,`ilist`]mp_tac termsem_VSUBST >>
  impl_tac >- metis_tac[welltyped_def] >>
  disch_then(qspecl_then[`tmsof(sigof thy)`,`i`,`v`]SUBST1_TAC) >>
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
  gen_tac >> strip_tac >>
  qspecl_then[`h`,`VSUBST ilist`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  first_x_assum(fn th => first_assum (CHANGED_TAC o SUBST1_TAC o SYM o MATCH_MP th)) >>
  metis_tac[MEM_term_image_imp,termsem_VSUBST,welltyped_def,VSUBST_WELLTYPED,termsem_aconv]
QED

Theorem INST_TYPE_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, term_image (INST tyin) h) |= INST tyin c
Proof
  rw[entails_def,EVERY_MAP,EVERY_MEM,satisfies_def] >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_INST >> fs[EVERY_MAP,EVERY_MEM] >> metis_tac[] ) >>
  TRY ( match_mp_tac INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool] ) >>
  qspecl_then[`sigof thy`,`c`,`tyin`]mp_tac termsem_INST >> simp[] >>
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
  gen_tac >> strip_tac >>
  qspecl_then[`h`,`INST tyin`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  first_x_assum(fn th => first_assum (CHANGED_TAC o SUBST1_TAC o SYM o MATCH_MP th)) >>
  metis_tac[MEM_term_image_imp,SIMP_RULE(srw_ss())[]termsem_INST,
            welltyped_def,INST_WELLTYPED,termsem_aconv]
QED

Theorem MK_COMB_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,term_union h1 h2) |= Comb l1 l2 === Comb r1 r2
Proof
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
  rw[termsem_def]
QED

Theorem REFL_correct:
   is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t
Proof
  rw[] >>
  simp[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- rw[term_ok_equation] >>
  rw[satisfies_def] >>
  `is_structure (sigof thy) i v` by (
    rw[is_structure_def] >> fs[models_def] ) >>
  imp_res_tac termsem_equation >>
  rw[boolean_def]
QED

Theorem proves_sound:
   is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
Proof
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
  rw[entails_def,theory_ok_def,models_def]
QED

val _ = export_theory()
