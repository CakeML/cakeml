open HolKernel boolLib bossLib lcsymtacs listTheory
open setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holSoundness"

val mem = ``mem:'U->'U-> bool``

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀ctxt p. is_std_sig (sigof ctxt) ∧ p has_type Bool ∧ term_ok (sigof ctxt) p
             ⇒ (ctxt,[p]) |= p``,
  rw[entails_def,satisfies_def])

val REFL_correct = store_thm("REFL_correct",
  ``is_set_theory ^mem ⇒
    is_std_sig (sigof ctxt) ⇒
    ∀t. term_ok (sigof ctxt) t ⇒
      (ctxt,[]) |= t === t``,
  rw[entails_def,satisfies_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac term_ok_welltyped >>
  `term_ok (sigof ctxt) (t === t)` by rw[term_ok_equation] >>
  `is_structure (sigof ctxt) v i` by (
    rw[is_structure_def] >> fs[is_model_def] ) >>
  imp_res_tac term_ok_type_ok >> fs[] >>
  imp_res_tac termsem_equation >>
  rw[boolean_def])

val binary_inference_rule = store_thm("binary_inference_rule",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof ctxt) q ∧
    (∀v i. is_structure (sigof ctxt) v i ∧
           termsem v i p1 = True ∧
           termsem v i p2 = True ⇒
           termsem v i q = True) ∧
    (ctxt,h1) |= p1 ∧ (ctxt,h2) |= p2
    ⇒ (ctxt, TERM_UNION h1 h2) |= q``,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def] >> rw[] >>
  rpt (first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def,EVERY_TERM_UNION] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- ( rw[is_structure_def] >> fs[is_model_def] ) >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[EVERY_MEM] >>
  metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,termsem_aconv,welltyped_def])

val TRANS_correct = store_thm("TRANS_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 l m1 m2 r.
      (ctxt,h1) |= l === m1 ∧ (ctxt,h2) |= m2 === r ∧ ACONV m1 m2
      ⇒ (ctxt,TERM_UNION h1 h2) |= l === r``,
  strip_tac >>
  rw[] >> match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l === m1`,`m2 === r`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  fs[entails_def] >>
  simp[CONJ_ASSOC] >> conj_asm1_tac >- (
    metis_tac[ACONV_TYPE,ACONV_welltyped,term_ok_welltyped,term_ok_equation] ) >>
  rw[] >> imp_res_tac termsem_equation >>
  rfs[boolean_eq_true] >> fs[term_ok_equation] >>
  metis_tac[termsem_aconv,ACONV_SYM,term_ok_welltyped])

val _ = export_theory()
