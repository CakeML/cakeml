(*
  Proves consistency of the inference system: starting from any context with a
  model, any context reached by non-axiomatic extensions has both provable and
  unprovable sequents. And the base case: the HOL contexts (initial context
  with no axioms, with all but infinity axiom, with all three axioms) have
  models (under suitable assumptions).
*)
open preamble
     setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory holAxiomsSyntaxTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holExtensionTheory holBoolTheory holAxiomsTheory

val _ = new_theory"holConsistency"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val consistent_theory_def = Define`
  consistent_theory thy ⇔
        (thy,[]) |- (Var (strlit"x") Bool === Var (strlit"x") Bool) ∧
      ¬((thy,[]) |- (Var (strlit"x") Bool === Var (strlit"y") Bool))`

Theorem proves_consistent:
   is_set_theory ^mem ⇒
    ∀thy. theory_ok thy ∧ (∃i. i models thy) ⇒
      consistent_theory thy
Proof
  rw[consistent_theory_def] >- (
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
              λ(x,ty). if (x,ty) = (strlit"x",Bool) then True else
                       if (x,ty) = (strlit"y",Bool) then False else
                       @v. v <: typesem (tyaof i) (K boolset) ty` >>
  conj_asm1_tac >- (
    simp[is_valuation_def] >>
    conj_asm1_tac >- (simp[is_type_valuation_def,mem_boolset] >> PROVE_TAC[]) >>
    fs[models_def,is_term_valuation_def,is_interpretation_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >>
    rw[mem_boolset] >>
    metis_tac[typesem_inhabited] ) >>
  qmatch_abbrev_tac`termsem (tmsof (sigof thy)) i v (s === t) ≠ True` >>
  qspecl_then[`sigof thy`,`i`,`v`,`s`,`t`]mp_tac(UNDISCH termsem_equation) >>
  simp[] >>
  impl_tac >- (
    simp[term_ok_equation,is_structure_def] >>
    fs[models_def,theory_ok_def] ) >>
  simp[Abbr`s`,Abbr`t`,termsem_def,boolean_eq_true,Abbr`v`,true_neq_false]
QED

Theorem init_ctxt_has_model:
   is_set_theory ^mem ⇒ ∃i. i models (thyof init_ctxt)
Proof
  rw[models_def,init_ctxt_def,conexts_of_upd_def] >>
  rw[is_std_interpretation_def,is_std_type_assignment_def,EXISTS_PROD] >>
  qho_match_abbrev_tac`∃f g. P f g ∧ (Q f ∧ f x2 z2 = y2) ∧ (g interprets x3 on z3 as y3)` >>
  qexists_tac`λx. if x = strlit"fun" then (λls. Funspace (HD ls) (HD (TL ls))) else if x = x2 then (K y2) else ARB` >>
  qexists_tac`K y3` >>
  rw[Abbr`x2`,Abbr`P`,Abbr`Q`,interprets_def] >>
  rw[is_interpretation_def,is_type_assignment_def,is_term_assignment_def] >>
  rw[FEVERY_FUPDATE,Abbr`y2`,Abbr`y3`,FEVERY_FEMPTY,Abbr`z3`] >>
  rw[typesem_def,tyvars_def] >- metis_tac[boolean_in_boolset] >>
  TRY (
    rw[INORDER_INSERT_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,mlstringTheory.implode_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] ) >>
  Cases_on`ls`>>fs[]>>Cases_on`t`>>fs[listTheory.LENGTH_NIL] >>
  match_mp_tac (UNDISCH funspace_inhabited) >>
  metis_tac[]
QED

Theorem min_hol_consistent:
   is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt ∧ (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) init_ctxt) ⇒
      consistent_theory (thyof ctxt)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[extends_theory_ok,extends_consistent,init_theory_ok,init_ctxt_has_model]
QED

val fhol_ctxt_def = Define`
  fhol_ctxt = mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`

Theorem fhol_extends_bool:
   fhol_ctxt extends (mk_bool_ctxt init_ctxt)
Proof
  rw[fhol_ctxt_def] >>
  match_mp_tac extends_trans >>
  qexists_tac`mk_eta_ctxt (mk_bool_ctxt init_ctxt)` >>
  reverse conj_asm2_tac >- (
    match_mp_tac eta_extends >>
    match_mp_tac is_bool_sig_std >>
    match_mp_tac bool_has_bool_sig >>
    `sigof init_ctxt = sigof (thyof init_ctxt)` by simp[] >>
    metis_tac[theory_ok_sig,init_theory_ok] ) >>
  match_mp_tac select_extends >>
  EVAL_TAC
QED

fun tac extends_bool unfold =
  strip_tac >> gen_tac >> strip_tac >>
  assume_tac bool_extends_init >>
  imp_res_tac init_ctxt_has_model >>
  qspecl_then[`init_ctxt`,`mk_bool_ctxt init_ctxt`]mp_tac(UNDISCH extends_consistent) >>
  simp[] >> disch_then(qspec_then`i`mp_tac) >>
  simp[init_theory_ok] >>
  impl_tac >- (EVAL_TAC >> simp[]) >>
  disch_then(qx_choose_then`i2`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`ctxt extends ctxt0` >>
  `theory_ok (thyof ctxt0)` by (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`init_ctxt` >>
    metis_tac[init_theory_ok,extends_bool,bool_extends_init,extends_trans]) >>
  qunabbrev_tac`ctxt0` >>
  conj_asm1_tac >- (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    metis_tac[]) >>
  unfold >>
  qspec_then`mk_bool_ctxt init_ctxt`mp_tac(UNDISCH eta_has_model) >>
  `∀ctxt. sigof ctxt = sigof (thyof ctxt)` by simp[] >>
  impl_tac >- (
    match_mp_tac is_bool_sig_std >>
    match_mp_tac bool_has_bool_sig >>
    metis_tac[theory_ok_sig,init_theory_ok] ) >>
  disch_then(qspec_then`i2`mp_tac) >> simp[] >> strip_tac >>
  qspec_then`mk_eta_ctxt (mk_bool_ctxt init_ctxt)`mp_tac(UNDISCH select_has_model) >>
  `theory_ok (thyof (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))` by (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`mk_bool_ctxt init_ctxt` >>
    reverse conj_asm2_tac >-
      metis_tac[extends_theory_ok,bool_extends_init,init_theory_ok] >>
    match_mp_tac eta_extends >>
    metis_tac[theory_ok_sig] ) >>
  impl_tac >- ( rw[] >> EVAL_TAC ) >>
  disch_then(qspec_then`i2`mp_tac) >>
  qspecl_then[`init_ctxt`,`i2`]mp_tac(UNDISCH bool_has_bool_interpretation) >>
  impl_tac >- (
    metis_tac[extends_theory_ok,bool_extends_init,init_theory_ok] ) >>
  strip_tac >>
  impl_tac >- fs[is_bool_interpretation_def] >>
  disch_then(qx_choose_then`i3`strip_assume_tac)

Theorem fhol_has_model:
   is_set_theory ^mem ⇒
    ∀ctxt.
      ctxt extends fhol_ctxt ∧
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) fhol_ctxt) ⇒
      theory_ok (thyof ctxt) ∧ ∃i. i models thyof ctxt
Proof
  tac fhol_extends_bool ALL_TAC >>
  fs[GSYM fhol_ctxt_def] >>
  qspecl_then[`fhol_ctxt`,`ctxt`]mp_tac(UNDISCH extends_consistent) >> simp[] >>
  metis_tac[]
QED

Theorem fhol_consistent:
   is_set_theory ^mem ⇒
    ∀ctxt.
      ctxt extends fhol_ctxt ∧
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) fhol_ctxt) ⇒
      consistent_theory (thyof ctxt)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[fhol_has_model]
QED

val hol_ctxt_def = Define`
  hol_ctxt = mk_infinity_ctxt fhol_ctxt`

Theorem hol_extends_fhol:
   hol_ctxt extends fhol_ctxt
Proof
  rw[hol_ctxt_def] >>
  match_mp_tac infinity_extends >>
  reverse conj_tac >- EVAL_TAC >>
  match_mp_tac (MP_CANON extends_theory_ok) >>
  match_exists_tac (concl fhol_extends_bool) >>
  conj_tac >- ACCEPT_TAC fhol_extends_bool >>
  match_mp_tac (MP_CANON extends_theory_ok) >>
  metis_tac[bool_extends_init,init_theory_ok]
QED

Theorem hol_extends_bool:
   hol_ctxt extends (mk_bool_ctxt init_ctxt)
Proof
  match_mp_tac extends_trans >>
  metis_tac[hol_extends_fhol,fhol_extends_bool]
QED

Theorem hol_has_model:
   is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
    ∀ctxt.
      ctxt extends hol_ctxt ∧
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) hol_ctxt) ⇒
      theory_ok (thyof ctxt) ∧ ∃i. i models thyof ctxt
Proof
  tac hol_extends_bool (fs[hol_ctxt_def]) >>
  assume_tac(UNDISCH(PROVE[]``is_infinite mem inf ⇒ ∃inf. is_infinite ^mem inf``)) >>
  qspec_then`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`mp_tac
    (infinity_has_model |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH |> UNDISCH) >>
  pop_assum kall_tac >>
  impl_tac >- (
    conj_tac >- (
      match_mp_tac (MP_CANON extends_theory_ok) >>
      qexists_tac`mk_eta_ctxt (mk_bool_ctxt init_ctxt)` >>
      conj_tac >- (
        match_mp_tac select_extends >>
        imp_res_tac theory_ok_sig >> fs[] >>
        EVAL_TAC ) >>
      simp[] ) >>
    EVAL_TAC ) >>
  disch_then(qspec_then`i3`mp_tac) >>
  impl_tac >- (
    simp[] >>
    fs[is_bool_interpretation_def] >>
    fs[is_implies_interpretation_def,is_and_interpretation_def,is_forall_interpretation_def,
       is_exists_interpretation_def,is_not_interpretation_def] >>
    rpt conj_tac >>
    match_mp_tac equal_on_interprets >>
    map_every qexists_tac[`sigof(mk_eta_ctxt (mk_bool_ctxt init_ctxt))`,`i2`] >> simp[] >>
    EVAL_TAC >> simp[] >> EVAL_TAC >> simp[SUBSET_DEF] ) >>
  disch_then(qx_choose_then`i4`strip_assume_tac) >>
  fs[GSYM hol_ctxt_def,GSYM fhol_ctxt_def] >>
  qspecl_then[`hol_ctxt`,`ctxt`]mp_tac(UNDISCH extends_consistent) >> simp[] >>
  metis_tac[]
QED

Theorem hol_consistent:
   is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
    ∀ctxt.
      ctxt extends hol_ctxt ∧
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) hol_ctxt) ⇒
      consistent_theory (thyof ctxt)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[hol_has_model]
QED

val _ = export_theory()
