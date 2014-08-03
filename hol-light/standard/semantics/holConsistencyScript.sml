open HolKernel boolLib bossLib lcsymtacs pairTheory finite_mapTheory pred_setTheory
open miscLib miscTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory holAxiomsSyntaxTheory
open holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holExtensionTheory holBoolTheory holAxiomsTheory
val _ = temp_tight_equality()
val _ = new_theory"holConsistency"

val mem = ``mem:'U->'U->bool``

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
  qmatch_abbrev_tac`termsem (tmsof ctxt) i v (s === t) ≠ True` >>
  qspecl_then[`sigof ctxt`,`i`,`v`,`s`,`t`]mp_tac(UNDISCH termsem_equation) >>
  simp[] >>
  discharge_hyps >- (
    simp[term_ok_equation,is_structure_def] >>
    fs[models_def,theory_ok_def] ) >>
  simp[Abbr`s`,Abbr`t`,termsem_def,boolean_eq_true,Abbr`v`,true_neq_false])

val init_ctxt_has_model = store_thm("init_ctxt_has_model",
  ``is_set_theory ^mem ⇒ ∃i. i models (thyof init_ctxt)``,
  rw[models_def,init_ctxt_def,conexts_of_upd_def] >>
  rw[is_std_interpretation_def,is_std_type_assignment_def,EXISTS_PROD] >>
  qho_match_abbrev_tac`∃f g. P f g ∧ (f x1 = y1 ∧ f x2 = y2) ∧ (g interprets x3 on z3 as y3)` >>
  qexists_tac`λx. if x = x1 then y1 else if x = x2 then y2 else ARB` >>
  qexists_tac`K y3` >>
  rw[Abbr`x1`,Abbr`x2`,Abbr`P`,interprets_def] >>
  rw[is_interpretation_def,is_type_assignment_def,is_term_assignment_def] >>
  rw[FEVERY_FUPDATE,Abbr`y2`,Abbr`y1`,Abbr`y3`,FEVERY_FEMPTY,Abbr`z3`] >>
  rw[typesem_def,tyvars_def] >>
  TRY (
    rw[INORDER_INSERT_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] ) >>
  BasicProvers.CASE_TAC >> fs[] >- metis_tac[boolean_in_boolset] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac (UNDISCH funspace_inhabited) >>
  metis_tac[])

val min_hol_consistent = store_thm("min_hol_consistent",
  ``is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt ∧ (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) init_ctxt) ⇒
      (thyof ctxt,[]) |- (Var "x" Bool === Var "x" Bool) ∧
      ¬((thyof ctxt,[]) |- (Var "x" Bool === Var "y" Bool))``,
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[extends_theory_ok,extends_consistent,init_theory_ok,init_ctxt_has_model])

val hol_ctxt_def = Define`
  hol_ctxt = mk_infinity_ctxt (mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt)))`

val hol_extends_bool = store_thm("hol_extends_bool",
  ``hol_ctxt extends (mk_bool_ctxt init_ctxt)``,
  rw[hol_ctxt_def] >>
  match_mp_tac extends_trans >>
  qexists_tac`mk_eta_ctxt (mk_bool_ctxt init_ctxt)` >>
  reverse conj_asm2_tac >- (
    match_mp_tac eta_extends >>
    match_mp_tac is_bool_sig_std >>
    match_mp_tac bool_has_bool_sig >>
    `sigof init_ctxt = sigof (thyof init_ctxt)` by simp[] >>
    metis_tac[theory_ok_sig,init_theory_ok] ) >>
  match_mp_tac extends_trans >>
  qexists_tac`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))` >>
  reverse conj_asm2_tac >- (
    match_mp_tac select_extends >>
    EVAL_TAC ) >>
  match_mp_tac infinity_extends >>
  assume_tac init_theory_ok >>
  assume_tac bool_extends_init >>
  imp_res_tac extends_theory_ok >>
  fs[] >>
  conj_tac >- (
    EVAL_TAC >>
    rw[IN_DISJOINT] >>
    spose_not_then strip_assume_tac >>
    pop_assum mp_tac >> simp[] >>
    conj_tac >>
    spose_not_then strip_assume_tac >>
    fs[] ) >>
  EVAL_TAC)

val subinterpretation_interprets = store_thm("subinterpretation_interprets",
  ``∀ctxt i1 i2 name args ty m.
      subinterpretation ctxt i1 i2 ∧
      tmaof i1 interprets name on args as m ∧
      (FLOOKUP (tmsof ctxt) name = SOME ty) ∧
      type_ok (tysof ctxt) ty ∧
      (set (tyvars ty) = set args) ⇒
      tmaof i2 interprets name on args as m``,
  rw[subinterpretation_def,interprets_def] >>
  qsuff_tac`tmaof i2 name = tmaof i1 name` >- metis_tac[] >>
  first_x_assum match_mp_tac >>
  rw[term_ok_def] >>
  qexists_tac`ty`>>rw[])

val _ = store_thm("hol_consistent",
  ``is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
    ∀ctxt.
      ctxt extends hol_ctxt ∧
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) hol_ctxt) ⇒
      (thyof ctxt,[]) |- Var "x" Bool === Var "x" Bool ∧
      ¬((thyof ctxt,[]) |- Var "x" Bool === Var "y" Bool)``,
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  assume_tac bool_extends_init >>
  imp_res_tac init_ctxt_has_model >>
  qspecl_then[`init_ctxt`,`mk_bool_ctxt init_ctxt`]mp_tac(UNDISCH extends_consistent) >>
  simp[] >> disch_then(qspec_then`i`mp_tac) >>
  simp[init_theory_ok] >>
  discharge_hyps >- (EVAL_TAC >> simp[]) >>
  disch_then(qx_choose_then`i2`strip_assume_tac) >>
  `theory_ok (thyof hol_ctxt)` by (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`init_ctxt` >>
    metis_tac[init_theory_ok,hol_extends_bool,bool_extends_init,extends_trans]) >>
  conj_asm1_tac >- (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`hol_ctxt` >> simp[] ) >>
  fs[hol_ctxt_def] >>
  qspec_then`mk_bool_ctxt init_ctxt`mp_tac(UNDISCH eta_has_model) >>
  `∀ctxt. sigof ctxt = sigof (thyof ctxt)` by simp[] >>
  discharge_hyps >- (
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
  discharge_hyps >- ( rw[] >> EVAL_TAC ) >>
  disch_then(qspec_then`i2`mp_tac) >>
  qspecl_then[`init_ctxt`,`i2`]mp_tac(UNDISCH bool_has_bool_interpretation) >>
  discharge_hyps >- (
    metis_tac[extends_theory_ok,bool_extends_init,init_theory_ok] ) >>
  strip_tac >>
  discharge_hyps >- fs[is_bool_interpretation_def] >>
  disch_then(qx_choose_then`i3`strip_assume_tac) >>
  assume_tac(UNDISCH(PROVE[]``is_infinite mem inf ⇒ ∃inf. is_infinite ^mem inf``)) >>
  qspec_then`mk_select_ctxt (mk_eta_ctxt (mk_bool_ctxt init_ctxt))`mp_tac
    (infinity_has_model |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH |> UNDISCH) >>
  pop_assum kall_tac >>
  discharge_hyps >- (
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
  discharge_hyps >- (
    simp[] >>
    rpt conj_tac >>
    match_mp_tac subinterpretation_interprets >>
    map_every qexists_tac[`mk_eta_ctxt (mk_bool_ctxt init_ctxt)`,`i2`] >>
    fs[is_bool_interpretation_def] >>
    EVAL_TAC >> simp[] >> EVAL_TAC >> simp[SUBSET_DEF] ) >>
  disch_then(qx_choose_then`i4`strip_assume_tac) >>
  fs[GSYM hol_ctxt_def] >>
  qspecl_then[`hol_ctxt`,`ctxt`]mp_tac(UNDISCH extends_consistent) >> simp[] >>
  metis_tac[])

val _ = export_theory()
