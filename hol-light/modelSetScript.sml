open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory cardinalTheory
val _ = numLib.prefer_num()
val _ = new_theory"modelSet"

val ind_model_exists = prove(
  ``∃x. (@s:num->bool. s ≠ {} ∧ FINITE s) x``,
    metis_tac[IN_DEF, MEMBER_NOT_EMPTY, IN_SING, FINITE_DEF])

val ind_model_ty =
  new_type_definition ("ind_model",ind_model_exists)
val ind_model_bij = define_new_type_bijections
  {ABS="mk_ind",REP="dest_ind",name="ind_model_bij",tyax=ind_model_ty}
val mk_ind_11     = prove_abs_fn_one_one ind_model_bij
val mk_ind_onto   = prove_abs_fn_onto    ind_model_bij
val dest_ind_11   = prove_rep_fn_one_one ind_model_bij
val dest_ind_onto = prove_rep_fn_onto    ind_model_bij

val inacc_exists = prove(
  ``∃x:num. UNIV x``,
  metis_tac[IN_UNIV,IN_DEF])

val inacc_ty =
  new_type_definition ("I",inacc_exists)
val inacc_bij = define_new_type_bijections
  {ABS="mk_I",REP="dest_I",name="inacc_bij",tyax=inacc_ty}
val mk_I_11     = prove_abs_fn_one_one inacc_bij
val mk_I_onto   = prove_abs_fn_onto    inacc_bij
val dest_I_11   = prove_rep_fn_one_one inacc_bij
val dest_I_onto = prove_rep_fn_onto    inacc_bij

val FINITE_CARD_LT = store_thm("FINITE_CARD_LT",
  ``∀s. FINITE s ⇔ s ≺ 𝕌(:num)``,
  metis_tac[INFINITE_Unum])

val lemma = prove(
  ``∀s. s ≺ 𝕌(:I) ⇔ FINITE s``,
  rw[FINITE_CARD_LT] >>
  match_mp_tac CARDEQ_CARDLEQ >>
  simp[cardeq_REFL] >>
  match_mp_tac cardleq_ANTISYM >>
  simp[cardleq_def,INJ_DEF] >>
  metis_tac[inacc_bij,dest_I_11,mk_I_11,IN_UNIV,IN_DEF])

val I_AXIOM = store_thm("I_AXIOM",
  ``𝕌(:ind_model) ≺ 𝕌(:I) ∧
    ∀s. s ≺ 𝕌(:I) ⇒ POW s ≺ 𝕌(:I)``,
  simp[lemma,FINITE_POW] >>
  `UNIV = IMAGE mk_ind (@s. s ≠ {} ∧ FINITE s)` by (
    simp[Once EXTENSION,IN_DEF,ind_model_bij] >>
    metis_tac[ind_model_bij]) >>
  metis_tac[IMAGE_FINITE,NOT_INSERT_EMPTY,FINITE_EMPTY,FINITE_INSERT])

(* TODO: move *)

val CARDLEQ_CARD = store_thm("CARDLEQ_CARD",
  ``FINITE s1 ∧ FINITE s2 ⇒ (s1 ≼ s2 ⇔ CARD s1 ≤ CARD s2)``,
  rw[EQ_IMP_THM] >-
    metis_tac[cardleq_def,INJ_CARD] >>
  Cases_on`CARD s1 = CARD s2` >-
    metis_tac[cardleq_lteq,CARDEQ_CARD_EQN] >>
  simp[Once cardleq_lteq] >> disj1_tac >>
  simp[cardleq_def] >>
  gen_tac >> match_mp_tac PHP >>
  fsrw_tac[ARITH_ss][])

val CARD_LT_CARD = store_thm("CARD_LT_CARD",
  ``FINITE s1 ∧ FINITE s2 ⇒ (s1 ≺ s2 ⇔ CARD s1 < CARD s2)``,
  rw[] >> simp[cardlt_lenoteq,CARDLEQ_CARD,CARDEQ_CARD_EQN])

val I_INFINITE = store_thm("I_INFINITE",
  ``INFINITE 𝕌(:I)``,
  DISCH_TAC >>
  Q.ISPEC_THEN`count (CARD 𝕌(:I) - 1)`mp_tac (CONJUNCT2 I_AXIOM) >>
  simp[] >>
  simp[CARD_LT_CARD,CARDLEQ_CARD,FINITE_POW] >>
  conj_asm1_tac >- (
    imp_res_tac CARD_EQ_0 >>
    fs[EXTENSION] >> DECIDE_TAC ) >>
  match_mp_tac(DECIDE``a - 1 < b ∧ 0 < a ==> a <= b``) >>
  reverse conj_tac >- pop_assum ACCEPT_TAC >>
  qmatch_abbrev_tac`n < CARD (POW (count n))` >>
  rpt (pop_assum kall_tac) >>
  Induct_on`n` >>
  simp[COUNT_SUC,POW_EQNS] >>
  qmatch_abbrev_tac`SUC n < CARD (a ∪ b)` >>
  `FINITE a ∧ FINITE b` by simp[Abbr`a`,Abbr`b`,IMAGE_FINITE,FINITE_POW] >>
  `∀s. s ∈ b ⇒ ∀x. x ∈ s ⇒ x < n` by (
    simp[Abbr`b`,IN_POW,SUBSET_DEF] ) >>
  `∀s. s ∈ a ⇒ n ∈ s` by (
    simp[Abbr`a`,GSYM LEFT_FORALL_IMP_THM] ) >>
  `a ∩ b = {}` by (
    simp[Once EXTENSION] >>
    metis_tac[prim_recTheory.LESS_REFL] ) >>
  qsuff_tac`SUC n < CARD a + CARD b`>-
    metis_tac[DECIDE``a + 0 = a``,CARD_EMPTY,CARD_UNION] >>
  fs[Abbr`b`,CARD_POW] >>
  qsuff_tac`CARD a ≠ 0`>-DECIDE_TAC>>
  simp[CARD_EQ_0,Abbr`a`] >>
  simp[EXTENSION,IN_POW] >>
  qexists_tac`{}`>>simp[])

val I_PAIR_EXISTS = store_thm("I_PAIR_EXISTS",
  ``∃f:I#I->I. !x y. (f x = f y) ==> (x = y)``,
  qsuff_tac `𝕌(:I#I) ≼ 𝕌(:I)` >-
    simp[cardleq_def,INJ_DEF] >>
  match_mp_tac CARDEQ_SUBSET_CARDLEQ >>
  qsuff_tac`𝕌(:I#I) = 𝕌(:I) × 𝕌(:I)` >-
    metis_tac[cardeq_TRANS,SET_SQUARED_CARDEQ_SET,I_INFINITE] >>
  simp[EXTENSION])

val INJ_LEMMA = METIS_PROVE[]``(!x y. (f x = f y) ==> (x = y)) <=> (!x y. (f x = f y) <=> (x = y))``

val I_PAIR_def =
  new_specification("I_PAIR_def",["I_PAIR"],
    REWRITE_RULE[INJ_LEMMA] I_PAIR_EXISTS)

val _ = export_theory()
