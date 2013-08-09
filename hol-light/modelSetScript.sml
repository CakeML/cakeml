open HolKernel boolLib bossLib lcsymtacs pred_setTheory cardinalTheory
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

val _ = export_theory()
