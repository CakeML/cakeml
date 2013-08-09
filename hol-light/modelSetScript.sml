open HolKernel boolLib bossLib lcsymtacs pred_setTheory
val _ = new_theory"modelSet"

val _ = Parse.add_infix("<=_c",450,Parse.NONASSOC)
val _ = Parse.add_infix("<_c",450,Parse.NONASSOC)

val le_c_def = xDefine"le_c"
  `s <=_c t ⇔ ∃f. INJ f s t`

val lt_c_def = xDefine"lt_c"
  `s <_c t ⇔ s <=_c t ∧ ~(t <=_c s)`

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

(*
val lemma = prove(
  ``∀s. s <_c UNIV:I->bool ⇔ FINITE s``,
  FINITE_CARD_LT

val I_AXIOM = store_thm("I_AXIOM",
  ``UNIV:ind_model->bool <_c UNIV:I->bool ∧
    (∀s. s <_c UNIV:I->bool ⇒ POW s <_c UNIV:I->bool)``,
*)

val _ = export_theory()
