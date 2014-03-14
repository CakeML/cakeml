open HolKernel boolLib bossLib lcsymtacs relationTheory setSpecTheory
open miscLib holBoolTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
val _ = new_theory"holAxioms"

val mem = ``mem:'U->'U->bool``

val _ = Parse.temp_overload_on("A",``Tyvar "A"``)
val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.temp_overload_on("x",``Var "x" A``)
val _ = Parse.temp_overload_on("Absx",``Abs "x" A``)
val _ = Parse.temp_overload_on("g",``Var "f" (Fun A B)``)

(* ETA_AX *)
val mk_eta_ctxt_def = Define`
  mk_eta_ctxt ctxt = NewAxiom ((Absx (Comb g x)) === g)::ctxt`

val eta_extends = store_thm("eta_extends",
  ``∀ctxt. is_std_sig (sigof ctxt) ⇒ mk_eta_ctxt ctxt extends ctxt``,
  rw[extends_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[Once RTC_CASES1] >> rw[mk_eta_ctxt_def] >>
  rw[updates_cases,EQUATION_HAS_TYPE_BOOL,term_ok_equation] >>
  rw[term_ok_def,type_ok_def] >> fs[is_std_sig_def])

val eta_has_model = store_thm("eta_has_model",
  ``is_set_theory ^mem ⇒
    ∀ctxt. is_std_sig (sigof ctxt) ⇒
      ∀i. i models (thyof ctxt) ⇒
        i models (thyof (mk_eta_ctxt ctxt))``,
  rw[models_def,mk_eta_ctxt_def,conexts_of_upd_def] >> res_tac >>
  rw[satisfies_def] >>
  `is_structure (sigof ctxt) i v` by simp[is_structure_def] >>
  `term_ok (sigof ctxt) (Absx (Comb g x) === g)` by (
    rw[term_ok_equation,term_ok_def,type_ok_def] >>
    fs[is_std_sig_def] ) >>
  rw[termsem_equation,boolean_eq_true] >>
  rw[termsem_def] >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Fun >>
  `termsem (sigof ctxt) i v g <: typesem (tyaof i) (tyvof v) (typeof g)` by (
    match_mp_tac (UNDISCH termsem_typesem) >> simp[term_ok_def,type_ok_def] >>
    fs[is_std_sig_def]) >>
  rfs[termsem_def] >>
  rfs[typesem_def] >>
  qspecl_then[`tmvof v ("f",Fun A B)`,`tyvof v "A"`,`tyvof v "B"`]mp_tac (UNDISCH in_funspace_abstract) >>
  discharge_hyps >- ( fs[is_valuation_def,is_type_valuation_def] ) >>
  rw[] >> rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[] >- (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`tyvof v "A"` >>
    rw[combinTheory.APPLY_UPDATE_THM] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[] ) >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  match_mp_tac (UNDISCH apply_abstract) >>
  rw[])

val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty)``)
val _ = Parse.temp_overload_on("P",``Var "P" (Fun A Bool)``)

(* SELECT_AX *)
val mk_select_ctxt_def = Define`
  mk_select_ctxt ctxt =
    NewAxiom (Comb P (Comb (Select A) P)) ::
    NewConst "@" (Fun (Fun A Bool) A) ::
    ctxt`

val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.overload_on("One_One",``λf. Comb (Const "ONE_ONE" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Onto",``λf. Comb (Const "ONTO" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Ind",``Tyapp "ind" []``)

val _ = Parse.temp_overload_on("EXx",``Exists "x" A``)
val _ = Parse.temp_overload_on("Absg",``Abs "f" (Fun A B)``)
val _ = Parse.temp_overload_on("x1",``Var "x1" A``)
val _ = Parse.temp_overload_on("FAx1",``Forall "x1" A``)
val _ = Parse.temp_overload_on("x2",``Var "x2" A``)
val _ = Parse.temp_overload_on("FAx2",``Forall "x2" A``)
val _ = Parse.temp_overload_on("y",``Var "y" B``)
val _ = Parse.temp_overload_on("FAy",``Forall "y" B``)
val _ = Parse.temp_overload_on("h",``Var "f" (Fun A B)``)
val _ = Parse.temp_overload_on("Exh",``Exists "f" (Fun Ind Ind)``)

 (* INFINITY_AX *)
val mk_inf_ctxt_def = Define`
  mk_inf_ctxt ctxt =
    NewAxiom (Exh (And (One_One h) (Not (Onto h)))) ::
    NewType "ind" 0 ::
    ConstDef "ONTO" (Absg (FAy (EXx (y === Comb g x)))) ::
    ConstDef "ONE_ONE"
      (Absg (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))) ::
    ctxt`

val _ = export_theory()
