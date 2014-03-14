open HolKernel boolLib bossLib lcsymtacs relationTheory pairTheory listTheory finite_mapTheory alistTheory
open miscLib miscTheory setSpecTheory holBoolTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
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
    NewAxiom (Implies (Comb P x) (Comb P (Comb (Select A) P))) ::
    NewConst "@" (Fun (Fun A Bool) A) ::
    ctxt`

val select_extends = store_thm("select_extends",
  ``∀ctxt. is_std_sig (sigof ctxt) ∧
           "@" ∉ FDOM (tmsof ctxt) ∧
           (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool)))
    ⇒ mk_select_ctxt ctxt extends ctxt``,
  rw[extends_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[Once RTC_CASES1] >> reverse(rw[mk_select_ctxt_def]) >- (
    rw[updates_cases,type_ok_def] >> fs[is_std_sig_def] ) >>
  rw[updates_cases,term_ok_def,type_ok_def] >- (
    rpt(simp[Once has_type_cases]) ) >>
  fs[is_std_sig_def,FLOOKUP_UPDATE])

val select_has_model = store_thm("select_has_model",
  ``is_set_theory ^mem ⇒
    ∀ctxt.
      "@" ∉ FDOM (tmsof ctxt) ∧
      (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
      theory_ok (thyof ctxt)
      ⇒
      ∀i. i models (thyof ctxt) ∧
          tmaof i interprets "==>" on [] as
            (K (Abstract boolset (Funspace boolset boolset)
                   (λp. Abstract boolset boolset
                       (λq. Boolean ((p = True) ⇒ (q = True))))))
      ⇒ ∃i'. i' models (thyof (mk_select_ctxt ctxt))``,
  rw[models_def,mk_select_ctxt_def,conexts_of_upd_def] >>
  qexists_tac`(tyaof i, ("@" =+ λl. Abstract (Funspace (HD l) boolset) (HD l)
    (λp. case some v. v <: HD l ∧ Holds p v of NONE => @v. v <: HD l | SOME v => v)) (tmaof i))` >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Fun >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
    rw[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
    rw[typesem_def,tyvars_def,STRING_SORT_def,LIST_UNION_def,INORDER_INSERT_def,LIST_INSERT_def] >>
    fs[is_std_type_assignment_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[holds_def] >> fs[is_type_valuation_def] >>
    qho_match_abbrev_tac`(case ($some Q) of NONE => R | SOME v => v) <: τ"A"` >>
    qho_match_abbrev_tac`Z ($some Q)` >>
    match_mp_tac optionTheory.some_intro >>
    unabbrev_all_tac >> simp[] >> metis_tac[] ) >>
  conj_tac >- (
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,interprets_def] ) >>
  reverse(rw[]) >- (
    match_mp_tac satisfies_extend >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    simp[] >>
    conj_asm1_tac >- fs[theory_ok_def] >>
    match_mp_tac satisfies_consts >>
    imp_res_tac theory_ok_sig >>
    fs[] >> qexists_tac`i` >>
    simp[] >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> fs[term_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  simp[satisfies_def] >>
  gen_tac >> strip_tac >>
  qmatch_abbrev_tac`termsem sig ii v tm = True` >>
  `FLOOKUP (tmsof sig) "@" = SOME (Fun (Fun A Bool) A)` by simp[Abbr`sig`,FLOOKUP_UPDATE] >>
  `FLOOKUP (tmsof sig) "==>" = SOME (Fun Bool (Fun Bool Bool))` by simp[Abbr`sig`,FLOOKUP_UPDATE] >>
  imp_res_tac identity_instance >>
  simp[Abbr`tm`,termsem_def] >>
  simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def] >>
  simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
  fs[interprets_def] >>
  last_x_assum(qspec_then`tyvof v`mp_tac) >>
  discharge_hyps >- fs[is_valuation_def] >>
  simp[] >> disch_then kall_tac >>
  qmatch_abbrev_tac`(Abstract bs fbs fi ' fz) ' fy = True` >>
  `fi fz <: fbs` by (
    unabbrev_all_tac >> simp[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  qmatch_assum_abbrev_tac`Abbrev(fz = fp ' fx)` >>
  Q.PAT_ABBREV_TAC`fa = tyvof v "A"` >>
  `fx <: fa ∧ fp <: Funspace fa boolset` by (
    fs[is_valuation_def,is_term_valuation_def] >>
    first_assum(qspecl_then[`"P"`,`Fun A Bool`]mp_tac) >>
    first_x_assum(qspecl_then[`"x"`,`A`]mp_tac) >>
    imp_res_tac typesem_Bool >>
    simp[type_ok_def,typesem_def] >>
    imp_res_tac theory_ok_sig >>
    fs[is_std_sig_def] ) >>
  `fz <: bs` by (
    unabbrev_all_tac >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    PROVE_TAC[] ) >>
  `Abstract bs fbs fi ' fz = fi fz` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    simp[] ) >>
  rfs[] >>
  simp[Abbr`fi`] >>
  match_mp_tac apply_abstract_matchable >>
  qmatch_assum_abbrev_tac`Abbrev(fy = fp ' fm)` >>
  qmatch_assum_abbrev_tac`Abbrev(fm = fo ' fp)` >>
  `fo <: Funspace (Funspace fa bs) fa` by (
    simp[Abbr`fo`] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[holds_def] >>
    qho_match_abbrev_tac`(case ($some Q) of NONE => R | SOME a => a) <: fa` >>
    qho_match_abbrev_tac`Z ($some Q)` >>
    match_mp_tac optionTheory.some_intro >>
    unabbrev_all_tac >> simp[] >> metis_tac[] ) >>
  `fm <: fa` by (
    unabbrev_all_tac >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    PROVE_TAC[] ) >>
  `fy <: bs` by (
    unabbrev_all_tac >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    PROVE_TAC[] ) >>
  simp[Abbr`bs`,boolean_in_boolset,boolean_eq_true] >>
  simp[Abbr`fz`,Abbr`fy`] >>
  simp[GSYM holds_def] >> strip_tac >>
  simp[Abbr`fm`] >>
  qmatch_assum_abbrev_tac`Abbrev(fo = Abstract (Funspace fa boolset) fa fs)` >>
  `fo ' fp = fs fp` by (
    unabbrev_all_tac >>
    match_mp_tac (UNDISCH apply_abstract) >> simp[] >>
    rw[holds_def] >>
    qho_match_abbrev_tac`(case ($some Q) of NONE => R | SOME a => a) <: fa` >> rfs[] >>
    qho_match_abbrev_tac`Z ($some Q)` >>
    match_mp_tac optionTheory.some_intro >>
    unabbrev_all_tac >> simp[] >> metis_tac[] ) >>
  simp[Abbr`fs`] >>
  qho_match_abbrev_tac`Holds fp (case ($some Q) of NONE => R | SOME a => a)` >>
  qho_match_abbrev_tac`Z ($some Q)` >>
  match_mp_tac optionTheory.some_intro >>
  unabbrev_all_tac >> simp[] >>
  metis_tac[])

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
