open HolKernel boolLib bossLib lcsymtacs relationTheory finite_mapTheory pred_setTheory
open holBoolSyntaxTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holAxiomsSyntax"

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
val mk_infinity_ctxt_def = Define`
  mk_infinity_ctxt ctxt =
    NewAxiom (Exh (And (One_One h) (Not (Onto h)))) ::
    NewType "ind" 0 ::
    ConstDef "ONTO" (Absg (FAy (EXx (y === Comb g x)))) ::
    ConstDef "ONE_ONE"
      (Absg (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))) ::
    ctxt`

val tyvar_inst_exists = prove(
  ``∃i. ty = REV_ASSOCD (Tyvar a) i b``,
  qexists_tac`[(ty,Tyvar a)]` >>
  rw[REV_ASSOCD])

val infinity_extends = store_thm("infinity_extends",
  ``∀ctxt. theory_ok (thyof ctxt) ∧
           DISJOINT (FDOM (tmsof ctxt)) {"ONE_ONE";"ONTO"} ∧
           "ind" ∉ FDOM (tysof ctxt) ∧
           (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) "/\\" = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) "!" = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) "?" = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) "~" = SOME (Fun Bool Bool))
       ⇒ mk_infinity_ctxt ctxt extends ctxt``,
  rw[extends_def] >>
  imp_res_tac theory_ok_sig >>
  `ALOOKUP (type_list ctxt) "fun" = SOME 2` by fs[is_std_sig_def] >>
  `ALOOKUP (type_list ctxt) "bool" = SOME 0` by fs[is_std_sig_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp_tac std_ss [mk_infinity_ctxt_def] >>
  Q.PAT_ABBREV_TAC`cd1 = ConstDef X Y` >>
  Q.PAT_ABBREV_TAC`cd2 = ConstDef X Y` >>
  rw[] >- (
    rw[updates_cases] >- (
      rpt(rw[Once has_type_cases])) >>
    simp[Abbr`cd1`,Abbr`cd2`] >>
    rw[term_ok_def,FLOOKUP_UPDATE,type_ok_def,tyvar_inst_exists
      ,FUNION_FEMPTY_1,FLOOKUP_FUNION]) >>
  rw[Once RTC_CASES1] >- rw[Abbr`cd1`,Abbr`cd2`,updates_cases] >>
  simp[Once RTC_CASES1] >>
  conj_asm2_tac >- (
    qunabbrev_tac`cd1` >>
    match_mp_tac ConstDef_updates >>
    full_simp_tac bool_ss [GSYM extends_def] >>
    imp_res_tac extends_theory_ok >>
    conj_tac >- rw[] >>
    conj_tac >- (
      match_mp_tac term_ok_extend >>
      map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
      qpat_assum`DISJOINT X Y`mp_tac >>
      simp[Abbr`cd2`,IN_DISJOINT] >>
      strip_tac >> conj_tac >- PROVE_TAC[] >>
      fs[] >>
      simp[term_ok_def,type_ok_def,tyvar_inst_exists,welltyped_equation
          ,EQUATION_HAS_TYPE_BOOL,typeof_equation,term_ok_equation] ) >>
    conj_tac >- (fs[Abbr`cd2`,IN_DISJOINT] >> PROVE_TAC[] ) >>
    simp[CLOSED_def,tvars_def,tyvars_def,equation_def] >>
    PROVE_TAC[] ) >>
  simp[Once RTC_CASES1] >>
  qunabbrev_tac`cd2` >>
  match_mp_tac ConstDef_updates >>
  full_simp_tac bool_ss [GSYM extends_def] >>
  imp_res_tac extends_theory_ok >>
  fs[IN_DISJOINT] >>
  simp[CLOSED_def,tvars_def,tyvars_def] >>
  simp[term_ok_def,type_ok_def,welltyped_equation,EQUATION_HAS_TYPE_BOOL
      ,typeof_equation,term_ok_equation] >>
  simp[equation_def,tvars_def,tyvars_def] >>
  PROVE_TAC[])

val _ = export_theory()
