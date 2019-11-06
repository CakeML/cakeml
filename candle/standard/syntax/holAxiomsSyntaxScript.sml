(*
  Context extensions for asserting the mathematical axioms.
*)
open preamble holBoolSyntaxTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = new_theory"holAxiomsSyntax"

val _ = Parse.hide "mem"

val mem = ``mem:'U->'U->bool``

Overload A[local] = ``Tyvar (implode "A")``
Overload B[local] = ``Tyvar (implode "B")``
Overload x[local] = ``Var (implode "x") A``
Overload g[local] = ``Var (implode "f") (Fun A B)``

(* ETA_AX *)
val mk_eta_ctxt_def = Define`
  mk_eta_ctxt ctxt = NewAxiom ((Abs x (Comb g x)) === g)::ctxt`

Theorem eta_extends:
   ∀ctxt. is_std_sig (sigof ctxt) ⇒ mk_eta_ctxt ctxt extends ctxt
Proof
  rw[extends_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[Once RTC_CASES1] >> rw[mk_eta_ctxt_def] >>
  rw[updates_cases,EQUATION_HAS_TYPE_BOOL,term_ok_equation] >>
  rw[term_ok_def,type_ok_def] >> fs[is_std_sig_def]
QED

Overload Select = ``λty. Const (implode "@") (Fun (Fun ty Bool) ty)``
Overload P[local] = ``Var (implode "P") (Fun A Bool)``

(* SELECT_AX *)
val mk_select_ctxt_def = Define`
  mk_select_ctxt ctxt =
    NewAxiom (Implies (Comb P x) (Comb P (Comb (Select A) P))) ::
    NewConst (implode "@") (Fun (Fun A Bool) A) ::
    ctxt`

Theorem select_extends:
   ∀ctxt. is_std_sig (sigof ctxt) ∧
           (implode "@") ∉ FDOM (tmsof ctxt) ∧
           (FLOOKUP (tmsof ctxt) (implode "==>") = SOME (Fun Bool (Fun Bool Bool)))
    ⇒ mk_select_ctxt ctxt extends ctxt
Proof
  rw[extends_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[Once RTC_CASES1] >> reverse(rw[mk_select_ctxt_def]) >- (
    rw[updates_cases,type_ok_def] >> fs[is_std_sig_def] ) >>
  rw[updates_cases,term_ok_def,type_ok_def] >- (
    rpt(simp[Once has_type_cases]) ) >>
  fs[is_std_sig_def,FLOOKUP_UPDATE]
QED

Overload B[local] = ``Tyvar (implode "B")``
Overload One_One = ``λf. Comb (Const (implode "ONE_ONE") (Fun (typeof f) Bool)) f``
Overload Onto = ``λf. Comb (Const (implode "ONTO") (Fun (typeof f) Bool)) f``
Overload Ind = ``Tyapp (implode "ind") []``

Overload EXx[local] = ``Exists (implode "x") A``
Overload x1[local] = ``Var (implode "x1") A``
Overload FAx1[local] = ``Forall (implode "x1") A``
Overload x2[local] = ``Var (implode "x2") A``
Overload FAx2[local] = ``Forall (implode "x2") A``
Overload y[local] = ``Var (implode "y") B``
Overload FAy[local] = ``Forall (implode "y") B``
Overload h[local] = ``Var (implode "f") (Fun Ind Ind)``
Overload Exh[local] = ``Exists (implode "f") (Fun Ind Ind)``

 (* INFINITY_AX *)
val mk_infinity_ctxt_def = Define`
  mk_infinity_ctxt ctxt =
    NewAxiom (Exh (And (One_One h) (Not (Onto h)))) ::
    NewType (implode "ind") 0 ::
    ConstDef (implode "ONTO") (Abs g (FAy (EXx (y === Comb g x)))) ::
    ConstDef (implode "ONE_ONE")
      (Abs g (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))) ::
    ctxt`

val tyvar_inst_exists = Q.prove(
  `∃i. ty = REV_ASSOCD (Tyvar a) i b`,
  qexists_tac`[(ty,Tyvar a)]` >>
  rw[REV_ASSOCD])

Theorem infinity_extends:
   ∀ctxt. theory_ok (thyof ctxt) ∧
           DISJOINT (FDOM (tmsof ctxt)) (IMAGE implode {"ONE_ONE";"ONTO"}) ∧
           (implode "ind") ∉ FDOM (tysof ctxt) ∧
           (FLOOKUP (tmsof ctxt) (implode "==>") = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) (implode "/\\") = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) (implode "!") = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) (implode "?") = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) (implode "~") = SOME (Fun Bool Bool))
       ⇒ mk_infinity_ctxt ctxt extends ctxt
Proof
  rw[extends_def] >>
  imp_res_tac theory_ok_sig >>
  `ALOOKUP (type_list ctxt) (implode "fun") = SOME 2` by fs[is_std_sig_def] >>
  `ALOOKUP (type_list ctxt) (implode "bool") = SOME 0` by fs[is_std_sig_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp_tac std_ss [mk_infinity_ctxt_def] >>
  Q.PAT_ABBREV_TAC`cd1 = ConstDef X Y` >>
  Q.PAT_ABBREV_TAC`cd2 = ConstDef X Y` >>
  rw[] >- (
    rw[updates_cases] >- (
      rpt(rw[Once has_type_cases])) >>
    simp[Abbr`cd1`,Abbr`cd2`] >>
    rw[term_ok_def,FLOOKUP_UPDATE,type_ok_def,tyvar_inst_exists
      ,FUNION_FEMPTY_1,FLOOKUP_FUNION] >>
    qexists_tac`[(Ind,A);(Ind,B)]` >>
    simp[REV_ASSOCD]) >>
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
      fs[Abbr`cd2`] >>
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
  PROVE_TAC[]
QED

val _ = export_theory()
