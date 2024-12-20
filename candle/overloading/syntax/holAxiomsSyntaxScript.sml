(*
  Context extensions for asserting the mathematical axioms.
*)
open preamble holBoolSyntaxTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory"holAxiomsSyntax"

val _ = Parse.hide "mem"

val mem = ``mem:'U->'U->bool``

Overload A[local] = ``Tyvar (strlit "A")``
Overload B[local] = ``Tyvar (strlit "B")``
Overload x[local] = ``Var (strlit "x") A``
Overload g[local] = ``Var (strlit "f") (Fun A B)``

(* ETA_AX *)
Definition mk_eta_ctxt_def:
  mk_eta_ctxt ctxt = NewAxiom ((Abs x (Comb g x)) === g)::ctxt
End

Theorem eta_extends:
   ∀ctxt. is_std_sig (sigof ctxt) ⇒ mk_eta_ctxt ctxt extends ctxt
Proof
  rw[extends_def] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[Once RTC_CASES1] >> rw[mk_eta_ctxt_def] >>
  rw[updates_cases,EQUATION_HAS_TYPE_BOOL,term_ok_equation] >>
  rw[term_ok_def,type_ok_def] >> fs[is_std_sig_def]
QED

Overload Select = ``λty. Const (strlit "@") (Fun (Fun ty Bool) ty)``
Overload P[local] = ``Var (strlit "P") (Fun A Bool)``

(* SELECT_AX *)
Definition mk_select_ctxt_def:
  mk_select_ctxt ctxt =
    NewAxiom (Implies (Comb P x) (Comb P (Comb (Select A) P))) ::
    NewConst (strlit "@") (Fun (Fun A Bool) A) ::
    ctxt
End

Theorem select_extends:
   ∀ctxt. is_std_sig (sigof ctxt) ∧
           (strlit "@") ∉ FDOM (tmsof ctxt) ∧
           (FLOOKUP (tmsof ctxt) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool)))
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

Overload B[local] = ``Tyvar (strlit "B")``
Overload One_One = ``λf. Comb (Const (strlit "ONE_ONE") (Fun (typeof f) Bool)) f``
Overload Onto = ``λf. Comb (Const (strlit "ONTO") (Fun (typeof f) Bool)) f``
Overload Ind = ``Tyapp (strlit "ind") []``

Overload EXx[local] = ``Exists (strlit "x") A``
Overload x1[local] = ``Var (strlit "x1") A``
Overload FAx1[local] = ``Forall (strlit "x1") A``
Overload x2[local] = ``Var (strlit "x2") A``
Overload FAx2[local] = ``Forall (strlit "x2") A``
Overload y[local] = ``Var (strlit "y") B``
Overload FAy[local] = ``Forall (strlit "y") B``
Overload h[local] = ``Var (strlit "f") (Fun Ind Ind)``
Overload Exh[local] = ``Exists (strlit "f") (Fun Ind Ind)``

 (* INFINITY_AX *)
Definition mk_infinity_ctxt_def:
  mk_infinity_ctxt ctxt =
    NewAxiom (Exh (And (One_One h) (Not (Onto h)))) ::
    NewType (strlit "ind") 0 ::
    ConstDef (strlit "ONTO") (Abs g (FAy (EXx (y === Comb g x)))) ::
    ConstDef (strlit "ONE_ONE")
      (Abs g (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))) ::
    ctxt
End

Triviality tyvar_inst_exists:
  ∃i. ty = REV_ASSOCD (Tyvar a) i b
Proof
  qexists_tac`[(ty,Tyvar a)]` >>
  rw[REV_ASSOCD]
QED

Theorem infinity_extends:
   ∀ctxt. theory_ok (thyof ctxt) ∧
           DISJOINT (FDOM (tmsof ctxt)) (IMAGE strlit {"ONE_ONE";"ONTO"}) ∧
           (strlit "ind") ∉ FDOM (tysof ctxt) ∧
           (FLOOKUP (tmsof ctxt) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) (strlit "/\\") = SOME (Fun Bool (Fun Bool Bool))) ∧
           (FLOOKUP (tmsof ctxt) (strlit "!") = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) (strlit "?") = SOME (Fun (Fun A Bool) Bool)) ∧
           (FLOOKUP (tmsof ctxt) (strlit "~") = SOME (Fun Bool Bool))
       ⇒ mk_infinity_ctxt ctxt extends ctxt
Proof
  rw[extends_def] >>
  imp_res_tac theory_ok_sig >>
  `ALOOKUP (type_list ctxt) (strlit "fun") = SOME 2` by fs[is_std_sig_def] >>
  `ALOOKUP (type_list ctxt) (strlit "bool") = SOME 0` by fs[is_std_sig_def] >>
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
