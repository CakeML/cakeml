open HolKernel Parse boolLib bossLib lcsymtacs;

val _ = new_theory "holSemantics";

open holSyntaxTheory;
open sholSyntaxTheory;
open sholSemanticsTheory;
open listTheory arithmeticTheory combinTheory pairTheory;

(*

   This script defines the semantics of stateful HOL in terms of the
   semantics of the stateless HOL. This file has three parts:

    (1) a translation from stateful types, terms, sequents to
        stateless types, terms and sequents is define as a relation,

    (2) the semantics of stateful sequents is define in using the
        translation relation from above, and

    (3) finally, we prove that for any derivation in the stateful
        version there is a derivation in the stateless version for
        the appropriate translation of the sequent.

   Parts (2) and (3) imply soundness of stateful HOL, if soundness has
   been proved for the stateless version.

*)

infix \\
val op \\ = op THEN;

(* -- part 1 -- *)

val const_def_def = Define `
  const_def n defs =
    case defs of
    | [] => NONE
    | (Constdef name tm::defs) =>
         if n = name then SOME (0,tm) else const_def n defs
    | (Typedef name tm abs rep::defs) =>
         if n = abs then SOME (1,tm) else
         if n = rep then SOME (2,tm) else const_def n defs
    | d::defs => const_def n defs`

val type_def_def = Define `
  type_def n defs =
    case defs of
    | [] => NONE
    | (Typedef name tm x y::defs) =>
         if n = name then SOME (tm,x,y) else type_def n defs
    | d::defs => type_def n defs`;

val (term_rules,term_ind,term_cases) = xHol_reln "term" `
  (type defs (Tyvar s) (Tyvar s)) /\
  (type defs Bool (Tyapp (Typrim "bool" 0) [])) /\
  (type defs Ind (Tyapp (Typrim "ind" 0) [])) /\
  (type defs tx tx1 /\ type defs ty ty1 ==>
   type defs (Fun tx ty) (Tyapp (Typrim "fun" 2) [tx1; ty1])) /\
  (EVERY2 (type defs) tys tys1 /\
   (type_def s defs = SOME (tm,abs,rep)) /\ term defs tm tm1 ==>
   type defs (Tyapp s tys) (Tyapp (Tydefined s tm1) tys1)) /\
  (type defs ty ty1 ==>
   term defs (Var s ty) (Var s ty1)) /\
  (type defs (Fun ty (Fun ty Bool)) ty1 ==>
   term defs (Equal ty) (Const "=" ty1 Prim)) /\
  (type defs (Fun (Fun ty Bool) ty) ty1 ==>
   term defs (Select ty) (Const "@" ty1 Prim)) /\
  (term defs x x1 /\ term defs y y1 ==>
   term defs (Comb x y) (Comb x1 y1)) /\
  (type defs ty ty1 /\ term defs x x1 ==>
   term defs (Abs s ty x) (Abs s ty1 x1)) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (n,tm)) /\ term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (if n = 0 then Defined tm1 else
                                        if n = 1 then Tyabs s tm1 else
                                     (* if n = 2 then *) Tyrep s tm1)))`

val seq_trans_def = Define `
  seq_trans ((defs,h),c) (h1,c1) <=>
    EVERY2 (term defs) h h1 /\ term defs c c1`;


(* -- part 2 -- *)

val hol_seq_def = Define `
  hol_seq ((defs,hyps),tm) = ?h c. seq_trans ((defs,hyps),tm) (h,c) /\ h |= c`;


(* -- part 3 -- *)

val _ = Parse.overload_on("α",``(Tyvar "a"):sholSyntax$type``)
val id_stm = ``Abs "x" α (Var "x" α)``
val id_ok = prove(
  ``term_ok ^id_stm``,
  simp[Once proves_cases] >>
  disj1_tac >>
  simp[Once proves_cases] >>
  simp[Once proves_cases] >>
  disj1_tac >>
  simp[Once proves_cases] )
val _ = Parse.overload_on("Ts",``^id_stm === ^id_stm``)
val truth_sthm =
   proves_rules
|> CONJUNCTS
|> C (curry List.nth) 14
|> SPEC id_stm
|> UNDISCH
|> PROVE_HYP id_ok

val Ts_ok = save_thm("Ts_ok",
   proves_rules
|> CONJUNCTS
|> C (curry List.nth) 13
|> SPEC ``Ts``
|> Q.SPEC `[]`
|> SIMP_RULE (srw_ss())[truth_sthm])
val _ = export_rewrites["Ts_ok"]

val Ts_has_type_Bool = prove(
  ``Ts has_type Bool``,
  simp[EQUATION_HAS_TYPE_BOOL])

val _ = Parse.overload_on("Arb",``λty. Comb (Select ty) (Abs "x" ty Ts)``)

val Arb_ok = prove(
  ``∀ty. type_ok ty ⇒ term_ok (Arb ty)``,
  rw[] >>
  simp[Once proves_cases] >>
  disj1_tac >>
  conj_tac >- simp[Once proves_cases] >>
  conj_tac >- simp[Once proves_cases] >>
  METIS_TAC[Ts_has_type_Bool,welltyped_def,WELLTYPED_LEMMA])

val term_type_11 = prove(
  ``(!ty ty1. type defs ty ty1 ==> !ty2. type defs ty ty2 ==> (ty1 = ty2)) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀tm2. term defs tm tm2 ⇒ (tm1 = tm2))``,
  HO_MATCH_MP_TAC term_ind >>
  rpt conj_tac >> rpt gen_tac
  >- simp[Once term_cases]
  >- simp[Once term_cases]
  >- simp[Once term_cases]
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- (strip_tac >> simp[Once term_cases] >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rw[LIST_EQ_REWRITE] >> rfs[MEM_ZIP] >>
      METIS_TAC[] )
  >> (strip_tac >> simp[Once term_cases] >> METIS_TAC[]))

val has_type_IMP = prove(
  ``∀tm ty. tm has_type ty ⇒ ∀defs tm1. term defs tm tm1 ⇒ ∃ty1. type defs ty ty1 ∧ tm1 has_type ty1``,
  HO_MATCH_MP_TAC holSyntaxTheory.has_type_strongind >> rw[] >>
  TRY (
    qpat_assum`term defs (Comb X Y) Z`mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
    METIS_TAC[term_type_11] ) >>
  TRY (
    qpat_assum`term defs (Abs X Y A) Z`mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    rw[Once term_cases] >>
    METIS_TAC[term_type_11] ) >>
  (
    last_x_assum mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    METIS_TAC[term_type_11] ))

val proves_IMP = store_thm("proves_IMP",
  ``(∀defs ty. type_ok defs ty ⇒ ∃ty1. type defs ty ty1 ∧ type_ok ty1) ∧
    (∀defs tm. term_ok defs tm ⇒ ∃tm1. term defs tm tm1 ∧ term_ok tm1) ∧
    (∀defs. context_ok defs ⇒ T) ∧
    (∀dh c. dh |- c ⇒ ∃h1 c1. seq_trans (dh,c) (h1,c1) ∧ h1 |- c1)``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_strongind >>
  conj_tac >- simp[Once term_cases,Once proves_cases] >>
  conj_tac >- simp[Once term_cases,Once proves_cases] >>
  conj_tac >- simp[Once term_cases,Once proves_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once term_cases] >> rw[] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once proves_cases] >>
    METIS_TAC[]) >>
  conj_tac >- (
    rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[has_type_IMP] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once CONJ_COMM] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once CONJ_COMM] >>
    simp[Once term_cases] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once CONJ_COMM] >>
    simp[Once term_cases] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once proves_cases] >>
    fs[welltyped_def,holSyntaxTheory.welltyped_def] >>
    map_every qexists_tac[`tm1`,`tm1'`] >> rw[] >>
    disj1_tac >>
    conj_tac >- METIS_TAC[has_type_IMP] >>
    conj_tac >- METIS_TAC[has_type_IMP] >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >> fs[] >> rw[] >>
    imp_res_tac has_type_IMP >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    IMP_RES_TAC WELLTYPED_LEMMA >> rw[] >>
    METIS_TAC[term_type_11] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >> rw[] >>
    qexists_tac`x1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >> rw[] >>
    qexists_tac`y1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >> rw[] >>
    qexists_tac`x1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[seq_trans_def,EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,13),MEM,MEM_EL] ) >>
  conj_tac >- rw[] >>
  conj_tac >- rw[seq_trans_def] >>
  conj_tac >- (
    rw[seq_trans_def] >>
    (* derive term for equations *)
    cheat ) >>
  cheat)

val _ = export_theory();
