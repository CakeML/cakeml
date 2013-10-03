open HolKernel Parse boolLib bossLib lcsymtacs miscTheory miscLib;

val _ = new_theory "holSemantics";

open holSyntaxTheory;
open sholSyntaxTheory;
open sholSyntaxExtraTheory;
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
  (term defs x x1 /\ term defs y y1 /\ welltyped (Comb x y) ==>
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

val term_type_11_inv = prove(
  ``(!ty ty1. type defs ty ty1 ==> !ty2. type defs ty2 ty1 ==> (ty = ty2)) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀tm2. term defs tm2 tm1 ⇒ (tm = tm2))``,
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
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- (
    strip_tac >>
    simp[Once term_cases] >>
    rw[] >- ( res_tac >> fs[] ) >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[ARITH_ss][] )
  >- (
    strip_tac >>
    simp[Once term_cases] >>
    rw[] >- ( res_tac >> fs[] ) >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[ARITH_ss][] )
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- ( strip_tac >> simp[Once term_cases] >> rw[] ))

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

val term_equation = prove(
  ``!x y z. (x === y) has_type Bool ⇒
    (term defs (x === y) z ⇔ ∃x1 y1. (z = x1 === y1) ∧ term defs x x1 ∧ term defs y y1)``,
  rpt gen_tac >> strip_tac >>
  simp[equation_def,holSyntaxTheory.equation_def] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >>
  fs[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
  rw[EQ_IMP_THM] >>
  METIS_TAC[term_type_11,has_type_IMP,holSyntaxTheory.WELLTYPED,WELLTYPED_LEMMA])

val term_welltyped = prove(
  ``(∀ty ty1. type defs ty ty1 ⇒ T) ∧
    (∀tm tm1. term defs tm tm1 ⇒ (welltyped tm ⇔ welltyped tm1))``,
  HO_MATCH_MP_TAC (theorem"term_strongind") >>
  simp[] >> rw[] >>
  rw[EQ_IMP_THM] >> fs[] >>
  fs[WELLTYPED,holSyntaxTheory.WELLTYPED] >>
  imp_res_tac has_type_IMP >>
  fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
  METIS_TAC[has_type_IMP,term_type_11,WELLTYPED_LEMMA,holSyntaxTheory.WELLTYPED_LEMMA])

val welltyped_equation = prove(
  ``holSyntax$welltyped (s === t) ⇔ (s === t) has_type Bool``,
  rw[holSyntaxTheory.equation_def] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  METIS_TAC[holSyntaxTheory.WELLTYPED,holSyntaxTheory.WELLTYPED_LEMMA])

val ALPHAVARS_IMP = prove(
  ``∀env tp. holSyntax$ALPHAVARS env tp ⇒
      ∀defs tp1 env1.
        LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
        LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
        sholSyntax$ALPHAVARS env1 tp1``,
  Induct >> simp[ALPHAVARS_def,holSyntaxTheory.ALPHAVARS_def] >- (
    Cases >> simp[] >> metis_tac[term_type_11] ) >>
  rw[] >>
  imp_res_tac term_type_11 >> rw[] >- (
    Cases_on`env1`>>fs[ALPHAVARS_def]>>
    metis_tac[PAIR_EQ,pair_CASES,FST,SND] ) >>
  Cases_on`env1`>>fs[ALPHAVARS_def]>>
  Cases_on`tp1=h'`>>fs[]>>
  rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- metis_tac[term_type_11_inv] >>
  conj_tac >- metis_tac[term_type_11_inv] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  map_every qexists_tac[`tp`,`defs`] >>
  simp[])

val RACONV_IMP = prove(
  ``∀env tp. RACONV env tp ⇒
    ∀defs tp1 env1.
      LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
      LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
      RACONV env1 tp1``,
   HO_MATCH_MP_TAC holSyntaxTheory.RACONV_ind >>
   simp[] >> rw[] >>
   Cases_on`tp1` >>
   fs[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Select X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Equal X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[RACONV] >> fsrw_tac[ARITH_ss][] >>
   TRY (match_mp_tac(MP_CANON(CONJUNCT1 term_type_11)) >> metis_tac[]) >>
   TRY (match_mp_tac(MP_CANON(CONJUNCT2 term_type_11)) >> metis_tac[]) >>
   TRY (first_x_assum match_mp_tac >> simp[] >> metis_tac[]) >>
   TRY (last_x_assum match_mp_tac >> simp[] >> metis_tac[]) >>
   TRY (
     match_mp_tac (MP_CANON ALPHAVARS_IMP) >>
     qexists_tac`env` >>
     qexists_tac`Var x1 ty1,Var x2 ty2` >>
     qexists_tac`defs` >>
     simp[] >>
     simp[Once term_cases] >>
     simp[Once term_cases] ) >>
   fs[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[RACONV] >- metis_tac[term_type_11] >>
   first_x_assum match_mp_tac >> simp[] >>
   qexists_tac`defs` >> simp[])

val ALPHAVARS_IMP_inv = prove(
  ``∀env1 tp1. sholSyntax$ALPHAVARS env1 tp1 ⇒
      ∀defs tp env.
        LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
        LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
        holSyntax$ALPHAVARS env tp``,
  Induct >> simp[ALPHAVARS_def,holSyntaxTheory.ALPHAVARS_def] >- (
    Cases >> simp[] >> metis_tac[term_type_11_inv] ) >>
  rw[] >>
  imp_res_tac term_type_11_inv >> rw[] >- (
    Cases_on`env`>>fs[holSyntaxTheory.ALPHAVARS_def]>>
    metis_tac[PAIR_EQ,pair_CASES,FST,SND] ) >>
  Cases_on`env`>>fs[holSyntaxTheory.ALPHAVARS_def]>>
  Cases_on`tp=h'`>>fs[]>>
  rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- metis_tac[term_type_11] >>
  conj_tac >- metis_tac[term_type_11] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  map_every qexists_tac[`tp1`,`defs`] >>
  simp[])

val RACONV_IMP_inv = prove(
  ``∀env1 tp1. RACONV env1 tp1 ⇒
    ∀defs tp env.
      LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
      LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
      RACONV env tp``,
   HO_MATCH_MP_TAC RACONV_ind >>
   simp[] >> rw[] >>
   Cases_on`tp` >>
   fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPECL[`A`,`Const X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPECL[`A`,`Comb X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[holSyntaxTheory.RACONV] >> fsrw_tac[ARITH_ss][] >>
   TRY (imp_res_tac term_type_11_inv >> fs[] >> NO_TAC) >>
   TRY (last_x_assum mp_tac >> rw[] >> fsrw_tac[ARITH_ss][]) >>
   TRY (first_x_assum match_mp_tac >> simp[] >> metis_tac[]) >>
   TRY (last_x_assum match_mp_tac >> simp[] >> metis_tac[]) >>
   TRY (
     match_mp_tac (MP_CANON ALPHAVARS_IMP_inv) >>
     qexists_tac`env1` >>
     qexists_tac`Var x1 ty1,Var x2 ty2` >>
     qexists_tac`defs` >>
     simp[] >>
     simp[Once term_cases] >>
     simp[Once term_cases] ) >>
   fs[Q.SPECL[`A`,`Abs X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[holSyntaxTheory.RACONV] >- metis_tac[term_type_11_inv] >>
   first_x_assum match_mp_tac >> simp[] >>
   qexists_tac`defs` >> simp[])

val ACONV_IMP = prove(
  ``∀defs t1 t2 t11 t22. ACONV t1 t2 ∧ term defs t1 t11 ∧ term defs t2 t22 ⇒ ACONV t11 t22``,
  rw[ACONV_def,holSyntaxTheory.ACONV_def] >>
  match_mp_tac (MP_CANON RACONV_IMP) >>
  simp[EXISTS_PROD] >>
  metis_tac[])

val ACONV_IMP_inv = prove(
  ``∀defs t1 t2 t11 t22. ACONV t11 t22 ∧ term defs t1 t11 ∧ term defs t2 t22 ⇒ ACONV t1 t2``,
  rw[ACONV_def,holSyntaxTheory.ACONV_def] >>
  match_mp_tac (MP_CANON RACONV_IMP_inv) >>
  simp[EXISTS_PROD] >>
  metis_tac[])

val LIST_REL_term_UNION = prove(
  ``∀defs l1 l2 r1 r2. LIST_REL (term defs) l1 r1 ∧ LIST_REL (term defs) l2 r2 ⇒
      LIST_REL (term defs) (TERM_UNION l1 l2) (TERM_UNION r1 r2)``,
  gen_tac >> Induct >> simp[TERM_UNION_def,holSyntaxTheory.TERM_UNION_def] >>
  rw[] >> simp[TERM_UNION_def] >> rw[] >>
  fs[EVERY2_EVERY,EXISTS_MEM,EVERY_MEM] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >- (
    imp_res_tac holSyntaxTheory.TERM_UNION_NONEW >>
    metis_tac[TERM_UNION_THM,MEM_EL,ACONV_SYM,ACONV_TRANS,ACONV_IMP] ) >>
  imp_res_tac TERM_UNION_NONEW >>
  METIS_TAC[holSyntaxTheory.TERM_UNION_THM,MEM_EL,ACONV_IMP_inv,holSyntaxTheory.ACONV_SYM,holSyntaxTheory.ACONV_TRANS])

val VFREE_IN_IMP = prove(
  ``!t2 t1 defs s2 s1. VFREE_IN t1 t2 ∧ term defs t1 s1 ∧ term defs t2 s2 ⇒ VFREE_IN s1 s2``,
  Induct >> simp[] >>
  fs[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Select X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Equal X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >> rw[holSyntaxTheory.VFREE_IN_def] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  imp_res_tac term_type_11 >> fs[] >> rw[]
  >- METIS_TAC[] >- METIS_TAC[]
  >- (
    spose_not_then strip_assume_tac >> rw[] >>
    fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    rw[] >> METIS_TAC[term_type_11_inv] ) >>
  METIS_TAC[])

val VFREE_IN_IMP_inv = prove(
  ``!s2 s1 defs t2 t1. VFREE_IN s1 s2 ∧ term defs t1 s1 ∧ term defs t2 s2 ⇒ VFREE_IN t1 t2``,
  Induct >> simp[] >>
  fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPECL[`A`,`Const X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPECL[`A`,`Comb X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >> rw[holSyntaxTheory.VFREE_IN_def] >>
  last_x_assum mp_tac >> rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  imp_res_tac term_type_11_inv >> fs[]
  >- METIS_TAC[] >- METIS_TAC[] >>
  fs[Q.SPECL[`A`,`Abs X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >- (
    spose_not_then strip_assume_tac >> rw[] >>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    rw[] >> METIS_TAC[term_type_11] ) >>
  METIS_TAC[])

val LIST_REL_term_FILTER_ACONV = prove(
  ``∀asl1 h1 c c1.
    LIST_REL (term defs) asl1 h1 ∧ term defs c c1
    ⇒
    LIST_REL (term defs) (FILTER ($~ o ACONV c) asl1)
    (FILTER ($~ o ACONV c1) h1)``,
  Induct >> simp[] >>
  rw[] >> rw[] >>
  METIS_TAC[ACONV_IMP,ACONV_IMP_inv])

(*
val safe_def_def = Define`
  (safe_def defs (Constdef n t) ⇔ n ∉ set (MAP FST (consts defs))) ∧
  (safe_def defs (Typedef n t a r) ⇔
    n ∉ set (MAP FST (types defs)) ∧
    a ∉ set (MAP FST (consts defs)) ∧
    r ∉ set (MAP FST (consts defs)))`

val proves_cons = prove(
  ``(∀defs ty. type_ok defs ty ⇒ ∀d. safe_def defs d ⇒ type_ok (d::defs) ty) ∧
    (∀defs tm. term_ok defs tm ⇒ ∀d. safe_def defs d ⇒ term_ok (d::defs) tm) ∧
    (∀defs. context_ok defs ⇒ ∀d. safe_def defs d ⇒ context_ok (d::defs)) ∧
    (∀dh c. dh |- c ⇒ ∀d. safe_def (FST dh) d ⇒ (d::(FST dh),SND dh) |- c)``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_ind >>
  conj_tac >- simp[Once holSyntaxTheory.proves_cases] >>
  conj_tac >- simp[Once holSyntaxTheory.proves_cases] >>
  conj_tac >- simp[Once holSyntaxTheory.proves_cases] >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once holSyntaxTheory.proves_cases] >>
    METIS_TAC[]) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> simp[Once holSyntaxTheory.proves_cases] >> METIS_TAC[]) >>
  conj_tac >- (
    rw[] >>
    simp[Once holSyntaxTheory.proves_cases] >>
    Cases_on`d`
*)

val safe_def_names_def = Define`
  (safe_def_names defs (Constdef n t) ⇔ n ∉ set (MAP FST (consts defs))) ∧
  (safe_def_names defs (Typedef n t a r) ⇔
    n ∉ set (MAP FST (types defs)) ∧
    a ∉ set (MAP FST (consts defs)) ∧
    r ∉ set (MAP FST (consts defs)))`

val type_def_MEM = prove(
  ``∀defs n tm x y. type_def n defs = SOME (tm,x,y) ⇒ MEM (Typedef n tm x y) defs``,
  Induct >> simp[Once type_def_def] >>
  Cases >> simp[] >> rw[])

val const_def_MEM_0 = prove(
  ``∀defs n tm. const_def n defs = SOME (0,tm) ⇒ MEM (Constdef n tm) defs``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[])

val const_def_MEM_1 = prove(
  ``∀defs n tm. const_def n defs = SOME (1,tm) ⇒ ∃x y z. MEM (Typedef x y n z) defs``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[] >> METIS_TAC[])

val const_def_MEM_2 = prove(
  ``∀defs n m tm. const_def n defs = SOME (m,tm) ∧ m ≠ 0 ∧ m ≠ 1 ⇒ ∃x y z. MEM (Typedef x y z n) defs``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[] >> METIS_TAC[])

val MEM_Typedef_MEM_types = prove(
  ``∀defs n tm a r. MEM (Typedef n tm a r) defs ⇒ MEM n (MAP FST (types defs))``,
  Induct >> simp[] >>
  rw[types_def,types_aux_def] >>
  rw[types_def,types_aux_def] >>
  fs[types_def] >>
  METIS_TAC[])

val MEM_Typedef_MEM_consts = prove(
  ``∀defs n tm a r. MEM (Typedef n tm a r) defs ⇒ MEM a (MAP FST (consts defs)) ∧ MEM r (MAP FST (consts defs))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  METIS_TAC[])

val MEM_Constdef_MEM_consts = prove(
  ``∀defs n tm. MEM (Constdef n tm) defs ⇒ MEM n (MAP FST (consts defs))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  METIS_TAC[])

val term_type_cons = prove(
  ``(∀ty ty1. type defs ty ty1 ⇒ ∀d. safe_def_names defs d ⇒ type (d::defs) ty ty1) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀d. safe_def_names defs d ⇒ term (d::defs) tm tm1)``,
  HO_MATCH_MP_TAC term_ind >> rw[] >>
  simp[Once term_cases] >- (
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[type_def_def] >>
    BasicProvers.CASE_TAC >- METIS_TAC[] >>
    fs[safe_def_names_def] >>
    imp_res_tac type_def_MEM >>
    rw[] >- METIS_TAC[MEM_Typedef_MEM_types] >>
    first_x_assum match_mp_tac >>
    rw[safe_def_names_def] )
  >- (
    qexists_tac`0` >> rw[] >>
    qexists_tac`tm` >>
    reverse conj_tac >- METIS_TAC[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >>
    imp_res_tac const_def_MEM_0 >>
    imp_res_tac MEM_Constdef_MEM_consts >>
    fs[safe_def_names_def] >>
    rw[] >> fs[] )
  >- (
    qexists_tac`1` >> rw[] >>
    imp_res_tac const_def_MEM_1 >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    qexists_tac`tm` >>
    reverse conj_tac >- METIS_TAC[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >>
    fs[safe_def_names_def] )
  >- (
    qexists_tac`n` >> rw[] >>
    imp_res_tac const_def_MEM_2 >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    qexists_tac`tm` >>
    reverse conj_tac >- METIS_TAC[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >> fs[safe_def_names_def] ))

val def_ok_def = Define`
  def_ok defs (Constdef n t) = term_ok defs t ∧
  def_ok defs (Typedef n t a r) = term_ok defs t`

val proves_ok = prove(
  ``(∀defs ty. type_ok defs ty ⇒ T) ∧
    (∀defs tm. term_ok defs tm ⇒ T) ∧
    (∀defs. context_ok defs ⇒ EVERY (def_ok defs) defs) ∧
    (∀dh c. dh |- c ⇒ EVERY (term_ok (FST dh)) (c::SND dh) ∧ context_ok (FST dh) ∧ EVERY (def_ok (FST dh)) (FST dh))``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_strongind >>
  simp[] >>
  conj_tac >- (
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >> simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,16)) >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`TERM_UNION asl1 asl2` >>
    qexists_tac`l === r` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,17)) >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`TERM_UNION asl1 asl2` >>
    qexists_tac`Comb l1 l2 === Comb r1 r2` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,18)) >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`asl` >>
    qexists_tac`Abs x ty l === Abs x ty r` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,19)) >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,20)) >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`TERM_UNION asl1 asl2` >>
    qexists_tac`c` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,22)) >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qmatch_abbrev_tac`term_ok defs X ∧ EVERY (term_ok defs) hh` >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`hh` >>
    qexists_tac`X` >>
    simp[] >>
    qunabbrev_tac`hh` >>
    qunabbrev_tac`X` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,23)) >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qmatch_abbrev_tac`term_ok defs X ∧ EVERY (term_ok defs) hh` >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`hh` >>
    qexists_tac`X` >>
    simp[] >>
    qunabbrev_tac`hh` >>
    qunabbrev_tac`X` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
    simp[] >>
    METIS_TAC[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qmatch_abbrev_tac`term_ok defs X ∧ EVERY (term_ok defs) hh` >>
    rw[EVERY_MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`hh` >>
    qexists_tac`X` >>
    simp[] >>
    qunabbrev_tac`hh` >>
    qunabbrev_tac`X` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
    simp[] >>
    METIS_TAC[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[EVERY_MEM] >>
    TRY (
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      qexists_tac`asl` >>
      qexists_tac`c` >>
      simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
      simp[] ) >>
    TRY (
      simp[def_ok_def] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,11)) >>
      qexists_tac`Comb (Equal (typeof (Const s (typeof tm)))) (Const s (typeof tm))` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      qexists_tac`[]` >>
      simp_tac std_ss [MEM] >>
      simp[GSYM holSyntaxTheory.equation_def] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,27)) >>
      simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,15)) >>
      qexists_tac`asl` >> qexists_tac`c` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
      simp[] ) >>
    TRY (
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,15)) >>
      qexists_tac`asl` >>
      qexists_tac`c` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
      simp[] ) >>
    qsuff_tac`∀t. term_ok defs t ⇒ term_ok (Constdef s tm::defs) t` >- (
      rw[] >>
      Cases_on`e`>>simp[def_ok_def] >>
      first_x_assum match_mp_tac >>
      fs[EVERY_MEM] >>
      res_tac >> fs[def_ok_def] ) >>
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,11)) >>
    qexists_tac`Comb (Equal (typeof t)) t` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >>
    simp_tac std_ss [MEM] >>
    simp[GSYM holSyntaxTheory.equation_def] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,16)) >>
    simp[] ) >>
  conj_tac >- (
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >> simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,27)) >>
    simp[] ) >>
  rpt gen_tac >> strip_tac >- (
    rw[EVERY_MEM] >>
    TRY (
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      qexists_tac`asl` >>
      qexists_tac`c` >>
      simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
      simp[] >>
      METIS_TAC[]) >>
    TRY (
      simp[def_ok_def] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,10)) >>
      qexists_tac`y` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      qexists_tac`[]` >>
      simp_tac std_ss [MEM] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
      simp[] >>
      METIS_TAC[]) >>
    TRY (
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,15)) >>
      qexists_tac`asl` >>
      qexists_tac`c` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
      simp[] >>
      METIS_TAC[]) >>
    qsuff_tac`∀x. term_ok defs x ⇒ term_ok (Typedef tyname t a r::defs) x` >- (
      rw[] >>
      Cases_on`e`>>simp[def_ok_def] >>
      first_x_assum match_mp_tac >>
      fs[EVERY_MEM] >>
      res_tac >> fs[def_ok_def] ) >>
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,11)) >>
    qexists_tac`Comb (Equal (typeof x)) x` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >>
    simp_tac std_ss [MEM] >>
    simp[GSYM holSyntaxTheory.equation_def] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
    simp[] >>
    metis_tac[List.nth(CONJUNCTS holSyntaxTheory.proves_rules,16)]) >>
  rw[EVERY_MEM] >>
  TRY (
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
    simp[] >>
    METIS_TAC[]) >>
  TRY (
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,15)) >>
    qexists_tac`[]` >>
    qexists_tac`Comb t y` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
    simp[] >>
    METIS_TAC[]) >>
  TRY (
    simp[def_ok_def] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,10)) >>
    qexists_tac`y` >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
    qexists_tac`[]` >>
    simp_tac std_ss [MEM] >>
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
    simp[] >>
    METIS_TAC[]) >>
  (qsuff_tac`∀x. term_ok defs x ⇒ term_ok (Typedef tyname t a r::defs) x` >- (
    rw[] >>
    Cases_on`e`>>simp[def_ok_def] >>
    first_x_assum match_mp_tac >>
    fs[EVERY_MEM] >>
    res_tac >> fs[def_ok_def] )) >>
  rw[] >>
  match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,11)) >>
  qexists_tac`Comb (Equal (typeof x)) x` >>
  match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
  qexists_tac`[]` >>
  simp_tac std_ss [MEM] >>
  simp[GSYM holSyntaxTheory.equation_def] >>
  match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,28)) >>
  simp[] >>
  metis_tac[List.nth(CONJUNCTS holSyntaxTheory.proves_rules,16)])

val REV_ASSOCD_ilist_IMP = prove(
  ``∀ilist defs t ilist1 t1 d d1.
      LIST_REL (term defs) (MAP FST ilist) (MAP FST ilist1) ∧
      LIST_REL (term defs) (MAP SND ilist) (MAP SND ilist1) ∧
      term defs t t1 ∧
      term defs d d1
      ⇒
      term defs (holSyntax$REV_ASSOCD t ilist d) (sholSyntax$REV_ASSOCD t1 ilist1 d1)``,
  Induct >> simp[holSyntaxTheory.REV_ASSOCD,REV_ASSOCD] >>
  Cases >> simp[holSyntaxTheory.REV_ASSOCD,REV_ASSOCD] >>
  rw[] >- (
    imp_res_tac term_type_11 >> rw[] >>
    Cases_on`ilist1`>>fs[]>>
    Cases_on`h`>>fs[]>>rw[]>>
    simp[REV_ASSOCD] ) >>
  Cases_on`ilist1`>>fs[]>>
  Cases_on`h`>>fs[]>>rw[]>>
  simp[REV_ASSOCD] >>
  imp_res_tac term_type_11 >> rw[] >>
  imp_res_tac term_type_11_inv)

val REV_ASSOCD_tyin_IMP = prove(
  ``∀tyin defs t tyin1 t1 d d1.
      LIST_REL (type defs) (MAP FST tyin) (MAP FST tyin1) ∧
      LIST_REL (type defs) (MAP SND tyin) (MAP SND tyin1) ∧
      type defs t t1 ∧
      type defs d d1
      ⇒
      type defs (holSyntax$REV_ASSOCD t tyin d) (sholSyntax$REV_ASSOCD t1 tyin1 d1)``,
  Induct >> simp[holSyntaxTheory.REV_ASSOCD,REV_ASSOCD] >>
  Cases >> simp[holSyntaxTheory.REV_ASSOCD,REV_ASSOCD] >>
  rw[] >- (
    imp_res_tac term_type_11 >> rw[] >>
    Cases_on`tyin1`>>fs[]>>
    Cases_on`h`>>fs[]>>rw[]>>
    simp[REV_ASSOCD] ) >>
  Cases_on`tyin1`>>fs[]>>
  Cases_on`h`>>fs[]>>rw[]>>
  simp[REV_ASSOCD] >>
  imp_res_tac term_type_11 >> rw[] >>
  imp_res_tac term_type_11_inv)

val VARIANT_IMP = prove(
  ``∀tm tm1 defs s ty ty1.
      term defs tm tm1 ∧
      type defs ty ty1
      ⇒
      VARIANT tm s ty = VARIANT tm1 s ty1``,
  rw[VARIANT_def,holSyntaxTheory.VARIANT_def] >>
  simp[LIST_EQ_REWRITE] >>
  conj_asm1_tac >- (
    qmatch_abbrev_tac`a = b` >>
    Cases_on`a < b` >- (
      fs[Abbr`b`] >>
      imp_res_tac VARIANT_PRIMES_def >>
      imp_res_tac VFREE_IN_IMP_inv >>
      fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
      fsrw_tac[boolSimps.DNF_ss][] >>
      METIS_TAC[holSyntaxTheory.VARIANT_PRIMES_def] ) >>
    Cases_on`b < a` >- (
      fs[Abbr`a`] >>
      imp_res_tac holSyntaxTheory.VARIANT_PRIMES_def >>
      imp_res_tac VFREE_IN_IMP >>
      fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
      fsrw_tac[boolSimps.DNF_ss][] >>
      METIS_TAC[VARIANT_PRIMES_def] ) >>
    DECIDE_TAC ) >>
  simp[])

val LIST_REL_MAP_FILTER_NEQ = store_thm("LIST_REL_MAP_FILTER_NEQ",
  ``∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))``,
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND])

val tac =
    match_mp_tac LIST_REL_MAP_FILTER_NEQ >>
    simp[] >>
    fs[EVERY2_EVERY] >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    unabbrev_all_tac >>
    fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[EQ_IMP_THM] >>
    rpt (first_x_assum(qspec_then`n`mp_tac)) >> rw[] >>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    METIS_TAC[term_type_11,term_type_11_inv]

val VSUBST_IMP = prove(
  ``∀tm ilist defs ilist1 tm1.
      term defs tm tm1 ∧
      LIST_REL (term defs) (MAP FST ilist) (MAP FST ilist1) ∧
      LIST_REL (term defs) (MAP SND ilist) (MAP SND ilist1) ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ∧
      (∀s s'. MEM (s',s) ilist1 ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      term defs (VSUBST ilist tm) (VSUBST ilist1 tm1)``,
  Induct >- (
    simp[Once term_cases] >> rw[] >>
    simp[holSyntaxTheory.VSUBST_def,VSUBST_def] >>
    match_mp_tac REV_ASSOCD_ilist_IMP >>
    simp[Once term_cases] )
  >- (
    simp[Once term_cases] >> rw[] >>
    simp[VSUBST_def,holSyntaxTheory.VSUBST_def] >>
    simp[Once term_cases] >>
    rw[] )
  >- (
    simp[Once term_cases] >> rw[] >>
    simp[VSUBST_def,holSyntaxTheory.VSUBST_def] >>
    simp[Once term_cases] )
  >- (
    simp[Once term_cases] >> rw[] >>
    simp[VSUBST_def,holSyntaxTheory.VSUBST_def] >>
    simp[Once term_cases] )
  >- (
    simp[Once term_cases] >> rw[] >>
    simp[VSUBST_def,holSyntaxTheory.VSUBST_def] >>
    simp[Once term_cases] >>
    imp_res_tac term_welltyped >>
    fs[WELLTYPED,holSyntaxTheory.WELLTYPED] >>
    imp_res_tac VSUBST_HAS_TYPE >>
    imp_res_tac holSyntaxTheory.VSUBST_HAS_TYPE >>
    imp_res_tac WELLTYPED_LEMMA >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
    fs[] )
  >- (
    simp[Once term_cases] >> rw[] >>
    simp[VSUBST_def,holSyntaxTheory.VSUBST_def] >>
    qmatch_abbrev_tac`term defs (if p then q else r) (if p1 then q1 else r1)` >>
    `p = p1` by (
      unabbrev_all_tac >>
      simp[EXISTS_MEM,MEM_FILTER,EXISTS_PROD] >>
      fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      fs[EL_MAP] >> rfs[EL_MAP] >>
      simp[MEM_EL] >>
      rw[EQ_IMP_THM] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      first_x_assum(qspec_then`n`mp_tac) >>
      rw[] >>
      qpat_assum`(X,Y) = Z`(assume_tac o SYM) >> fs[] >- (
        map_every qexists_tac[`FST (EL n ilist1)`,`SND (EL n ilist1)`] >>
        simp[] >>
        conj_tac >- (
          reverse conj_tac >- METIS_TAC[] >>
          spose_not_then strip_assume_tac >>
          qpat_assum`term defs X Y`mp_tac >>
          Cases_on`p_2`>>simp[Once term_cases] >>
          fs[] >> METIS_TAC[term_type_11_inv] ) >>
        METIS_TAC[VFREE_IN_IMP_inv,VFREE_IN_IMP,term_rules] ) >>
      map_every qexists_tac[`FST (EL n ilist)`,`SND (EL n ilist)`] >>
      simp[] >>
      conj_tac >- (
        reverse conj_tac >- METIS_TAC[] >>
        spose_not_then strip_assume_tac >>
        qpat_assum`term defs X Y`mp_tac >>
        Cases_on`p_2`>>simp[Once term_cases] >>
        fs[] >> METIS_TAC[term_type_11] ) >>
      METIS_TAC[VFREE_IN_IMP_inv,VFREE_IN_IMP,term_rules] ) >>
    rw[Abbr`p`,Abbr`p1`] >> fs[] >>
    unabbrev_all_tac >>
    simp[Once term_cases] >>
    TRY (
      conj_asm1_tac >- (
        match_mp_tac EQ_SYM >>
        match_mp_tac VARIANT_IMP >>
        qexists_tac`defs` >>
        simp[] >>
        first_x_assum match_mp_tac >>
        simp[MEM_FILTER] >>
        conj_tac >>
        tac )) >>
    first_x_assum match_mp_tac >>
    simp[MEM_FILTER] >>
    rw[] >>
    TRY ( simp[Once term_cases] >> NO_TAC ) >>
    TRY ( simp[Once has_type_cases,Once holSyntaxTheory.has_type_cases] >> NO_TAC) >>
    tac))

val (result_term_rules,result_term_ind,result_term_cases) = Hol_reln`
  (term defs tm tm1 ⇒ result_term defs (Clash tm) (Clash tm1)) ∧
  (term defs tm tm1 ⇒ result_term defs (Result tm) (Result tm1))`

val TYPE_SUBST_IMP = prove(
  ``∀ty1 tyin1 ty tyin defs.
      type defs ty ty1 ∧
      LIST_REL (type defs) (MAP FST tyin) (MAP FST tyin1) ∧
      LIST_REL (type defs) (MAP SND tyin) (MAP SND tyin1)
      ⇒
      type defs (TYPE_SUBST tyin ty) (TYPE_SUBST tyin1 ty1)``,
  HO_MATCH_MP_TAC type_ind >>
  conj_tac >- (
    simp[Once term_cases] >> rw[] >>
    match_mp_tac REV_ASSOCD_tyin_IMP >>
    rw[Once term_cases] >>
    rw[Once term_cases] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once term_cases] >>
  rw[] >>
  rw[holSyntaxTheory.TYPE_SUBST_def] >>
  rw[Once term_cases] >> fs[] >>
  simp[EVERY2_MAP] >>
  fs[EVERY_MEM,EVERY2_EVERY] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  rw[] >>
  first_x_assum(qspec_then`EL n l`mp_tac) >>
  discharge_hyps >- METIS_TAC[MEM_EL] >>
  last_x_assum(qspec_then`n`mp_tac) >>
  simp[] >> strip_tac >>
  disch_then(qspecl_then[`tyin1`,`EL n tys`,`tyin`,`defs`]mp_tac) >>
  simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM])

val INST_CORE_IMP = prove(
  ``∀env tyin tm defs env1 tyin1 tm1.
      term defs tm tm1 ∧
      LIST_REL (type defs) (MAP FST tyin) (MAP FST tyin1) ∧
      LIST_REL (type defs) (MAP SND tyin) (MAP SND tyin1) ∧
      LIST_REL (term defs) (MAP FST env) (MAP FST env1) ∧
      LIST_REL (term defs) (MAP SND env) (MAP SND env1) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀s s'. MEM (s,s') env1 ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin1 ty))
      ⇒
      result_term defs (INST_CORE env tyin tm) (INST_CORE env1 tyin1 tm1)``,
  HO_MATCH_MP_TAC holSyntaxTheory.INST_CORE_ind >>
  conj_tac >- (
    simp[Once term_cases] >> rw[] >>
    simp[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
    qmatch_abbrev_tac`result_term defs (if p then q else r) (if p1 then q1 else r1)` >>
    `p = p1` by (
      unabbrev_all_tac >>
      qspecl_then[`ty1`,`tyin1`,`ty`,`tyin`,`defs`]mp_tac TYPE_SUBST_IMP >>
      simp[] >> strip_tac >>
      qmatch_assum_abbrev_tac `type defs ity ity1` >>
      qspecl_then[`env`,`defs`,`Var x ity`,`env1`,`Var x ity1`,`Var x ty`,`Var x ty1`]mp_tac REV_ASSOCD_ilist_IMP >>
      simp[] >>
      discharge_hyps >- (
        simp[Once term_cases] >>
        simp[Once term_cases] ) >>
      strip_tac >>
      EQ_TAC >> strip_tac >> fs[] >>
      fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
      fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
      METIS_TAC[term_type_11_inv,term_type_11] ) >>
    rw[Abbr`p`,Abbr`p1`] >> fs[] >>
    unabbrev_all_tac >>
    rw[Once result_term_cases] >>
    rw[Once term_cases] >>
    match_mp_tac TYPE_SUBST_IMP >>
    rw[] ) >>
  conj_tac >- (
    simp[Once term_cases] >> rw[] >>
    rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
    rw[Once result_term_cases] >>
    rw[Once term_cases] >>
    match_mp_tac TYPE_SUBST_IMP >>
    rw[] ) >>
  conj_tac >- (
    simp[Once term_cases] >> rw[] >>
    rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
    rw[Once result_term_cases] >>
    rw[Once term_cases] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    match_mp_tac TYPE_SUBST_IMP >>
    rw[] ) >>
  conj_tac >- (
    simp[Once term_cases] >> rw[] >>
    rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
    rw[Once result_term_cases] >>
    rw[Once term_cases] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    match_mp_tac TYPE_SUBST_IMP >>
    rw[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once term_cases] >> rw[] >>
    rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
    first_x_assum(qspecl_then[`defs`,`env1`,`tyin1`,`x1`]mp_tac) >>
    simp[] >> strip_tac >>
    `IS_CLASH sres = IS_CLASH sres'` by (
      Cases_on`sres`>>fs[Once result_term_cases] ) >>
    Cases_on`IS_CLASH sres` >> fs[] >>
    first_x_assum(qspecl_then[`defs`,`env1`,`tyin1`,`y1`]mp_tac) >>
    simp[] >> strip_tac >>
    `IS_CLASH tres = IS_CLASH tres'` by (
      Cases_on`tres`>>fs[Once result_term_cases] ) >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once result_term_cases] >>
    simp[Once term_cases] >>
    Cases_on`sres`>>fs[]>>
    Cases_on`sres'`>>fs[]>>
    Cases_on`tres`>>fs[]>>
    Cases_on`tres'`>>fs[]>>
    fs[Once result_term_cases] >>
    map_every qunabbrev_tac[`s'`,`s''`,`t'`,`t''`] >>
    simp[] >>
    qspecl_then[`sizeof tm`,`tm`,`env`,`tyin`]mp_tac holSyntaxTheory.INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    qspecl_then[`sizeof tm'`,`tm'`,`env`,`tyin`]mp_tac holSyntaxTheory.INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    imp_res_tac has_type_IMP >>
    simp[holSyntaxTheory.welltyped_def] >>
    conj_tac >- METIS_TAC[] >>
    conj_tac >- METIS_TAC[] >>
    qpat_assum`t''' has_type (Fun Y Z)`mp_tac >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    `welltyped t'''` by METIS_TAC[term_welltyped,welltyped_def] >>
    `welltyped t''''` by METIS_TAC[term_welltyped,welltyped_def] >>
    rw[] >> fs[] >>
    fs[holSyntaxTheory.WELLTYPED] >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
    fs[] >> rw[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once term_cases] >> rw[] >>
  rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
  cheat )

val INST_IMP = prove(
  ``∀tm tyin defs tyin1 tm1.
      term defs tm tm1 ∧ welltyped tm ∧
      LIST_REL (type defs) (MAP FST tyin) (MAP FST tyin1) ∧
      LIST_REL (type defs) (MAP SND tyin) (MAP SND tyin1)
      ⇒
      term defs (INST tyin tm) (INST tyin1 tm1)``,
  rw[INST_def,holSyntaxTheory.INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`,`defs`,`[]`,`tyin1`,`tm1`]mp_tac INST_CORE_IMP >>
  simp[] >>
  simp[Once result_term_cases] >>
  rw[] >> rw[] >>
  imp_res_tac term_welltyped >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin1`mp_tac) >>
  rw[])

val REV_ASSOCD_FILTER_vars = store_thm("REV_ASSOCD_FILTER_vars",
  ``∀a tyin1 tyin2.
      (FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin1
      =FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin2)
      ⇒
      holSyntax$REV_ASSOCD (holSyntax$Tyvar a) tyin1 (holSyntax$Tyvar a) =
      holSyntax$REV_ASSOCD (holSyntax$Tyvar a) tyin2 (holSyntax$Tyvar a)``,
  gen_tac >>
  Induct >> simp[holSyntaxTheory.REV_ASSOCD] >- (
    Induct >> simp[holSyntaxTheory.REV_ASSOCD] >>
    Cases >> simp[holSyntaxTheory.REV_ASSOCD] >>
    rw[] ) >>
  Cases >> simp[holSyntaxTheory.REV_ASSOCD] >>
  Induct >> simp[holSyntaxTheory.REV_ASSOCD] >- (
    rw[] >>
    first_x_assum(qspec_then`[]`mp_tac) >>
    rw[holSyntaxTheory.REV_ASSOCD] ) >>
  Cases >> simp[holSyntaxTheory.REV_ASSOCD] >>
  rw[] >> fs[] >- (
    first_x_assum(qspec_then`(q',Tyvar a)::tyin2`mp_tac) >>
    rw[holSyntaxTheory.REV_ASSOCD] ) >>
  first_x_assum(qspec_then`(q',Tyvar a')::tyin2`mp_tac) >>
  rw[holSyntaxTheory.REV_ASSOCD] )

val TYPE_SUBST_FILTER = store_thm("TYPE_SUBST_FILTER",
  ``∀ty tyin1 tyin2.
      (FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin1
      =FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin2)
      ⇒
      holSyntax$TYPE_SUBST tyin1 ty = holSyntax$TYPE_SUBST tyin2 ty``,
  ((TypeBase.induction_of``:holSyntax$type``)
    |> Q.SPECL[`P`,`EVERY P`]
    |> SIMP_RULE(srw_ss())[]
    |> UNDISCH_ALL
    |> CONJUNCT1
    |> DISCH_ALL
    |> GEN_ALL
    |> HO_MATCH_MP_TAC) >>
  rw[] >- rw[REV_ASSOCD_FILTER_vars] >>
  simp[MAP_EQ_f] >> fs[EVERY_MEM])

val INST_CORE_FILTER = store_thm("INST_CORE_FILTER",
  ``∀env tyin1 tm tyin2.
      (FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin1
      =FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin2)
      ⇒
      INST_CORE env tyin1 tm = holSyntax$INST_CORE env tyin2 tm``,
  HO_MATCH_MP_TAC holSyntaxTheory.INST_CORE_ind >>
  rw[holSyntaxTheory.INST_CORE_def] >>
  imp_res_tac REV_ASSOCD_FILTER_vars >>
  imp_res_tac TYPE_SUBST_FILTER >> fs[] >- (
    first_x_assum(qspec_then`tyin2`mp_tac) >> simp[] >>
    rw[] >> fs[] >>
    first_x_assum(qspec_then`tyin2`mp_tac) >> simp[] >>
    rw[] >> fs[] ) >>
  first_x_assum(qspec_then`tyin2`mp_tac) >> simp[] >>
  unabbrev_all_tac >>
  rw[] >> fs[] >>
  first_x_assum(qspec_then`tyin2`mp_tac) >> simp[] >>
  rw[] >> fs[] >>
  first_x_assum(qspec_then`tyin2`mp_tac) >> simp[] >>
  rw[] >> fs[] )

val INST_FILTER = store_thm("INST_FILTER",
  ``∀tyin1 tyin2 tm.
      (FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin1
      =FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin2)
      ⇒
      INST tyin1 tm = holSyntax$INST tyin2 tm``,
  rw[holSyntaxTheory.INST_def] >>
  imp_res_tac INST_CORE_FILTER >>
  pop_assum(qspecl_then[`tm`,`[]`]mp_tac) >>
  rw[])

val deftm_def = Define`
  deftm (Constdef n t) = t ∧
  deftm (Typedef n t a r) = t`

val MEM_Constdef_const_def = prove(
  ``∀defs n t. ALL_DISTINCT (MAP FST (consts defs)) ∧ MEM (Constdef n t) defs ⇒ const_def n defs = SOME (0,t)``,
  Induct >> simp[] >>
  Cases >> simp[consts_def,consts_aux_def] >>
  rw[Once const_def_def] >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  fs[consts_def] >> fs[] >>
  spose_not_then strip_assume_tac >>
  res_tac >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  fs[consts_def] >> fs[] )

val proves_IMP = store_thm("proves_IMP",
  ``(∀defs ty. type_ok defs ty ⇒ ∃ty1. type defs ty ty1 ∧ type_ok ty1) ∧
    (∀defs tm. term_ok defs tm ⇒ ∃tm1. term defs tm tm1 ∧ term_ok tm1) ∧
    (∀defs. context_ok defs ⇒
      ALL_DISTINCT (MAP FST (consts defs)) ∧
      (∀t. MEM t (MAP deftm defs) ⇒ ∃t1. term defs t t1 ∧ term_ok t1)) ∧
    (∀dh c. dh |- c ⇒
      ALL_DISTINCT (MAP FST (consts (FST dh))) ∧
      (∀t. MEM t (MAP deftm (FST dh)) ⇒ ∃t1. term (FST dh) t t1 ∧ term_ok t1) ∧
      ∃h1 c1. seq_trans (dh,c) (h1,c1) ∧ h1 |- c1)``,
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
  conj_tac >- (
    rw[seq_trans_def] >>
    rw[consts_def]
    (* >>
    qexists_tac`[]` >> simp[] >>
    qexists_tac`Var x Bool === Var x Bool` >>
    qspecl_then[`[]`,`Var x Bool`,`Var x Bool`,`Var x Bool === Var x Bool`]mp_tac (Q.GEN`defs`term_equation) >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >> strip_tac >>
    qexists_tac`Var x Bool === Var x Bool` >> simp[] >>
    simp[Once term_cases] >>
    simp[Once term_cases] >>
    simp[Once term_cases] >>
    simp[Once term_cases] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,14)) >>
    simp[Once proves_cases] >>
    simp[Once proves_cases] *)) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qspecl_then[`tm`,`tm`,`tm1 === tm1`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    `welltyped tm1` by METIS_TAC[soundness,has_meaning_welltyped] >>
    `welltyped tm` by METIS_TAC[term_welltyped] >>
    simp[] >> strip_tac >>
    qexists_tac`tm1 === tm1` >>
    simp[] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,14)] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    `∀t. MEM t (c1::h1) ∨ MEM t (c1'::h1') ⇒ t has_type Bool` by (
      imp_res_tac soundness >>
      fs[sequent_def,EVERY_MEM] >>
      METIS_TAC[] ) >>
    `welltyped (l === m1) ∧ welltyped (m2 === r)` by METIS_TAC[term_welltyped,welltyped_def,MEM] >>
    fs[welltyped_equation,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    qexists_tac`TERM_UNION h1 h1'` >>
    qspecl_then[`l`,`m1`,`c1`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >> strip_tac >>
    qspecl_then[`m2`,`r`,`c1'`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >> strip_tac >>
    imp_res_tac term_type_11 >> rw[] >>
    qexists_tac`x1 === y1'` >>
    qspecl_then[`l`,`r`,`x1 === y1'`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac holSyntaxTheory.ACONV_TYPE >>
    discharge_hyps >- METIS_TAC[] >>
    strip_tac >> simp[] >>
    conj_tac >- METIS_TAC[LIST_REL_term_UNION] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,15)) >>
    METIS_TAC[ACONV_IMP]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qspecl_then[`l1`,`r1`,`c1`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    `∀t. MEM t (c1::h1) ∨ MEM t (c1'::h1') ⇒ t has_type Bool` by (
      imp_res_tac soundness >> fs[sequent_def,EVERY_MEM] >>
      METIS_TAC[] ) >>
    `welltyped (l1 === r1) ∧ welltyped (l2 === r2)` by (
      imp_res_tac term_welltyped >>
      METIS_TAC[MEM,welltyped_def] ) >>
    fs[welltyped_equation,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    strip_tac >>
    qspecl_then[`l2`,`r2`,`c1'`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    strip_tac >>
    qspecl_then[`Comb l1 l2`,`Comb r1 r2`,`Comb x1 x1' === Comb y1 y1'`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    strip_tac >>
    map_every qexists_tac[`TERM_UNION h1 h1'`,`Comb x1 x1' === Comb y1 y1'`] >>
    simp[LIST_REL_term_UNION] >>
    simp[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
    srw_tac[boolSimps.DNF_ss][] >- METIS_TAC[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,16)) >>
    simp[] >>
    conj_asm1_tac >- METIS_TAC[term_welltyped] >>
    conj_tac >- METIS_TAC[term_welltyped] >>
    fs[WELLTYPED,holSyntaxTheory.WELLTYPED] >>
    imp_res_tac has_type_IMP >> rfs[] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    METIS_TAC[term_type_11] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qexists_tac`h1` >>
    simp[] >>
    qspecl_then[`l`,`r`,`c1`]mp_tac term_equation >>
    simp[] >>
    `c1 has_type Bool` by (
      imp_res_tac soundness >>
      fs[sequent_def] ) >>
    `l === r has_type Bool` by (
      simp[GSYM welltyped_equation] >>
      metis_tac[term_welltyped,welltyped_def] ) >>
    simp[] >> strip_tac >>
    qexists_tac`Abs x ty1 x1 === Abs x ty1 y1` >>
    qspecl_then[`Abs x ty l`,`Abs x ty r`,`Abs x ty1 x1 === Abs x ty1 y1`]mp_tac term_equation >>
    fs[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    strip_tac >>
    simp[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
    conj_tac >- METIS_TAC[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,17)) >>
    simp[] >>
    fs[EVERY_MEM,EVERY2_EVERY] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    rw[] >> res_tac >> pop_assum mp_tac >>
    METIS_TAC[VFREE_IN_IMP_inv,term_rules]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qspecl_then[`Comb (Abs x ty tm) (Var x ty)`,`tm`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    `welltyped tm1` by METIS_TAC[soundness,has_meaning_welltyped] >>
    `welltyped tm` by METIS_TAC[term_welltyped] >>
    simp[] >> strip_tac >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    srw_tac[boolSimps.DNF_ss][] >>
    map_every qexists_tac[`tm1`,`ty1`,`tm1`,`ty1`] >>
    simp[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,18)) >>
    simp[] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    srw_tac[boolSimps.DNF_ss][] >>
    map_every qexists_tac[`tm1`,`tm1`] >>
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,19)) >>
    imp_res_tac has_type_IMP >>
    fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >>
    rw[] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qexists_tac`TERM_UNION h1 h1'` >>
    qspecl_then[`p`,`c`,`c1`]mp_tac term_equation >>
    `welltyped c1` by (
      imp_res_tac soundness >>
      fs[sequent_def,welltyped_def] >>
      METIS_TAC[] ) >>
    `welltyped (p === c)` by METIS_TAC[term_welltyped] >>
    fs[welltyped_equation] >>
    strip_tac >>
    qexists_tac`y1` >>
    simp[LIST_REL_term_UNION] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,20)) >>
    qexists_tac`x1` >> rw[] >>
    qexists_tac`c1'` >> rw[] >>
    METIS_TAC[ACONV_IMP] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qexists_tac`TERM_UNION (FILTER ($~ o ACONV c1') h1) (FILTER ($~ o ACONV c1) h1')` >>
    qexists_tac`c1 === c1'` >>
    qspecl_then[`c`,`c'`,`c1 === c1'`]mp_tac term_equation >>
    discharge_hyps >- (
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      `c1 has_type Bool ∧ c1' has_type Bool` by (
        imp_res_tac soundness >>
        fs[sequent_def] ) >>
      conj_asm1_tac >- METIS_TAC[welltyped_def,term_welltyped] >>
      conj_asm1_tac >- METIS_TAC[welltyped_def,term_welltyped] >>
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac has_type_IMP >>
      imp_res_tac WELLTYPED_LEMMA >> rw[] >>
      fs[] >>
      METIS_TAC[term_type_11_inv] ) >>
    disch_then(mp_tac o snd o EQ_IMP_RULE) >>
    discharge_hyps >- METIS_TAC[] >>
    strip_tac >> simp[] >>
    conj_tac >- (
      match_mp_tac LIST_REL_term_UNION >>
      conj_tac >>
      match_mp_tac LIST_REL_term_FILTER_ACONV >>
      METIS_TAC[] ) >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,21)) >>
    rw[] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qabbrev_tac`tyin0 = FILTER (λ(ty,s). ∃a. s = Tyvar a) tyin` >>
    `INST tyin = INST tyin0` by (
      simp[FUN_EQ_THM] >>
      gen_tac >>
      match_mp_tac INST_FILTER >>
      simp[Abbr`tyin0`,rich_listTheory.FILTER_FILTER] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      simp[FUN_EQ_THM] ) >>
    `∃tyin1. LIST_REL (type defs) (MAP FST tyin0) (MAP FST tyin1) ∧
             LIST_REL (type defs) (MAP SND tyin0) (MAP SND tyin1) ∧
             EVERY type_ok (MAP FST tyin1)` by (
      simp[exists_list_GENLIST] >>
      qexists_tac`LENGTH tyin0` >>
      simp[EVERY_MAP,EVERY_GENLIST] >>
      simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
      rw[] >>
      `MEM (EL i tyin0) tyin0` by METIS_TAC[MEM_EL] >>
      `MEM (EL i tyin0) tyin` by (
        fs[Abbr`tyin0`,MEM_FILTER] ) >>
      Cases_on`EL i tyin0` >>
      first_x_assum(qspecl_then[`r`,`q`]mp_tac) >>
      simp[] >> rw[] >>
      fs[Abbr`tyin0`,MEM_FILTER] >>
      simp[EXISTS_PROD] >>
      simp[Once CONJ_COMM] >>
      simp[Once term_cases] >>
      qexists_tac`ty1` >>
      simp[]) >>
    `∀t. MEM t (c1::h1) ⇒ welltyped t` by (
      imp_res_tac soundness >>
      fs[sequent_def,EVERY_MEM] >>
      METIS_TAC[has_meaning_welltyped] ) >>
    qexists_tac`MAP (INST tyin1) h1` >>
    qexists_tac`INST tyin1 c1` >>
    reverse conj_tac >- (
      match_mp_tac(List.nth(CONJUNCTS proves_rules,22)) >>
      simp[] ) >>
    qpat_assum`LIST_REL X asl h1`mp_tac >>
    simp[EVERY2_EVERY,EVERY_MEM] >>
    strip_tac >> pop_assum mp_tac >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac INST_IMP >>
    simp[] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    METIS_TAC[term_welltyped]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    `∃ilist1. LIST_REL (term defs) (MAP FST ilist) (MAP FST ilist1) ∧
              LIST_REL (term defs) (MAP SND ilist) (MAP SND ilist1)` by (
      simp[exists_list_GENLIST] >>
      qexists_tac`LENGTH ilist` >>
      simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
      fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
      Cases_on`EL n ilist` >>
      first_x_assum(qspecl_then[`r`,`q`,`n`]mp_tac) >>
      simp[] >> rw[] >>
      simp[Once CONJ_COMM] >>
      simp[Once term_cases] >>
      simp[EXISTS_PROD] >>
      qexists_tac`tm1` >>
      simp[] >>
      imp_res_tac has_type_IMP >>
      METIS_TAC[] ) >>
    qexists_tac`MAP (VSUBST ilist1) h1` >>
    qexists_tac`VSUBST ilist1 c1` >>
    reverse conj_tac >- (
      match_mp_tac(List.nth(CONJUNCTS proves_rules,23)) >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
      rpt gen_tac >> strip_tac >>
      Cases_on`EL n ilist` >>
      first_x_assum(qspecl_then[`r`,`q`,`n`]mp_tac) >>
      simp[] >> strip_tac >>
      rpt (first_x_assum(qspec_then`n`mp_tac)) >>
      simp[] >> ntac 3 strip_tac >>
      imp_res_tac term_type_11 >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qpat_assum`(X,Y)=Z`(assume_tac o SYM) >> fs[]>>
      fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
      imp_res_tac has_type_IMP >>
      METIS_TAC[term_type_11] ) >>
    qpat_assum`LIST_REL X asl h1`mp_tac >>
    simp[EVERY2_EVERY,EVERY_MEM] >>
    strip_tac >> pop_assum mp_tac >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac VSUBST_IMP >>
    simp[] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    conj_tac >- METIS_TAC[] >>
    qx_genl_tac[`x`,`y`,`m`] >> strip_tac >>
    Cases_on`EL m ilist` >>
    first_x_assum(qspecl_then[`r`,`q`,`m`]mp_tac) >>
    simp[] >> strip_tac >>
    rpt (first_x_assum(qspec_then`m`mp_tac)) >>
    simp[] >> ntac 3 strip_tac >>
    imp_res_tac term_type_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qpat_assum`(X,Y)=Z`(assume_tac o SYM) >> fs[]>>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    METIS_TAC[has_type_IMP,term_type_11] ) >>
  conj_tac >- (
    rw[seq_trans_def,deftm_def] >>
    TRY (
      first_x_assum(qspec_then`t`mp_tac) >>
      rw[] >>
      qexists_tac`t1` >> rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT2 term_type_cons)) >>
      simp[safe_def_names_def] ) >>
    TRY (
      qexists_tac`tm1` >> rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT2 term_type_cons)) >>
      simp[safe_def_names_def] ) >>
    TRY (
      fs[consts_def] >>
      fs[ALL_DISTINCT_APPEND] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      METIS_TAC[] ) >>
    map_every qexists_tac[`h1`,`c1`] >>
    simp[] >>
    fs[EVERY_MEM,EVERY2_EVERY] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    `safe_def_names defs (Constdef s tm)` by (
      simp[safe_def_names_def] ) >>
    METIS_TAC[term_type_cons]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    first_x_assum(qspec_then`t`mp_tac) >>
    simp[MEM_MAP] >>
    discharge_hyps >- (
      qexists_tac`Constdef n t` >>
      simp[deftm_def] ) >>
    strip_tac >>
    `welltyped t1` by (
      imp_res_tac soundness >>
      METIS_TAC[has_meaning_welltyped] ) >>
    `welltyped t` by METIS_TAC[term_welltyped] >>
    qexists_tac`Const n (typeof t1) (Defined t1) === t1` >>
    qspecl_then[`Const n (typeof t)`,`t`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >> strip_tac >>
    conj_tac >- (
      qexists_tac`Const n (typeof t1) (Defined t1)` >>
      qexists_tac`t1` >>
      simp[] >>
      simp[Once term_cases] >>
      qexists_tac`0` >>
      rw[] >>
      qexists_tac`t` >>
      simp[] >>
      conj_tac >- METIS_TAC[has_type_IMP,WELLTYPED_LEMMA,WELLTYPED,holSyntaxTheory.WELLTYPED_LEMMA,holSyntaxTheory.WELLTYPED] >>
      MEM_Constdef_const_def >>
      rw[] ) >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,24)) >>
    fs[WELLTYPED] >>
    (* need to remember all this information with the inductive hypothesis for context_ok *)
    cheat ) >>
  rpt gen_tac >>
  simp[seq_trans_def] >>
  strip_tac >- (
    conj_tac >- (
      fs[consts_def] >>
      simp[Once consts_aux_def]
    map_every qexists_tac[`h1`,`c1'`] >>
    fs[EVERY_MEM,EVERY2_EVERY] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    `safe_def_names defs (Typedef tyname t a r)` by (
      simp[safe_def_names_def] ) >>
    METIS_TAC[term_type_cons])
  >- (
    simp[] >>
    cheat ) >>
  simp[] >>
  cheat)

val _ = export_theory();
