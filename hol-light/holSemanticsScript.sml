open HolKernel Parse boolLib bossLib lcsymtacs miscTheory miscLib;

val _ = new_theory "holSemantics";

open holSyntaxTheory holSyntaxLibTheory;
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

val good_defs_def = Define`
  (good_defs defs ⇔
    ALL_DISTINCT (MAP FST (types defs)) ∧
    ALL_DISTINCT (MAP FST (consts defs)))`

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
   (const_def s defs = SOME (0,tm)) /\ term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (Defined tm1))) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (1,tm)) /\
   (type_def n defs = SOME (tm,s,s')) /\
   (∀tm n' s'. (MEM (Typedef n' tm s s') defs) ⇒ (n' = n)) /\
   term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (Tyabs n tm1))) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (2,tm)) /\
   (type_def n defs = SOME (tm,s',s)) /\
   (∀tm n' s'. (MEM (Typedef n' tm s' s) defs) ⇒ (n' = n)) /\
   term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (Tyrep n tm1)))`

val seq_trans_def = Define `
  seq_trans ((defs,h),c) (h1,c1) <=>
    EVERY2 (term defs) h h1 /\ term defs c c1`;


(* -- part 2 -- *)

val hol_seq_def = Define `
  hol_seq ((defs,hyps),tm) = ?h c. seq_trans ((defs,hyps),tm) (h,c) /\ h |= c`;


(* -- part 3 -- *)

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

val MEM_Typedef_MEM_types = store_thm("MEM_Typedef_MEM_types",
  ``∀defs n tm a r. MEM (Typedef n tm a r) defs ⇒
    MEM n (MAP FST (FLAT (MAP types_aux defs)))``,
  Induct >> simp[] >>
  rw[types_def,types_aux_def] >>
  rw[types_def,types_aux_def] >>
  fs[types_def] >>
  METIS_TAC[])

val MEM_Typedef_MEM_consts = store_thm("MEM_Typedef_MEM_consts",
  ``∀defs n tm a r. MEM (Typedef n tm a r) defs ⇒
    MEM a (MAP FST (FLAT (MAP consts_aux defs))) ∧ MEM r (MAP FST (FLAT (MAP consts_aux defs)))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  METIS_TAC[])

val MEM_Constdef_MEM_consts = prove(
  ``∀defs n tm. MEM (Constdef n tm) defs ⇒
    MEM n (MAP FST (FLAT (MAP consts_aux defs)))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  METIS_TAC[])

val neq210 = prove(``2:int ≠ 0 ∧ 2 ≠ 1``,simp[])

val good_defs_imp = store_thm("good_defs_imp",
  ``good_defs defs ⇒
      (type_def "fun" defs = NONE) ∧
      (type_def "bool" defs = NONE) ∧
      (type_def "ind" defs = NONE) ∧
      (const_def "=" defs = NONE) ∧
      (const_def "@" defs = NONE)``,
  rw[good_defs_def] >>
  qmatch_abbrev_tac`X = NONE` >>
  Cases_on`X` >> fs[markerTheory.Abbrev_def] >>
  pop_assum (assume_tac o SYM) >>
  PairCases_on`x` >>
  imp_res_tac type_def_MEM >>
  imp_res_tac MEM_Typedef_MEM_types >>
  TRY (Cases_on`x0 = 0` >> Cases_on`x0 = 1`) >>
  fs[] >> rfs[] >>
  imp_res_tac const_def_MEM_0 >>
  imp_res_tac const_def_MEM_1 >>
  imp_res_tac const_def_MEM_2 >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  imp_res_tac MEM_Typedef_MEM_consts >>
  fs[] >> rfs[] >>
  fs[types_def,consts_def,ALL_DISTINCT_APPEND] >>
  METIS_TAC[])
val _ = export_rewrites["good_defs_imp"]

val term_type_11 = prove(
  ``∀defs. good_defs defs ⇒
    (!ty ty1. type defs ty ty1 ==> !ty2. type defs ty ty2 ==> (ty1 = ty2)) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀tm2. term defs tm tm2 ⇒ (tm1 = tm2))``,
  gen_tac >> strip_tac >>
  HO_MATCH_MP_TAC term_ind >>
  rpt conj_tac >> rpt gen_tac
  >- simp[Once term_cases]
  >- simp[Once term_cases]
  >- simp[Once term_cases]
  >- ( strip_tac >> simp[Once term_cases] >> rw[])
  >- (
    strip_tac >> simp[Once term_cases] >> rw[] >> rfs[] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rw[LIST_EQ_REWRITE] >> rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
    METIS_TAC[] )
  >> (strip_tac >> simp[Once term_cases] >> rw[] >> rfs[] >>
    METIS_TAC[type_def_MEM,const_def_MEM_1,const_def_MEM_2,neq210
             ,const_def_MEM_0,MEM_Constdef_MEM_consts,MEM_Typedef_MEM_consts]))

val term_type_11_inv = prove(
  ``∀defs. good_defs defs ⇒
    (!ty ty1. type defs ty ty1 ==> !ty2. type defs ty2 ty1 ==> (ty = ty2)) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀tm2. term defs tm2 tm1 ⇒ (tm = tm2))``,
  gen_tac >> strip_tac >>
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
  >- ( strip_tac >> simp[Once term_cases] >> rw[] )
  >- ( strip_tac >> simp[Once term_cases] >> rw[] )
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- ( strip_tac >> simp[Once term_cases] >> rw[] )
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[])
  >- (strip_tac >> simp[Once term_cases] >> METIS_TAC[]))

val has_type_IMP = prove(
  ``∀tm ty. tm has_type ty ⇒ ∀defs tm1. good_defs defs ∧ term defs tm tm1 ⇒ ∃ty1. type defs ty ty1 ∧ tm1 has_type ty1``,
  HO_MATCH_MP_TAC holSyntaxTheory.has_type_strongind >> rw[] >>
  TRY (
    qpat_assum`term defs (Comb X Y) Z`mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
    fsrw_tac[boolSimps.DNF_ss][] >>
    METIS_TAC[term_type_11,type_def_MEM,MEM_Typedef_MEM_types] ) >>
  TRY (
    qpat_assum`term defs (Abs X Y A) Z`mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    rw[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] ) >>
  (
    first_x_assum mp_tac >>
    rw[Once term_cases] >>
    rw[Once has_type_cases] >>
    METIS_TAC[term_type_11] ))

val term_equation = prove(
  ``!x y z. (x === y) has_type Bool ∧ good_defs defs ⇒
    (term defs (x === y) z ⇔ ∃x1 y1. (z = x1 === y1) ∧ term defs x x1 ∧ term defs y y1)``,
  rpt gen_tac >> strip_tac >>
  simp[equation_def,holSyntaxTheory.equation_def] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp[Once term_cases] >>
  simp[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >>
  fs[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
  rw[EQ_IMP_THM] >>
  METIS_TAC[term_type_11,has_type_IMP,holSyntaxTheory.WELLTYPED,WELLTYPED_LEMMA,good_defs_def])

val term_welltyped = store_thm("term_welltyped",
  ``∀defs. good_defs defs ⇒
    (∀ty ty1. type defs ty ty1 ⇒ T) ∧
    (∀tm tm1. term defs tm tm1 ⇒ (welltyped tm ⇔ welltyped tm1))``,
  gen_tac >> strip_tac >>
  HO_MATCH_MP_TAC (theorem"term_strongind") >>
  simp[] >> rw[] >>
  rw[EQ_IMP_THM] >> fs[] >>
  fs[WELLTYPED,holSyntaxTheory.WELLTYPED] >>
  imp_res_tac has_type_IMP >>
  fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >> rfs[] >>
  METIS_TAC[has_type_IMP,term_type_11,WELLTYPED_LEMMA,holSyntaxTheory.WELLTYPED_LEMMA,type_def_MEM,MEM_Typedef_MEM_types])

val welltyped_equation = prove(
  ``holSyntax$welltyped (s === t) ⇔ (s === t) has_type Bool``,
  rw[holSyntaxTheory.equation_def] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  rw[Once holSyntaxTheory.has_type_cases] >>
  METIS_TAC[holSyntaxTheory.WELLTYPED,holSyntaxTheory.WELLTYPED_LEMMA])

val ALPHAVARS_IMP = prove(
  ``∀env tp. ALPHAVARS env tp ⇒
      ∀defs tp1 env1.
        good_defs defs ∧
        LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
        LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
        ALPHAVARS env1 tp1``,
  Induct >> simp[ALPHAVARS_def] >- (
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
      good_defs defs ∧
      LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
      LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
      RACONV env1 tp1``,
   HO_MATCH_MP_TAC holSyntaxTheory.RACONV_ind >>
   simp[] >> rw[] >>
   Cases_on`tp1` >>
   fs[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Select X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Equal X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   fs[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[RACONV] >> fsrw_tac[ARITH_ss][] >>
   TRY (match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH (SPEC_ALL term_type_11)))) >> metis_tac[]) >>
   TRY (
     match_mp_tac (MP_CANON ALPHAVARS_IMP) >>
     qexists_tac`env` >>
     qexists_tac`Var x1 ty1,Var x2 ty2` >>
     qexists_tac`defs` >>
     simp[] >>
     simp[Once term_cases] >>
     simp[Once term_cases] ) >>
   TRY (first_x_assum match_mp_tac >> simp[] >> metis_tac[]) >>
   TRY (last_x_assum match_mp_tac >> simp[] >> metis_tac[])
   >- (
     rpt(qpat_assum`term defs X Y`mp_tac) >>
     simp[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
     rw[] >> simp_tac(srw_ss())[RACONV] >>
     rpt conj_tac >>
     full_simp_tac pure_ss [] >>
     TRY (
       qpat_assum`SOME X = SOME Y`mp_tac >>
       simp_tac(srw_ss()++ARITH_ss)[] >>
       strip_tac ) >>
     rpt BasicProvers.VAR_EQ_TAC >> rfs[] >>
     metis_tac[term_type_11,const_def_MEM_1,const_def_MEM_2,const_def_MEM_0,neq210
     ,MEM_Constdef_MEM_consts,MEM_Typedef_MEM_consts,MEM_Typedef_MEM_types,type_def_MEM] ) >>
   fs[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[RACONV] >- metis_tac[term_type_11] >>
   first_x_assum match_mp_tac >> simp[] >>
   qexists_tac`defs` >> simp[])

val ALPHAVARS_IMP_inv = prove(
  ``∀env1 tp1. ALPHAVARS env1 tp1 ⇒
      ∀defs tp env.
        good_defs defs ∧
        LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
        LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
        ALPHAVARS env tp``,
  Induct >> simp[ALPHAVARS_def] >- (
    Cases >> simp[] >> metis_tac[term_type_11_inv] ) >>
  rw[] >>
  imp_res_tac term_type_11_inv >> rw[] >- (
    Cases_on`env`>>fs[ALPHAVARS_def]>>
    metis_tac[PAIR_EQ,pair_CASES,FST,SND] ) >>
  Cases_on`env`>>fs[ALPHAVARS_def]>>
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
      good_defs defs ∧
      LIST_REL (term defs) (MAP FST(tp::env)) (MAP FST(tp1::env1))∧
      LIST_REL (term defs) (MAP SND(tp::env)) (MAP SND(tp1::env1))⇒
      RACONV env tp``,
   HO_MATCH_MP_TAC RACONV_ind >>
   simp[] >> rw[] >>
   Cases_on`tp` >>
   fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
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
     simp[Once term_cases] )
   >- (
     fs[Q.SPECL[`A`,`Const X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
     rw[holSyntaxTheory.RACONV] >>
     TRY (match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH(SPEC_ALL term_type_11_inv)))) >> metis_tac[]) >>
     TRY (match_mp_tac(MP_CANON(CONJUNCT2 (UNDISCH(SPEC_ALL term_type_11_inv)))) >> metis_tac[]) >>
     imp_res_tac term_type_11_inv >> fs[] ) >>
   fs[Q.SPECL[`A`,`Abs X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
   rw[holSyntaxTheory.RACONV] >- metis_tac[term_type_11_inv] >>
   first_x_assum match_mp_tac >> simp[] >>
   qexists_tac`defs` >> simp[])

val ACONV_IMP = prove(
  ``∀defs t1 t2 t11 t22. good_defs defs ∧ ACONV t1 t2 ∧ term defs t1 t11 ∧ term defs t2 t22 ⇒ ACONV t11 t22``,
  rw[ACONV_def,holSyntaxTheory.ACONV_def] >>
  match_mp_tac (MP_CANON RACONV_IMP) >>
  simp[EXISTS_PROD] >>
  metis_tac[])

val ACONV_IMP_inv = prove(
  ``∀defs t1 t2 t11 t22. good_defs defs ∧ ACONV t11 t22 ∧ term defs t1 t11 ∧ term defs t2 t22 ⇒ ACONV t1 t2``,
  rw[ACONV_def,holSyntaxTheory.ACONV_def] >>
  match_mp_tac (MP_CANON RACONV_IMP_inv) >>
  simp[EXISTS_PROD] >>
  metis_tac[])

val LIST_REL_term_UNION = prove(
  ``∀defs l1 l2 r1 r2. good_defs defs ∧ LIST_REL (term defs) l1 r1 ∧ LIST_REL (term defs) l2 r2 ⇒
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
  ``!t2 t1 defs s2 s1. good_defs defs ∧ VFREE_IN t1 t2 ∧ term defs t1 s1 ∧ term defs t2 s2 ⇒ VFREE_IN s1 s2``,
  Induct >> simp[] >>
  fs[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Select X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Equal X`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >> rw[holSyntaxTheory.VFREE_IN_def] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  imp_res_tac term_type_11 >> fs[] >> rw[]
  >- (
    fs[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] )
  >- METIS_TAC[] >- METIS_TAC[]
  >- (
    spose_not_then strip_assume_tac >> rw[] >>
    fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    rw[] >> METIS_TAC[term_type_11_inv] ) >>
  METIS_TAC[])

val VFREE_IN_IMP_inv = prove(
  ``!s2 s1 defs t2 t1. good_defs defs ∧ VFREE_IN s1 s2 ∧ term defs t1 s1 ∧ term defs t2 s2 ⇒ VFREE_IN t1 t2``,
  Induct >> simp[] >>
  fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPECL[`A`,`Comb X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >> rw[holSyntaxTheory.VFREE_IN_def] >>
  last_x_assum mp_tac >> rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  imp_res_tac term_type_11_inv >> fs[] >- (
    fs[Q.SPECL[`A`,`Const X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] )
  >- METIS_TAC[] >- METIS_TAC[] >>
  fs[Q.SPECL[`A`,`Abs X Y Z`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  rw[] >- (
    spose_not_then strip_assume_tac >> rw[] >>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    rw[] >> METIS_TAC[term_type_11] ) >>
  METIS_TAC[])

val LIST_REL_term_FILTER_ACONV = prove(
  ``∀asl1 h1 c c1.
    good_defs defs ∧
    LIST_REL (term defs) asl1 h1 ∧ term defs c c1
    ⇒
    LIST_REL (term defs) (FILTER ($~ o ACONV c) asl1)
    (FILTER ($~ o ACONV c1) h1)``,
  Induct >> simp[] >>
  rw[] >> rw[] >>
  METIS_TAC[ACONV_IMP,ACONV_IMP_inv])

val safe_def_names_def = Define`
  (safe_def_names defs (Constdef n t) ⇔ n ∉ set (MAP FST (consts defs))) ∧
  (safe_def_names defs (Typedef n t a r) ⇔
    n ∉ set (MAP FST (types defs)) ∧
    a ∉ set (MAP FST (consts defs)) ∧
    r ∉ set (MAP FST (consts defs)))`

val term_type_cons = prove(
  ``∀defs. good_defs defs ⇒
    (∀ty ty1. type defs ty ty1 ⇒ ∀d. safe_def_names defs d ⇒ type (d::defs) ty ty1) ∧
    (∀tm tm1. term defs tm tm1 ⇒ ∀d. safe_def_names defs d ⇒ term (d::defs) tm tm1)``,
  gen_tac >> strip_tac >>
  HO_MATCH_MP_TAC term_ind >> rw[] >>
  simp[Once term_cases]
  >- (
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[type_def_def] >>
    BasicProvers.CASE_TAC >- METIS_TAC[] >>
    fs[safe_def_names_def] >>
    imp_res_tac type_def_MEM >>
    rw[] >- METIS_TAC[MEM_Typedef_MEM_types,types_def,MEM_APPEND,MAP_APPEND] >>
    first_x_assum match_mp_tac >>
    rw[safe_def_names_def] )
  >- (
    qexists_tac`tm` >>
    reverse conj_tac >- METIS_TAC[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >>
    imp_res_tac const_def_MEM_0 >>
    imp_res_tac MEM_Constdef_MEM_consts >>
    fs[safe_def_names_def,consts_def] >>
    rw[] >> fs[] )
  >- (
    qexists_tac`s'` >> qexists_tac`tm` >>
    imp_res_tac const_def_MEM_1 >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    res_tac >> simp[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >> rw[Once type_def_def] >>
    fs[safe_def_names_def] >>
    imp_res_tac type_def_MEM >>
    imp_res_tac MEM_Typedef_MEM_types >>
    fs[types_def,consts_def] >> rw[] >>
    METIS_TAC[])
  >- (
    qexists_tac`s'` >> qexists_tac`tm` >>
    imp_res_tac const_def_MEM_2 >>
    fsrw_tac[ARITH_ss][] >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    res_tac >> simp[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    rw[] >> rw[Once type_def_def] >>
    fs[safe_def_names_def] >>
    imp_res_tac type_def_MEM >>
    imp_res_tac MEM_Typedef_MEM_types >>
    fs[types_def,consts_def] >> rw[] >>
    METIS_TAC[const_def_MEM_2]))

val REV_ASSOCD_ilist_IMP = prove(
  ``∀ilist defs t ilist1 t1 d d1.
      good_defs defs ∧
      LIST_REL (term defs) (MAP FST ilist) (MAP FST ilist1) ∧
      LIST_REL (term defs) (MAP SND ilist) (MAP SND ilist1) ∧
      term defs t t1 ∧
      term defs d d1
      ⇒
      term defs (REV_ASSOCD t ilist d) (REV_ASSOCD t1 ilist1 d1)``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
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
      good_defs defs ∧
      LIST_REL (type defs) (MAP FST tyin) (MAP FST tyin1) ∧
      LIST_REL (type defs) (MAP SND tyin) (MAP SND tyin1) ∧
      type defs t t1 ∧
      type defs d d1
      ⇒
      type defs (REV_ASSOCD t tyin d) (REV_ASSOCD t1 tyin1 d1)``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
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
      good_defs defs ∧
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
      good_defs defs ∧
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
    rw[] >>
    METIS_TAC[const_def_MEM_1])
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
      good_defs defs ∧
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
      good_defs defs ∧
      welltyped tm ∧ term defs tm tm1 ∧
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
    TRY (
      match_mp_tac TYPE_SUBST_IMP >>
      rw[] ) >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
    TRY (match_mp_tac TYPE_SUBST_IMP) >>
    rw[] >>
    METIS_TAC[]) >>
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
    qpat_assum`a' has_type (Fun Y Z)`mp_tac >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    `welltyped a'` by METIS_TAC[term_welltyped,welltyped_def] >>
    `welltyped a''` by METIS_TAC[term_welltyped,welltyped_def] >>
    rw[] >> fs[] >>
    fs[holSyntaxTheory.WELLTYPED] >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
    fs[] >> rw[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once term_cases] >> rw[] >>
  rw[INST_CORE_def,holSyntaxTheory.INST_CORE_def] >>
  fs[] >>
  first_x_assum(qspecl_then[`defs`,`env'`,`tyin1`,`x1`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    simp[Abbr`env'`] >>
    simp[Once term_cases] >>
    simp[Once term_cases] >>
    conj_tac >- METIS_TAC[TYPE_SUBST_IMP] >>
    METIS_TAC[] ) >>
  strip_tac >>
  `IS_RESULT tres = IS_RESULT tres'` by (
    pop_assum mp_tac >>
    Cases_on`tres'`>>simp[Once result_term_cases] >>
    rw[] >> rw[] ) >>
  Cases_on`IS_RESULT tres` >> fs[] >- (
    simp[result_term_cases] >>
    simp[Once term_cases] >> rfs[] >>
    conj_tac >- METIS_TAC[TYPE_SUBST_IMP] >>
    Cases_on`tres`>>Cases_on`tres'`>>fs[]>>
    fs[result_term_cases] ) >>
  `term defs w w'` by (
    Cases_on`tres`>>Cases_on`tres'`>>
    rfs[result_term_cases] ) >>
  `w = Var x ty'' ⇔ w' = Var x ty'` by (
    EQ_TAC >>
    strip_tac >>
    qpat_assum`term defs w w'`mp_tac >>
    simp[Once term_cases] >>
    strip_tac >>
    Cases_on`tres`>>Cases_on`tres'`>>
    rfs[result_term_cases] >>
    METIS_TAC[TYPE_SUBST_IMP,term_type_11,term_type_11_inv] ) >>
  Cases_on`w = Var x ty''`>>rfs[]>>fs[]>>
  first_x_assum(qspecl_then[`defs`,`env''''`,`tyin1`,`t''`]mp_tac) >>
  `x' = x''` by (
    simp[Abbr`x'`,Abbr`x''`] >>
    match_mp_tac VARIANT_IMP >>
    qexists_tac`defs` >>
    simp[] >>
    reverse conj_tac >- METIS_TAC[TYPE_SUBST_IMP] >>
    first_x_assum(qspecl_then[`defs`,`tyin1`,`x1`]mp_tac) >>
    simp[] >>
    `IS_RESULT (INST_CORE [] tyin1 x1)` by (
      match_mp_tac INST_CORE_NIL_IS_RESULT >>
      METIS_TAC[term_welltyped] ) >>
    Cases_on`INST_CORE [] tyin1 x1`>>fs[] >>
    simp[result_term_cases] >> rw[] >> rw[] ) >>
  discharge_hyps >- (
    simp[] >>
    conj_tac >- (
      simp[Abbr`t'`] >>
      match_mp_tac holSyntaxTheory.VSUBST_WELLTYPED >>
      simp[] >>
      simp[Once holSyntaxTheory.has_type_cases] ) >>
    conj_tac >- (
      simp[Abbr`t'`,Abbr`t''`] >>
      match_mp_tac VSUBST_IMP >>
      simp[] >>
      simp[Once term_cases] >>
      simp[Once term_cases] >>
      simp[Once has_type_cases] >>
      simp[Once holSyntaxTheory.has_type_cases] ) >>
    simp[Abbr`env''''`] >>
    simp[Once term_cases] >>
    simp[Once term_cases] >>
    conj_tac >- METIS_TAC[TYPE_SUBST_IMP] >>
    METIS_TAC[] ) >>
  strip_tac >>
  `IS_RESULT tres'' = IS_RESULT tres'''` by (
    Cases_on`tres''`>>Cases_on`tres'''`>>rfs[result_term_cases] ) >>
  Cases_on`tres''`>>Cases_on`tres'''`>>fs[]>>rfs[result_term_cases] >>
  simp[Once term_cases] >>
  METIS_TAC[TYPE_SUBST_IMP] )

val INST_IMP = prove(
  ``∀tm tyin defs tyin1 tm1.
      good_defs defs ∧
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
      REV_ASSOCD (holSyntax$Tyvar a) tyin1 (holSyntax$Tyvar a) =
      REV_ASSOCD (holSyntax$Tyvar a) tyin2 (holSyntax$Tyvar a)``,
  gen_tac >>
  Induct >> simp[REV_ASSOCD] >- (
    Induct >> simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    rw[] ) >>
  Cases >> simp[REV_ASSOCD] >>
  Induct >> simp[REV_ASSOCD] >- (
    rw[] >>
    first_x_assum(qspec_then`[]`mp_tac) >>
    rw[REV_ASSOCD] ) >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    first_x_assum(qspec_then`(q',Tyvar a)::tyin2`mp_tac) >>
    rw[REV_ASSOCD] ) >>
  first_x_assum(qspec_then`(q',Tyvar a')::tyin2`mp_tac) >>
  rw[REV_ASSOCD] )

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

val MEM_Constdef_const_def = store_thm("MEM_Constdef_const_def",
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

val term_subterm = prove(
  ``∀tm defs tm1 t0. good_defs defs ∧ term defs tm tm1 ∧ VFREE_IN t0 tm ⇒ ∃t1. term defs t0 t1 ∧ VFREE_IN t1 tm1``,
  Induct >> simp[Once term_cases] >> rw[] >>
  simp[Once term_cases] >>
  rw[] >>
  res_tac >>
  imp_res_tac term_type_11 >>
  rw[]
  >- METIS_TAC[]
  >- METIS_TAC[] >>
  qexists_tac`t1` >> rw[] >>
  spose_not_then strip_assume_tac >>
  rw[] >>
  qpat_assum`term X Y Z`mp_tac >>
  simp_tac std_ss [Once term_cases] >>
  simp[] >>
  METIS_TAC[term_type_11_inv])

val term_subterm_inv = prove(
  ``∀tm1 defs tm t1. good_defs defs ∧ term defs tm tm1 ∧ VFREE_IN t1 tm1 ⇒ ∃t0. term defs t0 t1 ∧ VFREE_IN t0 tm``,
  Induct >> simp[Once term_cases] >> rw[] >>
  simp[Once term_cases] >>
  rw[] >>
  res_tac >>
  imp_res_tac term_type_11 >>
  rw[]
  >- METIS_TAC[]
  >- METIS_TAC[] >>
  qexists_tac`t0` >> rw[] >>
  spose_not_then strip_assume_tac >>
  rw[] >>
  qpat_assum`term X (A Y) Z`mp_tac >>
  simp_tac std_ss [Once term_cases] >>
  simp[] >>
  METIS_TAC[term_type_11])

val CLOSED_IMP = prove(
  ``∀tm defs tm1. good_defs defs ∧ term defs tm tm1 ⇒ (CLOSED tm ⇔ closed tm1)``,
  rw[holSyntaxTheory.CLOSED_def] >>
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  imp_res_tac VFREE_IN_IMP_inv >>
  imp_res_tac VFREE_IN_IMP >>
  fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[GSYM LEFT_FORALL_IMP_THM] >>
  imp_res_tac term_subterm >>
  imp_res_tac term_subterm_inv >>
  fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  fs[Q.SPECL[`A`,`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
  METIS_TAC[])

val tyvars_IMP = prove(
  ``∀ty1 defs ty. type defs ty ty1 ⇒ (tyvars ty = tyvars ty1)``,
  HO_MATCH_MP_TAC type_ind >> conj_tac >|[rpt gen_tac,rpt gen_tac >> strip_tac] >>
  simp[Once term_cases] >>
  rw[tyvars_def,holSyntaxTheory.tyvars_def] >>
  rw[tyvars_def,holSyntaxTheory.tyvars_def] >> fs[] >- (
    METIS_TAC[] ) >>
  ntac 2 (pop_assum kall_tac) >>
  fs[EVERY_MEM] >>
  ntac 2 (pop_assum mp_tac) >>
  qid_spec_tac`l` >>
  Induct_on`tys` >>
  simp[] >> rw[] >> rw[] >> fs[] >>
  METIS_TAC[] )

val tvars_IMP = prove(
  ``∀tm defs tm1. good_defs defs ∧ term defs tm tm1 ⇒ (tvars tm = tvars tm1)``,
  Induct >> simp[tvars_def,holSyntaxTheory.tvars_def] >>
  simp[Once term_cases] >> rw[] >>
  simp[tvars_def] >>
  fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
  fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >>
  rfs[] >>
  imp_res_tac term_type_11 >> rw[] >>
  simp[tyvars_def,holSyntaxTheory.tyvars_def] >>
  METIS_TAC[tyvars_IMP,LIST_UNION_NIL_2,tyvars_ALL_DISTINCT,LIST_UNION_same,pred_setTheory.SUBSET_DEF])

val TERM_UNION_NIL = store_thm("TERM_UNION_NIL",
  ``∀l2. holSyntax$TERM_UNION [] l2 = l2``,
  rw[holSyntaxTheory.TERM_UNION_def])
val _ = export_rewrites["TERM_UNION_NIL"]

val TERM_UNION_TERM_UNION_NIL = store_thm("TERM_UNION_TERM_UNION_NIL",
  ``∀l1 l2. holSyntax$TERM_UNION l2 [] = l2 ⇒ holSyntax$TERM_UNION (holSyntax$TERM_UNION l1 l2) [] = holSyntax$TERM_UNION l1 l2``,
  Induct >> simp[holSyntaxTheory.TERM_UNION_def] >>
  rw[holSyntaxTheory.TERM_UNION_def] >> rw[])
val _ = export_rewrites["TERM_UNION_TERM_UNION_NIL"]

val TERM_UNION_APPEND_SAME_NIL = store_thm("TERM_UNION_APPEND_SAME_NIL",
  ``∀ls l1. holSyntax$TERM_UNION ls [] = l1++ls ⇒ (l1 = [])``,
  Induct >> simp[holSyntaxTheory.TERM_UNION_def] >>
  rw[holSyntaxTheory.TERM_UNION_def] >- (
    first_x_assum(qspec_then`l1++[h]`mp_tac) >>
    simp[] ) >>
  Cases_on`l1`>>fs[])

val TERM_UNION_FILTER_NIL = store_thm("TERM_UNION_FILTER_NIL",
  ``!P l1. holSyntax$TERM_UNION l1 [] = l1 ⇒ holSyntax$TERM_UNION (FILTER P l1) [] = FILTER P l1``,
  gen_tac >> Induct >> simp[holSyntaxTheory.TERM_UNION_def] >>
  rw[holSyntaxTheory.TERM_UNION_def] >> rw[] >> fs[] >> TRY (
    qspecl_then[`l1`,`[h]`]mp_tac TERM_UNION_APPEND_SAME_NIL  >>
    simp[] ) >>
  fs[EVERY_MEM,EXISTS_MEM,Abbr`subun`,MEM_FILTER] >>
  METIS_TAC[])
val _ = export_rewrites["TERM_UNION_FILTER_NIL"]

val def_ok_def = Define`
  (def_ok (Constdef n t) ⇔ CLOSED t ∧ set (tvars t) ⊆ set (tyvars (typeof t))) ∧
  (def_ok (Typedef n t a r) ⇔ ∃rty. t has_type Fun rty Bool)`

val deftm_def = Define`
  deftm (Constdef n t) = [t;Const n (typeof t)] ∧
  deftm (Typedef n t a r) =
  let rty = domain(typeof t) in
  let aty = Tyapp n (MAP Tyvar (STRING_SORT (tvars t))) in
    [t;Const a (Fun rty aty);Const r (Fun aty rty)]`

val proves_IMP = store_thm("proves_IMP",
  ``(∀defs ty. type_ok defs ty ⇒ context_ok defs ∧ good_defs defs ∧ ∃ty1. type defs ty ty1 ∧ type_ok ty1) ∧
    (∀defs tm. term_ok defs tm ⇒ context_ok defs ∧ good_defs defs ∧ ∃tm1. term defs tm tm1 ∧ term_ok tm1) ∧
    (∀defs. context_ok defs ⇒
      good_defs defs ∧
      EVERY def_ok defs ∧
      (∀t. MEM t (FLAT (MAP deftm defs)) ⇒ term_ok defs t ∧ ∃t1. term defs t t1 ∧ term_ok t1)) ∧
    (∀dh c. dh |- c ⇒
      context_ok (FST dh) ∧
      good_defs (FST dh) ∧
      EVERY def_ok (FST dh) ∧
      (∀t. MEM t (FLAT (MAP deftm (FST dh))) ⇒ term_ok (FST dh) t ∧ ∃t1. term (FST dh) t t1 ∧ term_ok t1) ∧
      ∃h1 c1. seq_trans (dh,c) (h1,c1) ∧ h1 |- c1)``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_strongind >>
  conj_tac >- ( rw[] >> simp[Once term_cases,Once proves_cases] ) >>
  conj_tac >- ( rw[] >> rw[Once term_cases] >> rw[Once proves_cases] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[has_type_IMP] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >>
    rw[] >> fs[] >> rw[]
    >- (
      qexists_tac`tx1` >> rw[] >>
      rw[Once proves_cases] >>
      METIS_TAC[MEM] )
    >- (
      qexists_tac`ty1'` >> rw[] >>
      rw[Once proves_cases] >>
      METIS_TAC[MEM] ) >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL] >>
    qexists_tac`EL n' tys1` >> simp[] >>
    simp[Once proves_cases] >>
    METIS_TAC[MEM_EL] ) >>
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
    simp[Once proves_cases] >>
    fs[welltyped_def,holSyntaxTheory.welltyped_def] >>
    map_every qexists_tac[`tm1`,`tm1'`] >> rw[] >>
    disj1_tac >>
    conj_tac >- METIS_TAC[has_type_IMP] >>
    conj_tac >- METIS_TAC[has_type_IMP] >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >> fs[] >> rw[] >>
    imp_res_tac has_type_IMP >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >> rfs[] >>
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
    fs[] >>
    qexists_tac`x1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >> rw[] >>
    fs[] >>
    qexists_tac`y1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[Once term_cases] >> rw[] >>
    fs[] >>
    qexists_tac`x1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[seq_trans_def,EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,14),MEM,MEM_EL] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    rw[good_defs_def] >>
    rw[types_def] >>
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
    rw[seq_trans_def] >> rfs[] >>
    qspecl_then[`tm`,`tm`,`tm1 === tm1`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    `welltyped tm1` by METIS_TAC[soundness,has_meaning_welltyped] >>
    `welltyped tm` by METIS_TAC[term_welltyped] >>
    simp[] >> strip_tac >>
    qexists_tac`tm1 === tm1` >>
    simp[] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,15)] ) >>
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
    match_mp_tac(List.nth(CONJUNCTS proves_rules,16)) >>
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
    match_mp_tac(List.nth(CONJUNCTS proves_rules,17)) >>
    simp[] >>
    conj_asm1_tac >- METIS_TAC[term_welltyped] >>
    conj_tac >- METIS_TAC[term_welltyped] >>
    fs[WELLTYPED,holSyntaxTheory.WELLTYPED] >>
    imp_res_tac has_type_IMP >> rfs[] >>
    fs[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >> rw[] >> rfs[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    METIS_TAC[term_type_11] ) >>
  conj_tac >- (
    rw[seq_trans_def] >> fs[] >>
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
    match_mp_tac(List.nth(CONJUNCTS proves_rules,18)) >>
    simp[] >>
    fs[EVERY_MEM,EVERY2_EVERY] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    rw[] >> res_tac >> pop_assum mp_tac >>
    METIS_TAC[VFREE_IN_IMP_inv,term_rules]) >>
  conj_tac >- (
    rw[seq_trans_def] >> rfs[] >>
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
    match_mp_tac(List.nth(CONJUNCTS proves_rules,19)) >>
    simp[] ) >>
  conj_tac >- (
    rw[seq_trans_def] >> simp[holSyntaxTheory.TERM_UNION_def] >> rfs[] >>
    srw_tac[boolSimps.DNF_ss][] >>
    map_every qexists_tac[`tm1`,`tm1`] >>
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,20)) >>
    imp_res_tac has_type_IMP >>
    fs[Q.SPEC`Bool`(CONJUNCT1 (SPEC_ALL term_cases))] >>
    rw[] >> rfs[]) >>
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
    match_mp_tac(List.nth(CONJUNCTS proves_rules,21)) >>
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
      simp[] >>
      conj_tac >>
      match_mp_tac LIST_REL_term_FILTER_ACONV >>
      METIS_TAC[] ) >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,22)) >>
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
      match_mp_tac(List.nth(CONJUNCTS proves_rules,23)) >>
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
      match_mp_tac(List.nth(CONJUNCTS proves_rules,24)) >>
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
    rw[seq_trans_def,deftm_def] >> rfs[] >>
    TRY (
      first_x_assum(qspec_then`t`mp_tac) >>
      rw[] >>
      qexists_tac`t1` >> rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT2 (UNDISCH (SPEC_ALL term_type_cons)))) >>
      simp[safe_def_names_def] ) >>
    TRY (
      qexists_tac`tm1` >> rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT2 (UNDISCH (SPEC_ALL term_type_cons)))) >>
      simp[safe_def_names_def] >> NO_TAC ) >>
    TRY (
      fs[consts_def] >>
      fs[ALL_DISTINCT_APPEND] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      METIS_TAC[] ) >>
    TRY (
      simp[def_ok_def,pred_setTheory.SUBSET_DEF] >>
      NO_TAC ) >>
    TRY (
      fs[good_defs_def] >>
      fs[consts_def,types_def] >>
      fs[ALL_DISTINCT_APPEND] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      METIS_TAC[] ) >>
    TRY (
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`asl`,`c`] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,23)) >>
      simp[] >> NO_TAC) >>
    TRY (
      simp[Once holSyntaxTheory.proves_cases] >>
      ntac 4 disj2_tac >> disj1_tac >>
      qexists_tac`Comb (Equal (typeof (Const s (typeof t)))) (Const s (typeof t))` >>
      simp[GSYM holSyntaxTheory.equation_def] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      rpt disj2_tac >>
      qexists_tac`[]` >> simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
      simp[] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`asl`,`c`] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,23)) >>
      simp[] >> NO_TAC) >>
    TRY (
      simp[Once holSyntaxTheory.proves_cases] >>
      ntac 4 disj2_tac >> disj1_tac >>
      qexists_tac`Comb (Equal (typeof t)) t` >>
      simp[GSYM holSyntaxTheory.equation_def] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      rpt disj2_tac >>
      qexists_tac`[]` >> simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,23)) >>
      simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      simp[] >> NO_TAC) >>
    TRY (
      qexists_tac`Const s (typeof tm1) (Defined tm1)` >>
      `tm has_type (typeof tm)` by METIS_TAC[holSyntaxTheory.WELLTYPED] >>
      `type defs (typeof tm) (typeof tm1) ∧ tm1 has_type (typeof tm1)` by (
        imp_res_tac has_type_IMP >>
        METIS_TAC[WELLTYPED_LEMMA] ) >>
      conj_tac >- (
        simp[Once term_cases,Once const_def_def] >>
        METIS_TAC[safe_def_names_def,term_type_cons] ) >>
      simp[Once proves_cases] >>
      disj2_tac >> disj1_tac >>
      qexists_tac`Equal (typeof (Const s (typeof tm1) (Defined tm1)))` >>
      Q.PAT_ABBREV_TAC`tyy = typeof (Const X Y Z)` >>
      simp[Once proves_cases] >>
      disj2_tac >> disj1_tac >>
      qexists_tac`tm1` >>
      simp[Once proves_cases] >>
      rpt disj2_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`[]` >> simp[] >>
      qunabbrev_tac`tyy` >>
      simp_tac std_ss [GSYM equation_def] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) >>
      simp[] >>
      imp_res_tac CLOSED_IMP >>
      rfs[pred_setTheory.SUBSET_DEF] >>
      imp_res_tac tvars_IMP >>
      imp_res_tac tyvars_IMP >>
      fs[] >> NO_TAC ) >>
    TRY (
      simp[Once holSyntaxTheory.proves_cases] >>
      disj2_tac >> disj1_tac >>
      qexists_tac`Equal (typeof (Const s (typeof tm)))` >>
      Q.PAT_ABBREV_TAC`tyy = typeof (Const X Y)` >>
      simp[Once holSyntaxTheory.proves_cases] >>
      disj2_tac >> disj1_tac >>
      qexists_tac`tm` >>
      qunabbrev_tac`tyy` >>
      simp_tac std_ss [GSYM holSyntaxTheory.equation_def] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      rpt disj2_tac >>
      qexists_tac`[]` >> simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
      simp[] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`asl`,`c`] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,23)) >>
      simp[]) >>
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
    simp[MEM_FLAT,MEM_MAP] >>
    discharge_hyps >- (
      srw_tac[boolSimps.DNF_ss][] >>
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
      imp_res_tac MEM_Constdef_const_def >>
      qexists_tac`t` >>
      simp[] >>
      METIS_TAC[good_defs_def,has_type_IMP,WELLTYPED_LEMMA,WELLTYPED,holSyntaxTheory.WELLTYPED_LEMMA,holSyntaxTheory.WELLTYPED]) >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) >>
    fs[WELLTYPED] >>
    fs[EVERY_MEM] >>
    res_tac >> fs[def_ok_def] >>
    imp_res_tac CLOSED_IMP >> simp[] >>
    imp_res_tac tvars_IMP >>
    fs[holSyntaxTheory.WELLTYPED] >>
    imp_res_tac has_type_IMP >>
    imp_res_tac tyvars_IMP >>
    imp_res_tac WELLTYPED_LEMMA >>
    METIS_TAC[]) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[seq_trans_def] >>
    simp[GSYM AND_IMP_INTRO] >>
    ntac 14 strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_abbrev_tac`P ⇒ A ∧ B ∧ C` >>
    `A` by (
      simp[Abbr`A`] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`[]`,`holSyntax$Comb t y`] >>
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
      simp[] >>
      map_every qexists_tac[`rep_type`,`y`] >>
      METIS_TAC[] ) >>
    simp[Abbr`A`] >>
    `B` by (
      simp[Abbr`B`] >>
      fs[good_defs_def,types_def,consts_def] >>
      fs[ALL_DISTINCT_APPEND] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      METIS_TAC[]) >>
    simp[Abbr`B`] >>
    simp[Abbr`C`] >>
    qmatch_abbrev_tac`P ⇒ A ∧ B ∧ C` >>
    `A` by (
      simp[Abbr`A`,def_ok_def] >> PROVE_TAC[] ) >>
    simp[Abbr`A`] >>
    simp[Abbr`P`] >>
    qunabbrev_tac`C` >>
    qho_match_abbrev_tac`(P asl c) ∨ (Q asl c) ∨ (R asl c) ⇒ B ∧ (C asl c)` >>
    `∀asl c. P asl c ⇒ C asl c` by (
      rpt gen_tac >>
      simp(List.map Abbr [`B`,`C`,`P`,`Q`,`R`]) >>
      strip_tac >>
      map_every qexists_tac[`h1`,`c1'`] >>
      fs[EVERY_MEM,EVERY2_EVERY] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      `safe_def_names defs (Typedef tyname t a r)` by (
        simp[safe_def_names_def] ) >>
      METIS_TAC[term_type_cons]) >>
    `∀asl c. Q asl c ⇒ C asl c` by (
      rpt gen_tac >>
      simp(List.map Abbr [`B`,`C`,`P`,`Q`,`R`]) >>
      rw[] >>
      qho_match_abbrev_tac`∃e1. term ddefs (t1 === t2) e1 ∧ [] |- e1` >>
      rfs[] >>
      qmatch_assum_abbrev_tac`Abbrev (t2 = Var x ty)` >>
      `welltyped t2` by METIS_TAC[holSyntaxTheory.WELLTYPED_CLAUSES] >>
      `typeof t2 = ty` by METIS_TAC[holSyntaxTheory.typeof_def] >>
      `welltyped t1` by simp[Abbr`t1`] >>
      `typeof t1 = ty` by simp[Abbr`t1`] >>
      `t1 === t2 has_type Bool` by (
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
      qspecl_then[`ddefs`,`t1`,`t2`]mp_tac (Q.GEN`defs`term_equation) >>
      simp[] >> disch_then kall_tac >>
      simp[Abbr`t2`] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once CONJ_COMM] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Abbr`ty`] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      `tyname ∉ {"bool";"ind";"fun"}` by fs[types_def] >> fs[] >>
      simp[Abbr`ddefs`] >>
      qpat_assum`term defs X c1`mp_tac >>
      simp[Once term_cases] >>
      simp[Once type_def_def] >>
      strip_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`x1` >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`MAP Tyvar (STRING_SORT (tvars t))` >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_asm1_tac >- (
        simp[EVERY2_MAP] >>
        simp[Once term_cases] >>
        match_mp_tac EVERY2_refl >>
        simp[] ) >>
      conj_asm1_tac >- (
        match_mp_tac (MP_CANON(CONJUNCT2 (UNDISCH(SPEC_ALL term_type_cons)))) >>
        simp[safe_def_names_def] ) >>
      simp[Abbr`t1`] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      `a ≠ "@"` by fs[consts_def] >> simp[] >>
      simp[Once const_def_def] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      `∃ty1. x1 has_type ty1 ∧ type defs (Fun rep_type Bool) ty1` by METIS_TAC[has_type_IMP] >>
      pop_assum mp_tac >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      rpt strip_tac >>
      pop_assum mp_tac >>
      simp[Once term_cases] >>
      strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`x1` >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`tx1` >>
      simp[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      `r ≠ "="` by fs[consts_def] >> simp[] >>
      simp[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Tyapp X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      simp[Once type_def_def] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      `safe_def_names defs (Typedef tyname t a r)` by simp[safe_def_names_def] >>
      `type (Typedef tyname t a r::defs) rep_type tx1` by METIS_TAC[term_type_cons] >>
      qexists_tac`x1` >> simp[] >>
      qexists_tac`tx1` >> simp[] >>
      qexists_tac`x1` >> simp[] >>
      qmatch_assum_abbrev_tac`LIST_REL ff ll rr` >>
      qexists_tac`rr` >> simp[] >>
      qexists_tac`x1` >> simp[] >>
      qexists_tac`rr` >> simp[] >>
      simp[Once type_def_def] >>
      qexists_tac`x1` >> simp[] >>
      qexists_tac`rr` >> simp[] >>
      reverse conj_tac >- (
        rw[] >>
        imp_res_tac MEM_Typedef_MEM_consts >>
        fs[consts_def]) >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,26)) >>
      imp_res_tac CLOSED_IMP >>
      simp[] >>
      qexists_tac`y1` >>
      imp_res_tac tvars_IMP >>
      simp[Abbr`rr`] >>
      `welltyped x1` by METIS_TAC[term_welltyped] >>
      imp_res_tac has_type_IMP >>
      ntac 2 (pop_assum mp_tac) >>
      simp[Once term_cases] >>
      rw[] >>
      imp_res_tac WELLTYPED_LEMMA >>
      rw[] ) >>
    `∀asl c. R asl c ⇒ C asl c` by (
      rpt gen_tac >>
      simp(List.map Abbr [`B`,`C`,`P`,`Q`,`R`]) >>
      rw[] >>
      qho_match_abbrev_tac`∃e1. term ddefs (t1 === t2) e1 ∧ [] |- e1` >>
      rfs[] >>
      `welltyped t` by METIS_TAC[holSyntaxTheory.welltyped_def] >>
      `typeof t1 = Bool` by (
        simp[Abbr`t1`] >>
        imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
        fs[holSyntaxTheory.WELLTYPED] ) >>
      `welltyped t1` by (
        simp[Abbr`t1`] >>
        METIS_TAC[holSyntaxTheory.WELLTYPED_LEMMA,holSyntaxTheory.welltyped_def] ) >>
      `t2 has_type Bool` by (
        simp[Abbr`t2`] >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
      `welltyped t2` by METIS_TAC[holSyntaxTheory.welltyped_def] >>
      `t1 === t2 has_type Bool` by (
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
        METIS_TAC[holSyntaxTheory.WELLTYPED_LEMMA] ) >>
      qspecl_then[`ddefs`,`t1`,`t2`]mp_tac (Q.GEN`defs`term_equation) >>
      simp[] >> disch_then kall_tac >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Abbr`t1`] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once CONJ_COMM] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
      simp[] >>
      qpat_assum`term defs X c1`mp_tac >>
      simp[Once term_cases] >>
      rw[] >>
      `∃ty1. x1 has_type ty1 ∧ type defs (Fun (typeof y) Bool) ty1` by METIS_TAC[has_type_IMP] >>
      pop_assum mp_tac >>
      simp[Once term_cases] >> rw[] >>
      pop_assum mp_tac >>
      simp[Once term_cases] >> rw[] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      qexists_tac`tx1` >>
      simp[RIGHT_EXISTS_AND_THM] >>
      `safe_def_names defs (Typedef tyname t a r)` by (
        simp[safe_def_names_def] ) >>
      conj_asm1_tac >- METIS_TAC[term_type_cons] >>
      qmatch_assum_abbrev_tac`Abbrev (t2 = t3 === t4)` >>
      `t3 === t4 has_type Bool` by (
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
        simp[Abbr`t3`,Abbr`t4`] ) >>
      qspecl_then[`ddefs`,`t3`,`t4`]mp_tac (Q.GEN`defs`term_equation) >>
      simp[] >>
      disch_then kall_tac >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Abbr`t3`] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once term_cases] >>
      simp[Abbr`ddefs`,Once type_def_def] >>
      `r ∉ {"=";"@"}` by fs[consts_def] >> fs[] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      simp[Abbr`t4`] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once term_cases] >>
      `tyname ∉ {"bool";"ind";"fun"}` by fs[types_def] >> fs[] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      `term (Typedef tyname t a r::defs) t x1` by METIS_TAC[term_type_cons] >>
      qexists_tac`x1`>>simp[] >>
      simp[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      qexists_tac`x1`>>simp[] >>
      qexists_tac`tx1`>>simp[] >>
      qexists_tac`x1`>>simp[] >>
      simp[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      `a ≠ "@"` by fs[consts_def] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Fun X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Q.SPEC`Var X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`tx1`>>simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`x1`>>simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`tx1`>>simp[] >>
      simp[Q.SPEC`Tyapp X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`tx1`>>simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`x1`>>simp[] >>
      qexists_tac`MAP Tyvar (STRING_SORT (tvars x1))` >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_asm1_tac >- (
        simp[EVERY2_MAP] >>
        simp[Once term_cases] >>
        imp_res_tac tvars_IMP >>
        simp[] >>
        match_mp_tac EVERY2_refl >>
        simp[] ) >>
      fs[safe_def_names_def] >>
      conj_tac >- METIS_TAC[MEM_Typedef_MEM_consts,consts_def,MEM_MAP,MEM_APPEND] >>
      HINT_EXISTS_TAC >> simp[] >>
      conj_tac >- METIS_TAC[MEM_Typedef_MEM_consts,consts_def,MEM_MAP,MEM_APPEND] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,27)) >>
      imp_res_tac CLOSED_IMP >>
      simp[] >>
      qexists_tac`y1` >>
      imp_res_tac WELLTYPED_LEMMA >>
      simp[]) >>
    qsuff_tac`B` >- METIS_TAC[] >>
    simp[Abbr`B`] >>
    simp[deftm_def] >>
    fs[Abbr`Q`,Abbr`R`,Abbr`C`] >>
    `typeof t = Fun rep_type Bool` by imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
    gen_tac >> strip_tac >>
    TRY BasicProvers.VAR_EQ_TAC >- (
      qpat_assum`term defs X c1`mp_tac >>
      simp[Once term_cases] >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      conj_tac >- (
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 3 disj2_tac >> disj1_tac >>
        qexists_tac`y` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        rpt disj2_tac >>
        qexists_tac`[]` >> simp[] >>
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
        simp[] >> PROVE_TAC[] ) >>
      qexists_tac`x1` >>
      conj_tac >- (
        match_mp_tac (MP_CANON(CONJUNCT2 (UNDISCH(SPEC_ALL term_type_cons)))) >>
        simp[safe_def_names_def] ) >>
      match_mp_tac (List.nth(CONJUNCTS proves_rules,10)) >>
      qexists_tac`y1` >>
      match_mp_tac (List.nth(CONJUNCTS proves_rules,14)) >>
      qexists_tac`Comb x1 y1` >>
      qexists_tac`[]` >>
      simp[] >> fs[] )
    >- (
      simp[] >>
      qmatch_assum_abbrev_tac`term ddefs (Comb abs (Comb rep var) === var) e1` >>
      conj_tac >- (
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 3 disj2_tac >> disj1_tac >>
        qexists_tac`Comb rep var` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 2 disj2_tac >> disj1_tac >>
        qexists_tac`Equal (typeof (Comb abs (Comb rep var)))` >>
        Q.PAT_ABBREV_TAC`ty = holSyntax$typeof X` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 1 disj2_tac >> disj1_tac >>
        qexists_tac`var` >>
        qunabbrev_tac`ty` >>
        simp_tac std_ss [GSYM holSyntaxTheory.equation_def] >>
        simp[Once holSyntaxTheory.proves_cases] >>
        rpt disj2_tac >>
        qexists_tac`[]` >> simp[] >>
        simp[Abbr`ddefs`] >>
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
        simp[] >>
        qexists_tac`x` >>
        HINT_EXISTS_TAC >>
        HINT_EXISTS_TAC >>
        simp[]) >>
      qmatch_assum_abbrev_tac`term ddefs (ll === rr) e1` >>
      `has_meaning e1` by METIS_TAC[soundness,sequent_def,MEM,EVERY_MEM] >>
      `welltyped (ll === rr)` by (
        imp_res_tac term_welltyped >>
        simp[] >>
        METIS_TAC[has_meaning_welltyped] ) >>
      qspecl_then[`ddefs`,`ll`,`rr`,`e1`]mp_tac (Q.GEN`defs`term_equation) >>
      fs[welltyped_equation] >>
      simp[Abbr`ll`] >>
      simp[Once term_cases] >> rw[] >>
      qmatch_assum_rename_tac`[] |- Comb abs1 rep1 === var1`[] >>
      qexists_tac`abs1` >> simp[] >>
      simp[Once proves_cases] >>
      ntac 5 disj2_tac >> disj1_tac >>
      qexists_tac`rep1` >>
      simp[Once proves_cases] >>
      ntac 2 disj2_tac >> disj1_tac >>
      qexists_tac`Equal (typeof (Comb abs1 rep1))` >>
      Q.PAT_ABBREV_TAC`ty = typeof X` >>
      simp[Once proves_cases] >>
      ntac 1 disj2_tac >> disj1_tac >>
      qexists_tac`var1` >>
      simp[Once proves_cases] >>
      rpt disj2_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`[]` >> simp[] >>
      simp_tac std_ss [Abbr`ty`,GSYM sholSyntaxTheory.equation_def] >>
      rw[] )
    >- (
      simp[] >>
      qmatch_assum_abbrev_tac`term ddefs (Comb abs (Comb rep var) === var) e1` >>
      conj_tac >- (
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 3 disj2_tac >> disj1_tac >>
        qexists_tac`var` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 2 disj2_tac >> disj1_tac >>
        qexists_tac`abs` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 2 disj2_tac >> disj1_tac >>
        qexists_tac`Equal (typeof (Comb abs (Comb rep var)))` >>
        Q.PAT_ABBREV_TAC`ty = holSyntax$typeof X` >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 1 disj2_tac >> disj1_tac >>
        qexists_tac`var` >>
        qunabbrev_tac`ty` >>
        simp_tac std_ss [GSYM holSyntaxTheory.equation_def] >>
        simp[Once holSyntaxTheory.proves_cases] >>
        rpt disj2_tac >>
        qexists_tac`[]` >> simp[] >>
        simp[Abbr`ddefs`] >>
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
        simp[] >>
        qexists_tac`x` >>
        HINT_EXISTS_TAC >>
        HINT_EXISTS_TAC >>
        simp[]) >>
      qmatch_assum_abbrev_tac`term ddefs (ll === rr) e1` >>
      `has_meaning e1` by METIS_TAC[soundness,sequent_def,MEM,EVERY_MEM] >>
      `welltyped (ll === rr)` by (
        imp_res_tac term_welltyped >>
        simp[] >>
        METIS_TAC[has_meaning_welltyped] ) >>
      qspecl_then[`ddefs`,`ll`,`rr`,`e1`]mp_tac (Q.GEN`defs`term_equation) >>
      fs[welltyped_equation] >>
      simp[Abbr`ll`] >>
      simp[Once term_cases] >> rw[] >>
      qmatch_assum_rename_tac`[] |- Comb abs1 repa1 === var1`[] >>
      qpat_assum`term ddefs X repa1`mp_tac >>
      simp[Once term_cases] >> strip_tac >>
      qmatch_assum_rename_tac`term ddefs rep rep1`[] >>
      qexists_tac`rep1` >> simp[] >>
      simp[Once proves_cases] >>
      ntac 5 disj2_tac >> disj1_tac >>
      qexists_tac`var1` >>
      simp[Once proves_cases] >>
      ntac 2 disj2_tac >> disj1_tac >>
      qexists_tac`abs1` >>
      simp[Once proves_cases] >>
      ntac 2 disj2_tac >> disj1_tac >>
      qexists_tac`Equal (typeof (Comb abs1 (Comb rep1 var1)))` >>
      Q.PAT_ABBREV_TAC`ty = typeof X` >>
      simp[Once proves_cases] >>
      ntac 1 disj2_tac >> disj1_tac >>
      qexists_tac`var1` >>
      simp[Once proves_cases] >>
      rpt disj2_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`[]` >> simp[] >>
      simp_tac std_ss [Abbr`ty`,GSYM sholSyntaxTheory.equation_def] >>
      imp_res_tac term_type_11 >>
      rw[] ) >>
    conj_tac >- (
      simp[Once holSyntaxTheory.proves_cases] >>
      ntac 4 disj2_tac >> disj1_tac >>
      qexists_tac`Comb (Equal (typeof t')) t'` >>
      simp[GSYM holSyntaxTheory.equation_def] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      rpt disj2_tac >>
      qexists_tac`[]` >> simp[] >>
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,25)) >>
      simp[] >>
      qexists_tac`ARB` >>
      HINT_EXISTS_TAC >>
      HINT_EXISTS_TAC >>
      simp[] >> disj1_tac >>
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,13)) >>
      METIS_TAC[] ) >>
    res_tac >>
    qexists_tac`t1` >>
    simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT2 (UNDISCH(SPEC_ALL term_type_cons)))) >>
    simp[safe_def_names_def]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    qho_match_abbrev_tac`∃c1. term defs (l === r) c1 ∧ P c1` >> rfs[] >>
    qspecl_then[`l`,`r`]mp_tac term_equation >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    simp[Abbr`l`,Abbr`r`] >>
    disch_then kall_tac >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`ty1` >> simp[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`ty1'` >>
    qexists_tac`ty1` >> simp[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`ty1` >> simp[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    qexists_tac`ty1`>>simp[]>>
    qexists_tac`ty1'` >> simp[Abbr`P`] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,28)) >>
    rw[] ) >>
  rw[seq_trans_def] >>
  qexists_tac`h1` >> rw[] >>
  simp[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  qpat_assum`term defs X c1`mp_tac >>
  simp[Once term_cases] >>
  rw[] >>
  qexists_tac`x1` >> rw[] >>
  rw[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  rw[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  rw[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  rw[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  fs[holSyntaxTheory.WELLTYPED] >>
  imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
  fs[] >> rw[] >>
  qspecl_then[`p`,`Fun (typeof w) Bool`]mp_tac has_type_IMP >>
  simp[] >>
  disch_then(qspecl_then[`defs`,`x1`]mp_tac) >>
  simp[] >>
  simp[Once term_cases] >>
  srw_tac[boolSimps.DNF_ss][] >>
  qexists_tac`x1` >>
  qexists_tac`tx1` >>
  qexists_tac`tx1` >>
  rw[] >>
  simp[Once term_cases] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,29)) >>
  qexists_tac`y1` >> rw[] >>
  qpat_assum`type Y Bool Z`mp_tac >>
  simp[Once term_cases] >> rw[] >>
  rw[])

val soundness = store_thm("soundness",
  ``∀dh t. dh |- t ⇒ hol_seq (dh,t)``,
  Cases >> rw[hol_seq_def] >>
  METIS_TAC[proves_IMP,soundness])

val type_ok_Bool = store_thm("type_ok_Bool",
  ``∀d. context_ok d ⇒ type_ok d Bool``,
  rw[] >>
  simp[Once holSyntaxTheory.proves_cases] >>
  disj1_tac >>
  qexists_tac`Var x (Tyvar a) === Var x (Tyvar a)` >>
  simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
  simp[Once holSyntaxTheory.proves_cases] >>
  rpt disj2_tac >>
  qexists_tac`[]` >>
  simp[] >>
  simp[Once holSyntaxTheory.proves_cases] >>
  disj1_tac >>
  qexists_tac`Var x (Tyvar a)` >>
  simp[] >>
  simp[Once holSyntaxTheory.proves_cases] >>
  disj1_tac >>
  simp[Once holSyntaxTheory.proves_cases])
val _ = export_rewrites["type_ok_Bool"]

val consistency = store_thm("consistency",
  ``(∀d. context_ok d ⇒ (d,[]) |- (Var x Bool === Var x Bool)) ∧
    (∀d. ¬ ((d,[]) |- Var x Bool === Var (VARIANT (Var x Bool) x Bool) Bool))``,
  conj_tac >- (
    rpt strip_tac >>
    simp[Once holSyntaxTheory.proves_cases] >>
    disj1_tac >>
    qexists_tac`Var x Bool` >>
    simp[] >>
    simp[Once holSyntaxTheory.proves_cases] >>
    disj1_tac >>
    simp[type_ok_Bool] ) >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  imp_res_tac proves_IMP >>
  fs[seq_trans_def] >>
  qmatch_assum_abbrev_tac`term d (l === r) c1` >>
  qspecl_then[`d`,`l`,`r`,`c1`]mp_tac (Q.GEN`defs`term_equation) >>
  simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
  simp[Abbr`l`,Abbr`r`] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  METIS_TAC[consistency])

(*
val proves_cons_def = store_thm("proves_cons_def",
  ``∀defs h c d. (defs,h) |- c ⇒ context_ok (d::defs) ⇒ (d::defs,h) |- c``,
  rw[] >>
  Cases_on`d` >- (
    match_mp_tac(List.nth(CONJUNCTS proves_rules,23)) >>
    imp_res_tac proves_IMP >>
    fs[def_ok_def,deftm_def,pred_setTheory.SUBSET_DEF,good_defs_def]

val proves_append_defs = store_thm("proves_append_defs",
  ``(∀defs ty. type_ok defs ty ⇒ ∀d. context_ok (d++defs) ⇒ type_ok (d++defs) ty) ∧
    (∀defs tm. term_ok defs tm ⇒ ∀d. context_ok (d++defs) ⇒ term_ok (d++defs) tm) ∧
    (∀defs. context_ok defs ⇒ ∀n. context_ok (DROP n defs)) ∧
    (∀dh c. dh |- c ⇒ (∀n. context_ok (DROP n (FST dh))) ∧ ∀d. context_ok (d++(FST dh)) ⇒ (d++(FST dh),SND dh) |- c)``,
  HO_MATCH_MP_TAC holSyntaxTheory.proves_strongind >>
  conj_tac >- ( rw[] >> simp[Once term_cases,Once proves_cases] ) >>
  conj_tac >- ( rw[] >> simp[Once term_cases,Once proves_cases] ) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,2)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,3)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,4)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,5)) >> METIS_TAC[WELLTYPED_CLAUSES]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,6)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,7)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,8)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,9)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,10)) >> METIS_TAC[MEM]) >>
  conj_tac >- ( rw[] >> MATCH_ACCEPT_TAC(List.nth(CONJUNCTS proves_rules,11))) >>
  conj_tac >- rw[] >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,13)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,14)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,15)) >> METIS_TAC[WELLTYPED_CLAUSES]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,16)) >> METIS_TAC[NOT_EXISTS]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,17)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,18)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,19)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,20)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,21)) >> METIS_TAC[]) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,22)) >> METIS_TAC[]) >>
  conj_tac >- (
    rw[] >- (
      rw[] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,12)) >>
      map_every qexists_tac[`asl`,`c`] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,23)) >>
      simp[] ) >>
    METIS_TAC[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  conj_tac >- ( rw[] >> match_mp_tac(List.nth(CONJUNCTS proves_rules,24)) >> simp[] ) >>
  conj_tac >- (
    rw[] >> rw[] >>
    TRY (
      match_mp_tac(List.nth(CONJUNCTS proves_rules,12)) >>
      map_every qexists_tac[`[]`,`Comb t y`] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) >>
      simp[] >>
      METIS_TAC[] )
    >- METIS_TAC[rich_listTheory.CONS_APPEND,APPEND_ASSOC] >>
    Induct_on`d'`>>rw[]

    qmatch_abbrev_tac`p1 ∨ p2 ∨ p3 ⇒ q` >>
    strip_tac >> qunabbrev_tac`q` >>
    rpt strip_tac >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) 
*)

val _ = export_theory()
