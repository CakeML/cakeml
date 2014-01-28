open HolKernel Parse boolLib bossLib lcsymtacs miscTheory miscLib;
val _ = temp_tight_equality()
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

val _ = Hol_datatype`
  deftag = Consttag of num => (string # holSyntax$term) list => holSyntax$term
         | Abstag of holSyntax$term
         | Reptag of holSyntax$term`

val const_def_def = Define `
  const_def n defs =
    case defs of
    | [] => NONE
    | (Constdef eqs p::defs) =>
         (case find_index n (MAP FST eqs) 0 of
         | SOME i => SOME (Consttag i eqs p)
         | NONE => const_def n defs)
    | (Typedef name tm abs rep::defs) =>
         if n = abs then SOME (Abstag tm) else
         if n = rep then SOME (Reptag tm) else const_def n defs
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
   (const_def s defs = SOME (Consttag i eqs p)) /\
   MAP FST eqs = MAP FST eqs1 /\
   LIST_REL (term defs) (MAP SND eqs) (MAP SND eqs1) /\
   term defs p p1 ==>
   term defs (Const s ty) (Const s ty1 (Defined i eqs1 p1))) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (Abstag tm)) /\
   (type_def n defs = SOME (tm,s,s')) /\
   (∀tm n' s'. (MEM (Typedef n' tm s s') defs) ⇒ (n' = n)) /\
   term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (Tyabs n tm1))) /\
  (type defs ty ty1 /\
   (const_def s defs = SOME (Reptag tm)) /\
   (type_def n defs = SOME (tm,s',s)) /\
   (∀tm n' s'. (MEM (Typedef n' tm s' s) defs) ⇒ (n' = n)) /\
   term defs tm tm1 ==>
   term defs (Const s ty) (Const s ty1 (Tyrep n tm1)))`

val seq_trans_def = Define `
  seq_trans ((defs,h),c) (h1,c1) <=>
    EVERY2 (term defs) h h1 /\ term defs c c1`;


(* -- part 2 -- *)

val mem = ``mem:'U->'U->bool``
val indset = ``indset:'U``
val ch = ``ch:'U->'U``
val s = ``(^mem,^indset,^ch)``

val hol_seq_def = xDefine "hol_seq"`
  hol_seq0 ^s ((defs,hyps),tm) = ?h c. seq_trans ((defs,hyps),tm) (h,c) /\ h |= c`;
val _ = Parse.overload_on("hol_seq",``hol_seq0 M``)

(* -- part 3 -- *)

val type_def_MEM = prove(
  ``∀defs n tm x y. type_def n defs = SOME (tm,x,y) ⇒ MEM (Typedef n tm x y) defs``,
  Induct >> simp[Once type_def_def] >>
  Cases >> simp[] >> rw[])

val const_def_MEM_0 = prove(
  ``∀defs n i eqs tm. const_def n defs = SOME (Consttag i eqs tm) ⇒
      MEM (Constdef eqs tm) defs ∧
      find_index n (MAP FST eqs) 0 = SOME i``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[] >>
  TRY(pop_assum mp_tac >> BasicProvers.CASE_TAC) >>
  METIS_TAC[])

val const_def_MEM_1 = prove(
  ``∀defs n tm. const_def n defs = SOME (Abstag tm) ⇒ ∃x y z. MEM (Typedef x y n z) defs``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[] >>
  TRY(pop_assum mp_tac >> BasicProvers.CASE_TAC) >>
  METIS_TAC[])

val const_def_MEM_2 = prove(
  ``∀defs n m tm. const_def n defs = SOME (Reptag tm) ⇒ ∃x y z. MEM (Typedef x y z n) defs``,
  Induct >> simp[Once const_def_def] >>
  Cases >> simp[] >> rw[] >>
  TRY(pop_assum mp_tac >> BasicProvers.CASE_TAC) >>
  METIS_TAC[])

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
  ``∀defs n eqs tm. MEM (Constdef eqs tm) defs ∧ MEM n (MAP FST eqs) ⇒
    MEM n (MAP FST (FLAT (MAP consts_aux defs)))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  fs[MEM_MAP,EXISTS_PROD] >>
  METIS_TAC[])

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
  (PairCases_on`x` ORELSE Cases_on`x`)>>
  imp_res_tac type_def_MEM >>
  imp_res_tac MEM_Typedef_MEM_types >>
  fs[] >> rfs[] >>
  imp_res_tac const_def_MEM_0 >>
  imp_res_tac const_def_MEM_1 >>
  imp_res_tac const_def_MEM_2 >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  imp_res_tac MEM_Typedef_MEM_consts >>
  imp_res_tac find_index_is_MEM >>
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
  >> strip_tac >> simp[Once term_cases] >> rw[] >> rfs[] >>
  TRY (
    fs[Once LIST_EQ_REWRITE] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[UNCURRY,EL_MAP] >> rfs[UNCURRY,EL_MAP] >>
    METIS_TAC[PAIR_EQ,pair_CASES,FST,SND]) >>
  METIS_TAC[type_def_MEM,const_def_MEM_1,const_def_MEM_2
           ,const_def_MEM_0,MEM_Constdef_MEM_consts,MEM_Typedef_MEM_consts])

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

val has_type_IMP = store_thm("has_type_IMP",
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
     TRY (
       fs[EVERY_MEM,EVERY2_EVERY,Once LIST_EQ_REWRITE] >>
       rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
       fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
       fs[UNCURRY,EL_MAP] >>
       rfs[UNCURRY,EL_MAP] >>
       metis_tac[term_type_11,PAIR_EQ,pair_CASES,FST,SND] ) >>
     metis_tac[term_type_11,const_def_MEM_1,const_def_MEM_2,const_def_MEM_0
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
  (safe_def_names defs (Constdef eqs p) ⇔ DISJOINT (set (MAP FST eqs)) (set (MAP FST (consts defs)))) ∧
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
    qexists_tac`eqs` >>
    qexists_tac`tm` >>
    res_tac >> simp[] >>
    reverse conj_tac >- (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,UNCURRY] ) >>
    Cases_on`d`>>simp[Once const_def_def] >>
    BasicProvers.CASE_TAC >> rw[] >>
    imp_res_tac const_def_MEM_0 >>
    imp_res_tac find_index_is_MEM >>
    imp_res_tac MEM_Constdef_MEM_consts >>
    fs[safe_def_names_def,consts_def] >>
    rw[] >> fs[pred_setTheory.IN_DISJOINT] >>
    METIS_TAC[])
  >- (
    qexists_tac`s'` >> qexists_tac`tm` >>
    imp_res_tac const_def_MEM_1 >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    res_tac >> simp[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    BasicProvers.CASE_TAC >>
    rw[] >> rw[Once type_def_def] >>
    fs[safe_def_names_def,pred_setTheory.IN_DISJOINT] >>
    imp_res_tac type_def_MEM >>
    imp_res_tac MEM_Typedef_MEM_types >>
    imp_res_tac find_index_is_MEM >>
    fs[types_def,consts_def] >> rw[] >>
    METIS_TAC[])
  >- (
    qexists_tac`s'` >> qexists_tac`tm` >>
    imp_res_tac const_def_MEM_2 >>
    fsrw_tac[ARITH_ss][] >>
    imp_res_tac MEM_Typedef_MEM_consts >>
    res_tac >> simp[] >>
    Cases_on`d`>>simp[Once const_def_def] >>
    BasicProvers.CASE_TAC >>
    rw[] >> rw[Once type_def_def] >>
    fs[safe_def_names_def,pred_setTheory.IN_DISJOINT] >>
    imp_res_tac type_def_MEM >>
    imp_res_tac MEM_Typedef_MEM_types >>
    imp_res_tac find_index_is_MEM >>
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
      qpat_assum`pair$, X Y  = Z`(assume_tac o SYM) >> fs[] >- (
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
  ``∀defs n i eqs p.
    ALL_DISTINCT (MAP FST (consts defs)) ∧
    MEM (Constdef eqs p) defs ∧
    find_index n (MAP FST eqs) 0 = SOME i
    ⇒ const_def n defs = SOME (Consttag i eqs p)``,
  Induct >> simp[] >>
  Cases >> simp[consts_def,consts_aux_def] >>
  rw[Once const_def_def] >> simp[] >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  fs[consts_def] >> fs[] >>
  TRY(BasicProvers.CASE_TAC)>>
  spose_not_then strip_assume_tac >>
  res_tac >>
  imp_res_tac MEM_Constdef_MEM_consts >>
  imp_res_tac find_index_is_MEM >>
  fs[consts_def] >> fs[] >>
  fs[ALL_DISTINCT_APPEND] >-
    METIS_TAC[] >>
  fs[MEM_MAP,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EXISTS_PROD,MEM_FLAT] >>
  res_tac >>
  fs[consts_aux_def] >>
  METIS_TAC[])

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

fun memdef n =
  last(CONJUNCTS holSyntaxTheory.proves_rules)
  |> SPEC_ALL |> concl |> dest_imp |> fst |> strip_conj
  |> C (curry List.nth) n

val term_equation_matchable = store_thm("term_equation_matchable",
  ``∀z x y x1 y1 defs.
    z = x1 === y1 ∧ term defs x x1 ∧ term defs y y1 ∧ x === y has_type Bool ∧ good_defs defs
    ⇒ term defs (x === y) z``,
  METIS_TAC[term_equation])

val type_Tyvar = store_thm("type_Tyvar",
  ``type defs (Tyvar x) z ⇔ (z = Tyvar x)``,
  simp[Once term_cases])

val type_Fun = store_thm("type_Fun",
  ``good_defs defs ⇒
    (type defs (Fun x y) z ⇔ ∃x1 y1. type defs x x1 ∧ type defs y y1 ∧ (z = Fun x1 y1))``,
  simp[Once term_cases] >> METIS_TAC[] )

val type_Bool = store_thm("type_Bool",
  ``good_defs defs ⇒ (type defs Bool z ⇔ z = Bool)``,
  simp[Once term_cases])

val term_Var = store_thm("term_Var",
  ``term defs (Var x ty) z ⇔ ∃ty1. type defs ty ty1 ∧ (z = Var x ty1)``,
  simp[Once term_cases] >> METIS_TAC[])

val term_Abs = store_thm("term_Abs",
  ``term defs (Abs x ty t) z ⇔ ∃ty1 t1. type defs ty ty1 ∧ term defs t t1 ∧ (z = Abs x ty1 t1)``,
  simp[Once term_cases] >> METIS_TAC[])

val _ = export_rewrites["type_Tyvar","type_Fun","type_Bool","term_Var","term_Abs"]

val term_Truth = store_thm("term_Truth",
  ``good_defs defs ∧ ^(memdef 1)
    ⇒
    term defs Truth TT``,
  rw[good_defs_def] >>
  simp[Once term_cases,TT_def] >>
  simp[Once term_cases,typeof_shadow_def] >>
  simp[PULL_EXISTS,EXISTS_PROD] >>
  qspecl_then[`defs`,`"T"`]imp_res_tac MEM_Constdef_const_def >>
  fs[find_index_def] >>
  conj_asm1_tac >- (
    match_mp_tac term_equation_matchable >>
    simp[good_defs_def,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    rpt (simp[Once term_cases]) ) >>
  match_mp_tac term_equation_matchable >>
  simp[good_defs_def,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
  simp[Once term_cases] >>
  simp[Once term_cases,holSyntaxTheory.equation_def,typeof_shadow_def] >>
  simp[Once term_cases,equation_def] )

val term_And = store_thm("term_And",
  ``good_defs defs ∧
    ^(memdef 1) ∧
    ^(memdef 2) ∧
    p has_type Bool ∧ q has_type Bool ∧
    term defs p p1 ∧ term defs q q1
    ⇒
    term defs (And p q) (AN p1 q1)``,
  rw[] >>
  imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
  simp[Once term_cases,AN_def,holSyntaxTheory.WELLTYPED] >>
  ntac 6 (simp[Once term_cases]) >>
  qmatch_assum_abbrev_tac`MEM (Constdef eqs t) defs` >>
  simp[PULL_EXISTS] >>
  map_every qexists_tac[`eqs`,`t`] >>
  simp[Abbr`eqs`] >>
  conj_tac >- (
    match_mp_tac MEM_Constdef_const_def >>
    simp[find_index_def] >>
    fs[good_defs_def]) >>
  simp[holSyntaxTheory.WELLTYPED,typeof_shadow_def] >>
  conj_asm1_tac >- (
    match_mp_tac term_equation_matchable >>
    simp[] >>
    ntac 4 (simp[Once term_cases]) >>
    conj_tac >- ( match_mp_tac term_Truth >> simp[] ) >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
  simp[Once holSyntaxTheory.has_type_cases] >>
  simp[Once holSyntaxTheory.has_type_cases] >>
  qunabbrev_tac`t` >>
  match_mp_tac term_equation_matchable >>
  simp[] >>
  conj_tac >- (
    simp[equation_def,holSyntaxTheory.equation_def] ) >>
  simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation])

val term_Implies = store_thm("term_Implies",
  ``good_defs defs ∧ ^(list_mk_conj(map memdef [1,2,3])) ∧
    p has_type Bool ∧ q has_type Bool ∧
    term defs p p1 ∧ term defs q q1
    ⇒
    term defs (Implies p q) (IM p1 q1)``,
  rw[] >>
  imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
  simp[Once term_cases,IM_def,holSyntaxTheory.WELLTYPED] >>
  ntac 2 (simp[Once term_cases]) >>
  qmatch_assum_abbrev_tac`MEM (Constdef eqs t) defs` >>
  simp[PULL_EXISTS] >>
  map_every qexists_tac[`eqs`,`t`] >>
  simp[Abbr`eqs`,Abbr`t`] >>
  conj_tac >- (
    match_mp_tac MEM_Constdef_const_def >>
    simp[find_index_def] >>
    fs[good_defs_def]) >>
  simp[holSyntaxTheory.WELLTYPED,typeof_shadow_def] >>
  conj_asm1_tac >- (
    match_mp_tac term_equation_matchable >> simp[] >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation,good_defs_def] >>
    match_mp_tac term_And >>
    simp[] >>
    ntac 2 (simp[Once holSyntaxTheory.has_type_cases])) >>
  ntac 2 (simp[Once holSyntaxTheory.has_type_cases]) >>
  match_mp_tac term_equation_matchable >>
  simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
  simp[equation_def,holSyntaxTheory.equation_def])

val term_Forall = store_thm("term_Forall",
  ``good_defs defs ∧ ^(memdef 1) ∧ ^(memdef 4) ∧
    term defs (Var x ty) (Var x1 ty1) ∧
    p has_type Bool ∧
    term defs p p1 ∧ type defs ty ty1
    ⇒
    term defs (Forall x ty p) (FA x ty1 p1)``,
  rw[] >>
  imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
  simp[Once term_cases,FA_def,holSyntaxTheory.WELLTYPED] >>
  simp[Once term_cases] >>
  qmatch_assum_abbrev_tac`MEM (Constdef eqs t) defs` >>
  simp[PULL_EXISTS] >>
  map_every qexists_tac[`eqs`,`t`] >>
  simp[Abbr`eqs`,Abbr`t`] >>
  conj_tac >- (
    match_mp_tac MEM_Constdef_const_def >>
    simp[find_index_def] >>
    fs[good_defs_def]) >>
  simp[holSyntaxTheory.WELLTYPED,typeof_shadow_def] >>
  conj_asm1_tac >- (
    match_mp_tac term_equation_matchable >>
    simp[] >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
    match_mp_tac term_Truth >> simp[] ) >>
  simp[Once holSyntaxTheory.has_type_cases] >>
  simp[Once holSyntaxTheory.has_type_cases] >>
  match_mp_tac term_equation_matchable >>
  simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
  simp[equation_def,holSyntaxTheory.equation_def])

val def_ok_def = Define`
  (def_ok (Constdef eqs p) ⇔
    EVERY (λt. CLOSED t ∧ set (tvars t) ⊆ set (tyvars (typeof t)))
     (MAP SND eqs) ∧
    ALL_DISTINCT (MAP FST eqs) ∧
    (∀x ty. VFREE_IN (Var x ty) p ⇒ ∃t. MEM (x,t) eqs ∧ typeof t = ty)) ∧
  (def_ok (Typedef n t a r) ⇔ ∃rty. CLOSED t ∧ t has_type Fun rty Bool)`

val deftm_def = Define`
  deftm (Constdef eqs p) =
    p::MAP SND eqs ++
    MAP (λ(s,t).Const s (typeof t)) eqs ∧
  deftm (Typedef n t a r) =
  let rty = domain(typeof t) in
  let aty = Tyapp n (MAP Tyvar (STRING_SORT (tvars t))) in
    [t;Const a (Fun rty aty);Const r (Fun aty rty)]`

val defcnds_ok_def = Define`
  (defcnds_ok [] ⇔ T) ∧
  (defcnds_ok ((Typedef _ t _ _)::defs) ⇔ (∃w. (defs,[]) |- Comb t w) ∧ defcnds_ok defs) ∧
  (defcnds_ok ((Constdef eqs p)::defs) ⇔
    (defs, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- p (* ∧
    term_ok defs p ∧ EVERY (term_ok defs) (MAP SND eqs)*) ∧ defcnds_ok defs)`

val defthm_def = Define`
  defthm (Constdef eqs p) = [(MAP (λ(s,t). Var s (typeof t) === t) eqs, p)] ∧
  defthm _ = []`

val proves_IMP = store_thm("proves_IMP",
  ``(∀defs ty. type_ok defs ty ⇒ context_ok defs ∧ good_defs defs ∧ ∃ty1. type defs ty ty1 ∧ type_ok ty1) ∧
    (∀defs tm. term_ok defs tm ⇒ context_ok defs ∧ good_defs defs ∧ ∃tm1. term defs tm tm1 ∧ term_ok tm1) ∧
    (∀defs. context_ok defs ⇒
      good_defs defs ∧
      EVERY def_ok defs ∧
      defcnds_ok defs ∧
      (∀t. MEM t (FLAT (MAP deftm defs)) ⇒ term_ok defs t ∧ ∃t1. term defs t t1 ∧ term_ok t1) ∧
      (∀h c. MEM (h,c) (FLAT (MAP defthm defs)) ⇒ ∃h1 c1. seq_trans ((defs,h),c) (h1,c1) ∧ h1 |- c1)) ∧
    (∀dh c. dh |- c ⇒
      context_ok (FST dh) ∧
      good_defs (FST dh) ∧
      EVERY def_ok (FST dh) ∧
      defcnds_ok (FST dh) ∧
      (∀t. MEM t (FLAT (MAP deftm (FST dh))) ⇒ term_ok (FST dh) t ∧ ∃t1. term (FST dh) t t1 ∧ term_ok t1) ∧
      (∀h c. MEM (h,c) (FLAT (MAP defthm (FST dh))) ⇒ ∃h1 c1. seq_trans ((FST dh,h),c) (h1,c1) ∧ h1 |- c1) ∧
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
    rpt gen_tac >> simp[] >>
    rw[] >> fs[] >>
    qexists_tac`t1` >> rw[] >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[] >>
    fs[MEM_FLAT,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    res_tac >>
    fs[deftm_def,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO,EXISTS_PROD] >>
    METIS_TAC[] ) >>
  conj_tac >- (
    rw[seq_trans_def,EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,14),MEM,MEM_EL] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    rw[good_defs_def] >>
    rw[types_def] >>
    rw[consts_def] >>
    rw[defcnds_ok_def]
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
    `welltyped tm1` by METIS_TAC[proves_welltyped] >>
    `welltyped tm` by METIS_TAC[term_welltyped] >>
    simp[] >> strip_tac >>
    qexists_tac`tm1 === tm1` >>
    simp[] >>
    METIS_TAC[List.nth(CONJUNCTS proves_rules,15)] ) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    `∀t. MEM t (c1::h1) ∨ MEM t (c1'::h1') ⇒ t has_type Bool` by (
      imp_res_tac proves_welltyped >>
      fs[EVERY_MEM] >>
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
      imp_res_tac proves_welltyped >> fs[EVERY_MEM] >>
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
      imp_res_tac proves_welltyped >>
      fs[] ) >>
    `l === r has_type Bool` by (
      simp[GSYM welltyped_equation] >>
      metis_tac[term_welltyped,welltyped_def] ) >>
    simp[] >> strip_tac >>
    qexists_tac`Abs x ty1 x1 === Abs x ty1 y1` >>
    qspecl_then[`Abs x ty l`,`Abs x ty r`,`Abs x ty1 x1 === Abs x ty1 y1`]mp_tac term_equation >>
    fs[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    strip_tac >>
    simp[Q.SPEC`Abs X Y Z`(CONJUNCT2 (SPEC_ALL term_cases))] >>
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
    `welltyped tm1` by METIS_TAC[proves_welltyped] >>
    `welltyped tm` by METIS_TAC[term_welltyped] >>
    simp[] >> strip_tac >>
    srw_tac[boolSimps.DNF_ss][] >>
    simp[Once term_cases] >>
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
      imp_res_tac proves_welltyped >>
      fs[EVERY_MEM] >>
      METIS_TAC[welltyped_def] ) >>
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
        imp_res_tac proves_welltyped >> fs[] ) >>
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
      qexists_tac`ty1` >>
      simp[]) >>
    `∀t. MEM t (c1::h1) ⇒ welltyped t` by (
      imp_res_tac proves_welltyped >>
      fs[EVERY_MEM] >>
      METIS_TAC[welltyped_def] ) >>
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
      qpat_assum`pair$, X Y=Z`(assume_tac o SYM) >> fs[]>>
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
    qpat_assum`pair$, X Y=Z`(assume_tac o SYM) >> fs[]>>
    fs[Q.SPECL[`Var X Y`](CONJUNCT2 (SPEC_ALL term_cases))] >>
    METIS_TAC[has_type_IMP,term_type_11] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[seq_trans_def,deftm_def] >>
    strip_tac >>
    conj_asm1_tac >- (
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`asl`,`c`] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
      simp[]) >>
    conj_asm1_tac >- (
      fs[good_defs_def] >>
      fs[consts_def,types_def] >>
      fs[ALL_DISTINCT_APPEND] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once types_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[Once consts_aux_def] >>
      simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      METIS_TAC[] ) >>
    conj_asm1_tac >- (
      simp[def_ok_def,pred_setTheory.SUBSET_DEF] >>
      fs[ALL_DISTINCT_APPEND,MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[]) >>
    `∀t. MEM t (MAP SND eqs) ⇒ term_ok defs t` by (
      simp[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
      qx_genl_tac[`t`,`s`] >> strip_tac >>
      qsuff_tac`term_ok defs (Var s (typeof t) === t)` >- (
        simp[holSyntaxTheory.equation_def] >>
        strip_tac >>
        simp[Once holSyntaxTheory.proves_cases] >>
        METIS_TAC[] ) >>
      simp[Once holSyntaxTheory.proves_cases] >>
      rpt disj2_tac >>
      qmatch_assum_abbrev_tac`(defs,hh) |- cc` >>
      map_every qexists_tac[`hh`,`cc`] >>
      simp[Abbr`hh`,MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    conj_asm1_tac >- simp[defcnds_ok_def] >>
    simp[DISJ_IMP_THM] >>
    simp[FORALL_AND_THM] >>
    simp[GSYM CONJ_ASSOC] >>
    Q.PAT_ABBREV_TAC`ddefs = X::defs` >>
    `∀t. term_ok defs t ⇒ term_ok ddefs t` by (
      rw[] >>
      qsuff_tac`(ddefs,[]) |- (t === t)` >- (
        rw[holSyntaxTheory.equation_def] >>
        simp[Once holSyntaxTheory.proves_cases] >>
        ntac 4 disj2_tac >> disj1_tac >>
        simp[Once holSyntaxTheory.proves_cases] >>
        METIS_TAC[] ) >>
      qunabbrev_tac`ddefs` >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
      simp[] >>
      match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,14)) >>
      simp[] ) >>
    `∀t t1. term defs t t1 ⇒ term ddefs t t1` by (
      rw[] >>
      qunabbrev_tac`ddefs` >>
      match_mp_tac(MP_CANON (CONJUNCT2 (UNDISCH (SPEC_ALL term_type_cons)))) >>
      simp[safe_def_names_def,pred_setTheory.IN_DISJOINT] >>
      fs[ALL_DISTINCT_APPEND] >> METIS_TAC[] ) >>
    `∀s t. MEM (s,t) eqs ⇒
      ∃e. term defs (Var s (typeof t) === t) e ∧ term_ok e ∧ welltyped e` by (
        fs[EVERY2_EVERY,EVERY_MEM] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP,UNCURRY] >>
        fs[MEM_EL] >> rw[] >>
        qexists_tac`EL n h1'` >>
        conj_tac >- METIS_TAC[FST,SND] >>
        conj_asm1_tac >- (
          simp[Once proves_cases,MEM_EL] >>
          METIS_TAC[]) >>
        METIS_TAC[proves_welltyped] ) >>
    `term_ok defs c'` by (
      simp[Once holSyntaxTheory.proves_cases] >>
      METIS_TAC[] ) >>
    conj_asm1_tac >- (
      first_x_assum match_mp_tac >>
      simp[] ) >>
    conj_asm1_tac >- (
      res_tac >>
      qexists_tac`c1'` >>
      simp[] >>
      simp[Once proves_cases] >>
      METIS_TAC[] ) >>
    conj_asm1_tac >- (
      ntac 2 strip_tac >> simp[] >>
      pop_assum mp_tac >>
      simp[MEM_MAP,EXISTS_PROD] >>
      disch_then(qx_choose_then`s`strip_assume_tac) >>
      res_tac >>
      qspecl_then[`Var s (typeof t)`,`t`,`e`]mp_tac term_equation >>
      discharge_hyps >- (
        imp_res_tac term_welltyped >>
        fs[welltyped_equation] ) >>
      simp[] >>
      disch_then(qx_choosel_then[`l`,`r`]strip_assume_tac) >>
      qexists_tac`r` >>
      simp[] >>
      fs[equation_def] >>
      simp[Once proves_cases] >>
      METIS_TAC[] ) >>
    `∃w. ∀n. n < LENGTH eqs ⇒ welltyped (SND (EL n eqs)) ∧ term defs (SND (EL n eqs)) (w n)` by (
      simp[GSYM SKOLEM_THM] >> strip_tac >>
      simp[RIGHT_EXISTS_IMP_THM] >> strip_tac >>
      first_x_assum(qspecl_then[`FST(EL n eqs)`,`SND(EL n eqs)`]mp_tac) >>
      simp[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
      disch_then(qspec_then`n`mp_tac) >> simp[] >>
      disch_then(qx_choose_then`e`strip_assume_tac) >>
      qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
      `welltyped (e1 === e2)` by ( METIS_TAC[term_welltyped] ) >>
      fs[welltyped_equation,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Abbr`e1`,Abbr`e2`] >>
      METIS_TAC[] ) >>
    `GENLIST (λn. Var (FST(EL n eqs)) (typeof (w n)) === w n) (LENGTH eqs) = h1'` by (
      simp[LIST_EQ_REWRITE] >>
      fs[EVERY2_EVERY] >>
      rfs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      qx_gen_tac`m` >> strip_tac >>
      qpat_assum`∀n. n < LENGTH h1' ⇒ P`(qspec_then`m`mp_tac) >>
      qpat_assum`∀n. n < LENGTH h1' ⇒ P`(qspec_then`m`mp_tac) >>
      simp[UNCURRY] >> rw[] >>
      first_x_assum(qspecl_then[`FST(EL m eqs)`,`SND(EL m eqs)`]mp_tac) >>
      simp[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
      disch_then(qspec_then`m`mp_tac) >> simp[] >>
      rw[] >>
      imp_res_tac term_type_11 >> rw[] >>
      qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
      qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Abbr`e1`,Abbr`e2`] >>
      rw[Abbr`e`] >> simp[] >>
      imp_res_tac term_type_11 >> rw[] >>
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac has_type_IMP >>
      fs[WELLTYPED] >>
      METIS_TAC[WELLTYPED_LEMMA] ) >>
    conj_asm1_tac >- (
      simp[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`ddefs`] >>
      qx_genl_tac[`s`,`t`] >> strip_tac >>
      conj_tac >- (
        match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,10)) >>
        simp[] >> METIS_TAC[] ) >>
      Cases_on`find_index s (MAP FST eqs) 0` >- (
        fs[GSYM find_index_NOT_MEM,MEM_MAP,FORALL_PROD] ) >>
      `EL x eqs = (s,t)` by (
        `ALL_DISTINCT (MAP FST eqs)` by fs[ALL_DISTINCT_APPEND] >>
        Q.ISPEC_THEN`MAP FST eqs`mp_tac find_index_ALL_DISTINCT_EL_eq >>
        simp[] >>
        disch_then(qspecl_then[`s`,`0`,`x`]mp_tac) >>
        simp[GSYM AND_IMP_INTRO,EL_MAP] >>
        fs[EL_ALL_DISTINCT_EL_EQ] >>
        fs[MEM_EL] >> rw[] >>
        first_x_assum(qspecl_then[`n`,`x`]mp_tac) >>
        simp[EL_MAP] >>
        Cases_on`EL n eqs`>>fs[]>>
        Cases_on`EL x eqs`>>fs[]>>rw[]>>fs[]) >>
      imp_res_tac find_index_LESS_LENGTH >> fs[] >>
      qexists_tac`Const s (typeof (w x)) (Defined x (GENLIST (λn. (FST(EL n eqs),w n)) (LENGTH eqs)) c1')` >>
      conj_tac >- (
        match_mp_tac(List.nth(CONJUNCTS (SPEC_ALL term_rules),10)) >>
        simp[Once const_def_def] >>
        simp[MAP_GENLIST,combinTheory.o_DEF] >>
        conj_tac >- (
          match_mp_tac(MP_CANON (CONJUNCT1 (UNDISCH (SPEC_ALL term_type_cons)))) >>
          simp[safe_def_names_def,pred_setTheory.IN_DISJOINT] >>
          conj_tac >- (
            first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
            fs[holSyntaxTheory.WELLTYPED] >>
            imp_res_tac has_type_IMP >>
            `welltyped (w x)` by metis_tac[welltyped_def] >>
            fs[WELLTYPED] >>
            METIS_TAC[WELLTYPED_LEMMA] ) >>
          fs[ALL_DISTINCT_APPEND] >> METIS_TAC[] ) >>
        fs[EVERY2_EVERY,EVERY_MEM] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP,UNCURRY] >>
        simp[Once LIST_EQ_REWRITE,EL_MAP]) >>
      simp[Once proves_cases] >>
      rpt disj2_tac >>
      simp[EL_MAP,MEM_MAP,EXISTS_PROD,MAP_GENLIST,combinTheory.o_DEF] >>
      simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST,MEM_GENLIST] >>
      conj_tac >- (
        qpat_assum`EVERY X (MAP SND eqs)`mp_tac >>
        simp[EVERY_MAP,EVERY_MEM,Once MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
        ntac 3 strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[] >> strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[] >> strip_tac >>
        conj_asm1_tac >- METIS_TAC[CLOSED_IMP] >>
        fs[holSyntaxTheory.WELLTYPED] >>
        imp_res_tac has_type_IMP >>
        imp_res_tac WELLTYPED_LEMMA >>
        simp[WELLTYPED,pred_setTheory.SUBSET_DEF] >>
        imp_res_tac tvars_IMP >>
        imp_res_tac tyvars_IMP >>
        METIS_TAC[] ) >>
      conj_tac >- (
        fs[ALL_DISTINCT_APPEND] >>
        fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP] >>
        METIS_TAC[] ) >>
      rw[] >>
      qmatch_assum_abbrev_tac`sholSyntax$VFREE_IN X Y` >>
      qspecl_then[`Y`,`defs`,`c'`,`X`]mp_tac term_subterm_inv >>
      simp[Abbr`X`] >>
      disch_then(qx_choose_then`v`strip_assume_tac) >>
      qpat_assum`term defs v X`mp_tac >>
      Cases_on`v`>>TRY(simp[Once term_cases] >> NO_TAC) >>
      simp[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`VFREE_IN (Var v vy) c'`[] >>
      first_x_assum(qspecl_then[`v`,`vy`]mp_tac) >>
      simp[MEM_MAP,EXISTS_PROD,MEM_EL,PULL_EXISTS] >>
      rw[] >> pop_assum (assume_tac o SYM) >> simp[] >>
      qexists_tac`n`>>simp[] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[holSyntaxTheory.WELLTYPED] >>
      strip_tac >>
      imp_res_tac has_type_IMP >>
      imp_res_tac WELLTYPED_LEMMA >>
      rw[] >>
      METIS_TAC[term_type_11] ) >>
    conj_asm1_tac >- (
      ntac 2 strip_tac >>
      last_x_assum(qspec_then`t`mp_tac) >>
      simp[PULL_EXISTS] >>
      METIS_TAC[] ) >>
    simp[defthm_def] >>
    conj_tac >- (
      qexists_tac`h1'` >>
      qexists_tac`c1'` >>
      simp[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP,UNCURRY] >>
      rw[] >>
      match_mp_tac term_equation_matchable >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[holSyntaxTheory.WELLTYPED] >>
      strip_tac >>
      imp_res_tac has_type_IMP >>
      imp_res_tac WELLTYPED_LEMMA >>
      rw[] >>
      qunabbrev_tac`ddefs` >>
      match_mp_tac(MP_CANON (CONJUNCT1 (UNDISCH (SPEC_ALL term_type_cons)))) >>
      simp[safe_def_names_def,pred_setTheory.IN_DISJOINT] >>
      fs[ALL_DISTINCT_APPEND,MEM_MAP] >>
      METIS_TAC[]) >>
    conj_tac >- (
      rw[] >>
      res_tac >>
      qexists_tac`h1'` >>
      fs[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      rfs[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      METIS_TAC[] ) >>
    qpat_assum`LIST_REL X Y h1`mp_tac >>
    simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
    ntac 2 strip_tac >>
    qexists_tac`h1` >>
    simp[MEM_ZIP,PULL_EXISTS] >>
    qexists_tac`c1` >> simp[]) >>
  conj_tac >- (
    rw[seq_trans_def] >>
    Q.PAT_ABBREV_TAC`ilist:(holSyntax$term#holSyntax$term)list = MAP X eqs` >>
    first_x_assum(qspecl_then[`MAP (λ(s,t). Var s (typeof t) === t) eqs`,`p`]mp_tac) >>
    discharge_hyps >- (
      simp[MEM_MAP,MEM_FLAT,PULL_EXISTS] >>
      qexists_tac`Constdef eqs p` >>
      simp[defthm_def] ) >>
    disch_then(qx_choosel_then[`eqs1`,`p1`]strip_assume_tac) >>
    `∃vs1. LIST_REL (λ(x,t) e. e = Var x (typeof t) === t ∧ welltyped e) vs1 eqs1` by (
      simp[EVERY2_EVERY,EVERY_MEM,exists_list_GENLIST,MEM_ZIP,PULL_EXISTS,UNCURRY,GSYM SKOLEM_THM] >>
      fs[EVERY2_EVERY,EVERY_MEM] >> rfs[MEM_ZIP,PULL_EXISTS,EL_MAP,UNCURRY] >>
      rw[RIGHT_EXISTS_IMP_THM] >>
      res_tac >>
      qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
      qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
      `welltyped e` by (
        imp_res_tac proves_welltyped >>
        fs[EVERY_MEM] >>
        METIS_TAC[MEM_EL,welltyped_def] ) >>
      imp_res_tac term_welltyped >>
      fs[welltyped_equation] >> rw[Abbr`e`] >>
      simp[Abbr`e1`] >> fs[EXISTS_PROD] >>
      fs[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac has_type_IMP >>
      imp_res_tac term_type_11 >>
      rw[] >>
      METIS_TAC[WELLTYPED_LEMMA]) >>
    qexists_tac`VSUBST (GENLIST
      (λn. let x = FST(EL n eqs) in
           let ty = typeof(SND(EL n vs1)) in
      (Const x ty (Defined n vs1 p1),
       Var x ty)) (LENGTH eqs)) p1` >>
    conj_tac >- (
      match_mp_tac VSUBST_IMP >>
      simp[MAP_GENLIST,combinTheory.o_DEF] >>
      simp[EVERY2_EVERY,EVERY_MEM,GSYM AND_IMP_INTRO,MEM_ZIP
          ,Abbr`ilist`,PULL_EXISTS,EL_MAP,MEM_MAP] >>
      simp[UNCURRY,MEM_GENLIST,PULL_EXISTS] >>
      simp[Once has_type_cases] >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      reverse conj_asm2_tac >- (
        fs[EVERY2_EVERY,EVERY_MEM] >>
        rfs[MEM_ZIP,PULL_EXISTS,EL_MAP,UNCURRY] >>
        rw[] >> res_tac >>
        imp_res_tac term_welltyped >>
        fs[welltyped_equation] >>
        qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
        qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
        simp[] >> simp[Abbr`e1`,Abbr`e2`]) >>
      rw[] >>
      match_mp_tac(List.nth(CONJUNCTS (SPEC_ALL term_rules),10)) >>
      qexists_tac`eqs` >> qexists_tac`p` >>
      simp[] >>
      conj_tac >- (
        match_mp_tac MEM_Constdef_const_def >>
        fs[good_defs_def] >>
        Q.ISPECL_THEN[`MAP FST eqs`,`n`,`0:num`]mp_tac find_index_ALL_DISTINCT_EL >>
        discharge_hyps >- (
          simp[] >> fs[EVERY_MEM] >>
          res_tac >> fs[def_ok_def] ) >>
        simp[EL_MAP] ) >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,PULL_EXISTS,EL_MAP,UNCURRY] >>
      simp[Once LIST_EQ_REWRITE,EL_MAP,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      qx_gen_tac`m`>>strip_tac >>
      rpt(first_x_assum(qspec_then`m`mp_tac)) >>
      simp[] >> ntac 3 strip_tac >>
      qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
      qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
      discharge_hyps >- (
        imp_res_tac term_welltyped >> fs[welltyped_equation] ) >>
      simp[Abbr`e1`] ) >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) >>
    simp[] >>
    qexists_tac`vs1` >>
    `eqs1 = MAP (λ(s,t). Var s (typeof t) === t) vs1` by (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,PULL_EXISTS,UNCURRY] >>
      simp[Once LIST_EQ_REWRITE,EL_MAP,UNCURRY] ) >>
    conj_tac >- rw[] >>
    `MAP FST eqs = MAP FST vs1 ∧ LIST_REL (term defs) (MAP SND eqs) (MAP SND vs1)` by (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      simp[Once LIST_EQ_REWRITE,EL_MAP] >>
      rfs[MEM_ZIP,UNCURRY,PULL_EXISTS,EL_MAP] >>
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      ntac 2 strip_tac >>
      res_tac >>
      qmatch_assum_abbrev_tac`term defs (e1 === e2) e` >>
      qspecl_then[`e1`,`e2`,`e`]mp_tac term_equation >>
      discharge_hyps >- (
        imp_res_tac term_welltyped >> fs[welltyped_equation] ) >>
      simp[Abbr`e1`,Abbr`e`] ) >>
    `def_ok (Constdef eqs p)` by METIS_TAC[EVERY_MEM] >>
    fs[def_ok_def] >>
    conj_tac >- (
      fs[EVERY_MAP,EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,PULL_EXISTS,MEM_EL,EL_MAP] >>
      qx_gen_tac`m`>>strip_tac >> res_tac >>
      imp_res_tac CLOSED_IMP >>
      imp_res_tac tvars_IMP >>
      fs[UNCURRY] >>
      qpat_assum`sholSyntax$welltyped X`mp_tac >>
      simp_tac(srw_ss())[Once WELLTYPED] >>
      simp[Once equation_def,SimpR``sholSyntax$has_type``,EQUATION_HAS_TYPE_BOOL] >>
      strip_tac >>
      imp_res_tac term_welltyped >>
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac has_type_IMP >>
      imp_res_tac WELLTYPED_LEMMA >>
      imp_res_tac tyvars_IMP >>
      fs[] ) >>
    conj_tac >- (
      match_mp_tac (Q.ISPEC`FST`ALL_DISTINCT_MAP) >>
      simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      METIS_TAC[] ) >>
    conj_tac >- (
      rw[] >>
      qspecl_then[`p1`,`defs`,`p`,`Var x ty`]mp_tac term_subterm_inv >>
      simp[PULL_EXISTS] >>
      Cases >> TRY(simp[Once term_cases]>>NO_TAC) >>
      simp[MEM_MAP,EXISTS_PROD] >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rw[] >> res_tac >>
      rfs[MEM_ZIP,MEM_EL,PULL_EXISTS,EL_MAP] >>
      rpt(first_x_assum(qspec_then`n`mp_tac)) >>
      rw[UNCURRY] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`n` >> simp[] >>
      Cases_on`EL n vs1`>>fs[] >>
      qpat_assum`MAP X Y = MAP A B`mp_tac >>
      simp[Once LIST_EQ_REWRITE,EL_MAP] >>
      disch_then(qspec_then`n`mp_tac) >> simp[] >>
      qpat_assum`X = EL n eqs`(assume_tac o SYM) >> simp[] >>
      fs[] >>
      qpat_assum`sholSyntax$welltyped X`mp_tac >>
      simp_tac(srw_ss())[Once WELLTYPED] >>
      simp[Once equation_def,SimpR``sholSyntax$has_type``,EQUATION_HAS_TYPE_BOOL] >>
      strip_tac >>
      imp_res_tac term_welltyped >>
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac has_type_IMP >>
      imp_res_tac WELLTYPED_LEMMA >>
      fs[] >>
      imp_res_tac term_type_11 >>
      rw[]) >>
    simp[LIST_EQ_REWRITE] >>
    conj_asm1_tac >- fs[EVERY2_EVERY] >>
    simp[EL_GENLIST,EL_MAP,UNCURRY] >>
    qpat_assum`MAP FST X = MAP FST Y`mp_tac >>
    simp[Once LIST_EQ_REWRITE,EL_MAP] ) >>
  conj_tac >- (
    rpt gen_tac >>
    simp[seq_trans_def] >>
    simp[GSYM AND_IMP_INTRO] >>
    ntac 16 strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_abbrev_tac`P ⇒ A ∧ B ∧ C` >>
    `A` by (
      simp[Abbr`A`] >>
      simp[Once holSyntaxTheory.proves_cases] >>
      map_every qexists_tac[`[]`,`holSyntax$Comb t y`] >>
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
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
    simp[defcnds_ok_def] >>
    asm_simp_tac(srw_ss()++SatisfySimps.SATISFY_ss)[] >>
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
      simp[defthm_def] >>
      `safe_def_names defs (Typedef tyname t a r)` by (
        simp[safe_def_names_def] ) >>
      rw[] >> res_tac >|[map_every qexists_tac[`h1'`,`c1''`],
                         map_every qexists_tac[`h1`,`c1'`]] >>
      fs[EVERY_MEM,EVERY2_EVERY] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      METIS_TAC[term_type_cons]) >>
    `∀asl c. Q asl c ⇒ C asl c` by (
      rpt gen_tac >>
      simp(List.map Abbr [`B`,`C`,`P`,`Q`,`R`]) >>
      simp[defthm_def] >>
      rw[] >- (
        `safe_def_names defs (Typedef tyname t a r)` by (
          simp[safe_def_names_def] ) >>
        res_tac >>
        map_every qexists_tac[`h1`,`c1'`] >>
        fs[EVERY_MEM,EVERY2_EVERY] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        METIS_TAC[term_type_cons]) >>
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
      `∃ty1. x1 has_type ty1 ∧ type defs (Fun rep_type Bool) ty1` by METIS_TAC[has_type_IMP] >>
      pop_assum mp_tac >> simp[] >>
      disch_then(qx_choose_then`r1`strip_assume_tac) >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`x1` >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`r1` >>
      `type (Typedef tyname t a r::defs) rep_type r1` by (
        match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH(SPEC_ALL term_type_cons)))) >>
        simp[safe_def_names_def] ) >>
      simp[] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`x1` >> simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      HINT_EXISTS_TAC >> simp[] >>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`x1` >> simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      HINT_EXISTS_TAC >> simp[] >>
      simp[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      `r ≠ "="` by fs[consts_def] >> simp[] >>
      simp[Q.SPEC`Tyapp X Y`(CONJUNCT1 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      `safe_def_names defs (Typedef tyname t a r)` by simp[safe_def_names_def] >>
      qexists_tac`x1` >> simp[] >>
      qexists_tac`r1` >> simp[] >>
      qexists_tac`x1` >> simp[] >>
      qmatch_assum_abbrev_tac`LIST_REL ff ll rr` >>
      qexists_tac`rr` >> simp[] >>
      reverse conj_tac >- (
        rw[] >>
        imp_res_tac MEM_Typedef_MEM_consts >>
        fs[consts_def]) >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,27)) >>
      imp_res_tac CLOSED_IMP >>
      simp[] >>
      qexists_tac`y1` >>
      imp_res_tac tvars_IMP >>
      simp[Abbr`rr`] >>
      `welltyped x1` by METIS_TAC[term_welltyped] >>
      imp_res_tac has_type_IMP >>
      ntac 2 (pop_assum mp_tac) >>
      simp[] >>
      rw[] >>
      imp_res_tac WELLTYPED_LEMMA >>
      rw[] ) >>
    `∀asl c. R asl c ⇒ C asl c` by (
      rpt gen_tac >>
      simp(List.map Abbr [`B`,`C`,`P`,`Q`,`R`]) >>
      simp[defthm_def] >>
      rw[] >- (
        `safe_def_names defs (Typedef tyname t a r)` by (
          simp[safe_def_names_def] ) >>
        res_tac >>
        map_every qexists_tac[`h1`,`c1'`] >>
        fs[EVERY_MEM,EVERY2_EVERY] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        METIS_TAC[term_type_cons]) >>
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
      imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
      simp[] >>
      qpat_assum`term defs X c1`mp_tac >>
      simp[Once term_cases] >>
      rw[] >>
      `∃ty1. x1 has_type ty1 ∧ type defs (Fun (typeof y) Bool) ty1` by METIS_TAC[has_type_IMP] >>
      pop_assum mp_tac >>
      simp[] >> rw[] >>
      qmatch_assum_rename_tac`type defs (typeof y) ty1`[] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      qexists_tac`ty1` >>
      qexists_tac`x1` >>
      simp[RIGHT_EXISTS_AND_THM] >>
      `safe_def_names defs (Typedef tyname t a r)` by (
        simp[safe_def_names_def] ) >>
      conj_asm1_tac >- METIS_TAC[term_type_cons] >>
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
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`x1`>>simp[] >>
      simp[Q.SPEC`Comb X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      qexists_tac`ty1`>>simp[] >>
      qexists_tac`x1`>>simp[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`ty1`>>simp[] >>
      qexists_tac`MAP Tyvar (STRING_SORT (tvars t))` >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_asm1_tac >- (
        simp[EVERY2_MAP] >>
        simp[EVERY2_refl] ) >>
      conj_tac >- (
        METIS_TAC[MEM_Typedef_MEM_consts,consts_def,MEM_MAP,MEM_APPEND] ) >>
      `a ≠ "@"` by fs[consts_def] >>
      simp[Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))] >>
      simp[Once type_def_def] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp[Once const_def_def] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      qexists_tac`x1`>>simp[]>>
      qexists_tac`ty1`>>simp[]>>
      qexists_tac`ty1`>>simp[]>>
      simp[Once term_cases] >>
      simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
      simp[Once type_def_def] >>
      qexists_tac`x1`>>simp[]>>
      HINT_EXISTS_TAC >> simp[] >>
      conj_tac >- METIS_TAC[MEM_Typedef_MEM_consts,consts_def,MEM_MAP,MEM_APPEND] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,28)) >>
      imp_res_tac CLOSED_IMP >>
      simp[] >>
      qexists_tac`y1` >>
      imp_res_tac WELLTYPED_LEMMA >>
      imp_res_tac tvars_IMP >>
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
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
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
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
        simp[] >>
        qexists_tac`x` >>
        HINT_EXISTS_TAC >>
        HINT_EXISTS_TAC >>
        simp[]) >>
      qmatch_assum_abbrev_tac`term ddefs (ll === rr) e1` >>
      `welltyped (ll === rr)` by (
        imp_res_tac term_welltyped >>
        imp_res_tac proves_welltyped >>
        fs[] >> METIS_TAC[welltyped_def] ) >>
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
      Q.PAT_ABBREV_TAC`ty = sholSyntax$typeof X` >>
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
        match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
        simp[] >>
        qexists_tac`x` >>
        HINT_EXISTS_TAC >>
        HINT_EXISTS_TAC >>
        simp[]) >>
      qmatch_assum_abbrev_tac`term ddefs (ll === rr) e1` >>
      `welltyped (ll === rr)` by (
        imp_res_tac term_welltyped >>
        imp_res_tac proves_welltyped >>
        fs[] >>
        METIS_TAC[welltyped_def] ) >>
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
      Q.PAT_ABBREV_TAC`ty = sholSyntax$typeof X` >>
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
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
      simp[] >>
      qexists_tac`ARB` >>
      HINT_EXISTS_TAC >>
      HINT_EXISTS_TAC >>
      simp[] >> disj1_tac >>
      match_mp_tac (List.nth(CONJUNCTS holSyntaxTheory.proves_rules,14)) >>
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
    qexists_tac`ty1` >> simp[] >>
    simp[Once term_cases] >>
    srw_tac[boolSimps.DNF_ss][] >>
    qexists_tac`ty1` >> simp[] >>
    qexists_tac`ty1'` >> simp[] >>
    qexists_tac`ty1` >> simp[] >>
    qexists_tac`ty1` >> simp[] >>
    qexists_tac`ty1'` >> simp[] >>
    simp[Abbr`P`] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,29)) >>
    rw[] ) >>
  conj_tac >- (
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
    fs[holSyntaxTheory.WELLTYPED] >>
    imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
    fs[] >> rw[] >>
    qspecl_then[`p`,`Fun (typeof w) Bool`]mp_tac has_type_IMP >>
    simp[] >>
    disch_then(qspecl_then[`defs`,`x1`]mp_tac) >>
    simp[] >>
    srw_tac[boolSimps.DNF_ss][] >>
    qexists_tac`x1` >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    rw[] >>
    match_mp_tac(List.nth(CONJUNCTS proves_rules,30)) >>
    qexists_tac`y1` >> rw[]) >>
  rpt gen_tac >> strip_tac >>
  simp[seq_trans_def] >>
  conj_tac >- fs[seq_trans_def] >>
  simp[Once term_cases,PULL_EXISTS] >>
  exists_tac(EX_def|>Q.SPECL[`x`,`Fun Ind Ind`,`b`]|>concl|>rhs|>rator|>rand) >>
  simp[Once term_cases] >>
  qspecl_then[`defs`,`"?"`]imp_res_tac MEM_Constdef_const_def >>
  fs[find_index_def] >> rw[] >>
  pop_assum mp_tac >>
  discharge_hyps >- fs[good_defs_def] >> strip_tac >>
  simp[Once term_cases] >>
  qspecl_then[`defs`,`"!"`]imp_res_tac MEM_Constdef_const_def >>
  fs[find_index_def] >> rw[] >>
  pop_assum mp_tac >>
  discharge_hyps >- fs[good_defs_def] >> strip_tac >>
  simp[Once FA_def] >>
  simp[Once term_cases] >>
  simp[Once(Q.SPEC`Const X Y`(CONJUNCT2 (SPEC_ALL term_cases))),PULL_EXISTS] >>
  Q.PAT_ABBREV_TAC`p1 = holSyntax$Var XX (Fun Z Bool)` >>
  Q.PAT_ABBREV_TAC`p2 = sholSyntax$Var XX (Fun Z Bool)` >>
  Q.PAT_ABBREV_TAC`q1 = holSyntax$Abs  X Y Z` >>
  Q.PAT_ABBREV_TAC`q2 = sholSyntax$Abs  X Y Z` >>
  qspecl_then[`p1`,`q1`,`p2===q2`]mp_tac term_equation >>
  discharge_hyps >- (
    simp[Abbr`p1`,Abbr`q1`,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`Ind` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`Ind` >>
  simp[GSYM PULL_EXISTS] >>
  mp_tac term_Truth >>
  discharge_hyps >- simp[] >> strip_tac >>
  simp[GSYM CONJ_ASSOC] >>
  conj_asm1_tac >- ( simp[Abbr`p1`,Abbr`p2`] ) >>
  conj_asm1_tac >- ( simp[Abbr`q1`,Abbr`q2`] ) >>
  conj_asm1_tac >- (
    match_mp_tac term_equation_matchable >>
    simp[typeof_shadow_def] >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
    simp[Abbr`p1`,Abbr`q1`] >>
    conj_tac >- (
      unabbrev_all_tac >>
      simp[holSyntaxTheory.equation_def,equation_def] ) >>
    match_mp_tac term_equation_matchable >>
    simp[Abbr`q2`,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
  conj_asm1_tac >- (
    match_mp_tac term_Implies >>
    simp[] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases,Abbr`p1`] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    match_mp_tac (GEN_ALL term_Forall) >>
    simp[] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    match_mp_tac term_Implies >>
    simp[] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once holSyntaxTheory.has_type_cases] >>
    simp[Once term_cases] ) >>
  conj_tac >- (
    match_mp_tac term_equation_matchable >>
    simp[typeof_shadow_def,Once FA_def,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Abbr`p1`] >>
    match_mp_tac (GEN_ALL term_Forall) >>
    simp[] >>
    rpt(simp[Once holSyntaxTheory.has_type_cases])) >>
  simp[Once term_cases] >>
  simp[Once term_cases] >>
  qexists_tac`AN (O1 Ind Ind (Var "f" (Fun Ind Ind))) (NO (OT Ind Ind (Var "f" (Fun Ind Ind))))` >>
  conj_tac >- (
    match_mp_tac term_And >>
    simp[] >>
    ntac 8 (simp[Once holSyntaxTheory.has_type_cases]) >>
    conj_tac >- (
      simp[Once term_cases,O1_def] >>
      qspecl_then[`defs`,`"ONE_ONE"`]imp_res_tac MEM_Constdef_const_def >>
      fs[find_index_def] >>
      reverse conj_tac >- simp[Once term_cases] >> rw[] >>
      pop_assum mp_tac >>
      discharge_hyps >- fs[good_defs_def] >> strip_tac >>
      simp[Once term_cases] >>
      simp[Once term_cases] >>
      conj_asm1_tac >- (
        match_mp_tac (GEN_ALL term_Forall) >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
        match_mp_tac (GEN_ALL term_Forall) >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[Once holSyntaxTheory.has_type_cases] >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
        match_mp_tac term_Implies >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
        conj_tac >- (
          match_mp_tac term_equation_matchable >>
          simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
          simp[Once term_cases] >>
          simp[Once term_cases] ) >>
        match_mp_tac term_equation_matchable >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] ) >>
      match_mp_tac term_equation_matchable >>
      simp[typeof_shadow_def,Once FA_def] >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
      simp[holSyntaxTheory.equation_def] ) >>
    simp[Once term_cases,NO_def] >>
    qspecl_then[`defs`,`"~"`]imp_res_tac MEM_Constdef_const_def >>
    fs[find_index_def] >> rpt(qpat_assum`T`kall_tac) >>
    pop_assum mp_tac >>
    discharge_hyps >- fs[good_defs_def] >> strip_tac >>
    simp[Once term_cases,GSYM CONJ_ASSOC] >>
    conj_asm1_tac >- (
      match_mp_tac term_Implies >>
      simp[] >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      qspecl_then[`defs`,`"F"`]imp_res_tac MEM_Constdef_const_def >>
      fs[find_index_def] >> rpt(qpat_assum`T`kall_tac) >>
      pop_assum mp_tac >> discharge_hyps >- fs[good_defs_def] >> strip_tac >>
      simp[Once term_cases,FF_def] >>
      conj_tac >- (
        match_mp_tac(GEN_ALL term_Forall) >>
        simp[Once holSyntaxTheory.has_type_cases] ) >>
      match_mp_tac term_equation_matchable >>
      simp[typeof_shadow_def,Once FA_def] >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      match_mp_tac (GEN_ALL term_Forall) >>
      simp[Once holSyntaxTheory.has_type_cases] ) >>
    conj_asm1_tac >- (
      match_mp_tac term_equation_matchable >>
      simp[typeof_shadow_def,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      simp[IM_def] ) >>
    simp[Once term_cases,OT_def] >>
    qspecl_then[`defs`,`"ONTO"`]imp_res_tac MEM_Constdef_const_def >>
    fs[find_index_def] >> rpt(qpat_assum`T`kall_tac) >>
    pop_assum mp_tac >> discharge_hyps >- fs[good_defs_def] >> strip_tac >>
    simp[Once term_cases,GSYM CONJ_ASSOC] >>
    conj_asm1_tac >- simp[Once term_cases] >>
    conj_asm1_tac >- (
      match_mp_tac(GEN_ALL term_Forall) >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      simp[Once holSyntaxTheory.has_type_cases] >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      simp[Once term_cases,EX_def] >>
      simp[Once term_cases] >>
      conj_tac >- (
        conj_asm1_tac >- (
          match_mp_tac (GEN_ALL term_Forall) >>
          ntac 6 ( simp[Once holSyntaxTheory.has_type_cases] )>>
          simp[Once holSyntaxTheory.has_type_cases,Abbr`p1`] >>
          rpt (simp[Once holSyntaxTheory.has_type_cases])) >>
        match_mp_tac term_equation_matchable >>
        simp[typeof_shadow_def,holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Abbr`p1`] >>
        simp[Once FA_def] ) >>
      simp[welltyped_equation] >>
      reverse conj_tac >- (
        Q.PAT_ABBREV_TAC`eq:holSyntax$term = a === b` >>
        qsuff_tac`eq has_type Bool` >- PROVE_TAC[holSyntaxTheory.WELLTYPED,holSyntaxTheory.WELLTYPED_LEMMA] >>
        simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Abbr`eq`] ) >>
      match_mp_tac term_equation_matchable >>
      simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
      simp[Once term_cases] ) >>
    simp[typeof_shadow_def] >>
    match_mp_tac term_equation_matchable >>
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL,Once FA_def,welltyped_equation] >>
    simp[holSyntaxTheory.equation_def] ) >>
  simp[GSYM EX_def,Abbr`p2`] >>
  ACCEPT_TAC(List.nth(CONJUNCTS proves_rules,31)))

val soundness = store_thm("soundness",
  ``is_model M ⇒ ∀dh t. dh |- t ⇒ hol_seq (dh,t)``,
  strip_tac >>
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
  ``is_model M ⇒
    (∀d. context_ok d ⇒ (d,[]) |- (Var x Bool === Var x Bool)) ∧
    (∀d. ¬ ((d,[]) |- Var x Bool === Var (sholSyntax$VARIANT (Var x Bool) x Bool) Bool))``,
  strip_tac >>
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
  discharge_hyps >- (
    simp[holSyntaxTheory.EQUATION_HAS_TYPE_BOOL] >>
    simp[Abbr`l`,Abbr`r`] ) >>
  `term d (l === r) c1 = T` by (rfs[]>>fs[])>>
  pop_assum SUBST1_TAC >>
  simp [Abbr`l`,Abbr`r`] >>
  METIS_TAC[consistency])

val term_ok_welltyped = store_thm("term_ok_welltyped",
  ``∀defs tm. term_ok defs tm ⇒ welltyped tm``,
  rw[] >>
  imp_res_tac proves_IMP >>
  imp_res_tac proves_welltyped >> fs[] >>
  METIS_TAC[term_welltyped])

val proves_cons_def = store_thm("proves_cons_def",
  ``is_model M ⇒ ∀defs h c d. (defs,h) |- c ⇒ context_ok (d::defs) ⇒ (d::defs,h) |- c``,
  rw[] >>
  Cases_on`d` >- (
    match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,24)) >>
    imp_res_tac proves_IMP >>
    fs[def_ok_def,deftm_def,pred_setTheory.SUBSET_DEF,good_defs_def,defcnds_ok_def] >>
    imp_res_tac term_ok_welltyped >>
    fs[consts_def,ALL_DISTINCT_APPEND,consts_aux_def] >>
    fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    simp[MEM_MAP,EXISTS_PROD] >>
    METIS_TAC[]) >>
  match_mp_tac(List.nth(CONJUNCTS holSyntaxTheory.proves_rules,26)) >>
  simp[] >>
  imp_res_tac proves_IMP >>
  fs[def_ok_def,deftm_def,good_defs_def,defcnds_ok_def] >>
  Q.LIST_EXISTS_TAC[`rty`,`w`] >> simp[] >>
  fs[types_def,ALL_DISTINCT_APPEND,types_aux_def,consts_def,consts_aux_def,LET_THM] )

val _ = export_theory()
