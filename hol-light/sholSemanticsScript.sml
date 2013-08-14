open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory finite_mapTheory sholSyntaxTheory modelSetTheory
val _ = numLib.prefer_num()
val _ = new_theory"sholSemantics"

val (semantics_rules,semantics_ind,semantics_cases) = Hol_reln`
  (typeset τ (Tyvar s) (τ s)) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (LENGTH (tvars p) = LENGTH ts ∧
   tyin = ZIP (MAP Tyvar (STRING_SORT (tvars p)), ts) ∧
   INST tyin p has_type Fun rty Bool ∧
   semantics FEMPTY τ (INST tyin p) mp ∧
   typeset τ rty mrty (* do we need to know that mp is not empty? *)
   ⇒
   typeset τ (Tyapp (Tydefined s p) ts) (mrty suchthat holds mp)) ∧

  (FLOOKUP σ (n,ty) = SOME m
   ⇒
   semantics σ τ (Var n ty) m) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "=" (Fun ty (Fun ty Bool)) Prim)
    (abstract mty (funspace mty boolset)
       (λx. abstract mty boolset (λy. boolean (x = y))))) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "@" (Fun (Fun ty Bool) ty) Prim)
     (abstract (funspace mty boolset) mty
       (λp. let mp = (mty suchthat holds p) in
            ch (if ∃x. x <: mp then mp else mty)))) ∧

  (welltyped t ∧ closed t ∧
   set(tvars t) ⊆ set (tyvars (typeof t)) ∧
   INST tyin t has_type ty ∧
   semantics FEMPTY τ (INST tyin t) mt
   ⇒
   semantics σ τ (Const s ty (Defined t)) mt) ∧

  (typeset τ rty mrty ∧
   typeset τ (Tyapp (Tydefined op p) args) maty (* do we put all the conditions here too? *)
   ⇒
   semantics σ τ (Const s (Fun (Tyapp (Tydefined op p) args) rty) (Tyrep op p))
    (abstract maty mrty (λx. x))) ∧

  (typeset τ rty mrty ∧
   typeset τ (Tyapp (Tydefined op p) args) maty ∧
   welltyped p ∧ closed p ∧
   tyin = ZIP(args,MAP Tyvar(STRING_SORT(tvars p))) ∧ LENGTH args = LENGTH (tvars p) ∧
   semantics FEMPTY τ (INST tyin p) mp
   ⇒
   semantics σ τ (Const s (Fun rty (Tyapp (Tydefined op p) args)) (Tyabs op p))
    (abstract mrty maty (λx. if holds mp x then x else ch maty))) ∧

  (semantics σ τ t mt ∧
   semantics σ τ u mu
   ⇒
   semantics σ τ (Comb t u) (apply mt mu)) ∧

  (typeset τ ty mty ∧
   b has_type tyb ∧
   typeset τ tyb mtyb ∧
   (∀x. semantics (σ |+ ((n,ty),x)) τ b (mb x))
   ⇒
   semantics σ τ (Abs n ty b) (abstract mty mtyb mb))`

val type_valuation_def = Define`
  type_valuation τ ⇔ ∀x. ∃y. y <: τ x`

val term_valuation_def = Define`
  term_valuation τ σ ⇔
    FEVERY (λ(v,m). ∀mty. typeset τ (SND v) mty ⇒ m <: mty) σ`

val _ = Parse.add_infix("|=",450,Parse.NONASSOC)

val sequent_def = xDefine"sequent"`
  h |= c ⇔ EVERY (λt. t has_type Bool) (c::h) ∧
           ∀σ τ. type_valuation τ ∧
                 term_valuation τ σ ∧
                 EVERY (λt. semantics σ τ t true) h
                 ⇒
                 semantics σ τ c true`

val term_valuation_FUPDATE = store_thm("term_valuation_FUPDATE",
  ``∀τ σ v m.
    term_valuation τ σ ∧
    (∀mty. typeset τ (SND v) mty ⇒ m <: mty)
    ⇒
    term_valuation τ (σ |+ (v,m))``,
  rw[term_valuation_def,FEVERY_DEF,FAPPLY_FUPDATE_THM]>>PROVE_TAC[])

val semantics_closed = store_thm("semantics_closed",
  ``∀t σ τ mt. semantics σ τ t mt ⇒
      ∀n ty. VFREE_IN (Var n ty) t ⇒ (n,ty) ∈ FDOM σ``,
  reverse Induct >- (
    simp[Once semantics_cases] >>
    rpt gen_tac >> strip_tac >>
    simp[CONJ_SYM] >>
    simp[GSYM AND_IMP_INTRO] >>
    rpt gen_tac >> strip_tac >>
    `(n,ty) ∈ FDOM (σ |+ ((s,t),x))` by PROVE_TAC[] >>
    fs[] ) >>
  simp[Once semantics_cases] >>
  simp[FLOOKUP_DEF] >>
  metis_tac[])

val type_ind =
  TypeBase.induction_of``:type``
  |> Q.SPECL[`K T`,`P`,`K T`,`K T`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val MEM_LIST_INSERT = store_thm("MEM_LIST_INSERT",
  ``∀l x. set (LIST_INSERT x l) = x INSERT set l``,
  Induct >> simp[LIST_INSERT_def] >> rw[] >>
  rw[EXTENSION] >> metis_tac[])

val MEM_LIST_UNION = store_thm("MEM_LIST_UNION",
  ``∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2``,
  Induct >> fs[LIST_UNION_def,MEM_LIST_INSERT] >>
  rw[EXTENSION] >> metis_tac[])

val TYPE_SUBST_tyvars = store_thm("TYPE_SUBST_tyvars",
  ``∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)``,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  conj_tac >- metis_tac[] >>
  Induct >> simp[] >>
  gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> EQ_TAC >> strip_tac >> fs[] >>
  fs[MEM_LIST_UNION] >> metis_tac[])

val tvars_VSUBST_subset = store_thm("tvars_VSUBST_subset",
  ``∀t sub. set (tvars (VSUBST sub t)) ⊆ set (tvars t) ∪ set (FLAT (MAP (tvars o FST) sub))``,
  Induct >> simp[VSUBST_def,tvars_def] >- (
    rw[SUBSET_DEF,MEM_FLAT] >>
    Q.ISPECL_THEN[`sub`,`Var s t`,`Var s t`]mp_tac REV_ASSOCD_MEM >>
    rw[] >> fs[tvars_def] >>
    disj2_tac >> HINT_EXISTS_TAC >> simp[MEM_MAP] >>
    HINT_EXISTS_TAC >> simp[] )
  >- (
    fs[SUBSET_DEF,MEM_LIST_UNION] >>
    metis_tac[] )
  >- (
    rw[] >>
    fs[SUBSET_DEF,MEM_LIST_UNION,tvars_def,VSUBST_def] >>
    rw[] >> fs[] >>
    res_tac >> fs[tvars_def] >>
    fs[MEM_FLAT,MEM_MAP,MEM_FILTER,pairTheory.EXISTS_PROD] >>
    fsrw_tac[DNF_ss][] >> metis_tac[]))

val INST_CORE_tvars = store_thm("INST_CORE_tvars",
  ``∀env tyin t tyin'.
    (∀x. MEM x (tvars t) ⇒
         REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
         REV_ASSOCD (Tyvar x) tyin  (Tyvar x)) ∧
    (∀s s'. MEM (s,s') env ⇒
            ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty))
    ⇒
    INST_CORE env tyin t = INST_CORE env tyin' t``,
  ho_match_mp_tac INST_CORE_ind >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def,MEM_LIST_UNION] >>
    rw[] >>
    TRY (
    `INST_CORE env tyin t = INST_CORE env tyin' t` by (
      first_x_assum match_mp_tac >>
      metis_tac[] )) >>
    TRY (
    `INST_CORE env tyin t' = INST_CORE env tyin' t'` by (
      first_x_assum match_mp_tac >>
      metis_tac[] )) >>
    fs[] ) >>
  simp[tvars_def,MEM_LIST_UNION] >>
  simp[INST_CORE_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`env1 = X::env` >>
  Q.PAT_ABBREV_TAC`env2 = X::env` >>
  Q.PAT_ABBREV_TAC`env3 = X::env` >>
  Q.PAT_ABBREV_TAC`env4 = X::env` >>
  strip_tac >>
  `env1 = env3` by metis_tac[TYPE_SUBST_tyvars] >>
  `INST_CORE env1 tyin t = INST_CORE env1 tyin' t` by (
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[TYPE_SUBST_tyvars] ) >>
  `TYPE_SUBST tyin' ty = TYPE_SUBST tyin ty` by metis_tac[TYPE_SUBST_tyvars] >>
  Cases_on`IS_RESULT (INST_CORE env3 tyin t)`>>rfs[] >> fs[] >>
  Cases_on`CLASH (INST_CORE env3 tyin' t) = Var x (TYPE_SUBST tyin ty)`>>fs[] >>
  `INST_CORE [] tyin t = INST_CORE [] tyin' t` by (
    first_x_assum match_mp_tac >> simp[] ) >>
  `env2 = env4` by (
    simp[Abbr`env2`,Abbr`env4`]) >>
  fs[] >>
  Q.PAT_ABBREV_TAC`sub = [(Var X Y,Var A Z)]` >>
  `INST_CORE env4 tyin (VSUBST sub t) = INST_CORE env4 tyin' (VSUBST sub t)` by (
    first_x_assum match_mp_tac >>
    rw[] >- (
      imp_res_tac (SIMP_RULE std_ss [SUBSET_DEF] tvars_VSUBST_subset) >>
      fs[Abbr`sub`,tvars_def] ) >>
    metis_tac[] ) >>
  fs[])

(*
val INST_CORE_tvars_imp = store_thm("INST_CORE_tvars_imp",
  ``∀env tyin t tyin'.
    (∀s s'. MEM (s,s') env ⇒
            ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
    (∀s s'. MEM (s,s') env ⇒
            ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin' ty)) ∧
    INST_CORE env tyin t = INST_CORE env tyin' t
    ⇒
    (∀x. MEM x (tvars t) ⇒
         REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
         REV_ASSOCD (Tyvar x) tyin  (Tyvar x))``,
  ho_match_mp_tac INST_CORE_ind >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[INST_CORE_def] >>
    gen_tac >> strip_tac >>
    simp[tvars_def,MEM_LIST_UNION] >>
    pop_assum mp_tac >> rw[] >> fs[] >>

    INST_CORE_HAS_TYPE

    Cases_on`IS_CLASHOI
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def,MEM_LIST_UNION] >>
    ntac 2 (pop_assum mp_tac) >> rw[] >> fs[] >>
    TRY (
      first_assum (match_mp_tac o MP_CANON) >>
      qpat_assum`X = Y`(assume_tac o SYM) >> simp[] >>
      match_mp_tac EQ_SYM >>
      match_mp_tac INST_CORE_tvars >> simp[] >>
      first_x_assum match_mp_tac


      first_x_assum (match_mp_tac o MP_CANON) >>
      simp[] >>
      metis_tac[INST_CORE_tvars]
    metis_tac[TYPE_SUBST_tyvars]
    metis_tac[TYPE_SUBST_tyvars] ) >>
*)

val semantics_11 = store_thm("semantics_11",
  ``(∀τ ty mty. typeset τ ty mty ⇒
        ∀mty'. typeset τ ty mty' ⇒ mty' = mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        ∀mt'. semantics σ τ t mt' ⇒ mt' = mt)``,
  ho_match_mp_tac semantics_ind >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >>
    PROVE_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    `Fun ty Bool = Fun rty Bool` by (
      metis_tac[WELLTYPED_LEMMA] ) >>
    fs[] ) >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[] >>
    qspecl_then[`sizeof t`,`t`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    qspecl_then[`sizeof t`,`t`,`[]`,`tyin'`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> ntac 2 strip_tac >> fs[INST_def] >>
    `INST_CORE [] tyin' t = INST_CORE [] tyin t` by (
      match_mp_tac INST_CORE_tvars >>
      fs[SUBSET_DEF] >>
      imp_res_tac WELLTYPED_LEMMA >> rw[] >> fs[] >>
      metis_tac[TYPE_SUBST_tyvars] ) >>
    fs[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >>
    rw[] >> metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac (srw_ss()) [Once semantics_cases] >>
    rw[] >>
    `mrty = mty'` by metis_tac[] >>
    `maty = mty` by metis_tac[] >>
    qsuff_tac`mp = mt`>-rw[]>>
    first_x_assum match_mp_tac >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    metis_tac[] ) >>
  rpt gen_tac >>
  strip_tac >>
  simp[Once semantics_cases] >>
  rw[] >>
  metis_tac[WELLTYPED_LEMMA] )

(*
val semantics_typeset = store_thm("semantics_typeset",
  ``∀tm ty. tm has_type ty ⇒
      ∀σ τ mtm mty. type_valuation τ ∧ term_valuation τ σ ∧
                    typeset τ ty mty ∧ semantics σ τ tm mtm
                    ⇒ mtm <: mty``,
  ho_match_mp_tac has_type_strongind >>
  conj_tac >- (
    simp[Once (CONJUNCT2 semantics_cases)] >>
    rw[term_valuation_def] >>
    imp_res_tac FEVERY_FLOOKUP >> fs[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp[Once (CONJUNCT2 semantics_cases)] >>
    rw[] >- (
      qpat_assum`typeset τ (Fun X Y) Z`mp_tac >>
      simp[Once (CONJUNCT1 semantics_cases)] >> strip_tac >>
      qpat_assum`typeset τ (Fun X Y) Z`mp_tac >>
      simp[Once (CONJUNCT1 semantics_cases)] >> strip_tac >>
      pop_assum mp_tac >>
      simp[Once (CONJUNCT1 semantics_cases)] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      match_mp_tac ABSTRACT_IN_FUNSPACE

      print_apropos``x <: funspace y z``


val semantics_typeset = store_thm("semantics_typeset",
  ``(∀τ ty mty. typeset τ ty mty ⇒
        ∀σ t mt. type_valuation τ ∧ term_valuation τ σ ∧
                 t has_type ty ∧ semantics σ τ t mt ⇒
                 mt <: mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        ∀ty mty. type_valuation τ ∧ term_valuation τ σ ∧
                 t has_type ty ∧ typeset τ ty mty ⇒
                 mt <: mty)``,

  ho_match_mp_tac semantics_ind >>
  simp[INDSET_INHABITED,FUNSPACE_INHABITED] >>
  conj_tac >- simp[type_valuation_def] >>
  conj_tac >- metis_tac[BOOLEAN_IN_BOOLSET] >>

  gen_tac >> Induct >> simp[Once semantics_cases]
  Induct
*)

val _ = export_theory()
