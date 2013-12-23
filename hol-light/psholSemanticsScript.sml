open HolKernel boolLib boolSimps SatisfySimps bossLib lcsymtacs miscTheory miscLib pred_setTheory pairTheory listTheory finite_mapTheory alistTheory holSyntaxLibTheory sholSyntaxTheory sholSyntaxExtraTheory polySetTheory sortingTheory stringTheory
val _ = numLib.prefer_num()
val _ = new_theory"psholSemantics"

val discharge_hyps_keep =
  match_mp_tac(PROVE[]``(p ∧ (p ∧ q ==> r)) ==> ((p ==> q) ==> r)``) >> conj_tac

val alist_to_fmap_id_map = store_thm("alist_to_fmap_id_map",
  ``∀ls f. alist_to_fmap (ZIP (ls, MAP f ls)) = FUN_FMAP f (set ls)``,
  Induct >> simp[] >>
  simp[GSYM fmap_EQ_THM] >>
  simp[FUN_FMAP_DEF,FAPPLY_FUPDATE_THM] >>
  rw[FUN_FMAP_DEF])
val _ = export_rewrites["alist_to_fmap_id_map"]

val mem = ``mem:'U->'U->bool``
val indset = ``indset:'U``
val ch = ``ch:'U->'U``
val s = ``(^mem,^indset,^ch)``

val _ = Parse.overload_on("M",s)

val is_choice_def = Define`
  is_choice ^mem ch = ∀x. (∃a. a <: x) ⇒ ch x <: x`

val is_infinite_def = Define`
  is_infinite ^mem s = INFINITE {a | a <: s}`

val is_model_def = Define`
  is_model ^s ⇔
    is_set_theory mem ∧
    is_infinite mem indset ∧
    is_choice mem ch`

val indset_inhabited = store_thm("indset_inhabited",
  ``is_infinite ^mem indset ⇒ ∃i. i <: indset``,
  rw[is_infinite_def] >> imp_res_tac INFINITE_INHAB >>
  fs[] >> metis_tac[])

val funspace_inhabited = store_thm("funspace_inhabited",
  ``is_set_theory ^mem ⇒ ∀s t. (∃x. x <: s) ∧ (∃x. x <: t) ⇒ ∃f. f <: Funspace s t``,
  rw[] >> qexists_tac`Abstract s t (λx. @x. x <: t)` >>
  match_mp_tac (MP_CANON abstract_in_funspace) >>
  metis_tac[])

val type_valuation_def = Define`
  type_valuation0 ^s τ ⇔ ∀x. x ∈ FRANGE τ ⇒ ∃y. y <: x`
val _ = Parse.overload_on("type_valuation",``type_valuation0 ^s``)

val type_valuation_FEMPTY = store_thm("type_valuation_FEMPTY",
  ``type_valuation FEMPTY``, rw[type_valuation_def])
val _ = export_rewrites["type_valuation_FEMPTY"]

val (semantics_rules,semantics_ind,semantics_cases) = xHol_reln"semantics"`
  (FLOOKUP τ s = SOME m ⇒ typeset0 ^mem ^indset ^ch τ (Tyvar s) m) ∧

  (typeset0 ^mem ^indset ^ch τ Bool boolset) ∧

  (typeset0 ^mem ^indset ^ch τ Ind indset) ∧

  (typeset0 ^mem ^indset ^ch τ x mx ∧ typeset0 ^mem ^indset ^ch τ y my
   ⇒
   typeset0 ^mem ^indset ^ch τ (Fun x y) (Funspace mx my)) ∧

  (closed p ∧ p has_type Fun rty Bool ∧
   LENGTH (tvars p) = LENGTH args ∧
   LIST_REL (typeset0 ^mem ^indset ^ch τ) args ams ∧
   τi = alist_to_fmap(ZIP(STRING_SORT(tvars p),ams)) ∧
   (∀τ. type_valuation τ ∧ set (tvars p) ⊆ FDOM τ ⇒
      ∃mrty mp w.
        typeset0 ^mem ^indset ^ch τ rty mrty ∧
        semantics0 ^mem ^indset ^ch FEMPTY τ p mp ∧
        w <: mrty ∧ Holds mp w) ∧
   typeset0 ^mem ^indset ^ch τi rty mrty ∧
   semantics0 ^mem ^indset ^ch FEMPTY τi p mp ∧
   w <: mrty ∧ Holds mp w
   ⇒
   typeset0 ^mem ^indset ^ch τ (Tyapp (Tydefined op p) args) (mrty suchthat Holds mp)) ∧

  (FLOOKUP σ (s,ty) = SOME m
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Var s ty) m) ∧

  (typeset0 ^mem ^indset ^ch τ ty mty
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Const "=" (Fun ty (Fun ty Bool)) Prim)
    (Abstract mty (Funspace mty boolset)
       (λx. Abstract mty boolset (λy. Boolean (x = y))))) ∧

  (typeset0 ^mem ^indset ^ch τ ty mty
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Const "@" (Fun (Fun ty Bool) ty) Prim)
     (Abstract (Funspace mty boolset) mty
       (λp. let mp = (mty suchthat Holds p) in
            ch (if ∃x. x <: mp then mp else mty)))) ∧

  (t = fresh_term {} t0 ∧ welltyped t ∧ closed t ∧
   set(tvars t) ⊆ set (tyvars (typeof t)) ∧
   tyinst tyin (typeof t) = ty ∧
   semantics0 ^mem ^indset ^ch FEMPTY τ (simple_inst tyin t) mt
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Const s ty (Defined t0)) mt) ∧

  (typeset0 ^mem ^indset ^ch τ (Tyapp (Tydefined op p) args) maty ∧
   p has_type Fun rty Bool ∧
   LIST_REL (typeset0 ^mem ^indset ^ch τ) args ams ∧
   τi = alist_to_fmap(ZIP(STRING_SORT(tvars p),ams)) ∧
   typeset0 ^mem ^indset ^ch τi rty mrty ∧
   tyin = alist_to_fmap(ZIP(STRING_SORT(tvars p),args))
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Const s (Fun (Tyapp (Tydefined op p) args) (tyinst tyin rty)) (Tyrep op p))
    (Abstract maty mrty (λx. x))) ∧

  (typeset0 ^mem ^indset ^ch τ (Tyapp (Tydefined op p) args) maty ∧
   p has_type Fun rty Bool ∧
   LIST_REL (typeset0 ^mem ^indset ^ch τ) args ams ∧
   τi = alist_to_fmap(ZIP(STRING_SORT(tvars p),ams)) ∧
   typeset0 ^mem ^indset ^ch τi rty mrty ∧
   semantics0 ^mem ^indset ^ch FEMPTY τi p mp ∧
   tyin = alist_to_fmap(ZIP(STRING_SORT(tvars p),args))
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Const s (Fun (tyinst tyin rty) (Tyapp (Tydefined op p) args)) (Tyabs op p))
    (Abstract mrty maty (λx. if Holds mp x then x else ch maty))) ∧

  (semantics0 ^mem ^indset ^ch σ τ t1 m1 ∧
   semantics0 ^mem ^indset ^ch σ τ t2 m2 ∧
   welltyped (Comb t1 t2)
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Comb t1 t2) (m1 ' m2)) ∧

  (typeset0 ^mem ^indset ^ch τ ty mty ∧
   b has_type tyb ∧
   typeset0 ^mem ^indset ^ch τ tyb mtyb ∧
   (∀m. m <: mty ⇒ (mb m) <: mtyb ∧ semantics0 ^mem ^indset ^ch (σ|+((s,ty),m)) τ b (mb m))
   ⇒
   semantics0 ^mem ^indset ^ch σ τ (Abs s ty b) (Abstract mty mtyb mb))`
val _ = Parse.overload_on("semantics",``semantics0 ^mem ^indset ^ch``)
val _ = Parse.overload_on("typeset",``typeset0 ^mem ^indset ^ch``)

val typeset_Bool = store_thm("typeset_Bool",
  ``typeset τ Bool ty ⇔ ty = boolset``,
  simp[Once semantics_cases])
val _ = export_rewrites["typeset_Bool"]

val typeset_Ind = store_thm("typeset_Ind",
  ``typeset τ Ind ty ⇔ ty = indset``,
  rw[Once semantics_cases] >> rw[EQ_IMP_THM])
val _ = export_rewrites["typeset_Ind"]

val term_valuation_def = Define`
  term_valuation0 ^s τ σ ⇔
    FEVERY (λ(v,m). ∃mty. typeset τ (SND v) mty ∧ m <: mty) σ`
val _ = Parse.overload_on("term_valuation",``term_valuation0 ^s``)

val term_valuation_FEMPTY = store_thm("term_valuation_FEMPTY",
  ``term_valuation τ FEMPTY``,
  rw[term_valuation_def,FEVERY_DEF])
val _ = export_rewrites["term_valuation_FEMPTY"]

val term_valuation_FUPDATE = store_thm("term_valuation_FUPDATE",
  ``∀τ σ kv mty. term_valuation τ σ ∧ typeset τ (SND(FST kv)) mty ∧ (SND kv) <: mty ⇒ term_valuation τ (σ |+ kv)``,
  rw[term_valuation_def] >>
  Cases_on`kv` >>
  match_mp_tac(CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
  fs[] >> metis_tac[])

val term_valuation_FUPDATE_LIST = store_thm("term_valuation_FUPDATE_LIST",
  ``∀ls τ σ. term_valuation τ σ ∧ EVERY (λ(v,m). ∃mty. typeset τ (SND v) mty ∧ m <: mty) ls ⇒ term_valuation τ (σ |++ ls)``,
  Induct >> simp[FUPDATE_LIST_THM] >>
  Cases>>fs[]>>rw[]>>
  first_x_assum match_mp_tac >> rw[] >>
  match_mp_tac term_valuation_FUPDATE >>
  rw[] >> metis_tac[])

val type_valuation_reduce = store_thm("type_valuation_reduce",
  ``∀τ τ'. type_valuation τ' ∧ τ ⊑ τ' ⇒ type_valuation τ``,
  rw[type_valuation_def,IN_FRANGE,SUBMAP_DEF] >> metis_tac[])

val term_valuation_reduce = store_thm("term_valuation_reduce",
  ``∀τ σ σ'. term_valuation τ σ' ∧ σ ⊑ σ' ⇒ term_valuation τ σ``,
  metis_tac[term_valuation_def,FEVERY_SUBMAP])

val typeset_inhabited = store_thm("typeset_inhabited",
  ``is_model M ⇒ ∀ty τ mty. type_valuation τ ∧ typeset τ ty mty ⇒ ∃m. m <: mty``,
  strip_tac >>
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    simp[type_valuation_def] >>
    simp[Once semantics_cases] >>
    simp[FLOOKUP_DEF,FRANGE_DEF] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once semantics_cases] >>
  rw[] >- metis_tac[boolean_in_boolset,is_model_def]
  >- metis_tac[indset_inhabited,is_model_def]
  >- (fs [] >> metis_tac[funspace_inhabited,is_model_def]) >>
  fs[is_model_def] >>
  simp[mem_sub] >>
  metis_tac[] )

val tac1 =
    `ams' = ams` by (
      simp_tac(srw_ss())[LIST_EQ_REWRITE] >>
      rpt(qpat_assum`LIST_REL P X Y`mp_tac) >>
      rpt(qpat_assum`LENGTH X = Y`mp_tac) >>
      simp_tac(srw_ss())[EVERY2_EVERY] >>
      simp_tac(srw_ss())[EVERY_MEM,GSYM AND_IMP_INTRO] >>
      simp_tac(srw_ss())[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[]) >> rpt BasicProvers.VAR_EQ_TAC

val tac2 =
    `type_valuation ti` by (
      simp_tac(srw_ss())[Abbr`ti`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      rpt(qpat_assum`EVERY2 P X Y`mp_tac) >>
      rpt(qpat_assum`LENGTH X = LENGTH Y`mp_tac) >>
      simp_tac(srw_ss())[EVERY2_EVERY,GSYM AND_IMP_INTRO] >>
      simp_tac(srw_ss())[MAP_ZIP] >>
      simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
      simp_tac(srw_ss())[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[typeset_inhabited] )

val semantics_11 = store_thm("semantics_11",
  ``is_model M ⇒
    (∀τ ty mty. typeset τ ty mty ⇒
        ∀mty'. type_valuation τ ∧ typeset τ ty mty' ⇒ mty' = mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        ∀mt'. type_valuation τ ∧ semantics σ τ t mt' ⇒ mt' = mt)``,
  strip_tac >>
  ho_match_mp_tac semantics_ind >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    PROVE_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    qmatch_assum_abbrev_tac`X = ti` >>
    simp_tac(srw_ss())[Abbr`X`] >> rpt strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac WELLTYPED_LEMMA >>
    tac1 >> tac2 >>
    rpt(qpat_assum`typeof t = X`mp_tac) >> simp_tac(srw_ss())[] >>
    metis_tac[]) >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    metis_tac[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_abbrev_tac`welltyped t` >>
    `simple_inst tyin t = simple_inst tyin' t` by (
      simp[simple_inst_tvars] >>
      fs[SUBSET_DEF] >>
      metis_tac[tyinst_tyvars] ) >>
    fs[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qmatch_assum_abbrev_tac`τ' = ti` >>
    qmatch_assum_abbrev_tac`X = tyi` >>
    qunabbrev_tac`X` >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac std_ss [Once semantics_cases] >>
    simp_tac(srw_ss())[]>>rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    tac1 >>
    qpat_assum`typeset X Y maty`mp_tac >>
    simp_tac(srw_ss())[Once semantics_cases] >>
    rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    last_x_assum(qspec_then`mrty' suchthat Holds mp`mp_tac) >>
    asm_simp_tac(srw_ss())[Once semantics_cases] >>
    discharge_hyps >- metis_tac[] >>
    tac1 >> tac2 >>
    fs[] >> rfs[] >> imp_res_tac WELLTYPED_LEMMA >> fs[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qmatch_assum_abbrev_tac`τ' = ti` >>
    qmatch_assum_abbrev_tac`X = tyi` >>
    qunabbrev_tac`X` >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac (srw_ss()) [Once semantics_cases] >>
    rpt strip_tac >>
    tac1 >>
    `maty = mty` by metis_tac[] >>
    qpat_assum`typeset X Y maty`mp_tac >>
    simp_tac (srw_ss()) [Once semantics_cases] >>
    rpt strip_tac >>
    tac1 >> tac2 >>
    imp_res_tac WELLTYPED_LEMMA >>
    ntac 3 (pop_assum mp_tac) >>
    simp_tac(srw_ss())[] >>
    metis_tac[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac std_ss [Once semantics_cases] >>
    simp_tac (srw_ss()) [] >>
    metis_tac[] ) >>
  rpt gen_tac >>
  strip_tac >>
  simp_tac std_ss [Once semantics_cases] >>
  simp_tac (srw_ss()) [] >>
  rpt strip_tac >>
  imp_res_tac WELLTYPED_LEMMA >>
  res_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  match_mp_tac (MP_CANON abstract_eq) >>
  conj_tac >- fs[is_model_def] >>
  fs[] >> res_tac >> fs[])

val typeset_tyvars = store_thm("typeset_tyvars",
  ``(∀τ1 ty m. typeset τ1 ty m ⇒ ∀τ2. (∀x. x ∈ set(tyvars ty) ∧ x ∈ FDOM τ1 ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ typeset τ2 ty m) ∧
    (∀σ τ1 tm m. semantics σ τ1 tm m ⇒ ∀τ2. (∀x. x ∈ set(tvars tm) ∧ x ∈ FDOM τ1 ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ semantics σ τ2 tm m)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    qmatch_assum_rename_tac`w <: mrty`[] >>
    qmatch_assum_rename_tac`Holds mp w`[] >>
    map_every qexists_tac[`ams`,`mp`,`mrty`,`ty`,`w`] >> simp[] >>
    conj_tac >- (
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >>
      simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      first_x_assum match_mp_tac >>
      rw[] >>
      first_x_assum match_mp_tac >>
      simp[MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL]) >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[tvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`tyin` >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_tyinst,tvars_simple_inst] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`ams`,`m`,`m'`,`ty`] >>
    simp[] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >>
    simp[] >>
    imp_res_tac EVERY2_LENGTH >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[MEM_FOLDR_LIST_UNION] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qpat_assum`typeset X Y m`(strip_assume_tac o SIMP_RULE(srw_ss())[Once semantics_cases]) >>
    map_every qexists_tac[`ams`,`m`,`m'`,`m''`,`ty`] >>
    rw[] >>
    match_mp_tac EVERY2_MEM_MONO >>
    qmatch_assum_abbrev_tac`LIST_REL P args ams` >>
    qexists_tac`P` >>
    simp[Abbr`P`] >>
    imp_res_tac EVERY2_LENGTH >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[MEM_FOLDR_LIST_UNION] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`mb`,`m`,`m'`,`ty'`] >>
  rw[] >>
  first_x_assum match_mp_tac >>
  rw[] >>
  imp_res_tac tyvars_typeof_subset_tvars >>
  fs[SUBSET_DEF])

val typeset_closes_over = store_thm("typeset_closes_over",
  ``is_model M ⇒
    (∀τ ty m. typeset τ ty m ⇒ type_valuation τ ⇒ set (tyvars ty) ⊆ FDOM τ) ∧
    (∀σ τ tm m. semantics σ τ tm m ⇒
      type_valuation τ ∧ (∀s m ty. (s,ty) ∈ FDOM σ ⇒ set (tyvars ty) ⊆ FDOM τ)
      ⇒ set (tvars tm) ⊆ FDOM τ)``,
  strip_tac >>
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[tyvars_def] >>
  conj_tac >- ( rw[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FOLDR_LIST_UNION,EVERY_MEM,EVERY2_EVERY] >>
    fs[GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    `∃n. n < LENGTH args ∧ y = EL n args` by metis_tac[MEM_EL] >>
    first_x_assum (qspec_then`n`mp_tac) >> simp[] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[FLOOKUP_DEF,tvars_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[tyvars_tyinst,SUBSET_DEF,tvars_def] >> fs[] >>
    qmatch_assum_abbrev_tac`∀x. MEM x (tvars (simple_inst tyin tm)) ⇒ x ∈ FDOM τ` >>
    last_x_assum match_mp_tac >>
    simp[tvars_simple_inst] >>
    metis_tac[tyvars_typeof_subset_tvars,WELLTYPED,MAP,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    qpat_assum`typeset τ X m` mp_tac >>
    simp[Once semantics_cases] >> rw[] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[MAP_ZIP] >>
    fs[SUBSET_DEF] >>
    simp[tyvars_tyinst] >>
    fs[FLOOKUPD_def,MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      rfs[MEM_ZIP,tyvars_def,SUBSET_DEF] >>
      metis_tac[tvars_ALL_DISTINCT,LENGTH_STRING_SORT,MEM_STRING_SORT,MEM_EL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[tvars_ALL_DISTINCT,LENGTH_STRING_SORT,MEM_STRING_SORT,MEM_EL] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    qpat_assum`typeset τ X m` mp_tac >>
    simp[Once semantics_cases] >> rw[] >>
    imp_res_tac EVERY2_LENGTH >>
    fs[MAP_ZIP] >>
    fs[SUBSET_DEF] >>
    simp[tyvars_tyinst] >>
    fs[FLOOKUPD_def,MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      rfs[MEM_ZIP,tyvars_def,SUBSET_DEF] >>
      metis_tac[tvars_ALL_DISTINCT,LENGTH_STRING_SORT,MEM_STRING_SORT,MEM_EL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[tvars_ALL_DISTINCT,LENGTH_STRING_SORT,MEM_STRING_SORT,MEM_EL] ) >>
  rw[tvars_def,tyvars_def] >>
  metis_tac[typeset_inhabited])

val semantics_raconv = store_thm("semantics_raconv",
  ``∀env tp.
      RACONV env tp ⇒
      ∀σ1 σ2 τ.
        type_valuation τ ∧
        term_valuation τ σ1 ∧
        term_valuation τ σ2 ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (semantics σ1 τ (Var x1 ty1) =
             semantics σ2 τ (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        (semantics σ1 τ (FST tp) =
         semantics σ2 τ (SND tp))``,
  ho_match_mp_tac RACONV_strongind >>
  simp[FORALL_PROD] >>
  conj_tac >- (
    rw[] >>
    simp[Once FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[Once (CONJUNCT1 (SPEC_ALL semantics_cases))] >>
    simp[Once (CONJUNCT1 (SPEC_ALL semantics_cases)),SimpRHS] >>
    srw_tac[DNF_ss][] >> rfs[] >>
    `semantics σ1 τ s1 = semantics σ2 τ s2` by metis_tac[] >>
    `semantics σ1 τ t1 = semantics σ2 τ t2` by metis_tac[] >>
    simp[] ) >>
  rw[] >>
  simp[Once FUN_EQ_THM] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases,SimpRHS] >>
  rw[] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  simp[] >>
  qmatch_assum_abbrev_tac`RACONV env' (t1,t2)` >>
  qspecl_then[`env'`,`t1,t2`]mp_tac RACONV_TYPE >>
  simp[Abbr`env'`] >> strip_tac >>
  (conj_tac >- metis_tac[WELLTYPED,WELLTYPED_LEMMA]) >>
  rw[] >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_abbrev_tac`semantics σ2' τ tq mm` >>
  qmatch_assum_abbrev_tac`semantics σ1' τ tp mm` >>
  (qsuff_tac`semantics σ1' τ tp = semantics σ2' τ tq` >- metis_tac[]) >>
  (first_x_assum match_mp_tac ORELSE (match_mp_tac EQ_SYM >> first_x_assum match_mp_tac)) >>
  fs[term_valuation_def] >>
  (conj_tac >- (
    simp[Abbr`σ2'`,Abbr`σ1'`] >>
    match_mp_tac (CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
    simp[] >> metis_tac[] )) >>
  (conj_tac >- (
    simp[Abbr`σ2'`,Abbr`σ1'`] >>
    match_mp_tac (CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
    simp[] >> metis_tac[] )) >>
  simp[ALPHAVARS_def] >>
  (rw[] >- (
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[FLOOKUP_DEF,Abbr`σ1'`,Abbr`σ2'`] )) >>
  qmatch_assum_rename_tac`ALPHAVARS env (Var va vta, Var vb vtb)`[] >>
  first_x_assum(qspecl_then[`va`,`vta`,`vb`,`vtb`]mp_tac) >>
  simp[] >>
  simp[FUN_EQ_THM,Once(CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  simp[Once(CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  simp[Once(CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  simp[Once(CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  simp[Abbr`σ1'`,Abbr`σ2'`,FLOOKUP_UPDATE])

val semantics_aconv = store_thm("semantics_aconv",
  ``∀σ τ s t.
      type_valuation τ ∧ term_valuation τ σ ∧ welltyped s ∧ ACONV s t
      ⇒ semantics σ τ s = semantics σ τ t``,
  rw[] >> imp_res_tac ACONV_welltyped >>
  fs[ACONV_def]  >>
  qspecl_then[`[]`,`s,t`] mp_tac semantics_raconv >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[ALPHAVARS_def])

val closes_def = Define`
  closes s t tm ⇔
    set (tvars tm) ⊆ t ∧
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ (x,ty) ∈ s)`

val closes_extend = store_thm("closes_extend",
  ``∀σ τ t σ' τ'. closes σ τ t ∧ σ ⊆ σ' ∧ τ ⊆ τ' ⇒ closes σ' τ' t``,
  rw[SUBMAP_DEF,closes_def,SUBSET_DEF])

val semantics_closes = prove(
  ``is_model M ⇒
    (∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ type_valuation τ ∧ term_valuation τ σ ⇒ closes (FDOM σ) (FDOM τ) t)``,
  strip_tac >>
  ho_match_mp_tac(theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    simp[term_valuation_def,FEVERY_DEF,FORALL_PROD] >>
    rw[tvars_def] >> metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tvars_def] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    qmatch_assum_abbrev_tac`∀x. MEM x (tvars (inst tyin tm)) ⇒ x ∈ FDOM τ` >>
    qspecl_then[`tm`,`tyin`]strip_assume_tac tvars_simple_inst >>
    rfs[EXTENSION] >>
    imp_res_tac WELLTYPED >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  let val tac = (
    rw[closes_def,tyvars_def,tvars_def] >>
    TRY ( imp_res_tac typeset_closes_over >> fs[tyvars_def] >> NO_TAC ) >>
    simp[tyvars_tyinst,SUBSET_DEF,FLOOKUPD_def] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[tyvars_def,SUBSET_DEF] >>
    simp[GSYM LEFT_FORALL_IMP_THM] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,tyvars_def] >>
      qpat_assum`typeset τ (X Y) Z`mp_tac >>
      simp[Once semantics_cases] >> rw[] >>
      fs[MEM_ZIP] >>
      metis_tac[MEM_EL,tvars_ALL_DISTINCT,LENGTH_STRING_SORT,MEM_STRING_SORT] ) >>
    imp_res_tac ALOOKUP_MEM >>
    qpat_assum`typeset τ (X Y) Z`mp_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[MEM_ZIP,EVERY_MEM,EVERY2_EVERY] >>
    qpat_assum`LENGTH X = LENGTH ams`assume_tac >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] )
  in
    conj_tac >- tac >>
    conj_tac >- tac
  end >>
  conj_tac >- (
    rw[closes_def,tvars_def] >> fs[] >> metis_tac[] ) >>
  (
    fs[closes_def,tvars_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- metis_tac[typeset_closes_over] >> fs[] >>
    qmatch_assum_rename_tac`typeset τ ty mty`[] >>
    `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
    first_x_assum(qspec_then`m`mp_tac)>>simp[]>>strip_tac>>
    pop_assum mp_tac >>
    discharge_hyps >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    rw[] >> metis_tac[]))
val semantics_closes = save_thm("semantics_closes",MP_CANON (DISCH_ALL (CONJUNCT2 (UNDISCH semantics_closes))))

val closes_Comb = store_thm("closes_Comb",
  ``∀env σ τ t1 t2. closes σ τ (Comb t1 t2) ⇔ closes σ τ t1 ∧ closes σ τ t2``,
  rw[closes_def,tvars_def] >> metis_tac[])
val _ = export_rewrites["closes_Comb"]

val closes_Abs = store_thm("closes_Abs",
  ``∀s t x ty tm. closes s t (Abs x ty tm) ⇔ set (tyvars ty) ⊆ t ∧ closes ((x,ty)INSERT s) t tm``,
  rw[closes_def,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EXISTS_PROD,tvars_def] >>
  metis_tac[])
val _ = export_rewrites["closes_Abs"]

val closes_Const = store_thm("closes_Const",
  ``∀σ τ s ty c. closes σ τ (Const s ty c) ⇔ set (tyvars ty) ⊆ τ``,
  rw[closes_def,tvars_def])
val _ = export_rewrites["closes_Const"]

val closes_Var = store_thm("closes_Var",
  ``∀σ τ n ty. closes σ τ (Var n ty) ⇔ set (tyvars ty) ⊆ τ ∧ (n,ty) ∈ σ``,
  rw[closes_def,tvars_def])
val _ = export_rewrites["closes_Var"]

val closes_equation = store_thm("closes_equation",
  ``l has_type ty ∧ r has_type ty ⇒
  (closes σ τ (l === r) ⇔ closes σ τ l ∧ closes σ τ r)``,
  rw[closes_def,equation_def,tyvars_def,tvars_def] >> rw[EQ_IMP_THM] >>
  imp_res_tac tyvars_typeof_subset_tvars >>
  fs[SUBSET_DEF] >> metis_tac[WELLTYPED_LEMMA] )

val semantics_simple_inst = store_thm("semantics_simple_inst",
  ``is_model M ⇒
    (∀τi ty m. typeset τi ty m ⇒
       ∀τ tyin.
         type_valuation τi ∧ type_valuation τ ∧
         (∀a. MEM a (tyvars ty) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a))
         ⇒
         typeset τ (tyinst tyin ty) m) ∧
    (∀σi τi tm m. semantics σi τi tm m ⇒
        ∀σ τ tyin.
          type_valuation τi ∧ type_valuation τ ∧
          (∀a. MEM a (tvars tm) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a)) ∧
          (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst tyin ty)) ∧
          ALL_DISTINCT (bv_names tm) ∧
          DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
          ⇒
          semantics σ τ (simple_inst tyin tm) m)``,
  strip_tac >>
  ho_match_mp_tac (theorem"semantics_strongind") >>
  conj_tac >- simp[tyvars_def,FLOOKUP_DEF] >>
  conj_tac >- simp[tyvars_def] >>
  conj_tac >- simp[tyvars_def] >>
  conj_tac >- (
    simp[tyvars_def] >> rw[] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tyvars_def] >>
    qmatch_assum_rename_tac`w <: mp`[] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`ams`,`m`,`mp`,`ty`,`w`] >>
    simp[] >>
    conj_tac >- (
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      simp[] >>
      fs[MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL]) >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`m` >> simp[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`m` >> simp[] ) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    rw[tyinst_tyinst] >>
    fs[simple_inst_compose] >>
    qho_match_abbrev_tac`∃x. tyinst a z = tyinst x z ∧ c x` >>
    qexists_tac`a` >>
    unabbrev_all_tac >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[fresh_term_def] >>
    imp_res_tac semantics_closes >>
    fs[closes_def] >>
    simp[tvars_simple_inst,GSYM LEFT_FORALL_IMP_THM] >>
    fs[tyvars_tyinst,GSYM LEFT_FORALL_IMP_THM] >>
    fs[SUBSET_DEF] >>
    metis_tac[]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`ams`,`m`,`m'`,`ty`] >>
    simp[] >>
    simp[tyinst_tyinst] >>
    conj_tac >- (
      match_mp_tac tyinst_tyvars1 >>
      simp[FLOOKUPD_def,FLOOKUP_FUNION,FLOOKUP_o_f] >>
      `LENGTH (tvars p) = LENGTH args` by (
        qpat_assum`typeset X Y m` mp_tac >>
        simp[Once semantics_cases] >> rw[] ) >>
      simp[ALOOKUP_ZIP_MAP_SND] >>
      rw[] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF,ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        metis_tac[MEM_EL,LENGTH_STRING_SORT,MEM_STRING_SORT,tvars_ALL_DISTINCT] ) >>
      simp[] ) >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >> simp[] >>
    imp_res_tac EVERY2_LENGTH >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[] >>
    fs[MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`ams`,`m`,`m'`,`m''`,`ty`] >>
    simp[] >>
    simp[tyinst_tyinst] >>
    conj_tac >- (
      match_mp_tac tyinst_tyvars1 >>
      simp[FLOOKUPD_def,FLOOKUP_FUNION,FLOOKUP_o_f] >>
      `LENGTH (tvars tm) = LENGTH args` by (
        qpat_assum`typeset X Y m` mp_tac >>
        simp[Once semantics_cases] >> rw[] ) >>
      simp[ALOOKUP_ZIP_MAP_SND] >>
      rw[] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF,ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        metis_tac[MEM_EL,LENGTH_STRING_SORT,MEM_STRING_SORT,tvars_ALL_DISTINCT] ) >>
      simp[] ) >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >> simp[] >>
    imp_res_tac EVERY2_LENGTH >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[] >>
    fs[MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`m`,`m'`] >>
    simp[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_asm1_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
    conj_asm1_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >>
    qspecl_then[`tm'`,`tyin`]mp_tac simple_inst_has_type >>
    rw[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    rw[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`mb`,`m`,`m'`] >>
  qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  rw[] >>
  qexists_tac`tyinst tyin (typeof tm)` >>
  simp[] >>
  conj_asm1_tac >- (
    imp_res_tac WELLTYPED_LEMMA >>
    rw[] >>
    first_x_assum match_mp_tac >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF] ) >>
  qx_gen_tac`z` >> strip_tac >>
  first_x_assum(qspec_then`z`mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[] >>
  fs[IN_DISJOINT] >>
  reverse conj_tac >- metis_tac[] >>
  qx_genl_tac[`x`,`tx`] >> strip_tac >>
  reverse(Cases_on`s=x`) >- simp[FLOOKUP_UPDATE] >>
  reverse(Cases_on`tx=ty`) >> simp[FLOOKUP_UPDATE] >> rw[] >>
  metis_tac[])

val ABSTRACT_IN_FUNSPACE = MP_CANON abstract_in_funspace

val semantics_typeset = store_thm("semantics_typeset",
  ``is_model M ⇒
    (∀τ ty mty. typeset τ ty mty ⇒ type_valuation τ ⇒ ∃mt. mt <: mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        type_valuation τ ∧ term_valuation τ σ ⇒
           ∃mty. welltyped t ∧ typeset τ (typeof t) mty ∧ mt <: mty)``,
  strip_tac >>
  ho_match_mp_tac (theorem"semantics_strongind") >>
  conj_tac >- (
    simp[type_valuation_def] >>
    simp[FLOOKUP_DEF,FRANGE_DEF] >>
    metis_tac[] ) >>
  conj_tac >- metis_tac[boolean_in_boolset,is_model_def] >>
  conj_tac >- metis_tac[is_model_def,indset_inhabited] >>
  conj_tac >- metis_tac[is_model_def,funspace_inhabited] >>
  conj_tac >- ( fs[is_model_def] >> rw[mem_sub] >> metis_tac[] ) >>
  conj_tac >- (
    simp[] >> rw[] >>
    fs[term_valuation_def] >>
    imp_res_tac FEVERY_FLOOKUP >>
    fs[] >> metis_tac[]) >>
  conj_tac >- (
    rw[] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 (SPEC_ALL semantics_cases)))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    fs[is_model_def] >>
    match_mp_tac (MP_CANON abstract_in_funspace) >> rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    rw[boolean_in_boolset]) >>
  conj_tac >- (
    rw[] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 (SPEC_ALL semantics_cases)))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    fs[is_model_def] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    fs[mem_sub] >> rw[] >- (
      qmatch_abbrev_tac`ch s <: mty` >>
      `ch s <: s` by (
        fs[is_choice_def] >>
        first_x_assum match_mp_tac >>
        rfs[Abbr`s`,mem_sub] >>
        metis_tac[] ) >>
      rfs[Abbr`s`,mem_sub] ) >>
    fs[is_choice_def] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> fs[] >>
    qmatch_assum_abbrev_tac`welltyped (inst tyin tm)` >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac(CONJUNCT1 (UNDISCH typeset_closes_over)) >> fs[] >>
    metis_tac[WELLTYPED_LEMMA,typeset_tyvars,MEM]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_abbrev_tac`typeset tt ty mtt` >>
    map_every qexists_tac[`mty`,`mtt`] >>
    simp[] >>
    `type_valuation tt` by (
      simp[Abbr`tt`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      qpat_assum`typeset X Y mty` mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      simp[MAP_ZIP] >>
      qpat_assum`LENGTH X = LENGTH ams`assume_tac >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL] ) >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 (UNDISCH semantics_simple_inst))) >>
      qexists_tac`tt` >>
      simp[] >>
      gen_tac >> strip_tac >>
      `LENGTH (tvars p) = LENGTH ams` by (
        qpat_assum`typeset X Y mty` mp_tac >>
        simp[Once semantics_cases] >> rw[] >>
        fs[EVERY2_EVERY] ) >>
      `a ∈ FDOM tt` by (
        simp[Abbr`tt`,MAP_ZIP] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF] ) >>
      `∃z. FLOOKUP tt a = SOME z` by simp[FLOOKUP_DEF] >>
      `tt ' a = z` by fs[FLOOKUP_DEF] >>
      pop_assum SUBST1_TAC >>
      pop_assum mp_tac >>
      simp[Abbr`tt`,FLOOKUPD_def] >>
      strip_tac >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      qmatch_assum_abbrev_tac`a = EL n ls` >>
      Q.ISPECL_THEN[`ZIP(ls,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      simp[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rw[] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[] ) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> simp[] >>
    conj_asm1_tac >- metis_tac[is_model_def] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    rfs[mem_sub] >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[] >> rw[] >>
    `ams' = ams` by (
      simp[LIST_EQ_REWRITE] >>
      fs[EVERY2_EVERY] >>
      fs[EVERY_MEM] >>
      qpat_assum`LENGTH X = LENGTH ams`(assume_tac) >>
      qpat_assum`LENGTH args = LENGTH X`(assume_tac) >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[semantics_11]) >> rw[] >>
    metis_tac[semantics_11]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_abbrev_tac`typeset tt ty mtt` >>
    map_every qexists_tac[`mtt`,`mty`] >>
    simp[] >>
    `type_valuation tt` by (
      simp[Abbr`tt`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      qpat_assum`typeset X Y mty` mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      simp[MAP_ZIP] >>
      qpat_assum`LENGTH X = LENGTH ams`assume_tac >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL] ) >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 (UNDISCH semantics_simple_inst))) >>
      qexists_tac`tt` >>
      simp[] >>
      gen_tac >> strip_tac >>
      `LENGTH (tvars t) = LENGTH ams` by (
        qpat_assum`typeset X Y mty` mp_tac >>
        simp[Once semantics_cases] >> rw[] >>
        fs[EVERY2_EVERY] ) >>
      `a ∈ FDOM tt` by (
        simp[Abbr`tt`,MAP_ZIP] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF] ) >>
      `∃z. FLOOKUP tt a = SOME z` by simp[FLOOKUP_DEF] >>
      `tt ' a = z` by fs[FLOOKUP_DEF] >>
      pop_assum SUBST1_TAC >>
      pop_assum mp_tac >>
      simp[Abbr`tt`,FLOOKUPD_def] >>
      strip_tac >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      qmatch_assum_abbrev_tac`a = EL n ls` >>
      Q.ISPECL_THEN[`ZIP(ls,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      simp[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rw[] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[] ) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> simp[] >>
    conj_asm1_tac >- fs[is_model_def] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    rfs[mem_sub] >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    `ams' = ams` by (
      simp[LIST_EQ_REWRITE] >>
      fs[EVERY2_EVERY] >>
      fs[EVERY_MEM] >>
      qpat_assum`LENGTH X = LENGTH ams`(assume_tac) >>
      qpat_assum`LENGTH args = LENGTH X`(assume_tac) >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[semantics_11]) >>
    BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC
      >- metis_tac[semantics_11] >>
    `is_choice mem ch` by fs[is_model_def] >>
    `ch (mrty suchthat Holds mp) <: (mrty suchthat Holds mp)` by (
      fs[is_choice_def] >>
      pop_assum match_mp_tac >>
      simp[mem_sub] >>
      metis_tac[] ) >>
    rfs[mem_sub]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    fs[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 (SPEC_ALL semantics_cases)))] >> rw[] >>
    qexists_tac`my` >> simp[] >>
    match_mp_tac (MP_CANON apply_in_rng) >>
    metis_tac[semantics_11,is_model_def]) >>
  rw[] >> fs[] >>
  simp[Once semantics_cases] >>
  res_tac >>
  pop_assum mp_tac >>
  discharge_hyps >- (
    match_mp_tac term_valuation_FUPDATE >>
    rw[] >> metis_tac[] ) >>
  rw[] >>
  fsrw_tac[DNF_ss][] >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  qmatch_assum_rename_tac`typeset τ (typeof t) tty`[] >>
  map_every qexists_tac[`mty`,`tty`] >> rw[] >>
  match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
  fs[is_model_def])

val semantics_frees = store_thm("semantics_frees",
  ``∀τ1 τ2 σ1 σ2 t.
      type_valuation τ1 ∧ type_valuation τ2 ∧
      (∀x. MEM x (tvars t) ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ (FLOOKUP σ1 (x,ty) = FLOOKUP σ2 (x,ty)))
      ⇒ semantics σ1 τ1 t = semantics σ2 τ2 t``,
  gen_tac >> (CONV_TAC (RESORT_FORALL_CONV List.rev)) >> Induct
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases] )
  >- (
    rw[FUN_EQ_THM,tvars_def] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS]>>
    rw[EQ_IMP_THM] >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[SUBSET_DEF] >>
      fs[tyvars_tyinst] >>
      metis_tac[typeset_tyvars,SIMP_RULE(srw_ss())[EXTENSION]tvars_simple_inst] )
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`ams`,`maty`,`mrty`,`rty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 typeset_tyvars)) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL])
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`ams`,`maty`,`mp`,`mrty`,`rty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 typeset_tyvars)) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL])
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[SUBSET_DEF] >>
      fs[tyvars_tyinst] >>
      metis_tac[typeset_tyvars,SIMP_RULE(srw_ss())[EXTENSION]tvars_simple_inst] )
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`ams`,`maty`,`mrty`,`rty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 typeset_tyvars)) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL])
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`ams`,`maty`,`mp`,`mrty`,`rty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >> simp[] >>
      imp_res_tac EVERY2_LENGTH >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 typeset_tyvars)) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL]))
  >- (
    rw[FUN_EQ_THM,tvars_def] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS] >>
    metis_tac[]) >>
  rw[FUN_EQ_THM,tvars_def] >>
  rw[Once semantics_cases] >>
  rw[Once semantics_cases,SimpRHS] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  rw[] >>
  TRY(qmatch_abbrev_tac `typeset X t mty` >> metis_tac[typeset_tyvars]) >>
  TRY(qmatch_abbrev_tac `typeset X tyb mtyb` >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
    HINT_EXISTS_TAC >>
    rw[] >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF]) >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_abbrev_tac`semantics (f |+ z) τ tt mm` >>
  qmatch_assum_abbrev_tac`semantics (g |+ z) τ' tt mm` >>
  (qsuff_tac`semantics (f|+z) τ tt = semantics (g|+z) τ' tt` >- rw[]) >>
  (first_x_assum match_mp_tac ORELSE
   (match_mp_tac EQ_SYM >> first_x_assum match_mp_tac)) >>
  simp[Abbr`z`,FLOOKUP_UPDATE] >>
  metis_tac[])

val semantics_extend = store_thm("semantics_extend",
  ``∀σ τ t m σ' τ'. type_valuation τ' ∧ is_model M ∧
                    term_valuation τ σ ∧
                    term_valuation τ' σ' ∧
                 semantics σ τ t m ∧ σ ⊑ σ' ∧ τ ⊑ τ'
                 ⇒ semantics σ' τ' t m``,
  rw[] >>
  imp_res_tac type_valuation_reduce >>
  `closes (FDOM σ) (FDOM τ) t` by metis_tac[semantics_closes] >>
  qsuff_tac`semantics σ' τ' t = semantics σ τ t`>-rw[] >>
  match_mp_tac semantics_frees >>
  fs[closes_def,SUBSET_DEF,SUBMAP_DEF,FLOOKUP_DEF])

val semantics_reduce = store_thm("semantics_reduce",
  ``∀σ τ t m τ' σ'. type_valuation τ' ∧ term_valuation τ' σ' ∧
                 semantics σ' τ' t m ∧ σ ⊑ σ' ∧ τ ⊑ τ' ∧
                 closes (FDOM σ) (FDOM τ) t
                 ⇒ semantics σ τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  imp_res_tac type_valuation_reduce >>
  qsuff_tac`semantics σ τ t = semantics σ' τ' t`>-rw[] >>
  match_mp_tac semantics_frees >> simp[] >>
  fs[closes_def,SUBSET_DEF,FORALL_PROD,FLOOKUP_DEF,SUBMAP_DEF])

val typeset_extend = store_thm("typeset_extend",
  ``∀τ ty mty τ'. typeset τ ty mty ∧ τ ⊑ τ' ⇒ typeset τ' ty mty``,
  rw[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
  qexists_tac`τ` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF] >>
  imp_res_tac typeset_closes_over >>
  fs[SUBSET_DEF])

val typeset_reduce = store_thm("typeset_reduce",
  ``∀τ ty mty τ'. typeset τ' ty mty ∧ set (tyvars ty) ⊆ FDOM τ ∧ τ ⊑ τ' ⇒ typeset τ ty mty``,
  rw[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
  qexists_tac`τ'` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF,SUBSET_DEF])

val type_has_meaning_def = Define`
  type_has_meaning0 ^s ty ⇔ ∀τ. type_valuation τ ∧ set (tyvars ty) ⊆ FDOM τ ⇒ ∃m. typeset τ ty m`
val _ = Parse.overload_on("type_has_meaning",``type_has_meaning0 M``)

val type_has_meaning_Bool = store_thm("type_has_meaning_Bool",
  ``type_has_meaning Bool``,
  rw[type_has_meaning_def])
val _ = export_rewrites["type_has_meaning_Bool"]

val type_has_meaning_Ind = store_thm("type_has_meaning_Ind",
  ``type_has_meaning Ind``,
  rw[type_has_meaning_def])
val _ = export_rewrites["type_has_meaning_Ind"]

val covering_type_valuation_exists = store_thm("covering_type_valuation_exists",
  ``is_set_theory ^mem ⇒
    ∀s. FINITE s ⇒ ∀τ. ∃τ'. τ ⊑ τ' ∧ s ⊆ FDOM τ' ∧ (type_valuation τ ⇒ type_valuation τ')``,
  strip_tac >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[SUBMAP_REFL] >>
  first_x_assum(qspec_then`τ`strip_assume_tac) >>
  Cases_on`e ∈ FDOM τ'` >- metis_tac[] >>
  qexists_tac`τ' |+ (e,boolset)` >>
  simp[] >>
  fs[type_valuation_def,IN_FRANGE,FAPPLY_FUPDATE_THM] >>
  metis_tac[SUBMAP_FUPDATE_EQN,SUBMAP_TRANS,boolean_in_boolset])

val type_has_meaning_Fun = store_thm("type_has_meaning_Fun",
  ``is_set_theory ^mem ⇒
    ∀dty rty. type_has_meaning (Fun dty rty) ⇔ type_has_meaning dty ∧ type_has_meaning rty``,
  strip_tac >>
  rw[type_has_meaning_def,tyvars_def] >>
  rw[Once semantics_cases] >>
  rw[EQ_IMP_THM] >>
  PROVE_TAC[covering_type_valuation_exists,typeset_reduce,SUBMAP_DEF,SUBSET_DEF,FINITE_LIST_TO_SET])
val _ = export_rewrites["type_has_meaning_Fun"]

val is_model_is_set_theory = store_thm("is_model_is_set_theory",
  ``is_model M ⇒ is_set_theory ^mem``,
  rw[is_model_def])

val typeset_has_meaning = prove(
  ``is_model M ⇒
    (∀τ ty m. typeset τ ty m ⇒ type_valuation τ ⇒ type_has_meaning ty) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ T)``,
  strip_tac >> imp_res_tac is_model_is_set_theory >>
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[type_has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  rw[type_has_meaning_def,tyvars_def] >>
  simp[Once semantics_cases] >> fs[] >>
  qmatch_assum_rename_tac`typeset X ty mp`["X"] >>
  `∀n. ∃m. n < LENGTH args ⇒ typeset τ' (EL n args) m` by (
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    rw[RIGHT_EXISTS_IMP_THM] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
    metis_tac[MEM_EL] ) >>
  fs[SKOLEM_THM] >>
  qexists_tac`GENLIST f (LENGTH args)` >>
  qmatch_assum_abbrev_tac`type_valuation tt ⇒ Z` >>
  `type_valuation tt` by (
    simp[Abbr`tt`,type_valuation_def] >>
    ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[MAP_ZIP] >>
    metis_tac[MEM_EL,typeset_inhabited] ) >>
  fs[Abbr`Z`] >>
  Q.PAT_ABBREV_TAC`t2 = A(X):string|->'U` >>
  `type_valuation t2` by (
    simp[Abbr`t2`,type_valuation_def] >>
    ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[MAP_ZIP,MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[MEM_EL,typeset_inhabited] ) >>
  last_assum(qspec_then`t2`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`t2`,MAP_ZIP,SUBSET_DEF] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[tyvars_def,SUBSET_DEF]) >>
  disch_then(qx_choosel_then[`mty2`,`m2`,`w2`]strip_assume_tac) >>
  map_every qexists_tac[`m2`,`mty2`,`ty`,`w2`] >>
  simp[] >>
  simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM])
val typeset_has_meaning = save_thm("typeset_has_meaning",MP_CANON(DISCH_ALL (CONJUNCT1 (UNDISCH typeset_has_meaning))))

val semantics_frees_exists = store_thm("semantics_frees_exists",
  ``is_model M ⇒
    (∀τ1 ty m. typeset τ1 ty m ⇒
      ∀τ2. type_valuation τ1 ∧ type_valuation τ2 ∧ (∀x. x ∈ set(tyvars ty) ⇒ x ∈ FDOM τ2) ⇒ ∃m2. typeset τ2 ty m2) ∧
    (∀σ1 τ1 tm m. semantics σ1 τ1 tm m ⇒
      ∀σ2 τ2. type_valuation τ1 ∧ type_valuation τ2 ∧
              term_valuation τ1 σ1 ∧ term_valuation τ2 σ2 ∧
              (∀x. MEM x (tvars tm) ⇒ x ∈ FDOM τ2) ∧
              (∀x ty. VFREE_IN (Var x ty) tm ⇒ ((x,ty) ∈ FDOM σ2))
              ⇒
        ∃m2. semantics σ2 τ2 tm m2)``,
  strip_tac >>
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    qmatch_assum_rename_tac`typeset X ty mrty`["X"] >>
    qmatch_assum_rename_tac`Holds mp w`[] >>
    `∀n. ∃m. n < LENGTH args ⇒ typeset τ2 (EL n args) m` by (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      rw[RIGHT_EXISTS_IMP_THM] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      rw[] >> first_x_assum match_mp_tac >>
      fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL] ) >>
    fs[SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH args)` >>
    Q.PAT_ABBREV_TAC`t2 = A(ZIP X):string|->'U` >>
    qmatch_assum_abbrev_tac`semantics FEMPTY t1 tm mp` >>
    `type_valuation t1` by (
      simp[Abbr`t1`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    `type_valuation t2` by (
      simp[Abbr`t2`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      simp[MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    last_assum(qspec_then`t2`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`t2`,MAP_ZIP] >> simp[SUBSET_DEF] ) >>
    disch_then(qx_choosel_then[`mty2`,`mp2`,`w2`]strip_assume_tac) >>
    map_every qexists_tac[`mp2`,`mty2`,`ty`,`w2`] >>
    simp[] >>
    conj_tac >- (
      simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] ) >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[tvars_def] >>
    simp[Once semantics_cases] >>
    simp[FLOOKUP_DEF]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    first_x_assum(qspecl_then[`FEMPTY`,`τ2`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[tyvars_tyinst,tvars_simple_inst] >>
      fs[SUBSET_DEF] >>
      conj_tac >- metis_tac[] >>
      fs[VFREE_IN_simple_inst,fresh_term_def]) >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    `∀n. ∃m. n < LENGTH args ⇒ typeset τ2 (EL n args) m` by (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      rw[RIGHT_EXISTS_IMP_THM] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      rw[] >> first_x_assum match_mp_tac >>
      fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL] ) >>
    fs[SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH args)` >>
    Q.PAT_ABBREV_TAC`t2 = A(ZIP (X,GENLIST Y Z)):string|->'U` >>
    `LENGTH args = LENGTH (tvars p)` by (
      qpat_assum`typeset X Y m` mp_tac >> rw[Once semantics_cases] >> rw[] ) >>
    last_x_assum(qspec_then`τ2`mp_tac) >>
    discharge_hyps >- (
      simp[GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[] ) >>
    strip_tac >>
    qexists_tac`m2` >>
    `type_valuation t2` by (
      simp[Abbr`t2`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      simp[MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    last_x_assum(qspec_then`t2`mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] >>
      simp[Abbr`t2`,MAP_ZIP] >>
      simp[type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      qpat_assum`LENGTH (X Y) = LENGTH ams`assume_tac >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    disch_then(qx_choose_then`mty2`strip_assume_tac) >>
    map_every qexists_tac[`mty2`,`ty`] >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    `∀n. ∃m. n < LENGTH args ⇒ typeset τ2 (EL n args) m` by (
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      rw[RIGHT_EXISTS_IMP_THM] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      rw[] >> first_x_assum match_mp_tac >>
      fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL] ) >>
    fs[SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH args)` >>
    Q.PAT_ABBREV_TAC`t2 = A(ZIP (X,GENLIST Y Z)):string|->'U` >>
    `LENGTH args = LENGTH (tvars tm)` by (
      qpat_assum`typeset X Y m` mp_tac >> rw[Once semantics_cases] >> rw[] ) >>
    last_x_assum(qspec_then`τ2`mp_tac) >>
    discharge_hyps >- (
      simp[GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[] ) >>
    strip_tac >>
    qexists_tac`m2` >>
    `type_valuation t2` by (
      simp[Abbr`t2`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      simp[MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    last_x_assum(qspec_then`t2`mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] >>
      simp[Abbr`t2`,MAP_ZIP] >>
      simp[type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      qpat_assum`LENGTH (X Y) = LENGTH ams`assume_tac >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    disch_then(qx_choose_then`mty2`strip_assume_tac) >>
    first_x_assum(qspecl_then[`FEMPTY`,`t2`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`t2`,MAP_ZIP] >>
      qpat_assum`typeset X Y m` mp_tac >>
      simp[Once semantics_cases] >>
      strip_tac >> simp[] >>
      simp[type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      qpat_assum`X (Y Z) = LENGTH ams`assume_tac >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    disch_then(qx_choose_then`mm2`strip_assume_tac) >>
    map_every qexists_tac[`mm2`,`mty2`,`ty`] >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM]) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  last_x_assum(qspec_then`τ2`mp_tac) >> rw[] >>
  last_x_assum(qspec_then`τ2`mp_tac) >> simp[] >>
  discharge_hyps >- (
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF] ) >>
  rw[] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`ty'`,`m2'`,`m2`] >> rw[] >>
  rw[GSYM SKOLEM_THM] >>
  rw[RIGHT_EXISTS_IMP_THM] >>
  `∃z. z <: m` by metis_tac[typeset_inhabited] >>
  first_x_assum(qspec_then`z`mp_tac) >>
  rw[] >>
  qmatch_assum_rename_tac`z2 <: m2`[] >>
  first_x_assum(qspecl_then[`σ2|+((s,ty),z2)`,`τ2`]mp_tac) >>
  simp[] >>
  `term_valuation τ2 (σ2 |+ ((s,ty),z2))` by (
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >> metis_tac[] ) >>
  discharge_hyps >- (
    simp[] >>
    conj_tac >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    metis_tac[] ) >>
  disch_then(qx_choose_then`m3`strip_assume_tac) >>
  qexists_tac`m3` >> rw[] >>
  metis_tac[semantics_typeset,WELLTYPED,WELLTYPED_LEMMA,semantics_11])

val has_meaning_def = Define`
  has_meaning0 ^s t ⇔
    (∃τ σ. type_valuation τ ∧ term_valuation τ σ ∧ closes (FDOM σ) (FDOM τ) t) ∧
    ∀τ σ. type_valuation τ ∧
          term_valuation τ σ ∧
          closes (FDOM σ) (FDOM τ) t
          ⇒ ∃m. semantics σ τ t m`
val _ = Parse.overload_on("has_meaning",``has_meaning0 M``)

val has_meaning_welltyped = store_thm("has_meaning_welltyped",
  ``∀tm. is_model M ∧ has_meaning tm ⇒ welltyped tm``,
  rw[has_meaning_def] >> metis_tac[semantics_typeset])

val covering_sigma_exists = store_thm("covering_sigma_exists",
  ``is_model M ⇒
    ∀τ σ t. type_valuation τ ∧ term_valuation τ σ ∧
            (∀x ty. VFREE_IN (Var x ty) t ⇒ ∃mty. typeset τ ty mty) ⇒
      ∃σ'. σ ⊑ σ' ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ (x,ty) ∈ FDOM σ') ∧
      term_valuation τ σ'``,
  strip_tac >>
  qsuff_tac`∀s:(string#type) set. FINITE s ⇒
    ∀τ σ. type_valuation τ ∧ term_valuation τ σ ∧ (∀x ty. (x,ty) ∈ s ⇒ ∃mty. typeset τ ty mty)⇒
      ∃σ'. σ ⊑ σ' ∧ s ⊆ FDOM σ' ∧ term_valuation τ σ'` >- (
    rw[] >>
    first_x_assum(qspec_then`{(x,ty) | VFREE_IN (Var x ty) t}`mp_tac) >>
    simp[] >> rw[SUBSET_DEF,FORALL_PROD] >> metis_tac[] ) >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[SUBMAP_REFL] >>
  first_x_assum(qspecl_then[`τ`,`σ`]strip_assume_tac) >>
  rfs[] >>
  pop_assum mp_tac >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  Cases_on`e ∈ FDOM σ'` >- metis_tac[] >>
  `∃m mty. typeset τ (SND e) mty ∧ m <: mty` by (
    metis_tac[SND,pair_CASES,typeset_inhabited] ) >>
  qexists_tac`σ' |+ (e,m)` >>
  simp[] >>
  fs[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
  conj_tac >- (rw[] >> metis_tac[]) >> rw[] >>
  match_mp_tac term_valuation_FUPDATE >> rw[] >>
  metis_tac[])

val closing_envs_exist = store_thm("closing_envs_exist",
  ``is_model M ⇒
    ∀σ τ tm. type_valuation τ ∧ term_valuation τ σ ∧
             (∀x ty. VFREE_IN (Var x ty) tm ⇒ ∃mty. typeset τ ty mty)
                 ⇒
      ∃σ' τ'.
        σ ⊑ σ' ∧ τ ⊑ τ' ∧ closes (FDOM σ') (FDOM τ') tm ∧
        type_valuation τ' ∧ term_valuation τ' σ'``,
  rw[closes_def] >> imp_res_tac is_model_is_set_theory >>
  Q.ISPEC_THEN`set (tvars tm)`mp_tac (UNDISCH covering_type_valuation_exists) >>
  simp[] >>
  disch_then(qspec_then`τ`mp_tac) >>
  disch_then(qx_choose_then`τ'`strip_assume_tac) >>
  qspecl_then[`τ'`,`σ`,`tm`]mp_tac (UNDISCH covering_sigma_exists) >>
  discharge_hyps >- (
    fs[term_valuation_def,FEVERY_DEF] >>
    metis_tac[typeset_extend] ) >>
  strip_tac >>
  qexists_tac`σ'` >>
  qexists_tac`τ'` >>
  simp[])

val has_meaning_Var = store_thm("has_meaning_Var",
  ``is_model M ⇒ ∀x ty. has_meaning (Var x ty) ⇔ type_has_meaning ty``,
  rw[has_meaning_def] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  rw[EQ_IMP_THM] >> rw[type_has_meaning_def] >- (
    fs[term_valuation_def,FEVERY_DEF] >>
    metis_tac[SND,semantics_frees_exists,SUBSET_DEF] ) >>
  imp_res_tac is_model_is_set_theory >>
  Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
  simp[] >> (disch_then(qspec_then`FEMPTY`(qx_choose_then`τ`strip_assume_tac))) >> fs[] >>
  qspecl_then[`FEMPTY`,`τ`,`Var x ty`]mp_tac (UNDISCH closing_envs_exist) >>
  simp[] >>
  discharge_hyps >-
    metis_tac[type_has_meaning_def] >>
  metis_tac[])
val _ = export_rewrites["has_meaning_Var"]

val has_meaning_Comb = store_thm("has_meaning_Comb",
  ``is_model M ⇒ ∀s t. has_meaning (Comb s t) ⇔ welltyped (Comb s t) ∧ has_meaning s ∧ has_meaning t``,
  rw[] >> imp_res_tac is_model_is_set_theory >>
  EQ_TAC >> strip_tac >- (
    imp_res_tac has_meaning_welltyped >>
    fs[] >>
    fs[has_meaning_def] >>
    fs[Q.SPECL[`X`,`Y`,`Comb A B`](CONJUNCT2 (SPEC_ALL semantics_cases))] >>
    simp[GSYM CONJ_ASSOC] >> conj_tac >- metis_tac[] >>
    simp[Once CONJ_SYM] >> simp[GSYM CONJ_ASSOC] >> conj_tac >- metis_tac[] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM AND_IMP_INTRO] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    conj_tac >>
    qmatch_abbrev_tac`closes dσ' dτ' u ⇒ X` >>
    strip_tac >> qunabbrev_tac`X` >>
    qpat_assum`welltyped u`mp_tac >>
    qmatch_assum_abbrev_tac`welltyped v` >>
    strip_tac >>
    Q.ISPEC_THEN`set(tvars v)`mp_tac (UNDISCH covering_type_valuation_exists) >>
    rw[] >> pop_assum(qspec_then`τ'`mp_tac) >> rw[] >>
    qspecl_then[`σ'`,`τ''`,`v`]mp_tac (UNDISCH closing_envs_exist) >>
    (discharge_hyps >- (
      simp[] >>
      conj_tac >- (
        fs[term_valuation_def,FEVERY_DEF] >>
        metis_tac[typeset_extend] ) >>
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      rw[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def] >>
      metis_tac[semantics_frees_exists,SUBSET_DEF,SND])) >>
    disch_then(qx_choosel_then[`σ''`,`τ'''`]strip_assume_tac) >>
    first_x_assum(qspecl_then[`τ'''`,`σ''`]mp_tac) >>
    simp[] >>
    (discharge_hyps >- metis_tac[closes_extend,SUBMAP_DEF,SUBSET_DEF]) >>
    metis_tac[semantics_reduce,SUBMAP_TRANS] ) >>
  fs[has_meaning_def] >>
  conj_tac >- (
    Q.ISPEC_THEN`set(tvars t)`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >> (disch_then(qspec_then`τ`(qx_choose_then`τt`strip_assume_tac))) >> rfs[] >>
    qspecl_then[`σ`,`τt`,`t`]mp_tac (UNDISCH closing_envs_exist) >>
    simp[] >>
    discharge_hyps >- (
      conj_tac >- (
        fs[term_valuation_def,FEVERY_DEF] >>
        metis_tac[typeset_extend] ) >>
      rw[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
      metis_tac[SND,SUBSET_DEF] ) >>
    metis_tac[closes_extend,SUBMAP_DEF,SUBSET_DEF] ) >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`τ''`,`σ''`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`m1`]strip_assume_tac) >>
  last_x_assum(qspecl_then[`τ''`,`σ''`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`m2`]strip_assume_tac) >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`m1`,`m2`] >>
  simp[])
val _ = export_rewrites["has_meaning_Comb"]

val has_meaning_Abs = store_thm("has_meaning_Abs",
  ``is_model M ⇒ ∀x ty t. has_meaning (Abs x ty t) ⇔ type_has_meaning ty ∧ has_meaning t``,
  strip_tac >> imp_res_tac is_model_is_set_theory >> rpt gen_tac >>
  EQ_TAC >- (
    simp[has_meaning_def] >>
    strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >>
    simp[] >>
    simp[Once semantics_cases] >> strip_tac >>
    `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
    first_x_assum(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    `term_valuation τ (σ|+((x,ty),m))` by (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    conj_tac >- metis_tac[semantics_typeset,typeset_has_meaning] >>
    conj_tac >- metis_tac[FDOM_FUPDATE] >>
    rw[] >>
    match_mp_tac (MP_CANON (CONJUNCT2 (UNDISCH semantics_frees_exists))) >>
    map_every qexists_tac[`σ|+((x,ty),m)`,`τ`,`mb m`] >>
    simp[] >>
    fs[closes_def,SUBSET_DEF] ) >>
  rw[has_meaning_def] >- (
    Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >> (disch_then(qspec_then`τ`mp_tac)) >>
    strip_tac >> rfs[] >>
    map_every qexists_tac[`τ'`,`σ`] >>
    simp[] >>
    conj_tac >- (
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    match_mp_tac closes_extend >>
    fs[SUBMAP_DEF,SUBSET_DEF] >>
    metis_tac[] ) >>
  simp[Once semantics_cases] >>
  `∃mty. typeset τ' ty mty` by metis_tac[type_has_meaning_def] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  `welltyped t ∧ ∃mtyb. typeset τ (typeof t) mtyb` by (
    metis_tac[semantics_typeset] ) >>
  `∃mtyb'. typeset τ' (typeof t) mtyb'` by (
    match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
    fs[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[closes_def,SUBSET_DEF] >>
    metis_tac[] ) >>
  map_every qexists_tac[`typeof t`,`mtyb'`,`mty`] >>
  simp[GSYM WELLTYPED] >>
  simp[GSYM SKOLEM_THM] >>
  qx_gen_tac`z` >>
  simp[RIGHT_EXISTS_IMP_THM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`τ'`,`σ' |+ ((x,ty),z)`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    metis_tac[term_valuation_FUPDATE,FST,SND] ) >>
  disch_then(qx_choosel_then[`y`] strip_assume_tac) >>
  qexists_tac`y` >> simp[] >>
  metis_tac[semantics_typeset,term_valuation_FUPDATE,FST,SND,WELLTYPED_LEMMA,semantics_11])
val _ = export_rewrites["has_meaning_Abs"]

val semantics_has_meaning = prove(
  ``is_model M ⇒
    (∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ term_valuation τ σ ∧ type_valuation τ ⇒ has_meaning t)``,
  strip_tac >> imp_res_tac is_model_is_set_theory >>
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[has_meaning_def,Once semantics_cases] >> rw[FLOOKUP_DEF] >>
    fs[term_valuation_def,type_has_meaning_def,FEVERY_DEF] >>
    metis_tac[semantics_frees_exists,SND,SUBSET_DEF]) >>
  conj_tac >- (
    rw[has_meaning_def,tyvars_def] >- (
      Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
      simp[] >> disch_then(qspec_then`τ`mp_tac) >>
      rw[] >>
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def,tyvars_def] >- (
      Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
      simp[] >> disch_then(qspec_then`τ`mp_tac) >>
      rw[] >>
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >- (
      fs[closes_def,tvars_simple_inst,tyvars_tyinst] >>
      fs[SUBSET_DEF] >>
      metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF,WELLTYPED] ) >>
    rw[Once semantics_cases] >>
    fs[] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`tyin` >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    imp_res_tac semantics_closes >>
    rfs[] >>
    fs[closes_def] >>
    fs[SUBSET_DEF] >>
    fs[tvars_simple_inst,tyvars_tyinst] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    `LENGTH (tvars p) = LENGTH args` by (
      qpat_assum`typeset X Y m` mp_tac >> rw[Once semantics_cases] >> rw[] )
    >- (
      imp_res_tac typeset_closes_over >>
      map_every qexists_tac[`τ`,`σ`] >> simp[] >>
      fs[tyvars_def,tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
      rw[] >> fs[] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[FLOOKUPD_def,MAP_ZIP,MEM_FOLDR_LIST_UNION] >>
      first_x_assum match_mp_tac >>
      qmatch_assum_rename_tac`MEM z (tyvars ty)`[] >>
      qmatch_assum_abbrev_tac`typeset tt ty mm` >>
      `type_valuation tt` by (
        simp[Abbr`tt`,type_valuation_def] >>
        ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        fs[EVERY_MEM,EVERY2_EVERY,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MAP_ZIP] >>
        metis_tac[typeset_inhabited,MEM_EL] ) >>
      rfs[MAP_ZIP] >> fs[] >>
      `∃n. z = EL n (STRING_SORT (tvars p)) ∧ n < LENGTH args` by
        metis_tac[MEM_EL,MEM_STRING_SORT,tvars_ALL_DISTINCT,LENGTH_STRING_SORT]>>
      Q.ISPECL_THEN[`ZIP(STRING_SORT(tvars p),args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      simp[EL_ZIP,MAP_ZIP] >> rw[] >> fs[] >>
      metis_tac[MEM_EL]) >>
    rw[Once semantics_cases] >>
    qspecl_then[`τ`,`Tyapp(Tydefined op p) args`,`m`]mp_tac(CONJUNCT1 (UNDISCH semantics_frees_exists)) >>
    simp[] >>
    disch_then(qspec_then`τ'`mp_tac) >>
    simp[] >>
    discharge_hyps >- fs[SUBSET_DEF,tyvars_def] >>
    strip_tac >>
    `∀n. n < LENGTH args ⇒ ∃m. typeset τ' (EL n args) m` by (
      rw[] >>
      match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      qexists_tac`τ` >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      imp_res_tac typeset_closes_over >>
      fs[tyvars_def,SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL] ) >>
    fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH args)` >>
    Q.PAT_ABBREV_TAC`t2 = X(Y(A,GENLIST f Z)):string|->'U` >>
    qmatch_assum_abbrev_tac`typeset t1 ty mm` >>
    `type_valuation t1` by (
      simp[Abbr`t1`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    `type_valuation t2` by (
      simp[Abbr`t2`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      simp[MAP_ZIP,MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[typeset_inhabited] ) >>
    `∃mr2. typeset t2 ty mr2` by (
      match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      qexists_tac`t1` >>
      qexists_tac`mm` >>
      simp[Abbr`t2`,MAP_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] ) >>
    map_every qexists_tac[`m2`,`mr2`,`ty`] >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM]) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    `LENGTH (tvars t) = LENGTH args` by (
      qpat_assum`typeset X Y m` mp_tac >> rw[Once semantics_cases] >> rw[] )
    >- (
      imp_res_tac typeset_closes_over >>
      map_every qexists_tac[`τ`,`σ`] >> simp[] >>
      fs[tyvars_def,tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
      rw[] >> fs[] >>
      imp_res_tac EVERY2_LENGTH >>
      fs[FLOOKUPD_def,MAP_ZIP,MEM_FOLDR_LIST_UNION] >>
      first_x_assum match_mp_tac >>
      qmatch_assum_rename_tac`MEM z (tyvars ty)`[] >>
      qmatch_assum_abbrev_tac`typeset tt ty mm` >>
      `type_valuation tt` by (
        simp[Abbr`tt`,type_valuation_def] >>
        ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        fs[EVERY_MEM,EVERY2_EVERY,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MAP_ZIP] >>
        metis_tac[typeset_inhabited,MEM_EL] ) >>
      rfs[MAP_ZIP] >> fs[] >>
      `∃n. z = EL n (STRING_SORT (tvars t)) ∧ n < LENGTH args` by
        metis_tac[MEM_EL,MEM_STRING_SORT,tvars_ALL_DISTINCT,LENGTH_STRING_SORT]>>
      Q.ISPECL_THEN[`ZIP(STRING_SORT(tvars t),args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      simp[EL_ZIP,MAP_ZIP] >> rw[] >> fs[] >>
      metis_tac[MEM_EL]) >>
    rw[Once semantics_cases] >>
    qspecl_then[`τ`,`Tyapp(Tydefined op t) args`,`m`]mp_tac(CONJUNCT1 (UNDISCH semantics_frees_exists)) >>
    simp[] >>
    disch_then(qspec_then`τ'`mp_tac) >>
    simp[] >>
    discharge_hyps >- fs[SUBSET_DEF,tyvars_def] >>
    strip_tac >>
    `∀n. n < LENGTH args ⇒ ∃m. typeset τ' (EL n args) m` by (
      rw[] >>
      match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      qexists_tac`τ` >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      imp_res_tac typeset_closes_over >>
      fs[tyvars_def,SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      metis_tac[MEM_EL] ) >>
    fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH args)` >>
    Q.PAT_ABBREV_TAC`t2 = X(A(Y,GENLIST f Z)):string|->'U` >>
    qmatch_assum_abbrev_tac`typeset t1 ty mm` >>
    `type_valuation t1` by (
      simp[Abbr`t1`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[MAP_ZIP] >>
      metis_tac[MEM_EL,typeset_inhabited] ) >>
    `type_valuation t2` by (
      simp[Abbr`t2`,type_valuation_def] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      simp[MAP_ZIP,MEM_GENLIST,GSYM LEFT_FORALL_IMP_THM] >>
      metis_tac[typeset_inhabited] ) >>
    `∃mr2. typeset t2 ty mr2` by (
      match_mp_tac (MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      qexists_tac`t1` >>
      qexists_tac`mm` >>
      simp[Abbr`t2`,MAP_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] ) >>
    `∃mp2. semantics FEMPTY t2 t mp2` by (
      match_mp_tac (MP_CANON(CONJUNCT2 (UNDISCH semantics_frees_exists))) >>
      qexists_tac`FEMPTY` >>
      qexists_tac`t1` >>
      HINT_EXISTS_TAC >>
      simp[Abbr`t2`,MAP_ZIP] >>
      qpat_assum`typeset X Y m` mp_tac >>
      rw[Once semantics_cases] ) >>
    map_every qexists_tac[`m2`,`mp2`,`mr2`,`ty`] >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM]) >>
  rw[has_meaning_def] >- (
    fs[term_valuation_def,type_has_meaning_def,FEVERY_DEF] >>
    metis_tac[semantics_frees_exists,SND,SUBSET_DEF]) >>
  `∃a. a <: m` by metis_tac[typeset_inhabited] >>
  first_x_assum(qspec_then`a`mp_tac) >> rw[] >>
  pop_assum mp_tac >>
  (discharge_hyps_keep >- (
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >> metis_tac[])) >>
  rw[])
val semantics_has_meaning = save_thm("semantics_has_meaning",MP_CANON (DISCH_ALL (CONJUNCT2 (UNDISCH semantics_has_meaning))))

val closes_aconv = store_thm("closes_aconv",
  ``∀t1 t2 s t. ACONV t1 t2 ∧ closes s t t1 ⇒ closes s t t2``,
  rw[closes_def] >>
  metis_tac[ACONV_tvars,ACONV_VFREE_IN,ACONV_SYM])

val has_meaning_aconv = store_thm("has_meaning_aconv",
  ``∀t t'. is_model M ∧ has_meaning t ∧ ACONV t t' ⇒ has_meaning t'``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  fs[has_meaning_def] >> rw[] >>
  metis_tac[semantics_aconv,ACONV_SYM,closes_aconv,ACONV_welltyped])

val tac =
  imp_res_tac is_model_is_set_theory >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    TRY (conj_tac >- metis_tac[semantics_typeset,semantics_11]) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    metis_tac[semantics_typeset,WELLTYPED,boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[semantics_typeset,semantics_11,boolean_in_boolset] ) >>
  unabbrev_all_tac >> simp[]

val semantics_equation = store_thm("semantics_equation",
  ``is_model M ⇒
    ∀env σ τ s t ty mty ms mt mst.
    type_valuation τ ∧ term_valuation τ σ ∧
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    typeof s = typeof t ∧
    Boolean (ms = mt) = mst
    ⇒ semantics σ τ (s === t) mst``,
  rw[equation_def] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  qspecl_then[`σ`,`τ`,`s`,`ms`]mp_tac(CONJUNCT2 (UNDISCH semantics_typeset)) >>
  qspecl_then[`σ`,`τ`,`t`,`mt`]mp_tac(CONJUNCT2 (UNDISCH semantics_typeset)) >>
  rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  map_every qexists_tac[`mt`,`ms`,`mty`] >> simp[] >>
  match_mp_tac EQ_SYM >> tac)

val semantics_equation_imp = store_thm("semantics_equation_imp",
  ``is_model M ⇒
    ∀σ τ s t mst.
    type_valuation τ ∧ term_valuation τ σ ∧
    semantics σ τ (s === t) mst ⇒
    ∃ms mt.
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    typeof s = typeof t ∧
    Boolean (ms = mt) = mst``,
  rw[equation_def] >>
  fs[Q.SPECL[`σ`,`τ`,`Comb X Y`](CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  fs[Q.SPECL[`σ`,`τ`,`Const X Y Z`](CONJUNCT2 (SPEC_ALL semantics_cases))] >>
  qmatch_assum_rename_tac`semantics σ τ s ms`[] >> rw[] >>
  qmatch_assum_rename_tac`semantics σ τ t mt`[] >>
  map_every qexists_tac[`ms`,`mt`] >> rw[] >>
  match_mp_tac EQ_SYM >> tac)

val type_valuation_union = store_thm("type_valuation_union",
  ``type_valuation t1 ∧ type_valuation t2 ⇒ type_valuation (t1 ⊌ t2)``,
  rw[type_valuation_def,IN_FRANGE,FUNION_DEF] >> rw[] >>
  metis_tac[])

val equation_has_meaning = store_thm("equation_has_meaning",
  ``is_model M ⇒ ∀s t ty. has_meaning s ∧ has_meaning t ∧ typeof s = typeof t ⇒ has_meaning (s === t)``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  rfs[WELLTYPED] >>
  rw[has_meaning_def] >- (
    fs[has_meaning_def] >>
    last_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`ms`]strip_assume_tac) >>
    qspecl_then[`σ`,`τ ⊌ τ'`,`t`]mp_tac (UNDISCH closing_envs_exist) >>
    discharge_hyps >- (
      simp[type_valuation_union] >>
      reverse conj_tac >- (
        fs[closes_def,term_valuation_def,FEVERY_DEF] >>
        rw[] >>
        match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
        simp[type_valuation_union] >>
        first_x_assum(qspecl_then[`x`,`ty`]mp_tac) >> simp[] >> strip_tac >>
        fs[FORALL_PROD] >>
        metis_tac[typeset_closes_over,SUBSET_DEF,SND,FUNION_DEF,IN_UNION] ) >>
      fs[term_valuation_def,FEVERY_DEF] >>
      rw[] >> res_tac >>
      qexists_tac`mty` >> rw[] >>
      match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
      qexists_tac`τ` >>
      rw[FLOOKUP_FUNION] >>
      BasicProvers.CASE_TAC >>
      fs[FLOOKUP_DEF] ) >>
    disch_then(qx_choosel_then[`σt`,`τt`]strip_assume_tac) >>
    map_every qexists_tac[`τt`,`σt`] >>
    rw[] >>
    match_mp_tac(MP_CANON(GEN_ALL(DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH_ALL closes_equation))))))>>
    qexists_tac`typeof t` >>
    rw[] >>
    match_mp_tac closes_extend >>
    map_every qexists_tac[`FDOM σ`,`FDOM τ`] >>
    fs[SUBMAP_DEF,SUBSET_DEF] ) >>
  fs[has_meaning_def] >>
  `closes (FDOM σ) (FDOM τ) s ∧
   closes (FDOM σ) (FDOM τ) t` by
    metis_tac[closes_equation] >>
  `∃ms mt. semantics σ τ s ms ∧ semantics σ τ t mt` by metis_tac[] >>
  qexists_tac`Boolean (ms = mt)` >>
  match_mp_tac (UNDISCH semantics_equation) >>
  metis_tac[])

val equation_has_meaning_iff = store_thm("equation_has_meaning_iff",
  ``is_model M ⇒ ∀s t. has_meaning (s === t) ⇔ has_meaning s ∧ has_meaning t ∧ typeof s = typeof t``,
  rw[] >> reverse EQ_TAC >- metis_tac[equation_has_meaning] >>
  simp[has_meaning_def] >> strip_tac >>
  simp[GSYM CONJ_ASSOC] >>
  `welltyped s ∧ welltyped t ∧ typeof s = typeof t` by
    metis_tac[semantics_equation_imp,semantics_typeset] >>
  simp[] >>
  conj_tac >- metis_tac[closes_equation,WELLTYPED] >>
  simp[Once CONJ_SYM] >>
  simp[GSYM CONJ_ASSOC] >>
  conj_tac >- metis_tac[closes_equation,WELLTYPED] >>
  simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM AND_IMP_INTRO] >>
  qx_genl_tac[`t0`,`s0`] >> ntac 2 strip_tac >>
  conj_tac >>
  qmatch_abbrev_tac`closes fs0 ft0 u ⇒ X` >> strip_tac >>
  qpat_assum`welltyped u`mp_tac >>
  qmatch_assum_abbrev_tac`welltyped v` >> strip_tac >>
  qspecl_then[`s0`,`t0 ⊌ τ`,`v`]mp_tac (UNDISCH closing_envs_exist) >>
  (discharge_hyps >- (
    simp[type_valuation_union] >>
    `closes (FDOM σ) (FDOM τ) v` by metis_tac[closes_equation,WELLTYPED] >>
    reverse conj_tac >- (
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      rw[] >>
      match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH semantics_frees_exists))) >>
      simp[type_valuation_union] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
      metis_tac[typeset_closes_over,SUBSET_DEF,FUNION_DEF,IN_UNION] ) >>
    fs[closes_def,term_valuation_def,FEVERY_DEF,SUBSET_DEF] >>
    rw[] >>
    qsuff_tac`t0 ⊑ t0 ⊌ τ`>-metis_tac[typeset_extend] >>
    simp[SUBMAP_DEF,FUNION_DEF] )) >>
  disch_then(qx_choosel_then[`σt`,`τt`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`τt`,`σt`]mp_tac) >>
  (discharge_hyps >- (
    simp[] >>
    qsuff_tac`closes (FDOM σt) (FDOM τt) u` >- (
      metis_tac[closes_equation,WELLTYPED] ) >>
    match_mp_tac closes_extend >>
    map_every qexists_tac[`fs0`,`ft0`] >>
    simp[Abbr`fs0`,Abbr`ft0`] >>
    fs[SUBMAP_DEF,SUBSET_DEF] )) >>
  `t0 ⊑ τt` by (
    metis_tac[SUBMAP_TRANS,SUBMAP_FUNION,SUBMAP_REFL] ) >>
  PROVE_TAC[semantics_equation_imp,semantics_reduce])

val term_valuation_extend_type = store_thm("term_valuation_extend_type",
  ``∀s t t'. term_valuation t s ∧ t ⊑ t' ⇒ term_valuation t' s``,
  rw[term_valuation_def,FEVERY_DEF] >> metis_tac[typeset_extend])

val _ = Parse.add_infix("|=",450,Parse.NONASSOC)

val sequent_def = Define`
  sequent0 ^s h c ⇔
           EVERY (λt. t has_type Bool) (c::h) ∧
           EVERY has_meaning (c::h) ∧
           ∀σ τ. type_valuation τ ∧
                 term_valuation τ σ ∧
                 EVERY (λt. semantics σ τ t True) h ∧
                 closes (FDOM σ) (FDOM τ) c
                 ⇒
                 semantics σ τ c True`
val _ = Parse.overload_on("|=",``sequent0 M``)

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀p. has_meaning p ∧ p has_type Bool ⇒ [p] |= p``,
  rw[sequent_def])

val REFL_correct = store_thm("REFL_correct",
  ``is_model M ⇒ ∀t. has_meaning t ⇒ [] |= t === t``,
  rw[sequent_def,EQUATION_HAS_TYPE_BOOL,equation_has_meaning] >>
  imp_res_tac has_meaning_welltyped >>
  match_mp_tac (MP_CANON semantics_equation) >>
  fs[has_meaning_def,WELLTYPED] >>
  imp_res_tac closes_equation >>
  simp[boolean_def] >>
  metis_tac[])

val has_meaning_VFREE_IN = store_thm("has_meaning_VFREE_IN",
  ``is_model M ⇒ ∀tm. has_meaning tm ⇒ ∀st. VFREE_IN st tm ⇒ has_meaning st``,
  strip_tac >>Induct >> rw[] >> fs[])

val binary_inference_rule = store_thm("binary_inference_rule",
  ``is_model M ⇒
    ∀h1 h2 p1 p2 q.
    (p1 has_type Bool ∧ p2 has_type Bool ⇒ q has_type Bool) ∧
    (has_meaning p1 ∧ has_meaning p2 ⇒ has_meaning q) ∧
    (∀σ τ. type_valuation τ ∧ term_valuation τ σ ∧
           semantics σ τ p1 True ∧ semantics σ τ p2 True ∧
           closes (FDOM σ) (FDOM τ) q ⇒
           semantics σ τ q True) ∧
    h1 |= p1 ∧ h2 |= p2
    ⇒ TERM_UNION h1 h2 |= q``,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[sequent_def,ALL_BOOL_TERM_UNION] >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,has_meaning_aconv] ) >>
  rw[] >>
  `∀x ty. VFREE_IN (Var x ty) p1 ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_VFREE_IN,has_meaning_Var] >>
  `∀x ty. VFREE_IN (Var x ty) p2 ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_VFREE_IN,has_meaning_Var] >>
  `∀x ty. VFREE_IN (Var x ty) q ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_VFREE_IN,has_meaning_Var] >>
  imp_res_tac is_model_is_set_theory >>
  Q.ISPEC_THEN`set(tvars p1)`mp_tac (UNDISCH covering_type_valuation_exists) >> simp[] >>
  disch_then(qspec_then`τ`(qx_choose_then`τ0`strip_assume_tac)) >>
  qspecl_then[`σ`,`τ0`,`p1`]mp_tac (UNDISCH closing_envs_exist) >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ1`,`τ1`]strip_assume_tac) >>
  `EVERY (λt. semantics σ1 τ1 t True) h1` by (
    fs[EVERY_MEM] >> rw[] >>
    `∃t'. ACONV t t' ∧ semantics σ τ t' True` by metis_tac[TERM_UNION_THM] >>
    `semantics σ τ t True` by metis_tac[semantics_aconv,has_meaning_welltyped] >>
    metis_tac[semantics_extend,SUBMAP_TRANS] ) >>
  `semantics σ1 τ1 p1 True` by (
    first_x_assum match_mp_tac >>
    simp[] ) >>
  Q.ISPEC_THEN`set(tvars p2)`mp_tac (UNDISCH covering_type_valuation_exists) >> simp[] >>
  disch_then(qspec_then`τ1`(qx_choose_then`τ00`strip_assume_tac)) >>
  qspecl_then[`σ1`,`τ00`,`p2`]mp_tac (UNDISCH closing_envs_exist) >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ2`,`τ2`]strip_assume_tac) >>
  `EVERY (λt. semantics σ2 τ2 t True) h2` by (
    fs[EVERY_MEM] >> rw[] >>
    `∃t'. ACONV t t' ∧ semantics σ τ t' True` by metis_tac[TERM_UNION_THM] >>
    `semantics σ τ t True` by metis_tac[semantics_aconv,has_meaning_welltyped] >>
    PROVE_TAC[semantics_extend,SUBMAP_TRANS] ) >>
  `semantics σ2 τ2 p2 True` by (
    first_x_assum match_mp_tac >>
    simp[] ) >>
  Q.ISPEC_THEN`set(tvars q)`mp_tac (UNDISCH covering_type_valuation_exists) >> simp[] >>
  disch_then(qspec_then`τ2`(qx_choose_then`τ000`strip_assume_tac)) >>
  qspecl_then[`σ2`,`τ000`,`q`]mp_tac (UNDISCH closing_envs_exist) >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ3`,`τ3`]strip_assume_tac) >>
  `semantics σ3 τ3 p1 True` by (
    match_mp_tac semantics_extend >>
    metis_tac[SUBMAP_TRANS] ) >>
  `semantics σ3 τ3 p2 True` by (
    match_mp_tac semantics_extend >>
    metis_tac[SUBMAP_TRANS] ) >>
  match_mp_tac semantics_reduce >>
  map_every qexists_tac[`τ3`,`σ3`] >>
  simp[] >>
  metis_tac[SUBMAP_TRANS])

val TRANS_correct = store_thm("TRANS_correct",
  ``is_model M ⇒
    ∀h1 h2 l m1 m2 r.
      h1 |= l === m1 ∧ h2 |= m2 === r ∧ ACONV m1 m2
      ⇒ TERM_UNION h1 h2 |= l === r``,
  strip_tac >>
  rw[] >> match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l === m1`,`m2 === r`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[ACONV_TYPE] >>
  conj_tac >- (
    fs[equation_has_meaning_iff] >>
    metis_tac[has_meaning_welltyped,ACONV_TYPE] ) >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  qspecl_then[`σ`,`τ`,`l`,`m1`,`True`]mp_tac (UNDISCH semantics_equation_imp) >> simp[] >>
  disch_then(qx_choosel_then[`ml`,`mm1`]strip_assume_tac) >>
  qspecl_then[`σ`,`τ`,`m2`,`r`,`True`]mp_tac (UNDISCH semantics_equation_imp) >> simp[] >>
  disch_then(qx_choosel_then[`mm2`,`mr`]strip_assume_tac) >>
  map_every qexists_tac[`ml`,`mr`] >>
  `semantics σ τ m1 mm2` by metis_tac[semantics_aconv,semantics_typeset] >>
  `mm1 = mm2` by metis_tac[semantics_11] >>
  `typeof m1 = typeof m2` by metis_tac[ACONV_TYPE,semantics_typeset] >>
  imp_res_tac is_model_is_set_theory >>
  fs[boolean_eq_true])

val MK_COMB_correct = store_thm("MK_COMB_correct",
  ``is_model M ⇒
    ∀h1 h2 l1 r1 l2 r2.
      h1 |= l1 === r1 ∧ h2 |= l2 === r2 ∧
      (∃rty. typeof l1 = Fun (typeof l2) rty)
      ⇒ TERM_UNION h1 h2 |= Comb l1 l2 === Comb r1 r2``,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l1 === r1`,`l2 === r2`] >>
  conj_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[equation_has_meaning_iff] >>
    simp[has_meaning_Comb] >>
    metis_tac[has_meaning_welltyped ] ) >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  qspecl_then[`σ`,`τ`,`l1`,`r1`,`True`]mp_tac (UNDISCH semantics_equation_imp) >> simp[] >>
  disch_then(qx_choosel_then[`ml1`,`mr1`]strip_assume_tac) >>
  qspecl_then[`σ`,`τ`,`l2`,`r2`,`True`]mp_tac (UNDISCH semantics_equation_imp) >> simp[] >>
  disch_then(qx_choosel_then[`ml2`,`mr2`]strip_assume_tac) >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Comb A Z`](CONJUNCT2 (SPEC_ALL semantics_cases)))] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qexists_tac[`ml1`,`ml2`,`rty`,`mr1`,`mr2`,`rty`] >>
  simp[] >> fs[] >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    metis_tac[semantics_typeset,codomain_rwt] ) >>
  imp_res_tac is_model_is_set_theory >>
  fs[boolean_eq_true])

val EQ_MP_correct = store_thm("EQ_MP_correct",
  ``is_model M ⇒
    ∀h1 h2 p q p'.
      h1 |= p === q ∧ h2 |= p' ∧ ACONV p p' ⇒
      TERM_UNION h1 h2 |= q``,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`p === q`,`p'`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[ACONV_welltyped,ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >>
  conj_tac >- metis_tac[equation_has_meaning_iff] >>
  rw[] >>
  qspecl_then[`σ`,`τ`,`p`,`q`,`True`]mp_tac (UNDISCH semantics_equation_imp) >>
  rw[] >>
  fs[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac is_model_is_set_theory >>
  fs[boolean_eq_true] >>
  `ms = True` by metis_tac[semantics_aconv,semantics_11] >>
  rw[])

val BETA_correct = store_thm("BETA_correct",
  ``is_model M ⇒
    ∀x ty t. type_has_meaning ty ∧ has_meaning t ⇒ [] |= Comb (Abs x ty t) (Var x ty) === t``,
  strip_tac >>
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[has_meaning_welltyped] >>
  simp[equation_has_meaning_iff,has_meaning_Comb,has_meaning_Abs,has_meaning_Var] >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  imp_res_tac is_model_is_set_theory >>
  simp[boolean_eq_true] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Var A B`](CONJUNCT2 (SPEC_ALL semantics_cases)))] >>
  srw_tac[DNF_ss][FLOOKUP_DEF] >>
  qmatch_assum_abbrev_tac`closes fs ft (l === r)` >>
  `closes fs ft l ∧ closes fs ft r` by (
    fs[WELLTYPED] >>
    `l has_type (typeof r)` by (
      simp[Abbr`l`,Once has_type_cases] >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] ) >>
    metis_tac[closes_equation] ) >>
  unabbrev_all_tac >>
  fs[type_has_meaning_def,has_meaning_def] >>
  `∃mty. typeset τ ty mty` by metis_tac[] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  `∃mtyb. typeset τ (typeof t) mtyb` by (
    metis_tac[semantics_typeset] ) >>
  map_every qexists_tac[`typeof t`,`mtyb`,`mty`] >>
  simp[GSYM WELLTYPED] >>
  qmatch_abbrev_tac`G` >>
  qpat_assum`∀x y. P ∧ Q ⇒ R`mp_tac >>
  simp[GSYM RIGHT_EXISTS_IMP_THM] >>
  simp[SKOLEM_THM] >>
  disch_then(qx_choose_then`mf`strip_assume_tac) >>
  simp[Abbr`G`] >>
  qexists_tac`λz. mf τ (σ |+ ((x,ty),z))` >>
  simp[CONJ_ASSOC,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  conj_asm1_tac >- (
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ |+ ((x,ty),z)`]mp_tac) >>
    discharge_hyps_keep >- (
      simp[] >>
      metis_tac[term_valuation_FUPDATE,FST,SND]) >>
    strip_tac >>
    reverse conj_asm2_tac >- (
      match_mp_tac semantics_reduce >>
      map_every qexists_tac[`τ`,`σ|+((x,ty),z)`] >>
      simp[] ) >>
    metis_tac[semantics_typeset,semantics_11] ) >>
  `σ ' (x,ty) <: mty` by (
    qpat_assum`term_valuation τ σ`(fn th=> ASSUME_TAC th >> mp_tac th) >>
    simp_tac std_ss [term_valuation_def,FEVERY_DEF] >>
    disch_then(qspec_then`x,ty`mp_tac) >>
    simp[] >>
    metis_tac[semantics_11] ) >>
  qmatch_abbrev_tac`semantics σ τ t (Abstract mty mtyb f ' e)` >>
  `Abstract mty mtyb f ' e = f e` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`f`,Abbr`e`] ) >>
  simp[Abbr`f`,Abbr`e`] >>
  metis_tac[FUPDATE_ELIM])

val ABS_correct = store_thm("ABS_correct",
  ``is_model M ⇒
    ∀x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ h |= l === r ∧ type_has_meaning ty ⇒
    h |= Abs x ty l === Abs x ty r``,
  rw[] >>
  rfs[sequent_def,EQUATION_HAS_TYPE_BOOL,equation_has_meaning_iff,has_meaning_Abs] >> rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >> simp[] >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Abs A B Z`](CONJUNCT2 (SPEC_ALL semantics_cases)))] >>
  imp_res_tac is_model_is_set_theory >>
  srw_tac[DNF_ss][boolean_eq_true] >>
  qmatch_assum_abbrev_tac`closes fs ft (fl === fr)` >>
  `closes fs ft fl ∧ closes fs ft fr` by (
    qsuff_tac`∃ty. fl has_type ty ∧ fr has_type ty` >- metis_tac[closes_equation] >>
    qexists_tac`Fun ty (typeof l)` >>
    simp[Abbr`fl`,Abbr`fr`,Once has_type_cases] >>
    rfs[WELLTYPED] >> simp[Once has_type_cases] ) >>
  `set (tyvars ty) ⊆ ft` by (
    fs[Abbr`fl`,closes_def] ) >>
  `∃mty. typeset τ ty mty` by metis_tac[type_has_meaning_def] >>
  qabbrev_tac`σ0 = σ \\ (x,ty)` >>
  `term_valuation τ σ0` by (
    fs[term_valuation_def,Abbr`σ0`] >>
    fs[FEVERY_DEF] >>
    simp[DOMSUB_FAPPLY_THM] ) >>
  `EVERY (λt. semantics σ0 τ t True) h` by (
    fs[EVERY_MEM] >> rw[] >>
    match_mp_tac semantics_reduce >>
    map_every qexists_tac[`τ`,`σ`] >> simp[] >>
    conj_tac >- metis_tac[SUBMAP_DOMSUB] >>
    simp[Abbr`σ0`] >>
    `closes fs ft t` by metis_tac[semantics_closes] >>
    fs[closes_def]) >>
  `∀z. z <: mty ⇒
      term_valuation τ (σ0 |+ ((x,ty),z)) ∧
      semantics (σ0 |+ ((x,ty),z)) τ (l === r) True` by (
    gen_tac >> strip_tac >>
    conj_asm1_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
    first_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      fs[EVERY_MEM] >> rw[] >>
      match_mp_tac semantics_extend >>
      map_every qexists_tac[`σ0`,`τ`] >>
      simp[] >> simp[Abbr`σ0`] ) >>
    match_mp_tac(MP_CANON(GEN_ALL(DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH closes_equation)))))) >>
    fs[WELLTYPED,Abbr`σ0`,closes_def] >>
    qexists_tac`typeof r`>>simp[]>>
    fs[Abbr`fl`,Abbr`fr`,tvars_def] >>
    metis_tac[]) >>
  `∃m. ∀z. z <: mty ⇒
    semantics (σ0 |+ ((x,ty),z)) τ l (m z) ∧
    semantics (σ0 |+ ((x,ty),z)) τ r (m z)` by (
      simp[GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >> rw[] >>
      first_x_assum(qspec_then`z`mp_tac) >> rw[] >>
      imp_res_tac semantics_equation_imp >>
      rfs[boolean_eq_true] >>
      metis_tac[] ) >>
  `∃z. z <: mty` by metis_tac[typeset_inhabited] >>
  `∃mtyb. typeset τ (typeof l) mtyb` by metis_tac[semantics_typeset] >>
  map_every qexists_tac[`m`,`mty`,`mtyb`,`typeof l`,`m`,`mty`,`mtyb`,`typeof l`] >>
  simp[] >> fs[WELLTYPED] >>
  metis_tac[semantics_typeset,semantics_11,FUPDATE_PURGE])

val DEDUCT_ANTISYM_correct = store_thm("DEDUCT_ANTISYM_correct",
  ``is_model M ⇒
    ∀h1 p1 h2 p2.
      h1 |= p1 ∧ h2 |= p2 ⇒
      TERM_UNION (FILTER ($~ o ACONV p2) h1)
                 (FILTER ($~ o ACONV p1) h2)
      |= p1 === p2``,
  rw[] >>
  fs[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac has_meaning_welltyped >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[] >>
  simp[equation_has_meaning_iff] >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_NONEW,MEM_FILTER] ) >>
  rpt gen_tac >>
  qspecl_then[`FDOM σ`,`FDOM τ`,`p1`,`p2`,`Bool`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  imp_res_tac is_model_is_set_theory >>
  simp[boolean_eq_true] >>
  fs[EVERY_MEM] >>
  rpt(first_x_assum(qspecl_then[`σ`,`τ`]mp_tac)) >> simp[] >>
  qmatch_abbrev_tac`(a ⇒ b) ⇒ (c ⇒ d) ⇒ e` >>
  `∀x y ls. MEM x (FILTER ($~ o ACONV y) ls) ⇔ ¬ACONV y x ∧ MEM x ls` by simp[MEM_FILTER] >>
  `d ⇒ a` by (
    unabbrev_all_tac >> rw[] >>
    Cases_on`ACONV p2 t`>-metis_tac[semantics_aconv] >>
    metis_tac[TERM_UNION_THM,semantics_aconv,welltyped_def] ) >>
  `b ⇒ c` by (
    unabbrev_all_tac >> rw[] >>
    Cases_on`ACONV p1 t`>-metis_tac[semantics_aconv] >>
    metis_tac[TERM_UNION_THM,semantics_aconv,welltyped_def] ) >>
  ntac 2 strip_tac >>
  `a = d ∧ b = d ∧ c = d` by metis_tac[] >> fs[] >>
  Cases_on`d` >> fs[markerTheory.Abbrev_def] >- metis_tac[] >>
  `∃m1 m2. semantics σ τ p1 m1 ∧ semantics σ τ p2 m2` by (
    metis_tac[has_meaning_def,semantics_reduce] ) >>
  metis_tac[semantics_typeset,typeset_Bool,WELLTYPED_LEMMA,mem_boolset])

val semantics_simple_subst = store_thm("semantics_simple_subst",
  ``is_model M ⇒
    ∀tm subst ss σ τ.
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ u ∈ FRANGE subst} ∧
      FEVERY (λ((x,ty),tm). tm has_type ty) subst ∧
      FDOM subst = FDOM ss ∧
      FEVERY (λ(v,m). semantics σ τ (subst ' v) m) ss ∧
      closes (FDOM (ss ⊌ σ)) (FDOM τ) tm ∧
      welltyped tm ∧
      type_valuation τ
      ⇒
      semantics σ τ (simple_subst subst tm) = semantics (ss ⊌ σ) τ tm``,
  strip_tac >>
  Induct >- (
    rpt gen_tac >> simp[] >>
    Cases_on`(s,t) ∈ FDOM ss` >- (
      rw[] >>
      simp[FLOOKUPD_def,FUN_EQ_THM] >> rw[] >>
      fs[FEVERY_DEF,FLOOKUP_DEF,SUBSET_DEF] >>
      simp[Once semantics_cases,SimpRHS] >>
      fs[FLOOKUP_DEF,FUNION_DEF] >>
      metis_tac[semantics_11] ) >>
    rw[] >>
    simp[FLOOKUPD_def,FUN_EQ_THM] >> rw[] >>
    fs[FEVERY_DEF,FLOOKUP_DEF,SUBSET_DEF] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[Once semantics_cases] >>
    fs[FLOOKUP_DEF,FUNION_DEF])
  >- (
    rw[] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] )
  >- (
    rw[] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    `simple_subst subst tm has_type (typeof tm) ∧
     simple_subst subst tm' has_type (typeof tm')` by (
       fs[WELLTYPED] >>
       metis_tac[simple_subst_has_type] ) >>
    imp_res_tac WELLTYPED_LEMMA >>
    pop_assum(assume_tac o SYM) >>
    fs[] >> simp[WELLTYPED] >>
    metis_tac[] ) >>
  rw[] >>
  simp[FUN_EQ_THM] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases,SimpRHS] >>
  rw[] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  rw[] >>
  TRY (
    qmatch_assum_abbrev_tac`simple_subst sb tm has_type tyb` >>
    qsuff_tac`tyb = typeof tm` >- metis_tac[WELLTYPED] >>
    qsuff_tac`simple_subst sb tm has_type (typeof tm)` >- metis_tac[WELLTYPED_LEMMA] >>
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    fs[WELLTYPED] >>
    fs[FEVERY_DEF,Abbr`sb`,DOMSUB_FAPPLY_THM] ) >>
  TRY (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    fs[FEVERY_DEF,DOMSUB_FAPPLY_THM] ) >>
  qmatch_abbrev_tac`semantics sx τ stm mm` >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_assum_abbrev_tac`semantics sy τ ttm mm` >>
  qsuff_tac`semantics sx τ stm = semantics sy τ ttm` >- rw[] >>
  first_x_assum(qspecl_then[`subst \\ (s,t)`,`ss \\ (s,t)`,`σ |+ ((s,t),m)`,`τ`]mp_tac) >>
  (discharge_hyps >- (
    simp[] >>
    fs[FEVERY_DEF,DOMSUB_FAPPLY_THM] >>
    conj_tac >- (
      fs[IN_DISJOINT,IN_FRANGE,DOMSUB_FAPPLY_THM] >>
      metis_tac[] ) >>
    reverse conj_tac >- (
      fs[closes_def] >>
      metis_tac[] ) >>
    rw[] >>
    ((qsuff_tac`semantics σ τ (subst ' x) = semantics sx τ (subst ' x)` >- metis_tac[])
     ORELSE
     (qsuff_tac`semantics σ τ (subst ' x) = semantics sy τ (subst ' x)` >- metis_tac[])) >>
    match_mp_tac semantics_frees >>
    simp[] >>
    fs[IN_FRANGE,FLOOKUP_DEF,Abbr`sx`,FAPPLY_FUPDATE_THM,Abbr`sy`] >>
    metis_tac[] )) >>
  rw[] >>
  rw[Abbr`sy`,GSYM FUNION_FUPDATE_1,Abbr`sx`] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[GSYM fmap_EQ_THM] >>
  simp[FUNION_DEF,FAPPLY_FUPDATE_THM] >>
  (conj_tac >- (
    simp[EXTENSION] >>
    metis_tac[] )) >>
  simp[DOMSUB_FAPPLY_THM] >>
  PROVE_TAC[])

val _ = Hol_datatype` dbterm =
    dbVar of string => type
  | dbBound of num
  | dbConst of string => type => const_tag
  | dbComb of dbterm => dbterm
  | dbAbs of type => dbterm`

val bind_def = Define`
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty g) = dbConst x ty g ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)`
val _ = export_rewrites["bind_def"]

val db_def = Define`
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty g) = dbConst x ty g ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs x ty tm) = dbAbs ty (bind (x,ty) 0 (db tm))`
val _ = export_rewrites["db_def"]

val dbVSUBST_def = Define`
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty g) = dbConst x ty g ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)`
    (*
    let ilist' = FILTER (λ(s',s). s ≠ dbVar x ty) ilist in
    let t' = dbVSUBST ilist' t in
    dbAbs ty t'
    *)
    (*
    if EXISTS (λ(s',s). dbVFREE_IN (dbVar x ty) s' ∧ dbVFREE_IN s t) ilist'
    then
      let z = VARIANT ???? in
      let ilist'' = (dbVar z ty,dbVar x ty)::ilist'
      in dbAbs ty (dbVSUBST ilist'' t)
    else dbAbs ty t'
    *)
val _ = export_rewrites["dbVSUBST_def"]

val dbVFREE_IN_def = Define`
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty g) ⇔ dbConst x ty g = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)`
val _ = export_rewrites["dbVFREE_IN_def"]

val bind_not_free = store_thm("bind_not_free",
  ``∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t``,
  Induct >> simp[] >> rw[])

val bind_dbVSUBST = store_thm("bind_dbVSUBST",
  ``∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[] >- (
    `REV_ASSOCD (dbVar s t) ls (dbVar s t) = dbVar s t` by (
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[REV_ASSOCD_MEM,MEM_MAP] ) >>
    rw[] ) >>
  Induct_on`ls` >- simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> strip_tac >>
  rw[] >> metis_tac[bind_not_free])

val bind_dbVSUBST_cons = store_thm("bind_dbVSUBST_cons",
  ``∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[REV_ASSOCD] >>fs[] >- (
    Cases_on`z`>>fs[] ) >>
  Cases_on`z`>>fs[] >- (
    Cases_on`x`>>fs[] ) >>
  match_mp_tac bind_not_free >> fs[] )

val dbVSUBST_frees = store_thm("dbVSUBST_frees",
  ``∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm``,
  Induct >> simp[])

val dbVFREE_IN_bind = store_thm("dbVFREE_IN_bind",
  ``∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm``,
  Induct >> simp[] >> rw[] >- metis_tac[]
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]>>
    metis_tac[])
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]) >>
  Cases_on`v`>>fs[]>>
  Cases_on`x=dbVar q r`>>fs[])

val dbVFREE_IN_VFREE_IN = store_thm("dbVFREE_IN_VFREE_IN",
  ``∀tm x. dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm``,
  Induct >> simp[VFREE_IN_def] >- (
    gen_tac >> Cases >> simp[VFREE_IN_def] )
  >- (
    gen_tac >> Cases >> simp[VFREE_IN_def] ) >>
  simp[dbVFREE_IN_bind] >>
  gen_tac >> Cases >> simp[] >>
  metis_tac[] )

val MAP_db_FILTER_neq = store_thm("MAP_db_FILTER_neq",
  ``∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls)``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  rw[] >-( Cases_on`r`>>fs[] ) >> fs[])

val REV_ASSOCD_MAP_db = store_thm("REV_ASSOCD_MAP_db",
  ``∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky))``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    Cases_on`r`>>fs[]>>rw[] ) >>
  `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
  metis_tac[])

val dbVFREE_IN_dbVSUBST = store_thm("dbVFREE_IN_dbVSUBST",
  ``∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))``,
  Induct >> simp[] >> rw[] >> metis_tac[])

val VSUBST_dbVSUBST = store_thm("VSUBST_dbVSUBST",
  ``∀tm ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    strip_tac >>
    qpat_assum`p ⇒ qq`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    rw[] >> fs[] >>
    Cases_on`r`>>fs[] )
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  reverse(rw[]) >- (
    first_x_assum(qspec_then`ilist'`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[Abbr`t'`] >>
    qmatch_abbrev_tac`bind v n (dbVSUBST ls tt) = X` >>
    qspecl_then[`tt`,`v`,`n`,`ls`]mp_tac bind_dbVSUBST >>
    discharge_hyps >- (
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD,FORALL_PROD,Abbr`ls`,GSYM LEFT_FORALL_IMP_THM,Abbr`ilist'`,MEM_FILTER] >>
      qunabbrev_tac`v` >>
      conj_tac >- (
        gen_tac >> Cases >> simp[] >>
        metis_tac[] ) >>
      qx_gen_tac`k` >> strip_tac >> simp[] >>
      simp[MAP_db_FILTER_neq] >>
      simp[REV_ASSOCD_FILTER] >>
      qmatch_assum_rename_tac`k = db u`[] >>
      `∃x ty. u = Var x ty` by metis_tac[] >>
      qspecl_then[`ilist`,`x`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
      discharge_hyps >- metis_tac[] >>
      simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        qmatch_abbrev_tac`¬dbVFREE_IN (dbVar s t) (db tz)` >>
        qspecl_then[`tz`,`Var s t`]mp_tac dbVFREE_IN_VFREE_IN >>
        simp[] >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC >>
        spose_not_then strip_assume_tac >>
        metis_tac[REV_ASSOCD_MEM,VFREE_IN_def,dbVFREE_IN_VFREE_IN] ) >>
      fs[] ) >>
    rw[Abbr`ls`,Abbr`ilist'`] >>
    match_mp_tac dbVSUBST_frees >>
    simp[MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
    rw[Abbr`v`] >>
    fs[dbVFREE_IN_bind]) >>
  first_x_assum(qspec_then`ilist''`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
    metis_tac[] ) >>
  qunabbrev_tac`ilist''` >> rw[] >>
  qmatch_abbrev_tac`bind v n (dbVSUBST ((zz,x)::ls) tt) = X` >>
  qspecl_then[`tt`,`(z,t)`,`(s,t)`,`n`,`ls`]mp_tac bind_dbVSUBST_cons >>
  simp[Abbr`v`] >>
  discharge_hyps >- (
    qunabbrev_tac`zz` >>
    simp[dbVFREE_IN_dbVSUBST] >>
    simp[dbVFREE_IN_bind] >>
    rpt gen_tac >>
    qspecl_then[`ilist'`,`y`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`tv = db tu` >>
    qspecl_then[`tu`,`Var z t`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`tm`,`Var y ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[Abbr`tt`] >>
    spose_not_then strip_assume_tac >>
    qsuff_tac`VFREE_IN (Var z t) t'`>-
      metis_tac[VARIANT_THM] >>
    simp[Abbr`tu`,Abbr`t'`,VFREE_IN_VSUBST] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Abbr`ls`] >>
  match_mp_tac dbVSUBST_frees >>
  simp[Abbr`ilist'`,MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
  rw[Abbr`x`] >>
  fs[dbVFREE_IN_bind])

val dbterm_def = Define`
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty g) = dbConst s ty g) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs x ty t) = dbAbs ty (dbterm ((x,ty)::env) t))`
val _ = export_rewrites["dbterm_def"]

val bind_list_aux_def = Define`
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)`
val _ = export_rewrites["bind_list_aux_def"]

val bind_list_aux_clauses = store_thm("bind_list_aux_clauses",
  ``(∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty g) = dbConst x ty g) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm))``,
  rpt conj_tac >> Induct >> simp[])

val dbterm_bind = store_thm("dbterm_bind",
  ``∀tm env. dbterm env tm = bind_list_aux 0 env (db tm)``,
  Induct >> simp[bind_list_aux_clauses] >>
  gen_tac >>
  Q.SPEC_TAC(`0`,`n`) >>
  Induct_on`env` >> simp[find_index_def] >>
  Cases >> simp[] >>
  rw[] >> rw[bind_list_aux_clauses])

val dbterm_db = store_thm("dbterm_db",
  ``∀tm. dbterm [] tm = db tm``,
  rw[dbterm_bind])

val dbterm_RACONV = store_thm("dbterm_RACONV",
  ``∀t1 env1 t2 env2. dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2)``,
  Induct >- (
    ntac 2 gen_tac >> simp[] >>
    Cases >> simp[RACONV] >>
    TRY (BasicProvers.CASE_TAC >> simp[] >> NO_TAC) >>
    Induct_on`env1` >- (
      simp[find_index_def,LENGTH_NIL_SYM,ALPHAVARS_def] ) >>
    gen_tac >> Cases >> simp[] >>
    simp[find_index_def,ALPHAVARS_def] >>
    Cases_on`h`>>Cases_on`h'`>>simp[] >>
    simp[Once find_index_shift_0] >>
    simp[Once find_index_shift_0,SimpRHS] >>
    rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] )
  >- (
    simp[] >> ntac 2 gen_tac >>
    Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] )
  >- (
    simp[] >>
    gen_tac >> Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[RACONV] >- (
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  rw[] >> res_tac >> fs[])

val RACONV_dbterm = store_thm("RACONV_dbterm",
  ``∀env tp. RACONV env tp ⇒
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)``,
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- rw[find_index_def] >> fs[] >>
  simp[find_index_def] >>
  `∃x ty. FST h = Var x ty` by metis_tac[] >>
  `∃y tz. SND h = Var y tz` by metis_tac[] >>
  simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[])

val dbterm_ACONV = store_thm("dbterm_ACONV",
  ``∀t1 t2. ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2``,
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[])

val ACONV_db = store_thm("ACONV_db",
  ``∀t1 t2. ACONV t1 t2 ⇔ db t1 = db t2``,
  metis_tac[dbterm_ACONV,dbterm_db])

val ACONV_VSUBST = store_thm("ACONV_VSUBST",
  ``∀t1 t2 ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)``,
  rw[ACONV_db] >> metis_tac[VSUBST_dbVSUBST])

val has_meaning_VSUBST = store_thm("has_meaning_VSUBST",
  ``is_model M ⇒
    ∀tm ilist.
    has_meaning tm ∧
    (∀v k. MEM (v,k) ilist ⇒ has_meaning v ∧ ∃x ty. k = Var x ty ∧ v has_type ty)
    ⇒ has_meaning (VSUBST ilist tm)``,
  strip_tac >>
  Induct >- (
    simp[VSUBST_def] >>
    gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    rw[] >> fs[] >> metis_tac[] )
  >- (
    simp[VSUBST_def] )
  >- (
    simp[VSUBST_def] >>
    rw[] >>
    TRY (
      match_mp_tac VSUBST_WELLTYPED >>
      metis_tac[] ) >>
    TRY (
      qexists_tac`rty` >>
      metis_tac[VSUBST_HAS_TYPE,type_11,WELLTYPED_LEMMA,WELLTYPED] ) >>
    first_x_assum match_mp_tac >>
    metis_tac[]) >>
  rw[] >> fs[] >>
  rw[VSUBST_def] >>
  rw[] >>
  rw[Abbr`t'`] >>
  first_x_assum match_mp_tac >>
  unabbrev_all_tac >>
  simp[MEM_FILTER] >>
  metis_tac[has_meaning_Var,has_type_cases])

val simple_subst_frees = store_thm("simple_subst_frees",
  ``∀tm s1 s2.
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP s1 (x,ty) = FLOOKUP s2 (x,ty))
    ⇒
    simple_subst s1 tm = simple_subst s2 tm``,
  Induct >> simp[FLOOKUPD_def] >> rw[] >>
  first_x_assum match_mp_tac >>
  simp[DOMSUB_FLOOKUP_THM] >>
  rw[] >> fs[])

val tvars_VSUBST_lookup = store_thm("tvars_VSUBST_lookup",
  ``∀tm ilist x ty. VFREE_IN (Var x ty) tm ⇒ set (tvars (REV_ASSOCD (Var x ty) ilist (Var x ty))) ⊆ set (tvars (VSUBST ilist tm))``,
  Induct >> simp[VSUBST_def,tvars_def] >- (
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  qmatch_abbrev_tac`X ⊆ Y ∪ set (tvars (VSUBST ls tm))` >>
  first_x_assum(qspecl_then[`ls`,`x`,`ty`]mp_tac) >>
  unabbrev_all_tac >>
  simp[SUBSET_DEF,REV_ASSOCD,REV_ASSOCD_FILTER])

val closes_VSUBST_lookup = store_thm("closes_VSUBST_lookup",
  ``closes s t (VSUBST ilist tm) ∧
    VFREE_IN (Var x ty) tm
    ⇒
    closes s t (REV_ASSOCD (Var x ty) ilist (Var x ty))``,
  rw[closes_def] >- (
    metis_tac[tvars_VSUBST_lookup,SUBSET_TRANS] ) >>
  first_x_assum match_mp_tac >>
  rw[VFREE_IN_VSUBST] >>
  metis_tac[])

val tvars_subset_VSUBST = store_thm("tvars_subset_VSUBST",
  ``∀tm ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty)
    ⇒
    set (tvars tm) ⊆ set (tvars (VSUBST ilist tm))``,
  Induct >> rw[VSUBST_def,tvars_def] >- (
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[tvars_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    res_tac >> fs[] >> rw[] >>
    metis_tac[tyvars_typeof_subset_tvars] ) >>
  TRY ( fs[SUBSET_DEF] >> NO_TAC) >>
  rw[tvars_def,Abbr`t'`] >>
  qmatch_abbrev_tac`X ⊆ Y ∪ Z` >>
  (qsuff_tac`X ⊆ Z` >- (simp[SUBSET_DEF])) >>
  unabbrev_all_tac >>
  first_x_assum match_mp_tac >>
  simp[MEM_FILTER] >>
  metis_tac[has_type_cases])

val INST_correct = store_thm("INST_correct",
  ``is_model M ⇒
    ∀ilist h c.
      (∀s s'. MEM (s',s) ilist ⇒ has_meaning s' ∧ ∃x ty. (s = Var x ty) ∧ s' has_type ty) ∧ h |= c
      ⇒
      (MAP (VSUBST ilist) h) |= VSUBST ilist c``,
  rw[] >>
  fs[sequent_def] >>
  conj_asm1_tac >- (
    conj_tac >- (
      match_mp_tac VSUBST_HAS_TYPE >>
      metis_tac[] ) >>
    fs[EVERY_MEM,MEM_MAP] >>
    metis_tac[VSUBST_HAS_TYPE] ) >>
  conj_tac >- (
    conj_tac >- (
      match_mp_tac (UNDISCH has_meaning_VSUBST) >>
      metis_tac[] ) >>
    fs[EVERY_MEM,MEM_MAP] >>
    metis_tac[has_meaning_VSUBST] ) >>
  rw[] >>
  qabbrev_tac`tm = fresh_term {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u (MAP FST ilist)} c` >>
  `ACONV c tm` by simp[fresh_term_def,Abbr`tm`] >>
  qspecl_then[`c`,`tm`,`ilist`]mp_tac ACONV_VSUBST >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  qsuff_tac`semantics σ τ (VSUBST ilist tm) True` >- (
    metis_tac[semantics_aconv,welltyped_def] ) >>
  `VSUBST ilist tm = simple_subst (ilist_to_fmap ilist) tm` by (
    match_mp_tac VSUBST_simple_subst >>
    simp[fresh_term_def,Abbr`tm`] >>
    metis_tac[] ) >>
  simp[] >>
  qabbrev_tac`subst = DRESTRICT (ilist_to_fmap ilist) {(x,ty) | VFREE_IN (Var x ty) c ∨ ∃t. MEM t h ∧ VFREE_IN (Var x ty) t}` >>
  `simple_subst (ilist_to_fmap ilist) tm = simple_subst subst tm` by (
    match_mp_tac simple_subst_frees >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `∀k v. FLOOKUP subst k = SOME v ⇒ ∃m. semantics σ τ v m` by (
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    Cases >> simp[FLOOKUP_ilist_to_fmap] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
    `has_meaning x` by (
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    pop_assum mp_tac >>
    simp[has_meaning_def] >>
    strip_tac >>
    strip_tac >>
    first_x_assum match_mp_tac >>
    simp[] >>
    `x = REV_ASSOCD (Var q r) ilist (Var q r)` by (
      simp[REV_ASSOCD_ALOOKUP] ) >>
    fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[closes_VSUBST_lookup,semantics_closes] ) >>
  pop_assum mp_tac >>
  simp[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  disch_then(qx_choose_then`ssf`strip_assume_tac) >>
  qabbrev_tac`ss = FUN_FMAP (λk. ssf k (subst ' k)) (FDOM subst)` >>
  qspecl_then[`tm`,`subst`,`ss`,`σ`,`τ`]mp_tac (UNDISCH semantics_simple_subst) >>
  `FDOM subst = FDOM ss` by (
    unabbrev_all_tac >> simp[] ) >>
  `closes (FDOM (ss ⊌ σ)) (FDOM τ) tm` by (
    fs[closes_def] >>
    conj_tac >- (
      metis_tac[tvars_subset_VSUBST,ACONV_tvars,SUBSET_DEF] ) >>
    fs[Abbr`ss`] >>
    rw[] >>
    `VFREE_IN (Var x ty) c` by metis_tac[ACONV_VFREE_IN,ACONV_SYM] >>
    fs[VFREE_IN_VSUBST,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`(x,ty) ∈ FDOM ss`>>simp[] >>
    first_x_assum match_mp_tac >>
    map_every qexists_tac[`x`,`ty`] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    qpat_assum`X = FDOM ss`(assume_tac o SYM) >>
    fs[Abbr`subst`,FDOM_DRESTRICT] >>
    `FLOOKUP (ilist_to_fmap ilist) (x,ty) = NONE` by fs[FLOOKUP_DEF] >>
    fs[FLOOKUP_ilist_to_fmap,MEM_MAP,EXISTS_PROD] ) >>
  `FEVERY (λ((x,ty),tm). tm has_type ty) subst` by (
    simp[FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
    rw[] >>
    metis_tac[REV_ASSOCD_MEM,term_11,has_type_cases] ) >>
  `FEVERY (λ(v,m). semantics σ τ (subst ' v) m) ss` by (
    simp[FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`ss`,FLOOKUP_FUN_FMAP] >>
    fs[FLOOKUP_DEF] ) >>
  discharge_hyps >- (
    conj_tac >- (
      qmatch_assum_abbrev_tac`Abbrev(tm = fresh_term s c)` >>
      `DISJOINT (set (bv_names tm)) s` by (
        simp[Abbr`tm`,Abbr`s`,fresh_term_def] ) >>
      fs[Abbr`s`,IN_DISJOINT,FRANGE_FLOOKUP] >>
      simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
      simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
      spose_not_then strip_assume_tac >>
      qsuff_tac`MEM u (MAP FST ilist)`>-metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[] >>
    metis_tac[ACONV_welltyped,welltyped_def] ) >>
  rw[] >>
  `term_valuation τ (ss ⊌ σ)` by (
    fs[term_valuation_def,FEVERY_ALL_FLOOKUP,FLOOKUP_FUNION] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> simp[] >>
    rw[] >>
    fs[Abbr`ss`,FLOOKUP_FUN_FMAP] >>
    `FLOOKUP subst k = SOME (subst ' k)` by simp[FLOOKUP_DEF] >>
    `semantics σ τ (subst ' k) v` by metis_tac[] >>
    qspecl_then[`σ`,`τ`,`subst ' k`,`v`]mp_tac(CONJUNCT2 (UNDISCH semantics_typeset)) >>
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qsuff_tac`typeof (subst ' k) = SND k` >- metis_tac[] >>
    qsuff_tac`MEM (subst ' k,UNCURRY Var k) ilist` >- (
      strip_tac >> res_tac >> Cases_on`k` >> fs[] >>
      metis_tac[has_meaning_welltyped,WELLTYPED_LEMMA] ) >>
    qabbrev_tac`w = subst ' k` >>
    Cases_on`k` >>
    fs[Abbr`subst`,FLOOKUP_DRESTRICT,FLOOKUP_ilist_to_fmap] >>
    rw[] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >>
    fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] ) >>
  qsuff_tac`semantics (ss ⊌ σ) τ c True` >- metis_tac[semantics_aconv,welltyped_def] >>
  first_x_assum match_mp_tac >>
  simp[] >> fs[] >>
  reverse conj_tac >- metis_tac[closes_aconv,ACONV_SYM] >>
  fs[EVERY_MAP] >>
  fs[EVERY_MEM] >>
  rw[] >>
  `semantics σ τ (VSUBST ilist t) True` by metis_tac[] >>
  qmatch_assum_abbrev_tac`Abbrev(tm = fresh_term s c)` >>
  qabbrev_tac`th = fresh_term s t` >>
  `ACONV t th` by simp[Abbr`th`,Abbr`s`,fresh_term_def] >>
  qsuff_tac`semantics (ss ⊌ σ) τ th True` >-  metis_tac[semantics_aconv,welltyped_def] >>
  `semantics (ss ⊌ σ) τ th = semantics σ τ (simple_subst subst th)` by (
    match_mp_tac EQ_SYM >>
    match_mp_tac (UNDISCH semantics_simple_subst) >>
    conj_tac >- (
      `DISJOINT (set (bv_names th)) s` by (
        simp[Abbr`th`,Abbr`s`,fresh_term_def] ) >>
      fs[Abbr`s`,IN_DISJOINT,FRANGE_FLOOKUP] >>
      simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
      simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
      spose_not_then strip_assume_tac >>
      qsuff_tac`MEM u (MAP FST ilist)`>-metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[] >>
    reverse conj_tac >- (
      metis_tac[ACONV_welltyped,welltyped_def] ) >>
    `closes (FDOM σ) (FDOM τ) (VSUBST ilist t)` by metis_tac[semantics_closes] >>
    fs[closes_def] >>
    conj_tac >- (
      metis_tac[tvars_subset_VSUBST,ACONV_tvars,SUBSET_DEF] ) >>
    fs[Abbr`ss`] >>
    rw[] >>
    `VFREE_IN (Var x ty) t` by metis_tac[ACONV_VFREE_IN,ACONV_SYM] >>
    fs[VFREE_IN_VSUBST,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`(x,ty) ∈ FDOM ss`>>simp[] >>
    first_x_assum match_mp_tac >>
    map_every qexists_tac[`x`,`ty`] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    qpat_assum`X = FDOM ss`(assume_tac o SYM) >>
    fs[Abbr`subst`,FDOM_DRESTRICT] >>
    `FLOOKUP (ilist_to_fmap ilist) (x,ty) = NONE` by fs[FLOOKUP_DEF] >>
    fs[FLOOKUP_ilist_to_fmap,MEM_MAP,EXISTS_PROD] >>
    metis_tac[]) >>
  simp[] >>
  `simple_subst subst th = simple_subst (ilist_to_fmap ilist) th` by (
    match_mp_tac simple_subst_frees >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    rw[] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `simple_subst (ilist_to_fmap ilist) th = VSUBST ilist th` by (
    match_mp_tac EQ_SYM >>
    match_mp_tac VSUBST_simple_subst >>
    simp[Abbr`th`,Abbr`s`,fresh_term_def] >>
    metis_tac[] ) >>
  metis_tac[semantics_aconv,ACONV_VSUBST,welltyped_def])

val tyinst_FEMPTY = store_thm("tyinst_FEMPTY",
 ``∀ty. tyinst FEMPTY ty = ty``,
 ho_match_mp_tac type_ind >> simp[EVERY_MEM,MAP_EQ_ID])
val _ = export_rewrites["tyinst_FEMPTY"]

val dbINST_def = Define`
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty g) = dbConst x (TYPE_SUBST tyin ty) g ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)`
val _ = export_rewrites["dbINST_def"]

val dbINST_bind = store_thm("dbINST_bind",
  ``∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)``,
  Induct >> simp[] >>
  Cases_on`v`>>simp[] >>
  rpt strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[])

val dbVSUBST_nil = store_thm("dbVSUBST_nil",
  ``∀tm. dbVSUBST [] tm = tm``,
  Induct >> simp[REV_ASSOCD])
val _ = export_rewrites["dbVSUBST_nil"]

val INST_CORE_dbINST = store_thm("INST_CORE_dbINST",
  ``∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm)``,
  completeInduct_on`sizeof tm` >> Cases >> simp[] >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> rw[] )
  >- (
    strip_tac >> rw[INST_CORE_def] >> rw[] )
  >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> fs[] >>
    qmatch_assum_rename_tac`typeof t1 = Fun (typeof t2) rty`[] >>
    first_assum(qspec_then`sizeof t1`mp_tac) >>
    first_x_assum(qspec_then`sizeof t2`mp_tac) >>
    simp[] >>
    disch_then(qspec_then`t2`strip_assume_tac) >>
    disch_then(qspec_then`t1`strip_assume_tac) >>
    rfs[] >>
    Cases_on`INST_CORE env tyin t1` >>fs[] >>
    Cases_on`INST_CORE env tyin t2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  qmatch_assum_rename_tac`welltyped tm`[] >>
  qmatch_assum_abbrev_tac`IS_RESULT X` >>
  Cases_on`X`>>
  pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >- (
    qmatch_abbrev_tac`bind (x,TYPE_SUBST tyin ty) 0 (db tt) = X` >>
    pop_assum mp_tac >> ntac 3 (pop_assum kall_tac) >> strip_tac >>
    qspecl_then[`db tm`,`x,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
    discharge_hyps >- (
      qx_gen_tac`ty2` >>
      qspecl_then[`tm`,`Var x ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
      rw[] >>
      qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
      qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
      discharge_hyps >- (
        simp[Abbr`env'`] >>
        metis_tac[] ) >>
      simp[Abbr`Y`] >>
      simp[Abbr`env'`,REV_ASSOCD] >>
      strip_tac >>
      last_x_assum(qspecl_then[`x`,`ty2`]mp_tac) >>
      simp[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
    simp[Abbr`env'`] >>
    discharge_hyps >- metis_tac[] >>
    rw[] ) >>
  qmatch_abbrev_tac`bind (z,TYPE_SUBST tyin ty) 0 (db tt) = dbINST tyin (bind (x,ty) 0 (db tm))` >>
  ntac 3 (pop_assum kall_tac) >>
  qspecl_then[`db tm`,`z,ty`,`x,ty`,`0`,`[]`]mp_tac bind_dbVSUBST_cons >>
  discharge_hyps >- (
    simp[] >>
    simp[dbVFREE_IN_bind] >>
    `∃tmi. INST_CORE [] tyin tm = Result tmi` by (
      Cases_on`INST_CORE [] tyin tm`>>simp[] >>
      imp_res_tac INST_CORE_NIL_IS_RESULT >>
      pop_assum(qspec_then`tyin`strip_assume_tac) >>
      rfs[] ) >> fs[] >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`[]`,`tmi`]mp_tac) >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    qspecl_then[`tm`,`Var z ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    simp[] >>
    qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[VARIANT_THM,Abbr`z`] >>
    metis_tac[] ) >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qmatch_assum_abbrev_tac`INST_CORE env' tyin tv = Result tt` >>
  `sizeof tv = sizeof tm` by (
    simp[Abbr`tv`] >>
    match_mp_tac SIZEOF_VSUBST >>
    simp[] ) >>
  first_x_assum(qspec_then`sizeof tv`mp_tac) >> simp[] >>
  disch_then(qspec_then`tv`mp_tac) >> simp[] >>
  disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
  `welltyped tv` by (
    simp[Abbr`tv`] >>
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  discharge_hyps >- (
    simp[Abbr`env'`] >>
    metis_tac[] ) >>
  rw[] >>
  qspecl_then[`tm`,`[Var z ty,Var x ty]`]mp_tac VSUBST_dbVSUBST >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qspecl_then[`db tv`,`z,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
  discharge_hyps >- (
    simp[] >>
    qx_gen_tac`ty2` >>
    qspecl_then[`tv`,`Var z ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`sizeof tv`,`tv`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    discharge_hyps >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    simp[] >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    strip_tac >>
    last_x_assum(qspecl_then[`z`,`ty2`]mp_tac) >>
    simp[] ) >>
  simp[])

val INST_dbINST = store_thm("INST_dbINST",
  ``∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm)``,
  rw[INST_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`tm`,`tyin`,`[]`,`a`]mp_tac INST_CORE_dbINST >>
  simp[])

val ACONV_INST = store_thm("ACONV_INST",
  ``∀t1 t2 tyin. welltyped t1 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2)``,
  rw[] >> imp_res_tac ACONV_welltyped >>
  fs[ACONV_db] >> imp_res_tac INST_dbINST >> rw[] )

val INST_HAS_TYPE = store_thm("INST_HAS_TYPE",
  ``∀tm tyin ty. tm has_type ty ⇒ INST tyin tm has_type (TYPE_SUBST tyin ty)``,
  rw[INST_def] >>
  `welltyped tm` by metis_tac[welltyped_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  rw[] >>
  metis_tac[WELLTYPED_LEMMA])

val type_has_meaning_TYPE_SUBST = store_thm("type_has_meaning_TYPE_SUBST",
  ``is_model M ⇒
    ∀ty tyin.
    type_has_meaning ty ∧
    EVERY type_has_meaning (MAP FST tyin)
    ⇒
    type_has_meaning (TYPE_SUBST tyin ty)``,
  rw[type_has_meaning_def] >>
  fs[tyinst_TYPE_SUBST] >>
  fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM,type_has_meaning_def] >>
  qabbrev_tac`ti = FUN_FMAP (λa. @m. typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) m) (set (tyvars ty))` >>
  `∀a. MEM a (tyvars ty) ⇒ ∃x. typeset τ (FLOOKUPD (tyin_to_fmap tyin) a (Tyvar a)) x` by (
    rw[] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    fs[FLOOKUPD_def,tyin_to_fmap_def] >>
    BasicProvers.CASE_TAC >- (
      simp[Once semantics_cases,FLOOKUP_DEF] >>
      first_x_assum match_mp_tac >>
      qexists_tac`a` >> simp[tyvars_def] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,MEM_FILTER] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    last_x_assum(qspecl_then[`x`,`Tyvar a`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`τ`mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      qexists_tac`a` >>
      simp[] ) >>
    simp[] ) >>
  `type_valuation ti` by (
    simp[type_valuation_def,Abbr`ti`] >>
    rw[] >>
    SELECT_ELIM_TAC >>
    simp[] >>
    metis_tac[typeset_inhabited] ) >>
  first_x_assum(qspec_then`ti`mp_tac) >>
  simp[] >>
  discharge_hyps >- simp[Abbr`ti`] >>
  strip_tac >> qexists_tac`m` >>
  match_mp_tac (MP_CANON (CONJUNCT1 (UNDISCH semantics_simple_inst))) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  rw[] >>
  simp[Abbr`ti`,FUN_FMAP_DEF] >>
  SELECT_ELIM_TAC >> simp[] )

val has_meaning_simple_inst = store_thm("has_meaning_simple_inst",
  ``is_model M ⇒
    ∀tm tyin.
      has_meaning tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
     (∀ty. ty ∈ FRANGE tyin ⇒ type_has_meaning ty)
     ⇒ has_meaning (simple_inst tyin tm)``,
  rw[] >>
  match_mp_tac semantics_has_meaning >>
  qabbrev_tac`τ = FUN_FMAP (K boolset) (set (tvars (simple_inst tyin tm)))` >>
  `type_valuation τ` by (
    simp[type_valuation_def] >>
    simp[Abbr`τ`] >>
    metis_tac[boolean_in_boolset,is_model_is_set_theory] ) >>
  `∃τi. (FDOM τi = set (tvars tm)) ∧ (∀a. MEM a (tvars tm) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a))` by (
    qexists_tac`FUN_FMAP (λa. @m. typeset τ (tyinst tyin (Tyvar a)) m) (set (tvars tm))` >>
    simp[] >> rw[] >>
    simp[FUN_FMAP_DEF] >>
    SELECT_ELIM_TAC >> simp[] >>
    simp[FLOOKUPD_def] >>
    BasicProvers.CASE_TAC >- (
      simp[Once semantics_cases] >>
      simp[Abbr`τ`,FLOOKUP_FUN_FMAP] >>
      simp[tvars_simple_inst,FLOOKUPD_def] >>
      qexists_tac`a`>>simp[tyvars_def] ) >>
    `x ∈ FRANGE tyin` by metis_tac[FRANGE_FLOOKUP] >>
    res_tac >> pop_assum mp_tac >>
    simp_tac std_ss [type_has_meaning_def] >>
    disch_then match_mp_tac >>
    simp[] >>
    simp[Abbr`τ`,tvars_simple_inst] >>
    simp[SUBSET_DEF,FLOOKUPD_def] >> rw[] >>
    qexists_tac`a`>>simp[] ) >>
  `type_valuation τi` by (
    simp[type_valuation_def,IN_FRANGE] >>
    metis_tac[typeset_inhabited] ) >>
  qabbrev_tac`σ = FUN_FMAP (λ(x,ty). @x. ∃m. typeset τ ty m ∧ x <: m) {(x,ty) | VFREE_IN (Var x ty) (simple_inst tyin tm)}` >>
  `term_valuation τ σ` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`σ`,FLOOKUP_FUN_FMAP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[VFREE_IN_simple_inst,GSYM LEFT_FORALL_IMP_THM] >>
    qx_genl_tac[`x`,`ty`] >> rw[] >>
    `∃m. typeset τi ty m` by (
      imp_res_tac has_meaning_VFREE_IN >> rfs[] >>
      fs[type_has_meaning_def] >> rw[] >>
      pop_assum match_mp_tac >>
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] ) >>
    `typeset τ (tyinst tyin ty) m` by (
      match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH semantics_simple_inst))) >>
      qexists_tac`τi` >>
      simp[] >> rw[] >> fs[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] ) >>
    qexists_tac`m` >>
    simp[] >>
    SELECT_ELIM_TAC >>
    metis_tac[typeset_inhabited,semantics_11] ) >>
  `∃σi. FDOM σi = { (x,ty) | VFREE_IN (Var x ty) tm } ∧
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst tyin ty))` by (
    qexists_tac`FUN_FMAP (λ(x,ty). σ ' (x,tyinst tyin ty)) { (x,ty) | VFREE_IN (Var x ty) tm }` >>
    simp[FLOOKUP_FUN_FMAP] >>
    simp[FLOOKUP_DEF] >>
    simp[Abbr`σ`,VFREE_IN_simple_inst] >>
    metis_tac[] ) >>
  `term_valuation τi σi` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qx_gen_tac`k` >>
    PairCases_on`k` >>
    reverse(Cases_on`VFREE_IN (Var k0 k1) tm`) >- (
      simp[FLOOKUP_DEF] ) >>
    simp[] >>
    simp[Abbr`σ`,FLOOKUP_FUN_FMAP] >>
    strip_tac >>
    `type_has_meaning k1` by (
      imp_res_tac has_meaning_VFREE_IN >> rfs[] ) >>
    fs[type_has_meaning_def] >>
    pop_assum(qspec_then`τi`mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def] ) >>
    strip_tac >>
    qexists_tac`m` >> simp[] >>
    SELECT_ELIM_TAC >>
    `typeset τ (tyinst tyin k1) m` by (
      match_mp_tac(MP_CANON(CONJUNCT1 (UNDISCH semantics_simple_inst))) >>
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def,SUBSET_DEF] >>
      metis_tac[] ) >>
    metis_tac[typeset_inhabited,semantics_11] ) >>
  `∃m. semantics σi τi tm m` by (
    fs[has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    simp[closes_def] ) >>
  map_every qexists_tac[`σ`,`τ`,`m`] >>
  simp[] >>
  match_mp_tac(MP_CANON(CONJUNCT2 (UNDISCH semantics_simple_inst))) >>
  map_every qexists_tac[`σi`,`τi`] >>
  simp[])

val IN_FRANGE_tyin_to_fmap_suff = store_thm("IN_FRANGE_tyin_to_fmap_suff",
  ``∀P tyin. (∀x. MEM x (MAP FST tyin) ⇒ P x) ⇒ (∀x. x ∈ FRANGE (tyin_to_fmap tyin) ⇒ P x)``,
  rw[FRANGE_FLOOKUP,tyin_to_fmap_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
  rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
  metis_tac[])

val INST_TYPE_correct = store_thm("INST_TYPE_correct",
  ``is_model M ⇒
    ∀h c tyin.
      h |= c ∧ EVERY type_has_meaning (MAP FST tyin)
      ⇒
      (MAP (INST tyin) h) |= INST tyin c``,
  strip_tac >>
  simp[sequent_def] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    `TYPE_SUBST tyin Bool = Bool` by simp[] >>
    metis_tac[INST_HAS_TYPE] ) >>
  `welltyped c ∧ EVERY welltyped h` by (
    fs[EVERY_MEM] >> metis_tac[welltyped_def] ) >>
  qabbrev_tac`tm = fresh_term {x | ∃ty. VFREE_IN (Var x ty) c} c` >>
  qabbrev_tac`tms = MAP (λt. fresh_term {x | ∃ty. VFREE_IN (Var x ty) t} t) h` >>
  `ACONV c tm` by simp[Abbr`tm`,fresh_term_def] >>
  `EVERY (UNCURRY ACONV) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    simp[fresh_term_def] ) >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm } = {x | ∃ty. VFREE_IN (Var x ty) c}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `EVERY (λ(c,tm). {x | ∃ty. VFREE_IN (Var x ty) tm } = {x | ∃ty. VFREE_IN (Var x ty) c}) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `has_meaning tm` by metis_tac[has_meaning_aconv] >>
  `EVERY has_meaning tms` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[has_meaning_aconv] ) >>
  `ACONV (INST tyin tm) (INST tyin c)` by metis_tac[ACONV_INST,ACONV_SYM] >>
  `EVERY (λ(c,tm). ACONV (INST tyin tm) (INST tyin c)) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[ACONV_INST,ACONV_SYM] ) >>
  `INST tyin tm = simple_inst (tyin_to_fmap tyin) tm` by (
    match_mp_tac INST_simple_inst >>
    simp[Abbr`tm`,fresh_term_def] ) >>
  `EVERY (λtm. INST tyin tm = simple_inst (tyin_to_fmap tyin) tm) tms` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac INST_simple_inst >>
    simp[fresh_term_def] ) >>
  conj_asm1_tac >- (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_ZIP,EXISTS_PROD,Abbr`tms`,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac has_meaning_aconv >|[
      qexists_tac`INST tyin tm`,
      res_tac >>
      qmatch_assum_abbrev_tac`INST tyin tmh = X` >>
      qunabbrev_tac`X` >>
      qexists_tac`INST tyin tmh` >>
      qunabbrev_tac`tmh`] >> simp[] >>
    match_mp_tac (UNDISCH has_meaning_simple_inst) >>
    simp[Abbr`tm`,fresh_term_def] >>
    ho_match_mp_tac IN_FRANGE_tyin_to_fmap_suff >>
    simp[MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP]) >>
  rw[] >>
  `semantics σ τ (INST tyin c) = semantics σ τ (INST tyin tm)` by (
    metis_tac[semantics_aconv,ACONV_welltyped,simple_inst_has_type,welltyped_def] ) >>
  `EVERY (λ(c,tm). semantics σ τ (INST tyin c) = semantics σ τ (INST tyin tm)) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[semantics_aconv,ACONV_welltyped,simple_inst_has_type,welltyped_def] ) >>
  simp[] >>
  match_mp_tac(MP_CANON (CONJUNCT2 (UNDISCH semantics_simple_inst))) >>
  qabbrev_tac`τi = FUN_FMAP (λa. @m. typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) m) (BIGUNION (set (MAP (set o tvars) (c::h))))` >>
  qmatch_assum_abbrev_tac`Abbrev(τi = FUN_FMAP ff ss)` >>
  `FINITE ss` by (
    simp[Abbr`ss`,MEM_MAP] >>
    rw[] >> rw[] ) >>
  `type_valuation τi ∧ (∀a. MEM a (tvars c) ∨ (∃t. MEM t h ∧ MEM a (tvars t)) ⇒ ∃x. typeset τ (FLOOKUPD (tyin_to_fmap tyin) a (Tyvar a)) x)` by (
    simp[type_valuation_def] >>
    simp[FRANGE_FLOOKUP] >>
    simp[Abbr`τi`,FLOOKUP_FUN_FMAP] >>
    simp[Abbr`ff`,Abbr`ss`,MEM_MAP] >>
    simp[GSYM LEFT_FORALL_IMP_THM] >>
    simp[CONJ_COMM] >>
    simp[GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    simp[AND_IMP_INTRO] >>
    conj_asm1_tac >- (
      gen_tac >>
      simp[FLOOKUPD_def] >>
      strip_tac >>
      BasicProvers.CASE_TAC >- (
        simp[Once semantics_cases] >>
        fs[closes_def] >>
        `tvars (INST tyin c) = tvars (INST tyin tm)` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        simp[FLOOKUP_DEF] >>
        first_x_assum match_mp_tac >>
        qexists_tac`a` >>
        simp[tyvars_def] >>
        metis_tac[ACONV_tvars] )
      >- (
        fs[tyin_to_fmap_def] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[EVERY_MEM,MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
        rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
        res_tac >> fs[type_has_meaning_def] >>
        first_x_assum match_mp_tac >>
        fs[closes_def] >>
        `tvars (INST tyin c) = tvars (INST tyin tm)` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        rw[] >>
        first_x_assum match_mp_tac >>
        qmatch_assum_rename_tac`MEM v (tvars c)`[] >>
        qexists_tac`v` >>
        simp[] >>
        metis_tac[ACONV_tvars] )
      >- (
        simp[Once semantics_cases] >>
        `semantics σ τ (INST tyin t) True` by (
          fs[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
        `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
        `semantics σ τ (INST tyin (EL n tms)) True` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`,EL_MAP] >>
          metis_tac[] ) >>
        `ACONV t (EL n tms)` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
        `ACONV (INST tyin (EL n tms)) (INST tyin t) ∧ (INST tyin (EL n tms) = simple_inst (tyin_to_fmap tyin) (EL n tms))` by (
          fs[EVERY_MEM,FORALL_PROD,MEM_ZIP,Abbr`tms`,EL_MAP,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          fs[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          metis_tac[] ) >>
        `closes (FDOM σ) (FDOM τ) (INST tyin (EL n tms))`
            by metis_tac[semantics_closes] >>
        fs[closes_def] >>
        `tvars (INST tyin t) = tvars (INST tyin (EL n tms))` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        simp[FLOOKUP_DEF] >>
        first_x_assum match_mp_tac >>
        qexists_tac`a` >>
        simp[tyvars_def] >>
        metis_tac[ACONV_tvars] )
      >- (
        `semantics σ τ (INST tyin t) True` by (
          fs[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
        `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
        `semantics σ τ (INST tyin (EL n tms)) True` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`,EL_MAP] >>
          metis_tac[] ) >>
        `ACONV t (EL n tms)` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
        `ACONV (INST tyin (EL n tms)) (INST tyin t) ∧ (INST tyin (EL n tms) = simple_inst (tyin_to_fmap tyin) (EL n tms))` by (
          fs[EVERY_MEM,FORALL_PROD,MEM_ZIP,Abbr`tms`,EL_MAP,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          fs[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          metis_tac[] ) >>
        `closes (FDOM σ) (FDOM τ) (INST tyin (EL n tms))`
            by metis_tac[semantics_closes] >>
        fs[tyin_to_fmap_def] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[EVERY_MEM,MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
        rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
        res_tac >> fs[type_has_meaning_def] >>
        first_x_assum match_mp_tac >>
        fs[closes_def] >>
        `tvars (INST tyin (EL n h)) = tvars (INST tyin (EL n tms))` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        rw[] >>
        first_x_assum match_mp_tac >>
        qmatch_assum_rename_tac`MEM v (tvars (EL n h))`[] >>
        qexists_tac`v` >>
        simp[] >>
        metis_tac[ACONV_tvars] ))>>
    qx_genl_tac[`v`,`t`] >> rw[] >>
    SELECT_ELIM_TAC >>
    metis_tac[typeset_inhabited]) >>
  `∀a. MEM a (tvars tm) ∨ (∃t. MEM t h ∧ MEM a (tvars t)) ⇒
       typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) (τi ' a)` by (
    `tvars tm = tvars c` by metis_tac[ACONV_tvars] >>
    rw[] >- (
      `a ∈ ss` by (rw[Abbr`ss`] >> metis_tac[]) >>
      rw[Abbr`τi`,FUN_FMAP_DEF,Abbr`ff`] >>
      SELECT_ELIM_TAC >> simp[] ) >>
    `a ∈ ss` by (rw[Abbr`ss`,MEM_MAP] >> metis_tac[]) >>
    rw[Abbr`τi`,FUN_FMAP_DEF,Abbr`ff`] >>
    SELECT_ELIM_TAC >> simp[] >>
    metis_tac[]) >>
  qabbrev_tac`σi = FUN_FMAP (λ(x,ty). @m. FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty) = SOME m) {(x,ty) | ∃t. VFREE_IN (Var x ty) t ∧ MEM t (c::h)}` >>
  qmatch_assum_abbrev_tac`Abbrev(σi = FUN_FMAP ft st)` >>
  `FINITE st` by (
    `st = BIGUNION (IMAGE (λt. {(x,ty) | VFREE_IN (Var x ty) t}) (set(c::h)))` by (
      simp[Abbr`st`,Once EXTENSION,EXISTS_PROD,FORALL_PROD] >> srw_tac[DNF_ss][] ) >>
    rw[] >> rw[] ) >>
  `∀x ty. (x,ty) ∈ st ⇒ ∃m. FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty) = SOME m` by (
    simp[Abbr`st`,GSYM LEFT_FORALL_IMP_THM] >>
    rw[] >- (
      fs[closes_def,FLOOKUP_DEF] >>
      first_x_assum match_mp_tac >>
      qmatch_abbrev_tac`VFREE_IN v ti` >>
      qmatch_assum_abbrev_tac`ACONV tj ti` >>
      qsuff_tac`VFREE_IN v tj` >- metis_tac[VFREE_IN_ACONV] >>
      simp[Abbr`tj`] >>
      qmatch_abbrev_tac`VFREE_IN v (simple_inst tyi tm)` >>
      qspecl_then[`tm`,`tyi`]mp_tac VFREE_IN_simple_inst >>
      discharge_hyps >- (
        simp[Abbr`tm`,fresh_term_def] ) >>
      rw[Abbr`v`] >>
      metis_tac[VFREE_IN_ACONV] ) >>
    `semantics σ τ (INST tyin t) True` by fs[EVERY_MAP,EVERY_MEM] >>
    `closes (FDOM σ) (FDOM τ) (INST tyin t)` by metis_tac[semantics_closes] >>
    fs[closes_def,FLOOKUP_DEF] >>
    first_x_assum match_mp_tac >>
    `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
    `ACONV (INST tyin (EL n h)) (INST tyin (EL n tms))` by (
      fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_ZIP,Abbr`tms`] >>
      metis_tac[ACONV_SYM] ) >>
    BasicProvers.VAR_EQ_TAC >>
    qmatch_abbrev_tac`VFREE_IN v ti` >>
    qmatch_assum_abbrev_tac`ACONV ti tj` >>
    qsuff_tac`VFREE_IN v tj` >- metis_tac[VFREE_IN_ACONV] >>
    simp[Abbr`tj`,Abbr`tms`,EL_MAP] >>
    fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    qmatch_abbrev_tac`VFREE_IN v (simple_inst tyi th)` >>
    qspecl_then[`th`,`tyi`]mp_tac VFREE_IN_simple_inst >>
    discharge_hyps >- (
      fs[MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      simp[Abbr`th`,fresh_term_def] ) >>
    rw[Abbr`v`] >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EL_MAP] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `∀x ty. VFREE_IN (Var x ty) tm ∨ (∃t. VFREE_IN (Var x ty) t ∧ MEM t h) ⇒
      FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty)` by (
    rw[] >- (
      `VFREE_IN (Var x ty) c` by metis_tac[VFREE_IN_ACONV] >>
      simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >> simp[Abbr`st`] >>
      reverse BasicProvers.CASE_TAC >- metis_tac[] >>
      simp[Abbr`ft`] >>
      SELECT_ELIM_TAC >>
      simp[] ) >>
    simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >> simp[Abbr`st`] >>
    reverse BasicProvers.CASE_TAC >- metis_tac[] >>
    simp[Abbr`ft`] >>
    SELECT_ELIM_TAC >>
    simp[] ) >>
  `term_valuation τi σi` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >>
    simp[Abbr`st`,Abbr`ft`,GSYM LEFT_FORALL_IMP_THM] >>
    rpt gen_tac >>
    reverse(Cases_on`type_has_meaning ty`) >- (
      rw[] >>
      `has_meaning (Var x ty)` by (
        imp_res_tac has_meaning_VFREE_IN >>
        fs[EVERY_MEM] >> res_tac >>
        imp_res_tac has_meaning_VFREE_IN >>
        rfs[]>>NO_TAC) >>
      rfs[] ) >>
    reverse(Cases_on`set (tyvars ty) ⊆ FDOM τi`) >- (
      rfs[Abbr`τi`,FUN_FMAP_DEF,Abbr`ss`] >>
      fs[SUBSET_DEF,MEM_MAP] >>
      rw[] >> imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] >>
      metis_tac[] ) >>
    `∃mty. typeset τi ty mty` by (
      fs[type_has_meaning_def] ) >>
    fs[FLOOKUPD_def] >>
    fs[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qmatch_abbrev_tac`P ⇒ Q` >>
    strip_tac >>
    qunabbrev_tac`Q` >>
    qexists_tac`mty` >>
    simp[] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[] >>
    qx_gen_tac`z` >> strip_tac >>
    qmatch_assum_abbrev_tac`FLOOKUP σ k = SOME z` >>
    first_x_assum(qspecl_then[`k`,`z`]mp_tac) >>
    rw[Abbr`k`] >>
    qspecl_then[`τi`,`ty`,`mty`]mp_tac(CONJUNCT1 (UNDISCH semantics_simple_inst)) >>
    simp[] >>
    disch_then(qspecl_then[`τ`,`tyin_to_fmap tyin`]mp_tac) >>
    discharge_hyps >- (
      rw[] >>
      last_x_assum(qspec_then`a`kall_tac) >>
      last_x_assum(qspec_then`a`mp_tac) >>
      simp[FLOOKUPD_def] >>
      disch_then match_mp_tac >>
      qpat_assum`Abbrev(T = X)`mp_tac >>
      simp[markerTheory.Abbrev_def] >>
      rw[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def,SUBSET_DEF] >>
      metis_tac[ACONV_tvars] ) >>
    metis_tac[semantics_11] ) >>
  map_every qexists_tac[`σi`,`τi`] >>
  simp[] >>
  reverse conj_tac >- (
    simp[Abbr`tm`,fresh_term_def] ) >>
  qsuff_tac`semantics σi τi c True` >- metis_tac[semantics_aconv] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  reverse conj_tac >- (
    simp[closes_def] >>
    simp[Abbr`τi`,Abbr`σi`] >>
    simp[Abbr`ss`,Abbr`st`] >>
    metis_tac[] ) >>
  simp[EVERY_MEM] >>
  rw[] >>
  `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
  `ACONV (EL n h) (EL n tms)` by (
    fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
  `welltyped t` by fs[EVERY_MEM] >>
  qsuff_tac`semantics σi τi (EL n tms) True` >- metis_tac[semantics_aconv] >>
  `semantics σ τ (INST tyin t) True` by (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] ) >>
  `semantics σ τ (simple_inst (tyin_to_fmap tyin) (EL n tms)) True` by (
    rfs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_ZIP,FORALL_PROD,Abbr`tms`,EL_MAP,GSYM LEFT_FORALL_IMP_THM,MEM_MAP] >>
    metis_tac[] ) >>
  `has_meaning (EL n tms)` by (
    match_mp_tac has_meaning_aconv >>
    qexists_tac`EL n h` >>
    fs[EVERY_MEM] ) >>
  `∃m. semantics σi τi (EL n tms) m` by (
    fs[has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fs[closes_def] >>
    simp[Abbr`τi`,Abbr`σi`] >>
    simp[Abbr`ss`,Abbr`st`,SUBSET_DEF,MEM_MAP] >>
    metis_tac[VFREE_IN_ACONV,ACONV_tvars] ) >>
  qspecl_then[`σi`,`τi`,`EL n tms`,`m`]mp_tac(CONJUNCT2 (UNDISCH semantics_simple_inst)) >>
  simp[] >>
  disch_then(qspecl_then[`σ`,`τ`,`tyin_to_fmap tyin`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    conj_tac >- (
      rw[] >> fs[] >>
      metis_tac[ACONV_tvars] ) >>
    conj_tac >- metis_tac[VFREE_IN_ACONV] >>
    fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EXISTS_PROD,Abbr`tms`,EL_MAP,fresh_term_def] ) >>
  metis_tac[semantics_11])

val simple_inst_FEMPTY = store_thm("simple_inst_FEMPTY",
  ``∀tm. simple_inst FEMPTY tm = tm``,
  Induct >> simp[])
val _ = export_rewrites["simple_inst_FEMPTY"]

val new_basic_definition_correct = store_thm("new_basic_definition_correct",
  ``is_model M ⇒
    ∀r ty n. has_meaning r ∧ closed r ∧ set(tvars r) ⊆ set(tyvars ty) ∧ r has_type ty
    ⇒ [] |= (Const n ty (Defined r) === r)``,
  strip_tac >>
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL,welltyped_def,equation_has_meaning_iff] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[WELLTYPED_LEMMA] >> simp[] >> pop_assum kall_tac >>
  conj_tac >- (
    match_mp_tac semantics_has_meaning >>
    fs[has_meaning_def] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`σ`,`τ`] >> simp[] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`FEMPTY` >>
    simp[] >>
    `ACONV r (fresh_term {} r)` by metis_tac[fresh_term_def,FINITE_EMPTY] >>
    first_x_assum(qspecl_then[`τ`,`FEMPTY`]mp_tac) >>
    fs[closes_def] >> rw[] >>
    qexists_tac`m` >>
    conj_asm1_tac >- metis_tac[welltyped_def,ACONV_welltyped,ACONV_TYPE] >>
    conj_asm1_tac >- metis_tac[welltyped_def,ACONV_welltyped,ACONV_TYPE] >>
    conj_asm1_tac >- metis_tac[VFREE_IN_ACONV] >>
    conj_tac >- metis_tac[ACONV_tvars,WELLTYPED_LEMMA,ACONV_TYPE,ACONV_welltyped,WELLTYPED] >>
    metis_tac[semantics_aconv,term_valuation_FEMPTY,welltyped_def] ) >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  `Const n (typeof r) (Defined r) has_type (typeof r)` by (
    simp[Once has_type_cases] ) >>
  `r has_type typeof r` by metis_tac[WELLTYPED_LEMMA] >>
  `typeof r = ty` by metis_tac[WELLTYPED_LEMMA] >>
  qspecl_then[`FDOM σ`,`FDOM τ`,`Const n (typeof r) (Defined r)`,`r`,`ty`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
  rw[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`FEMPTY` >>
  simp[] >>
  `∃m. semantics σ τ r m` by (
    fs[has_meaning_def] ) >>
  `semantics FEMPTY τ r = semantics σ τ r` by (
    match_mp_tac semantics_frees >>
    simp[] ) >>
  `ACONV r (fresh_term {} r)` by metis_tac[fresh_term_def,FINITE_EMPTY] >>
  map_every qexists_tac[`m`,`m`] >>
  simp[boolean_def] >>
  conj_asm1_tac >- metis_tac[welltyped_def,ACONV_welltyped,ACONV_TYPE] >>
  conj_asm1_tac >- metis_tac[welltyped_def,ACONV_welltyped,ACONV_TYPE] >>
  conj_asm1_tac >- metis_tac[VFREE_IN_ACONV] >>
  conj_tac >- metis_tac[ACONV_tvars,WELLTYPED_LEMMA,ACONV_TYPE,ACONV_welltyped,WELLTYPED] >>
  metis_tac[semantics_aconv,term_valuation_FEMPTY,welltyped_def] )

val has_meaning_type_has_meaning = store_thm("has_meaning_type_has_meaning",
  ``is_model M ⇒ ∀tm. has_meaning tm ⇒ type_has_meaning (typeof tm)``,
  rw[] >>
  fs[has_meaning_def] >>
  res_tac >>
  imp_res_tac semantics_typeset >>
  metis_tac[typeset_has_meaning])

val tyinst_id_map = store_thm("tyinst_id_map",
  ``∀ty s. FINITE s ⇒ tyinst (FUN_FMAP Tyvar s) ty = ty``,
  ho_match_mp_tac type_ind >>
  simp[EVERY_MEM,MAP_EQ_ID,FLOOKUPD_def,FLOOKUP_FUN_FMAP] >>
  rw[])
val _ = export_rewrites["tyinst_id_map"]

val simple_inst_id_map = store_thm("simple_inst_id_map",
  ``∀tm s. FINITE s ⇒ simple_inst (FUN_FMAP Tyvar s) tm = tm``,
  Induct >> simp[])
val _ = export_rewrites["simple_inst_id_map"]

val new_basic_type_definition_correct = store_thm("new_basic_type_definition_correct",
  ``is_model M ⇒
    ∀p w n abs rep x rty aty.
      closed p ∧ [] |= Comb p w ∧
      rty = domain (typeof p) ∧
      aty = Tyapp (Tydefined n p) (MAP Tyvar (STRING_SORT (tvars p)))
      ⇒
      [] |=
        Comb (Const abs (Fun rty aty) (Tyabs n p))
             (Comb (Const rep (Fun aty rty) (Tyrep n p))
                   (Var x aty)) === Var x aty ∧
      [] |=
        Comb p (Var x rty) ===
        Comb (Const rep (Fun aty rty) (Tyrep n p))
             (Comb (Const abs (Fun rty aty) (Tyabs n p))
                   (Var x rty)) === Var x rty``,
  strip_tac >>
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  rpt gen_tac >> strip_tac >>
  fs[Q.SPECL[`Comb p w`,`Bool`]has_type_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  `∀τ. type_valuation τ ∧ set (tvars p) ⊆ FDOM τ ⇒
     ∃mrty mp z.
       typeset τ (typeof w) mrty ∧ semantics FEMPTY τ p mp ∧ z <: mrty ∧
       Holds mp z` by (
    gen_tac >> strip_tac >>
    `type_has_meaning (typeof w)` by metis_tac[has_meaning_type_has_meaning] >>
    pop_assum mp_tac >>
    simp[type_has_meaning_def] >>
    disch_then(qspec_then`τ`mp_tac) >>
    discharge_hyps >- (
      fs[WELLTYPED] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] ) >>
    strip_tac >>
    qexists_tac`m` >> rw[] >>
    `∃mp. semantics FEMPTY τ p mp` by (
      fs[has_meaning_def] >>
      first_x_assum match_mp_tac >>
      simp[] >>
      fs[closes_def] ) >>
    qexists_tac`mp` >>
    rw[] >>
    `∃σ τw mw. term_valuation τw σ ∧ type_valuation τw ∧ semantics σ τw w mw` by (
      fs[has_meaning_def] >> metis_tac[] ) >>
    qspecl_then[`FEMPTY`,`τ ⊌ τw`,`w`]mp_tac (UNDISCH closing_envs_exist) >>
    discharge_hyps >- (
      simp[type_valuation_union] >>
      rw[] >>
      imp_res_tac has_meaning_VFREE_IN >>
      rfs[type_has_meaning_def] >>
      first_x_assum match_mp_tac >>
      simp[type_valuation_union] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def] >>
      imp_res_tac semantics_closes >>
      fs[closes_def,SUBSET_DEF] ) >>
    disch_then(qx_choosel_then[`s`,`t`]strip_assume_tac) >>
    first_x_assum(qspecl_then[`s`,`t`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      match_mp_tac closes_extend >>
      map_every qexists_tac[`{}`,`FDOM τ`] >>
      simp[] >>
      fs[SUBMAP_DEF,SUBSET_DEF] >>
      metis_tac[semantics_closes,FDOM_FEMPTY,term_valuation_FEMPTY] ) >>
    simp[Once semantics_cases] >>
    rw[] >>
    `semantics FEMPTY τ p m1` by (
      match_mp_tac semantics_reduce >>
      map_every qexists_tac[`t`,`s`] >>
      simp[] >>
      conj_tac >- metis_tac[SUBMAP_FUNION,SUBMAP_REFL,SUBMAP_TRANS] >>
      metis_tac[semantics_closes,FDOM_FEMPTY,term_valuation_FEMPTY] ) >>
    `m1 = mp` by metis_tac[semantics_11] >>
    qexists_tac`m2` >> simp[holds_def] >>
    qspecl_then[`s`,`t`,`w`,`m2`]mp_tac(CONJUNCT2 (UNDISCH semantics_typeset)) >>
    simp[] >> rw[] >>
    qsuff_tac`typeset t (typeof w) m` >- metis_tac[semantics_11] >>
    match_mp_tac typeset_extend >>
    qexists_tac`τ` >>
    metis_tac[SUBMAP_FUNION,SUBMAP_REFL,SUBMAP_TRANS] ) >>
  simp[GSYM CONJ_ASSOC] >>
  conj_asm1_tac >- (
    simp[equation_has_meaning_iff] >>
    reverse conj_asm2_tac >- (
      simp[type_has_meaning_def] >>
      rw[] >>
      simp[Once semantics_cases] >>
      qexists_tac`MAP (FAPPLY τ) (STRING_SORT (tvars p))` >>
      Q.PAT_ABBREV_TAC`t0 = A(X):string|->'U` >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`typeof w` >>
      simp[] >>
      `t0 ⊑ τ` by (
        simp[Abbr`t0`,SUBMAP_DEF,FUN_FMAP_DEF,MAP_ZIP] >>
        fs[SUBSET_DEF,tyvars_def,MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM,MEM_MAP] ) >>
      first_x_assum(qspec_then`t0`mp_tac) >>
      discharge_hyps >- (
        conj_tac >- metis_tac[type_valuation_reduce] >>
        simp[Abbr`t0`,MAP_ZIP,SUBSET_DEF] ) >>
      strip_tac >>
      map_every qexists_tac[`z`,`mrty`,`mp`] >>
      simp[] >>
      simp[EVERY2_MAP] >>
      simp[Once semantics_cases,FLOOKUP_DEF] >>
      match_mp_tac EVERY2_refl >>
      simp[] >>
      fs[tyvars_def,SUBSET_DEF,MEM_MAP,MEM_FOLDR_LIST_UNION]) >>
    simp[] >>
    conj_tac >>
    match_mp_tac semantics_has_meaning >>
    simp[Once semantics_cases] >>
    srw_tac[DNF_ss][] >>
    `∃τ mp. type_valuation τ ∧ semantics FEMPTY τ p mp` by (
      fs[has_meaning_def] >>
      qexists_tac`τ` >> simp[] >>
      first_x_assum match_mp_tac >>
      simp[] >>
      fs[closes_def]) >>
    map_every qexists_tac[`FEMPTY`,`τ`,`MAP (FAPPLY τ) (STRING_SORT (tvars p))`] >>
    simp[] >>
    Q.PAT_ABBREV_TAC`tt:string|->'U = FUN_FMAP X Y` >>
    qmatch_assum_abbrev_tac`type_has_meaning ty` >>
    `tt ⊑ τ` by (
      simp[Abbr`tt`,SUBMAP_DEF,FUN_FMAP_DEF,MAP_ZIP] >>
      imp_res_tac semantics_closes >>
      fs[closes_def,SUBSET_DEF] ) >>
    `type_valuation tt` by metis_tac[type_valuation_reduce] >>
    `∃maty. typeset τ ty maty` by (
      fs[type_has_meaning_def] >>
      first_x_assum match_mp_tac >>
      simp[Abbr`ty`,tyvars_def,SUBSET_DEF,MEM_FOLDR_LIST_UNION,MEM_MAP] >>
      rw[] >> fs[tyvars_def] >> rw[] >>
      imp_res_tac semantics_closes >>
      fs[closes_def,SUBSET_DEF] ) >>
    `∃mrty. typeset tt (typeof w) mrty` by (
      imp_res_tac has_meaning_type_has_meaning >>
      fs[type_has_meaning_def] >>
      first_x_assum match_mp_tac >>
      simp[SUBSET_DEF] >> rw[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      imp_res_tac semantics_closes >>
      fs[closes_def,SUBSET_DEF,tyvars_def] >>
      simp[Abbr`tt`]) >>
    qexists_tac`maty` >>
    ((map_every qexists_tac [`mp`,`mrty`])ORELSE(qexists_tac`mrty`)) >>
    simp[] >>
    TRY conj_tac >>
    TRY (
      match_mp_tac semantics_reduce >>
      qexists_tac`τ` >>
      qexists_tac`FEMPTY` >>
      simp[closes_def,Abbr`tt`,SUBSET_DEF]) >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_refl >>
    simp[] >>
    fs[tyvars_def,SUBSET_DEF,MEM_MAP,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases,FLOOKUP_DEF] >>
    imp_res_tac semantics_closes >>
    fs[closes_def,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[] >>
    match_mp_tac (UNDISCH semantics_equation) >>
    rw[] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases] >>
    srw_tac[DNF_ss][] >>
    rfs[equation_has_meaning_iff] >>
    qmatch_assum_abbrev_tac`closes s t (l === r)` >>
    qspecl_then[`s`,`t`,`l`,`r`,`typeof r`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
    discharge_hyps_keep >- (
      unabbrev_all_tac >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] ) >>
    strip_tac >> fs[] >>
    pop_assum kall_tac >>
    `p has_type (typeof p)` by metis_tac[WELLTYPED] >>
    first_assum(qspec_then`τ`mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[Abbr`r`,tyvars_def,SUBSET_DEF,tvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP] ) >>
    disch_then(qx_choosel_then[`mrty`,`mp`,`z`]strip_assume_tac) >>
    qabbrev_tac`ams = MAP (FAPPLY τ) (STRING_SORT (tvars p))` >>
    `set (tvars p) ⊆ t` by (
      imp_res_tac semantics_closes >>
      rfs[closes_def] ) >>
    `LIST_REL (typeset τ) (MAP Tyvar (STRING_SORT (tvars p))) ams` by (
      simp[EVERY2_MAP,Abbr`ams`] >>
      match_mp_tac EVERY2_refl >>
      simp[] >>
      simp[Once semantics_cases,FLOOKUP_DEF] >>
      fs[SUBSET_DEF] ) >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => List.drop(ls,2) @ List.take(ls,2))) >>
    qexists_tac`ams` >>
    Q.PAT_ABBREV_TAC`t0 = A(X):string|->'U` >>
    `t0 ⊑ τ` by (
      simp[Abbr`ams`,Abbr`t0`,SUBMAP_DEF,FUN_FMAP_DEF,MAP_ZIP] >>
      fs[SUBSET_DEF] ) >>
    `closes ∅ (FDOM t0) p` by (
      simp[closes_def,Abbr`t0`,MAP_ZIP,Abbr`ams`,SUBSET_DEF] ) >>
    `semantics FEMPTY t0 p mp` by (
      match_mp_tac semantics_reduce >>
      map_every qexists_tac[`τ`,`FEMPTY`] >>
      simp[] ) >>
    `typeset t0 (typeof w) mrty` by (
      match_mp_tac typeset_reduce >>
      qexists_tac`τ` >>
      simp[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[Abbr`t0`,tyvars_def,SUBSET_DEF,MAP_ZIP,Abbr`ams`] ) >>
    `∃maty. typeset τ (Tyapp (Tydefined n p) (MAP Tyvar (STRING_SORT (tvars p)))) maty` by (
      simp[Once semantics_cases] >>
      map_every qexists_tac[`ams`,`mp`,`mrty`,`typeof w`,`z`] >>
      simp[] ) >>
    map_every qexists_tac[`maty`,`mp`,`mrty`] >>
    simp[] >>
    simp[Once semantics_cases] >>
    srw_tac[DNF_ss][] >>
    simp[Once semantics_cases] >>
    srw_tac[DNF_ss][] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`mrty`,`maty`,`ams`] >>
    simp[] >>
    simp[Abbr`r`] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases] >>
    simp[FLOOKUP_DEF] >>
    fs[closes_def] >>
    imp_res_tac is_model_is_set_theory >>
    simp[boolean_eq_true] >>
    qmatch_abbrev_tac`Abstract a b c ' (Abstract b a f ' g) = g` >>
    `type_valuation t0` by metis_tac[type_valuation_reduce] >>
    `g <: a ∧ Holds mp g` by (
      fs[term_valuation_def,FEVERY_DEF] >>
      qmatch_assum_abbrev_tac`(x,y) ∈ s` >>
      first_x_assum(qspec_then`x,y`mp_tac) >>
      simp[] >>
      simp[Abbr`y`,Once semantics_cases] >>
      strip_tac >>
      rfs[mem_sub] >>
      `ams' = ams` by (
        rfs[LIST_EQ_REWRITE,EVERY2_EVERY,EVERY_MEM] >>
        fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
        metis_tac[semantics_11] ) >>
      BasicProvers.VAR_EQ_TAC >> rfs[] >>
      `mp' = mp` by metis_tac[semantics_11] >>
      imp_res_tac WELLTYPED_LEMMA >>
      rfs[] >>
      `mrty' = mrty` by metis_tac[semantics_11] >>
      fs[Abbr`a`] ) >>
    `g <: b` by (
      fs[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
      qmatch_assum_abbrev_tac`Abbrev(g = σ ' k)` >>
      `FLOOKUP σ k = SOME g` by ( simp[FLOOKUP_DEF] ) >>
      metis_tac[semantics_11,SND]) >>
    `Abstract b a f ' g = f g` by (
      match_mp_tac (MP_CANON apply_abstract) >>
      simp[Abbr`f`] ) >>
    simp[Abbr`a`,Abbr`f`] >>
    `g = c g` by ( simp[Abbr`c`] ) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac`c g` >>
    reverse conj_tac >- rw[] >>
    simp[Abbr`b`] >>
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`c`,mem_sub]) >>
  conj_asm1_tac >- (
    simp[welltyped_def] >>
    qexists_tac`Bool` >>
    simp[EQUATION_HAS_TYPE_BOOL] ) >>
  conj_asm1_tac >- (
    rfs[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac WELLTYPED_LEMMA >>
    simp[EQUATION_HAS_TYPE_BOOL] ) >>
  conj_tac >- (
    simp[equation_has_meaning_iff] >>
    rfs[equation_has_meaning_iff] >>
    rw[has_meaning_type_has_meaning] ) >>
  rw[] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  simp[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  Q.PAT_ABBREV_TAC`P = (Bool = X)` >>
  `P` by (
    qunabbrev_tac`P` >>
    match_mp_tac EQ_SYM >>
    match_mp_tac WELLTYPED_LEMMA >>
    simp[EQUATION_HAS_TYPE_BOOL] ) >>
  qunabbrev_tac`P` >> simp[] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`closes s t (l === r)` >>
  qspecl_then[`s`,`t`,`l`,`r`,`typeof l`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
  discharge_hyps_keep >- (
    unabbrev_all_tac >>
    simp[Once has_type_cases] >>
    simp[GSYM LEFT_EXISTS_AND_THM] >>
    qexists_tac`typeof w` >> simp[] >>
    simp[Once has_type_cases] >>
    simp[EQUATION_HAS_TYPE_BOOL]) >>
  strip_tac >> fs[] >>
  pop_assum kall_tac >>
  `p has_type (typeof p)` by metis_tac[WELLTYPED] >>
  rfs[] >>
  first_assum(qspec_then`τ`mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    rfs[Abbr`l`,closes_def]) >>
  disch_then(qx_choosel_then[`mrty`,`mp`,`z`]strip_assume_tac) >>
  `semantics σ τ p mp` by metis_tac[semantics_extend,term_valuation_FEMPTY,SUBMAP_FEMPTY,SUBMAP_REFL] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`mp` >> simp[] >>
  simp[Once semantics_cases] >>
  fs[Abbr`l`,closes_def] >>
  simp[FLOOKUP_DEF] >>
  imp_res_tac is_model_is_set_theory >>
  simp[boolean_eq_true] >>
  simp[Abbr`r`] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  simp[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  qabbrev_tac`ams = MAP (FAPPLY τ) (STRING_SORT (tvars p))` >>
  `set (tvars p) ⊆ t` by (
    imp_res_tac semantics_closes >>
    rfs[closes_def] ) >>
  `LIST_REL (typeset τ) (MAP Tyvar (STRING_SORT (tvars p))) ams` by (
    simp[EVERY2_MAP,Abbr`ams`] >>
    match_mp_tac EVERY2_refl >>
    simp[] >>
    simp[Once semantics_cases,FLOOKUP_DEF] >>
    fs[SUBSET_DEF] ) >>
  CONV_TAC(RESORT_EXISTS_CONV(fn ls => List.drop(ls,2) @ List.take(ls,2))) >>
  qexists_tac`ams` >>
  Q.PAT_ABBREV_TAC`t0 = A(X):string|->'U` >>
  `t0 ⊑ τ` by (
    simp[Abbr`ams`,Abbr`t0`,SUBMAP_DEF,FUN_FMAP_DEF,MAP_ZIP] >>
    fs[SUBSET_DEF] ) >>
  `closes ∅ (FDOM t0) p` by (
    simp[closes_def,Abbr`t0`,MAP_ZIP,Abbr`ams`,SUBSET_DEF] ) >>
  `semantics FEMPTY t0 p mp` by (
    match_mp_tac semantics_reduce >>
    map_every qexists_tac[`τ`,`FEMPTY`] >>
    simp[] ) >>
  `typeset t0 (typeof w) mrty` by (
    match_mp_tac typeset_reduce >>
    qexists_tac`τ` >>
    simp[] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[Abbr`t0`,tyvars_def,SUBSET_DEF,MAP_ZIP,Abbr`ams`] ) >>
  `∃maty. typeset τ (Tyapp (Tydefined n p) (MAP Tyvar (STRING_SORT (tvars p)))) maty` by (
    simp[Once semantics_cases] >>
    map_every qexists_tac[`ams`,`mp`,`mrty`,`typeof w`,`z`] >>
    simp[] ) >>
  map_every qexists_tac[`maty`,`mrty`] >>
  simp[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`mrty`,`mp`,`maty`,`ams`] >>
  simp[] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[FLOOKUP_DEF] >>
  qmatch_abbrev_tac`Boolean (Abstract b a f ' (Abstract a b g ' d)= d) = e` >>
  `d <: a` by (
    fs[term_valuation_def,FEVERY_DEF] >>
    qmatch_assum_abbrev_tac`(x,y) ∈ s` >>
    first_x_assum(qspec_then`x,y`mp_tac) >>
    simp[] >>
    strip_tac >>
    metis_tac[semantics_11] ) >>
  `is_choice mem ch` by fs[is_model_def] >> fs[is_choice_def] >>
  first_assum(qspec_then`a suchthat Holds mp`mp_tac) >>
  discharge_hyps >- (simp[mem_sub] >> metis_tac[]) >>
  simp[mem_sub] >> strip_tac >>
  `ch maty <: maty` by (
    metis_tac[typeset_inhabited] ) >>
  `type_valuation t0` by metis_tac[type_valuation_reduce] >>
  `if Holds mp d then d <: maty else ch maty <: mrty ∧ ch maty ≠ d` by (
    rw[] >>
    qpat_assum`typeset X Y b`mp_tac >>
    simp[Once semantics_cases] >>
    rw[] >>
    simp[mem_sub] >>
    `ams' = ams` by (
      rfs[LIST_EQ_REWRITE,EVERY2_EVERY,EVERY_MEM] >>
      fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      metis_tac[semantics_11] ) >>
    BasicProvers.VAR_EQ_TAC >> rfs[] >>
    `mp' = mp` by metis_tac[semantics_11] >>
    imp_res_tac WELLTYPED_LEMMA >>
    rfs[] >>
    `mrty' = mrty` by metis_tac[semantics_11] >>
    fs[Abbr`a`] >> metis_tac[] ) >>
  `Abstract a b g ' d = g d` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`g`,Abbr`b`,mem_sub] >>
    BasicProvers.CASE_TAC >>
    simp[] ) >>
  rfs[] >>
  `Abstract b a f ' (g d) = f (g d)` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`f`,Abbr`g`,Abbr`b`] >>
    BasicProvers.CASE_TAC >>
    fs[] ) >>
  simp[Abbr`f`,Abbr`g`,Abbr`d`,boolean_def,Abbr`e`] >>
  simp[holds_def] >>
  BasicProvers.CASE_TAC >>
  fs[Abbr`a`,Abbr`b`,holds_def] >>
  `mp ' (σ ' (x,typeof w)) <: boolset` by (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`mrty` >> simp[] >>
    qspecl_then[`FEMPTY`,`τ`,`p`,`mp`]mp_tac(CONJUNCT2 (UNDISCH semantics_typeset)) >>
    simp[] >>
    simp[Once semantics_cases] >>
    asm_simp_tac(srw_ss()++DNF_ss)[] >>
    qpat_assum`Bool = X`(assume_tac o SYM) >>
    simp[] >>
    metis_tac[semantics_11] ) >>
  pop_assum mp_tac >>
  simp[mem_boolset])

val ETA_AX_correct = store_thm("ETA_AX_correct",
  ``is_model M ⇒
    ∀t ty x.
    has_meaning t ∧ type_has_meaning ty ∧ welltyped (Comb t (Var x ty)) ∧ ¬VFREE_IN (Var x ty) t
    ⇒
    [] |= Abs x ty (Comb t (Var x ty)) === t``,
  rw[sequent_def,EQUATION_HAS_TYPE_BOOL] >> rw[] >- (
    match_mp_tac (UNDISCH equation_has_meaning) >> simp[] ) >>
  match_mp_tac (UNDISCH semantics_equation) >>
  imp_res_tac is_model_is_set_theory >>
  simp[boolean_eq_true] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  qmatch_assum_abbrev_tac`closes s y (l === t)` >>
  qspecl_then[`s`,`y`,`l`,`t`,`typeof l`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
  discharge_hyps_keep >- (
    unabbrev_all_tac >>
    simp[] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    imp_res_tac WELLTYPED >> rfs[] >>
    qexists_tac`ty` >> simp[] >>
    simp[Once has_type_cases] ) >>
  strip_tac >> fs[] >> pop_assum kall_tac >>
  `∃mty. typeset τ ty mty` by (
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[closes_def] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[SUBSET_DEF] >> rfs[tyvars_def] ) >>
  `∃mtyb. typeset τ rty mtyb` by (
    imp_res_tac has_meaning_type_has_meaning >> rfs[] >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[closes_def] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[SUBSET_DEF] >> rfs[tyvars_def] ) >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`rty`,`mtyb`,`mty`] >>
  simp[] >>
  simp[Once has_type_cases,RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    qexists_tac`ty` >>
    imp_res_tac WELLTYPED >>
    rfs[] >>
    simp[Once has_type_cases] ) >>
  `∃m. semantics σ τ t m` by (
    fs[has_meaning_def] ) >>
  `m <: Funspace mty mtyb` by (
    imp_res_tac semantics_typeset >>
    rfs[] >>
    ntac 2 (pop_assum mp_tac) >>
    simp[Once semantics_cases] >>
    rw[] >>
    metis_tac[semantics_11] ) >>
  qspecl_then[`m`,`mty`,`mtyb`]mp_tac (UNDISCH in_funspace_abstract) >>
  discharge_hyps >- (
    simp[] >>
    metis_tac[typeset_inhabited] ) >>
  strip_tac >>
  qexists_tac`f` >>
  fs[] >>
  rw[Once semantics_cases] >>
  qmatch_assum_rename_tac`z <: mty`[] >>
  `semantics (σ |+ ((x,ty),z)) τ t = semantics σ τ t` by (
    match_mp_tac semantics_frees >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >> fs[] ) >>
  simp[] >>
  qexists_tac`Abstract mty mtyb f` >>
  simp[] >>
  simp[Once semantics_cases,FLOOKUP_UPDATE] >>
  match_mp_tac EQ_SYM >>
  metis_tac[apply_abstract])

val SELECT_AX_correct = store_thm("SELECT_AX_correct",
  ``is_model M ⇒
    ∀h p ty w.
      p has_type Fun ty Bool ∧ h |= Comb p w ⇒
      h |= Comb p (Comb (Select ty) p)``,
  rw[sequent_def] >>
  imp_res_tac is_model_is_set_theory
  >- (
    simp[Once has_type_cases] >>
    qexists_tac`ty` >> simp[] >>
    simp[Once has_type_cases] >>
    qexists_tac`Fun ty Bool` >>
    simp[] >>
    simp[Once has_type_cases] )
  >- metis_tac[WELLTYPED_LEMMA]
  >- metis_tac[WELLTYPED_LEMMA]
  >- metis_tac[WELLTYPED_LEMMA]
  >- (
    match_mp_tac semantics_has_meaning >>
    simp[Once semantics_cases] >>
    srw_tac[DNF_ss][] >>
    imp_res_tac has_meaning_type_has_meaning >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] >>
    Q.ISPEC_THEN`set (tyvars (typeof w))`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >>
    disch_then(qspec_then`FEMPTY`mp_tac) >>
    simp[] >> strip_tac >>
    map_every qexists_tac[`FEMPTY`,`τ'`] >>
    simp[] >>
    fs[type_has_meaning_def] ) >>
  simp[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] >>
  `∃m. semantics σ τ p m` by (
    fs[has_meaning_def] ) >>
  qexists_tac`m` >> simp[] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  qexists_tac`m` >> simp[] >>
  `∃mty. typeset τ (typeof w) mty` by (
    imp_res_tac has_meaning_type_has_meaning >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fs[closes_def] >>
    `w has_type (typeof w)` by metis_tac[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[SUBSET_DEF,tyvars_def] ) >>
  qexists_tac`mty` >>
  simp[] >>
  qmatch_abbrev_tac `True = m ' (Abstract fs mty f ' m)` >>
  `Abstract fs mty f ' m = f m` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    imp_res_tac semantics_typeset >>
    rfs[] >>
    ntac 2 (pop_assum mp_tac) >>
    simp[Once semantics_cases] >>
    strip_tac >>
    imp_res_tac semantics_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[Abbr`fs`] >>
    simp[Abbr`f`] >>
    rw[] >>
    metis_tac[is_model_def,is_choice_def,mem_sub] ) >>
  simp[Abbr`f`] >>
  pop_assum kall_tac >>
  BasicProvers.CASE_TAC >- (
    match_mp_tac EQ_SYM >>
    simp[GSYM holds_def] >>
    qmatch_abbrev_tac`Holds m (ch s)` >>
    `ch s <: s` by (
      metis_tac[is_model_def,is_choice_def] ) >>
    rfs[Abbr`s`,mem_sub] ) >>
  `∃τw. set (tvars w) ⊆ (FDOM τw) ∧ type_valuation τw` by (
    fs[has_meaning_def,closes_def] >> metis_tac[] ) >>
  qspecl_then[`σ`,`τ ⊌ τw`,`Comb p w`]mp_tac (UNDISCH closing_envs_exist) >>
  discharge_hyps >- (
    simp[type_valuation_union] >>
    conj_tac >- (
      match_mp_tac term_valuation_extend_type >>
      qexists_tac`τ` >>
      simp[SUBMAP_FUNION] ) >>
    imp_res_tac has_meaning_VFREE_IN >>
    rw[] >>
    ntac 2 (first_x_assum (qspec_then`Var x ty`mp_tac)) >> rw[] >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[type_valuation_union] >>
    fs[closes_def] >>
    imp_res_tac tvars_VFREE_IN_subset >>
    fs[tvars_def,SUBSET_DEF] ) >>
  rw[] >>
  first_x_assum(qspecl_then[`σ'`,`τ'`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    fs[EVERY_MEM] >>
    rw[] >>
    match_mp_tac semantics_extend >>
    map_every qexists_tac[`σ`,`τ`] >>
    simp[] >>
    metis_tac[SUBMAP_FUNION,SUBMAP_TRANS,SUBMAP_REFL] ) >>
  `semantics σ' τ' p m` by (
    match_mp_tac semantics_extend >>
    map_every qexists_tac[`σ`,`τ`] >>
    simp[] >>
    metis_tac[SUBMAP_FUNION,SUBMAP_TRANS,SUBMAP_REFL] ) >>
  simp[Once semantics_cases] >> rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  rfs[mem_sub,holds_def] >>
  qsuff_tac`m2 <: mty` >- metis_tac[] >>
  `typeset τ' (typeof w) mty` by (
    match_mp_tac typeset_extend >>
    metis_tac[SUBMAP_FUNION,SUBMAP_REFL,SUBMAP_TRANS] ) >>
  metis_tac[semantics_typeset,semantics_11])

val truth_has_type_bool = store_thm("truth_has_type_bool",
  ``TT has_type Bool``,
  rw[TT_def] >> rw[Once has_type_cases])
val _ = export_rewrites["truth_has_type_bool"]

val closed_truth = store_thm("closed_truth",
  ``closed TT``, rw[TT_def])
val _ = export_rewrites["closed_truth"]

val semantics_truth = store_thm("semantics_truth",
  ``is_model M ⇒ ∀σ τ.
    type_valuation τ ∧
    term_valuation τ σ
    ⇒
    semantics σ τ TT True``,
  rw[TT_def] >>
  simp[Once semantics_cases] >>
  qexists_tac`FEMPTY` >> simp[] >>
  Q.PAT_ABBREV_TAC`tm = x === x` >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >>
  simp[] >> strip_tac >>
  `tm has_type Bool` by (
    simp[Abbr`tm`,EQUATION_HAS_TYPE_BOOL] ) >>
  `welltyped tm` by PROVE_TAC[welltyped_def] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[] >>
  conj_tac >- (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac ACONV_SYM >>
    imp_res_tac ACONV_VFREE_IN >>
    fs[Abbr`tm`,vfree_in_equation] >>
    PROVE_TAC[] ) >>
  qpat_assum`Bool = X`(assume_tac o SYM) >>
  conj_asm1_tac >- (
    simp[SUBSET_DEF,tyvars_def] >>
    rpt strip_tac >>
    imp_res_tac ACONV_tvars >>
    pop_assum(mp_tac o SYM) >>
    Q.PAT_ABBREV_TAC`fm = fresh_term X Y` >>
    simp[Abbr`tm`,tvars_def,equation_def,tyvars_def,LIST_UNION_def] >>
    metis_tac[MEM] ) >>
  qsuff_tac`semantics FEMPTY τ tm True` >-
    metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  qmatch_assum_abbrev_tac`Abbrev(tm = tt === tt)` >>
  qspec_then`tt`mp_tac(UNDISCH REFL_correct) >>
  discharge_hyps >- simp[Abbr`tt`] >>
  simp[sequent_def] >> strip_tac >>
  first_x_assum match_mp_tac >>
  simp[Abbr`tm`] >> fs[EQUATION_HAS_TYPE_BOOL] >>
  qspecl_then[`typeof tt`,`tt`,`tt`,`{}`,`FDOM τ`]mp_tac(Q.GENL[`τ`,`σ`,`l`,`r`,`ty`] closes_equation) >>
  simp[GSYM WELLTYPED] >>
  disch_then kall_tac >>
  rfs[] >>
  simp[Abbr`tt`,tyvars_def])

val sequent_truth = store_thm("sequent_truth",
  ``is_model M ⇒ [] |= TT``,
  strip_tac >>
  simp[sequent_def] >>
  conj_asm2_tac >- (
    match_mp_tac semantics_has_meaning >>
    ntac 2 (qexists_tac`FEMPTY`) >>
    qexists_tac`True` >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[TT_def,tyvars_def] ) >>
  rw[semantics_truth])

val conjunction_has_type_bool = store_thm("conjunction_has_type_bool",
  ``∀p q. AN p q has_type Bool ⇔ p has_type Bool ∧ q has_type Bool``,
  simp[AN_def] >>
  simp[Once has_type_cases] >>
  simp[Once has_type_cases] >>
  simp[Once has_type_cases] )

val ACONV_closed = store_thm("ACONV_closed",
  ``∀t1 t2. ACONV t1 t2 ⇒ (closed t1 ⇔ closed t2)``,
  qsuff_tac`∀t1 t2. ACONV t1 t2 ∧ closed t1 ⇒ closed t2` >-
    metis_tac[ACONV_SYM] >>
  rw[] >> spose_not_then strip_assume_tac >>
  imp_res_tac ACONV_VFREE_IN >>
  metis_tac[ACONV_SYM])

val apply_abstract_matchable = store_thm("apply_abstract_matchable",
  ``∀f x s t u. x <: s ∧ f x <: t ∧ is_set_theory ^mem ∧ f x = u ⇒ Abstract s t f ' x = u``,
  metis_tac[apply_abstract])

val apply_abstract_both_matchable = store_thm("apply_abstract_both_matchable",
  ``∀f x s t u v. x <: s ∧ f x <: t ∧ is_set_theory ^mem ∧ f x = u ∧ Abstract s t f = v ⇒ v ' x = u``,
  metis_tac[apply_abstract])

val semantics_and = store_thm("semantics_and",
  ``is_model M ⇒
    ∀σ τ.
    type_valuation τ ∧
    term_valuation τ σ
    ⇒
    semantics σ τ ^(rand(rator(rand(rhs(concl(SPEC_ALL AN_def))))))
      (Abstract boolset (Funspace boolset boolset)
        (λp. Abstract boolset boolset (λq. Boolean (p = True ∧ q = True))))``,
  Q.PAT_ABBREV_TAC`tm:term = (Abs X Y Z)` >>
  rw[Once semantics_cases] >>
  imp_res_tac is_model_is_set_theory >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >> rw[] >>
  `tm has_type Fun Bool (Fun Bool Bool)` by (
    simp[Abbr`tm`] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `welltyped tm` by metis_tac[WELLTYPED] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >> pop_assum (assume_tac o SYM) >> rfs[] >>
  `closed tm` by (
    simp[Abbr`tm`,vfree_in_equation] >>
    PROVE_TAC[] ) >>
  imp_res_tac ACONV_closed >>
  simp[tyvars_def] >>
  imp_res_tac ACONV_tvars >> pop_assum (assume_tac o SYM) >>
  `tvars tm = []` by (
    simp[Abbr`tm`,tvars_def,tyvars_def,equation_def,TT_def] ) >>
  simp[] >>
  qexists_tac`FEMPTY`>>simp[] >>
  qmatch_abbrev_tac`semantics x y z w` >>
  qsuff_tac`semantics x y tm w` >- metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  unabbrev_all_tac >>
  ntac 12 (pop_assum kall_tac) >>
  simp[Once semantics_cases] >>
  qexists_tac`λp. Abstract boolset boolset (λq. Boolean (p = True ∧ q = True))` >>
  qexists_tac`Funspace boolset boolset` >>
  qexists_tac`Fun Bool Bool` >>
  simp[Once has_type_cases] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] >>
  simp[Once semantics_cases] >>
  qx_gen_tac`p` >> strip_tac >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Once semantics_cases] >>
  qexists_tac`λq. Boolean (p = True ∧ q = True)` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] >>
  qx_gen_tac`q` >> strip_tac >>
  simp[boolean_in_boolset] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (
    match_mp_tac term_valuation_FUPDATE >> simp[] >>
    match_mp_tac term_valuation_FUPDATE >> simp[] ) >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS,FLOOKUP_UPDATE] >>
  simp[Once semantics_cases,PULL_EXISTS,FLOOKUP_UPDATE] >>
  simp[Once semantics_cases,PULL_EXISTS,FLOOKUP_UPDATE] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once has_type_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS] >>
  simp[Once semantics_cases,PULL_EXISTS,FLOOKUP_UPDATE] >>
  qexists_tac`λm. m ' p ' q` >>
  qexists_tac`λm. m ' True ' True` >>
  simp[] >>
  conj_asm1_tac >- (
    rw[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`boolset` >> simp[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`boolset` >> simp[] ) >>
  conj_tac >- (
    rw[] >>
    ntac 2 (qexists_tac`True`) >>
    simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH apply_in_rng) >>
      qexists_tac`boolset` >> simp[mem_boolset] >>
      match_mp_tac (UNDISCH apply_in_rng) >>
      qexists_tac`boolset` >> simp[mem_boolset] ) >>
    conj_tac >- (
      match_mp_tac (UNDISCH semantics_truth) >>
      simp[] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] ) >>
    conj_tac >- metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] >>
    conj_tac >- metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] >>
    conj_tac >- (
      match_mp_tac (UNDISCH semantics_truth) >>
      simp[] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[Once semantics_cases,PULL_EXISTS] ) >>
    metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] ) >>
  simp[boolean_def] >>
  rw[] >>
  qmatch_assum_abbrev_tac`f1 = f2` >>
  qabbrev_tac`m = Abstract boolset (Funspace boolset boolset) (λx. Abstract boolset boolset (λy. Boolean (x = p ∧ y = q)))` >>
  `m <: Funspace boolset (Funspace boolset boolset)` by (
    simp[Abbr`m`] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    simp[boolean_in_boolset] ) >>
  `f1 ' m = True` by (
    qunabbrev_tac`f1` >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    `m ' p = Abstract boolset boolset (λy. Boolean (y = q))` by (
      simp[Abbr`m`] >>
      match_mp_tac apply_abstract_matchable >>
      simp[] >>
      match_mp_tac ABSTRACT_IN_FUNSPACE >>
      simp[boolean_in_boolset] ) >>
    simp[] >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset,boolean_eq_true] ) >>
  `f2 ' m = False` by (
    qunabbrev_tac`f2` >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH apply_in_rng) >>
      qexists_tac`boolset`>>simp[mem_boolset] >>
      match_mp_tac (UNDISCH apply_in_rng) >>
      qexists_tac`boolset`>>simp[mem_boolset] ) >>
    `m ' True = Abstract boolset boolset (λy. Boolean (True = p ∧ y = q))` by (
      simp[Abbr`m`] >>
      match_mp_tac apply_abstract_matchable >>
      simp[mem_boolset] >>
      match_mp_tac ABSTRACT_IN_FUNSPACE >>
      simp[boolean_in_boolset] ) >>
    simp[] >>
    match_mp_tac apply_abstract_matchable >>
    simp[mem_boolset,boolean_def] >>
    rw[] >> fs[] ) >>
  metis_tac[true_neq_false])

val semantics_conjunction = store_thm("semantics_conjunction",
  ``is_model M ⇒
    ∀σ τ p1 p2 m1 m2.
    p1 has_type Bool ∧ p2 has_type Bool ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    semantics σ τ p1 m1 ∧
    semantics σ τ p2 m2
    ⇒
    semantics σ τ (AN p1 p2) (Boolean (m1 = True ∧ m2 = True))``,
  rw[AN_def] >>
  imp_res_tac is_model_is_set_theory >>
  rw[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[WELLTYPED] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m2` >> simp[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m1` >> simp[] >>
  simp[WELLTYPED] >>
  exists_tac(rand(rand(concl(SPEC_ALL (UNDISCH semantics_and))))) >>
  `m1 <: boolset ∧ m2 <: boolset` by (
    imp_res_tac semantics_typeset >> rfs[] ) >>
  conj_tac >- (
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_both_matchable >>
    qexists_tac`λq. Boolean (m1 = True ∧ q = True)` >>
    qexists_tac`boolset` >>
    qexists_tac`boolset` >>
    simp[boolean_in_boolset] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    simp[boolean_in_boolset] ) >>
  match_mp_tac (UNDISCH semantics_and) >>
  simp[])

val semantics_implies = store_thm("semantics_implies",
  ``is_model M ⇒
    ∀σ τ.
    type_valuation τ ∧
    term_valuation τ σ
    ⇒
    semantics σ τ ^(rand(rator(rand(rhs(concl(SPEC_ALL IM_def))))))
      (Abstract boolset (Funspace boolset boolset)
        (λp. Abstract boolset boolset (λq. Boolean (p = True ⇒ q = True))))``,
  Q.PAT_ABBREV_TAC`tm:term = (Abs X Y Z)` >>
  rw[Once semantics_cases] >>
  imp_res_tac is_model_is_set_theory >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >> rw[] >>
  qabbrev_tac`p = Var "p" Bool` >>
  qabbrev_tac`q = Var "q" Bool` >>
  `tm has_type Fun Bool (Fun Bool Bool)` by (
    simp[Abbr`tm`] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[EQUATION_HAS_TYPE_BOOL] >>
    qspecl_then[`p`,`q`]mp_tac conjunction_has_type_bool >>
    `p has_type Bool ∧ q has_type Bool` by (
      simp[Abbr`p`,Abbr`q`,Once has_type_cases] >>
      simp[Once has_type_cases]) >>
    metis_tac[WELLTYPED_LEMMA,WELLTYPED] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `welltyped tm` by metis_tac[WELLTYPED] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >> pop_assum (assume_tac o SYM) >> rfs[] >>
  `closed tm` by (
    simp[Abbr`tm`,vfree_in_equation,AN_def,Abbr`p`,Abbr`q`] >>
    PROVE_TAC[] ) >>
  imp_res_tac ACONV_closed >>
  simp[tyvars_def] >>
  imp_res_tac ACONV_tvars >> pop_assum (assume_tac o SYM) >>
  `tvars tm = []` by (
    simp[Abbr`tm`,tvars_def,tyvars_def,equation_def,AN_def,Abbr`p`,Abbr`q`] ) >>
  simp[] >>
  qexists_tac`FEMPTY`>>simp[] >>
  qmatch_abbrev_tac`semantics x y z w` >>
  qsuff_tac`semantics x y tm w` >- metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  unabbrev_all_tac >>
  ntac 12 (pop_assum kall_tac) >>
  simp[Once semantics_cases] >>
  qexists_tac`λp. Abstract boolset boolset (λq. Boolean (p = True ⇒ q = True))` >>
  qexists_tac`Funspace boolset boolset` >>
  qexists_tac`Fun Bool Bool` >>
  simp[Once has_type_cases] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_asm1_tac >- (
    qabbrev_tac`p = Var "p" Bool` >>
    qabbrev_tac`q = Var "q" Bool` >>
    qspecl_then[`p`,`q`]mp_tac conjunction_has_type_bool >>
    `p has_type Bool ∧ q has_type Bool` by (
      simp[Abbr`p`,Abbr`q`,Once has_type_cases] >>
      simp[Once has_type_cases]) >>
    metis_tac[WELLTYPED_LEMMA,WELLTYPED] ) >>
  simp[Once semantics_cases] >>
  qx_gen_tac`p` >> strip_tac >>
  conj_tac >- (
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    simp[boolean_in_boolset] ) >>
  simp[Once semantics_cases] >>
  qexists_tac`λq. Boolean (p = True ⇒ q = True)` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[conjunction_has_type_bool,EQUATION_HAS_TYPE_BOOL] >>
  qx_gen_tac`q` >> strip_tac >>
  simp[boolean_in_boolset] >>
  match_mp_tac (UNDISCH semantics_equation) >>
  simp[] >>
  qexists_tac`Boolean (p = True ∧ q = True)` >>
  qexists_tac`p` >>
  conj_tac >- simp[term_valuation_FUPDATE] >>
  conj_tac >- (
    match_mp_tac (UNDISCH semantics_conjunction) >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[term_valuation_FUPDATE] ) >>
  simp[Once semantics_cases,FLOOKUP_UPDATE] >>
  simp[boolean_def] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  metis_tac[true_neq_false,mem_boolset])

val semantics_implication = store_thm("semantics_implication",
  ``is_model M ⇒
    ∀σ τ p1 p2 m1 m2.
    p1 has_type Bool ∧ p2 has_type Bool ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    semantics σ τ p1 m1 ∧
    semantics σ τ p2 m2
    ⇒
    semantics σ τ (IM p1 p2) (Boolean (m1 = True ⇒ m2 = True))``,
  rw[IM_def] >>
  imp_res_tac is_model_is_set_theory >>
  rw[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[WELLTYPED] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m2` >> simp[] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m1` >> simp[] >>
  simp[WELLTYPED] >>
  exists_tac(rand(rand(concl(SPEC_ALL (UNDISCH semantics_implies))))) >>
  `m1 <: boolset ∧ m2 <: boolset` by (
    imp_res_tac semantics_typeset >> rfs[] ) >>
  conj_tac >- (
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_both_matchable >>
    qexists_tac`λq. Boolean (m1 = True ⇒ q = True)` >>
    qexists_tac`boolset` >>
    qexists_tac`boolset` >>
    simp[boolean_in_boolset] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    simp[boolean_in_boolset] ) >>
  match_mp_tac (UNDISCH semantics_implies) >>
  simp[])

val semantics_implication_matchable = store_thm("semantics_implication_matchable",
  ``is_model M ⇒
    ∀σ τ p1 p2 m1 m2 m.
    p1 has_type Bool ∧ p2 has_type Bool ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    semantics σ τ p1 m1 ∧
    semantics σ τ p2 m2 ∧
    (m = Boolean (m1 = True ⇒ m2 = True))
    ⇒
    semantics σ τ (IM p1 p2) m``,
  metis_tac[semantics_implication])

val implication_has_type_bool = store_thm("implication_has_type_bool",
  ``∀p q. IM p q has_type Bool ⇔ p has_type Bool ∧ q has_type Bool``,
  rw[IM_def] >>
  rw[Once has_type_cases] >>
  rw[Once has_type_cases] >>
  rw[Once has_type_cases] )

val semantics_universal = store_thm("semantics_universal",
  ``is_model M ⇒
    ∀σ τ ty mty.
    type_valuation τ ∧
    term_valuation τ σ ∧
    typeset τ ty mty
    ⇒
    semantics σ τ ^(rand(rator(rhs(concl(SPEC_ALL FA_def)))))
      (Abstract (Funspace mty boolset) boolset
        (λp. Boolean (∀x. x <: mty ⇒ p ' x = True)))``,
  rw[] >>
  imp_res_tac is_model_is_set_theory >>
  simp[Once semantics_cases] >>
  Q.PAT_ABBREV_TAC`tm:term = (Abs X Y Z)` >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >> rw[] >>
  `tm has_type Fun (Fun (Tyvar "A") Bool) Bool` by (
    simp[Abbr`tm`] >>
    simp[Once has_type_cases] >>
    simp[EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `welltyped tm` by metis_tac[WELLTYPED] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >> pop_assum (assume_tac o SYM) >> rfs[] >>
  `closed tm` by (
    simp[Abbr`tm`,vfree_in_equation] ) >>
  imp_res_tac ACONV_closed >>
  simp[tyvars_def] >>
  imp_res_tac ACONV_tvars >> pop_assum (assume_tac o SYM) >>
  `tvars tm = ["A"]` by (
    simp[Abbr`tm`,tvars_def,tyvars_def,equation_def,TT_def,LIST_UNION_def,LIST_INSERT_def] ) >>
  simp[] >>
  qexists_tac`FEMPTY|+("A",ty)`>>simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
  match_mp_tac (MP_CANON (CONJUNCT2 (UNDISCH semantics_simple_inst))) >>
  simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
  qexists_tac`FEMPTY` >>
  qexists_tac`τ|+("A",mty)` >>
  reverse conj_asm2_tac >- (
    conj_tac >- (
      simp[type_valuation_def] >>
      rw[] >- metis_tac[typeset_inhabited] >>
      pop_assum mp_tac >>
      qid_spec_tac`x` >>
      ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
      fs[type_valuation_def] ) >>
    simp[FLOOKUP_UPDATE] ) >>
  qmatch_abbrev_tac`semantics x y z w` >>
  qsuff_tac`semantics x y tm w` >- metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  fs[] >>
  qpat_assum`type_valuation y`mp_tac >>
  unabbrev_all_tac >>
  ntac 13 (pop_assum kall_tac) >>
  strip_tac >>
  simp[Once semantics_cases] >>
  qexists_tac`λp. Boolean (∀x. x <: mty ⇒ p ' x = True)` >>
  qexists_tac`Funspace mty boolset` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- (
    simp[Once semantics_cases] >>
    qexists_tac`mty` >> simp[] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_asm1_tac >- (
    metis_tac[truth_has_type_bool,WELLTYPED_LEMMA,WELLTYPED] ) >>
  simp[boolean_in_boolset] >>
  qx_gen_tac`p` >> strip_tac >>
  match_mp_tac (UNDISCH semantics_equation) >>
  simp[] >>
  simp[Once semantics_cases,FLOOKUP_UPDATE] >>
  simp[Once semantics_cases,FLOOKUP_UPDATE,PULL_EXISTS] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`Bool`,`boolset`,`mty`] >>
  simp[truth_has_type_bool,GSYM PULL_EXISTS] >>
  conj_asm1_tac >- (
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >>
    simp[Once semantics_cases,PULL_EXISTS] >>
    map_every qexists_tac[`mty`,`boolset`] >>
    simp[] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_UPDATE] ) >>
  qexists_tac`λx. True` >>
  simp[mem_boolset] >>
  conj_tac >- (
    rw[] >>
    match_mp_tac (UNDISCH semantics_truth) >>
    simp[] >>
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] ) >>
  qspecl_then[`p`,`mty`,`boolset`]mp_tac (UNDISCH in_funspace_abstract) >>
  simp[] >>
  discharge_hyps >- (
    metis_tac[typeset_inhabited,boolean_in_boolset] ) >>
  disch_then(qx_choose_then`f`strip_assume_tac) >>
  simp[boolean_def] >>
  BasicProvers.CASE_TAC >- (
    rw[] >> fs[] >>
    simp[true_neq_false] >>
    qpat_assum`X <> True`mp_tac >>
    simp[] >>
    match_mp_tac apply_abstract_matchable >>
    simp[mem_boolset] ) >>
  rw[] >>
  simp[true_neq_false] >>
  qpat_assum`x <> y`mp_tac >>
  simp[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[mem_boolset] >>
  rw[] >>
  first_x_assum(qspec_then`x`mp_tac) >>
  rw[] >> pop_assum (SUBST1_TAC o SYM) >>
  match_mp_tac EQ_SYM >>
  match_mp_tac apply_abstract_matchable >>
  rw[])

val semantics_forall = store_thm("semantics_forall",
  ``is_model M ⇒
    ∀σ τ x ty mty p mp.
    p has_type Bool ∧
    (∀mx. mx <: mty ⇒ semantics (σ|+((x,ty),mx)) τ p (mp mx)) ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    typeset τ ty mty
    ⇒
    semantics σ τ (FA x ty p) (Boolean (∀mx. mx <: mty ⇒ mp mx = True))``,
  rw[FA_def] >>
  imp_res_tac is_model_is_set_theory >>
  simp[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[WELLTYPED] >>
  Q.PAT_ABBREV_TAC`bb = Boolean X` >>
  simp[Once semantics_cases,SimpR``$/\``] >>
  simp[PULL_EXISTS] >>
  qexists_tac`Abstract (Funspace mty boolset) boolset (λp. Boolean (∀x. x <: mty ⇒ p ' x = True))` >>
  qexists_tac`mp` >>
  qexists_tac`mty` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[] >>
  simp[CONJ_ASSOC] >>
  reverse conj_asm2_tac >- (
    rw[] >> res_tac >>
    imp_res_tac semantics_typeset >>
    rfs[] >>
    metis_tac[term_valuation_FUPDATE,SND,FST] ) >>
  conj_tac >- (
    simp[Abbr`bb`] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- (
      match_mp_tac ABSTRACT_IN_FUNSPACE >>
      simp[] ) >>
    simp[boolean_def] >>
    rw[true_neq_false] >> fs[] >>
    metis_tac[apply_abstract] ) >>
  match_mp_tac (UNDISCH semantics_universal) >>
  simp[])

val semantics_forall_matchable = store_thm("semantics_forall_matchable",
  ``is_model M ⇒
    ∀σ τ x ty mty p mp m.
    p has_type Bool ∧
    (∀mx. mx <: mty ⇒ semantics (σ|+((x,ty),mx)) τ p (mp mx)) ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    typeset τ ty mty ∧
    (m = Boolean (∀mx. mx <: mty ⇒ mp mx = True))
    ⇒
    semantics σ τ (FA x ty p) m``,
  metis_tac[semantics_forall])

val forall_has_type_bool = store_thm("forall_has_type_bool",
  ``FA x ty p has_type Bool ⇔ p has_type Bool``,
  rw[FA_def] >>
  rw[Once has_type_cases] >>
  rw[Once has_type_cases] >>
  rw[Once has_type_cases])

val semantics_falsity = store_thm("semantics_falsity",
  ``is_model M ⇒
    ∀σ τ. type_valuation τ ∧ term_valuation τ σ ⇒ semantics σ τ FF False``,
  rw[FF_def] >>
  imp_res_tac is_model_is_set_theory >>
  rw[Once semantics_cases] >>
  qexists_tac`FEMPTY` >>
  simp[] >>
  Q.PAT_ABBREV_TAC`tm = FA X Y Z` >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >>
  simp[] >> strip_tac >>
  `tm has_type Bool` by (
    simp[Abbr`tm`,forall_has_type_bool] >>
    simp[Once has_type_cases]) >>
  `welltyped tm` by PROVE_TAC[welltyped_def] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[] >>
  conj_tac >- (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac ACONV_SYM >>
    imp_res_tac ACONV_VFREE_IN >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[Abbr`tm`,FA_def] >>
    PROVE_TAC[] ) >>
  qpat_assum`Bool = X`(assume_tac o SYM) >>
  conj_asm1_tac >- (
    simp[SUBSET_DEF,tyvars_def] >>
    rpt strip_tac >>
    imp_res_tac ACONV_tvars >>
    pop_assum(mp_tac o SYM) >>
    Q.PAT_ABBREV_TAC`fm = fresh_term X Y` >>
    simp[Abbr`tm`,FA_def,tvars_def,equation_def,tyvars_def,LIST_UNION_def] >>
    metis_tac[MEM] ) >>
  qsuff_tac`semantics FEMPTY τ tm False` >-
    metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  fs[] >>
  qmatch_assum_abbrev_tac`Abbrev(tm = FA x ty p)` >>
  `False = Boolean (∀mx. mx <: boolset ⇒ I mx = True)` by (
    simp[boolean_def] >> rw[] >>
    rfs[mem_boolset] ) >>
  pop_assum(SUBST1_TAC) >>
  qunabbrev_tac`tm` >>
  match_mp_tac (UNDISCH semantics_forall) >>
  simp[Abbr`ty`] >>
  simp[Once has_type_cases] >>
  simp[Once semantics_cases,FLOOKUP_UPDATE])

val falsity_has_type_bool = store_thm("falsity_has_type_bool",
  ``FF has_type Bool``,
  rw[FF_def] >> rw[Once has_type_cases])
val _ = export_rewrites["falsity_has_type_bool"]

val semantics_not = store_thm("semantics_not",
  ``is_model M ⇒
    ∀σ τ p mp.
      type_valuation τ ∧ term_valuation τ σ ∧
      p has_type Bool ∧
      semantics σ τ p mp
      ⇒ semantics σ τ (NO p) (Boolean (mp ≠ True))``,
  strip_tac >>
  imp_res_tac is_model_is_set_theory >>
  rw[NO_def] >>
  simp[Once semantics_cases] >>
  qexists_tac`Abstract boolset boolset (λm. Boolean (m ≠ True))` >>
  qexists_tac`mp` >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[WELLTYPED] >>
  conj_tac >- (
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    imp_res_tac semantics_typeset >>
    rfs[boolean_in_boolset] ) >>
  ntac 3 (pop_assum kall_tac) >>
  simp[Once semantics_cases] >>
  qexists_tac`FEMPTY` >>
  Q.PAT_ABBREV_TAC`tm = Abs X Y Z` >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >>
  simp[] >> strip_tac >>
  `tm has_type Fun Bool Bool` by (
    simp[Abbr`tm`] >>
    simp[Once has_type_cases,implication_has_type_bool] >>
    simp[Once has_type_cases]) >>
  `welltyped tm` by PROVE_TAC[welltyped_def] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[] >>
  conj_tac >- (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac ACONV_SYM >>
    imp_res_tac ACONV_VFREE_IN >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[Abbr`tm`,IM_def,FF_def] >>
    PROVE_TAC[] ) >>
  qpat_assum`Fun Bool Bool = X`(assume_tac o SYM) >>
  conj_asm1_tac >- (
    simp[SUBSET_DEF,tyvars_def] >>
    rpt strip_tac >>
    imp_res_tac ACONV_tvars >>
    pop_assum(mp_tac o SYM) >>
    Q.PAT_ABBREV_TAC`fm = fresh_term X Y` >>
    simp[Abbr`tm`,IM_def,tvars_def,tyvars_def,LIST_UNION_def,FF_def] >>
    metis_tac[MEM] ) >>
  qmatch_abbrev_tac`semantics x y z w` >>
  qsuff_tac`semantics x y tm w` >-
    metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  fs[Abbr`x`,Abbr`y`,Abbr`tm`] >>
  simp[Once semantics_cases] >>
  simp[Abbr`w`] >>
  qexists_tac`λm. Boolean (m ≠ True)` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[] >>
  conj_tac >- metis_tac[WELLTYPED] >>
  simp[boolean_in_boolset] >>
  qx_gen_tac`m`>>strip_tac >>
  `Boolean (m ≠ True) = Boolean (m = True ⇒ False = True)` by (
    simp[boolean_def] >>
    metis_tac[true_neq_false,mem_boolset] ) >>
  pop_assum(SUBST1_TAC) >>
  match_mp_tac (UNDISCH semantics_implication) >>
  simp[Once has_type_cases] >>
  conj_asm1_tac >- simp[term_valuation_FUPDATE] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  metis_tac[semantics_falsity])

val semantics_existential = store_thm("semantics_existential",
  ``is_model M ⇒
    ∀σ τ ty mty.
    type_valuation τ ∧
    term_valuation τ σ ∧
    typeset τ ty mty
    ⇒
    semantics σ τ ^(rand(rator(rhs(concl(SPEC_ALL EX_def)))))
      (Abstract (Funspace mty boolset) boolset
        (λp. Boolean (∃x. x <: mty ∧ p ' x = True)))``,
  rw[] >>
  imp_res_tac is_model_is_set_theory >>
  simp[Once semantics_cases] >>
  Q.PAT_ABBREV_TAC`tm:term = (Abs X Y Z)` >>
  qspecl_then[`{}`,`tm`]mp_tac fresh_term_def >> rw[] >>
  `tm has_type Fun (Fun (Tyvar "A") Bool) Bool` by (
    simp[Abbr`tm`] >>
    simp[Once has_type_cases] >>
    simp[forall_has_type_bool,implication_has_type_bool] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `welltyped tm` by metis_tac[WELLTYPED] >>
  imp_res_tac ACONV_welltyped >>
  imp_res_tac ACONV_TYPE >> pop_assum (assume_tac o SYM) >> rfs[] >>
  `closed tm` by (
    simp[Abbr`tm`,FA_def,IM_def] >>
    PROVE_TAC[] ) >>
  imp_res_tac ACONV_closed >>
  simp[tyvars_def] >>
  imp_res_tac ACONV_tvars >> pop_assum (assume_tac o SYM) >>
  `tvars tm = ["A"]` by (
    simp[Abbr`tm`,tvars_def,tyvars_def,FA_def,IM_def,LIST_UNION_def,LIST_INSERT_def] ) >>
  simp[] >>
  qexists_tac`FEMPTY|+("A",ty)`>>simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
  match_mp_tac (MP_CANON (CONJUNCT2 (UNDISCH semantics_simple_inst))) >>
  simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
  qexists_tac`FEMPTY` >>
  qexists_tac`τ|+("A",mty)` >>
  reverse conj_asm2_tac >- (
    conj_tac >- (
      simp[type_valuation_def] >>
      rw[] >- metis_tac[typeset_inhabited] >>
      pop_assum mp_tac >>
      qid_spec_tac`x` >>
      ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
      fs[type_valuation_def] ) >>
    simp[FLOOKUP_UPDATE] ) >>
  qmatch_abbrev_tac`semantics x y z w` >>
  qsuff_tac`semantics x y tm w` >- metis_tac[semantics_aconv,term_valuation_FEMPTY] >>
  fs[] >>
  qpat_assum`type_valuation y`mp_tac >>
  unabbrev_all_tac >>
  ntac 13 (pop_assum kall_tac) >>
  strip_tac >>
  simp[Once semantics_cases] >>
  qexists_tac`λp. Boolean (∃x. x <: mty ∧ p ' x = True)` >>
  qexists_tac`Funspace mty boolset` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[forall_has_type_bool,implication_has_type_bool] >>
  conj_tac >- (
    simp[Once semantics_cases] >>
    qexists_tac`mty` >> simp[] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_asm1_tac >- (
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] ) >>
  simp[boolean_in_boolset] >>
  qx_gen_tac`p` >> strip_tac >>
  match_mp_tac (UNDISCH semantics_forall_matchable) >>
  fs[implication_has_type_bool,forall_has_type_bool] >>
  Q.PAT_ABBREV_TAC`t1 = FA "x"  Y Z` >>
  Q.PAT_ABBREV_TAC`P = term_valuation X Y` >>
  `P` by (
    simp[Abbr`P`] >>
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >>
    simp[Once semantics_cases,PULL_EXISTS] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] ) >>
  qunabbrev_tac`P` >> simp[] >>
  qexists_tac`λmq. Boolean ((∀mx. mx <: mty ⇒ (p ' mx = True ⇒ mq = True)) ⇒ mq = True)` >>
  conj_tac >- (
    qx_gen_tac`mq` >> strip_tac >>
    match_mp_tac (UNDISCH semantics_implication_matchable) >>
    simp[Abbr`t1`,forall_has_type_bool,implication_has_type_bool,GSYM PULL_EXISTS] >>
    conj_asm1_tac >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] ) >>
    simp[PULL_EXISTS,CONJ_COMM] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    qexists_tac`Boolean (∀mx. mx <: mty ⇒ p ' mx = True ⇒ mq = True)` >>
    conj_tac >- ( simp[boolean_eq_true] ) >>
    match_mp_tac (UNDISCH semantics_forall_matchable) >>
    simp[implication_has_type_bool] >>
    simp[Once (CONJUNCT1 (SPEC_ALL semantics_cases)),FLOOKUP_UPDATE] >>
    qexists_tac`λmx. Boolean (p ' mx  = True ⇒ mq = True)` >>
    simp[boolean_eq_true] >>
    rw[] >>
    match_mp_tac (UNDISCH semantics_implication_matchable) >>
    simp[] >>
    simp[Once semantics_cases,PULL_EXISTS] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] >>
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >>
    simp[Once semantics_cases,FLOOKUP_UPDATE] ) >>
  simp[boolean_eq_true] >>
  simp[boolean_def] >>
  rw[true_neq_false] >>
  metis_tac[mem_boolset,apply_in_rng,true_neq_false])

val semantics_exists = store_thm("semantics_exists",
  ``is_model M ⇒
    ∀σ τ x ty mty p mp.
    p has_type Bool ∧
    (∀mx. mx <: mty ⇒ semantics (σ|+((x,ty),mx)) τ p (mp mx)) ∧
    type_valuation τ ∧
    term_valuation τ σ ∧
    typeset τ ty mty
    ⇒
    semantics σ τ (EX x ty p) (Boolean (∃mx. mx <: mty ∧ mp mx = True))``,
  rw[EX_def] >>
  imp_res_tac is_model_is_set_theory >>
  simp[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  simp[WELLTYPED] >>
  Q.PAT_ABBREV_TAC`bb = Boolean X` >>
  simp[Once semantics_cases,SimpR``$/\``] >>
  simp[PULL_EXISTS] >>
  qexists_tac`Abstract (Funspace mty boolset) boolset (λp. Boolean (∃x. x <: mty ∧ p ' x = True))` >>
  qexists_tac`mp` >>
  qexists_tac`mty` >>
  qexists_tac`boolset` >>
  qexists_tac`Bool` >>
  simp[] >>
  simp[CONJ_ASSOC] >>
  reverse conj_asm2_tac >- (
    rw[] >> res_tac >>
    imp_res_tac semantics_typeset >>
    rfs[] >>
    metis_tac[term_valuation_FUPDATE,SND,FST] ) >>
  conj_tac >- (
    simp[Abbr`bb`] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- (
      match_mp_tac ABSTRACT_IN_FUNSPACE >>
      simp[] ) >>
    simp[boolean_def] >>
    rw[true_neq_false] >> fs[] >>
    metis_tac[apply_abstract] ) >>
  match_mp_tac (UNDISCH semantics_existential) >>
  simp[])

val INFINITY_AX_correct = store_thm("INFINITY_AX_correct",
  ``is_model M ⇒
    [] |= EX "f" (Fun Ind Ind) (AN (O1 Ind Ind (Var "f" (Fun Ind Ind)))
                                   (NO (OT Ind Ind (Var "f" (Fun Ind Ind)))))``,
    cheat)

val soundness = store_thm("soundness",
  ``is_model M ⇒
    (∀ty. type_ok ty ⇒ type_has_meaning ty) ∧
    (∀tm. term_ok tm ⇒ has_meaning tm) ∧
    (∀h c. h |- c ⇒ h |= c)``,
  strip_tac >>
  ho_match_mp_tac proves_ind >>
  simp[] >>
  conj_tac >- (
    simp[type_has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_tac >- (
    rw[type_has_meaning_def] >>
    simp[Once semantics_cases] >>
    fs[tyvars_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[type_has_meaning_def] >>
    imp_res_tac is_model_is_set_theory >>
    Q.ISPEC_THEN`set (tyvars (Tyapp op args))`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >>
    disch_then(qspec_then`τ`mp_tac) >>
    disch_then(qx_choose_then`t`strip_assume_tac) >>
    first_x_assum(qspec_then`t`mp_tac) >>
    simp[] >> strip_tac >>
    qsuff_tac`∃m. typeset t ty m` >- metis_tac[typeset_reduce] >>
    pop_assum mp_tac >>
    simp[Once semantics_cases] >>
    rw[] >> fs[] >> TRY (metis_tac[]) >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    simp[has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    simp[type_has_meaning_def] >>
    rw[] >>
    imp_res_tac is_model_is_set_theory >>
    Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >>
    disch_then(qspec_then`FEMPTY`mp_tac) >>
    simp[] >>
    disch_then(qx_choose_then`τ`strip_assume_tac) >>
    map_every qexists_tac[`τ`,`FEMPTY`] >>
    simp[] ) >>
  conj_tac >- (
    simp[has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    simp[type_has_meaning_def] >>
    rw[] >>
    imp_res_tac is_model_is_set_theory >>
    Q.ISPEC_THEN`set (tyvars ty)`mp_tac (UNDISCH covering_type_valuation_exists) >>
    simp[] >>
    disch_then(qspec_then`FEMPTY`mp_tac) >>
    simp[] >>
    disch_then(qx_choose_then`τ`strip_assume_tac) >>
    map_every qexists_tac[`τ`,`FEMPTY`] >>
    simp[] ) >>
  conj_tac >- (
    metis_tac[has_meaning_type_has_meaning,has_meaning_welltyped,WELLTYPED_LEMMA] ) >>
  conj_tac >- (
    rw[sequent_def] >>
    fs[EVERY_MEM] ) >>
  conj_tac >- metis_tac[REFL_correct] >>
  conj_tac >- metis_tac[TRANS_correct] >>
  conj_tac >- metis_tac[MK_COMB_correct] >>
  conj_tac >- metis_tac[ABS_correct,NOT_EXISTS] >>
  conj_tac >- metis_tac[BETA_correct] >>
  conj_tac >- metis_tac[ASSUME_correct] >>
  conj_tac >- metis_tac[EQ_MP_correct] >>
  conj_tac >- metis_tac[DEDUCT_ANTISYM_correct] >>
  conj_tac >- metis_tac[INST_TYPE_correct] >>
  conj_tac >- metis_tac[INST_correct] >>
  conj_tac >- metis_tac[new_basic_definition_correct] >>
  conj_tac >- metis_tac[new_basic_type_definition_correct] >>
  conj_tac >- metis_tac[new_basic_type_definition_correct] >>
  conj_tac >- (
    rpt strip_tac >>
    match_mp_tac (UNDISCH ETA_AX_correct) >>
    imp_res_tac is_model_is_set_theory >>
    simp[type_has_meaning_Fun] >> disj2_tac >>
    spose_not_then strip_assume_tac >>
    `type_size (Fun ty ty') = type_size ty` by metis_tac[] >>
    fsrw_tac[ARITH_ss][term_size_def]) >>
  metis_tac[INFINITY_AX_correct,SELECT_AX_correct])

val consistency = store_thm("consistency",
  ``is_model M ⇒
    ([] |- (Var x Bool === Var x Bool)) ∧
    (¬([] |- (Var x Bool === Var (VARIANT (Var x Bool) x Bool) Bool)))``,
  strip_tac >>
  conj_tac >- (
    simp[Once proves_cases] >>
    disj1_tac >>
    qexists_tac`Var x Bool` >>
    simp[] >>
    simp[Once proves_cases] >>
    disj1_tac >>
    simp[Once proves_cases] ) >>
  spose_not_then strip_assume_tac >>
  imp_res_tac soundness >>
  pop_assum mp_tac >>
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL,equation_has_meaning_iff] >>
  qmatch_assum_abbrev_tac`[] |- Var x Bool === Var y Bool` >>
  map_every qexists_tac[`FEMPTY|+((x,Bool),True)|+((y,Bool),False)`,`FEMPTY`] >>
  simp[] >>
  imp_res_tac is_model_is_set_theory >>
  conj_asm1_tac >- (
    conj_tac >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[mem_boolset] >>
      match_mp_tac term_valuation_FUPDATE >>
      simp[mem_boolset] ) >>
    match_mp_tac(MP_CANON(GEN_ALL(DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH_ALL closes_equation))))))>>
    simp[] >>
    qexists_tac`Bool`>>simp[tyvars_def] >>
    simp[Once has_type_cases] >>
    simp[Once has_type_cases] ) >>
  strip_tac >>
  imp_res_tac (UNDISCH semantics_equation_imp) >>
  rfs[] >>
  ntac 2 (pop_assum mp_tac) >>
  simp[Once semantics_cases,FLOOKUP_UPDATE] >>
  simp[Once semantics_cases,FLOOKUP_UPDATE] >>
  `x ≠ y` by (
    simp[Abbr`y`] >>
    metis_tac[VARIANT_THM,VFREE_IN_def] ) >>
  simp[] >>
  rfs[boolean_eq_true] >>
  metis_tac[true_neq_false])

val _ = export_theory()
