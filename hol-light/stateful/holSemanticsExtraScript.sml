open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory finite_mapTheory alistTheory pairTheory pred_setTheory
open miscLib miscTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemanticsExtra"

val mem = ``mem:'U->'U->bool``

val is_std_interpretation_is_type = store_thm("is_std_interpretation_is_type",
  ``is_std_interpretation i ⇒ is_std_type_assignment (FST i)``,
  Cases_on`i` >> simp[is_std_interpretation_def])

(* typesem *)

val typesem_inhabited = store_thm("typesem_inhabited",
  ``is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)``,
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def,FLOOKUP_DEF] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then match_mp_tac >>
  simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[])

val typesem_Fun = store_thm("typesem_Fun",
  ``∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)``,
  rw[is_std_type_assignment_def,typesem_def])

val typesem_Bool = store_thm("typesem_Bool",
  ``∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset``,
  rw[is_std_type_assignment_def,typesem_def])

val typesem_TYPE_SUBST = store_thm("typesem_TYPE_SUBST",
  ``∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty``,
  ho_match_mp_tac TYPE_SUBST_ind >> simp[typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >>
  simp[MAP_MAP_o,MAP_EQ_f])

val typesem_tyvars = store_thm("typesem_tyvars",
  ``∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty``,
  ho_match_mp_tac typesem_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >> rw[MAP_EQ_f] >>
  metis_tac[])

(* termsem *)

val termsem_typesem = store_thm("termsem_typesem",
  ``is_set_theory ^mem ⇒
    ∀sig i tm v δ τ.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm
      ⇒
      termsem sig i v tm <: typesem δ τ (typeof tm)``,
  strip_tac >> ntac 2 Cases >> Induct
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_term_valuation_def,term_ok_def] )
  >- (
    Cases_on`v`>>
    simp[termsem_def,term_ok_def] >> rw[] >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: X` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    rw[Abbr`ty`,Abbr`ii`,Abbr`sig`] >>
    simp[Once typesem_TYPE_SUBST,Abbr`X`,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`X <: typesem δ τi ty0` >>
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    first_x_assum (qspecl_then[`name`,`ty0`]mp_tac) >>
    simp[] >> disch_then(qspec_then`λx. if MEM x (tyvars ty0) then τi x else boolset`mp_tac) >>
    simp[Abbr`X`,Abbr`τi`] >>
    discharge_hyps >- (
      fs[is_type_valuation_def] >>
      reverse(rw[])>-metis_tac[mem_boolset]>>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[is_valuation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`a <: b ⇒ a' <: b'` >>
    `a' = a` by (
      unabbrev_all_tac >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] ) >>
    `b' = b` by (
      unabbrev_all_tac >>
      match_mp_tac typesem_tyvars >> rw[] ) >>
    rw[] )
  >- (
    simp[termsem_def,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    metis_tac[]) >>
  simp[termsem_def,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  first_x_assum (qspec_then`vv`mp_tac) >>
  simp[Abbr`vv`] >> disch_then match_mp_tac >>
  Cases_on`v`>> fs[is_valuation_def,is_term_valuation_def] >>
  rw[combinTheory.APPLY_UPDATE_THM] >> rw[])

val Equalsem =
  is_std_interpretation_def
  |> SPEC_ALL |> concl |> rhs
  |> strip_conj |> last
  |> strip_comb |> snd |> last

val termsem_Equal = store_thm("termsem_Equal",
  ``is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem Γ i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]``,
  rw[termsem_def,LET_THM] >> fs[is_structure_def] >>
  qspecl_then[`Γ`,`i`,`"="`]mp_tac instance_def >> fs[is_std_sig_def]>>
  disch_then(qspec_then`[(ty,Tyvar"A")]`mp_tac)>>
  simp[REV_ASSOCD] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`aa = tyvars X` >>
  `aa = ["A"]` by simp[tyvars_def,Abbr`aa`,LIST_UNION_def,LIST_INSERT_def] >>
  Q.PAT_ABBREV_TAC`tt = typesem (tyaof i) Y o TYPE_SUBST Z o Tyvar` >>
  `is_type_valuation tt` by (
    simp[Abbr`tt`,is_type_valuation_def] >>
    rw[REV_ASSOCD,typesem_def] >- (
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_valuation_def,is_interpretation_def] >>
      metis_tac[] ) >>
    fs[is_valuation_def,is_type_valuation_def] ) >>
  qunabbrev_tac`aa` >>
  fs[is_std_interpretation_def,interprets_def] >>
  `STRING_SORT ["A"] = ["A"]` by simp[STRING_SORT_def,INORDER_INSERT_def] >>
  simp[] >> simp[Abbr`tt`,REV_ASSOCD])

(* equations *)

val termsem_equation = store_thm("termsem_equation",
  ``is_set_theory ^mem ⇒
    ∀sig i v s t.
    is_structure sig i v ∧
    term_ok sig (s === t)
    ⇒ termsem sig i v (s === t) = Boolean (termsem sig i v s = termsem sig i v t)``,
  rw[] >>
  `is_std_sig sig ∧ is_std_interpretation i` by fs[is_structure_def] >>
  fs[term_ok_equation] >>
  imp_res_tac term_ok_type_ok >>
  simp[equation_def,termsem_def,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[is_structure_def,termsem_typesem] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset,is_structure_def] ) >>
  unabbrev_all_tac >> simp[])

(* aconv *)

val termsem_raconv = store_thm("termsem_raconv",
  ``∀env tp. RACONV env tp ⇒
      ∀Γ i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem Γ i v1 (Var x1 ty1) =
             termsem Γ i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp)``,
  ho_match_mp_tac RACONV_strongind >>
  rpt conj_tac >> simp[termsem_def] >>
  TRY (metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`RACONV env1 p1` >>
  qspecl_then[`env1`,`p1`]mp_tac RACONV_TYPE >>
  simp[Abbr`env1`,Abbr`p1`] >> strip_tac >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[ALPHAVARS_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> fs[])

val termsem_aconv = store_thm("termsem_aconv",
  ``∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ⇒ termsem Γ i v t1 = termsem Γ i v t2``,
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_welltyped,ACONV_def])

(* semantics only depends on valuation of free variables *)

val termsem_frees = store_thm("termsem_frees",
  ``∀Γ i t v1 v2.
      FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t``,
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[])

val typesem_frees = store_thm("typesem_frees",
  ``∀ty τ1 τ2 δ.
      (∀a. MEM a (tyvars ty) ⇒ τ1 a = τ2 a) ⇒
      typesem δ τ1 ty = typesem δ τ2 ty``,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def,PULL_EXISTS] >>
  rw[] >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
  fs[EVERY_MEM] >> metis_tac[])

val termsem_tyfrees = store_thm("termsem_tyfrees",
  ``∀Γ i t v1 v2.
      term_ok Γ t ∧
      SND v1 = SND v2 ∧
      (∀a. MEM a (tvars t) ⇒ FST v1 a = FST v2 a)
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t``,
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def,tvars_def,term_ok_def] >- (
    rw[] >>
    qmatch_abbrev_tac`instance Γ i name ty τ = X` >>
    qspecl_then[`Γ`,`i`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`ty`] >> disch_then kall_tac >>
    rpt AP_TERM_TAC >> simp[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    match_mp_tac typesem_frees >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[tyvars_TYPE_SUBST] >>
    metis_tac[] ) >>
  rw[] >- PROVE_TAC[] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[]  >>
    match_mp_tac typesem_tyvars >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF,term_ok_welltyped,WELLTYPED] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM])

(* TODO: move. List of updates to a function *)

val UPDATE_LIST_def = Define`
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`
val _ = Parse.add_infix("=++",500,Parse.LEFT)
val _ = Parse.overload_on("=++",``UPDATE_LIST``)

val UPDATE_LIST_THM = store_thm("UPDATE_LIST_THM",
  ``∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)``,
  rw[UPDATE_LIST_def,pairTheory.UNCURRY])

val APPLY_UPDATE_LIST_ALOOKUP = store_thm("APPLY_UPDATE_LIST_ALOOKUP",
  ``∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y``,
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> BasicProvers.CASE_TAC)

val ALOOKUP_FILTER = store_thm("ALOOKUP_FILTER",
  ``∀ls x. ALOOKUP (FILTER (λ(k,v). P k) ls) x =
           if P x then ALOOKUP ls x else NONE``,
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> fs[] >> metis_tac[])

val ALOOKUP_MAP_dest_var = store_thm("ALOOKUP_MAP_dest_var",
  ``∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))``,
  Induct >> simp[] >> Cases >> simp[EVERY_MEM,EVERY_MAP] >>
  rw[] >> fs[])

(* semantics of substitution *)

val termsem_simple_subst = store_thm("termsem_simple_subst",
  ``∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀Γ i v.
        termsem Γ i v (simple_subst ilist tm) =
        termsem Γ i
          (FST v, SND v =++
                  MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist))
          tm``,
  Induct >> simp[termsem_def] >- (
    simp[REV_ASSOCD_ALOOKUP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> rw[termsem_def] >- (
      imp_res_tac ALOOKUP_FAILS >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >> metis_tac[] ) >>
    rw[GSYM MAP_MAP_o] >>
    qmatch_assum_abbrev_tac`ALOOKUP ls (Var s ty) = SOME x` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[]) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`il = FILTER X ilist` >>
  `simple_subst il tm has_type typeof tm` by (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    imp_res_tac WELLTYPED >>
    fs[Abbr`il`,EVERY_MEM,EVERY_FILTER,FORALL_PROD] >>
    rw[] >> res_tac >> rw[] ) >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM] >> rw[] >>
  qmatch_abbrev_tac `termsem Γ i vv xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`Γ`,`i`,`vv`]mp_tac) >>
  rw[Abbr`vv`,Abbr`yy`] >>
  rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
  simp[FUN_EQ_THM,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  Cases >>
  simp[GSYM MAP_MAP_o] >>
  BasicProvers.CASE_TAC >>
  qmatch_assum_abbrev_tac`ALOOKUP (MAP (dest_var ## f) ls) (z,ty) = X` >>
  qunabbrev_tac`X` >>
  Q.ISPECL_THEN[`ls`,`f`,`z`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
  (discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`,Abbr`il`,MEM_FILTER] >> metis_tac[])) >>
  qmatch_assum_abbrev_tac`Abbrev(il = FILTER P ilist)` >>
  qmatch_assum_abbrev_tac`Abbrev(ls = MAP sw il)` >>
  `ls = FILTER (P o sw) (MAP sw ilist)` by (
    simp[Abbr`ls`,Abbr`il`] >>
    simp[rich_listTheory.FILTER_MAP] >>
    simp[Abbr`P`,Abbr`sw`,combinTheory.o_DEF,UNCURRY,LAMBDA_PROD] ) >>
  qunabbrev_tac`ls` >>
  simp[ALOOKUP_FILTER,Abbr`P`,Abbr`sw`,combinTheory.o_DEF,LAMBDA_PROD] >- (
    rw[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
    qmatch_assum_abbrev_tac`P ⇒ ALOOKUP ls vv = NONE` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
  (discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[])

val termsem_VSUBST = store_thm("termsem_VSUBST",
  `` ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm``,
  rw[] >>
  Q.ISPECL_THEN[`{y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` by (
    match_mp_tac ACONV_VSUBST >> metis_tac[] ) >>
  `welltyped (VSUBST ilist tm)` by metis_tac[VSUBST_WELLTYPED] >>
  `termsem Γ i v (VSUBST ilist tm) = termsem Γ i v (VSUBST ilist fm)` by
    metis_tac[termsem_aconv] >>
  `VSUBST ilist fm = simple_subst ilist fm` by
    metis_tac[VSUBST_simple_subst] >>
  rw[] >>
  `welltyped fm` by metis_tac[ACONV_welltyped] >>
  metis_tac[termsem_simple_subst,termsem_aconv])

(* semantics of instantiation *)

val termsem_simple_inst = store_thm("termsem_simple_inst",
  ``∀Γ tm tyin.
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
      ⇒
      ∀i v.
        termsem Γ i v (simple_inst tyin tm) =
        termsem Γ i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm``,
  Cases >> Induct >> simp[termsem_def,term_ok_def] >- (
    rw[] >> rw[TYPE_SUBST_compose] >>
    qmatch_abbrev_tac`instance sig int name (TYPE_SUBST i2 ty0) t1 =
                      instance sig int name (TYPE_SUBST i1 ty0) t2` >>
    qspecl_then[`sig`,`int`,`name`]mp_tac instance_def >> simp[Abbr`sig`] >>
    disch_then kall_tac >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    rw[Once REV_ASSOCD_ALOOKUP,Abbr`i2`,ALOOKUP_APPEND,MAP_MAP_o,swap_ff] >>
    rw[ff_def,GSYM MAP_MAP_o,ALOOKUP_MAP] >>
    rw[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >> fs[typesem_def] >>
    rw[Once typesem_TYPE_SUBST,REV_ASSOCD_ALOOKUP] )
  >- (
    rw[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    metis_tac[] ) >>
  rw[] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d2 = d1` by (
    unabbrev_all_tac >>
    simp[Once typesem_TYPE_SUBST] ) >>
  `r2 = r1` by (
    unabbrev_all_tac >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    simp[Once typesem_TYPE_SUBST] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM] >>
  first_x_assum(qspec_then`tyin`mp_tac) >>
  discharge_hyps >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac termsem_frees >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[])

val termsem_INST = store_thm("termsem_INST",
  ``∀Γ tm tyin.
      welltyped tm ∧ term_ok Γ tm ⇒
      ∀i v.
        termsem Γ i v (INST tyin tm) =
        termsem Γ i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm``,
  rw[] >>
  Q.ISPECL_THEN[`{x | ∃ty. VFREE_IN (Var x ty) tm}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (INST tyin tm) (INST tyin fm)` by (
    match_mp_tac ACONV_INST >> metis_tac[] ) >>
  `welltyped (INST tyin tm)` by metis_tac[INST_WELLTYPED] >>
  `termsem Γ i v (INST tyin tm) = termsem Γ i v (INST tyin fm)` by
    metis_tac[termsem_aconv] >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm} = {x | ∃ty. VFREE_IN (Var x ty) fm}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `INST tyin fm = simple_inst tyin fm` by
    metis_tac[INST_simple_inst] >>
  rw[] >>
  `welltyped fm` by metis_tac[ACONV_welltyped] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv])

(* extending the context doesn't change the semantics *)

val termsem_extend = store_thm("termsem_extend",
  ``∀tyenv tmenv tyenv' tmenv' tm.
      tmenv ⊑ tmenv' ∧
      term_ok (tyenv,tmenv) tm ⇒
      ∀i v. termsem (tyenv',tmenv') i v tm =
            termsem (tyenv,tmenv) i v tm``,
  ntac 4 gen_tac >> Induct >> simp[termsem_def,term_ok_def] >>
  rw[] >>
  qmatch_abbrev_tac`X = instance sig int name ty t` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  fs[Abbr`sig`,Abbr`ty`,Abbr`X`] >>
  disch_then kall_tac >>
  qmatch_abbrev_tac`instance sig int name ty t = X` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  imp_res_tac FLOOKUP_SUBMAP >>
  fs[Abbr`sig`,Abbr`ty`])

val is_valuation_reduce = store_thm("is_valuation_reduce",
  ``∀tyenv tyenv' δ v. tyenv ⊑ tyenv' ∧ is_valuation tyenv' δ v ⇒
    is_valuation tyenv δ v``,
  rw[is_valuation_def,is_term_valuation_def] >>
  metis_tac[type_ok_extend])

val satisfies_extend = store_thm("satisfies_extend",
  ``∀tyenv tmenv tyenv' tmenv' tm i h c.
      tmenv ⊑ tmenv' ∧ tyenv ⊑ tyenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      i satisfies ((tyenv,tmenv),h,c) ⇒
      i satisfies ((tyenv',tmenv'),h,c)``,
  rw[satisfies_def] >> fs[EVERY_MEM] >>
  metis_tac[term_ok_extend,termsem_extend,is_valuation_reduce])

(* semantics only depends on interpretation of things in the term *)

val typesem_consts = store_thm("typesem_consts",
  ``∀ty τ δ δ' tyenv. type_ok tyenv ty ∧ (∀name args. type_ok tyenv (Tyapp name args) ⇒ δ' name = δ name) ⇒
                    typesem δ' τ ty = typesem δ τ ty``,
  ho_match_mp_tac type_ind >> simp[typesem_def,type_ok_def] >> rw[] >>
  qmatch_abbrev_tac`δ' name args1 = δ name args2` >>
  `args1 = args2` by (
    unabbrev_all_tac >>
    simp[MAP_EQ_f] >>
    fs[EVERY_MEM] >>
    metis_tac[] ) >>
  simp[] >> AP_THM_TAC >>
  first_x_assum match_mp_tac >>
  metis_tac[])

val termsem_consts = store_thm("termsem_consts",
  ``∀tm Γ i v i'.
      is_std_sig Γ ∧ term_ok Γ tm ∧
      (∀name args. type_ok (tysof Γ) (Tyapp name args) ⇒ tyaof i' name = tyaof i name) ∧
      (∀name ty. term_ok Γ (Const name ty) ⇒ tmaof i' name = tmaof i name)
      ⇒
      termsem Γ i' v tm = termsem Γ i v tm``,
  Induct >> simp[termsem_def] >- (
    rw[term_ok_def] >>
    imp_res_tac instance_def >>
    qmatch_abbrev_tac`instance Γ i' s ty τ = X` >>
    qmatch_assum_abbrev_tac`Abbrev(ty = TYPE_SUBST tyin ty0)` >>
    first_x_assum(qspecl_then[`tyin`,`ty`]mp_tac) >>
    simp[Abbr`ty`] >> disch_then kall_tac >>
    qmatch_abbrev_tac`f1 x1 = f2 x2` >>
    `x1 = x2` by (
      unabbrev_all_tac >>
      simp[FUN_EQ_THM,MAP_EQ_f] >>
      rw[] >>
      match_mp_tac typesem_consts >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[] >> metis_tac[] ) >>
    simp[] >> AP_THM_TAC >>
    unabbrev_all_tac >>
    metis_tac[]) >>
  fs[term_ok_def] >- metis_tac[] >>
  rw[term_ok_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[] >>
    match_mp_tac typesem_consts >>
    metis_tac[term_ok_type_ok] ) >>
  simp[] >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM] >>
  unabbrev_all_tac >> fs[] >>
  metis_tac[])

val satisfies_consts = store_thm("satisfies_consts",
  ``∀i i' sig h c.
    is_std_sig sig ∧
    EVERY (term_ok sig) (c::h) ∧
    (∀name args. type_ok (tysof sig) (Tyapp name args) ⇒ tyaof i' name = tyaof i name) ∧
    (∀name ty. term_ok sig (Const name ty) ⇒ tmaof i' name = tmaof i name) ∧
    i satisfies (sig,h,c)
    ⇒
    i' satisfies (sig,h,c)``,
  rw[satisfies_def] >>
  qsuff_tac`termsem sig i v c = True` >- metis_tac[termsem_consts] >>
  first_x_assum match_mp_tac >>
  reverse conj_tac >- ( fs[EVERY_MEM] >> metis_tac[termsem_consts] ) >>
  fs[is_valuation_def] >>
  fs[is_term_valuation_def] >>
  metis_tac[typesem_consts])

(* valuations exist *)

val term_valuation_exists = store_thm("term_valuation_exists",
  ``is_set_theory ^mem ⇒
    ∀tyenv δ τ. is_type_valuation τ ∧ is_type_assignment tyenv δ ⇒
      ∃σ. is_valuation tyenv δ (τ,σ)``,
  rw[is_valuation_def,is_term_valuation_def] >>
  qexists_tac`λ(x,ty). @v. v <: typesem δ τ ty` >> rw[] >>
  metis_tac[typesem_inhabited])

val valuation_exists = store_thm("valuation_exists",
  ``is_set_theory ^mem ⇒
    ∀tyenv δ. is_type_assignment tyenv δ ⇒
      ∃v. is_valuation tyenv δ v``,
  rw[is_valuation_def] >>
  qexists_tac`K boolset, λ(x,ty). @v. v <: typesem δ (K boolset) ty` >>
  conj_asm1_tac >- (simp[is_type_valuation_def] >> metis_tac[boolean_in_boolset]) >>
  fs[is_term_valuation_def] >> metis_tac[typesem_inhabited])

(* identity instance *)

val identity_instance = store_thm("identity_instance",
  ``∀sig (i:'U interpretation) name ty τ. FLOOKUP (tmsof sig) name = SOME ty ⇒
      instance sig i name ty = λτ. tmaof i name (MAP τ (STRING_SORT (tyvars ty)))``,
  rw[] >>
  qspecl_then[`sig`,`i`,`name`,`ty`,`ty`,`[]`]mp_tac instance_def >>
  rw[FUN_EQ_THM,typesem_def,combinTheory.o_DEF,ETA_AX])

(*
(* for models, reducing the context *)

val is_type_assignment_reduce = store_thm("is_type_assignment_reduce",
  ``∀tyenv tyenv' δ.
     tyenv ⊑ tyenv' ∧
     is_type_assignment tyenv' δ ⇒
     is_type_assignment tyenv δ``,
  rw[is_type_assignment_def] >>
  imp_res_tac FEVERY_SUBMAP)

val is_term_assignment_reduce = store_thm("is_term_assignment_reduce",
  ``∀tmenv tmenv' δ γ.
     tmenv ⊑ tmenv' ∧
     is_term_assignment tmenv' δ γ ⇒
     is_term_assignment tmenv δ γ``,
   rw[is_term_assignment_def] >>
   imp_res_tac FEVERY_SUBMAP)

val is_interpretation_reduce = store_thm("is_interpretation_reduce",
  ``∀i tyenv tmenv tyenv' tmenv'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
     is_interpretation (tyenv',tmenv') i ⇒
     is_interpretation (tyenv,tmenv) i``,
  Cases >> rw[is_interpretation_def] >>
  imp_res_tac is_type_assignment_reduce >>
  imp_res_tac is_term_assignment_reduce)

val models_reduce = store_thm("models_reduce",
  ``∀i tyenv tmenv axs tyenv' tmenv' axs'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧ (axs ⊆ axs') ∧
     i models ((tyenv',tmenv'),axs') ∧
     (∀p. p ∈ axs ⇒ (term_ok (tyenv,tmenv)) p)
     ⇒
     i models ((tyenv,tmenv),axs)``,
  Cases >> rw[models_def] >>
  imp_res_tac is_interpretation_reduce >>
  fs[SUBSET_DEF] >> metis_tac[satisfies_extend,EVERY_DEF])
*)

val _ = export_theory()
