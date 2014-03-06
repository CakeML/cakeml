open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory finite_mapTheory
open miscTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemanticsExtra"

val mem = ``mem:'U->'U->bool``

val is_std_interpretation_is_type = store_thm("is_std_interpretation_is_type",
  ``is_std_interpretation i ⇒ is_std_type_assignment (FST i)``,
  Cases_on`i` >> simp[is_std_interpretation_def])

val typesem_inhabited = store_thm("typesem_inhabited",
  ``is_set_theory ^mem ⇒
    ∀tyenv τ δ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ
    ⇒
    (inhabited (typesem τ δ ty) ⇔ type_ok tyenv ty)``,
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def] >>
  rw[FLOOKUP_DEF] >>
  Cases_on`name ∈ FDOM tyenv`>> simp[mem_empty] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then(qspec_then`MAP (typesem τ δ) args`mp_tac) >>
  simp_tac(srw_ss()++ETA_ss)[EVERY_MAP] >>
  simp[EVERY_MEM] >> metis_tac[])

val typesem_Fun = store_thm("typesem_Fun",
  ``∀τ δ dom rng.
    is_std_type_assignment δ ⇒
    typesem τ δ (Fun dom rng) =
    Funspace (typesem τ δ dom) (typesem τ δ rng)``,
  rw[is_std_type_assignment_def,typesem_def])

val termsem_clauses = store_thm("termsem_clauses",
  ``(∀v i x ty. termsem v i (Var x ty) = (SND v) (x,ty)) ∧
    (∀v i name ty. termsem v i (Const name ty) = (SND i) name ty (FST v)) ∧
    (∀v i t1 t2. termsem v i (Comb t1 t2) = termsem v i t1 ' (termsem v i t2)) ∧
    (∀v i x ty b. termsem v i (Abs x ty b) =
      Abstract (typesem (FST v) (FST i) ty) (typesem (FST v) (FST i) (typeof b))
        (λm. termsem (FST v, ((x,ty) =+ m) (SND v)) i b))``,
  rpt conj_tac >> Cases >> Cases >> rw[termsem_def])

val termsem_niceind = store_thm("termsem_niceind",
  ``∀P.
    ((∀v i x ty. P v i (Var x ty)) ∧
     (∀v i name ty. P v i (Const name ty)) ∧
     (∀v i t1 t2. P v i t1 ∧ P v i t2 ⇒ P v i (Comb t1 t2)) ∧
     (∀v i x ty b. (∀m. P (FST v, ((x,ty) =+ m) (SND v)) i b) ⇒
                   P v i (Abs x ty b)))
    ⇒ ∀v i t. P (v:'U valuation) (i:'U interpretation) t``,
  rw[] >>
  Q.ISPEC_THEN`λ(^mem) (v1,v2) i t. P (v1,v2) i t`mp_tac termsem_ind >>
  Cases_on`v`>> simp[])

val termsem_typesem = store_thm("termsem_typesem",
  ``is_set_theory ^mem ⇒
    ∀sig v i tm.
      is_valuation (FST i) v ∧
      is_interpretation sig i ∧
      is_std_type_assignment (FST i) ∧
      term_ok sig tm
      ⇒
      termsem v i tm <: typesem (FST v) (FST i) (typeof tm)``,
  strip_tac >> gen_tac >>
  ho_match_mp_tac termsem_niceind >> Cases_on`sig` >>
  strip_tac >- (
    Cases >> Cases >>
    simp[termsem_clauses,is_valuation_def,is_term_valuation_def
        ,is_interpretation_def,term_ok_def] >>
    rw[] >> metis_tac[typesem_inhabited] ) >>
  strip_tac >- (
    Cases >> Cases >>
    simp[termsem_clauses,is_valuation_def,is_interpretation_def
        ,is_term_assignment_def,FEVERY_ALL_FLOOKUP,term_ok_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    Cases >>
    simp[termsem_clauses,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  Cases >> Cases >>
  simp[termsem_clauses,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  first_x_assum match_mp_tac >>
  fs[is_valuation_def,is_term_valuation_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val Equalsem =
  is_std_interpretation_def
  |> SPEC_VAR |> snd
  |> Q.SPECL [`FST (i:'U interpretation)`,`SND i`]
  |> concl |> rhs
  |> strip_conj |> tl |> hd
  |> strip_forall |> snd |> rhs
  |> C (curry mk_comb) ``FST(v:'U valuation)``
  |> beta_conv

val termsem_Equal = store_thm("termsem_Equal",
  ``∀v i ty.
      is_std_interpretation i ⇒
      termsem v i (Equal ty) = ^Equalsem``,
  Cases >> Cases >>
  rw[is_std_interpretation_def,termsem_clauses])

val term_ok_equation = store_thm("term_ok_equation",
  ``is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        welltyped t ∧ welltyped s ∧
        typeof t = typeof s ∧
        type_ok (FST sig) (typeof s))``,
  Cases_on`sig` >> rw[equation_def,term_ok_def,type_ok_def,is_std_sig_def] >>
  rw[EQ_IMP_THM] >>
  qexists_tac`[(typeof s,Tyvar "A")]` >>
  rw[holSyntaxLibTheory.REV_ASSOCD_def])

val termsem_equation = store_thm("termsem_equation",
  ``is_set_theory ^mem ⇒
    ∀sig v i s t.
    is_structure sig v i ∧
    term_ok sig (s === t)
    ⇒ termsem v i (s === t) = Boolean (termsem v i s = termsem v i t)``,
  rw[is_structure_def] >> rfs[term_ok_equation] >>
  simp[equation_def,termsem_clauses,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    TRY (conj_tac >- metis_tac[termsem_typesem]) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset] ) >>
  unabbrev_all_tac >> simp[])

val _ = export_theory()
