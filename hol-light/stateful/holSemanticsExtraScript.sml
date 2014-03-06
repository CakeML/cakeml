open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory finite_mapTheory
open miscTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemanticsExtra"

val mem = ``mem:'U->'U->bool``

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

val termsem_typesem = store_thm("termsem_typesem",
  ``is_set_theory ^mem ⇒
    ∀sig τ σ i tm.
      is_type_valuation τ ∧
      is_type_assignment (FST sig) (FST i) ∧
      is_term_valuation τ (FST i) σ ∧
      is_term_assignment (SND sig) (FST i) (SND i) ∧
      is_std_type_assignment (FST i) ∧
      term_ok sig tm
      ⇒
      termsem τ σ i tm <: typesem τ (FST i) (typeof tm)``,
  simp[PULL_FORALL] >> gen_tac >> Q.ID_SPEC_TAC`mem` >>
  ho_match_mp_tac termsem_ind >> Cases_on`sig` >>
  strip_tac >- (
    simp[termsem_def,is_term_valuation_def,term_ok_def] >>
    rw[] >> metis_tac[typesem_inhabited] ) >>
  strip_tac >- (
    simp[termsem_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,term_ok_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[termsem_def,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  simp[termsem_def,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  first_x_assum match_mp_tac >>
  fs[is_term_valuation_def] >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val Equalsem =
  is_std_interpretation_def
  |> SPEC_VAR |> snd
  |> Q.SPECL [`FST (i:'U interp)`,`SND i`]
  |> concl |> rhs
  |> strip_conj |> tl |> hd
  |> strip_forall |> snd |> rhs
  |> dest_abs |> snd

val termsem_Equal = store_thm("termsem_Equal",
  ``∀τ σ i ty.
      is_std_interpretation i ⇒
      termsem τ σ i (Equal ty) = ^Equalsem``,
  Cases_on`i` >>
  rw[is_std_interpretation_def,termsem_def])

(*
val tac =
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    TRY (conj_tac >-
    termsem_typesem
    metis_tac[semantics_typeset,semantics_11]) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    metis_tac[semantics_typeset,WELLTYPED,boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[semantics_typeset,semantics_11,boolean_in_boolset] ) >>
  unabbrev_all_tac >> simp[]

val termsem_equation = store_thm("termsem_equation",
  ``is_set_theory ^mem ⇒
    ∀sig τ σ i s t mst.
    is_type_valuation τ ∧
    is_term_valuation τ (FST i) σ ∧
    is_interpretation sig i ∧
    typeof s = typeof t ∧
    mst = Boolean (termsem τ σ i s = termsem τ σ i t)
    ⇒ termsem τ σ i (s === t) = mst``,
  rw[equation_def] >>
  simp[termsem_def,termsem_Equal] >>
*)

val _ = export_theory()
