open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory finite_mapTheory
open miscTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemanticsExtra"

val mem = ``mem:'U->'U->bool``

val is_std_interpretation_is_type = store_thm("is_std_interpretation_is_type",
  ``is_std_interpretation i ⇒ is_std_type_assignment (FST i)``,
  Cases_on`i` >> simp[is_std_interpretation_def])

(* typesem *)

val typesem_inhabited = store_thm("typesem_inhabited",
  ``is_set_theory ^mem ⇒
    ∀tyenv δ ty τ.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ ty τ)``,
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def,FLOOKUP_DEF] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then match_mp_tac >>
  simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[])

val typesem_Fun = store_thm("typesem_Fun",
  ``∀δ dom rng τ.
    is_std_type_assignment δ ⇒
    typesem δ (Fun dom rng) τ =
    Funspace (typesem δ dom τ) (typesem δ rng τ)``,
  rw[is_std_type_assignment_def,typesem_def])

val typesem_Bool = store_thm("typesem_Bool",
  ``∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ Bool τ = boolset``,
  rw[is_std_type_assignment_def,typesem_def])

(* termsem *)

val termsem_clauses = store_thm("termsem_clauses",
  ``(∀i x ty. termsem i (Var x ty) = λσ. σ (x,ty)) ∧
    (∀i name ty. termsem i (Const name ty) = λσ. (SND i) name ty) ∧
    (∀i t1 t2. termsem i (Comb t1 t2) = λσ τ. termsem i t1 σ τ ' (termsem i t2 σ τ)) ∧
    (∀i x ty b. termsem i (Abs x ty b) = λσ τ.
      Abstract (typesem (FST i) ty τ) (typesem (FST i) (typeof b) τ)
        (λm. termsem i b (((x,ty) =+ (K m)) σ) τ))``,
  rpt conj_tac >> Cases >> rw[FUN_EQ_THM,termsem_def])

val termsem_typesem = store_thm("termsem_typesem",
  ``is_set_theory ^mem ⇒
    ∀sig i tm σ τ.
      is_type_valuation τ ∧
      (∀v ty. σ (v,ty) τ <: typesem (FST i) ty τ) ∧
      is_interpretation sig i ∧
      is_std_type_assignment (FST i) ∧
      term_ok sig tm
      ⇒
      termsem i tm σ τ <: typesem (FST i) (typeof tm) τ``,
  strip_tac >> Cases >> Cases >> Induct
  >- (
    simp[termsem_clauses,is_interpretation_def,term_ok_def] )
  >- (
    simp[termsem_clauses,is_interpretation_def
        ,is_term_assignment_def,FEVERY_ALL_FLOOKUP,term_ok_def] >>
    metis_tac[] )
  >- (
    simp[termsem_clauses,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    metis_tac[]) >>
  simp[termsem_clauses,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  first_x_assum match_mp_tac >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[])

val Equalsem =
  is_std_interpretation_def
  |> SPEC_VAR |> snd
  |> Q.SPECL [`FST (i:'U interpretation)`,`SND i`]
  |> concl |> rhs
  |> strip_conj |> tl |> hd
  |> strip_forall |> snd |> rhs

val termsem_Equal = store_thm("termsem_Equal",
  ``∀i ty σ.
      is_std_interpretation i ⇒
      termsem i (Equal ty) σ = ^Equalsem``,
  Cases >> rw[is_std_interpretation_def,termsem_clauses])

(* equations *)

val termsem_equation = store_thm("termsem_equation",
  ``is_set_theory ^mem ⇒
    ∀sig i σ τ s t.
    is_structure sig i σ τ ∧
    term_ok sig (s === t)
    ⇒ termsem i (s === t) σ τ = Boolean (termsem i s σ τ = termsem i t σ τ)``,
  rw[is_structure_def] >> rfs[term_ok_equation] >>
  simp[equation_def,termsem_clauses,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[termsem_typesem,is_term_valuation_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,is_term_valuation_def,boolean_in_boolset] ) >>
  unabbrev_all_tac >> simp[])

(* aconv *)

val termsem_raconv = store_thm("termsem_raconv",
  ``is_set_theory ^mem ⇒
    ∀env tp. RACONV env tp ⇒
      ∀i σ1 σ2.
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem i (Var x1 ty1) σ1 =
             termsem i (Var x2 ty2) σ2)) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem i (FST tp) σ1 = termsem i (SND tp) σ2``,
  strip_tac >>
  ho_match_mp_tac RACONV_strongind >>
  rpt conj_tac >> simp[termsem_clauses] >>
  TRY (metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`RACONV env1 p1` >>
  qspecl_then[`env1`,`p1`]mp_tac RACONV_TYPE >>
  simp[Abbr`env1`,Abbr`p1`] >> strip_tac >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >> AP_THM_TAC >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[ALPHAVARS_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> fs[])

val termsem_aconv = store_thm("termsem_aconv",
  ``is_set_theory ^mem ⇒
    ∀i t1 t2. ACONV t1 t2 ∧ welltyped t1 ⇒ termsem i t1 = termsem i t2``,
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_welltyped,ACONV_def])

(* semantics only depends on valuation of free variables at the given type
   valuation *)

val termsem_frees = store_thm("termsem_frees",
  ``∀i t σ1 σ2 τ.
      (∀x ty. VFREE_IN (Var x ty) t ⇒ σ1 (x,ty) τ = σ2 (x,ty) τ)
      ⇒ termsem i t σ1 τ = termsem i t σ2 τ``,
  gen_tac >> Induct >>
  simp[termsem_clauses] >- metis_tac[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[])

(* term_assignment dependency on type assignment *)

val is_term_assignment_types = store_thm("is_term_assignment_types",
  ``∀tmenv δ γ δ'.
    (∀ty0 ty τ. ty0 ∈ FRANGE tmenv ∧ is_instance ty0 ty ∧ is_type_valuation τ
                ⇒ typesem δ' ty τ = typesem δ ty τ) ∧
    is_term_assignment tmenv δ γ ⇒
    is_term_assignment tmenv δ' γ``,
  rw[is_term_assignment_def] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF,IN_FRANGE,PULL_EXISTS])

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

val is_model_reduce = store_thm("is_model_reduce",
  ``∀i tyenv tmenv axs tyenv' tmenv' axs'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧ (∃ls. axs' = ls ++ axs) ∧
     is_model ((tyenv',tmenv'),axs') i ⇒
     is_model ((tyenv,tmenv),axs) i``,
  Cases >> rw[holSemanticsTheory.is_model_def] >>
  fs[EVERY_APPEND] >> imp_res_tac is_interpretation_reduce)

val _ = export_theory()
