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

(* termsem *)

val termsem_typesem = store_thm("termsem_typesem",
  ``is_set_theory ^mem ⇒
    ∀sig i tm v δ τ.
      δ = FST i ∧ τ = FST v ∧
      is_valuation δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm
      ⇒
      termsem i v tm <: typesem δ τ (typeof tm)``,
  strip_tac >> ntac 2 Cases >> Induct
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_term_valuation_def] )
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_interpretation_def
        ,is_term_assignment_def,FEVERY_ALL_FLOOKUP,term_ok_def] >>
    metis_tac[] )
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
  |> SPEC_VAR |> snd
  |> Q.SPECL [`FST (i:'U interpretation)`,`SND i`]
  |> concl |> rhs
  |> strip_conj |> tl |> hd
  |> strip_forall |> snd |> rhs

val termsem_Equal = store_thm("termsem_Equal",
  ``∀i v ty.
      is_std_interpretation i ⇒
      termsem i v (Equal ty) = ^Equalsem (FST v)``,
  Cases >> rw[is_std_interpretation_def,termsem_def])

(* equations *)

val termsem_equation = store_thm("termsem_equation",
  ``is_set_theory ^mem ⇒
    ∀sig i v s t.
    is_structure sig i v ∧
    term_ok sig (s === t)
    ⇒ termsem i v (s === t) = Boolean (termsem i v s = termsem i v t)``,
  rw[is_structure_def] >> rfs[term_ok_equation] >>
  simp[equation_def,termsem_def,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[termsem_typesem] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset] ) >>
  unabbrev_all_tac >> simp[])

(* aconv *)

val termsem_raconv = store_thm("termsem_raconv",
  ``is_set_theory ^mem ⇒
    ∀env tp. RACONV env tp ⇒
      ∀i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem i v1 (Var x1 ty1) =
             termsem i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem i v1 (FST tp) = termsem i v2 (SND tp)``,
  strip_tac >>
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
  ``is_set_theory ^mem ⇒
    ∀i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ⇒ termsem i v t1 = termsem i v t2``,
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_welltyped,ACONV_def])

(* semantics only depends on valuation of free variables *)

val termsem_frees = store_thm("termsem_frees",
  ``∀i t v1 v2.
      FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem i v1 t = termsem i v2 t``,
  gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[])

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

val ALOOKUP_MAP_dest_var = store_thm("ALOOKUP_MAP_dest_var",
  ``∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))``,
  Induct >> simp[] >> Cases >> simp[EVERY_MEM,EVERY_MAP] >>
  rw[] >> fs[])

val ALOOKUP_FILTER = store_thm("ALOOKUP_FILTER",
  ``∀ls x. ALOOKUP (FILTER (λ(k,v). P k) ls) x =
           if P x then ALOOKUP ls x else NONE``,
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> fs[] >> metis_tac[])

(* semantics of substitution *)

val termsem_simple_subst = store_thm("termsem_simple_subst",
  ``is_set_theory ^mem ⇒
    ∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀i v. termsem i v (simple_subst ilist tm) =
            termsem i
              (FST v, SND v =++
                      MAP ((dest_var ## termsem i v) o (λ(s',s). (s,s')))
                          (REVERSE ilist))
              tm``,
  strip_tac >> Induct >> simp[termsem_def] >- (
    simp[REV_ASSOCD_ALOOKUP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> rw[termsem_def] >- (
      imp_res_tac ALOOKUP_FAILS >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >> metis_tac[] ) >>
    rw[GSYM MAP_MAP_o] >>
    qmatch_assum_abbrev_tac`ALOOKUP ls (Var s ty) = SOME x` >>
    Q.ISPECL_THEN[`ls`,`termsem i v`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
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
  qmatch_abbrev_tac `termsem i vv xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`i`,`vv`]mp_tac) >>
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
    Q.ISPECL_THEN[`ls`,`termsem i v`,`z`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem i v`,`z`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
  (discharge_hyps >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[])

(* TODO: semantics of instantiation *)

(* term_assignment dependency on type assignment *)

val is_term_assignment_types = store_thm("is_term_assignment_types",
  ``∀tmenv δ γ δ'.
    (∀ty0 ty τ. ty0 ∈ FRANGE tmenv ∧ is_instance ty0 ty ∧ is_type_valuation τ
                ⇒ typesem δ' τ ty = typesem δ τ ty) ∧
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
