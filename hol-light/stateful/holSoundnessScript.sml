open HolKernel boolLib bossLib lcsymtacs listTheory finite_mapTheory alistTheory pred_setTheory pairTheory
open miscLib setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holSoundness"

val mem = ``mem:'U->'U-> bool``

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀ctxt p. is_std_sig (sigof ctxt) ∧ p has_type Bool ∧ term_ok (sigof ctxt) p
             ⇒ (ctxt,[p]) |= p``,
  rw[entails_def,satisfies_def])

val REFL_correct = store_thm("REFL_correct",
  ``is_set_theory ^mem ⇒
    is_std_sig (sigof ctxt) ⇒
    ∀t. term_ok (sigof ctxt) t ⇒
      (ctxt,[]) |= t === t``,
  rw[entails_def,satisfies_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac term_ok_welltyped >>
  `term_ok (sigof ctxt) (t === t)` by rw[term_ok_equation] >>
  `is_structure (sigof ctxt) i v` by (
    rw[is_structure_def] >> fs[is_model_def] ) >>
  imp_res_tac term_ok_type_ok >> fs[] >>
  imp_res_tac termsem_equation >>
  rw[boolean_def])

val binary_inference_rule = store_thm("binary_inference_rule",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof ctxt) q ∧
    (∀i v. is_structure (sigof ctxt) i v ∧
           termsem (sigof ctxt) i v p1 = True ∧
           termsem (sigof ctxt) i v p2 = True ⇒
           termsem (sigof ctxt) i v q = True) ∧
    (ctxt,h1) |= p1 ∧ (ctxt,h2) |= p2
    ⇒ (ctxt, TERM_UNION h1 h2) |= q``,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def] >> rw[] >>
  rpt (first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  fs[satisfies_def,EVERY_TERM_UNION] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- ( rw[is_structure_def] >> fs[is_model_def] ) >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[EVERY_MEM] >>
  metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,termsem_aconv,welltyped_def])

val TRANS_correct = store_thm("TRANS_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 l m1 m2 r.
      (ctxt,h1) |= l === m1 ∧ (ctxt,h2) |= m2 === r ∧ ACONV m1 m2
      ⇒ (ctxt,TERM_UNION h1 h2) |= l === r``,
  strip_tac >>
  rw[] >> match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l === m1`,`m2 === r`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  fs[entails_def] >>
  simp[CONJ_ASSOC] >> conj_asm1_tac >- (
    metis_tac[ACONV_TYPE,ACONV_welltyped,term_ok_welltyped,term_ok_equation] ) >>
  rw[] >> imp_res_tac termsem_equation >>
  rfs[boolean_eq_true] >> fs[term_ok_equation] >>
  metis_tac[termsem_aconv,ACONV_SYM,term_ok_welltyped])

val MK_COMB_correct = store_thm("MK_COMB_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 l1 r1 l2 r2.
      (ctxt,h1) |= l1 === r1 ∧ (ctxt,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (ctxt,TERM_UNION h1 h2) |= Comb l1 l2 === Comb r1 r2``,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l1 === r1`,`l2 === r2`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  fs[entails_def] >>
  simp[CONJ_ASSOC] >> conj_asm1_tac >- (
    fs[term_ok_equation,term_ok_def] >>
    rfs[term_ok_equation] >>
    imp_res_tac term_ok_welltyped >> rw[] ) >>
  rw[] >>
  imp_res_tac (UNDISCH termsem_equation) >>
  rfs[boolean_eq_true] >>
  rw[termsem_def])

val EQ_MP_correct = store_thm("EQ_MP_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 h2 p q p'.
      (ctxt,h1) |= p === q ∧ (ctxt,h2) |= p' ∧ ACONV p p' ⇒
      (ctxt,TERM_UNION h1 h2) |= q``,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`p === q`,`p'`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  fs[entails_def] >>
  simp[CONJ_ASSOC] >> conj_asm1_tac >- (
    fs[term_ok_equation,term_ok_def,EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] ) >>
  rw[] >>
  imp_res_tac (UNDISCH termsem_equation) >>
  rfs[boolean_eq_true,EQUATION_HAS_TYPE_BOOL] >>
  metis_tac[termsem_aconv])

val BETA_correct = store_thm("BETA_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt x ty t.
      is_std_sig (sigof ctxt) ∧ type_ok (types ctxt) ty ∧ term_ok (sigof ctxt) t ⇒
      (ctxt,[]) |= Comb (Abs x ty t) (Var x ty) === t``,
  strip_tac >>
  simp[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- (
    simp[term_ok_equation,term_ok_def] ) >>
  rw[satisfies_def] >>
  `is_structure (sigof ctxt) i v` by (
    rw[is_structure_def] >> fs[is_model_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  rw[boolean_eq_true,termsem_def] >>
  qmatch_abbrev_tac`(Abstract mty mtyb f ' e) = termsem Γ i v τ` >>
  `Abstract mty mtyb f ' e = f e` by (
    match_mp_tac (MP_CANON apply_abstract) >>
    simp[Abbr`f`,Abbr`e`] >>
    conj_tac >- (
      Cases_on`v`>>
      fs[is_valuation_def,is_term_valuation_def,Abbr`mty`]) >>
    simp[Abbr`mtyb`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[is_structure_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    Cases_on`v`>>
    fs[is_valuation_def,is_term_valuation_def] >>
    rw[combinTheory.APPLY_UPDATE_THM]) >>
  simp[Abbr`f`,Abbr`e`] >>
  rw[combinTheory.APPLY_UPDATE_ID])

val ABS_correct = store_thm("ABS_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧
    (ctxt,h) |= l === r ∧
    type_ok (types ctxt) ty ⇒
    (ctxt,h) |= Abs x ty l === Abs x ty r``,
  rw[] >>
  fs[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  conj_asm1_tac >- rfs[term_ok_equation,term_ok_def] >>
  fs[satisfies_def] >> rw[] >>
  first_x_assum(qspec_then`i`mp_tac) >> rw[] >>
  `is_structure (sigof ctxt) i v` by (
    fs[is_model_def,is_structure_def] ) >>
  imp_res_tac termsem_equation >>
  rw[boolean_eq_true,termsem_def] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  qx_gen_tac`m` >> strip_tac >> simp[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  `is_valuation (FST i) vv` by (
    Cases_on`v`>>
    fs[is_valuation_def,Abbr`vv`,is_term_valuation_def] >>
    rw[combinTheory.APPLY_UPDATE_THM] >> rw[]) >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    fs[is_structure_def] >>
    metis_tac[termsem_typesem,is_std_interpretation_is_type
             ,pairTheory.FST,term_ok_equation]) >>
  first_x_assum(qspec_then`vv`mp_tac) >>
  `is_structure (sigof ctxt) i vv` by (
    fs[is_structure_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  simp[boolean_eq_true] >> disch_then match_mp_tac >>
  fs[EVERY_MEM] >> rw[] >>
  qsuff_tac`termsem (sigof ctxt) i vv t = termsem (sigof ctxt) i v t`>-metis_tac[] >>
  match_mp_tac termsem_frees >>
  simp[Abbr`vv`,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[])

val DEDUCT_ANTISYM_correct = store_thm("DEDUCT_ANTISYM_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h1 p1 h2 p2.
      (ctxt,h1) |= p1 ∧ (ctxt,h2) |= p2 ⇒
      (ctxt,
       TERM_UNION (FILTER ($~ o ACONV p2) h1)
                  (FILTER ($~ o ACONV p1) h2))
      |= p1 === p2``,
  rw[] >>
  fs[entails_def] >>
  conj_asm1_tac >- (
    simp[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    match_mp_tac EVERY_TERM_UNION >>
    fs[EVERY_MEM,MEM_FILTER] ) >>
  conj_asm1_tac >- (
    simp[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[WELLTYPED] >>
    match_mp_tac EVERY_TERM_UNION >>
    fs[EVERY_MEM,MEM_FILTER] ) >>
  rw[] >> fs[satisfies_def] >> rw[] >>
  `is_structure (sigof ctxt) i v` by (
    fs[is_model_def,is_structure_def] ) >>
  imp_res_tac (UNDISCH termsem_equation) >>
  simp[boolean_eq_true] >>
  rpt(first_x_assum(qspec_then`i`mp_tac)>>rw[]) >>
  rpt(first_x_assum(qspec_then`v`mp_tac)>>rw[]) >>
  fs[EVERY_MEM] >>
  ntac 2 (pop_assum mp_tac) >>
  `∀x y ls. MEM x (FILTER ($~ o ACONV y) ls) ⇔ ¬ACONV y x ∧ MEM x ls` by simp[MEM_FILTER] >>
  qmatch_abbrev_tac`(a ⇒ b) ⇒ (c ⇒ d) ⇒ e` >>
  `d ⇒ a` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[TERM_UNION_THM,termsem_aconv,welltyped_def] ) >>
  `b ⇒ c` by (
    unabbrev_all_tac >> rw[] >>
    metis_tac[TERM_UNION_THM,termsem_aconv,welltyped_def] ) >>
  `termsem (sigof ctxt) i v p1 <: boolset ∧
   termsem (sigof ctxt) i v p2 <: boolset` by (
    fs[is_structure_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac termsem_typesem >>
    imp_res_tac WELLTYPED_LEMMA >>
    metis_tac[typesem_Bool]) >>
  metis_tac[mem_boolset])

val INST_correct = store_thm("INST_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof ctxt) s') ∧
      (ctxt, h) |= c
    ⇒ (ctxt, MAP (VSUBST ilist) h) |= VSUBST ilist c``,
  rw[entails_def,term_ok_VSUBST,EVERY_MAP,EVERY_MEM] >>
  TRY ( match_mp_tac VSUBST_HAS_TYPE >> metis_tac[] ) >>
  fs[satisfies_def] >> rw[] >>
  qspecl_then[`c`,`ilist`]mp_tac termsem_VSUBST >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  disch_then(qspecl_then[`sigof ctxt`,`i`,`v`]SUBST1_TAC) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  conj_tac >- (
    Cases_on`v`>>
    fs[is_valuation_def] >>
    fs[is_term_valuation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,UNCURRY,EXISTS_PROD] >>
    res_tac >> imp_res_tac WELLTYPED_LEMMA >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    rw[is_valuation_def,is_term_valuation_def] >>
    fs[is_model_def] >> metis_tac[is_std_interpretation_is_type] ) >>
  fs[EVERY_MAP,EVERY_MEM] >>
  metis_tac[termsem_VSUBST,welltyped_def])

val INST_TYPE_correct = store_thm("INST_TYPE_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h c.
      EVERY (type_ok (types ctxt)) (MAP FST tyin) ∧
      (ctxt, h) |= c
    ⇒ (ctxt, MAP (INST tyin) h) |= INST tyin c``,
  rw[entails_def,term_ok_INST,EVERY_MAP,EVERY_MEM] >>
  TRY ( match_mp_tac INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool] ) >>
  fs[satisfies_def] >> rw[] >>
  qspecl_then[`sigof ctxt`,`c`,`tyin`]mp_tac termsem_INST >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  disch_then(qspecl_then[`i`,`v`]SUBST1_TAC) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  conj_tac >- (
    Cases_on`v`>>
    fs[is_valuation_def] >>
    conj_tac >- (
      fs[is_type_valuation_def] >> rw[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      Cases_on`i`>>fs[is_model_def,is_interpretation_def] >>
      qexists_tac`types ctxt` >> simp[is_type_valuation_def] >>
      fs[FORALL_PROD] >>
      metis_tac[holSyntaxLibTheory.REV_ASSOCD_MEM,type_ok_def] ) >>
    fs[is_term_valuation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    simp[Once (typesem_TYPE_SUBST |> SIMP_RULE(srw_ss())[] |> GSYM)]) >>
  fs[EVERY_MAP,EVERY_MEM] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_INST,welltyped_def])

val new_type_correct = store_thm("new_type_correct",
  ``∀ctxt h c name arity.
      name ∉ (FDOM (types ctxt)) ∧
      (ctxt,h) |= c
      ⇒ ((NewType name arity)::ctxt,h) |= c``,
  simp[entails_def,types_of_def_def,consts_of_def_def,axioms_of_def_def] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- (
    match_mp_tac is_std_sig_extend >>
    map_every qexists_tac[`types ctxt`,`consts ctxt`] >>
    simp[] ) >>
  conj_asm1_tac >- (
    fs[EVERY_MEM] >> rw[] >>
    match_mp_tac term_ok_extend >>
    map_every qexists_tac[`types ctxt`,`consts ctxt`] >>
    simp[] ) >>
  rw[] >>
  first_x_assum match_mp_tac >>
  match_mp_tac is_model_reduce >>
  qmatch_assum_abbrev_tac`is_model ((tyenv,tmenv),axs) i` >>
  map_every qexists_tac[`tyenv`,`tmenv`,`axs`] >>
  simp[Abbr`tyenv`])

val new_constant_correct = store_thm("new_constant_correct",
  ``∀ctxt h c name ty.
      name ∉ (FDOM (consts ctxt)) ∧
      (ctxt,h) |= c
      ⇒ ((NewConst name ty)::ctxt,h) |= c``,
  simp[entails_def,types_of_def_def,consts_of_def_def,axioms_of_def_def] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- (
    match_mp_tac is_std_sig_extend >>
    map_every qexists_tac[`types ctxt`,`consts ctxt`] >>
    simp[] ) >>
  conj_asm1_tac >- (
    fs[EVERY_MEM] >> rw[] >>
    match_mp_tac term_ok_extend >>
    map_every qexists_tac[`types ctxt`,`consts ctxt`] >>
    simp[] ) >>
  rw[] >>
  first_x_assum match_mp_tac >>
  match_mp_tac is_model_reduce >>
  qmatch_assum_abbrev_tac`is_model ((tyenv,tmenv),axs) i` >>
  map_every qexists_tac[`tyenv`,`tmenv`,`axs`] >>
  simp[Abbr`tmenv`])

val new_axiom_correct = store_thm("new_axiom_correct",
  ``∀ctxt p h c.
    p has_type Bool ∧ term_ok (sigof ctxt) p ∧
    ((ctxt,h) |= c ∨ ((h,c) = ([],p) ∧ is_std_sig (sigof ctxt)))
    ⇒ ((NewAxiom p)::ctxt, h) |= c``,
  simp[entails_def,types_of_def_def,consts_of_def_def,axioms_of_def_def] >>
  rpt gen_tac >> strip_tac >> simp[] >> rw[] >- (
    first_x_assum match_mp_tac >>
    match_mp_tac is_model_reduce >>
    metis_tac[rich_listTheory.CONS_APPEND,SUBMAP_REFL] ) >>
  fs[is_model_def])

val new_specification_correct = store_thm("new_specification_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt eqs prop asl p.
    (ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |= prop ∧
    EVERY
      (λt. CLOSED t ∧
           (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
      (MAP SND eqs) ∧
    (∀x ty. VFREE_IN (Var x ty) prop ⇒
              MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
    (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (consts ctxt))) ∧
    ALL_DISTINCT (MAP FST eqs) ∧
    ((ctxt, asl) |= p ∨
     (let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
        (asl,p) = ([],VSUBST ilist prop)))
    ⇒ ((ConstSpec eqs prop)::ctxt,asl) |= p``,
  strip_tac >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`D ⇔ A ∨ B` >>
  simp[entails_def,types_of_def_def,consts_of_def_def,axioms_of_def_def] >>
  rpt gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`cs:(string |-> type) = alist_to_fmap Z` >>
  `consts ctxt ⊑ cs ⊌ consts ctxt` by (
    match_mp_tac SUBMAP_FUNION >>
    simp[Abbr`cs`,IN_DISJOINT] >>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    match_mp_tac is_std_sig_extend >>
    metis_tac[SUBMAP_REFL] ) >>
  conj_asm1_tac >- (
    fs[Abbr`D`,EVERY_MEM,entails_def,LET_THM] >> rw[] >>
    TRY (match_mp_tac term_ok_VSUBST >> conj_tac) >>
    TRY (
      match_mp_tac term_ok_extend >>
      map_every qexists_tac[`types ctxt`,`consts ctxt`] >>
      simp[] >> NO_TAC) >>
    rw[MEM_MAP,EXISTS_PROD,term_ok_def,Abbr`cs`,FLOOKUP_FUNION] >>
    rw[Once has_type_cases] >>
    rw[ALOOKUP_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    rw[] >>
    fs[MEM_MAP,PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`MEM eq eqs` >>
    last_x_assum(qspec_then`eq`mp_tac) >>
    simp[Abbr`eq`,term_ok_equation,term_ok_def] ) >>
  conj_asm1_tac >- (
    fs[Abbr`D`,entails_def,LET_THM] >>
    match_mp_tac VSUBST_HAS_TYPE >>
    simp[MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    rw[Once has_type_cases] ) >>
  rpt strip_tac >>
  `is_model (sigof ctxt,axioms ctxt) i` by (
    match_mp_tac is_model_reduce >>
    metis_tac[APPEND,SUBMAP_REFL] ) >>
  fs[Abbr`D`,LET_THM,entails_def] >>
  fs[satisfies_def] >> rw[] >>
  first_x_assum(qspec_then`i`mp_tac) >> rw[] >>
  qabbrev_tac`vv = λ(x,ty).
    case ALOOKUP eqs x of
    | NONE => SND v (x,ty)
    | SOME t => if ty ≠ typeof t then SND v (x,ty) else termsem i v t` >>
  first_x_assum(qspec_then`(FST v,vv)`mp_tac) >>
  discharge_hyps >- (
    conj_asm1_tac >- (
      Cases_on`v`>>fs[is_valuation_def,is_term_valuation_def] >>
      simp[Abbr`vv`] >> rw[] >>
      Cases_on`i`>>fs[is_model_def,is_interpretation_def,is_term_assignment_def] >>
      BasicProvers.CASE_TAC >> rw[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MAP,EVERY_MEM] >>
      match_mp_tac (UNDISCH termsem_typesem) >>
      simp[is_valuation_def,is_term_valuation_def] >>
      qexists_tac`sigof ctxt` >>
      simp[is_interpretation_def,is_term_assignment_def] >>
      imp_res_tac is_std_interpretation_is_type >> fs[] >>
      fs[FORALL_PROD] >>
      metis_tac[term_ok_equation]) >>
    simp[EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
    `is_structure (sigof ctxt) i (FST v,vv)` by (
      fs[is_structure_def,is_model_def] ) >>
    qx_genl_tac[`x`,`t`] >> strip_tac >>
    `term_ok (sigof ctxt) (Var x (typeof t) === t)` by (
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD] ) >>
    imp_res_tac (UNDISCH termsem_equation) >>
    simp[boolean_eq_true,termsem_def] >>
    simp[Abbr`vv`] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    simp[] >>
    match_mp_tac termsem_frees >>
    simp[] >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
    metis_tac[CLOSED_def] ) >>
  cheat)

(*
val new_type_definition_correct = store_thm("new_type_definition_correct",
*)

val _ = export_theory()
