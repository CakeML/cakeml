open HolKernel boolLib bossLib lcsymtacs pairTheory listTheory alistTheory finite_mapTheory pred_setTheory
open miscLib miscTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory
val _ = temp_tight_equality()
val _ = new_theory"holConsistency"

val mem = ``mem:'U->'U->bool``

val proves_consistent = store_thm("proves_consistent",
  ``is_set_theory ^mem ⇒
    ∀ctxt. theory_ok (thyof ctxt) ∧ (∃i. i models (thyof ctxt)) ⇒
      (thyof ctxt,[]) |- (Var "x" Bool === Var "x" Bool) ∧
      ¬((thyof ctxt,[]) |- (Var "x" Bool === Var "y" Bool))``,
  rw[] >- (
    match_mp_tac (List.nth(CONJUNCTS proves_rules,8)) >>
    simp[term_ok_def,type_ok_def] >>
    imp_res_tac theory_ok_sig >>
    fs[is_std_sig_def] ) >>
  spose_not_then strip_assume_tac >>
  imp_res_tac proves_sound >>
  fs[entails_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  simp[satisfies_def] >>
  qexists_tac`(K boolset),
              λ(x,ty). if (x,ty) = ("x",Bool) then True else
                       if (x,ty) = ("y",Bool) then False else
                       @v. v <: typesem (tyaof i) (K boolset) ty` >>
  conj_asm1_tac >- (
    simp[is_valuation_def] >>
    conj_asm1_tac >- (simp[is_type_valuation_def,mem_boolset] >> PROVE_TAC[]) >>
    fs[models_def,is_term_valuation_def,is_interpretation_def] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >>
    rw[mem_boolset] >>
    metis_tac[typesem_inhabited] ) >>
  qmatch_abbrev_tac`termsem sig i v (s === t) ≠ True` >>
  qspecl_then[`sig`,`i`,`v`,`s`,`t`]mp_tac(UNDISCH termsem_equation) >>
  discharge_hyps >- (
    simp[term_ok_equation,is_structure_def] >>
    fs[models_def,Abbr`sig`,theory_ok_def] ) >>
  simp[Abbr`s`,Abbr`t`,termsem_def,boolean_eq_true,Abbr`v`,true_neq_false])

val init_ctxt_has_model = store_thm("init_ctxt_has_model",
  ``is_set_theory ^mem ⇒ ∃i. i models (thyof init_ctxt)``,
  rw[models_def,init_ctxt_def,conexts_of_upd_def] >>
  rw[is_std_interpretation_def,is_std_type_assignment_def,EXISTS_PROD] >>
  qho_match_abbrev_tac`∃f g. P f g ∧ (f x1 = y1 ∧ f x2 = y2) ∧ (g interprets x3 on z3 as y3)` >>
  qexists_tac`λx. if x = x1 then y1 else if x = x2 then y2 else ARB` >>
  qexists_tac`K y3` >>
  rw[Abbr`x1`,Abbr`x2`,Abbr`P`,interprets_def] >>
  rw[is_interpretation_def,is_type_assignment_def,is_term_assignment_def] >>
  rw[FEVERY_FUPDATE,Abbr`y2`,Abbr`y1`,Abbr`y3`,FEVERY_FEMPTY,Abbr`z3`] >>
  rw[typesem_def,tyvars_def] >>
  TRY (
    rw[INORDER_INSERT_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] ) >>
  BasicProvers.CASE_TAC >> fs[] >- metis_tac[boolean_in_boolset] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac (UNDISCH funspace_inhabited) >>
  metis_tac[])

val subinterpretation_def = Define`
  subinterpretation ctxt i i' ⇔
  (∀name args. type_ok (tysof ctxt) (Tyapp name args) ⇒ tyaof i' name = tyaof i name) ∧
  (∀name ty. term_ok (sigof ctxt) (Const name ty) ⇒ tmaof i' name = tmaof i name)`

val consistent_update_def = xDefine"consistent_update"`
  consistent_update0 ^mem ctxt upd ⇔
    ∀i. i models (thyof ctxt) ⇒
      ∃i'. subinterpretation ctxt i i' ∧
           i' models (thyof (upd::ctxt))`
val _ = Parse.overload_on("consistent_update",``consistent_update0 ^mem``)

val new_constant_correct = store_thm("new_constant_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt name ty.
     theory_ok (thyof ctxt) ∧
     name ∉ (FDOM (tmsof ctxt)) ∧
     type_ok (tysof ctxt) ty ⇒
     consistent_update ctxt (NewConst name ty)``,
  rw[] >> REWRITE_TAC[consistent_update_def,subinterpretation_def] >>
  gen_tac >> strip_tac >>
  qexists_tac`(tyaof i,
    (name =+ λl. @v. v <: typesem (tyaof i) ((K boolset) =++ (REVERSE(ZIP(STRING_SORT (tyvars ty),l)))) ty)
    (tmaof i))` >>
  conj_asm1_tac >- (
    simp[term_ok_def,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> PROVE_TAC[] ) >>
  fs[models_def,conexts_of_upd_def] >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
    simp[combinTheory.APPLY_UPDATE_THM] >> rw[] >>
    qmatch_abbrev_tac`(@v. v <: (typesem δ τ' ty)) <: x` >>
    `typesem δ τ' ty = typesem δ τ ty` by (
      match_mp_tac typesem_tyvars >>
      simp[Abbr`τ'`,APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
      rw[] >> BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP]) >>
    metis_tac[typesem_inhabited] ) >>
  conj_tac >- (
    imp_res_tac theory_ok_sig >>
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,is_std_sig_def,interprets_def] >>
    imp_res_tac ALOOKUP_MEM >> rw[] >>
    fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac satisfies_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  rw[] >- fs[theory_ok_def] >>
  match_mp_tac satisfies_consts >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  metis_tac[])

val new_specification_correct = store_thm("new_specification_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt eqs prop.
     theory_ok (thyof ctxt) ∧
     (thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
     EVERY
       (λt. CLOSED t ∧
            (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
       (MAP SND eqs) ∧
     (∀x ty. VFREE_IN (Var x ty) prop ⇒
               MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
     (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
     ALL_DISTINCT (MAP FST eqs) ⇒
    consistent_update ctxt (ConstSpec eqs prop)``,
  rw[] >> REWRITE_TAC[consistent_update_def,subinterpretation_def] >>
  gen_tac >> strip_tac >>
  qexists_tac`(tyaof i,
    (tmaof i) =++
      MAP (λ(s,t). (s, λl. termsem (sigof ctxt) i ((K boolset)=++(REVERSE(ZIP(STRING_SORT(tyvars(typeof t)),l))),ARB) t))
          (REVERSE eqs))` >>
  conj_asm1_tac >- (
    simp[term_ok_def,ALOOKUP_MAP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> PROVE_TAC[] ) >>
  fs[models_def] >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_FUNION] >>
    simp[ALOOKUP_MAP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> fs[] >> rw[] >>
    qmatch_abbrev_tac`termsem sig i t1 t <: x` >>
    imp_res_tac theory_ok_sig >>
    `termsem sig i t1 t = termsem sig i (τ,SND t1) t` by (
      match_mp_tac termsem_tyfrees >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac proves_term_ok >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] >>
      rfs[term_ok_equation] >>
      conj_tac >- metis_tac[] >>
      rw[Abbr`t1`,APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
      BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP] >> metis_tac[] ) >>
    `is_valuation (tysof sig) (tyaof i) (τ,λ(x,ty). @v. v <: typesem (tyaof i) τ ty)` by (
      fs[is_valuation_def,is_term_valuation_def] >> rw[] >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[Abbr`sig`] >> metis_tac[] ) >>
    qmatch_assum_abbrev_tac`is_valuation tyenv δ v` >>
    `termsem sig i (τ,tmvof t1) t = termsem sig i v t` by (
      match_mp_tac termsem_frees >>
      simp[Abbr`v`] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,CLOSED_def] >>
      metis_tac[] ) >>
    rw[] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    unabbrev_all_tac >> simp[] >>
    fs[is_interpretation_def] >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    imp_res_tac is_std_interpretation_is_type >> simp[] >>
    imp_res_tac proves_term_ok >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] >>
    rfs[term_ok_equation] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[] ) >>
  conj_tac >- (
    fs[is_std_interpretation_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP,interprets_def] >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac theory_ok_sig  >>
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  simp[conexts_of_upd_def] >>
  gen_tac >> reverse strip_tac >- (
    match_mp_tac satisfies_extend >>
    imp_res_tac proves_sound >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    discharge_hyps >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      match_mp_tac SUBMAP_FUNION >>
      fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,ETA_AX,UNCURRY] >>
      metis_tac[] ) >>
    match_mp_tac satisfies_consts >>
    qexists_tac`i` >> simp[] >>
    simp[term_ok_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac proves_sound >> pop_assum mp_tac >>
  rw[entails_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  discharge_hyps >- fs[models_def] >>
  rw[satisfies_def] >>
  qmatch_abbrev_tac`termsem sig ii v (VSUBST ilist tm) = True` >>
  qspecl_then[`tm`,`ilist`]mp_tac termsem_VSUBST >>
  discharge_hyps >- (
    simp[welltyped_def,Abbr`ilist`,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    metis_tac[has_type_rules] ) >>
  simp[] >> disch_then kall_tac >>
  qmatch_abbrev_tac`termsem sig ii vv tm = True` >>
  `tmsof ctxt ⊑ tmsof sig` by (
    simp[Abbr`sig`] >>
    match_mp_tac SUBMAP_FUNION >>
    fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    metis_tac[] ) >>
  `termsem sig ii vv tm = termsem (sigof ctxt) ii vv tm` by (
    fs[Abbr`sig`] >> metis_tac[termsem_extend] ) >>
  `termsem (sigof ctxt) ii vv tm = termsem (sigof ctxt) i vv tm` by (
    match_mp_tac termsem_consts >>
    simp[Abbr`ii`] >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_def] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  rw[] >>
  first_x_assum match_mp_tac >>
  conj_asm1_tac >- (
    fs[Abbr`vv`,is_valuation_def,is_term_valuation_def] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[termsem_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rpt (qpat_assum `termsem X Y Z tm = A`kall_tac) >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: x` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`sig`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    simp[] >>
    disch_then(qspec_then`[]`mp_tac) >>
    simp[] >> disch_then kall_tac >>
    simp[Abbr`ii`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    `is_valuation (tysof ctxt) (tyaof i) (τ,λ(x,ty). @v. v <: typesem (tyaof i) τ ty)` by (
      fs[is_valuation_def,is_term_valuation_def] >> rw[] >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_interpretation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`termsem sig i (v1,v2) tt <: tysem` >>
    qmatch_assum_abbrev_tac`is_valuation (tysof ctxt) (tyaof i) (τ,σ)` >>
    `termsem sig i (v1,v2) tt = termsem sig i (τ,v2) tt` by (
      match_mp_tac termsem_tyfrees >>
      simp[Abbr`v1`,REV_ASSOCD,typesem_def,Abbr`sig`] >>
      imp_res_tac theory_ok_sig >>
      fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      conj_tac >- metis_tac[] >>
      simp[APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
      rw[] >>
      BasicProvers.CASE_TAC >> fs[ALOOKUP_FAILS] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD,Abbr`ty`] >>
      rw[typesem_def] >> metis_tac[]) >>
    `termsem sig i (τ,v2) tt = termsem sig i (τ,σ) tt` by (
       match_mp_tac termsem_frees >>
       fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,CLOSED_def] >>
       metis_tac[] ) >>
    rw[Abbr`tysem`,Abbr`ty`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[Abbr`sig`] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
    metis_tac[] ) >>
  imp_res_tac theory_ok_sig >>
  `is_structure (sigof ctxt) i vv` by (
    fs[is_structure_def] ) >>
  simp[EVERY_MAP,EVERY_MEM,FORALL_PROD] >> rw[] >>
  fs[EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
  simp[termsem_equation,boolean_eq_true,termsem_def] >>
  simp[Abbr`vv`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
  simp[termsem_def] >>
  qmatch_abbrev_tac`instance sig ii name ty τ = X` >>
  qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
  simp[Abbr`sig`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`ii`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
  qmatch_abbrev_tac`termsem sig i (v1,v2) tt = termsem sig i (v3,v4) tt` >>
  `termsem sig i (v1,v2) tt = termsem sig i (v3,v2) tt` by (
    match_mp_tac termsem_tyfrees >>
    simp[Abbr`sig`,Abbr`v1`,REV_ASSOCD,typesem_def] >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    conj_tac >- metis_tac[]>>
    simp[APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
    rw[] >>
    BasicProvers.CASE_TAC >> fs[ALOOKUP_FAILS] >>
    imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >>
    rw[typesem_def] >> metis_tac[]) >>
  `termsem sig i (v3,v2) tt = termsem sig i (v3,v4) tt` by (
    match_mp_tac termsem_frees >> simp[] >>
    fs[EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD,CLOSED_def] >>
    metis_tac[] ) >>
  rw[Abbr`v4`])

val new_type_correct = store_thm("new_type_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt name arity.
     theory_ok (thyof ctxt) ∧
     name ∉ FDOM (tysof ctxt) ⇒
     consistent_update ctxt (NewType name arity)``,
  rw[] >> REWRITE_TAC[consistent_update_def,subinterpretation_def] >>
  gen_tac >> strip_tac >>
  qexists_tac`((name =+ (K boolset)) (tyaof i),tmaof i)` >>
  conj_tac >- (
    simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> PROVE_TAC[] ) >>
  fs[models_def] >>
  simp[conexts_of_upd_def] >>
  conj_asm1_tac >- (
    fs[is_interpretation_def,is_term_assignment_def,is_type_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
    simp[combinTheory.APPLY_UPDATE_THM] >> rw[] >- metis_tac[boolean_in_boolset] >>
    qmatch_abbrev_tac`x <: typesem δ' τ ty` >>
    `typesem δ' τ ty = typesem (tyaof i) τ ty` by (
      match_mp_tac typesem_consts >>
      rw[Abbr`δ'`,combinTheory.APPLY_UPDATE_THM] >>
      qexists_tac`tysof ctxt` >>
      conj_asm1_tac >- (
        fs[theory_ok_def] >>
        first_x_assum match_mp_tac >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
        simp[IN_FRANGE,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
        metis_tac[] ) >>
      rw[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    rw[Abbr`x`] ) >>
  conj_tac >- (
    imp_res_tac theory_ok_sig >>
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,is_std_sig_def,interprets_def] >>
    fs[is_std_type_assignment_def,combinTheory.APPLY_UPDATE_THM] >>
    imp_res_tac ALOOKUP_MEM >> rw[] >>
    fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac satisfies_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  rw[] >- fs[theory_ok_def] >>
  match_mp_tac satisfies_consts >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  rw[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[])

val eqsh_def = new_definition("eqsh",``eqsh = $=``)
val new_type_definition_correct = store_thm("new_type_definition_correct",
  ``is_set_theory ^mem ⇒
    ∀ctxt h c name pred abs rep rep_type witness.
    (thyof ctxt,[]) |- Comb pred witness ∧
    CLOSED pred ∧ pred has_type (Fun rep_type Bool) ∧
    name ∉ (FDOM (tysof ctxt)) ∧
    abs ∉ (FDOM (tmsof ctxt)) ∧
    rep ∉ (FDOM (tmsof ctxt)) ∧
    abs ≠ rep ⇒
    consistent_update ctxt (TypeDefn name pred abs rep)``,
  rw[consistent_update_def,subinterpretation_def,models_def,LET_THM] >>
  Q.PAT_ABBREV_TAC`tys' = tysof ctxt |+ X` >>
  Q.PAT_ABBREV_TAC`tms' = tmsof ctxt |+ X |+ Y` >>
  imp_res_tac WELLTYPED_LEMMA >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac theory_ok_sig >> fs[] >>
  `name ∉ {"fun";"bool"} ∧ abs ≠ "=" ∧ rep ≠ "="` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >> fs[] >>
  qmatch_assum_abbrev_tac`Abbrev(tms' = tmsof ctxt |+ (rep, Fun abs_type rep_type) |+ Y)` >>
  qunabbrev_tac`Y` >>
  qabbrev_tac`argv = STRING_SORT (tvars pred)` >>
  qabbrev_tac`tv:'U list -> 'U tyval = λargs a.
    (K boolset =++ (REVERSE(ZIP((STRING_SORT(tvars pred),args))))) a` >>
  qabbrev_tac`δ = tyaof i` >>
  qabbrev_tac`sv:'U tyval->'U tmval = λτ (x,ty). @v. v <: typesem δ τ ty` >>
  qabbrev_tac`mpred = λτ. termsem (sigof ctxt) i (τ, sv τ) pred` >>
  qabbrev_tac`mty = λargs. typesem δ (tv args) rep_type suchthat Holds (mpred (tv args))` >>
  qabbrev_tac`mrep = λargs. Abstract (mty args) (typesem δ (tv args) rep_type)  I` >>
  qabbrev_tac`mabs = λargs. Abstract (typesem δ (tv args) rep_type) (mty args)
                           (λv. if Holds (mpred (tv args)) v then v else @v. v <: mty args)` >>
  imp_res_tac proves_sound >>
  imp_res_tac proves_term_ok >>
  fs[term_ok_def] >>
  imp_res_tac term_ok_type_ok >>
  rfs[type_ok_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac is_std_interpretation_is_type >>
  `∀ls. EVERY inhabited ls ∧ LENGTH ls = LENGTH (tvars pred)
    ⇒ is_type_valuation (tv ls)` by (
    simp[is_type_valuation_def,Abbr`tv`] >> rw[] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP] >>
    BasicProvers.CASE_TAC >- metis_tac[boolean_in_boolset] >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP,Abbr`argv`,EVERY_MEM] >>
    metis_tac[MEM_EL] ) >>
  `is_std_type_assignment ((name =+ mty) δ)` by (
    fs[is_std_type_assignment_def,combinTheory.APPLY_UPDATE_THM,Abbr`δ`] ) >>
  `∀τ. is_type_valuation τ ⇒ is_term_valuation (tysof ctxt) δ τ (sv τ)` by (
    rw[is_term_valuation_def,Abbr`sv`] >>
    fs[is_interpretation_def,Abbr`δ`] >>
    metis_tac[typesem_inhabited] ) >>
  `∀ls. EVERY inhabited ls ∧ LENGTH ls = LENGTH argv ⇒ ∃v. v <: mty ls` by (
    gen_tac >> strip_tac >>
    simp[Abbr`mty`,mem_sub] >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    simp[models_def] >>
    fs[satisfies_def] >>
    qabbrev_tac`tt = tv ls` >>
    `is_valuation (tysof ctxt) δ (tt, sv tt)` by (
      simp[Abbr`tt`,is_valuation_def] >>
      conj_asm1_tac >- (
        first_x_assum match_mp_tac >>
        fs[Abbr`argv`] ) >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    disch_then(qspec_then`tt, sv tt`mp_tac)>>simp[] >>
    simp[termsem_def] >> strip_tac >>
    qexists_tac`termsem (sigof ctxt) i (tt, sv tt) witness` >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem) >>
      simp[Abbr`δ`] ) >>
    simp[holds_def,Abbr`mpred`] >> NO_TAC) >>
  `∀τ. typesem ((name =+ mty) δ) τ (typeof witness) = typesem δ τ (typeof witness)` by (
    gen_tac >>
    match_mp_tac typesem_consts >>
    qexists_tac`tysof ctxt` >>
    rw[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
  `∀x. MEM x (tyvars (typeof witness)) ∨ MEM x (tvars pred) ⇔ MEM x (tvars pred)` by (
    rw[] >> imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF,tyvars_def] >>
    metis_tac[]) >>
  `∀τ. tv (MAP τ argv) = (λx. if MEM x (tvars pred) then τ x else boolset)` by (
    simp[Abbr`tv`,FUN_EQ_THM] >> rw[] >- (
      simp[APPLY_UPDATE_LIST_ALOOKUP] >>
      `MEM x argv` by simp[Abbr`argv`] >>
      BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS,MEM_ZIP] >- metis_tac[MEM_EL] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_ZIP] >>
      simp[EL_MAP] ) >>
    `¬MEM x argv` by simp[Abbr`argv`] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP] >>
    BasicProvers.CASE_TAC  >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_ZIP] >> metis_tac[MEM_EL]) >>
  `∀τ y. mpred (λx. if MEM x (tvars pred) then τ x else y) =
         mpred τ` by (
    rpt gen_tac >> simp[Abbr`mpred`] >>
    qmatch_abbrev_tac`termsem sig i (v1,v2) pred = termsem sig i (v3,v4) pred` >>
    `termsem sig i (v1,v2) pred = termsem sig i (v3,v2) pred` by (
      match_mp_tac termsem_tyfrees >>
      fs[Abbr`sig`,Abbr`v1`] ) >>
    `termsem sig i (v3,v2) pred = termsem sig i (v3,v4) pred` by (
      match_mp_tac termsem_frees >>
      fs[CLOSED_def] ) >>
    unabbrev_all_tac >> simp[] ) >>
  `∀τ y. typesem δ (λx. if MEM x (tvars pred) then τ x else y) (typeof witness) =
         typesem δ τ (typeof witness)` by (
    rpt gen_tac >> match_mp_tac typesem_tyvars >> rw[] >> metis_tac[]) >>
  `eqsh (STRING_SORT (tyvars (Fun (typeof witness) abs_type))) argv` by (
    simp[Abbr`argv`,eqsh_def] >>
    qmatch_abbrev_tac`STRING_SORT l1 = STRING_SORT l2` >>
    qsuff_tac`set l1 = set l2` >- (
      simp[EXTENSION] >>
      `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by metis_tac [tvars_ALL_DISTINCT,tyvars_ALL_DISTINCT] >>
      metis_tac[STRING_SORT_EQ,sortingTheory.MEM_PERM,sortingTheory.PERM_ALL_DISTINCT] ) >>
    simp[Abbr`l1`,Abbr`l2`,tyvars_def,Abbr`abs_type`,EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS] ) >>
  `eqsh (STRING_SORT (tyvars (Fun abs_type (typeof witness)))) argv` by (
    simp[Abbr`argv`,eqsh_def] >>
    qmatch_abbrev_tac`STRING_SORT l1 = STRING_SORT l2` >>
    qsuff_tac`set l1 = set l2` >- (
      simp[EXTENSION] >>
      `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by metis_tac [tvars_ALL_DISTINCT,tyvars_ALL_DISTINCT] >>
      metis_tac[STRING_SORT_EQ,sortingTheory.MEM_PERM,sortingTheory.PERM_ALL_DISTINCT] ) >>
    simp[Abbr`l1`,Abbr`l2`,tyvars_def,Abbr`abs_type`,EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS] >>
    imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF,tyvars_def] >>
    metis_tac[]) >>
  qexists_tac`(name =+ mty) δ,
              (abs =+ mabs) ((rep =+ mrep) (tmaof i))` >>
  conj_tac >- (
    simp[term_ok_def,type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >> PROVE_TAC[] ) >>
  conj_asm1_tac >- (
    fs[is_interpretation_def] >>
    conj_asm1_tac >- (
      fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP,Abbr`tys'`,FLOOKUP_UPDATE] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      rw[Abbr`mty`] >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[Abbr`argv`] ) >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP,Abbr`tms'`,FLOOKUP_UPDATE] >>
    rw[combinTheory.APPLY_UPDATE_THM] >- (
      mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
      simp[Abbr`mabs`] >>
      qmatch_abbrev_tac`Abstract a b f <: Funspace c d` >>
      `a = c` by (
        simp[Abbr`a`,Abbr`c`] >>
        match_mp_tac typesem_frees >>
        fs[eqsh_def] >> rw[] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF]) >>
      `b = d` by (
        simp[Abbr`b`,Abbr`d`,Abbr`mty`,Abbr`abs_type`,typesem_def
            ,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
        fs[eqsh_def]) >>
      simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[Abbr`f`,Abbr`c`,Abbr`d`,Abbr`a`,Abbr`b`] >>
      gen_tac >> strip_tac >> BasicProvers.CASE_TAC >- (
        rw[Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF,Abbr`mty`] >>
        simp[mem_sub] >>
        rfs[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS,Abbr`argv`,eqsh_def] ) >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      qexists_tac`tys'` >> simp[] >>
      simp[Abbr`abs_type`,type_ok_def,Abbr`tys'`,FLOOKUP_UPDATE,Abbr`argv`,EVERY_MAP] )
    >- (
      mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
      simp[Abbr`mrep`] >>
      qmatch_abbrev_tac`Abstract a b f <: Funspace c d` >>
      `a = c` by (
        rfs[eqsh_def] >>
        simp[Abbr`a`,Abbr`c`,Abbr`mty`,Abbr`b`,Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM] >>
        simp[MAP_MAP_o,typesem_def,Abbr`d`,tyvars_def,MEM_FOLDR_LIST_UNION,PULL_EXISTS,MEM_MAP,Abbr`argv`,eqsh_def] >>
        fs[DISJ_COMM] ) >>
      `b = d` by (
        rfs[eqsh_def] >>
        simp[Abbr`b`,Abbr`d`,Abbr`mty`,Abbr`abs_type`,typesem_def
            ,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
        simp[tyvars_def,MEM_FOLDR_LIST_UNION] >>
        simp[MEM_MAP,PULL_EXISTS,tyvars_def,Abbr`argv`] >>
        fs[DISJ_COMM]) >>
      simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[Abbr`f`,Abbr`c`,Abbr`d`,Abbr`a`,Abbr`b`] >>
      simp[Abbr`abs_type`,typesem_def,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
      simp[Abbr`mty`,mem_sub] ) >>
    first_x_assum(qspecl_then[`k`,`v`]mp_tac) >>
    simp[] >> disch_then(qspec_then`τ`mp_tac) >>
    simp[] >>
    `typesem ((name =+ mty) δ) τ v = typesem δ τ v` by (
      match_mp_tac typesem_consts >>
      qexists_tac`tysof ctxt` >>
      simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
      fs[theory_ok_def] >>
      reverse(rw[]) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >-
      metis_tac[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
      simp[IN_FRANGE,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    simp[] ) >>
  conj_asm1_tac >- (
    fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,interprets_def] ) >>
  `is_std_sig (tys',tms')` by (
    fs[is_std_sig_def,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] ) >>
  gen_tac >> reverse strip_tac >- (
    match_mp_tac satisfies_extend >>
    fs[entails_def] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    discharge_hyps >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      simp[Abbr`tms'`,SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    conj_tac >- simp[Abbr`tys'`] >>
    match_mp_tac satisfies_consts >>
    qexists_tac`i` >> simp[] >>
    simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    simp[term_ok_def] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  pop_assum mp_tac >>
  simp[conexts_of_upd_def] >>
  strip_tac >- (
    simp[satisfies_def] >>
    gen_tac >> strip_tac >>
    qmatch_abbrev_tac`termsem sig ii v (l1 === l2) = True` >>
    `is_structure sig ii v` by (
      simp[is_structure_def,Abbr`sig`,Abbr`ii`] ) >>
    `term_ok sig (l1 === l2)` by (
      simp[term_ok_equation,Abbr`l1`,Abbr`l2`,term_ok_def] >>
      simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
      simp[Abbr`abs_type`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,Abbr`argv`] >>
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >>
      simp[] ) >>
    simp[termsem_equation,boolean_eq_true] >>
    simp[Abbr`l2`,Abbr`l1`,termsem_def] >>
    qspecl_then[`sig`,`ii`,`abs`]mp_tac instance_def >>
    qspecl_then[`sig`,`ii`,`rep`]mp_tac instance_def >>
    simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
    disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
    disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
    simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
    simp[REV_ASSOCD,typesem_def] >>
    rpt(qpat_assum`eqsh X Y`mp_tac) >>
    simp[eqsh_def] >> ntac 2 (disch_then kall_tac) >>
    simp[Abbr`mrep`,Abbr`argv`,combinTheory.o_DEF,typesem_def,Abbr`abs_type`,Abbr`mty`] >>
    PairCases_on`v` >>
    simp[Abbr`mabs`,ETA_AX] >>
    qmatch_abbrev_tac`Abstract a b f ' (Abstract b a I ' c) = c` >> rfs[] >>
    `c <: b` by (
      fs[is_valuation_def,is_term_valuation_def] >>
      qmatch_assum_abbrev_tac`Abbrev(c = v1 (x,ty))` >>
      first_x_assum(qspecl_then[`x`,`ty`]mp_tac) >>
      simp[Abbr`ty`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,typesem_def,combinTheory.APPLY_UPDATE_THM] >>
      simp[MAP_MAP_o,typesem_def] ) >>
    `c <: a` by rfs[Abbr`b`,mem_sub] >>
    `Abstract b a I ' c = I c` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[] ) >>
    `f c = c` by (
      simp[Abbr`f`] >>
      rfs[Abbr`b`,mem_sub] ) >>
    simp[ETA_AX] >>
    metis_tac[apply_abstract] ) >>
  simp[satisfies_def] >>
  gen_tac >> strip_tac >>
  qmatch_abbrev_tac`termsem sig ii v (l1 === l2) = True` >>
  `is_structure sig ii v` by (
    simp[is_structure_def,Abbr`sig`,Abbr`ii`] ) >>
  qmatch_assum_abbrev_tac`Abbrev(l2 = l3 === l4)` >>
  `term_ok sig (l3 === l4)` by (
    simp[term_ok_equation,Abbr`l3`,Abbr`l4`,term_ok_def] >>
    simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
    simp[Abbr`abs_type`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,Abbr`argv`] >>
    match_mp_tac type_ok_extend >>
    qexists_tac`tysof ctxt` >>
    simp[] ) >>
  `l2 has_type Bool` by (
    simp[Abbr`l2`,EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    rfs[term_ok_equation] >>
    imp_res_tac term_ok_welltyped >> fs[] ) >>
  `term_ok sig (l1 === l2)` by (
    simp[term_ok_equation] >> rfs[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    simp[Abbr`l1`,term_ok_def,Abbr`l4`,Abbr`sig`] >>
    conj_tac >- (
      match_mp_tac term_ok_extend >>
      map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
      simp[Abbr`tms'`,Abbr`tys'`] >>
      simp[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    match_mp_tac type_ok_extend >>
    qexists_tac`tysof ctxt` >>
    simp[Abbr`tys'`] ) >>
  simp[termsem_equation,boolean_eq_true] >>
  imp_res_tac term_ok_welltyped >>
  simp[Abbr`l2`,Abbr`l1`,termsem_def,termsem_equation,Abbr`l4`] >>
  simp[Abbr`l3`,termsem_def] >>
  qspecl_then[`sig`,`ii`,`abs`]mp_tac instance_def >>
  qspecl_then[`sig`,`ii`,`rep`]mp_tac instance_def >>
  simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
  simp[REV_ASSOCD,typesem_def] >>
  Q.PAT_ABBREV_TAC`mpred' = termsem X Y v pred` >>
  `mpred' = mpred (tyvof v)` by (
    simp[Abbr`mpred`,Abbr`mpred'`] >>
    qmatch_abbrev_tac`termsem sig ii v pred = x` >>
    `termsem sig ii v pred = termsem (sigof ctxt) ii v pred` by (
      simp[Abbr`sig`] >>
      match_mp_tac termsem_extend >>
      simp[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    `termsem (sigof ctxt) ii v pred = termsem (sigof ctxt) i v pred` by (
      match_mp_tac termsem_consts >>
      simp[type_ok_def,term_ok_def,Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    simp[Abbr`x`] >>
    match_mp_tac termsem_frees >>
    fs[CLOSED_def] ) >>
  rpt(qpat_assum`eqsh X Y`mp_tac) >>
  simp[eqsh_def] >> ntac 2 (disch_then kall_tac) >>
  simp[Abbr`mrep`,Abbr`argv`,combinTheory.o_DEF,typesem_def,Abbr`abs_type`,Abbr`mty`] >>
  PairCases_on`v` >>
  simp[Abbr`mabs`,ETA_AX] >>
  qmatch_abbrev_tac`f ' x = Boolean (Abstract a b I ' (Abstract b a g ' x) = x)` >>
  rfs[ETA_AX] >>
  `f <: typesem (tyaof i) v0 (typeof pred)` by (
    simp_tac std_ss [Abbr`f`,Abbr`mpred`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    fs[Abbr`δ`,is_valuation_def] ) >>
  pop_assum mp_tac >>
  mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
  strip_tac >>
  `x <: b` by (
    simp[Abbr`x`,Abbr`b`] >>
    fs[is_valuation_def,is_term_valuation_def] >>
    first_x_assum (qspecl_then[`"r"`,`typeof witness`]mp_tac) >>
    discharge_hyps >- (
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >> simp[] ) >>
    simp[] ) >>
  `f ' x <: boolset` by (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`b` >>
    metis_tac[typesem_Bool] ) >>
  `inhabited a` by (
    simp[Abbr`a`] >>
    first_x_assum(qspec_then`MAP v0 (STRING_SORT (tvars pred))`mp_tac) >>
    discharge_hyps >- (
      simp[EVERY_MAP,EVERY_MEM] >>
      fs[is_valuation_def,is_type_valuation_def] ) >>
    simp[] ) >>
  `Abstract b a g ' x = g x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    simp[Abbr`g`] >> rw[] >- simp[Abbr`a`,mem_sub] >>
    SELECT_ELIM_TAC >> simp[] >>
    metis_tac[] ) >>
  simp[Abbr`g`] >>
  Cases_on`f ' x = True` >- (
    simp[holds_def,boolean_eq_true] >>
    `Abstract a b I ' x = I x` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[Abbr`a`,mem_sub,holds_def] ) >>
    simp[] ) >>
  simp[holds_def,boolean_def] >>
  `Abstract a b I ' (@v. v <: a) = I (@v. v <: a)` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[] >>
    simp[Abbr`a`,mem_sub] ) >>
  simp[] >>
  `f ' (@v. v <: a) = True` by (
    SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
    simp[Abbr`a`,mem_sub,holds_def] ) >>
  metis_tac[mem_boolset])
val _ = delete_const"eqsh"

val updates_consistent = store_thm("updates_consistent",
  ``is_set_theory ^mem ⇒
    ∀upd ctxt. upd updates ctxt ⇒
      theory_ok (thyof ctxt) ∧ (∀p. upd ≠ NewAxiom p) ⇒
      consistent_update ctxt upd``,
  strip_tac >>
  ho_match_mp_tac updates_ind >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[update_distinct,new_constant_correct] >>
  conj_tac >- metis_tac[update_distinct,new_specification_correct] >>
  conj_tac >- metis_tac[update_distinct,new_type_correct] >>
  metis_tac[update_distinct,new_type_definition_correct])

val subinterpretation_reduce = store_thm("subinterpretation_reduce",
  ``∀ls ctxt i i'. subinterpretation (ls++ctxt) i i' ∧
                 DISJOINT (FDOM (tysof ls)) (FDOM (tysof ctxt)) ∧
                 DISJOINT (FDOM (tmsof ls)) (FDOM (tmsof ctxt))
    ⇒ subinterpretation ctxt i i'``,
  rw[subinterpretation_def] >>
  first_x_assum match_mp_tac >|
  [qexists_tac`args`>>
   match_mp_tac type_ok_extend >>
   qexists_tac`tysof ctxt`
  ,qexists_tac`ty` >>
   match_mp_tac term_ok_extend >>
   qexists_tac`tysof ctxt` >>
   qexists_tac`tmsof ctxt`] >>
  simp[] >>
  TRY conj_tac >>
  match_mp_tac SUBMAP_FUNION >>
  fs[IN_DISJOINT] >>
  metis_tac[])

val subinterpretation_trans = store_thm("subinterpretation_trans",
  ``∀ctxt i1 i2 i3. subinterpretation ctxt i1 i2 ∧ subinterpretation ctxt i2 i3
    ⇒ subinterpretation ctxt i1 i3``,
  rw[subinterpretation_def] >> metis_tac[])

val subinterpretation_refl = store_thm("subinterpretation_refl",
  ``∀ctxt i. subinterpretation ctxt i i``,
  rw[subinterpretation_def])

val extends_consistent = store_thm("extends_consistent",
  ``is_set_theory ^mem ⇒
    ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      ∀i. theory_ok (thyof ctxt1) ∧ i models (thyof ctxt1) ∧
          (∀p. MEM (NewAxiom p) ctxt2 ⇒ MEM (NewAxiom p) ctxt1)
        ⇒
        ∃i'. subinterpretation ctxt1 i i' ∧ i' models (thyof ctxt2)``,
  rw[] >>
  Q.ISPEC_THEN
    `λctxt. theory_ok (thyof ctxt) ∧
            ∃ls. ctxt = ls ++ ctxt1 ∧
                 DISJOINT (FDOM (tysof ls)) (FDOM (tysof ctxt1)) ∧
                 DISJOINT (FDOM (tmsof ls)) (FDOM (tmsof ctxt1)) ∧
              ((∀p. MEM (NewAxiom p) ls ⇒ MEM (NewAxiom p) ctxt1) ⇒
               ∃i'. subinterpretation ctxt1 i i' ∧
                    i' models (thyof ctxt))`
    mp_tac extends_ind >>
  discharge_hyps >- (
    rpt gen_tac >> strip_tac >>
    full_simp_tac std_ss [] >>
    conj_asm1_tac >- metis_tac[updates_theory_ok] >>
    qexists_tac`upd::ls` >> simp_tac std_ss [APPEND] >>
    conj_asm1_tac >- fs[updates_cases] >>
    conj_asm1_tac >- (
      fs[updates_cases,LET_THM] >>
      fs[IN_DISJOINT,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
      metis_tac[] ) >>
    strip_tac >>
    full_simp_tac std_ss [MEM] >>
    reverse(Cases_on`∃p. upd = NewAxiom p`) >- (
      imp_res_tac updates_consistent >> pop_assum kall_tac >>
      pop_assum mp_tac >> discharge_hyps >- metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      disch_then(imp_res_tac o SIMP_RULE std_ss [consistent_update_def]) >>
      qmatch_assum_rename_tac`z models thyof (upd::(ls++ctxt1))`[] >>
      qexists_tac`z` >> simp[] >>
      match_mp_tac subinterpretation_trans >>
      qmatch_assum_rename_tac`subinterpretation ctxt1 i m`[] >>
      qexists_tac`m` >> simp[] >>
      match_mp_tac subinterpretation_reduce >>
      qexists_tac`ls` >> fs[IN_DISJOINT] ) >>
    qmatch_assum_rename_tac`j models thyof ctxt`[] >>
    qexists_tac`j` >>
    rfs[models_def,conexts_of_upd_def] >>
    `MEM p (axiom_list ctxt1)` by (
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      qexists_tac`NewAxiom p` >> simp[] ) >>
    metis_tac[]) >>
  disch_then(qspecl_then[`ctxt1`,`ctxt2`]mp_tac) >>
  simp[PULL_EXISTS] >>
  disch_then(qspec_then`i`mp_tac) >> simp[subinterpretation_refl] >>
  strip_tac >>
  first_x_assum match_mp_tac >>
  fs[EVERY_MEM])

val min_hol_consistent = store_thm("min_hol_consistent",
  ``is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt ∧ (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) init_ctxt) ⇒
      (thyof ctxt,[]) |- (Var "x" Bool === Var "x" Bool) ∧
      ¬((thyof ctxt,[]) |- (Var "x" Bool === Var "y" Bool))``,
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[extends_theory_ok,extends_consistent,init_theory_ok,init_ctxt_has_model])

val _ = export_theory()
