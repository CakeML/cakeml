(*
  Proves soundness of the context extension rules: any model of a context can
  be extended to a model of the context obtained by applying one of the
  non-axiomatic context updates.
*)
open preamble mlstringTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory

val _ = new_theory"holExtension"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val sound_update_def = xDefine"sound_update"`
  sound_update0 ^mem ctxt upd ⇔
    ∀i. i models (thyof ctxt) ⇒
      ∃i'. equal_on (sigof ctxt) i i' ∧
           i' models (thyof (upd::ctxt))`
val _ = Parse.overload_on("sound_update",``sound_update0 ^mem``)

Theorem new_constant_correct:
   is_set_theory ^mem ⇒
    ∀ctxt name ty.
     theory_ok (thyof ctxt) ∧
     name ∉ (FDOM (tmsof ctxt)) ∧
     type_ok (tysof ctxt) ty ⇒
     sound_update ctxt (NewConst name ty)
Proof
  rw[] >> REWRITE_TAC[sound_update_def,equal_on_def] >>
  gen_tac >> strip_tac >>
  qexists_tac`(tyaof i,
    (name =+ λl. @v. v <: typesem (tyaof i) ((K boolset) =++
      (REVERSE(ZIP((MAP implode (STRING_SORT (MAP explode (tyvars ty))),l))))) ty)
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
      rw[MAP_MAP_o,combinTheory.o_DEF] >> BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode]) >>
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
  match_mp_tac satisfies_sig >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  simp[equal_on_def] >>
  metis_tac[]
QED

Theorem new_specification_correct:
   is_set_theory ^mem ⇒
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
    sound_update ctxt (ConstSpec eqs prop)
Proof
  rw[] >> REWRITE_TAC[sound_update_def,equal_on_def] >>
  gen_tac >> strip_tac >>
  qexists_tac`(tyaof i,
    (tmaof i) =++
      MAP (λ(s,t). (s, λl. termsem (tmsof ctxt) i ((K boolset)=++(REVERSE(ZIP(MAP implode (STRING_SORT(MAP explode(tyvars(typeof t)))),l))),ARB) t))
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
    qmatch_abbrev_tac`termsem (tmsof ctxt) i t1 t <: x` >>
    imp_res_tac theory_ok_sig >>
    `termsem (tmsof ctxt) i t1 t = termsem (tmsof ctxt) i (τ,SND t1) t` by (
      match_mp_tac termsem_tyfrees >> qexists_tac`sigof ctxt` >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac proves_term_ok >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] >>
      rfs[term_ok_equation] >>
      conj_tac >- metis_tac[] >>
      rw[Abbr`t1`,APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >> metis_tac[] ) >>
    `is_valuation (tysof ctxt) (tyaof i) (τ,λ(x,ty). @v. v <: typesem (tyaof i) τ ty)` by (
      fs[is_valuation_def,is_term_valuation_def] >> rw[] >>
      SELECT_ELIM_TAC >> simp[] >>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[] >> metis_tac[] ) >>
    qmatch_assum_abbrev_tac`is_valuation tyenv δ v` >>
    `termsem (tmsof ctxt) i (τ,tmvof t1) t = termsem (tmsof ctxt) i v t` by (
      match_mp_tac termsem_frees >>
      simp[Abbr`v`] >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac proves_term_ok >>
      fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,CLOSED_def] >>
      rfs[term_ok_equation] >>
      metis_tac[term_ok_welltyped] ) >>
    rw[Abbr`x`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    unabbrev_all_tac >> simp[] >>
    fs[is_interpretation_def] >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    imp_res_tac is_std_interpretation_is_type >> simp[] >>
    imp_res_tac proves_term_ok >>
    qexists_tac`sigof ctxt` >>
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
    impl_tac >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      match_mp_tac SUBMAP_FUNION >>
      fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,ETA_AX,UNCURRY] >>
      metis_tac[] ) >>
    match_mp_tac satisfies_sig >>
    qexists_tac`i` >> simp[equal_on_def] >>
    simp[term_ok_def,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac proves_sound >> pop_assum mp_tac >>
  rw[entails_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  impl_tac >- fs[models_def] >>
  rw[satisfies_def] >>
  qmatch_abbrev_tac`termsem tmenv ii v (VSUBST ilist tm) = True` >>
  qspecl_then[`tm`,`ilist`]mp_tac termsem_VSUBST >>
  impl_tac >- (
    simp[welltyped_def,Abbr`ilist`,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    metis_tac[has_type_rules] ) >>
  simp[] >> disch_then kall_tac >>
  qmatch_abbrev_tac`termsem tmenv ii vv tm = True` >>
  `tmsof ctxt ⊑ tmenv` by (
    simp[Abbr`tmenv`] >>
    match_mp_tac SUBMAP_FUNION >>
    fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    metis_tac[] ) >>
  `termsem tmenv ii vv tm = termsem (tmsof ctxt) ii vv tm` by (
    metis_tac[termsem_extend] ) >>
  `termsem (tmsof ctxt) ii vv tm = termsem (tmsof ctxt) i vv tm` by (
    match_mp_tac termsem_sig >>
    qexists_tac`sigof ctxt` >>
    simp[Abbr`ii`,equal_on_def] >>
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
    rpt (qpat_x_assum `termsem X Y Z tm = A`kall_tac) >>
    qmatch_abbrev_tac`instance tmenv ii name ty τ <: x` >>
    qspecl_then[`tmenv`,`ii`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`tmenv`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
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
    qmatch_abbrev_tac`termsem tmenv i (v1,v2) tt <: tysem` >>
    qmatch_assum_abbrev_tac`is_valuation (tysof ctxt) (tyaof i) (τ,σ)` >>
    `termsem tmenv i (v1,v2) tt = termsem tmenv i (τ,v2) tt` by (
      match_mp_tac termsem_tyfrees >>
      qexists_tac`sigof ctxt` >>
      simp[Abbr`v1`,REV_ASSOCD,typesem_def,Abbr`tmenv`] >>
      imp_res_tac theory_ok_sig >>
      fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      conj_tac >- metis_tac[] >>
      simp[APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
      rw[MAP_MAP_o,combinTheory.o_DEF] >>
      BasicProvers.CASE_TAC >> fs[ALOOKUP_FAILS] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD,Abbr`ty`,mlstringTheory.implode_explode] >>
      rw[typesem_def] >> metis_tac[mlstringTheory.implode_explode]) >>
    `termsem tmenv i (τ,v2) tt = termsem tmenv i (τ,σ) tt` by (
       match_mp_tac termsem_frees >>
       imp_res_tac proves_term_ok >>
       fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,CLOSED_def,MEM_MAP,PULL_EXISTS] >>
       imp_res_tac theory_ok_sig >>
       fs[term_ok_equation] >>
       metis_tac[term_ok_welltyped] ) >>
    rw[Abbr`tysem`,Abbr`ty`,Abbr`x`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >>
    fs[Abbr`tmenv`] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
    metis_tac[] ) >>
  imp_res_tac theory_ok_sig >>
  `is_structure (sigof ctxt) i vv` by (
    fs[is_structure_def] ) >>
  simp[EVERY_MAP,EVERY_MEM,FORALL_PROD] >> rw[] >>
  fs[EVERY_MAP,LAMBDA_PROD,EVERY_MEM,FORALL_PROD] >>
  `tmsof ctxt = tmsof (sigof ctxt)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true,termsem_def] >>
  simp[Abbr`vv`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,Abbr`ilist`,EXISTS_PROD,PULL_EXISTS] >>
  simp[termsem_def] >>
  qmatch_abbrev_tac`instance tmenv ii name ty τ = X` >>
  qspecl_then[`tmenv`,`ii`,`name`,`ty`]mp_tac instance_def >>
  simp[Abbr`tmenv`,FLOOKUP_FUNION,ALOOKUP_MAP] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  simp[Abbr`X`,Abbr`ii`,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE,ALOOKUP_MAP] >>
  qmatch_abbrev_tac`termsem tmenv i (v1,v2) tt = termsem tmenv i (v3,v4) tt` >>
  `termsem tmenv i (v1,v2) tt = termsem tmenv i (v3,v2) tt` by (
    match_mp_tac termsem_tyfrees >>
    qexists_tac`sigof ctxt` >>
    simp[Abbr`v1`,REV_ASSOCD,typesem_def] >>
    imp_res_tac theory_ok_sig >>
    fs[EVERY_MAP,term_ok_equation,LAMBDA_PROD] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    conj_tac >- metis_tac[]>>
    simp[APPLY_UPDATE_LIST_ALOOKUP,ZIP_MAP] >>
    rw[MAP_MAP_o,combinTheory.o_DEF] >>
    BasicProvers.CASE_TAC >> fs[ALOOKUP_FAILS] >>
    imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD,mlstringTheory.implode_explode] >>
    rw[typesem_def] >> metis_tac[mlstringTheory.implode_explode]) >>
  `termsem tmenv i (v3,v2) tt = termsem tmenv i (v3,v4) tt` by (
    match_mp_tac termsem_frees >> simp[] >>
    imp_res_tac proves_term_ok >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,CLOSED_def,MEM_MAP,PULL_EXISTS] >>
    imp_res_tac theory_ok_sig >> fs[term_ok_equation] >>
    metis_tac[term_ok_welltyped] ) >>
  rw[Abbr`v4`]
QED

Theorem new_definition_correct:
   is_set_theory ^mem ⇒
    ∀ctxt name tm.
    theory_ok (thyof ctxt) ∧
    term_ok (sigof ctxt) tm ∧
    name ∉ FDOM (tmsof ctxt) ∧
    CLOSED tm ∧
    set (tvars tm) ⊆ set (tyvars (typeof tm))
    ⇒ sound_update ctxt (ConstDef name tm)
Proof
  rw[] >>
  ho_match_mp_tac (UNDISCH new_specification_correct) >>
  simp[] >> fs[SUBSET_DEF,CLOSED_def,vfree_in_equation] >>
  ho_match_mp_tac(proves_rules |> CONJUNCTS |> el 2) >>
  imp_res_tac theory_ok_sig >>
  fs[EQUATION_HAS_TYPE_BOOL,term_ok_equation,term_ok_def] >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac term_ok_type_ok >> fs[]
QED

Theorem new_type_correct:
   is_set_theory ^mem ⇒
    ∀ctxt name arity.
     theory_ok (thyof ctxt) ∧
     name ∉ FDOM (tysof ctxt) ⇒
     sound_update ctxt (NewType name arity)
Proof
  rw[] >> REWRITE_TAC[sound_update_def,equal_on_def] >>
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
      match_mp_tac typesem_sig >>
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
  match_mp_tac satisfies_sig >>
  imp_res_tac theory_ok_sig >>
  qexists_tac`i` >> simp[equal_on_def] >>
  conj_tac >- (Cases_on`ctxt`>>fs[]) >>
  conj_tac >- fs[theory_ok_def] >>
  rw[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[]
QED

val eqsh_def = new_definition("eqsh",``eqsh = $=``)
Theorem new_type_definition_correct:
   is_set_theory ^mem ⇒
    ∀ctxt name pred abs rep witness.
    (thyof ctxt,[]) |- Comb pred witness ∧
    CLOSED pred ∧
    name ∉ (FDOM (tysof ctxt)) ∧
    abs ∉ (FDOM (tmsof ctxt)) ∧
    rep ∉ (FDOM (tmsof ctxt)) ∧
    abs ≠ rep ⇒
    sound_update ctxt (TypeDefn name pred abs rep)
Proof
  rw[sound_update_def,equal_on_def,models_def,LET_THM] >>
  Q.PAT_ABBREV_TAC`tys' = tysof ctxt |+ X` >>
  Q.PAT_ABBREV_TAC`tms' = tmsof ctxt |+ X |+ Y` >>
  imp_res_tac WELLTYPED_LEMMA >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac theory_ok_sig >> fs[] >>
  `name ∉ {strlit "fun";strlit "bool"} ∧ abs ≠ strlit "=" ∧ rep ≠ strlit "="` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >> fs[] >>
  qmatch_assum_abbrev_tac`Abbrev(tms' = tmsof ctxt |+ (rep, Fun abs_type rep_type) |+ Y)` >>
  qunabbrev_tac`Y` >>
  qabbrev_tac`argv = MAP implode (STRING_SORT (MAP explode (tvars pred)))` >>
  qabbrev_tac`tv:'U list -> 'U tyval = λargs a.
    (K boolset =++ (REVERSE(ZIP((MAP implode (STRING_SORT(MAP explode(tvars pred))),args))))) a` >>
  qabbrev_tac`δ = tyaof i` >>
  qabbrev_tac`sv:'U tyval->'U tmval = λτ (x,ty). @v. v <: typesem δ τ ty` >>
  qabbrev_tac`mpred = λτ. termsem (tmsof ctxt) i (τ, sv τ) pred` >>
  qabbrev_tac`mty = λargs. typesem δ (tv args) rep_type suchthat Holds (mpred (tv args))` >>
  qabbrev_tac`mrep = λargs. Abstract (mty args) (typesem δ (tv args) rep_type)  I` >>
  qabbrev_tac`mabs = λargs. Abstract (typesem δ (tv args) rep_type) (mty args)
                           (λv. if Holds (mpred (tv args)) v then v else @v. v <: mty args)` >>
  imp_res_tac proves_sound >>
  imp_res_tac proves_term_ok >>
  fs[term_ok_def] >>
  `pred has_type Fun rep_type Bool` by (
    qhdtm_x_assum`$has_type`mp_tac >>
    simp[Once has_type_cases] >>
    rw[Abbr`rep_type`] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] ) >>
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
    qexists_tac`termsem (tmsof ctxt) i (tt, sv tt) witness` >>
    conj_tac >- (
      simp[Abbr`rep_type`] >>
      match_mp_tac (UNDISCH termsem_typesem) >>
      qexists_tac`sigof ctxt` >>
      simp[Abbr`δ`] ) >>
    simp[holds_def,Abbr`mpred`] >> NO_TAC) >>
  `∀τ. typesem ((name =+ mty) δ) τ (typeof witness) = typesem δ τ (typeof witness)` by (
    gen_tac >>
    match_mp_tac typesem_sig >>
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
      `MEM x argv` by simp[Abbr`argv`,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >>
      BasicProvers.CASE_TAC >>
      fs[ALOOKUP_FAILS,MEM_ZIP] >- metis_tac[MEM_EL] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_ZIP] >>
      simp[EL_MAP] ) >>
    `¬MEM x argv` by simp[Abbr`argv`,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode] >>
    simp[APPLY_UPDATE_LIST_ALOOKUP] >>
    BasicProvers.CASE_TAC  >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_ZIP] >> metis_tac[MEM_EL]) >>
  `∀τ y. mpred (λx. if MEM x (tvars pred) then τ x else y) =
         mpred τ` by (
    rpt gen_tac >> simp[Abbr`mpred`] >>
    qmatch_abbrev_tac`termsem tmenv i (v1,v2) pred = termsem tmenv i (v3,v4) pred` >>
    `termsem tmenv i (v1,v2) pred = termsem tmenv i (v3,v2) pred` by (
      match_mp_tac termsem_tyfrees >>
      qexists_tac`sigof ctxt` >>
      fs[Abbr`tmenv`,Abbr`v1`] ) >>
    `termsem tmenv i (v3,v2) pred = termsem tmenv i (v3,v4) pred` by (
      match_mp_tac termsem_frees >>
      fs[CLOSED_def] ) >>
    unabbrev_all_tac >> simp[] ) >>
  `∀τ y. typesem δ (λx. if MEM x (tvars pred) then τ x else y) (typeof witness) =
         typesem δ τ (typeof witness)` by (
    rpt gen_tac >> match_mp_tac typesem_tyvars >> rw[] >> metis_tac[]) >>
  `eqsh (MAP implode (STRING_SORT (MAP explode (tyvars (Fun (typeof witness) abs_type))))) argv` by (
    simp[Abbr`argv`,eqsh_def] >>
    AP_TERM_TAC >>
    qmatch_abbrev_tac`STRING_SORT l1 = STRING_SORT l2` >>
    qsuff_tac`set l1 = set l2` >- (
      simp[EXTENSION] >>
      `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by metis_tac [tvars_ALL_DISTINCT,tyvars_ALL_DISTINCT,ALL_DISTINCT_MAP_explode] >>
      metis_tac[STRING_SORT_EQ,sortingTheory.MEM_PERM,sortingTheory.PERM_ALL_DISTINCT] ) >>
    simp[Abbr`l1`,Abbr`l2`,tyvars_def,Abbr`abs_type`,EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS] >>
    rw[EQ_IMP_THM] >>rw[mlstringTheory.explode_11,mlstringTheory.implode_explode] >>
    metis_tac[]) >>
  `eqsh (MAP implode (STRING_SORT (MAP explode (tyvars (Fun abs_type (typeof witness)))))) argv` by (
    simp[Abbr`argv`,eqsh_def] >>
    AP_TERM_TAC >>
    qmatch_abbrev_tac`STRING_SORT l1 = STRING_SORT l2` >>
    qsuff_tac`set l1 = set l2` >- (
      simp[EXTENSION] >>
      `ALL_DISTINCT l1 ∧ ALL_DISTINCT l2` by metis_tac [tvars_ALL_DISTINCT,tyvars_ALL_DISTINCT,ALL_DISTINCT_MAP_explode] >>
      metis_tac[STRING_SORT_EQ,sortingTheory.MEM_PERM,sortingTheory.PERM_ALL_DISTINCT] ) >>
    simp[Abbr`l1`,Abbr`l2`,tyvars_def,Abbr`abs_type`,EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP,PULL_EXISTS] >>
    imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF,tyvars_def] >>
    rw[EQ_IMP_THM] >>rw[mlstringTheory.explode_11,mlstringTheory.implode_explode] >>
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
        simp[Abbr`a`,Abbr`c`,Abbr`rep_type`] >>
        match_mp_tac typesem_frees >>
        fs[eqsh_def] >> rw[] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF]) >>
      `b = d` by (
        simp[Abbr`b`,Abbr`d`,Abbr`mty`,Abbr`abs_type`,Abbr`rep_type`,typesem_def
            ,combinTheory.APPLY_UPDATE_THM,combinTheory.o_DEF] >>
        fs[eqsh_def,Abbr`c`] >>
        fs[MAP_MAP_o,combinTheory.o_DEF,combinTheory.APPLY_UPDATE_THM,typesem_def]) >>
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
        fs[DISJ_COMM,combinTheory.o_DEF,MAP_MAP_o,typesem_def,combinTheory.APPLY_UPDATE_THM] ) >>
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
      simp[Abbr`mty`,Abbr`rep_type`,mem_sub] ) >>
    first_x_assum(qspecl_then[`k`,`v`]mp_tac) >>
    simp[] >> disch_then(qspec_then`τ`mp_tac) >>
    simp[] >>
    `typesem ((name =+ mty) δ) τ v = typesem δ τ v` by (
      match_mp_tac typesem_sig >>
      qexists_tac`tysof ctxt` >>
      simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
      fs[theory_ok_def] >>
      rw[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
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
    impl_tac >- fs[models_def] >> strip_tac >>
    map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
    fs[theory_ok_def] >>
    conj_tac >- (
      simp[Abbr`tms'`,SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      rw[] ) >>
    conj_tac >- simp[Abbr`tys'`] >>
    match_mp_tac satisfies_sig >>
    qexists_tac`i` >> simp[equal_on_def] >>
    simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    simp[term_ok_def] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  pop_assum mp_tac >>
  simp[conexts_of_upd_def] >>
  fs[] >> rfs[] >>
  strip_tac >- (
    simp[satisfies_def] >>
    gen_tac >> strip_tac >>
    qmatch_abbrev_tac`termsem tms' ii v (l1 === l2) = True` >>
    qmatch_assum_abbrev_tac`is_std_sig sig` >>
    `is_structure sig ii v` by (
      simp[is_structure_def,Abbr`sig`,Abbr`ii`] ) >>
    `term_ok sig (l1 === l2)` by (
      simp[term_ok_equation,Abbr`l1`,Abbr`l2`,term_ok_def] >>
      simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
      simp[Abbr`abs_type`,Abbr`rep_type`,type_ok_def,FLOOKUP_UPDATE,EVERY_MAP,Abbr`argv`] >>
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >>
      simp[] ) >>
    `tms' = tmsof sig` by simp[Abbr`sig`] >> pop_assum SUBST1_TAC >>
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true] >>
    simp[Abbr`l2`,Abbr`l1`,termsem_def] >>
    qspecl_then[`tmsof sig`,`ii`,`abs`]mp_tac instance_def >>
    qspecl_then[`tmsof sig`,`ii`,`rep`]mp_tac instance_def >>
    simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
    disch_then(qspec_then`[]`mp_tac)>>CHANGED_TAC(simp[]) >> disch_then kall_tac >>
    disch_then(qspec_then`[]`mp_tac)>>CHANGED_TAC(simp[]) >> disch_then kall_tac >>
    Q.PAT_ABBREV_TAC`l1 = STRING_SORT X` >>
    Q.PAT_ABBREV_TAC`l2 = STRING_SORT X` >>
    simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
    CHANGED_TAC(simp[REV_ASSOCD,typesem_def]) >>
    simp[GSYM combinTheory.o_DEF,GSYM MAP_MAP_o] >>
    rpt(qpat_x_assum`eqsh X Y`mp_tac) >>
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
      simp[MAP_MAP_o,typesem_def,combinTheory.o_DEF] >>
      simp[GSYM combinTheory.o_DEF,GSYM MAP_MAP_o]) >>
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
  qmatch_abbrev_tac`termsem tms' ii v (l1 === l2) = True` >>
  qmatch_assum_abbrev_tac`is_std_sig sig` >>
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
  `tms' = tmsof sig` by simp[Abbr`sig`] >> pop_assum SUBST1_TAC >>
  simp[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true] >>
  imp_res_tac term_ok_welltyped >>
  simp[Abbr`l2`,Abbr`l1`,termsem_def,SIMP_RULE std_ss [] termsem_equation,Abbr`l4`] >>
  simp[Abbr`l3`,termsem_def] >>
  qspecl_then[`tmsof sig`,`ii`,`abs`]mp_tac instance_def >>
  qspecl_then[`tmsof sig`,`ii`,`rep`]mp_tac instance_def >>
  simp[Abbr`sig`,Abbr`tms'`,Abbr`tys'`,FLOOKUP_UPDATE] >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  disch_then(qspec_then`[]`mp_tac)>>simp[] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`l1 = STRING_SORT X` >>
  Q.PAT_ABBREV_TAC`l2 = STRING_SORT X` >>
  simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM,MAP_MAP_o,combinTheory.o_DEF] >>
  CHANGED_TAC(simp[REV_ASSOCD,typesem_def]) >>
  simp[GSYM combinTheory.o_DEF,GSYM MAP_MAP_o] >>
  Q.PAT_ABBREV_TAC`mpred' = termsem X Y v pred` >>
  `mpred' = mpred (tyvof v)` by (
    simp[Abbr`mpred`,Abbr`mpred'`] >>
    qmatch_abbrev_tac`termsem tmenv ii v pred = x` >>
    `termsem tmenv ii v pred = termsem (tmsof ctxt) ii v pred` by (
      simp[Abbr`tmenv`] >>
      match_mp_tac termsem_extend >>
      simp[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
      qexists_tac`tysof ctxt` >>
      rw[] ) >>
    `termsem (tmsof ctxt) ii v pred = termsem (tmsof ctxt) i v pred` by (
      match_mp_tac termsem_sig >>
      qexists_tac`sigof ctxt` >>
      simp[equal_on_def,type_ok_def,term_ok_def,Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    simp[Abbr`x`] >>
    match_mp_tac termsem_frees >>
    fs[CLOSED_def] ) >>
  rpt(qpat_x_assum`eqsh X Y`mp_tac) >>
  simp[eqsh_def] >> ntac 2 (disch_then kall_tac) >>
  simp[Abbr`mrep`,Abbr`argv`,combinTheory.o_DEF,typesem_def,Abbr`abs_type`,Abbr`mty`] >>
  PairCases_on`v` >>
  simp[Abbr`mabs`,ETA_AX] >>
  qmatch_abbrev_tac`f ' x = Boolean (Abstract a b I ' (Abstract b a g ' x) = x)` >>
  rfs[ETA_AX] >>
  `f <: typesem (tyaof i) v0 (typeof pred)` by (
    simp_tac std_ss [Abbr`f`,Abbr`mpred`] >>
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >>
    fs[Abbr`δ`,is_valuation_def] ) >>
  pop_assum mp_tac >>
  mp_tac typesem_Fun >> simp[] >> disch_then kall_tac >>
  strip_tac >>
  `x <: b` by (
    simp[Abbr`x`,Abbr`b`] >>
    fs[is_valuation_def,is_term_valuation_def] >>
    first_x_assum (qspecl_then[`strlit "r"`,`typeof witness`]mp_tac) >>
    impl_tac >- (
      match_mp_tac type_ok_extend >>
      qexists_tac`tysof ctxt` >> simp[] ) >>
    simp[] ) >>
  `f ' x <: boolset` by (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`b` >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rfs[] >>
    metis_tac[typesem_Bool] ) >>
  `inhabited a` by (
    simp[Abbr`a`] >>
    first_x_assum(qspec_then`MAP v0 (MAP implode (STRING_SORT (MAP explode (tvars pred))))`mp_tac) >>
    impl_tac >- (
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
  metis_tac[mem_boolset]
QED
val _ = delete_const"eqsh"

Theorem updates_consistent:
   is_set_theory ^mem ⇒
    ∀upd ctxt. upd updates ctxt ⇒
      theory_ok (thyof ctxt) ∧ (∀p. upd ≠ NewAxiom p) ⇒
      sound_update ctxt upd
Proof
  strip_tac >>
  ho_match_mp_tac updates_ind >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[update_distinct,new_constant_correct] >>
  conj_tac >- metis_tac[update_distinct,new_specification_correct] >>
  conj_tac >- metis_tac[update_distinct,new_type_correct] >>
  metis_tac[update_distinct,new_type_definition_correct]
QED

Theorem extends_consistent:
   is_set_theory ^mem ⇒
    ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      ∀i. theory_ok (thyof ctxt1) ∧ i models (thyof ctxt1) ∧
          (∀p. MEM (NewAxiom p) ctxt2 ⇒ MEM (NewAxiom p) ctxt1)
        ⇒
        ∃i'. equal_on (sigof ctxt1) i i' ∧ i' models (thyof ctxt2)
Proof
  rw[] >>
  Q.ISPEC_THEN
    `λctxt. theory_ok (thyof ctxt) ∧
            ∃ls. ctxt = ls ++ ctxt1 ∧
                 DISJOINT (FDOM (tysof ls)) (FDOM (tysof ctxt1)) ∧
                 DISJOINT (FDOM (tmsof ls)) (FDOM (tmsof ctxt1)) ∧
              ((∀p. MEM (NewAxiom p) ls ⇒ MEM (NewAxiom p) ctxt1) ⇒
               ∃i'. equal_on (sigof ctxt1) i i' ∧
                    i' models (thyof ctxt))`
    mp_tac extends_ind >>
  impl_tac >- (
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
      pop_assum mp_tac >> impl_tac >- metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      disch_then(imp_res_tac o SIMP_RULE std_ss [sound_update_def]) >>
      qmatch_assum_rename_tac`z models thyof (upd::(ls++ctxt1))` >>
      qexists_tac`z` >> simp[] >>
      match_mp_tac equal_on_trans >>
      qmatch_assum_rename_tac`equal_on (sigof ctxt1) i m` >>
      qexists_tac`m` >> simp[] >>
      match_mp_tac equal_on_reduce >>
      qexists_tac`ls` >> fs[IN_DISJOINT] ) >>
    qmatch_assum_rename_tac`j models thyof ctxt` >>
    qexists_tac`j` >>
    rfs[models_def,conexts_of_upd_def] >>
    `MEM p (axiom_list ctxt1)` by (
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      qexists_tac`NewAxiom p` >> simp[] ) >>
    metis_tac[]) >>
  disch_then(qspecl_then[`ctxt1`,`ctxt2`]mp_tac) >>
  simp[PULL_EXISTS] >>
  disch_then(qspec_then`i`mp_tac) >> simp[equal_on_refl] >>
  strip_tac >>
  first_x_assum match_mp_tac >>
  fs[EVERY_MEM]
QED

val _ = export_theory()
