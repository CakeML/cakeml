open HolKernel boolLib bossLib lcsymtacs miscLib
open miscTheory finite_mapTheory alistTheory listTheory pairTheory
open holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory holExtensionTheory
val _ = new_theory"holConstrainedExtension"

val constrain_assignment_def = Define`
  constrain_assignment cs f =
    λname args. case cs name args of SOME x => x | NONE => f name args`

val constrain_interpretation_def = Define`
  constrain_interpretation (tycs,tmcs) ((δ,γ):'U interpretation) =
    (constrain_assignment tycs δ,
     constrain_assignment tmcs γ)`

val add_constraints_thm = store_thm("add_constraints_thm",
  ``∀i upd ctxt cs.
      upd updates ctxt ∧ ctxt extends init_ctxt ∧
      i models (thyof (upd::ctxt)) ∧
      (∀name args. IS_SOME (FST cs name args) ⇒
        MEM (name,LENGTH args) (types_of_upd upd) ∧
        inhabited (THE (FST cs name args)) ∧
        ∀x. MEM x (MAP FST (consts_of_upd upd)) ⇒
            IS_SOME (SND cs x args)
            (* the type of the constant should have exactly the same type
            variables as the new type hence the re-use of args here *)) ∧
      (∀name args. IS_SOME (SND cs name args) ⇒
        ∃ty. MEM (name,ty) (consts_of_upd upd) ∧
             (LENGTH (tyvars ty) = LENGTH args) ∧
             ∀τ. is_type_valuation τ ∧
                 (MAP τ (STRING_SORT (tyvars ty)) = args) ⇒
             (THE (SND cs name args)) <: typesem (constrain_assignment (FST cs) (FST i)) τ ty) ∧
      (∀p. MEM p (axioms_of_upd upd) ⇒
        constrain_interpretation cs i satisfies (sigof (upd::ctxt),[],p))
      ⇒
      (constrain_interpretation cs i) models (thyof (upd::ctxt))``,
  rw[] >> fs[models_def] >>
  REWRITE_TAC[CONJ_ASSOC] >>
  `theory_ok (thyof ctxt)` by metis_tac[extends_theory_ok,init_theory_ok] >>
  conj_tac >- (
    `∃δ γ. i =(δ,γ)` by metis_tac[pair_CASES] >>
    `∃tycs tmcs. cs =(tycs,tmcs)` by metis_tac[pair_CASES] >>
    fs[is_interpretation_def,is_std_interpretation_def,constrain_interpretation_def] >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- (
      fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
      res_tac >> rw[constrain_assignment_def] >>
      BasicProvers.CASE_TAC >> rw[] >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      res_tac >> metis_tac[] ) >>
    CONV_TAC(lift_conjunct_conv(can (match_term ``is_std_type_assignment X``))) >>
    conj_asm1_tac >- (
      fs[is_std_type_assignment_def,constrain_assignment_def] >>
      simp[FUN_EQ_THM] >>
      fs[IS_SOME_EXISTS] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] >>
      imp_res_tac ALOOKUP_MEM >>
      `ALL_DISTINCT (MAP FST (type_list (upd::ctxt))) ∧
       ALL_DISTINCT (MAP FST (const_list (upd::ctxt)))` by (
        conj_tac >>
        imp_res_tac updates_ALL_DISTINCT >>
        first_x_assum match_mp_tac >>
        imp_res_tac extends_ALL_DISTINCT >>
        first_x_assum match_mp_tac >>
        EVAL_TAC ) >>
      rw[] >> fs[ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      res_tac >> fs[] >> rw[] >>
      rpt (BasicProvers.CASE_TAC >> res_tac >> fs[]) >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
    conj_tac >- (
      fs[interprets_def,constrain_assignment_def] >> rw[] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[Once updates_cases] >> rw[] >> fs[] >>
      res_tac >> fs[] >> rw[] >>
      fs[MEM_MAP,EXISTS_PROD,LET_THM] >>
      metis_tac[] ) >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rw[constrain_assignment_def] >>
    reverse BasicProvers.CASE_TAC >- (
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      qpat_assum`FLOOKUP X Y = Z`mp_tac >>
      simp[FLOOKUP_FUNION] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[] ) >>
      rw[] >>
      `v = ty` by (
        fs[Once updates_cases] >> rw[] >> fs[] >>
        qmatch_assum_abbrev_tac`ALOOKUP al k = SOME v` >>
        `ALL_DISTINCT (MAP FST al)` by (
          simp[Abbr`al`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        fs[Abbr`al`] ) >>
      rw[] >> res_tac >> fs[constrain_assignment_def]) >>
    Cases_on`type_ok (tysof ctxt) v` >- (
      qmatch_abbrev_tac`a <: b` >>
      qmatch_assum_abbrev_tac`a <: c` >>
      qsuff_tac `b = c` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac typesem_consts >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[type_ok_def] >> rw[FUN_EQ_THM] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
      fs[Once updates_cases] >> rw[] >> fs[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    qpat_assum`FLOOKUP X Y = Z`mp_tac >>
    simp[FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      strip_tac >>
      fs[theory_ok_def] >>
      qsuff_tac`F`>-rw[]>>
      qpat_assum`¬x`mp_tac >>simp[]>>
      first_x_assum match_mp_tac >>
      simp[IN_FRANGE_FLOOKUP] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_abbrev_tac`a <: b` >>
    qmatch_assum_abbrev_tac`a <: c` >>
    qsuff_tac `b = c` >- rw[] >>
    unabbrev_all_tac >>
    fs[Once updates_cases] >> rw[] >> fs[] >- (
      rpt AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM] ) >>
    qmatch_abbrev_tac`typesem d1 τ v = typesem δ τ v` >>
    `is_std_type_assignment d1 ∧
     is_std_type_assignment δ` by (
       reverse conj_asm2_tac >- fs[is_std_interpretation_def] >>
       simp[Abbr`d1`,GSYM constrain_assignment_def] ) >>
    rator_x_assum`ALOOKUP` mp_tac >> simp[] >>
    Q.PAT_ABBREV_TAC`t1 = domain (typeof pred)` >>
    Q.PAT_ABBREV_TAC`t2 = Tyapp name X` >>
    qsuff_tac`k ∈ {abs;rep} ∧ (set (tyvars v) = set (tyvars (Fun t1 t2))) ⇒
              (typesem d1 τ t1 = typesem δ τ t1) ∧
              (typesem d1 τ t2 = typesem δ τ t2)` >- (
      match_mp_tac SWAP_IMP >> strip_tac >>
      discharge_hyps >- (
        pop_assum mp_tac >> rw[] >>
        simp[tyvars_def] >>
        metis_tac[pred_setTheory.UNION_COMM] ) >>
      pop_assum mp_tac >>
      rw[] >>
      qmatch_abbrev_tac`typesem d1 τ (Fun dom rng) = typesem δ τ (Fun dom rng)` >>
      qspecl_then[`δ`,`τ`,`dom`,`rng`]mp_tac typesem_Fun >>
      qspecl_then[`d1`,`τ`,`dom`,`rng`]mp_tac typesem_Fun >>
      simp[] >> rw[]) >>
    strip_tac >>
    conj_tac >- (
      unabbrev_all_tac >>
      match_mp_tac typesem_consts >>
      qexists_tac`tysof (ctxt)` >>
      imp_res_tac proves_term_ok >>
      qpat_assum`k ∈ X`kall_tac >>
      fs[term_ok_def] >>
      conj_tac >- (
        imp_res_tac term_ok_type_ok >>
        fs[theory_ok_def] ) >>
      simp[type_ok_def] >> rw[FUN_EQ_THM] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    unabbrev_all_tac >>
    simp[typesem_def,MAP_MAP_o,combinTheory.o_DEF,ETA_AX] >>
    BasicProvers.CASE_TAC >>
    qsuff_tac`set (tyvars v) = set (tvars pred)` >- (
      qpat_assum`set (tyvars v) = X`kall_tac >>
      rw[] >>
      `STRING_SORT (tvars pred) = STRING_SORT (tyvars v)` by (
        `ALL_DISTINCT (tvars pred)` by simp[] >>
        `ALL_DISTINCT (tyvars v)` by simp[] >>
        `PERM (tvars pred) (tyvars v)` by (
          match_mp_tac sortingTheory.PERM_ALL_DISTINCT >>
          fs[pred_setTheory.EXTENSION] ) >>
        metis_tac[holSyntaxLibTheory.STRING_SORT_EQ] ) >>
      fs[IS_SOME_EXISTS,PULL_EXISTS,LET_THM] >>
      metis_tac[optionTheory.NOT_SOME_NONE] ) >>
    simp[tyvars_def,pred_setTheory.EXTENSION,
         holSyntaxLibTheory.MEM_FOLDR_LIST_UNION,
         MEM_MAP,PULL_EXISTS] >>
    qpat_assum`k ∈ X`kall_tac >>
    imp_res_tac proves_term_ok >> fs[term_ok_def] >>
    fs[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[pred_setTheory.SUBSET_DEF,tyvars_def] >>
    metis_tac[] ) >>
  gen_tac >>
  qmatch_abbrev_tac`P ⇒ q` >>
  strip_tac >> qunabbrev_tac`q` >>
  first_x_assum(qspec_then`p`mp_tac) >>
  fs[Abbr`P`] >>
  cheat)

val _ = export_theory()
