open HolKernel bossLib boolLib boolSimps listTheory pairTheory rich_listTheory pred_setTheory arithmeticTheory finite_mapTheory relationTheory sortingTheory stringTheory
open miscLib miscTheory bigStepTheory semanticPrimitivesTheory bigClockTheory replTheory terminationTheory
open bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeClockTheory bytecodeLabelsTheory bytecodeTerminationTheory
open intLangTheory toBytecodeTheory intLangExtraTheory intLangProofTheory bytecodeProofTheory compilerTerminationTheory
open patLangProofTheory
val _ = new_theory"compilerProof"

(* misc *)

val code_env_cd_append = store_thm("code_env_cd_append",
  ``∀code cd code'. code_env_cd code cd ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒ code_env_cd (code ++ code') cd``,
  rw[] >> PairCases_on`cd` >>
  fs[code_env_cd_def] >>
  HINT_EXISTS_TAC>>simp[]>>
  HINT_EXISTS_TAC>>simp[])

val FOLDL_emit_thm = store_thm("FOLDL_emit_thm",
  ``∀ls s. FOLDL (λs i. s with out := i::s.out) s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality])

(* label_closures *)

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ set (free_vars e) ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     set (free_vars e') ⊆ set (free_vars e) ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ set (free_vars_list es) ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     set (free_vars_list es') ⊆ set (free_vars_list es) ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     EVERY2 (syneq_exp ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0.
     (no_labs_defs (ls0 ++ MAP ($, NONE) defs)) ∧
     set (free_vars_defs nz (MAP ($, NONE) defs)) ⊆ count ez ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     syneq_defs ez ez $= (ls0 ++ MAP ($, NONE) defs) (ds0 ++ MAP ($, NONE) defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (defs',j') = label_closures_defs ez j nz k defs in
     (j' = j + LENGTH (free_labs_defs ez nz k defs')) ∧
     (MAP (FST o FST o SND) (free_labs_defs ez nz k defs') = GENLIST ($+ j) (LENGTH (free_labs_defs ez nz k defs'))) ∧
     set (free_vars_defs nz defs') ⊆ set (free_vars_defs nz (MAP ($, NONE) defs)) ∧
     (LENGTH defs' = LENGTH defs) ∧
     all_labs_defs defs' ∧
     EVERY good_cd (free_labs_defs ez nz k defs') ∧
     syneq_defs ez ez $= (ls0 ++ (MAP ($, NONE) defs)) (ds0 ++ defs') (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `set (free_vars e2) ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    Cases_on`bd` >- (
      ntac 2 gen_tac >>
      map_every qx_gen_tac[`e1`,`e2`] >>
      rpt strip_tac >> fs[] >>
      `set (free_vars e2) ⊆ count (ez + 1)` by (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
      qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
      qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
      simp[LIST_EQ_REWRITE] >>
      conj_tac >- (
        gen_tac >>
        Cases_on`x<LENGTH (free_labs ez p0)`>>
        lrw[EL_APPEND1,EL_APPEND2] ) >>
      rfs[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases >> rw[ADD1] >>
        res_tac >>
        disj2_tac >> HINT_EXISTS_TAC >>
        fsrw_tac[ARITH_ss][] ) >>
      simp[Once syneq_exp_cases] >>
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[]) >>
    simp[] >>
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    simp[Once syneq_exp_cases] >>
    qabbrev_tac`p = label_closures ez j e1` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >>
    PairCases_on`q`>>fs[LET_THM] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
  strip_tac >- (
    rpt strip_tac >>
    simp[] >>
    `FILTER (IS_NONE o FST) defs = defs` by (
      simp[FILTER_EQ_ID] >>
      fs[FLAT_EQ_NIL,EVERY_MAP] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      qx_gen_tac`z` >> rpt strip_tac >>
      res_tac >> Cases_on`z`>>fs[] ) >>
    full_simp_tac std_ss [LET_THM] >>
    full_simp_tac std_ss [FILTER_EQ_ID,LENGTH_MAP] >>
    qabbrev_tac`p = label_closures_defs ez j (LENGTH defs) 0 (MAP SND defs)` >>
    PairCases_on`p`>>
    `no_labs e`by fs[] >>
    `set (free_vars e) ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`set (free_vars X) ⊆ Y`mp_tac >>
      rpt (pop_assum kall_tac) >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,LET_THM] >>
      srw_tac[ARITH_ss][ADD1] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    full_simp_tac std_ss [] >>
    qabbrev_tac`q = label_closures (ez + LENGTH defs) p1 e` >>
    PairCases_on`q` >>
    full_simp_tac std_ss [] >>
    `MAP ($, NONE) (MAP SND defs) = defs` by (
      fs[EVERY_MEM] >>
      lrw[MAP_MAP_o] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once (CONJUNCT2 (GSYM MAP_ID)),SimpRHS])) >>
      lrw[MAP_EQ_f,FORALL_PROD] >> res_tac >> fs[]) >>
    full_simp_tac std_ss [] >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[syneq_defs_refl,EVERY_MAP] >>
    fs[LET_THM] >>
    strip_tac >>
    fsrw_tac[ETA_ss][] >>
    rfs[] >> simp[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs_defs ez (LENGTH defs) 0 p0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,free_vars_defs_MAP] >>
      gen_tac >> strip_tac >>
      disj2_tac >>
      qexists_tac`m` >>
      simp[] ) >>
    simp[Once syneq_exp_cases] >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    map_every qx_gen_tac[`e`,`es`] >>
    rpt strip_tac >>
    qabbrev_tac`p = label_closures ez j e` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >> PairCases_on`q`>>fs[] >>
    fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >> rfs[] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`p2`,`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`,`e3`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    qabbrev_tac`r = label_closures ez (j + LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)) e3` >> PairCases_on`r`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] >>
      Cases_on`x < LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    simp[] >> simp[Once syneq_exp_cases] ) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rpt strip_tac >>
    fs[] >>
    qabbrev_tac`p = label_closures ez j e` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >>
    PairCases_on`q`>>fs[] >> simp[] >> rfs[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[] >> rw[FUNION_FEMPTY_2] >>
    fs[LENGTH_NIL]) >>
  rpt gen_tac >> rpt strip_tac >>
  full_simp_tac (std_ss++ARITH_ss) [] >>
  last_x_assum mp_tac >>
  last_x_assum mp_tac >>
  simp[] >> ntac 2 strip_tac >>
  Q.PAT_ABBREV_TAC`r = bind_fv X Y Z` >>
  PairCases_on`r`>>fs[] >>
  Q.PAT_ABBREV_TAC`ezz:num = az + (X + (Y + 1))` >>
  qabbrev_tac`p = label_closures ezz (j+1) r3` >>
  PairCases_on`p` >> full_simp_tac std_ss [] >>
  qabbrev_tac`q = label_closures_defs ez p1 nz (k+1) defs` >>
  PairCases_on`q` >> full_simp_tac std_ss [] >>
  `no_labs r3` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] ) >>
  `set (free_vars r3) ⊆ count ezz` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >- (
      qho_match_abbrev_tac`(the n (find_index x ls n)) < y` >>
      qho_match_abbrev_tac`P (the n (find_index x ls n))` >>
      ho_match_mp_tac the_find_index_suff >>
      simp[Abbr`P`,Abbr`x`,Abbr`ls`,MEM_FILTER,ADD1,MEM_GENLIST,Abbr`n`,Abbr`y`] >>
      rw[] >>
      qmatch_abbrev_tac`m < A + B` >>
      Cases_on`m=A`>>fsrw_tac[ARITH_ss][]>>
      Cases_on`B=0`>>fsrw_tac[ARITH_ss][]>>
      fs[LENGTH_NIL_SYM,FILTER_EQ_NIL,EVERY_MEM,QSORT_MEM,markerTheory.Abbrev_def] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    qho_match_abbrev_tac`(the 0 (find_index x ls n)) < y` >>
    qho_match_abbrev_tac`P (the 0 (find_index x ls n))` >>
    ho_match_mp_tac the_find_index_suff >>
    `n ≤ nz` by (
      unabbrev_all_tac >>
      simp[GSYM ADD1] >>
      simp[GSYM LESS_EQ] >>
      qmatch_abbrev_tac`LENGTH (FILTER P ls) < nz` >>
      `nz = LENGTH ls` by rw[Abbr`ls`] >> pop_assum SUBST1_TAC >>
      match_mp_tac LENGTH_FILTER_LESS >>
      simp[Abbr`P`,Abbr`ls`,EXISTS_MEM,MEM_GENLIST] >>
      qexists_tac`LENGTH ls0` >>
      simp[] ) >>
    reverse conj_tac >- (
      unabbrev_all_tac >>
      simp[MEM_MAP,MEM_FILTER,sortingTheory.QSORT_MEM] >>
      qexists_tac`v` >> simp[] ) >>
    simp[Abbr`P`,Abbr`y`] >>
    qx_gen_tac`m`>>strip_tac >>
    qmatch_abbrev_tac`m + n < l1 + l2` >>
    `l2 = LENGTH ls + 1` by rw[Abbr`l2`,Abbr`ls`] >> rw[] >>
    qsuff_tac`n ≤ l1 + 1` >- DECIDE_TAC >>
    simp[Abbr`n`]) >>
  full_simp_tac std_ss [LET_THM] >>
  Q.PAT_ABBREV_TAC`cd:def = (SOME X,az,p0)` >>
  last_x_assum(qspecl_then[`ds0++[cd]`,`ls0++[(NONE,az,b)]`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[EVERY_MAP] >> strip_tac >>
    simp[Once syneq_exp_cases,EVERY_MAP] >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Cases_on`v < k`>>simp[EL_APPEND1,EL_APPEND2,ADD1,EL_MAP] >- (
      strip_tac >>
      ntac 2 (first_x_assum (mp_tac o SYM)) >>
      ntac 2 strip_tac >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    Cases_on`v=k` >- (
      simp[Abbr`cd`] >> strip_tac >>
      simp[syneq_cb_aux_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      simp[syneq_cb_aux_def] >>
      conj_asm1_tac >- (
        fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
        simp[EVERY_MEM,MEM_MAP,MEM_FILTER,QSORT_MEM,MEM_FILTER,MEM_GENLIST] >>
        simp[GSYM LEFT_FORALL_IMP_THM] >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        metis_tac[] ) >>
      qmatch_abbrev_tac`syneq_exp z1 ezz V b p0` >>
      qsuff_tac`syneq_exp z1 ezz V b r3` >- (
        strip_tac >>
        `V = $= O V` by metis_tac[Id_O] >> pop_assum SUBST1_TAC >>
        match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
        PROVE_TAC[] ) >>
      qpat_assum`Abbrev(X = bind_fv A Y Z)`mp_tac >>
      simp[bind_fv_def,markerTheory.Abbrev_def] >> rw[] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`z1`,Abbr`ezz`] >>
      conj_tac >- simp[Abbr`V`,syneq_cb_V_def] >>
      reverse conj_tac >- (
        qpat_assum`Y ⊆ count ez`mp_tac >>
        qpat_assum`Y ⊆ count ez`mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        Cases_on`az + nz ≤ x`>>simp[]) >>
      gen_tac >> strip_tac >>
      reverse conj_tac >- (
        rw[] >- (
          qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
          qunabbrev_tac`X` >>
          qho_match_abbrev_tac`P (the c (find_index a w c))` >>
          match_mp_tac the_find_index_suff >>
          reverse conj_tac >- (
            unabbrev_all_tac >>
            fs[SUBSET_DEF] >>
            simp[MEM_FILTER,MEM_GENLIST] ) >>
          simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
        qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (the 0 (find_index a w c))` >>
        match_mp_tac the_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
      Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
      `¬(x < az + nz) ⇒ MEM (x-(az+nz)) envs` by (
        simp[Abbr`envs`,MEM_MAP,MEM_FILTER,QSORT_MEM] >>
        strip_tac >>
        qexists_tac`x` >> simp[] ) >>
      Q.PAT_ABBREV_TAC`recs = LENGTH ls0::X` >>
      `x < az + nz ⇒ MEM (x - az) recs` by (
        simp[Abbr`recs`,MEM_FILTER,MEM_GENLIST] ) >>
      simp[Abbr`V`] >>
      reverse(rw[]) >- (
        fs[] >>
        simp[syneq_cb_V_def] >>
        Q.PAT_ABBREV_TAC`rz = LENGTH (FILTER X Y) + 1` >>
        Q.ISPECL_THEN[`envs`,`x-(az+nz)`,`rz`]mp_tac find_index_MEM >>
        simp[] >> disch_then strip_assume_tac >> simp[] >>
        simp[Abbr`rz`] ) >>
      simp[syneq_cb_V_def] >> fs[] >>
      Q.ISPECL_THEN[`recs`,`x-az`,`0:num`]mp_tac find_index_MEM >>
      simp[] >> disch_then strip_assume_tac >> simp[] >>
      Cases_on`i=0` >- (
        simp[] >> fs[Abbr`recs`]) >>
      simp[] >>
      qpat_assum`EL X Y = x - def0`mp_tac >>
      simp[Abbr`recs`,EL_CONS,PRE_SUB1] >>
      fsrw_tac[ARITH_ss][]) >>
    lrw[EL_CONS] >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[PRE_SUB1,EL_MAP] >>
    Q.PAT_ABBREV_TAC`p = EL X defs` >>
    PairCases_on`p` >>
    simp[syneq_cb_aux_def] >>
    ntac 2 strip_tac >>
    fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `LENGTH defs + (LENGTH ls0 + 1) = nz` by simp[] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  simp[] >> strip_tac >>
  simp[Abbr`cd`,ADD1]>>
  conj_tac >- (
    fsrw_tac[ARITH_ss][] >>
    lrw[LIST_EQ_REWRITE,EL_CONS,ADD1] >>
    Cases_on`x=0` >> lrw[EL_CONS,PRE_SUB1] >>
    Cases_on`x < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2] >>
    Cases_on `x-1 < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2]) >>
  conj_tac >- (
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  reverse conj_tac >- (
    metis_tac[CONS_APPEND,APPEND_ASSOC] ) >>
  simp[good_cd_def] >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    simp[EVERY_MEM,QSORT_MEM] >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    qpat_assum`set (free_vars p0) ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> strip_tac >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`v<az+nz`>>fsrw_tac[ARITH_ss][]>- (
      qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
      qho_match_abbrev_tac`P (the n (find_index a ls n))` >>
      match_mp_tac the_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] ) >>
    rw[] >>
    qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
    qho_match_abbrev_tac`P (the 0 (find_index a ls n))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] >>
    HINT_EXISTS_TAC >> simp[] ) >>
  map_every qexists_tac[`b`,`r3`] >>
  simp[])

(* compile_code_env *)

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀c s. let s' = FOLDL cce_aux s c in
     ALL_DISTINCT (MAP (FST o FST) c) ∧
     EVERY (combin$C $< s.next_label) (MAP (FST o FST) c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP (FST o FST) c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     (EVERY all_labs (MAP (SND o SND) c) ⇒ ∀l. uses_label code l ⇒
       MEM (Label l) code ∨ MEM l (MAP (FST o FST o SND) (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST(SND p))) p4) c)))) ∧
     (∀l. MEM l (MAP (FST o FST) c) ⇒ MEM (Label l) code) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let ((l,ccenv,ce),(az,body)) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile (MAP CTEnv ccenv) (TCTail az 0) 0 (cs i) body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   Induct >- ( simp[Once SWAP_REVERSE] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`MAP CTEnv p1`,`TCTail p3 0`,`0`,`s0`,`p4`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   Q.PAT_ABBREV_TAC`s1 = compile X Y Z A B` >>
   first_x_assum(qspecl_then[`s1`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     fsrw_tac[ARITH_ss][EVERY_MEM,Abbr`s0`] >>
     rw[] >> res_tac >> DECIDE_TAC ) >>
   disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
   simp[Abbr`s0`] >>
   simp[Once SWAP_REVERSE] >>
   fs[] >> simp[] >>
   simp[FILTER_APPEND,FILTER_REVERSE,MEM_FILTER,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
   conj_tac >- (
     rfs[FILTER_APPEND] >>
     fs[EVERY_MAP,EVERY_FILTER,EVERY_REVERSE,between_def] >>
     fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_MAP] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]
       >- metis_tac[] >>
     res_tac >> fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     fs[EVERY_MAP,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
     fsrw_tac[DNF_ss][EVERY_MEM,between_def] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     rw[] >>
     Cases_on`l=p0`>>rw[]>>
     Cases_on`MEM (Label l)c0`>>rw[]>>
     Cases_on`MEM (Label l)bc`>>rw[]>>
     fs[uses_label_thm,EXISTS_REVERSE] >>
     metis_tac[] ) >>
   conj_tac >- metis_tac[] >>
   qexists_tac`λi. if i = 0 then (s with out := Label p0::s.out) else cs (i-1)` >>
   Cases >> simp[] >- (
     map_every qexists_tac[`[]`,`c0`] >> simp[] ) >>
   strip_tac >>
   first_x_assum(qspec_then`n`mp_tac) >>
   simp[UNCURRY] >> strip_tac >>
   simp[] >>
   conj_asm1_tac >- ( Cases >> simp[] ) >>
   qexists_tac`Label p0::(REVERSE bc ++ bc0)` >>
   simp[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
   qpat_assum`EVERY X (FILTER is_Label bc0)`mp_tac >>
   qpat_assum`EVERY X (MAP Y (FILTER is_Label bc))`mp_tac >>
   simp[EVERY_FILTER,EVERY_MAP,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
   asm_simp_tac(srw_ss()++ARITH_ss++DNF_ss)[EVERY_MEM] >>
   rw[] >> res_tac >> DECIDE_TAC)

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀ez s e. let s' = compile_code_env s e in
      ALL_DISTINCT (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY (combin$C $< s.next_label) (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY good_cd (free_labs ez e)
      ⇒
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      ALL_DISTINCT (FILTER is_Label code) ∧
      EVERY (λn. MEM n (MAP (FST o FST o SND) (free_labs ez e)) ∨ between s.next_label s'.next_label n)
        (MAP dest_Label (FILTER is_Label code)) ∧
      (EVERY all_labs (MAP (SND o SND o SND) (free_labs ez e)) ⇒
       ∀l. uses_label code l ⇒ MEM (Label l) code ∨
         MEM l (MAP (FST o FST o SND)
           (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST (SND p))) p4) (MAP SND (free_labs ez e)))))) ∧
      (∀l. MEM l (MAP (FST o FST o SND) (free_labs ez e)) ⇒ MEM (Label l) code) ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP (FST o FST o SND) (free_labs ez e))) ⇒ l1 < l2)
        ⇒
        EVERY (code_env_cd (bc0++code)) (free_labs ez e) ∧
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  `MAP SND (free_labs 0 e) = MAP SND (free_labs ez e)` by metis_tac[MAP_SND_free_labs_any_ez] >>
  fs[] >>
  Q.ISPECL_THEN[`MAP SND (free_labs ez e)`,`s''`]mp_tac FOLDL_cce_aux_thm >>
  simp[Abbr`s''`] >>
  discharge_hyps >- (
    fsrw_tac[ARITH_ss][EVERY_MEM,MAP_MAP_o] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Once SWAP_REVERSE,Abbr`s''''`] >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP,MAP_MAP_o] >>
    res_tac >> rw[] >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
    reverse conj_tac >- (disj2_tac >> DECIDE_TAC) >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    rw[] >> res_tac >>
    TRY(metis_tac[]) >>
    disj2_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    rw[] >>
    fs[MAP_MAP_o] >>
    fs[uses_label_thm] >>
    metis_tac[] ) >>
  conj_tac >- fs[MAP_MAP_o] >>
  rpt gen_tac >>
  strip_tac >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    qx_gen_tac`z` >>
    PairCases_on`z` >> strip_tac >>
    simp[code_env_cd_def] >>
    qmatch_assum_abbrev_tac`MEM cd (free_labs ez e)` >>
    `∃i. i < LENGTH (free_labs ez e) ∧ (EL i (free_labs ez e) = cd)` by metis_tac[MEM_EL] >>
    qpat_assum`∀i. P ⇒ Q`(qspec_then`i`mp_tac) >>
    simp[EL_MAP] >>
    simp[Abbr`cd`] >> strip_tac >>
    qexists_tac`cs i`>>simp[] >>
    qexists_tac`bc0++Jump (Lab s.next_label)::bc0'` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP,FILTER_APPEND] >>
    fsrw_tac[DNF_ss][] >- (
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
    rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  `bc_fetch bs = SOME (Jump (Lab s.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

val _ = export_theory()
