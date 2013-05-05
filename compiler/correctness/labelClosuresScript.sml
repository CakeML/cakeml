open HolKernel boolLib boolSimps bossLib quantHeuristicsLib pairTheory listTheory alistTheory prim_recTheory sortingTheory whileTheory
open Parse relationTheory arithmeticTheory rich_listTheory finite_mapTheory pred_setTheory state_transformerTheory lcsymtacs
open SatisfySimps miscLib miscTheory intLangTheory compileTerminationTheory
val _ = new_theory"labelClosures"

(*
val free_labs_bind_fv = store_thm("free_labs_bind_fv",
  ``free_labs (bind_fv def nz ez k).body = free_labs (SND def)``,
  Cases_on`def`>>rw[bind_fv_def] >> rw[Abbr`e`])
val _ = export_rewrites["free_labs_bind_fv"]

val body_count_bind_fv = store_thm("body_count_bind_fv",
  ``body_count (bind_fv def nz ez k).body = body_count (SND def)``,
  Cases_on`def`>>rw[bind_fv_def] >> rw[Abbr`e`])
val _ = export_rewrites["body_count_bind_fv"]

val bind_fv_nz_ez_ix = store_thm("bind_fv_nz_ez_ix",
  ``((bind_fv def nz ez ix).nz = nz) ∧
    ((bind_fv def nz ez ix).ez = ez) ∧
    ((bind_fv def nz ez ix).ix = ix)``,
  Cases_on`def`>>rw[bind_fv_def,LET_THM])
val _ = export_rewrites["bind_fv_nz_ez_ix"]

val bind_fv_az = store_thm("bind_fv_az",
  ``(bind_fv def nz ez ix).az = FST def``,
  Cases_on`def`>>rw[bind_fv_def,LET_THM])
val _ = export_rewrites["bind_fv_az"]
*)

val good_cd_def = Define`
  good_cd ((ez,nz,ix),(l,cc,recs,envs),az,b) ⇔
    EVERY (λv. v < ez) envs ∧
    free_vars b ⊆ count (LENGTH cc) ∧
    ∃e e'. (cc,(recs,envs),e') = (bind_fv (az,e) nz ix)`

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ free_vars e ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     free_vars e' ⊆ free_vars e ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ free_vars_list es ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     free_vars_list es' ⊆ free_vars_list es ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     EVERY2 (syneq_exp ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0.
     (no_labs_defs (ls0 ++ MAP ($, NONE) defs)) ∧
     free_vars_defs nz (MAP ($, NONE) defs) ⊆ count ez ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     syneq_defs ez ez $= (ls0 ++ MAP ($, NONE) defs) (ds0 ++ MAP ($, NONE) defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (defs',j') = label_closures_defs ez j nz k defs in
     (j' = j + LENGTH (free_labs_defs ez nz k defs')) ∧
     (MAP (FST o FST o SND) (free_labs_defs ez nz k defs') = GENLIST ($+ j) (LENGTH (free_labs_defs ez nz k defs'))) ∧
     free_vars_defs nz defs' ⊆ free_vars_defs nz (MAP ($, NONE) defs) ∧
     (LENGTH defs' = LENGTH defs) ∧
     all_labs_defs defs' ∧
     EVERY good_cd (free_labs_defs ez nz k defs') ∧
     syneq_defs ez ez $= (ls0 ++ (MAP ($, NONE) defs)) (ds0 ++ defs') (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `free_vars e2 ⊆ count (ez + 1)` by (
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
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `free_vars e2 ⊆ count (ez + 1)` by (
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
    `free_vars e ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`free_vars X ⊆ Y`mp_tac >>
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
    rpt gen_tac >> strip_tac >> strip_tac >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      simp[syneq_defs_refl] >>
      PairCases_on`def`>>fs[]) >>
    qabbrev_tac`p = label_closures_defs ez j 1 0 [def]` >>
    PairCases_on`p` >>
    full_simp_tac std_ss [] >>
    strip_tac >>
    Cases_on`p0`>>fs[]>>
    Cases_on`t`>>fs[]>>
    PairCases_on`h`>>PairCases_on`def`>>fs[]>>
    simp[Once syneq_exp_cases] >> fs[] >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  strip_tac >- (
    rw[] >> PairCases_on`x`>>fs[]>>
    PairCases_on`y`>>fs[]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
  `free_vars r3 ⊆ count ezz` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >- (
      qho_match_abbrev_tac`(THE (find_index x ls n)) < y` >>
      qho_match_abbrev_tac`P (THE (find_index x ls n))` >>
      ho_match_mp_tac THE_find_index_suff >>
      simp[Abbr`P`,Abbr`x`,Abbr`ls`,MEM_FILTER,ADD1,MEM_GENLIST,Abbr`n`,Abbr`y`] >>
      rw[] >>
      qmatch_abbrev_tac`m < A + B` >>
      Cases_on`m=A`>>fsrw_tac[ARITH_ss][]>>
      Cases_on`B=0`>>fsrw_tac[ARITH_ss][]>>
      fs[LENGTH_NIL_SYM,FILTER_EQ_NIL,EVERY_MEM,QSORT_MEM,markerTheory.Abbrev_def] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    qho_match_abbrev_tac`(THE (find_index x ls n)) < y` >>
    qho_match_abbrev_tac`P (THE (find_index x ls n))` >>
    ho_match_mp_tac THE_find_index_suff >>
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
        qpat_assum`IMAGE X  Y ⊆ count ez` mp_tac >>
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
        qpat_assum`IMAGE X Y ⊆ count ez`mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        Cases_on`az + nz ≤ x`>>simp[]) >>
      gen_tac >> strip_tac >>
      reverse conj_tac >- (
        rw[] >- (
          qho_match_abbrev_tac`THE (find_index a w c) < X` >>
          qunabbrev_tac`X` >>
          qho_match_abbrev_tac`P (THE (find_index a w c))` >>
          match_mp_tac THE_find_index_suff >>
          reverse conj_tac >- (
            unabbrev_all_tac >>
            fs[SUBSET_DEF] >>
            simp[MEM_FILTER,MEM_GENLIST] ) >>
          simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
        qho_match_abbrev_tac`THE (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (THE (find_index a w c))` >>
        match_mp_tac THE_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
      Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y (QSORT Z A))` >>
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
  reverse conj_tac >-
    metis_tac[CONS_APPEND,APPEND_ASSOC] >>
  simp[good_cd_def] >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    simp[EVERY_MEM,QSORT_MEM] >>
    qpat_assum`IMAGE X Y ⊆ count ez` mp_tac >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    qpat_assum`free_vars p0 ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> strip_tac >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`v<az+nz`>>fsrw_tac[ARITH_ss][]>- (
      qho_match_abbrev_tac`THE (find_index a ls n) < X` >>
      qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
      match_mp_tac THE_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] ) >>
    rw[] >>
    qho_match_abbrev_tac`THE (find_index a ls n) < X` >>
    qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
    match_mp_tac THE_find_index_suff >>
    simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] >>
    HINT_EXISTS_TAC >> simp[] ) >>
  map_every qexists_tac[`b`,`r3`] >>
  simp[])

val _ = export_theory()
