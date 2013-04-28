open HolKernel boolLib boolSimps bossLib quantHeuristicsLib pairTheory listTheory alistTheory prim_recTheory sortingTheory whileTheory
open Parse relationTheory arithmeticTheory rich_listTheory finite_mapTheory pred_setTheory state_transformerTheory lcsymtacs
open SatisfySimps miscLib miscTheory intLangTheory compileTerminationTheory
val _ = new_theory"labelClosures"

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

val good_code_env_def = Define`
  good_code_env c = ∀cd. cd ∈ FRANGE c ⇒
    (body_count cd.body = 0) ∧ free_labs cd.body ⊆ FDOM c ∧
    EVERY (λv. v < cd.ez) (SND cd.ceenv) ∧
    free_vars cd.body ⊆ count (LENGTH cd.ccenv) ∧
    ∃e. (cd = (bind_fv (cd.az,e) cd.nz cd.ez cd.ix) with body := cd.body)`

val good_code_env_FEMPTY = store_thm("good_code_env_FEMPTY",
  ``good_code_env FEMPTY``,
  rw[good_code_env_def,IN_FRANGE])
val _ = export_rewrites["good_code_env_FEMPTY"]

val good_code_env_FUNION = store_thm("good_code_env_FUNION",
  ``∀c1 c2. DISJOINT (FDOM c1) (FDOM c2) ∧ good_code_env c1 ∧ good_code_env c2 ⇒ good_code_env (c1 ⊌ c2)``,
  simp[good_code_env_def,FRANGE_FUNION] >>
  metis_tac[SUBSET_UNION,SUBSET_TRANS])

val good_code_env_FUPDATE = store_thm("good_code_env_FUPDATE",
  ``∀c k cd. (good_code_env c ∧
    (body_count cd.body = 0) ∧ free_labs cd.body ⊆ k INSERT FDOM c ∧
    EVERY (λv. v < cd.ez) (SND cd.ceenv) ∧
    free_vars cd.body ⊆ count (LENGTH cd.ccenv) ∧
    ∃e. (cd = (bind_fv (cd.az,e) cd.nz cd.ez cd.ix) with body := cd.body))
    ⇒ good_code_env (c |+ (k,cd))``,
  rpt gen_tac >> strip_tac >>
  fs[good_code_env_def] >>
  gen_tac >> strip_tac >- metis_tac[] >>
  pop_assum mp_tac >>
  metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_DEF,IN_INSERT])

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (free_labs e = {}) ∧ free_vars e ⊆ count ez ⇒
     let (e',c,j') = label_closures ez j e in
     (j' = j + body_count e) ∧
     (MAP FST c = (GENLIST ($+ j) (body_count e))) ∧
     (body_count e' = 0) ∧
     free_labs e' ⊆ set (MAP FST c) ∧
     free_vars e' ⊆ free_vars e ∧
     closed_code_env (alist_to_fmap c) ∧
     good_code_env (alist_to_fmap c) ∧
     syneq_exp (alist_to_fmap c) ez ez $= e e') ∧
    (∀ez j es.
     (free_labs_list es = {}) ∧ BIGUNION (IMAGE free_vars (set es)) ⊆ count ez ⇒
     let (es',c,j') = label_closures_list ez j es in
     (j' = j + body_count_list es) ∧
     (MAP FST c = (GENLIST ($+ j) (body_count_list es))) ∧
     (body_count_list es' = 0) ∧
     free_labs_list es' ⊆ set (MAP FST c) ∧
     BIGUNION (IMAGE free_vars (set es')) ⊆ BIGUNION (IMAGE free_vars (set es)) ∧
     closed_code_env (alist_to_fmap c) ∧
     good_code_env (alist_to_fmap c) ∧
     EVERY2 (syneq_exp (alist_to_fmap c) ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0 c0.
     (free_labs_defs (MAP INL ls0 ++ MAP INL defs) = {}) ∧ (FDOM c0 = set ds0) ∧
     BIGUNION (IMAGE (cbod_fvs o INL) (set defs)) ⊆ count (nz+ez) ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     (∀l. MEM l ds0 ⇒ l < j) ∧ closed_code_env c0 ∧
     syneq_defs c0 ez ez $= (MAP INL ls0 ++ MAP INL defs) (MAP INR ds0 ++ MAP INL defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (lds,c,j') = label_closures_defs ez j nz k defs in
     (j' = j + SUM (MAP body_count_def (MAP INL defs))) ∧
     (MAP FST c = (GENLIST ($+ j) (SUM (MAP body_count_def (MAP INL defs))))) ∧
     (LENGTH lds = LENGTH defs) ∧
     set lds ⊆ set (MAP FST c) ∧
     closed_code_env (alist_to_fmap c) ∧
     good_code_env (alist_to_fmap c) ∧
     syneq_defs (c0 ⊌ alist_to_fmap c) ez ez $= (MAP INL ls0 ++ MAP INL defs) (MAP INR ds0 ++ MAP INR lds) (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (rw[] >> rw[syneq_exp_FEMPTY_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_FEMPTY_refl]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `free_vars e2 ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + body_count e1) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<body_count e1`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      PROVE_TAC[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[DISJOINT_DEF,MEM_GENLIST,EXTENSION] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >>
      simp[SUBMAP_FUNION] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`alist_to_fmap q1` >>
    simp[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[] ) >>
    match_mp_tac SUBMAP_FUNION >>
    simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] ) >>
  strip_tac >- (rw[] >> rw[syneq_exp_FEMPTY_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_FEMPTY_refl]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM] >- simp[Once syneq_exp_cases] >>
    fs[IMAGE_EQ_SING,FOLDL_UNION_BIGUNION] >>
    qabbrev_tac`p = label_closures_list ez j es` >> PairCases_on`p`>>fs[LET_THM] >>
    rfs[FOLDL_UNION_BIGUNION] >>
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
    qabbrev_tac`q = label_closures (ez+1) (j + body_count e1) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<body_count e1`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      PROVE_TAC[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[DISJOINT_DEF,MEM_GENLIST,EXTENSION] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >>
      simp[SUBMAP_FUNION] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`alist_to_fmap q1` >>
    simp[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[] ) >>
    match_mp_tac SUBMAP_FUNION >>
    simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] ) >>
  strip_tac >- (
    rpt strip_tac >>
    simp[] >>
    `FILTER ISL defs = defs` by (
      simp[FILTER_EQ_ID] >>
      fs[IMAGE_EQ_SING,FILTER_EQ_NIL,EXISTS_MEM,EVERY_MEM] >>
      qx_gen_tac`z` >> strip_tac >>
      res_tac >> Cases_on`z`>>fs[] ) >>
    full_simp_tac std_ss [LET_THM] >>
    full_simp_tac std_ss [FILTER_EQ_ID,LENGTH_MAP] >>
    qabbrev_tac`p = label_closures_defs ez j (LENGTH defs) 0 (MAP OUTL defs)` >>
    PairCases_on`p`>>
    `free_labs e = {}`by fs[] >>
    `free_vars e ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`free_vars X ⊆ Y`mp_tac >>
      rpt (pop_assum kall_tac) >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,LET_THM,FOLDL_UNION_BIGUNION] >>
      Cases>>srw_tac[ARITH_ss][ADD1] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    full_simp_tac std_ss [] >>
    qabbrev_tac`q = label_closures (ez + LENGTH defs) p2 e` >>
    PairCases_on`q` >>
    full_simp_tac std_ss [] >>
    `MAP INL (MAP OUTL defs) = defs` by (
      fs[EVERY_MEM] >>
      lrw[MAP_MAP_o] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once (CONJUNCT2 (GSYM MAP_ID)),SimpRHS])) >>
      lrw[MAP_EQ_f] ) >>
    full_simp_tac std_ss [] >>
    first_x_assum(qspecl_then[`[]`,`[]`,`FEMPTY`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[LENGTH_NIL,syneq_defs_FEMPTY_refl] >>
      fsrw_tac[DNF_ss,ARITH_ss][LET_THM,FOLDL_UNION_BIGUNION,SUBSET_DEF,EXISTS_PROD,MEM_MAP] >>
      simp[GSYM FORALL_AND_THM] >>
      simp[GSYM IMP_CONJ_THM] >>
      map_every qx_gen_tac[`d1`,`d2`,`d`,`m`] >>
      strip_tac >>
      rpt (first_x_assum(qspec_then`d`mp_tac)) >>
      fs[EVERY_MEM] >> res_tac >>
      Cases_on`d`>>fs[] >> BasicProvers.VAR_EQ_TAC >>
      simp[AND_IMP_INTRO,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      disch_then(qspec_then`m-d1`mp_tac) >>
      Cases_on`m<d1`>>fsrw_tac[ARITH_ss][]>>
      simp[GSYM LEFT_EXISTS_AND_THM,GSYM LEFT_FORALL_IMP_THM] >>
      disch_then(qspec_then`m`mp_tac) >>
      srw_tac[ARITH_ss][]) >>
    strip_tac >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    rfs[] >- (
      fs[] >> rfs[] >> fs[markerTheory.Abbrev_def] >>
      simp[FUNION_FEMPTY_1] >>
      simp[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] >>
      qexists_tac`REMPTY` >> simp[] >>
      qmatch_abbrev_tac`P x y z` >>
      qmatch_assum_abbrev_tac`P x' y z` >>
      `x = x'` by rw[FUN_EQ_THM,Abbr`x`,Abbr`x'`] >> fs[] ) >>
    simp[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < SUM (MAP body_count_def defs)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      simp[SUM_eq_0,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] ) >>
    conj_tac >- (
      rfs[] >> fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,MEM_MAP] >>
      rfs[] ) >>
    fs[FOLDL_UNION_BIGUNION,LET_THM] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
      gen_tac >> strip_tac >>
      disj1_tac >>
      qexists_tac`m` >>
      simp[] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      rfs[] >> fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
      metis_tac[] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[IN_DISJOINT,MEM_GENLIST,EXTENSION] ) >>
    fs[FUNION_FEMPTY_1] >>
    simp[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)` >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT2 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >>
      simp[SUBMAP_FUNION] >>
      rfs[] >> fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,MEM_MAP] >> rfs[] >>
      Cases_on`p0`>>fs[] >> metis_tac[] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`alist_to_fmap q1` >>
    simp[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      qexists_tac`$=` >>
      simp[] ) >>
    match_mp_tac SUBMAP_FUNION >>
    simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    first_x_assum(qspecl_then[`[]`,`[]`,`FEMPTY`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      BasicProvers.CASE_TAC >> fs[syneq_defs_FEMPTY_refl] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
    Q.PAT_ABBREV_TAC`ezz = FST def + X` >>
    qabbrev_tac`p = label_closures ezz (j+1) (bind_fv def 1 ez 0).body` >>
    PairCases_on`p` >>
    full_simp_tac std_ss [] >>
    strip_tac >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
      qexists_tac`0` >>
      Cases_on`def`>>simp[] ) >>
    simp[MEM_GENLIST] >>
    conj_tac >- (
      Cases_on`def`>>qexists_tac`0`>>simp[] ) >>
    simp[Once syneq_exp_cases] >> fs[] >>
    fs[FUNION_FEMPTY_1] >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  strip_tac >- (
    rw[] >> rw[syneq_exp_FEMPTY_refl] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e`,`es`] >>
    rpt strip_tac >>
    qabbrev_tac`p = label_closures ez j e` >> PairCases_on`p`>>fs[LET_THM] >- (
      rfs[] >> simp[Once syneq_exp_cases] ) >>
    qabbrev_tac`q = label_closures_list ez (j + body_count e) es` >> PairCases_on`q`>>fs[] >>
    fs[FOLDL_UNION_BIGUNION] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<body_count e`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      PROVE_TAC[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[IN_DISJOINT,EXTENSION,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >>
      simp[SUBMAP_FUNION] ) >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rpt strip_tac >> res_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`alist_to_fmap q1` >>
    simp[] >>
    conj_tac >- (
      match_mp_tac SUBMAP_FUNION >>
      simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,IMAGE_EQ_SING] >> rfs[MEM_ZIP] >>
    fs[MEM_EL] >> conj_tac >- metis_tac[] >>
    rw[] >> first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >> rfs[] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`p2`,`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + body_count e1) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < body_count e1`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      metis_tac[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[IN_DISJOINT,EXTENSION,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >> match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >- (
      HINT_EXISTS_TAC >> rfs[SUBMAP_FUNION] ) >>
    qexists_tac`alist_to_fmap q1` >>
    rfs[] >>
    match_mp_tac SUBMAP_FUNION >>
    simp[IN_DISJOINT,MEM_GENLIST]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + body_count e1) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < body_count e1`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      metis_tac[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[IN_DISJOINT,EXTENSION,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >> match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >- (
      HINT_EXISTS_TAC >> rfs[SUBMAP_FUNION] ) >>
    qexists_tac`alist_to_fmap q1` >>
    rfs[] >>
    match_mp_tac SUBMAP_FUNION >>
    simp[IN_DISJOINT,MEM_GENLIST]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`,`e3`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + body_count e1) e2` >> PairCases_on`q`>>fs[] >>
    qabbrev_tac`r = label_closures ez (j + body_count e1 + body_count e2) e3` >> PairCases_on`r`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < body_count e1`>>
      lrw[EL_APPEND1,EL_APPEND2] >>
      Cases_on`x < body_count e1 + body_count e2` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_GENLIST] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      reverse conj_tac >-
        metis_tac[SUBSET_UNION,SUBSET_TRANS] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      metis_tac[SUBSET_UNION,SUBSET_TRANS]) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[EXTENSION,IN_DISJOINT,MEM_GENLIST] >>
      match_mp_tac good_code_env_FUNION >>
      simp[EXTENSION,IN_DISJOINT,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >> rfs[SUBMAP_FUNION] ) >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      qexists_tac`alist_to_fmap q1` >>
      rfs[] >>
      match_mp_tac SUBMAP_FUNION >>
      simp[IN_DISJOINT,MEM_GENLIST] >>
      disj1_tac >>
      match_mp_tac SUBMAP_FUNION >>
      simp[IN_DISJOINT,MEM_GENLIST] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`alist_to_fmap r1` >>
    rfs[] >>
    match_mp_tac SUBMAP_FUNION >>
    simp[IN_DISJOINT,MEM_GENLIST] ) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rpt strip_tac >>
    fs[] >- (
      fs[LET_THM,UNCURRY] >> rfs[] ) >>
    qabbrev_tac`p = label_closures ez j e` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + body_count e) es` >>
    PairCases_on`q`>>fs[] >> simp[] >> rfs[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < body_count e`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      metis_tac[SUBSET_UNION,SUBSET_TRANS] ) >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[IN_DISJOINT,EXTENSION,MEM_GENLIST] ) >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      HINT_EXISTS_TAC >> fs[SUBMAP_FUNION] ) >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rw[] >> res_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    HINT_EXISTS_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
    conj_tac >- (
      match_mp_tac SUBMAP_FUNION >>
      simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] ) >>
    rfs[MEM_ZIP,MEM_EL,IMAGE_EQ_SING] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >> rw[FUNION_FEMPTY_2] >>
    fs[LENGTH_NIL]) >>
  rpt gen_tac >> rpt strip_tac >>
  full_simp_tac (std_ss++ARITH_ss) [] >>
  last_x_assum mp_tac >>
  last_x_assum mp_tac >>
  simp[] >> ntac 2 strip_tac >>
  Q.PAT_ABBREV_TAC`ezz = FST def + X` >>
  qabbrev_tac`p = label_closures ezz (j+1) (bind_fv def nz ez k).body` >>
  PairCases_on`p` >>
  full_simp_tac std_ss [] >>
  qabbrev_tac`q = label_closures_defs ez p2 nz (k+1) defs` >>
  PairCases_on`q` >>
  full_simp_tac std_ss [] >>
  `free_labs (bind_fv def nz ez k).body = {}` by (
    fs[] >> Cases_on`def` >> fs[] ) >>
  `free_labs (SND def) = {}` by (
    fs[] >> Cases_on`def` >> fs[] ) >>
  `free_vars (bind_fv def nz ez k).body ⊆ count ezz` by (
    PairCases_on`def`>>simp[bind_fv_def,Abbr`ezz`] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    rpt(qpat_assum`X = {}`kall_tac) >>
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
  last_x_assum(qspecl_then[`ds0++[j]`,`ls0++[def]`,`c0|+(j,bind_fv def nz ez k)`]mp_tac) >>
  discharge_hyps >- (
    qpat_assum`free_labs_defs X = Y`mp_tac >>
    PairCases_on`def` >>
    simp[IMAGE_EQ_SING] >>
    qmatch_abbrev_tac`s ∧ p ∧ (q ∨ (¬q ∧ r)) ⇒ t` >>
    qsuff_tac`s ∧ p ∧ r ⇒ t`>-(
      unabbrev_all_tac >>
      strip_tac >> strip_tac >>
      first_x_assum match_mp_tac >> fs[] ) >>
    map_every qunabbrev_tac[`s`,`p`,`q`,`r`,`t`] >>
    qmatch_abbrev_tac`(q ∨ (¬q ∧ r)) ∧ p ⇒ t` >>
    qsuff_tac`p ∧ r ⇒ t`>-(
      unabbrev_all_tac >>
      strip_tac >> strip_tac >>
      first_x_assum match_mp_tac >> fs[] ) >>
    map_every qunabbrev_tac[`p`,`q`,`r`,`t`] >>
    strip_tac >>
    conj_tac >- (
      gen_tac >> strip_tac >- metis_tac[] >> simp[] ) >>
    conj_tac >- (simp[EXTENSION]>>PROVE_TAC[]) >>
    conj_tac >- fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_asm1_tac >- fsrw_tac[ARITH_ss][] >>
    conj_asm1_tac >- fsrw_tac[ARITH_ss][] >>
    conj_tac >- (
      srw_tac[ARITH_ss][] >>
      res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    conj_asm1_tac >- (
      fsrw_tac[DNF_ss][closed_code_env_def] >>
      ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
      rpt strip_tac >> res_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[] ) >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[EVERY_MAP] >> strip_tac >>
    simp[Once syneq_exp_cases,EVERY_MAP] >>
    conj_tac >- (
      qmatch_abbrev_tac`P <=> Q` >>
      `P` by (
        unabbrev_all_tac >>
        rpt gen_tac >>
        qmatch_abbrev_tac`P ⇒ Q` >>
        qsuff_tac`¬P`>-rw[] >>
        simp[Abbr`P`] >>
        Cases_on`i<nz`>>simp[] >>
        Cases_on`i < LENGTH ls0`>> simp[EL_APPEND1,EL_APPEND2,EL_MAP] >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        Q.PAT_ABBREV_TAC`lss:def list = [x]++y` >>
        simp[EL_APPEND2] >>
        rw[Abbr`lss`] >>
        ONCE_REWRITE_TAC[GSYM MAP] >>
        simp[EL_MAP] ) >>
      simp[] >>
      pop_assum kall_tac >>
      simp[Abbr`P`,Abbr`Q`] >>
      qmatch_assum_abbrev_tac`P <=> Q` >>
      `P` by (
        unabbrev_all_tac >>
        rpt gen_tac >>
        qmatch_abbrev_tac`P ⇒ Q` >>
        qsuff_tac`¬P`>-rw[] >>
        simp[Abbr`P`] >>
        Cases_on`i<nz`>>simp[] >>
        Cases_on`i < LENGTH ls0`>> simp[EL_APPEND1,EL_APPEND2,EL_MAP] >>
        rw[] >>
        ONCE_REWRITE_TAC[GSYM MAP] >>
        simp[EL_MAP] ) >>
      qunabbrev_tac`P` >>
      `Q` by metis_tac[] >>
      pop_assum mp_tac >>
      pop_assum kall_tac >>
      qunabbrev_tac`Q` >>
      ntac 2 (pop_assum kall_tac) >>
      strip_tac >>
      rpt gen_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      strip_tac >> pop_assum mp_tac >>
      Cases_on`i < LENGTH ls0 + 1`>>simp[EL_APPEND2,EL_MAP] >>
      simp[EL_APPEND1] >>
      first_x_assum(qspecl_then[`i`,`l`]mp_tac) >>
      Cases_on`i < LENGTH ds0`>>simp[EL_APPEND1,EL_MAP] >- (
        simp[FAPPLY_FUPDATE_THM] >>
        strip_tac >> strip_tac >> fs[] >>
        `l < j` by metis_tac[MEM_EL] >>
        simp[] ) >>
      `i = LENGTH ls0` by DECIDE_TAC >>
      simp[EL_APPEND2] ) >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Cases_on`v < k`>>simp[EL_APPEND1,EL_APPEND2,ADD1,EL_MAP] >- (
      strip_tac >>
      ntac 2 (first_x_assum (mp_tac o SYM)) >>
      ntac 2 strip_tac >>
      Q.PAT_ABBREV_TAC`c1 = c0 |+ kv` >>
      `syneq_cb_aux c1 v nz ez (INR (EL v ds0)) =
       syneq_cb_aux c0 v nz ez (INR (EL v ds0))` by (
        match_mp_tac syneq_cb_aux_mono_c >>
        simp[EL_MAP,Abbr`c1`,FLOOKUP_UPDATE] >>
        rw[] >> fs[MEM_EL] >>
        metis_tac[LESS_REFL] ) >>
      `syneq_cb_aux c1 v nz ez (INL (EL v ls0)) =
       syneq_cb_aux c0 v nz ez (INL (EL v ls0))` by (
        match_mp_tac syneq_cb_aux_mono_c >>
        simp[EL_MAP,Abbr`c1`,FLOOKUP_UPDATE] >>
        Cases_on`EL v ls0`>>simp[] >>
        fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
        fsrw_tac[DNF_ss][MEM_EL] >>
        `v < LENGTH ls0` by rw[] >>
        metis_tac[NOT_IN_EMPTY]) >>
      simp[] >> strip_tac >> fs[] >>
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >> qexists_tac`c0` >>
      simp[Abbr`c1`] >>
      conj_tac >- metis_tac[LESS_REFL] >>
      rfs[EL_MAP] >>
      qpat_assum`X = Y`kall_tac >>
      qpat_assum`X = Y`kall_tac >>
      qpat_assum`X = Y`mp_tac >>
      qpat_assum`X = Y`mp_tac >>
      Cases_on`EL v ls0` >>
      simp[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      ntac 2 strip_tac >>
      qpat_assum`X = e2`(SUBST1_TAC o SYM) >>
      qpat_assum`X = e1`(SUBST1_TAC o SYM) >>
      qpat_assum`closed_code_env c0`mp_tac >>
      ntac 4 (pop_assum kall_tac) >>
      simp[closed_code_env_def,IN_FRANGE] >>
      fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
      fsrw_tac[DNF_ss][MEM_EL] >>
      metis_tac[] ) >>
    Cases_on`v=k` >- (
      simp[] >> strip_tac >>
      simp[syneq_cb_aux_def] >>
      simp[UNCURRY] >>
      Q.PAT_ABBREV_TAC`V = syneq_cb_V def0 X Y` >>
      conj_asm1_tac >- simp[EVERY_MEM,bind_fv_def,MEM_FILTER,MEM_GENLIST] >>
      `free_vars def1 ⊆ count (def0+ez+nz)` by (
        simp[SUBSET_DEF] >>
        qx_gen_tac`z` >> strip_tac >>
        Cases_on`z < def0`>-simp[Abbr`ezz`,bind_fv_def] >>
        qpat_assum`X ⊆ count (ez + nz)`mp_tac >>
        simp_tac(srw_ss())[SUBSET_DEF] >>
        disch_then(qspec_then`z-def0`mp_tac)>>
        discharge_hyps >- (
          qexists_tac`cbod_fvs (INL (def0,def1))` >>
          simp[] >>
          conj_tac >- ( qexists_tac`z` >> simp[] ) >>
          qexists_tac`(def0,def1)` >>
          simp[] ) >>
        simp[Abbr`ezz`,bind_fv_def] ) >>
      conj_asm1_tac >- (
        simp[EVERY_MEM,bind_fv_def,MEM_MAP,MEM_FILTER,QSORT_MEM,Abbr`V`] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,Abbr`ezz`] >>
        pop_assum mp_tac >>
        simp_tac(srw_ss()++ARITH_ss)[] >>
        srw_tac[ARITH_ss][] >>
        res_tac >> fsrw_tac[ARITH_ss][] ) >>
      qmatch_abbrev_tac`syneq_exp c1 z1 z2 sc def1 bb` >>
      qsuff_tac`syneq_exp FEMPTY z1 z2 sc def1 bb` >- (
        strip_tac >>
        match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
        qexists_tac`FEMPTY` >>
        simp[SUBMAP_FEMPTY] ) >>
      qunabbrev_tac`bb` >>
      rw[bind_fv_def] >> rw[] >>
      rw[Abbr`e`] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`z1`,Abbr`z2`] >>
      conj_tac >- simp[Abbr`sc`,Abbr`V`,syneq_cb_V_def] >>
      reverse conj_tac >- fsrw_tac[ARITH_ss][Abbr`ezz`] >>
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
          simp[Abbr`w`,Abbr`c`,Abbr`P`,Abbr`envs'`,Abbr`rz`] >>
          rw[bind_fv_def] >> rw[] >>
          unabbrev_all_tac >> rw[] >>
          fsrw_tac[ARITH_ss][]) >>
        qho_match_abbrev_tac`THE (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (THE (find_index a w c))` >>
        match_mp_tac THE_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`,Abbr`envs'`,Abbr`rz`] >>
        rw[bind_fv_def] >> rw[] >>
        unabbrev_all_tac >> fsrw_tac[ARITH_ss][]) >>
      simp[Abbr`sc`,Abbr`V`] >>
      Q.PAT_ABBREV_TAC`recs2 = FST X.ceenv` >>
      Q.PAT_ABBREV_TAC`envs2 = SND X.ceenv` >>
      `recs2 = recs` by (
        rw[Abbr`recs2`,bind_fv_def] >>
        rw[] >> unabbrev_all_tac >> rw[] ) >>
      `envs2 = envs'` by (
        rw[Abbr`envs2`,bind_fv_def] >>
        rw[] >> unabbrev_all_tac >> rw[] ) >>
      qpat_assum`Abbrev(envs2 = X)`kall_tac >>
      qpat_assum`Abbrev(recs2 = X)`kall_tac >>
      reverse(rw[]) >- (
        simp[syneq_cb_V_def] >>
        `MEM (x-(def0+nz)) envs'` by (
          simp[Abbr`envs'`,Abbr`envs`,MEM_MAP,MEM_FILTER,QSORT_MEM,Abbr`fvs`] >>
          qexists_tac`x` >> simp[] ) >>
        Q.ISPECL_THEN[`envs'`,`x-(def0+nz)`,`rz`]mp_tac find_index_MEM >>
        simp[] >> disch_then strip_assume_tac >> simp[] >>
        simp[Abbr`rz`] ) >>
      simp[syneq_cb_V_def] >>
      `MEM (x-def0) (LENGTH ls0::recs)` by (
        simp[Abbr`recs`,MEM_FILTER,MEM_GENLIST]) >>
      Q.ISPECL_THEN[`LENGTH ls0::recs`,`x-def0`,`0:num`]mp_tac find_index_MEM >>
      simp[] >> disch_then strip_assume_tac >> simp[] >>
      `i < rz` by simp[Abbr`rz`] >>
      simp[] >>
      Cases_on`i=0` >- (
        simp[] >> fs[] >> DECIDE_TAC ) >>
      simp[] >>
      qpat_assum`EL X Y = x - def0`mp_tac >>
      simp[EL_CONS,PRE_SUB1]) >>
    lrw[EL_CONS] >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[PRE_SUB1,EL_MAP] >>
    Q.PAT_ABBREV_TAC`p = EL X defs` >>
    PairCases_on`p` >>
    simp[syneq_cb_aux_def] >>
    ntac 2 strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`c0` >>
    fsrw_tac[ARITH_ss][] >>
    reverse conj_tac >- (
      conj_tac >- metis_tac[LESS_REFL] >>
      fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
      qsuff_tac `free_labs e1 = {}` >- rw[] >>
      last_x_assum match_mp_tac >>
      qexists_tac`az` >>
      simp[MEM_EL] >>
      qexists_tac`v - (LENGTH ls0 + 1)` >>
      simp[]) >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[] >>
    simp[syneq_cb_V_def] >>
    srw_tac[ARITH_ss][] ) >>
  simp[] >> strip_tac >>
  PairCases_on`def`>>simp[ADD1]>>
  conj_tac >- (
    fsrw_tac[ARITH_ss][] >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x=0`>>lrw[EL_CONS] ) >>
    lrw[LIST_EQ_REWRITE,EL_CONS,ADD1] >>
    Cases_on`x=0` >> lrw[EL_CONS,PRE_SUB1] >>
    Cases_on`x < body_count def1 +1` >>
    lrw[EL_APPEND1,EL_APPEND2] ) >>
  conj_tac >- fsrw_tac[ARITH_ss][] >>
  conj_tac >- (
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  conj_tac >- (
    full_simp_tac std_ss [closed_code_env_def] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_suff >>
    conj_tac >- (
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      conj_tac >- (
        rfs[] >>
        metis_tac[SUBSET_DEF,IN_INSERT,IN_UNION] ) >>
      simp[] >>
      metis_tac[FDOM_alist_to_fmap,SUBSET_DEF,IN_INSERT,IN_UNION] ) >>
    simp[] >>
    metis_tac[SUBSET_DEF,IN_INSERT,IN_UNION]) >>
  conj_tac >- (
    match_mp_tac good_code_env_FUPDATE >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      simp[EXTENSION,IN_DISJOINT,MEM_GENLIST] ) >>
    rpt(qpat_assum`X = {}`kall_tac) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][MEM_GENLIST,SUBSET_DEF] ) >>
    conj_tac >- (
      simp[bind_fv_def,EVERY_MEM,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM,QSORT_MEM] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      ntac 4 (pop_assum kall_tac) >>
      conj_tac >> gen_tac >> strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    conj_tac >- (
      qpat_assum`free_vars p0 ⊆ X`mp_tac >>
      simp[bind_fv_def,SUBSET_DEF] >> strip_tac >>
      qx_gen_tac`v` >> strip_tac >>
      first_x_assum(qspec_then`v`mp_tac) >>
      simp[] >> rw[] >> srw_tac[ARITH_ss][] >>
      qho_match_abbrev_tac`THE (find_index x ls n) < X` >>
      qho_match_abbrev_tac`P (THE (find_index x ls n))` >>
      match_mp_tac THE_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`x`,MEM_MAP,QSORT_MEM] >>
      HINT_EXISTS_TAC >> simp[] ) >>
    PROVE_TAC[] ) >>
  ONCE_REWRITE_TAC[prove(``a ++ x::y = a ++ [x] ++ y``,simp[])] >>
  full_simp_tac std_ss [FUNION_FUPDATE_1] >>
  qmatch_assum_abbrev_tac`syneq_defs (c20 |+ v1) ez ez $= defs1 defs2 U` >>
  `¬MEM j ds0` by metis_tac[LESS_REFL] >>
  simp[FUNION_FUPDATE_2] >>
  qmatch_abbrev_tac`syneq_defs (c21 |+ v2) ez ez $= defs1 defs2 U` >>
  `syneq_defs (c21 |+ v1) ez ez $= defs1 defs2 U` by (
    match_mp_tac (MP_CANON (CONJUNCT2 syneq_exp_c_SUBMAP)) >>
    qexists_tac`c20 |+ v1` >>
    conj_tac >- rw[] >>
    conj_tac >- (
      simp[Abbr`v1`] >>
      simp[SUBMAP_FUPDATE] >>
      match_mp_tac DOMSUB_SUBMAP >>
      simp[] >>
      match_mp_tac SUBMAP_TRANS >>
      qexists_tac`c20` >>
      simp[SUBMAP_DOMSUB] >>
      simp[Abbr`c20`,Abbr`c21`] >>
      Q.ISPECL_THEN[`alist_to_fmap p1`,`alist_to_fmap q1`]mp_tac FUNION_COMM >>
      discharge_hyps >- (
        simp[IN_DISJOINT,MEM_GENLIST] ) >>
      disch_then SUBST1_TAC >>
      simp[FUNION_ASSOC] >>
      match_mp_tac SUBMAP_FUNION >>
      simp[] ) >>
    conj_tac >- (
      metis_tac[CONS_APPEND,MAP,APPEND_ASSOC] ) >>
    conj_tac >- (
      simp[Abbr`defs2`,Abbr`c20`,Abbr`v1`,SUBSET_DEF,MEM_GENLIST] >>
      simp_tac(srw_ss()++DNF_ss++ARITH_ss)[MEM_MAP] >>
      qpat_assum`set q0 ⊆ X`mp_tac >>
      simp[SUBSET_DEF,MEM_GENLIST] ) >>
    simp[closed_code_env_def] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_suff >>
    simp[Abbr`v1`] >>
    qunabbrev_tac`c20` >>
    ho_match_mp_tac IN_FRANGE_FUNION_suff >>
    rator_x_assum`closed_code_env`mp_tac >>
    rator_x_assum`closed_code_env`mp_tac >>
    rator_x_assum`closed_code_env`mp_tac >>
    simp[closed_code_env_def] >>
    metis_tac[SUBSET_DEF,IN_INSERT,IN_UNION] ) >>
  qmatch_assum_abbrev_tac`syneq_exp c10 ezz ezz $= v3 p0` >>
  `syneq_exp (c21 |+ v2) ezz ezz $= v3 p0` by (
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
    qexists_tac`c10` >>
    simp[Abbr`c10`] >>
    conj_tac >- (
      match_mp_tac SUBMAP_TRANS >>
      qexists_tac`c21` >>
      conj_tac >- (
        qunabbrev_tac`c21` >>
        match_mp_tac SUBMAP_FUNION >>
        disj2_tac >>
        conj_tac >- (
          simp[IN_DISJOINT,MEM_GENLIST] >>
          gen_tac >> spose_not_then strip_assume_tac >>
          res_tac >> DECIDE_TAC ) >>
        match_mp_tac SUBMAP_FUNION >>
        simp[] ) >>
      qunabbrev_tac`v2` >>
      simp[SUBMAP_FUPDATE_EQN,Abbr`c21`,MEM_GENLIST] ) >>
    metis_tac[SUBSET_TRANS] ) >>
  qunabbrev_tac`v2` >>
  qspecl_then[`c21|+v1`,`ez`,`ez`,`$=`,`defs1`,`defs2`,`U`]mp_tac(CONJUNCT2 syneq_exp_c_syneq) >>
  simp[] >>
  Q.PAT_ABBREV_TAC`cd = X with body := p0` >>
  disch_then(qspecl_then[`j`,`cd`]mp_tac) >>
  simp[Abbr`v1`,Abbr`cd`] >>
  disch_then match_mp_tac >>
  last_x_assum mp_tac >>
  simp[Abbr`defs1`,IMAGE_EQ_SING] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  metis_tac[])

val _ = export_theory()
