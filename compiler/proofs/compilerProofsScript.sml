open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory pred_setTheory relationTheory arithmeticTheory whileTheory pairTheory quantHeuristicsLib lcsymtacs sortingTheory finite_mapTheory alistTheory optionTheory stringTheory
open SatisfySimps miscLib BigStepTheory terminationTheory semanticsExtraTheory miscTheory ToBytecodeTheory CompilerTheory compilerTerminationTheory IntLangTheory intLangExtraTheory pmatchTheory toIntLangProofsTheory toBytecodeProofsTheory bytecodeTerminationTheory bytecodeExtraTheory bytecodeEvalTheory bigClockTheory replTheory bytecodeClockTheory
val _ = new_theory"compilerProofs"

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀menv c s. let s' = FOLDL (cce_aux menv) s c in
     ALL_DISTINCT (MAP (FST o FST) c) ∧
     EVERY (combin$C $< s.next_label) (MAP (FST o FST) c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP (FST o FST) c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let ((l,ccenv,ce),(az,body)) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile menv (MAP CTEnv ccenv) (TCTail az 0) 0 (cs i) body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   gen_tac >> Induct >- ( simp[Once SWAP_REVERSE] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`menv`,`MAP CTEnv p1`,`TCTail p3 0`,`0`,`s0`,`p4`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   Q.PAT_ABBREV_TAC`s1 = compile menv X Y Z A B` >>
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

val mvars_list_MAP = store_thm("mvars_list_MAP",
  ``∀ls. mvars_list ls = BIGUNION (IMAGE mvars (set ls))``,
  Induct >> simp[])

val mvars_defs_MAP = store_thm("mvars_defs_MAP",
  ``∀ds. mvars_defs ds = BIGUNION (IMAGE mvars_def (set ds))``,
  Induct >> simp[])

val mvars_list_APPEND = store_thm("mvars_list_APPEND",
  ``mvars_list (l1 ++ l2) = mvars_list l1 ∪ mvars_list l2``,
  simp[mvars_list_MAP])

(*
val syneq_exp_mvars = store_thm("syneq_exp_mvars",
  ``(∀z1 z2 V e1 e2. syneq_exp z1 z2 V e1 e2 ⇒ mvars e2 = mvars e1) ∧
    (∀z1 z2 V d1 d2 U. syneq_defs z1 z2 V d1 d2 U ⇒ mvars_defs d2 = mvars_defs d1)``,
  ho_match_mp_tac IntLangTheory.syneq_exp_ind >>
  simp[] >>
  rw[] >>
  TRY (
    Q.PAT_ABBREV_TAC`X = mvars_list es1`>>qunabbrev_tac`X`>>
    fsrw_tac[DNF_ss][mvars_list_MAP,EVERY2_EVERY,EVERY_MEM,Once EXTENSION] >>
    rfs[MEM_ZIP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[MEM_EL] ) >>
*)

val mvars_mkshift = store_thm("mvars_mkshift",
  ``∀f k e. mvars (mkshift f k e) = mvars e``,
  ho_match_mp_tac mkshift_ind >>
  simp[] >> rw[] >>
  TRY (
    fsrw_tac[DNF_ss,ETA_ss][mvars_list_MAP,Once EXTENSION,MEM_MAP] >>
    metis_tac[] ) >>
  fsrw_tac[DNF_ss][mvars_defs_MAP,Once EXTENSION,MEM_MAP,EXISTS_PROD] >>
  rw[] >>
  Cases_on`x ∈ mvars e`>>simp[] >>
  EQ_TAC >> rw[] >> fs[] >- (
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    fsrw_tac[ARITH_ss][] >>
    res_tac >>
    fsrw_tac[ARITH_ss][] >>
    metis_tac[] ) >>
  CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
  qmatch_assum_rename_tac`MEM (a,b,c) defs`[] >>
  map_every qexists_tac [`c`,`b`,`a`] >>
  simp[] >> Cases_on`a`>>simp[])
val _ = export_rewrites["mvars_mkshift"]

;val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ set (free_vars e) ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     set (free_vars e') ⊆ set (free_vars e) ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     mvars e' = mvars e ∧
     mvars_list (MAP (SND o SND o SND) (free_labs ez e')) ⊆ mvars e ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ set (free_vars_list es) ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     set (free_vars_list es') ⊆ set (free_vars_list es) ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     mvars_list es' = mvars_list es ∧
     mvars_list (MAP (SND o SND o SND) (free_labs_list ez es')) ⊆ mvars_list es ∧
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
     mvars_defs defs' = mvars_defs (MAP ($, NONE) defs) ∧
     mvars_list (MAP (SND o SND o SND) (free_labs_defs ez nz k defs')) ⊆ mvars_defs (MAP ($, NONE) defs) ∧
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    conj_tac >- (
      simp[mvars_list_APPEND]>> fs[SUBSET_DEF]) >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,mvars_list_APPEND] ) >>
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
    reverse conj_tac >- (
      reverse conj_tac >- (
        metis_tac[CONS_APPEND,APPEND_ASSOC] ) >>
      fsrw_tac[DNF_ss][mvars_list_APPEND,SUBSET_DEF] >>
      fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] ) >>
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def]  ) >>
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

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀ez menv s e. let s' = compile_code_env menv s e in
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
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP (FST o FST o SND) (free_labs ez e))) ⇒ l1 < l2) ∧
        (∀mn x b. (mn,x) ∈ mvars b ∧ MEM b (MAP (SND o SND o SND) (free_labs ez e)) ⇒
         ∃env. FLOOKUP menv mn = SOME env ∧ MEM x env)
        ⇒
        EVERY (code_env_cd menv (bc0++code)) (free_labs ez e) ∧
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  `MAP SND (free_labs 0 e) = MAP SND (free_labs ez e)` by metis_tac[MAP_SND_free_labs_any_ez] >>
  fs[] >>
  Q.ISPECL_THEN[`menv`,`MAP SND (free_labs ez e)`,`s''`]mp_tac FOLDL_cce_aux_thm >>
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
    conj_tac >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      HINT_EXISTS_TAC >>
      simp[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
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

val code_env_cd_append = store_thm("code_env_cd_append",
  ``∀menv code cd code'. code_env_cd menv code cd ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒ code_env_cd menv (code ++ code') cd``,
  rw[] >> PairCases_on`cd` >>
  fs[code_env_cd_def] >>
  HINT_EXISTS_TAC>>simp[]>>
  HINT_EXISTS_TAC>>simp[])

val good_contab_def = Define`
  good_contab ((m,w,n):contab) ⇔
    ALL_DISTINCT (MAP FST w) ∧
    ALL_DISTINCT (MAP SND w) ∧
    EVERY (combin$C $< n) (MAP FST w) ∧
    set (MAP SND w) ⊆ (FDOM m) ∧
    cmap_linv m w`

val good_labels_def = Define`
  good_labels nl code ⇔
    ALL_DISTINCT (FILTER is_Label code) ∧
    EVERY (combin$C $< nl o dest_Label) (FILTER is_Label code)`

val closed_Clocs_def = Define`
  closed_Clocs Cmenv Cenv Cs ⇔
    (BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE Cmenv)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cs)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cenv)) ⊆ count (LENGTH Cs))`

val closed_vlabs_def = Define`
  closed_vlabs Cmenv Cenv Cs cmnv code ⇔
    EVERY all_vlabs Cs ∧ EVERY all_vlabs Cenv ∧ all_vlabs_menv Cmenv ∧
    (∀cd. cd ∈ vlabs_list Cs ⇒ code_env_cd cmnv code cd) ∧
    (∀cd. cd ∈ vlabs_list Cenv ⇒ code_env_cd cmnv code cd) ∧
    (∀cd. cd ∈ vlabs_menv Cmenv ⇒ code_env_cd cmnv code cd)`

val env_rs_def = Define`
  env_rs menv cenv env rs csz rd s bs ⇔
    good_contab rs.contab ∧
    good_cmap cenv (cmap rs.contab) ∧
    (cenv_dom cenv = FDOM (cmap rs.contab)) ∧
    (cmap rs.contab ' NONE = tuple_cn) ∧
    (∀id. (FLOOKUP (cmap rs.contab) id = SOME ((cmap rs.contab) ' NONE)) ⇒ (id = NONE)) ∧
    let fmv = alist_to_fmap menv in
    let mv = MAP FST o_f fmv in
    let Cs0 = MAP (v_to_Cv mv (cmap rs.contab)) (SND s) in
    let Cenv0 = env_to_Cenv mv (cmap rs.contab) env in
    let Cmenv0 = env_to_Cenv mv (cmap rs.contab) o_f fmv in
    let cmnv = MAP SND o_f rs.rmenv in
    ∃Cmenv Cenv Cs.
    LIST_REL syneq Cs0 Cs ∧ LIST_REL syneq Cenv0 Cenv ∧ fmap_rel (LIST_REL syneq) Cmenv0 Cmenv ∧
    closed_Clocs Cmenv Cenv Cs ∧
    closed_vlabs Cmenv Cenv Cs cmnv bs.code ∧
    (MAP FST rs.renv = MAP FST env) ∧ (mv = MAP FST o_f rs.rmenv) ∧
    LENGTH rs.renv + SIGMA I (IMAGE LENGTH (FRANGE rs.rmenv)) ≤ rs.rsz ∧
    rs.rsz = LENGTH bs.stack ∧
    Cenv_bs rd Cmenv (FST s, Cs) Cenv cmnv (MAP (CTDec o SND) rs.renv) rs.rsz csz bs`

val _ = Parse.overload_on("print_bv",``λm. ov_to_string o bv_to_ov m``)
val print_bv_str_def = Define`print_bv_str m v w = "val "++v++" = "++(print_bv m w)`

val append_cons_lemma = prove(``ls ++ [x] ++ a::b = ls ++ x::a::b``,lrw[])

val MAP_PrintC_thm = store_thm("MAP_PrintC_thm",
  ``∀ls bs bc0 bc1 bs'.
    bs.code = bc0 ++ (MAP PrintC ls) ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs' = bs with <| output := bs.output ++ ls; pc := next_addr bs.inst_length (bc0 ++ (MAP PrintC ls))|>
    ⇒
    bc_next^* bs bs'``,
  Induct >- (
    simp[] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[] >> rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (PrintC h)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality] >>
  qexists_tac`bc0 ++ [PrintC h]` >>
  simp[FILTER_APPEND,SUM_APPEND])

val _ = Parse.overload_on("print_bv_list",``λm vs ws. FLAT (MAP (UNCURRY (print_bv_str m)) (ZIP (vs,ws)))``)

(* TODO: move *)
val closed_under_menv_def = Define`
  closed_under_menv menv env s ⇔
    EVERY (closed menv) s ∧
    EVERY (closed menv) (MAP SND env) ∧
    EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv)`

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o filter (P o concl))
fun contains tms tm = can (find_term (C mem tms)) tm

val err_to_Cerr_def = Define`
  (err_to_Cerr (Rraise Bind_error) = Craise CBind_excv) ∧
  (err_to_Cerr (Rraise Div_error) = Craise CDiv_excv) ∧
  (err_to_Cerr (Rraise Eq_error) = Craise CEq_excv) ∧
  (err_to_Cerr (Rraise (Int_error n)) = Craise (CLitv (IntLit n))) ∧
  (err_to_Cerr (Rtype_error) = Ctype_error) ∧
  (err_to_Cerr (Rtimeout_error) = Ctimeout_error)`
val _ = export_rewrites["err_to_Cerr_def"]

val err_bv_def = Define`
  (err_bv Div_error bv ⇔ bv = Block (block_tag+div_exc_cn) []) ∧
  (err_bv Bind_error bv ⇔ bv = Block (block_tag+bind_exc_cn) []) ∧
  (err_bv Eq_error bv ⇔ bv = Block (block_tag+eq_exc_cn) []) ∧
  (err_bv (Int_error n) bv ⇔ bv = Number n)`

val Cmap_result_Rerr = store_thm("Cmap_result_Rerr",
 ``Cmap_result f (Rerr err) = Cexc (err_to_Cerr err)``,
 Cases_on`err`>>simp[]>>Cases_on`e`>>simp[IntLangTheory.eq_exc_cn_def])

val env_renv_APPEND_suff = store_thm("env_renv_APPEND_suff",
  ``∀rd sz bs l1 l2 l3 l4.
    env_renv rd sz bs l1 l3 ∧ env_renv rd sz bs l2 l4 ⇒ env_renv rd sz bs (l1 ++ l2) (l3 ++ l4)``,
  rw[env_renv_def] >>
  match_mp_tac EVERY2_APPEND_suff >>
  simp[])

val env_renv_imp_incsz_many = store_thm("env_renv_imp_incsz_many",
  ``∀rd sz bs l1 l2 sz' bs' ls. env_renv rd sz bs l1 l2 ∧
    bs' = bs with stack := ls ++ bs.stack ∧
    sz' = sz + LENGTH ls ⇒
    env_renv rd sz' bs' l1 l2``,
  Induct_on`ls` >- simp[] >>
  simp[ADD1] >> rw[] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac env_renv_imp_incsz >>
  qexists_tac`bs with stack := ls++bs.stack` >>
  simp[bc_state_component_equality] >>
  first_x_assum match_mp_tac >>
  qexists_tac`sz` >>
  qexists_tac`bs` >>
  simp[bc_state_component_equality])

val Cv_bv_l2a_mono_mp = MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono)))

val env_renv_append_code = store_thm("env_renv_append_code",
  ``∀rd sz bs l1 l2 bs' ls. env_renv rd sz bs l1 l2  ∧ bs' = bs with code := bs.code ++ ls ⇒
     env_renv rd sz bs' l1 l2``,
  rw[env_renv_def] >>
  match_mp_tac (GEN_ALL (MP_CANON EVERY2_mono)) >>
  HINT_EXISTS_TAC >>
  simp[] >> rpt gen_tac >> BasicProvers.CASE_TAC >>
  strip_tac >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val print_envE_cons = store_thm("print_envE_cons",
  ``print_envE (x::xs) = print_envE[x]++print_envE xs``,
  rw[print_envE_def])

val print_v_ov = store_thm("print_v_ov",
  ``(∀v cm m sm mv. ov_to_string (Cv_to_ov m sm (v_to_Cv mv cm v)) = print_v v)
    ∧ (∀x:envE. T)
    ∧ (∀y:string#v. T)
    ∧ (∀vs:v list. T)``,
  ho_match_mp_tac(TypeBase.induction_of``:v``) >>
  simp[print_v_def,v_to_Cv_def,PrinterTheory.ov_to_string_def] >>
  Cases >> simp[PrinterTheory.ov_to_string_def,print_lit_def] >>
  Cases_on`b`>>simp[PrinterTheory.ov_to_string_def,print_lit_def])

val print_bv_list_print_envE = store_thm("print_bv_list_print_envE",
  ``∀mv pp vars vs cm m Cvs bvs env.
    EVERY2 syneq (MAP (v_to_Cv mv cm) vs) Cvs ∧ EVERY2 (Cv_bv pp) Cvs bvs ∧ LENGTH vars = LENGTH vs ∧
    env = ZIP(vars,vs)
    ⇒
    print_bv_list m vars bvs = print_envE env``,
  ntac 2 gen_tac >>
  Induct >- ( Cases >> simp[print_envE_def] ) >>
  qx_gen_tac`x`>>
  qx_gen_tac`ws`>>
  ntac 2 gen_tac >>
  map_every qx_gen_tac[`wvs`,`wbs`] >>
  ntac 2 strip_tac >>
  `∃v vs. ws = v::vs` by ( Cases_on`ws`>>fs[] ) >>
  `∃Cv Cvs. wvs = Cv::Cvs` by ( Cases_on`wvs`>>fs[EVERY2_EVERY] ) >>
  `∃bv bvs. wbs = bv::bvs` by ( Cases_on`wbs`>>fs[EVERY2_EVERY] ) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[Once print_envE_cons] >>
  first_x_assum(qspecl_then[`vs`,`cm`,`m`,`Cvs`,`bvs`]mp_tac) >>
  simp[] >>
  discharge_hyps >- fs[EVERY2_EVERY] >> rw[] >>
  rw[print_envE_def,print_bv_str_def] >>
  fs[EVERY2_EVERY] >>
  imp_res_tac Cv_bv_ov >>
  `bv_to_ov m bv = Cv_to_ov m (FST pp).sm (v_to_Cv mv cm v)` by
    metis_tac[syneq_ov] >>
  pop_assum SUBST1_TAC >>
  simp[print_v_ov])

val between_labels_def = Define`
  between_labels bc l1 l2 ⇔
  ALL_DISTINCT (FILTER is_Label bc) ∧
  EVERY (between l1 l2) (MAP dest_Label (FILTER is_Label bc)) ∧
  l1 ≤ l2`

val FOLDL_emit_thm = store_thm("FOLDL_emit_thm",
  ``∀ls s. FOLDL (λs i. s with out := i::s.out) s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality])

val compile_news_thm = store_thm("compile_news_thm",
  ``∀vs cs i. let cs' = compile_news cs i vs in
      ∃code.
        (cs'.out = REVERSE code ++ cs.out) ∧
        (cs'.next_label = cs.next_label) ∧
        EVERY ($~ o is_Label) code ∧
        ∀bs bc0 u ws st.
          (bs.code = bc0 ++ code) ∧
          (bs.pc = next_addr bs.inst_length bc0) ∧
          (bs.stack = Block u ws::st) ∧
          (LENGTH ws = LENGTH vs + i)
          ⇒
          let bs' =
          bs with <| pc := next_addr bs.inst_length (bc0 ++ code)
                   ; stack := (REVERSE (DROP i ws))++st
                   (*
                   ; output := if pr then
                     FLAT (REVERSE (MAP (REVERSE o (UNCURRY (print_bv_str bs.cons_names))) (ZIP (vs, DROP i ws)))) ++ bs.output
                     else bs.output
                     *)
                   |> in
          bc_next^* bs bs'``,
  Induct >- (
    simp[compile_news_def,Once SWAP_REVERSE,DROP_LENGTH_NIL] >> rw[] >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm] >>
    `bc_fetch bs = SOME(Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[] ) >>
    simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
    simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND]) >>
  qx_gen_tac`v` >>
  simp[compile_news_def,FOLDL_emit_thm] >>
  rpt gen_tac >>
  simp[append_cons_lemma,IMPLODE_EXPLODE_I,REVERSE_APPEND] >>
  REWRITE_TAC[prove(``REVERSE (MAP PrintC v) ++ ls ++ cs.out = REVERSE (MAP PrintC v) ++ (ls ++ cs.out)``,lrw[])] >>
  REWRITE_TAC[prove(``[a;b;c;d;e;f;g]++ls = a::b::c::d::e::f::g::ls``,lrw[])] >>
  Q.PAT_ABBREV_TAC`c1 = Stack (El i)::X` >>
  (*
  Q.PAT_ABBREV_TAC`cs0 = if pr then X else Y:compiler_result` >>
  *)
  Q.PAT_ABBREV_TAC`cs1 = cs0 with out := X` >>
  first_x_assum(qspecl_then[`cs1`,`i+1`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  `cs1.next_label = cs.next_label ∧ ∃code. cs1.out = code ++ c1 ∧ EVERY ($~ o is_Label) code` by (
    simp[Abbr`cs1`] >> rw[] >> rw[EVERY_REVERSE,EVERY_MAP] ) >>
  simp[Once SWAP_REVERSE,EVERY_REVERSE,Abbr`c1`] >>
  rpt gen_tac >> strip_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 1) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (El i))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 2) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  (*
  `bc_next^* bs1 (bs1 with <| output := if pr then REVERSE (print_bv_str bs.cons_names v (EL i ws)) ++ bs.output else bs.output
                            ; pc := next_addr bs'.inst_length (BUTLASTN (LENGTH c0 + 1) bs'.code)|>)` by (
    reverse(Cases_on`pr`) >- (
      simp[Once RTC_CASES1] >> disj1_tac >>
      simp[bc_state_component_equality,Abbr`bs1`] >>
      simp[Abbr`bs'`] >> fs[Abbr`cs1`,Abbr`cs0`] >>
      rw[] >>
      simp[BUTLASTN_APPEND1,BUTLASTN_APPEND2,BUTLASTN] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    fs[Abbr`cs0`,Abbr`cs1`] >> rw[] >> fs[EVERY_REVERSE,EVERY_MAP] >> rw[] >>
    fs[REVERSE_APPEND] >>
    first_x_assum(qspec_then`bs`kall_tac) >>
    qpat_assum`X = Y.next_label`kall_tac >>
    qpat_assum`X.out = Y`kall_tac >>
    simp[print_bv_str_def,REVERSE_APPEND] >>
    qmatch_assum_abbrev_tac `bs.code = bc0 ++ c3 ++ c2 ++ c1 ++ c0` >>
    `bc_next^* bs1 (bs1 with <| output := REVERSE ("val "++v++" = ") ++ bs1.output
                              ; pc := next_addr bs1.inst_length (bc0 ++ c3 ++ c2 ++ (TAKE 3 c1)) |>)` by (
      match_mp_tac MAP_PrintC_thm >>
      qexists_tac`"val "++v++" = "` >>
      simp[bc_state_component_equality] >>
      qexists_tac`bc0 ++ TAKE 3 c3` >>
      simp[Abbr`bs1`,Abbr`c3`,Abbr`c1`] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3` >>
    qsuff_tac`bc_next^* bs2 bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qpat_assum`bc_next^* bs1 bs2`kall_tac >> qunabbrev_tac`bs1` >> fs[] >>
    `bc_fetch bs2 = SOME (Stack (Load 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ c3 ++ c2 ++ TAKE 3 c1` >>
      simp[Abbr`c1`] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    pop_assum kall_tac >>
    simp[Abbr`bs2`,bc_eval_stack_def] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3` >>
    `bc_fetch bs1 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`] >>
      qexists_tac`bc0 ++ c3 ++ c2 ++ TAKE 4 c1` >>
      simp[Abbr`c1`] >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    pop_assum kall_tac >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3` >>
    `bs1 = bs3` by (
      simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs3`,IMPLODE_EXPLODE_I] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`bs'`] >>
      simp[BUTLASTN_APPEND1,BUTLASTN_APPEND2] >>
      REWRITE_TAC[BUTLASTN_compute] >>
      simp[TAKE_APPEND1,TAKE_APPEND2,Abbr`c2`,Abbr`c1`,SUM_APPEND,FILTER_APPEND,Abbr`c3`]) >>
    rw[] ) >>
  *)
  fs[Abbr`cs1`] >> BasicProvers.VAR_EQ_TAC >>
  (*
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  qsuff_tac`bc_next^* bs2 bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  qpat_assum`bc_next^* bs1 X`kall_tac >> qunabbrev_tac`bs1` >>
  *)
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (Store 1))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`c0` >>
    simp[] >>
    simp[FILTER_APPEND,SUM_APPEND]
    (*
    qexists_tac`BUTLASTN (LENGTH c0 + 1) bs'.code` >>
    simp[Abbr`bs'`,BUTLASTN_APPEND1] >>
    REWRITE_TAC[BUTLASTN_compute] >>
    simp[TAKE_APPEND1,TAKE_APPEND2] >>
    fs[Abbr`cs1`,Abbr`cs0`] >>
    Cases_on`pr`>>fs[]>>rw[]>>simp[TAKE_APPEND1,TAKE_APPEND2] *)) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  first_x_assum(qspecl_then[`bs1`,`BUTLASTN (LENGTH c0) bs.code`]mp_tac) >>
  simp[Abbr`bs1`] >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    simp[Abbr`P`,BUTLASTN_APPEND1,BUTLASTN] >>
    REWRITE_TAC[BUTLASTN_compute] >>
    simp[Abbr`bs'`] >>
    (*
    Cases_on`pr`>>fs[Abbr`cs0`,Abbr`cs1`]>>rw[]>>
    *)
    simp[SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  qmatch_abbrev_tac`bc_next^* bs1' bs2 ⇒ bc_next^* bs1 bs'` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] ) >>
  `bs2 = bs'` by (
    simp[Abbr`bs2`,Abbr`bs'`,bc_state_component_equality] >>
    conj_asm1_tac >- (
      lrw[LIST_EQ_REWRITE,EL_REVERSE,PRE_SUB1,EL_APPEND1,EL_APPEND2,ADD1] >>
      Cases_on`x < LENGTH vs`>>
      lrw[EL_DROP,EL_REVERSE,PRE_SUB1,EL_APPEND1,EL_APPEND2,ADD1] >>
      `x = LENGTH vs` by DECIDE_TAC >>
      simp[] ) >>
    (*
    conj_tac >- (
      simp[BUTLASTN_APPEND1,BUTLASTN] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    pop_assum mp_tac >>
    *)
    simp[BUTLASTN_APPEND1,BUTLASTN] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    simp[Once SWAP_REVERSE] ) >>
  metis_tac[])

val Cevaluate_closed_vlabs = store_thm("Cevaluate_closed_vlabs",
  ``∀menv s env exp res cmnv code.
    closed_vlabs menv env (SND s) cmnv code ∧
    Cevaluate menv s env exp res ∧ all_labs exp ∧
    (∀cd. MEM cd (free_labs (LENGTH env) exp) ⇒ code_env_cd cmnv code cd)
    ⇒
    closed_vlabs menv env (SND(FST res)) cmnv code ∧
    (∀v. SND res = Cval v ∨ SND res = Cexc (Craise v) ⇒
      all_vlabs v ∧
      vlabs v ⊆ vlabs_menv menv ∪ vlabs_list (SND s) ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp))``,
  rpt gen_tac >>
  simp[closed_vlabs_def] >>
  strip_tac >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_vlabs)>>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs)>>
  simp[] >>
  rw[] >> fs[SUBSET_DEF] >>
  metis_tac[])

val Cevaluate_closed_Clocs = store_thm("Cevaluate_closed_Clocs",
  ``∀menv s env exp res.
    closed_Clocs menv env (SND s) ∧
    Cevaluate menv s env exp res
    ⇒
    closed_Clocs menv env (SND(FST res)) ∧
    (∀v. SND res = Cval v ∨ SND res = Cexc (Craise v) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res))))``,
  rw[closed_Clocs_def] >>
  TRY (
    match_mp_tac SUBSET_TRANS >>
    HINT_EXISTS_TAC >> simp[] >>
    qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
    simp[SUBSET_DEF] ) >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_Clocs) >>
  simp[])

val compile_Cexp_thm = store_thm("compile_Cexp_thm",
  ``∀rmenv renv rsz cs exp.
      set (free_vars exp) ⊆ count (LENGTH renv)
    ∧ no_labs exp
    ⇒
    let cs' = compile_Cexp rmenv renv rsz cs exp in
    ∃c0 code. cs'.out = REVERSE code ++ REVERSE c0 ++ cs.out ∧ between_labels (code++c0) cs.next_label cs'.next_label ∧
    ∀menv s env res rd csz bs bc0.
      Cevaluate menv s env exp res
    ∧ closed_Clocs menv env (SND s)
    ∧ closed_vlabs menv env (SND s) rmenv bc0
    ∧ Cenv_bs rd menv s env rmenv renv rsz csz (bs with code := bc0)
    ∧ bs.code = bc0 ++ c0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.clock = SOME (FST s)
    ∧ good_labels cs.next_label bc0
    ∧ (∀mn x. (mn,x) ∈ mvars exp ⇒ ∃env. FLOOKUP rmenv mn = SOME env ∧ MEM x env)
    ⇒
    case SND res of
    | Cval v =>
        ∃s' w. syneq v w ∧ LIST_REL syneq (SND(FST res)) s' ∧ closed_vlabs menv env s' rmenv (bc0++c0) ∧ closed_Clocs menv env s' ∧
        all_Clocs w ⊆ count (LENGTH s') ∧ all_vlabs w ∧ (∀cd. cd ∈ vlabs w ⇒ code_env_cd rmenv (bc0++c0) cd) ∧
        code_for_push rd menv bs (bc0++c0) bc0 (c0++code) s (FST(FST res),s') env [w] rmenv renv rsz csz
    | Cexc (Craise err) =>
      ∀st hdl sp ig.
        bs.stack = ig++StackPtr sp::CodePtr hdl::st
      ∧ bs.handler = LENGTH st + 1
      ∧ csz ≤ LENGTH st
      ⇒
        ∃s' w. syneq err w ∧ LIST_REL syneq (SND(FST res)) s' ∧ closed_vlabs menv env s' rmenv (bc0++c0) ∧ closed_Clocs menv env s' ∧
        code_for_return rd bs (bc0++c0) st hdl sp w s (FST(FST res),s')
    | Cexc Ctimeout_error =>
      ∃bs'. bc_next^* bs bs' ∧ bs'.clock = SOME 0 ∧ bc_fetch bs' = SOME Tick
    | _ => T``,
  rw[compile_Cexp_def] >>
  qspecl_then[`LENGTH renv`,`cs.next_label`,`exp`]mp_tac (CONJUNCT1 label_closures_thm) >>
  simp[] >> strip_tac >>
  qspecl_then[`LENGTH renv`,`rmenv`,`cs with next_label := nl`,`Ce`]mp_tac compile_code_env_thm >>
  simp[] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST] ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  qspecl_then[`rmenv`,`renv`,`TCNonTail`,`rsz`,`cs'`,`Ce`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs''`] >>
  qexists_tac`c0` >> simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    simp[between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >>
    fsrw_tac[DNF_ss][MEM_GENLIST] >>
    res_tac >> DECIDE_TAC ) >>
  rpt gen_tac >>
  strip_tac >>
  first_x_assum(qspecl_then[`bs`,`bc0`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[Once CONJ_ASSOC] >>
    conj_tac >- (
      simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,is_Label_rwt] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,good_labels_def] >>
      rw[] >> res_tac >> DECIDE_TAC ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,mvars_list_MAP] >>
    metis_tac[]) >>
  strip_tac >>
  `LENGTH renv = LENGTH env` by (
    fs[Cenv_bs_def,env_renv_def,EVERY2_EVERY] ) >>
  fs[] >>
  qmatch_assum_abbrev_tac`bc_next bs bs0` >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 Cevaluate_syneq) >>
  simp[] >>
  disch_then(qspecl_then[`$=`,`menv`,`s`,`env`,`Ce`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`Cres`strip_assume_tac) >>
  qspecl_then[`menv`,`s`,`env`,`Ce`,`Cres`]mp_tac(CONJUNCT1 compile_val) >>
  PairCases_on`Cres`>>simp[]>>
  disch_then(qspecl_then[`rd`,`rmenv`,`cs'`,`renv`,`rsz`,`csz`,`bs0`,`bc0 ++ c0`,`REVERSE c1`,`bc0 ++ c0`,`REVERSE c1`,`[]`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs0`] >>
    fs[closed_Clocs_def] >>
    simp[CONJ_ASSOC] >>
    qmatch_abbrev_tac`(A ∧ B) ∧ C` >>
    `B ∧ C` by (
      simp[Abbr`A`,Abbr`B`,Abbr`C`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,good_labels_def] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[Abbr`A`,Abbr`B`,Abbr`C`,GSYM CONJ_ASSOC] >>
    fs[closed_vlabs_def] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[SUBSET_TRANS] >>
    match_mp_tac Cenv_bs_with_irr >>
    qexists_tac`bs with code := bc0 ++ c0` >> simp[] >>
    match_mp_tac Cenv_bs_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] ) >>
  PairCases_on`res`>>fs[]>>
  strip_tac >>
  Cases_on`res2`>>fs[]>>rfs[]>-(
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    qspecl_then[`menv`,`s`,`env`,`Ce`,`((Cres0,Cres1),Cres2)`]mp_tac Cevaluate_closed_Clocs >>
    simp[] >> strip_tac >>
    qspecl_then[`menv`,`s`,`env`,`Ce`,`((Cres0,Cres1),Cres2)`,`rmenv`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
    simp[] >>
    discharge_hyps >- (
      fs[EVERY_MEM] >>
      fs[closed_vlabs_def] >>
      `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
        fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      metis_tac[code_env_cd_append] ) >>
    simp[] >> strip_tac >>
    conj_tac >- (
      fs[closed_vlabs_def,SUBSET_DEF] >>
      fs[EVERY_MEM] >>
      rw[] >> res_tac >> TRY(metis_tac[]) >>
      match_mp_tac code_env_cd_append >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    rw[] >>
    ntac 6 (pop_assum kall_tac) >>
    pop_assum mp_tac >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[]>>
    simp[Abbr`bs0`] >>
    map_every qx_gen_tac [`rf`,`rd'`,`ck`,`bv`] >>
    strip_tac >>
    map_every qexists_tac [`rf`,`rd'`,`ck`,`bv`] >>
    simp[] >>
    simp[Once RTC_CASES1] >>
    disj2_tac >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  rw[] >>
  BasicProvers.CASE_TAC >> fs[] >- (
    first_x_assum(qspec_then`TCNonTail`mp_tac) >>
    simp[Abbr`bs0`] >>
    metis_tac[RTC_SUBSET,RTC_TRANSITIVE,transitive_def] ) >>
  rpt gen_tac >> strip_tac >>
  rpt HINT_EXISTS_TAC >>
  fs[] >>
  qmatch_assum_abbrev_tac`Cevaluate menv s env Ce ((Cres0,Cres1),Cres2)` >>
  qspecl_then[`menv`,`s`,`env`,`Ce`,`((Cres0,Cres1),Cres2)`]mp_tac Cevaluate_closed_Clocs >>
  simp[] >> strip_tac >>
  qspecl_then[`menv`,`s`,`env`,`Ce`,`((Cres0,Cres1),Cres2)`,`rmenv`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
  simp[] >>
  discharge_hyps >- (
    fs[EVERY_MEM] >>
    fs[closed_vlabs_def] >>
    `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    metis_tac[code_env_cd_append] ) >>
  rw[] >>
  first_x_assum(qspec_then`TCNonTail`mp_tac) >>
  simp[Abbr`bs0`] >>
  disch_then(qspec_then`ig`mp_tac) >>
  simp[] >>
  simp[code_for_return_def] >>
  simp_tac(srw_ss()++DNF_ss)[]>>
  map_every qx_gen_tac [`bv`,`rf`,`rd'`,`ck`] >>
  strip_tac >>
  map_every qexists_tac [`bv`,`rf`,`rd'`,`ck`] >>
  simp[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[] )

val mvars_exp_to_Cexp = store_thm("mvars_exp_to_Cexp",
  ``(∀m e. mvars (exp_to_Cexp m e) = { (mn, the 0 (find_index x (fapply [] mn m.mvars) 0)) | Long mn x ∈ FV e })``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once EXTENSION] >>
    metis_tac[] ) >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[mvars_list_MAP,exps_to_Cexps_MAP,FV_list_MAP] >>
    rw[Once EXTENSION,MEM_MAP] >>
    fs[EVERY_MEM] >>
    fsrw_tac[DNF_ss][] >>
    fs[Once EXTENSION] >>
    metis_tac[] ) >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once EXTENSION] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[ToIntLangTheory.shift_def] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[]) >>
  strip_tac >- (
    gen_tac >> Cases >>
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> rw[] >>
    fs[Once EXTENSION,ToIntLangTheory.shift_def] >>

    remove_mat_var

    metis_tac[] ) >>

  cheat)

val compile_fake_exp_thm = store_thm("compile_fake_exp_thm",
  ``∀rmenv m renv rsz cs vars expf.
    let exp = expf (Con NONE (MAP (Var o Short) (REVERSE vars))) in
    SFV exp ⊆ set m.bvars
    ∧ LENGTH renv = LENGTH m.bvars
    ⇒
    let cs' = compile_fake_exp rmenv m renv rsz cs vars expf in
    ∃code. cs'.out = REVERSE code ++ cs.out ∧ between_labels code cs.next_label cs'.next_label ∧
    ∀menv tup cenv env s s' beh rs csz rd bs bc0.
    evaluate T menv cenv s env exp (s',beh)
    ∧ closed_under_menv menv env (SND s)
    ∧ closed_under_cenv cenv menv env (SND s)
    ∧ all_cns_exp exp ⊆ cenv_dom cenv ∪ {NONE}
    ∧ FV exp ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
    ∧ ALL_DISTINCT vars
    ∧ env_rs menv cenv env rs csz rd s (bs with code := bc0)
    ∧ m.bvars = MAP FST env
    ∧ m.mvars = MAP FST o_f alist_to_fmap menv
    ∧ m.cnmap = cmap rs.contab
    ∧ rmenv = MAP SND o_f rs.rmenv
    ∧ renv = MAP (CTDec o SND) rs.renv
    ∧ rs.rnext_label = cs.next_label
    ∧ rsz = rs.rsz
    ∧ bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ IS_SOME bs.clock
    ∧ good_labels rs.rnext_label bc0
    ⇒
    (∀vs. (beh = Rval (Conv NONE (REVERSE vs))) ∧ (LENGTH vars = LENGTH vs) ⇒
      ∃Cws bvs rf rd' Cs'.
      let tt = block_tag + (cmap rs.contab) ' NONE in
      let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ code); stack := (Block tt bvs)::bs.stack; refs := rf; clock := SOME (FST s')|> in
      bc_next^* bs bs' ∧
      LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (REVERSE vs)) Cws ∧
      LIST_REL (Cv_bv (mk_pp rd' bs')) Cws bvs ∧
      LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (SND s')) Cs' ∧
      EVERY all_vlabs Cs' ∧ EVERY all_vlabs Cws
      ∧ BIGUNION (IMAGE all_Clocs (set Cws)) ⊆ count (LENGTH Cs')
      ∧ BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs') ∧
      (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd rmenv (bc0 ++ code) cd) ∧
      (∀cd. cd ∈ vlabs_list Cws ⇒ code_env_cd rmenv (bc0 ++ code) cd) ∧
      LENGTH (SND s) ≤ LENGTH (SND s') ∧
      s_refs rd' (FST s',Cs') bs' ∧
      DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
      rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls) ∧
    (∀err. (beh = Rerr (Rraise err)) ⇒
      ∀ig h0 sp st0.
        bs.stack = ig++StackPtr h0::CodePtr sp::st0
      ∧ bs.handler = LENGTH st0 + 1
      ∧ csz ≤ LENGTH st0
      ⇒
      ∃bv rf rd' Cs'.
      let bs' = bs with <|pc := sp; stack := bv::st0; handler := h0; refs := rf; clock := SOME (FST s')|> in
      bc_next^* bs bs' ∧
      err_bv err bv ∧
      LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (SND s')) Cs' ∧
      EVERY all_vlabs Cs' ∧ BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs') ∧
      (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd rmenv (bc0 ++ code) cd) ∧
      LENGTH (SND s) ≤ LENGTH (SND s') ∧
      s_refs rd' (FST s',Cs') bs' ∧
      DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
      rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls) ∧
    ((beh = Rerr Rtimeout_error) ⇒
      ∃bs'. bc_next^* bs bs' ∧ (bs'.clock = SOME 0) ∧ bc_fetch bs' = SOME Tick)``,
  rw[] >>
  pop_assum mp_tac >>
  simp[compile_fake_exp_def] >>
  strip_tac >>
  `cs' = compile_Cexp rmenv renv rsz cs (exp_to_Cexp m exp)` by (
    simp[Abbr`exp`,Abbr`cs'`,combinTheory.o_DEF] ) >>
  qpat_assum`Abbrev(cs' = X)`kall_tac >>
  pop_assum(assume_tac o REWRITE_RULE [Once(GSYM markerTheory.Abbrev_def)]) >>
  qspecl_then[`rmenv`,`renv`,`rsz`,`cs`,`exp_to_Cexp m exp`]mp_tac compile_Cexp_thm >>
  discharge_hyps >- (
    simp[] >>
    match_mp_tac free_vars_exp_to_Cexp_matchable >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM,MEM_FLAT]) >>
  simp[] >>
  disch_then(qx_choosel_then[`c0`,`c1`]strip_assume_tac) >>
  qexists_tac`c0 ++ c1` >>
  simp[] >>
  conj_tac >- (
    fs[between_labels_def,FILTER_APPEND] >>
    metis_tac[PERM_APPEND,ALL_DISTINCT_PERM] ) >>
  rpt gen_tac >>
  strip_tac >>
  qspecl_then[`T`,`menv`,`cenv`,`s`,`env`,`exp`,`s',beh`]mp_tac(CONJUNCT1 exp_to_Cexp_thm1) >>
  simp[] >>
  Cases_on`beh=Rerr Rtype_error`>>simp[]>>
  discharge_hyps >- (
    fs[closed_under_menv_def] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,closed_under_cenv_def,FORALL_PROD,EXISTS_PROD, cenv_dom_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  disch_then(qspec_then`m.cnmap`mp_tac) >>
  discharge_hyps >- (
    fs[env_rs_def] >>
    rator_x_assum`good_cmap`mp_tac >>
    qpat_assum`X = FDOM (cmap rs.contab)`mp_tac >>
    simp[SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,EXISTS_PROD] >>
    qpat_assum`Short "" ∉ X`mp_tac >>
    qpat_assum`∀id. X ⇒ Y = Short ""`mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[good_cmap_def,FLOOKUP_DEF] >>
    ntac 4 strip_tac >>
    simp[FORALL_PROD] >>
    pop_assum(assume_tac o SIMP_RULE(srw_ss())[FORALL_PROD]) >>
    qpat_assum`X ∉ Y`(assume_tac o SIMP_RULE(srw_ss())[MEM_MAP,FORALL_PROD]) >>
    metis_tac[PAIR_EQ] ) >>
  Q.PAT_ABBREV_TAC`m' = exp_to_Cexp_state_bvars_fupd X Y` >>
  `m' = m` by simp[ToIntLangTheory.exp_to_Cexp_state_component_equality,Abbr`m'`] >>
  qunabbrev_tac`m'`>>pop_assum SUBST1_TAC >>
  qmatch_abbrev_tac`G` >>
  rator_x_assum`env_rs`(mp_tac o SIMP_RULE std_ss [env_rs_def]) >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fmv = MAP FST o_f alist_to_fmap menv` >>
  rfs[] >>
  Q.PAT_ABBREV_TAC`Csf:v list -> Cv list = MAP X` >>
  Q.PAT_ABBREV_TAC`Cenvf = env_to_Cenv X Y` >>
  strip_tac >>
  qunabbrev_tac`G` >>
  simp[EXISTS_PROD] >>
  disch_then(qx_choosel_then[`Cs0'`,`Cv0`]strip_assume_tac) >>
  qmatch_assum_abbrev_tac`Cevaluate Cmenv0 Cs0 Cenv0 Cexp Cres0` >>
  qspecl_then[`Cmenv0`,`Cs0`,`Cenv0`,`Cexp`,`Cres0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
  disch_then(qspecl_then[`$=`,`Cmenv`,`FST s,Cs`,`Cenv`,`Cexp`]mp_tac) >>
  `LENGTH Cenv0 = LENGTH env` by rw[Abbr`Cenv0`,Abbr`Cenvf`,env_to_Cenv_MAP] >>
  `LENGTH Cenv = LENGTH env` by fs[EVERY2_EVERY] >>
  simp[EXISTS_PROD] >>
  discharge_hyps >- (
    simp[Abbr`Cs0`] >>
    conj_tac >- (
      match_mp_tac (CONJUNCT1 syneq_exp_refl) >>
      simp[] ) >>
    qpat_assum`LIST_REL syneq Cenv0 Cenv`mp_tac >>
    ntac 2 (pop_assum mp_tac) >>
    rfs[MAP_EQ_EVERY2] >>
    rpt (pop_assum kall_tac) >>
    simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] ) >>
  disch_then(qx_choosel_then[`Cs'`,`Cv`]strip_assume_tac) >>
  fs[Abbr`Cres0`] >>
  first_x_assum(qspecl_then[`Cmenv`,`FST s,Cs`,`Cenv`,`(FST s',Cs'),Cv`,`rd`,`csz`,`bs`,`bc0`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    rfs[] >>
    fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
    Cases_on`bs.clock`>>fs[] >>
    simp[Abbr`Cexp`,mvars_exp_to_Cexp] >>
    simp[GSYM LEFT_FORALL_IMP_THM] >>
    qpat_assum`FV exp ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> rpt strip_tac >>
    qmatch_assum_rename_tac`Long mn v ∈ FV exp`[] >>
    first_x_assum(qspec_then`Long mn v`mp_tac) >>
    simp[MEM_MAP,MEM_FLAT] >>
    srw_tac[DNF_ss][MEM_MAP] >>
    rpt(rator_x_assum`fmap_rel`mp_tac) >>
    simp[fmap_rel_def,Abbr`Cmenv0`] >>
    simp[FLOOKUP_DEF] >>
    PairCases_on`x`>>fs[MEM_MAP,EXISTS_PROD] >>
    strip_tac >> strip_tac >>
    conj_tac >- metis_tac[] >>
    first_x_assum(qspec_then`x0`mp_tac) >>
    discharge_hyps >- metis_tac[] >>
    `x0 ∈ FDOM rs.rmenv` by (
      simp[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[o_f_FAPPLY,MAP_MAP_o] >>
    simp[env_renv_def,option_case_NONE_F] >>
    first_x_assum(qspec_then`x0`mp_tac) >>
    discharge_hyps >- metis_tac[] >>
    simp[Abbr`Cenvf`,env_to_Cenv_MAP] >>
    rpt strip_tac >>
    qexists_tac`FST y` >>
    reverse BasicProvers.CASE_TAC >- metis_tac[] >>


    ) >>
  Cases_on`beh`>>fs[]>>BasicProvers.VAR_EQ_TAC>>fs[]>>BasicProvers.VAR_EQ_TAC>-(
    disch_then(qx_choosel_then[`Cs1`,`w`]strip_assume_tac) >>
    gen_tac >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
    simp[markerTheory.Abbrev_def] >>
    rator_x_assum`code_for_push`mp_tac >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`rd'`,`ck`,`bv`] >>
    strip_tac >>
    qpat_assum`syneq X v'`mp_tac >>
    simp[v_to_Cv_def,FLOOKUP_DEF] >>
    `NONE ∈ FDOM (cmap rs.contab)` by (
      fs[cenv_dom_def, EXTENSION] >> metis_tac[] ) >>
    simp[] >>
    simp[Once IntLangTheory.syneq_cases] >>
    disch_then(Q.X_CHOOSE_THEN`Cvs0`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`v' = CConv tt Cvs0` >>
    `syneq (CConv tt Cvs0) w` by metis_tac[syneq_trans] >>
    pop_assum mp_tac >>
    rator_x_assum`syneq`kall_tac >>
    rator_x_assum`syneq`kall_tac >>
    BasicProvers.VAR_EQ_TAC >>
    simp[Once IntLangTheory.syneq_cases] >>
    disch_then(Q.X_CHOOSE_THEN`Cws`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`LIST_REL syneq Cvs Cvs0` >>
    `LIST_REL syneq Cvs Cws` by metis_tac[EVERY2_syneq_trans] >>
    pop_assum mp_tac >>
    qpat_assum`EVERY2 syneq X Y`kall_tac >>
    qpat_assum`EVERY2 syneq X Y`kall_tac >>
    BasicProvers.VAR_EQ_TAC >>
    strip_tac >>
    rator_x_assum`Cv_bv`mp_tac >>
    simp[Once Cv_bv_cases] >>
    disch_then(Q.X_CHOOSE_THEN`bvs`strip_assume_tac) >>
    `ck = SOME (FST s')` by (
      fs[Cenv_bs_def,s_refs_def] >>
      imp_res_tac RTC_bc_next_clock_less >>
      Cases_on`bs.clock`>>rfs[optionTheory.OPTREL_def] ) >>
    map_every qexists_tac[`Cws`,`bvs`,`rf`,`rd'`,`Cs1`] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[] >>
    conj_tac >- (
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      rpt strip_tac >>
      res_tac >>
      match_mp_tac Cv_bv_l2a_mono_mp >>
      HINT_EXISTS_TAC >>
      simp[] >>
      rpt strip_tac >>
      match_mp_tac bc_find_loc_aux_append_code >>
      simp[]) >>
    conj_tac >- (
      simp[vs_to_Cvs_MAP] >>
      metis_tac[EVERY2_syneq_trans] ) >>
    fs[closed_vlabs_def,closed_Clocs_def] >>
    fsrw_tac[ETA_ss][] >>
    conj_tac >- (
      rw[] >>
      match_mp_tac code_env_cd_append >> rw[] >>
      fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,between_labels_def,good_labels_def,MEM_FILTER,between_def,EVERY_MEM,MEM_MAP,is_Label_rwt] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    conj_tac >- (
      rw[] >>
      match_mp_tac code_env_cd_append >> rw[] >>
      fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,between_labels_def,good_labels_def,MEM_FILTER,between_def,EVERY_MEM,MEM_MAP,is_Label_rwt] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    conj_tac >- (
      fs[EVERY2_EVERY,Abbr`Csf`] >>
      metis_tac[Cevaluate_store_SUBSET,FST,SND] ) >>
    fs[Cenv_bs_def] >>
    match_mp_tac s_refs_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality]) >>
  fs[Cmap_result_Rerr] >>
  BasicProvers.VAR_EQ_TAC >>
  fs[] >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on`e=Rtimeout_error`>>fs[]>-(
    BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    metis_tac[]) >>
  Cases_on`e`>>fs[]>>
  qmatch_assum_rename_tac`Cexc_rel syneq (err_to_Cerr (Rraise err)) e`[] >>
  simp[markerTheory.Abbrev_def] >>
  `∃Cv. e = Craise Cv` by (
    Cases_on`err`>>fs[] ) >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  strip_tac >> rpt strip_tac >>
  first_x_assum(qspecl_then[`st0`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`Cs1`,`Cw`]strip_assume_tac) >>
  `syneq v' Cw` by metis_tac[syneq_trans] >>
  pop_assum mp_tac >>
  ntac 3 (rator_x_assum`syneq`kall_tac) >>
  strip_tac >>
  rator_x_assum`code_for_return`mp_tac >>
  simp[code_for_return_def] >>
  disch_then(qx_choosel_then[`bw`,`rf`,`rd'`,`ck`]strip_assume_tac) >>
  `ck = SOME (FST s')` by (
    fs[s_refs_def] >>
    imp_res_tac RTC_bc_next_clock_less >>
    Cases_on`bs.clock`>>fs[optionTheory.OPTREL_def] ) >>
  map_every qexists_tac[`bw`,`rf`,`rd'`,`Cs1`] >>
  BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  conj_tac >- (
    Cases_on`err`>>fs[err_bv_def]>>BasicProvers.VAR_EQ_TAC>>
    fs[Once IntLangTheory.syneq_cases]>>BasicProvers.VAR_EQ_TAC>>
    fs[Once Cv_bv_cases]>>simp[]) >>
  conj_tac >- (
    simp[vs_to_Cvs_MAP] >>
    metis_tac[EVERY2_syneq_trans] ) >>
  fs[closed_vlabs_def,closed_Clocs_def] >>
  conj_tac >- (
    rw[] >>
    match_mp_tac code_env_cd_append >> rw[] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,between_labels_def,good_labels_def,MEM_FILTER,between_def,EVERY_MEM,MEM_MAP,is_Label_rwt] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY2_EVERY,Abbr`Csf`] >>
    metis_tac[Cevaluate_store_SUBSET,FST,SND] ) >>
  match_mp_tac s_refs_append_code >>
  HINT_EXISTS_TAC >>
  simp[bc_state_component_equality])

(* TODO: move?*)
val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {})`
val _ = export_rewrites["FV_dec_def"]

val dec_cns_def = Define`
  (dec_cns (Dlet p e) = all_cns_pat p ∪ all_cns_exp e) ∧
  (dec_cns (Dletrec defs) = all_cns_defs defs) ∧
  (dec_cns (Dtype _) = {})`
val _ = export_rewrites["dec_cns_def"]

val new_dec_cns_def = Define`
  (new_dec_cns (Dtype ts) = (MAP FST (FLAT (MAP (SND o SND) ts)))) ∧
  (new_dec_cns _ = [])`
val _ = export_rewrites["new_dec_cns_def"]

val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _) = []) ∧
  (new_dec_vs (Dlet p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"]

val pmatch_extend_cenv = store_thm("pmatch_extend_cenv",
  ``(∀(cenv:envC) s p v env id x. id ∉ set (MAP FST cenv) ∧ pmatch cenv s p v env ≠ Match_type_error
    ⇒ pmatch ((id,x)::cenv) s p v env = pmatch cenv s p v env) ∧
    (∀(cenv:envC) s ps vs env id x. id ∉ set (MAP FST cenv) ∧ pmatch_list cenv s ps vs env ≠ Match_type_error
    ⇒ pmatch_list ((id,x)::cenv) s ps vs env = pmatch_list cenv s ps vs env)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac) >>
  TRY (BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac)) >>
  TRY (BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac)) >>
  TRY (BasicProvers.CASE_TAC) >> rw[] >>
  TRY (
    TRY (BasicProvers.CASE_TAC) >> rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
    metis_tac[]))

    (*
val evaluate_extend_cenv = store_thm("evaluate_extend_cenv",
  ``(∀ck menv (cenv:envC) cs env exp res. evaluate ck menv cenv cs env exp res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate ck menv ((id,x)::cenv) cs env exp res) ∧
    (∀ck menv (cenv:envC) cs env es res. evaluate_list ck menv cenv cs env es res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate_list ck menv ((id,x)::cenv) cs env es res) ∧
    (∀ck menv (cenv:envC) cs env v pes res. evaluate_match ck menv cenv cs env v pes res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate_match ck menv ((id,x)::cenv) cs env v pes res)``,
  ho_match_mp_tac evaluate_strongind >>
  rw[FORALL_PROD,EXISTS_PROD] >>
  TRY(Cases_on`cs`)>>TRY(Cases_on`cs'`)>>
  rw[Once evaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD,MEM_MAP] >>
  TRY(metis_tac[])>>
  TRY(
    fs[SemanticPrimitivesTheory.do_con_check_def] >> rw[] >>
    Cases_on`ALOOKUP cenv cn`>>fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    PairCases_on`x`>>fs[] >> metis_tac[]) >>
  Q.ISPECL_THEN[`cenv`,`s`,`p`,`v`,`env`,`id`]mp_tac(CONJUNCT1 pmatch_extend_cenv) >>
  simp[MEM_MAP,FORALL_PROD])
  *)

val evaluate_list_MAP_Var = store_thm("evaluate_list_MAP_Var",
  ``∀vs ck menv cenv s env. set vs ⊆ set (MAP FST env) ⇒ evaluate_list ck menv cenv s env (MAP (Var o Short) vs) (s,Rval (MAP (THE o ALOOKUP env) vs))``,
  Induct >> simp[Once evaluate_cases] >>
  rw[] >> rw[Once evaluate_cases,SemanticPrimitivesTheory.lookup_var_id_def] >>
  Cases_on`ALOOKUP env h`>>simp[] >>
  imp_res_tac ALOOKUP_FAILS >>
  fsrw_tac[DNF_ss][MEM_MAP,EXISTS_PROD])

val number_constructors_thm = store_thm("number_constructors_thm",
  ``∀mn cs ac. number_constructors mn cs ac =
    ((FST(ac) |++ GENLIST (λi. (SOME (mk_id mn (FST (EL i cs))), (SND(SND(ac)))+i)) (LENGTH cs)
     ,REVERSE (GENLIST (λi. ((SND(SND(ac)))+i,SOME (mk_id mn(FST(EL i cs))))) (LENGTH cs)) ++ (FST(SND(ac)))
     ,(SND(SND(ac))) + LENGTH cs))``,
  gen_tac >> Induct >- simp[number_constructors_def,FUPDATE_LIST_THM] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  qx_gen_tac`q` >> PairCases_on`q` >>
  simp[number_constructors_def] >>
  conj_tac >- (
    simp[GENLIST_CONS,FUPDATE_LIST_THM] >>
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE] ) >>
  simp[GENLIST_CONS] >>
  simp[LIST_EQ_REWRITE])

val number_constructors_append = store_thm("number_constructors_append",
  ``∀l1 l2 mn ct. number_constructors mn (l1 ++ l2) ct = number_constructors mn l2 (number_constructors mn l1 ct)``,
  Induct >> simp[number_constructors_def] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  ntac 2 gen_tac >> qx_gen_tac`q` >> PairCases_on`q` >>
  simp[number_constructors_def])

val FOLDL_number_constructors_thm = store_thm("FOLDL_number_constructors_thm",
  ``∀tds mn ct. FOLDL (λct p. case p of (x,y,cs) => number_constructors mn cs ct) ct tds =
    number_constructors mn (FLAT (MAP (SND o SND) tds)) ct``,
  Induct >- (simp[number_constructors_thm,FUPDATE_LIST_THM]) >>
  simp[] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  simp[] >>
  simp[number_constructors_append])

val check_dup_ctors_ALL_DISTINCT = store_thm("check_dup_ctors_ALL_DISTINCT",
  ``check_dup_ctors menv cenv tds ⇒ ALL_DISTINCT (MAP FST (FLAT (MAP (SND o SND) tds)))``,
  simp[SemanticPrimitivesTheory.check_dup_ctors_def] >>
  rw[] >>
  qmatch_assum_abbrev_tac`ALL_DISTINCT l1` >>
  qmatch_abbrev_tac`ALL_DISTINCT l2` >>
  qsuff_tac`l1 = l2`>- PROVE_TAC[] >>
  unabbrev_all_tac >>
  rpt (pop_assum kall_tac) >>
  Induct_on`tds` >> simp[FORALL_PROD] >>
  Induct >> simp[FORALL_PROD])

val check_dup_ctors_NOT_MEM = store_thm("check_dup_ctors_NOT_MEM",
  ``check_dup_ctors mn cenv tds ∧ MEM e (MAP FST (FLAT (MAP (SND o SND) tds))) ⇒ ¬MEM (mk_id mn e) (MAP FST cenv)``,
  simp[SemanticPrimitivesTheory.check_dup_ctors_def] >>
  strip_tac >>
  qpat_assum`ALL_DISTINCT X`kall_tac >>
  Induct_on`tds` >> simp[] >>
  fs[FORALL_PROD,res_quanTheory.RES_FORALL] >>
  rw[] >- (
    fsrw_tac[DNF_ss][MEM_MAP] >>
    qmatch_assum_rename_tac`MEM a b`[] >>
    PairCases_on`a`>>fs[] >>
    res_tac >>
    imp_res_tac ALOOKUP_FAILS >>
    simp[FORALL_PROD] >>
    metis_tac[] ) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >> metis_tac[])

val FLAT_MAP_MAP_lemma = store_thm("FLAT_MAP_MAP_lemma",
  ``MAP FST (FLAT (MAP (λ(tvs,tn,condefs). (MAP (λ(conN,ts). (mk_id mn conN,LENGTH ts,mk_id mn tn)) condefs)) tds)) =
    MAP (mk_id mn o FST) (FLAT (MAP (SND o SND) tds))``,
  simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY])

val pat_to_Cpat_SUBMAP = store_thm("pat_to_Cpat_SUBMAP",
  ``(∀p m m'. all_cns_pat p ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ⇒ (SND (pat_to_Cpat m' p) = SND (pat_to_Cpat m p))) ∧
    (∀ps m m'. all_cns_pats ps ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ⇒ (SND (pats_to_Cpats m' ps) = SND (pats_to_Cpats m ps)))``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``)>>
  simp[ToIntLangTheory.pat_to_Cpat_def,UNCURRY,FLOOKUP_DEF] >>
  simp[pat_to_Cpat_cnmap] >>
  conj_tac >- rw[SUBMAP_DEF] >>
  rw[] >>
  first_x_assum match_mp_tac >>
  simp[pat_to_Cpat_cnmap] >>
  simp[FST_pat_to_Cpat_bvars])

val exp_to_Cexp_SUBMAP = store_thm("exp_to_Cexp_SUBMAP",
  ``(∀m exp m'. all_cns_exp exp ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (exp_to_Cexp m' exp = exp_to_Cexp m exp)) ∧
    (∀m ds m'. all_cns_defs ds ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (defs_to_Cdefs m' ds = defs_to_Cdefs m ds)) ∧
    (∀m pes m'. all_cns_pes pes ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (pes_to_Cpes m' pes = pes_to_Cpes m pes)) ∧
    (∀m es m'. all_cns_list es ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (exps_to_Cexps m' es = exps_to_Cexps m es))``,
  ho_match_mp_tac exp_to_Cexp_ind >>
  simp[exp_to_Cexp_def] >>
  conj_tac >- rw[SUBMAP_DEF,FLOOKUP_DEF] >>
  simp[UNCURRY] >>
  simp[pat_to_Cpat_SUBMAP] >>
  rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[pat_to_Cpat_cnmap,FST_pat_to_Cpat_bvars] >>
  Cases_on`pat_to_Cpat m p`>>simp[])

val v_to_Cv_SUBMAP = store_thm("v_to_Cv_SUBMAP",
  ``(∀mv m v m'. all_cns v ⊆ (FDOM m) ∧ m ⊑ m' ⇒ v_to_Cv mv m' v = v_to_Cv mv m v) ∧
    (∀mv m vs m'. BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m ∧ m ⊑ m' ⇒ vs_to_Cvs mv m' vs = vs_to_Cvs mv m vs) ∧
    (∀mv m env m'. BIGUNION (IMAGE all_cns (env_range env)) ⊆ FDOM m ∧ m ⊑ m' ⇒ env_to_Cenv mv m' env = env_to_Cenv mv m env)``,
  ho_match_mp_tac v_to_Cv_ind >> simp[v_to_Cv_def] >>
  conj_tac >- rw[SUBMAP_DEF,FLOOKUP_DEF] >>
  simp[exp_to_Cexp_SUBMAP] >>
  rw[] >> AP_TERM_TAC >>
  simp[exp_to_Cexp_SUBMAP])

val mk_id_inj = store_thm("mk_id_inj",
  ``mk_id mn n1 = mk_id mn n2 ⇒ n1 = n2``,
  rw[AstTheory.mk_id_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val closed_context_def = Define`
  closed_context menv cenv s env ⇔
    ALL_DISTINCT (MAP FST menv) ∧
    EVERY (closed menv) s ∧
    EVERY (closed menv) (MAP SND env) ∧
    EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
    closed_under_cenv cenv menv env s ∧
    closed_under_menv menv env s ∧
    (∀v. v ∈ menv_range menv ∨ v ∈ env_range env ∨ MEM v s ⇒ all_locs v ⊆ count (LENGTH s))`

val with_same_contab = store_thm("with_same_contab",
 ``rs with contab := rs.contab = rs``,
 simp[compiler_state_component_equality])
val _ = export_rewrites["with_same_contab"]

val _ = Parse.overload_on("new_decs_cns",``λds. BIGUNION (IMAGE (set o new_dec_cns) (set ds))``)

val decs_contab_thm = store_thm("decs_contab_thm",
  ``∀mn ds menv cenv env rs csz rd cs bs cenv' rs'.
     env_rs menv cenv env rs csz rd cs bs ∧
     cenv' = decs_to_cenv mn ds ++ cenv ∧
     rs' = rs with contab := decs_to_contab mn rs.contab ds ∧
     (∀i tds. i < LENGTH ds ∧ (EL i ds = Dtype tds) ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i ds) ++ cenv) tds) ∧
     closed_context menv cenv (SND cs) env
     ⇒
     env_rs menv cenv' env rs' csz rd cs bs``,
  gen_tac >>
  Induct >>
  simp[decs_to_contab_def,decs_to_cenv_def] >>
  Cases >>
  simp[dec_to_contab_def,dec_to_cenv_def] >>
  TRY (
    rw[] >>
    first_x_assum match_mp_tac >>
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    rpt strip_tac >>
    first_x_assum(qspec_then`SUC i`mp_tac) >>
    simp[decs_to_cenv_def,dec_to_cenv_def] >>
    NO_TAC) >>
  rpt strip_tac >>
  simp[FOLDL_number_constructors_thm] >>
  first_x_assum match_mp_tac >>
  simp[compiler_state_component_equality] >>
  Q.PAT_ABBREV_TAC`X:contab = number_constructors a b c` >>
  qexists_tac`rs with contab := X` >>
  simp[Abbr`X`] >>
  reverse conj_tac >- (
    rw[] >- (
      first_x_assum(qspec_then`SUC i`mp_tac) >>
      simp[decs_to_cenv_def,dec_to_cenv_def] )
    >- (
      fs[closed_context_def] >>
      reverse conj_tac >- metis_tac[] >>
      fs[closed_under_cenv_def] >>
      fs[SUBSET_DEF, cenv_dom_def] >>
      metis_tac[] )) >>
  last_x_assum(qspec_then`0`mp_tac) >>
  simp[decs_to_cenv_def] >> strip_tac >>
  qmatch_assum_rename_tac`check_dup_ctors mn cenv tds`[] >>
  fs[FOLDL_number_constructors_thm,SemanticPrimitivesTheory.build_tdefs_def,LibTheory.emp_def] >>
  fs[env_rs_def] >>
  conj_tac >- (
    fs[number_constructors_thm,LET_THM] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qabbrev_tac`p = rs.contab` >>
    PairCases_on`p` >>
    fs[good_contab_def] >>
    fs[good_cmap_def,cmap_linv_def] >>
    conj_asm1_tac >- (
      simp[MAP_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,MAP_GENLIST,ALL_DISTINCT_GENLIST] >>
      fsrw_tac[DNF_ss][EVERY_MEM] >>
      simp[MEM_GENLIST] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> simp[] ) >>
    conj_asm1_tac >- (
      simp[MAP_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,MAP_GENLIST,ALL_DISTINCT_GENLIST] >>
      simp[MEM_GENLIST,MEM_MAP,FORALL_PROD] >>
      imp_res_tac check_dup_ctors_ALL_DISTINCT >>
      fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP] >>
      conj_tac >- metis_tac[mk_id_inj] >>
      qsuff_tac`∀e. MEM e (MAP FST (FLAT (MAP (SND o SND) tds))) ⇒ ¬MEM (SOME (mk_id mn e)) (MAP SND p1)` >- (
        simp[MEM_MAP] >>
        simp[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
        simp[FORALL_PROD] ) >>
      imp_res_tac check_dup_ctors_NOT_MEM >>
      qx_gen_tac`z` >> strip_tac >>
      first_x_assum(qspec_then`z`mp_tac) >>
      simp[] >>
      qpat_assum`X = FDOM p0`mp_tac >>
      simp[EXTENSION] >>
      rpt strip_tac >>
      fs[SUBSET_DEF] >>
      `SOME (mk_id mn z) ∈ FDOM p0` by metis_tac[] >>
      fs [cenv_dom_def, MEM_MAP] >>
      rw [] >>
      qsuff_tac`¬(MEM (mk_id mn z) (MAP FST cenv))`>-metis_tac[NOT_SOME_NONE, SOME_11]>>
      simp[] >>
      Cases_on`mn`>>fs[AstTheory.mk_id_def] >>
      fs[SemanticPrimitivesTheory.id_to_string_def] >>
      res_tac >> fs[] >> rw[] >> fs[] >> metis_tac[]) >>
    conj_asm1_tac >- (
      simp[EVERY_MAP,EVERY_REVERSE,EVERY_GENLIST] >>
      fs[EVERY_MAP,EVERY_MEM] >>
      rw[] >> res_tac >> simp[] ) >>
    conj_asm1_tac >- (
      simp[FDOM_FUPDATE_LIST] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_GENLIST,SemanticPrimitivesTheory.id_to_string_def] ) >>
    simp[FDOM_FUPDATE_LIST] >>
    gen_tac >> strip_tac >- (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      fsrw_tac[ARITH_ss][] >>
      simp[MEM_GENLIST] >>
      res_tac >>
      imp_res_tac ALOOKUP_MEM >>
      disj2_tac >>
      qmatch_abbrev_tac`MEM (A,y) p1` >>
      qsuff_tac`A = p0 ' x`>-(simp[Abbr`A`] >> PROVE_TAC[]) >>
      simp[Abbr`A`] >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[MAP_GENLIST,MEM_GENLIST] >>
      gen_tac >>
      spose_not_then strip_assume_tac >>
      `p0 ' x < p2` by (
        fs[EVERY_MAP,EVERY_MEM] >>
        res_tac >> fs[] ) >>
      qunabbrev_tac`y` >>
      qmatch_assum_abbrev_tac`x = SOME (mk_id mn (FST (EL m ls)))` >>
      qmatch_assum_abbrev_tac`x = SOME (mk_id mn z)` >>
      `MEM z (MAP FST ls)` by metis_tac[MEM_MAP,MEM_EL] >>
      `mk_id mn z ∉ set (MAP FST cenv)` by metis_tac[check_dup_ctors_NOT_MEM] >>
      pop_assum mp_tac >>
      fs[EXTENSION, cenv_dom_def, MEM_MAP] >>
      metis_tac [NOT_SOME_NONE, SOME_11] ) >>
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
    fsrw_tac[ARITH_ss][] >>
    simp[MEM_GENLIST] >>
    disj1_tac >>
    pop_assum mp_tac >>
    simp[MEM_MAP,MEM_GENLIST] >>
    strip_tac >>
    qexists_tac`i` >>
    simp[SemanticPrimitivesTheory.id_to_string_def] >>
    qmatch_abbrev_tac`((p0 |++ ls) ' k) = z` >>
    qho_match_abbrev_tac`P ((p0 |++ ls) ' k)` >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp[Abbr`P`,Abbr`ls`,MEM_GENLIST,Abbr`k`] >>
    reverse conj_tac >- metis_tac[] >>
    fsrw_tac[DNF_ss][MAP_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
    qmatch_abbrev_tac`ALL_DISTINCT ls` >>
    qmatch_assum_abbrev_tac`ALL_DISTINCT (MAP SND (GENLIST X Y))` >>
    `ls = (MAP SND (GENLIST X Y))` by (
      simp[Abbr`ls`,Abbr`X`,Abbr`Y`,MAP_MAP_o,MAP_GENLIST,combinTheory.o_DEF] ) >>
    pop_assum SUBST1_TAC >>
    simp[] ) >>
  conj_tac >- (
    fs[good_cmap_def] >>
    fs[number_constructors_thm] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    conj_asm1_tac >- (
      simp[ALL_DISTINCT_APPEND] >>
      conj_tac >- (
        imp_res_tac check_dup_ctors_ALL_DISTINCT >>
        qmatch_assum_abbrev_tac`ALL_DISTINCT ls2` >>
        simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        qmatch_abbrev_tac`ALL_DISTINCT ls` >>
        `ls = MAP (mk_id mn) ls2` by (
          simp[Abbr`ls`,Abbr`ls2`,MAP_GENLIST,MAP_MAP_o,MAP_FLAT] >>
          simp[combinTheory.o_DEF]) >>
        pop_assum SUBST1_TAC >>
        match_mp_tac ALL_DISTINCT_MAP_INJ >>
        simp[] >>
        metis_tac[mk_id_inj]) >>
      imp_res_tac check_dup_ctors_NOT_MEM >>
      pop_assum mp_tac >>
      simp_tac(srw_ss()++DNF_ss)[MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      metis_tac[] ) >>
    rpt gen_tac >>
    simp[FDOM_FUPDATE_LIST] >>
    Q.PAT_ABBREV_TAC`ls:((string id option) list) = MAP FST (GENLIST X Y)` >>
    Q.PAT_ABBREV_TAC`al:((string id option#num) list) = X` >>
    qabbrev_tac`p = rs.contab` >> PairCases_on`p`>>fs[] >>
    Q.PAT_ABBREV_TAC`ls3:((string id#num#string id) list) = FLAT (MAP X tds)` >>
    `∀x. MEM x ls3 ⇒ MEM (SOME (FST x)) ls` by (
      gen_tac >> strip_tac >>
      `MEM (FST x) (MAP FST ls3)` by metis_tac[MEM_MAP] >>
      fs[Abbr`ls3`,FLAT_MAP_MAP_lemma] >>
      simp[Abbr`ls`,Abbr`al`] >>
      pop_assum mp_tac >>
      simp[MEM_MAP,MEM_GENLIST] >>
      simp[MEM_EL] >>
      strip_tac >> simp[] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      metis_tac[] ) >>
    `∀x. x ∈ FDOM p0 ⇒ (p0 |++ al) ' x = p0 ' x` by (
      gen_tac >> strip_tac >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[Abbr`al`,Abbr`ls`,MAP_GENLIST,MEM_GENLIST] >>
      imp_res_tac check_dup_ctors_NOT_MEM >>
      pop_assum mp_tac >>
      simp[MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[Once MEM_EL,GSYM LEFT_FORALL_IMP_THM] >> strip_tac >>
      spose_not_then strip_assume_tac >>
      first_x_assum(qspec_then`m`mp_tac) >>
      simp[] >> fs[EXTENSION, cenv_dom_def] >>
      Cases_on`MEM x (MAP (SOME o FST) cenv)` >- (
        fs[MEM_MAP] >> metis_tac[SOME_11] ) >>
      `x = NONE` by metis_tac[] >>
      fs [] ) >>
    `ALL_DISTINCT ls` by (
      simp[Abbr`ls`,Abbr`al`] >>
      imp_res_tac check_dup_ctors_ALL_DISTINCT >>
      qmatch_assum_abbrev_tac`ALL_DISTINCT ls2` >>
      simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      qmatch_abbrev_tac`ALL_DISTINCT ls` >>
      `ls = MAP (SOME o mk_id mn) ls2` by (
        simp[Abbr`ls`,Abbr`ls2`,MAP_GENLIST,LIST_EQ_REWRITE,combinTheory.o_DEF,EL_MAP] ) >>
      pop_assum SUBST1_TAC >>
      match_mp_tac ALL_DISTINCT_MAP_INJ >>
      simp[] >> metis_tac[mk_id_inj] ) >>
    `∀x. MEM x cenv ⇒ SOME (FST x) ∈ FDOM p0` by (
      fs[EXTENSION,MEM_MAP] >> metis_tac[] ) >>
    `∀k1 k2 v v. MEM (k1,v) al ∧ MEM (k2,v) al ⇒ k1 = k2` by (
      simp[Abbr`al`,MEM_GENLIST] >>
      rpt gen_tac >> strip_tac >> fs[] ) >>
    `∀x. MEM x ls ⇒ MEM (x, (p0 |++ al) ' x) al` by (
      simp[Abbr`ls`] >> gen_tac >> strip_tac >>
      qsuff_tac `(λv. MEM (x,v) al) ((p0 |++ al) ' x)` >- rw[] >>
      match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
    `∀k v1 v2. MEM (k,v1) ls3 ∧ MEM (k,v2) ls3 ⇒ v1 = v2` by (
      fs[ALL_DISTINCT_APPEND] >>
      qpat_assum`ALL_DISTINCT (MAP_FST ls3)`mp_tac >>
      simp[EL_ALL_DISTINCT_EL_EQ] >>
      simp_tac std_ss [MEM_EL,EL_MAP] >>
      strip_tac >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      ntac 3 gen_tac >>
      map_every qx_gen_tac[`n1`,`n2`] >> strip_tac >>
      first_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
      rpt (qpat_assum`X = EL Y ls3`(mp_tac o SYM)) >>
      rw[] >> fs[] ) >>
    `∀x. MEM x ls ⇒ x ∉ FDOM p0` by (
      simp[Abbr`ls`,Abbr`al`,MEM_GENLIST,EXISTS_PROD,MEM_MAP] >>
      ntac 8 (pop_assum kall_tac) >>
      qmatch_assum_rename_tac`Abbrev((p0,w,n) = rs.contab)`[] >>
      imp_res_tac check_dup_ctors_NOT_MEM >>
      gen_tac >> strip_tac >>
      fs[EXTENSION] >>
      spose_not_then strip_assume_tac >>
      Cases_on`x ∈ (cenv_dom cenv)` >- (
        fs[MEM_MAP,EXISTS_PROD, cenv_dom_def] >>
        rw [] >>
        fs [MEM_EL] >>
        Cases_on`EL i (FLAT (MAP (SND o SND) tds))`>>simp[] >>
        metis_tac [FST] ) >>
      fs [cenv_dom_def, MEM_MAP] >>
      rw [] >>
      metis_tac[FST, SOME_11, NOT_SOME_NONE] ) >>
    `∀x y z. MEM (x,y) al ∧ z ∈ FDOM p0 ⇒ y ≠ (p0 ' z)` by (
      simp[Abbr`al`,MEM_GENLIST] >>
      ntac 9 (pop_assum kall_tac) >>
      gen_tac >> spose_not_then strip_assume_tac >>
      fs[good_contab_def,cmap_linv_def,EVERY_MAP] >>
      res_tac >> imp_res_tac ALOOKUP_MEM >>
      fs[EVERY_MEM,MEM_MAP] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    strip_tac >- (
      res_tac >> simp[] >>
      Cases_on`p1`>>Cases_on`p2`>>fs[] >>
      metis_tac[] ) >>
    rw [] >>
    metis_tac[SOME_11, FST, NOT_SOME_NONE, SND, PAIR_EQ, pair_CASES] ) >>
  conj_tac >- (
    fs[EXTENSION,number_constructors_thm,FDOM_FUPDATE_LIST,LET_THM] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qx_gen_tac`x` >>
    qabbrev_tac`p = rs.contab` >>
    PairCases_on`p` >> fs[] >>
    fs [cenv_dom_def, MEM_MAP] >>
    simp[FDOM_FUPDATE_LIST] >>
    Cases_on`x=NONE`>-metis_tac[]>>simp[]>>
    `?y. x = SOME y` by (Cases_on `x` >> fs []) >>
    rw [] >>
    Cases_on`SOME y ∈ FDOM p0`>>simp[] >-
      metis_tac[optionTheory.NOT_SOME_NONE,optionTheory.SOME_11] >>
    Cases_on`MEM y (MAP FST cenv)`>-metis_tac[MEM_MAP]>>simp[]>>
    simp[MEM_MAP,MEM_GENLIST,MEM_FLAT,EXISTS_PROD,UNCURRY]>>
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD]>>
    qmatch_abbrev_tac`A ⇔ B` >>
    qsuff_tac`A ⇔ ∃z. MEM z (FLAT (MAP (SND o SND) tds)) ∧ (y = mk_id mn (FST z))`>-metis_tac[MEM_EL]>>
    simp[Abbr`A`,Abbr`B`,MEM_FLAT,EXISTS_PROD,MEM_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[EXISTS_PROD]>>
    fs[MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[number_constructors_thm] >>
    ho_match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    qabbrev_tac`p = rs.contab` >> PairCases_on`p`>>fs[] >>
    simp[MAP_GENLIST,MEM_GENLIST] >>
    Cases_on`mn`>>simp[AstTheory.mk_id_def] >>
    fs[MEM_EL] >>
    metis_tac[EL_MAP] ) >>
  conj_tac >- (
    fs[number_constructors_thm] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qabbrev_tac`p = rs.contab` >>
    PairCases_on`p` >> fs[] >>
    fs[FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
    qx_gen_tac`id` >>
    qmatch_abbrev_tac`(P ∨ Q) ∧ A ⇒ R` >>
    fs[good_contab_def,cmap_linv_def] >>
    qmatch_assum_abbrev_tac`Abbrev(A ⇔ (((p0 |++ ls) ' id) = ((p0 |++ ls) ' NONE)))` >>
    `MEM (p0 ' NONE, NONE) p1` by (
      match_mp_tac ALOOKUP_MEM >>
      first_x_assum match_mp_tac >>
      fs[EXTENSION, cenv_dom_def] >> metis_tac[] ) >>
    `MEM (p0 ' NONE) (MAP FST p1)` by (simp[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
    `p0 ' NONE < p2` by fs[EVERY_MEM] >>
    `(p0 |++ ls) ' NONE = p0 ' NONE` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[Abbr`ls`,MEM_MAP,MEM_GENLIST,FORALL_PROD] >>
      Cases_on`mn`>>fs[AstTheory.mk_id_def] >>
      metis_tac[MEM_EL,LENGTH_MAP,MEM_MAP] ) >>
    `ALL_DISTINCT (MAP FST ls)` by (
      imp_res_tac check_dup_ctors_ALL_DISTINCT >>
      qmatch_assum_abbrev_tac`ALL_DISTINCT ls2` >>
      `MAP FST ls = MAP (SOME o mk_id mn) ls2` by (
        simp[Abbr`ls`,Abbr`ls2`,MAP_GENLIST,LIST_EQ_REWRITE,EL_MAP] ) >>
      pop_assum SUBST1_TAC >>
      match_mp_tac ALL_DISTINCT_MAP_INJ >>
      simp[] >> metis_tac[mk_id_inj] ) >>
    Cases_on`Q=T` >- (
      fs[Abbr`P`,Abbr`A`,Abbr`R`,Abbr`Q`] >> strip_tac >>
      qpat_assum`p0 ' X = tuple_cn`(assume_tac o SYM) >> fs[] >>
      pop_assum kall_tac >>
      spose_not_then strip_assume_tac >>
      `(λv. MEM v (MAP SND ls)) (p0 ' NONE)` by (
        qpat_assum`X = p0 ' Y`(SUBST1_TAC o SYM) >>
        match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      pop_assum mp_tac >>
      simp[Abbr`ls`,MEM_MAP,MEM_GENLIST,FORALL_PROD] ) >>
    fs[Abbr`P`,Abbr`Q`,Abbr`R`,Abbr`A`] >>
    strip_tac >>
    `(p0 |++ ls) ' id = p0 ' id` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[] ) >>
    fs[] ) >>
  fs[LET_THM] >>
  map_every qexists_tac[`Cmenv`,`Cenv`,`Cs`] >>
  simp[] >>
  fs[number_constructors_thm] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (
    match_mp_tac Cenv_bs_with_irr >>
    simp[] >> rfs[] >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  reverse conj_tac >- (
    match_mp_tac (GEN_ALL (MP_CANON fmap_rel_trans)) >>
    HINT_EXISTS_TAC >> simp[] >>
    conj_tac >- metis_tac[EVERY2_syneq_trans] >>
    simp[fmap_rel_def] >> gen_tac >> strip_tac >>
    qmatch_abbrev_tac`EVERY2 syneq ls1 ls2` >>
    qsuff_tac`ls1 = ls2`>-rw[] >>
    simp[Abbr`ls1`,Abbr`ls2`,MAP_EQ_f,env_to_Cenv_MAP] >>
    rw[] >>
    match_mp_tac(CONJUNCT1 v_to_Cv_SUBMAP)>>
    qabbrev_tac`p = rs.contab` >>
    PairCases_on`p`>>fs[closed_context_def,closed_under_cenv_def] >>
    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      qexists_tac`cenv_dom cenv` >>
      simp[] >> fs[cenv_dom_def, EXTENSION,SUBSET_DEF] >>
      fsrw_tac[DNF_ss][MEM_FLAT] >>
      Q.ISPECL_THEN[`menv`,`x`]mp_tac alist_to_fmap_FAPPLY_MEM >>
      simp[] >> strip_tac >>
      qx_gen_tac`z` >> strip_tac >>
      qsuff_tac `z = NONE ∨ MEM z (MAP (SOME o FST) cenv)` >- metis_tac [] >>
      first_x_assum(qspecl_then[`SND e`,`z`,`MAP SND (alist_to_fmap menv ' x)`](match_mp_tac o MP_CANON)) >>
      simp[MEM_MAP,EXISTS_PROD] >>
      PairCases_on`e`>>fs[] >>
      PROVE_TAC[]) >>
    simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >> rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
    simp[MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
    imp_res_tac check_dup_ctors_NOT_MEM >>
    spose_not_then strip_assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL,EL_MAP] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    simp[combinTheory.o_DEF] >> fs[cenv_dom_def,EXTENSION,MEM_EL] >>
    metis_tac[EL_MAP, LENGTH_MAP, combinTheory.o_DEF, NOT_SOME_NONE, SOME_11]) >>
  conj_tac >- (
    match_mp_tac EVERY2_syneq_trans >>
    qmatch_assum_abbrev_tac`EVERY2 syneq X Cs` >>
    qexists_tac`X` >>
    simp[Abbr`X`] >>
    qmatch_abbrev_tac`EVERY2 syneq ls1 ls2` >>
    qsuff_tac`ls1 = ls2`>-rw[] >>
    simp[Abbr`ls1`,Abbr`ls2`,MAP_EQ_f] >>
    rw[] >>
    match_mp_tac(CONJUNCT1 v_to_Cv_SUBMAP)>>
    qabbrev_tac`p = rs.contab` >>
    PairCases_on`p`>>fs[closed_context_def,closed_under_cenv_def] >>
    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      qexists_tac`cenv_dom cenv` >>
      simp[] >> fs[cenv_dom_def, EXTENSION,SUBSET_DEF] ) >>
    simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >> rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
    simp[MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
    imp_res_tac check_dup_ctors_NOT_MEM >>
    spose_not_then strip_assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL,EL_MAP] >>
    first_x_assum(qspec_then`i`mp_tac) >>
    simp[combinTheory.o_DEF] >> fs[EXTENSION,MEM_EL] >>
    fs [cenv_dom_def, EXTENSION, MEM_MAP, MEM_EL] >>
    metis_tac[EL_MAP, LENGTH_MAP, combinTheory.o_DEF, NOT_SOME_NONE, SOME_11] ) >>
  match_mp_tac EVERY2_syneq_trans >>
  qmatch_assum_abbrev_tac`LIST_REL syneq X Cenv` >>
  qexists_tac`X` >>
  simp[Abbr`X`] >>
  qmatch_abbrev_tac`EVERY2 syneq ls1 ls2` >>
  qsuff_tac`ls1 = ls2`>-rw[] >>
  simp[Abbr`ls1`,Abbr`ls2`,MAP_EQ_f,env_to_Cenv_MAP] >>
  rw[] >>
  match_mp_tac(CONJUNCT1 v_to_Cv_SUBMAP)>>
  qabbrev_tac`p = rs.contab` >>
  PairCases_on`p`>>fs[closed_context_def,closed_under_cenv_def] >>
  conj_tac >- (
    match_mp_tac SUBSET_TRANS >>
    qexists_tac`cenv_dom cenv` >>
    fs [SUBSET_DEF] >>
    rw [] >>
    simp[] >> fs[cenv_dom_def, EXTENSION,SUBSET_DEF,MEM_MAP, EL_MEM] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    metis_tac[EL_MAP, LENGTH_MAP, combinTheory.o_DEF, NOT_SOME_NONE, SOME_11, MEM_EL, pair_CASES, FST, SND] ) >>
  simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >> rw[] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
  simp[MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
  imp_res_tac check_dup_ctors_NOT_MEM >>
  spose_not_then strip_assume_tac >>
  fsrw_tac[DNF_ss][MEM_EL,EL_MAP] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  simp[combinTheory.o_DEF] >> fs[EXTENSION,MEM_EL] >>
  res_tac >>
  simp[] >> fs[cenv_dom_def, EXTENSION,SUBSET_DEF,MEM_MAP, EL_MEM] >>
  metis_tac[EL_MAP, LENGTH_MAP, combinTheory.o_DEF, NOT_SOME_NONE, SOME_11, MEM_EL] );

val compile_dec_append_out = store_thm("compile_dec_append_out",
  ``∀rmenv m renv rsz cs dec.
    let (vso,cs') = compile_dec rmenv m renv rsz cs dec in
    LENGTH renv = LENGTH m.bvars ∧ {x | Short x ∈ FV_dec dec} ⊆ set m.bvars
    ⇒
    ∃code. cs'.out = REVERSE code ++ cs.out ∧ between_labels code cs.next_label cs'.next_label ∧
    case vso of NONE => new_dec_vs dec = [] | SOME vs => new_dec_vs dec = vs``,
  ntac 5 gen_tac >> reverse Cases >> simp[compile_dec_def] >- (
    simp[Once SWAP_REVERSE,between_labels_def] ) >>
  Q.PAT_ABBREV_TAC`vars:string list = X Z Y` >>
  Q.PAT_ABBREV_TAC`expf:exp->exp = Y` >>
  strip_tac >>
  qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`vars`,`expf`]mp_tac compile_fake_exp_thm >>
  simp[Abbr`expf`] >>
  (discharge_hyps >- (
     fsrw_tac[DNF_ss][SUBSET_DEF,FV_defs_MAP,FORALL_PROD,FV_list_MAP,MEM_MAP,Abbr`vars`] >>
     metis_tac[])) >>
  strip_tac >> simp[] >>
  first_x_assum(qspec_then`X`kall_tac) >>
  simp[Abbr`vars`] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM,FORALL_PROD])

val evaluate_dec_decs = store_thm("evaluate_dec_decs",
  ``evaluate_dec mn menv cenv s env dec (s',res) =
    evaluate_decs mn menv cenv s env [dec] (s',(case res of Rval (cenv',_) => cenv' | _ => []),map_result SND res)``,
  simp[Once evaluate_decs_cases] >>
  Cases_on`res`>>simp[] >>
  simp[Once evaluate_decs_cases,SemanticPrimitivesTheory.combine_dec_result_def] >>
  simp[LibTheory.emp_def,LibTheory.merge_def] >>
  Cases_on`a`>>simp[])

val tac1 =
  rpt gen_tac >>
  simp[compile_dec_def] >>
  strip_tac >>
  `count' = 0` by metis_tac[big_unclocked] >> BasicProvers.VAR_EQ_TAC >>
  fs[big_clocked_unclocked_equiv] >>
  qexists_tac`count'` >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac`vars = pat_bindings p[]` >>
  qabbrev_tac`exp = Con NONE (MAP (Var o Short) (REVERSE vars))` 

val compile_dec_thm = store_thm("compile_dec_thm",
  ``∀mn menv cenv s env dec res.
     evaluate_dec mn menv cenv s env dec res ⇒
     ∃ck. ∀rmenv m renv rsz cs vso cs' rs rd bs bc0 code csz.
      compile_dec rmenv m renv rsz cs dec = (vso,cs')
      ∧ closed_context menv cenv s env
      ∧ FV_dec dec ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
      ∧ dec_cns dec ⊆ cenv_dom cenv
      ∧ env_rs menv cenv env rs csz rd (ck,s) (bs with code := bc0)
      ∧ m.bvars = MAP FST env
      ∧ m.mvars = MAP FST o_f alist_to_fmap menv
      ∧ m.cnmap = cmap rs.contab
      ∧ rmenv = MAP SND o_f rs.rmenv
      ∧ renv = MAP (CTDec o SND) rs.renv
      ∧ rsz = rs.rsz
      ∧ rs.rnext_label = cs.next_label
      ∧ cs'.out = REVERSE code ++ cs.out
      ∧ bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ IS_SOME bs.clock
      ∧ good_labels rs.rnext_label bc0
      ⇒
      case res of
      | (s',Rval(cenv',env')) =>
        ∃Cws bvs rf rd' Cs'.
        let tt = block_tag + cmap rs.contab ' NONE in
        let mv = MAP FST o_f rs.rmenv in
        let cm = cmap rs.contab in
        let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ code); stack := (Block tt bvs)::bs.stack; refs := rf; clock := SOME 0|> in
        bc_next^* bs bs'
        ∧ vso = (if ∃ts. dec = Dtype ts then NONE else SOME (MAP FST env'))
        ∧ LIST_REL syneq (vs_to_Cvs mv cm (REVERSE (MAP SND env'))) Cws
        ∧ LIST_REL (Cv_bv (mk_pp rd' bs')) Cws bvs
        ∧ LIST_REL syneq (vs_to_Cvs mv cm s') Cs'
        ∧ EVERY all_vlabs Cws
        ∧ EVERY all_vlabs Cs'
        ∧ BIGUNION (IMAGE all_Clocs (set Cws)) ⊆ count (LENGTH Cs')
        ∧ BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs')
        ∧ (∀cd. cd ∈ vlabs_list Cws ⇒ code_env_cd rmenv (bc0 ++ code) cd)
        ∧ (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd rmenv (bc0 ++ code) cd)
        ∧ LENGTH s ≤ LENGTH s'
        ∧ s_refs rd' (0,Cs') bs'
        ∧ DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm))
        ∧ rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls
      | (s',Rerr(Rraise err)) =>
        ∀ig h0 sp st0.
        bs.stack = ig ++ StackPtr h0::CodePtr sp::st0
        ∧ bs.handler = LENGTH st0 + 1
        ∧ csz = LENGTH st0
        ⇒
        ∃bv rf rd' Cs'.
        let mv = MAP FST o_f rs.rmenv in
        let cm = cmap rs.contab in
        let bs' = bs with <|pc := sp; stack := bv::st0; refs := rf; handler := h0; clock := SOME 0|> in
        bc_next^*bs bs'
        ∧ err_bv err bv
        ∧ LIST_REL syneq (vs_to_Cvs mv cm s') Cs'
        ∧ EVERY all_vlabs Cs'
        ∧ BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs')
        ∧ (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd rmenv (bc0 ++ code) cd)
        ∧ LENGTH s ≤ LENGTH s'
        ∧ s_refs rd' (0,Cs') bs'
        ∧ DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm))
        ∧ rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls
      | _ => T``,
  ho_match_mp_tac evaluate_dec_ind >>
  strip_tac >- (
    tac1 >>
    `evaluate T menv cenv (count',s) env (Mat e [(p,exp)])
        ((0,s2),Rval (Conv NONE (MAP (THE o ALOOKUP (env' ++ env)) (REVERSE vars))))` by (
      simp[Once evaluate_cases] >>
      map_every qexists_tac[`v`,`0,s2`] >>
      simp[] >>
      simp[Once evaluate_cases] >>
      disj1_tac >>
      fs[LibTheory.emp_def] >>
      simp[Once pmatch_nil] >>
      simp[Once evaluate_cases,Abbr`exp`] >>
      simp[SemanticPrimitivesTheory.do_con_check_def] >>
      match_mp_tac evaluate_list_MAP_Var >>
      qspecl_then[`cenv`,`s2`,`p`,`v`,`[]`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
      qspecl_then[`T`,`menv`,`cenv`,`count',s`,`env`,`e`,`((0,s2),Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> fs[closed_context_def]) >>
    qmatch_assum_abbrev_tac`evaluate T menv cenv (count',s) env Mexp ((0,s2),Rval (Conv NONE vs))` >>
    qmatch_assum_abbrev_tac`(compile_fake_exp rmenv m renv rsz cs vars expf).out = X` >> qunabbrev_tac`X` >>
    `LENGTH renv = LENGTH env` by fs[env_rs_def,Abbr`renv`,LET_THM,LIST_EQ_REWRITE] >>
    qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`vars`,`expf`]mp_tac compile_fake_exp_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[Abbr`expf`,Abbr`Mexp`,Abbr`renv`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD,Abbr`vars`,Abbr`exp`,FV_list_MAP] >>
      rw[] >> res_tac >> fs[] >> PROVE_TAC[] ) >>
    strip_tac >>
    first_x_assum(qspecl_then[`menv`,`cenv`,`env`,`count',s`,`0,s2`,`Rval (Conv NONE vs)`]mp_tac) >>
    simp[Abbr`expf`] >>
    disch_then(qspecl_then[`rs`,`csz`,`rd`,`bs`,`bc0`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[closed_context_def] >>
      simp[Abbr`Mexp`,Abbr`exp`,Abbr`vars`,FV_list_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,all_cns_list_MAP]) >>
    simp[Once SWAP_REVERSE] >>
    discharge_hyps >- simp[Abbr`vars`,Abbr`vs`] >>
    qspecl_then[`cenv`,`s2`,`p`,`v`,`emp`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
    discharge_hyps >- (
      simp[] >>
      simp[LibTheory.emp_def] >>
      qspecl_then[`T`,`menv`,`cenv`,`count',s`,`env`,`e`,`((0,s2),Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> fs[closed_context_def]) >>
    simp[LibTheory.emp_def,Abbr`vars`] >>
    strip_tac >>
    `REVERSE (MAP SND env') = vs` by (
      pop_assum (assume_tac o SYM) >>
      simp[Abbr`vs`] >>
      simp[MAP_MAP_o,MAP_EQ_f,ALOOKUP_APPEND,FORALL_PROD,MAP_REVERSE] >>
      pop_assum (assume_tac o SYM) >>
      rw[] >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
      rfs[]) >>
    simp[] >>
    metis_tac[] ) >>
  strip_tac >- (
    tac1 >>
    `evaluate T menv cenv (count',s) env (Mat e [(p,exp)])
        ((0,s2),Rerr (Rraise Bind_error))` by (
      simp[Once evaluate_cases] >>
      disj1_tac >>
      map_every qexists_tac[`v`,`0,s2`] >> simp[] >>
      simp[Once evaluate_cases] >>
      disj2_tac >>
      simp[Once evaluate_cases] >>
      fs[LibTheory.emp_def] >>
      simp[Once pmatch_nil]) >>
    qmatch_assum_abbrev_tac`evaluate T menv cenv (count',s) env Mexp ((0,s2),Rerr err)` >>
    qmatch_assum_abbrev_tac`(compile_fake_exp rmenv m renv rsz cs vars expf).out = X` >> qunabbrev_tac`X` >>
    `LENGTH renv = LENGTH env` by fs[env_rs_def,Abbr`renv`,LET_THM,LIST_EQ_REWRITE] >>
    qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`vars`,`expf`]mp_tac compile_fake_exp_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[Abbr`expf`,Abbr`Mexp`,Abbr`renv`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD,Abbr`vars`,Abbr`exp`,FV_list_MAP] >>
      rw[] >> res_tac >> fs[] >> PROVE_TAC[] ) >>
    strip_tac >>
    first_x_assum(qspecl_then[`menv`,`cenv`,`env`,`count',s`,`0,s2`,`Rerr err`]mp_tac) >>
    simp[Abbr`expf`] >>
    disch_then(qspecl_then[`rs`,`csz`,`rd`,`bs`,`bc0`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[closed_context_def] >>
      simp[Abbr`Mexp`,Abbr`exp`,Abbr`vars`,FV_list_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,all_cns_list_MAP] ) >>
    simp[Abbr`err`] >>
    simp[err_bv_def] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    tac1 >>
    Cases_on`err=Rtype_error`>>simp[]>>
    `evaluate T menv cenv (count',s) env (Mat e [(p,exp)])
        ((0,s'),Rerr err)` by ( simp[Once evaluate_cases] ) >>
    qmatch_assum_abbrev_tac`evaluate T menv cenv (count',s) env Mexp ((0,s2),Rerr err)` >>
    qmatch_assum_abbrev_tac`(compile_fake_exp rmenv m renv rsz cs vars expf).out = X` >> qunabbrev_tac`X` >>
    `LENGTH renv = LENGTH env` by fs[env_rs_def,Abbr`renv`,LET_THM,LIST_EQ_REWRITE] >>
    qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`vars`,`expf`]mp_tac compile_fake_exp_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[Abbr`expf`,Abbr`Mexp`,Abbr`renv`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD,Abbr`vars`,Abbr`exp`,FV_list_MAP] >>
      rw[] >> res_tac >> fs[] >> PROVE_TAC[] ) >>
    strip_tac >>
    first_x_assum(qspecl_then[`menv`,`cenv`,`env`,`count',s`,`0,s2`,`Rerr err`]mp_tac) >>
    simp[Abbr`expf`] >>
    disch_then(qspecl_then[`rs`,`csz`,`rd`,`bs`,`bc0`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[closed_context_def] >>
      simp[Abbr`Mexp`,Abbr`exp`,Abbr`vars`,FV_list_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,all_cns_list_MAP] ) >>
    Cases_on`err`>>simp[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >>
    simp[compile_dec_def,FST_triple] >>
    strip_tac >>
    qexists_tac`0` >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`MFF:string list = MAP X funs` >>
    `MFF = MAP FST funs` by (
      rw[Once LIST_EQ_REWRITE,Abbr`MFF`,EL_MAP] >>
      BasicProvers.CASE_TAC ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`MFF` >>
    strip_tac >>
    qabbrev_tac`exp = Con NONE (MAP (Var o Short) (REVERSE (MAP FST funs)))` >>
    `evaluate T menv cenv (0,s) env (Letrec funs exp)
        ((0,s),Rval (Conv NONE (MAP (THE o (ALOOKUP (build_rec_env funs env env))) (REVERSE (MAP FST funs)))))` by (
      simp[Once evaluate_cases,FST_triple] >>
      simp[Once evaluate_cases,Abbr`exp`] >>
      simp[SemanticPrimitivesTheory.do_con_check_def] >>
      REWRITE_TAC[GSYM MAP_APPEND] >>
      match_mp_tac evaluate_list_MAP_Var >>
      simp[build_rec_env_dom]) >>
    qmatch_assum_abbrev_tac`evaluate T menv cenv (0,s) env Mexp ((0,s),Rval (Conv NONE vs))` >>
    qmatch_assum_abbrev_tac`(compile_fake_exp rmenv m renv rsz cs vars expf).out = X` >> qunabbrev_tac`X` >>
    `LENGTH renv = LENGTH env` by fs[env_rs_def,Abbr`renv`,LET_THM,LIST_EQ_REWRITE] >>
    qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`vars`,`expf`]mp_tac compile_fake_exp_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[Abbr`expf`,Abbr`Mexp`,Abbr`renv`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_list_MAP,FV_defs_MAP,UNCURRY,MEM_MAP,EXISTS_PROD,FORALL_PROD,Abbr`vs`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD,Abbr`vars`,Abbr`exp`,FV_list_MAP] >>
      rw[] >> res_tac >> fs[] >> PROVE_TAC[] ) >>
    strip_tac >>
    first_x_assum(qspecl_then[`menv`,`cenv`,`env`,`0,s`,`0,s`,`Rval (Conv NONE vs)`]mp_tac) >>
    simp[Abbr`expf`] >>
    disch_then(qspecl_then[`rs`,`csz`,`rd`,`bs`,`bc0`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[closed_context_def] >>
      simp[Abbr`Mexp`,Abbr`exp`,Abbr`vars`,FV_list_MAP,FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,all_cns_list_MAP,FV_defs_MAP] >>
      metis_tac[]) >>
    simp[Once SWAP_REVERSE] >>
    discharge_hyps >- simp[Abbr`vars`,Abbr`vs`] >>
    `build_rec_env funs env [] = ZIP (vars,REVERSE vs)` by (
      simp[build_rec_env_MAP,LIST_EQ_REWRITE,Abbr`vs`,EL_MAP,UNCURRY,EL_ZIP,Abbr`vars`] >>
      simp[MAP_REVERSE,EL_MAP] >>
      simp[ALOOKUP_APPEND] >> rw[] >>
      Q.PAT_ABBREV_TAC`al:(string#v)list = MAP X funs` >>
      `MEM (FST (EL x funs), Recclosure env funs (FST (EL x funs))) al` by (
        simp[Abbr`al`,MEM_MAP,EXISTS_PROD] >>
        simp[MEM_EL] >>
        metis_tac[pair_CASES,FST] ) >>
      `ALL_DISTINCT (MAP FST al)` by (
        simp[Abbr`al`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        srw_tac[ETA_ss][] ) >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
      simp[]) >>
    `LENGTH vars = LENGTH vs` by simp[Abbr`vars`,Abbr`vs`] >>
    simp[LibTheory.emp_def,MAP_ZIP] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[compile_dec_def,dec_to_contab_def] >>
    rpt gen_tac >> strip_tac >>
    qexists_tac`0` >>
    rpt gen_tac >>
    strip_tac >>
    simp[LibTheory.emp_def,vs_to_Cvs_MAP] >>
    fs[env_rs_def,LET_THM] >>
    map_every qexists_tac[`bs.refs`,`rd`,`Cs`] >>
    rfs[] >>
    conj_tac >- (
      match_mp_tac RTC_SUBSET >>
      simp[bc_eval1_thm] >>
      fs[Once SWAP_REVERSE] >>
      `bc_fetch bs = SOME (Stack (Cons (block_tag + tuple_cn) 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0`>>simp[] ) >>
      simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      Cases_on`bs.clock`>>fs[Cenv_bs_def,s_refs_def] ) >>
    fs[closed_vlabs_def,closed_Clocs_def] >>
    conj_tac >- (
      rw[] >> match_mp_tac code_env_cd_append >>
      rw[] >> fs[Once SWAP_REVERSE,FILTER_APPEND,ALL_DISTINCT_APPEND,good_labels_def] ) >>
    fs[Cenv_bs_def] >>
    match_mp_tac s_refs_with_irr >>
    qexists_tac`bs with code := bc0 ++ code` >>
    simp[] >>
    reverse conj_tac >- (Cases_on`bs.clock`>>fs[s_refs_def]) >>
    match_mp_tac s_refs_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] ) >>
  simp[])

val compile_decs_contab = store_thm("compile_decs_contab",
  ``∀decs mn menv ct m env rsz cs.
    FST(compile_decs mn menv ct m env rsz cs decs) = decs_to_contab mn ct decs``,
  Induct >> simp[compile_decs_def,decs_to_contab_def] >>
  Cases>>fs[compile_dec_def,decs_to_contab_def,dec_to_contab_def,LET_THM])

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val decs_cns_def = Define`
  (decs_cns _ [] = {}) ∧
  (decs_cns mn (d::ds) = dec_cns d ∪ (decs_cns mn ds DIFF (IMAGE (SOME o mk_id mn) (set (new_dec_cns d)))))`

val evaluate_dec_err_cenv_emp = store_thm("evaluate_dec_err_cenv_emp",
  ``∀mn menv cenv s env d res. evaluate_dec mn menv cenv s env d res ⇒
    ∀err. SND res = Rerr err ∧ err ≠ Rtype_error ⇒ dec_to_cenv mn d = []``,
  ho_match_mp_tac evaluate_dec_ind >> simp[dec_to_cenv_def])

val evaluate_dec_new_dec_cns = store_thm("evaluate_dec_new_dec_cns",
  ``∀mn menv cenv s env d res. evaluate_dec mn menv cenv s env d res ⇒
    ∀tds env. SND res = Rval (tds,env) ⇒
    MAP (mk_id mn) (new_dec_cns d) = (MAP FST tds)``,
  ho_match_mp_tac evaluate_dec_ind >>
  simp[LibTheory.emp_def,SemanticPrimitivesTheory.build_tdefs_def] >>
  rw[] >>
  simp[MAP_MAP_o,MAP_FLAT] >> AP_TERM_TAC >>
  simp[MAP_EQ_f,FORALL_PROD,MAP_MAP_o])

val evaluate_dec_dec_to_cenv = store_thm("evaluate_dec_dec_to_cenv",
  ``∀mn menv cenv s env d res. evaluate_dec mn menv cenv s env d res ⇒
    ∀tds env. SND res = Rval (tds,env) ⇒
    tds = dec_to_cenv mn d``,
  ho_match_mp_tac evaluate_dec_ind >>
  simp[LibTheory.emp_def,dec_to_cenv_def])

val env_rs_change_store = store_thm("env_rs_change_store",
  ``∀menv cenv env rs csz rd cs bs rd' cs' Cs' bs' ck' rf'.
    env_rs menv cenv env rs csz rd cs bs ∧
    (IS_SOME ck' ⇒ ck' = SOME (FST cs')) ∧
    bs' = bs with <| refs := rf'; clock := ck'|> ∧
    LENGTH (SND cs) ≤ LENGTH (SND cs') ∧
    s_refs rd' (FST cs',Cs') bs' ∧
    LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (SND cs')) Cs' ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧
    EVERY all_vlabs Cs' ∧
    (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd (MAP SND o_f rs.rmenv) bs.code cd) ∧
    BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs')
    ⇒
    env_rs menv cenv env rs csz rd' cs' bs'``,
  rw[] >>
  fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
  rpt HINT_EXISTS_TAC >> simp[] >>
  qexists_tac`Cs'` >>
  fs[vs_to_Cvs_MAP] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(FST cs,Cs)`,`bs`,`rf'`,`ck'`] >>
    simp[BytecodeTheory.bc_state_component_equality] ) >>
  fs[closed_Clocs_def,closed_vlabs_def] >>
  fs[EVERY2_EVERY] >>
  full_simp_tac pure_ss [SUBSET_DEF,IN_COUNT] >>
  metis_tac[LESS_LESS_EQ_TRANS])

val env_rs_with_irr = store_thm("env_rs_with_irr",
  ``∀menv cenv env rs cz rd cs bs rs'.
    env_rs menv cenv env rs cz rd cs bs ∧
    rs'.contab = rs.contab ∧
    rs'.rsz = rs.rsz ∧
    rs'.renv = rs.renv ∧
    rs'.rmenv = rs.rmenv
    ⇒
    env_rs menv cenv env rs' cz rd cs bs``,
  simp[env_rs_def])

val env_rs_with_bs_irr = store_thm("env_rs_with_bs_irr",
  ``∀menv cenv env rs cz rd cs bs bs'.
    env_rs menv cenv env rs cz rd cs bs
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.clock = bs.clock
    ∧ bs'.code = bs.code
    ∧ bs'.inst_length = bs.inst_length
    ⇒
    env_rs menv cenv env rs cz rd cs bs'``,
  simp[env_rs_def] >> rw[] >>
  rpt HINT_EXISTS_TAC >> simp[] >>
  match_mp_tac Cenv_bs_with_irr >>
  HINT_EXISTS_TAC >> rfs[])

val env_rs_append_code = store_thm("env_rs_append_code",
  ``∀menv cenv env rs cz rd cs bs bs' c.
    env_rs menv cenv env rs cz rd cs bs ∧
    bs' = bs with code := bs.code ++ c ∧
    ALL_DISTINCT (FILTER is_Label (bs.code ++ c))
    ⇒
    env_rs menv cenv env rs cz rd cs bs'``,
  simp[env_rs_def] >>
  rpt gen_tac >> strip_tac  >>
  rpt HINT_EXISTS_TAC >>
  simp[] >>
  rfs[closed_vlabs_def] >>
  conj_tac >- (
    rw[]>>
    match_mp_tac code_env_cd_append >>
    metis_tac[]) >>
  match_mp_tac Cenv_bs_append_code >>
  metis_tac[])

val compile_decs_append_out = store_thm("compile_decs_append_out",
  ``∀decs mn menv ct m env rsz cs.
    let (ct',m',rsz',cs') = compile_decs mn menv ct m env rsz cs decs in
    LENGTH env = LENGTH m.bvars ∧ {x | Short x ∈ FV_decs decs} ⊆ set m.bvars ⇒
    ∃code. cs'.out = REVERSE code ++ cs.out ∧ between_labels code cs.next_label cs'.next_label ∧
    m'.bvars = FLAT (REVERSE (MAP new_dec_vs decs)) ++ m.bvars ∧
    rsz' = rsz + LENGTH (FLAT (REVERSE (MAP new_dec_vs decs)))``,
  Induct >> simp[compile_decs_def,Once SWAP_REVERSE] >- simp[between_labels_def] >>
  qx_gen_tac`dec` >>
  rpt gen_tac >>
  qabbrev_tac`p = compile_dec menv m env rsz cs dec` >> PairCases_on`p` >> simp[] >>
  Q.PAT_ABBREV_TAC`vs:string list = option_CASE X Y Z` >>
  qspecl_then[`vs`,`p1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
  simp[] >> rw[] >>
  qabbrev_tac`q = compile_news p1 0 vs` >>
  Q.PAT_ABBREV_TAC`m' = exp_to_Cexp_state_bvars_fupd X Y` >>
  Q.PAT_ABBREV_TAC`renv' = GENLIST X Y ++ env` >>
  qabbrev_tac`r = compile_decs mn menv (dec_to_contab mn ct dec) m' renv' (rsz + LENGTH vs) q decs` >>
  PairCases_on`r`>>fs[] >>
  strip_tac >>
  first_x_assum(qspecl_then[`mn`,`menv`,`dec_to_contab mn ct dec`,`m'`,`renv'`,`rsz + LENGTH vs`,`q`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[Abbr`renv'`,Abbr`m'`] >>
    fs[FV_decs_def] >>
    Cases_on`dec`>> fsrw_tac[DNF_ss][SUBSET_DEF,compile_dec_def,LET_THM,dec_to_contab_def,MEM_MAP,FV_defs_MAP,FORALL_PROD,markerTheory.Abbrev_def] >>
    rw[] >> res_tac >>
    qmatch_abbrev_tac`a ∨ b` >>
    Cases_on`b`>>fs[EXISTS_PROD,MEM_MAP] ) >>
  strip_tac >>
  qspecl_then[`menv`,`m`,`env`,`rsz`,`cs`,`dec`]mp_tac compile_dec_append_out >>
  simp[] >>
  discharge_hyps >- (
    fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF] ) >>
  rw[] >> simp[Once SWAP_REVERSE] >>
  fsrw_tac[DNF_ss][between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MEM,MEM_MAP,is_Label_rwt,MEM_FILTER] >>
  `FILTER is_Label code = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[]) >>
  simp[] >>
  fsrw_tac[DNF_ss][between_def,Abbr`m'`,Abbr`vs`] >>
  reverse conj_tac >- (Cases_on`p0`>>fs[]>>simp[])>>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

val evaluate_dec_closed_context = store_thm("evaluate_dec_closed_context",
  ``∀mn menv cenv s env d s' res. evaluate_dec mn menv cenv s env d (s',res) ∧
    closed_context menv cenv s env ∧
    FV_dec d ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
    dec_cns d ⊆ cenv_dom cenv
    ⇒
    let (cenv',env') = case res of Rval(c,e)=>(c++cenv,e++env) | _ => (cenv,env) in
    closed_context menv cenv' s' env'``,
  rpt gen_tac >>
  Cases_on`d`>>simp[Once evaluate_dec_cases]>>
  Cases_on`res`>>simp[]>>strip_tac>>rpt BasicProvers.VAR_EQ_TAC>>simp[LibTheory.emp_def]>>TRY(strip_tac)>>
  TRY (
    fs[closed_context_def] >>
    qmatch_assum_abbrev_tac`evaluate ck menv cenv s0 env e res` >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac(CONJUNCT1 semanticsExtraTheory.evaluate_closed) >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac toIntLangProofsTheory.evaluate_closed_under_cenv >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac (CONJUNCT1 evaluate_locs) >>
    UNABBREV_ALL_TAC >> simp[] >> ntac 3 strip_tac >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    conj_tac >- fs[closed_under_menv_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (
    fs[closed_context_def] >>
    qmatch_assum_abbrev_tac`evaluate ck menv cenv s0 env e res` >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac(CONJUNCT1 semanticsExtraTheory.evaluate_closed) >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac toIntLangProofsTheory.evaluate_closed_under_cenv >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac (CONJUNCT1 evaluate_locs) >>
    UNABBREV_ALL_TAC >> simp[] >> ntac 3 strip_tac >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    qspecl_then[`cenv`,`s'`,`p`,`v`,`emp`]mp_tac(CONJUNCT1 semanticsExtraTheory.pmatch_closed) >>
    simp[] >> disch_then(qspec_then`menv`mp_tac) >>
    simp[LibTheory.emp_def] >> strip_tac >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      qx_gen_tac`z` >> strip_tac >> TRY(metis_tac[]) >>
      imp_res_tac (CONJUNCT1 semanticsExtraTheory.pmatch_all_cns) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,LibTheory.emp_def] >>
      metis_tac[] ) >>
    conj_tac >- fs[closed_under_menv_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
    conj_tac >- (
      qspecl_then[`cenv`,`s'`,`p`,`v`,`emp`,`env'`]mp_tac(CONJUNCT1 pmatch_locs) >>
      discharge_hyps >- (
        simp[] >>
        fsrw_tac[DNF_ss][LibTheory.emp_def,SUBSET_DEF] >>
        metis_tac[] ) >>
      simp[SUBSET_DEF] >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (
    simp[semanticsExtraTheory.build_rec_env_MAP] >>
    fs[closed_context_def,miscTheory.MAP_FST_funs] >>
    simp[EVERY_MAP,UNCURRY] >>
    conj_tac >- (
      simp[Once semanticsExtraTheory.closed_cases] >>
      simp[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      fs[] >> rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      fs[semanticsExtraTheory.FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      qx_gen_tac`z` >> strip_tac >> TRY(metis_tac[]) >>
      pop_assum mp_tac >>
      simp[MEM_MAP,EXISTS_PROD] >> strip_tac >>
      simp[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[closed_under_menv_def,EVERY_MAP,UNCURRY] >>
      simp[Once semanticsExtraTheory.closed_cases] >>
      fs[EVERY_MEM] >>
      fs[FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      fs[semanticsExtraTheory.FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    gen_tac >> strip_tac >> TRY(metis_tac[]) >>
    fs[MEM_MAP,UNCURRY] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP] >>
    metis_tac[] )
  >> (
    simp[SemanticPrimitivesTheory.build_tdefs_def] >>
    Cases_on`mn`>>fs[AstTheory.mk_id_def] >- (
      fs[closed_context_def] >>
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      reverse conj_tac >- metis_tac[] >>
      fs[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      fs [cenv_dom_def] >>
      metis_tac[] ) >>
    fs[closed_context_def] >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      fsrw_tac[DNF_ss][MEM_MAP,SUBSET_DEF] >>
      fs [cenv_dom_def] >>
      metis_tac[] ) >>
    metis_tac[] ))

(*
val evaluate_decs_to_cenv = store_thm("evaluate_decs_to_cenv",
  ``∀mn menv cenv s env decs res.
    evaluate_decs mn menv cenv s env decs res ⇒
    case SND res of (cenv',Rval _) => (cenv' = decs_to_cenv mn decs) | _ => T``,
  ho_match_mp_tac evaluate_decs_ind >>
  simp[LibTheory.emp_def,decs_to_cenv_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  simp[SemanticPrimitivesTheory.combine_dec_result_def] >>
  simp[LibTheory.merge_def] >>
  metis_tac[evaluate_dec_dec_to_cenv,SND])
*)

val evaluate_decs_to_cenv = store_thm("evaluate_decs_to_cenv",
  ``∀mn menv cenv s env decs res.
     evaluate_decs mn menv cenv s env decs res ⇒
     ∃cenv'. decs_to_cenv mn decs = cenv' ++ (FST(SND res))``,
   HO_MATCH_MP_TAC evaluate_decs_ind >>
   simp[LibTheory.emp_def] >> rw[] >>
   imp_res_tac evaluate_dec_dec_to_cenv >>
   fs[] >> simp[decs_to_cenv_def,LibTheory.merge_def])

val evaluate_dec_all_cns = store_thm("evaluate_dec_all_cns",
  ``∀mn menv (cenv:envC) s env dec res.
    evaluate_dec mn menv cenv s env dec res ⇒
    (∀v. MEM v (FLAT (MAP (MAP SND o SND) menv)) ∨ MEM v (MAP SND env) ∨ MEM v s ⇒ all_cns v ⊆ cenv_dom cenv)
    ∧ dec_cns dec ⊆ cenv_dom cenv
    ⇒
    ∀v. MEM v (FST res) ⇒ all_cns v ⊆ cenv_dom cenv``,
  ho_match_mp_tac evaluate_dec_ind >> simp[] >>
  rpt conj_tac >>
  rpt strip_tac >>
  imp_res_tac (CONJUNCT1 evaluate_all_cns) >>
  rfs[] >> metis_tac[] )

val decs_to_cenv_append = store_thm("decs_to_cenv_append",
  ``∀d1 d2. decs_to_cenv mn (d1 ++ d2) = decs_to_cenv mn d2 ++ decs_to_cenv mn d1``,
  Induct >> simp[decs_to_cenv_def])

val decs_to_contab_cmap_SUBMAP = store_thm("decs_to_contab_cmap_SUBMAP",
  ``∀ds mn ct cenv.
    (∀i tds. i < LENGTH ds ∧ (EL i ds = Dtype tds) ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i ds) ++ cenv) tds)
    ∧ FDOM (cmap ct) ⊆ cenv_dom cenv
    ⇒
    cmap ct ⊑ cmap(decs_to_contab mn ct ds)``,
  Induct >> simp[decs_to_contab_def] >>
  Cases >> simp[dec_to_contab_def,FOLDL_number_constructors_thm] >>
  rpt gen_tac >>
  TRY (
    strip_tac >>
    first_x_assum match_mp_tac >>
    qexists_tac `cenv` >>
    simp[] >>
    rpt strip_tac >>
    first_x_assum(qspec_then`SUC i`mp_tac) >>
    simp[decs_to_cenv_def,dec_to_cenv_def] ) >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`ct1:contab = number_constructors X Y Z` >>
  match_mp_tac SUBMAP_TRANS >>
  qexists_tac`cmap ct1` >>
  reverse conj_tac >- (
    first_x_assum match_mp_tac >>
    qexists_tac`dec_to_cenv mn (Dtype l) ++ cenv` >>
    reverse conj_tac >- (
      simp[Abbr`ct1`,number_constructors_thm,FDOM_FUPDATE_LIST,dec_to_cenv_def,SemanticPrimitivesTheory.build_tdefs_def] >>
      PairCases_on`ct`>>fs[] >>
      conj_tac >- (fsrw_tac[DNF_ss][SUBSET_DEF, cenv_dom_def] >> metis_tac[] ) >>
      Q.PAT_ABBREV_TAC`l1:(string#t list) list = FLAT (MAP X l)` >>
      Q.PAT_ABBREV_TAC`l2:(string id #num#string id) list = FLAT (MAP X l)` >>
      `MAP FST l2 = MAP (mk_id mn o FST) l1` by (
        simp[Abbr`l1`,Abbr`l2`,MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF] >>
        AP_TERM_TAC >>
        simp[MAP_EQ_f,FORALL_PROD,MAP_MAP_o] ) >>
      simp[MAP_GENLIST,combinTheory.o_DEF] >>
      fs[SUBSET_DEF, cenv_dom_def, LIST_EQ_REWRITE,EL_MAP, MEM_MAP, MEM_GENLIST] >>
      fs [EL_MAP] >>
      rw [] >>
      disj1_tac >>
      qexists_tac `EL i l2` >>
      rw [EL_MAP] >>
      metis_tac [EL_MEM]) >>
    rpt strip_tac >>
    first_x_assum(qspec_then`SUC i`mp_tac) >>
    simp[decs_to_cenv_def,dec_to_cenv_def] ) >>
  simp[Abbr`ct1`,number_constructors_thm] >>
  PairCases_on`ct`>>simp[] >>
  simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >>
  rpt strip_tac >>
  match_mp_tac EQ_SYM >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
  simp[MEM_MAP,MEM_GENLIST,FORALL_PROD] >>
  first_x_assum(qspec_then`0`mp_tac) >>
  simp[] >>
  strip_tac >>
  imp_res_tac check_dup_ctors_NOT_MEM >>
  rw [METIS_PROVE [] ``(~a ∨ b) = (a ⇒ b)``] >>
  fs[cenv_dom_def, MEM_EL,GSYM LEFT_FORALL_IMP_THM,decs_to_cenv_def,SUBSET_DEF] >>
  res_tac >>
  fs [] >>
  res_tac >>
  fs [] >>
  rw [EL_MAP] >>
  metis_tac [EL_MAP]);

val env_rs_change_clock = store_thm("env_rs_change_clock",
  ``∀menv cenv env rs cz rd cs bs cs' ck' bs'.
    env_rs menv cenv env rs cz rd cs bs ∧
    cs' = (ck',SND cs) ∧
    bs' = bs with clock := SOME ck'
    ⇒
    env_rs menv cenv env rs cz rd cs' bs'``,
  rw[] >>
  fs[env_rs_def,LET_THM] >>
  rfs[] >> fs[] >>
  rpt HINT_EXISTS_TAC >> simp[] >>
  match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
  map_every qexists_tac[`rd`,`(FST cs,Cs)`,`bs`,`bs.refs`,`SOME ck'`] >>
  simp[BytecodeTheory.bc_state_component_equality] >>
  fs[Cenv_bs_def,s_refs_def,good_rd_def])

val Cenv_bs_FUPDATE_CTDec = store_thm("Cenv_bs_FUPDATE_CTDec",
  ``∀rd menv s env rmenv renv rsz csz bs v bv bs' n.
    Cenv_bs rd menv s env rmenv renv rsz csz bs ∧
    Cv_bv (mk_pp rd bs') v bv ∧
    bs' = bs with stack := bv::bs.stack ∧
    n = LENGTH bs.stack
    ⇒
    Cenv_bs rd menv s (v::env) rmenv ((CTDec n)::renv) (rsz+1) csz bs'``,
  rpt gen_tac >>
  simp[Cenv_bs_def] >>
  reverse(reverse(rw[Cenv_bs_def,s_refs_def]) >> fs[CompilerLibTheory.el_check_def] >- fs[good_rd_def]) >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def,fmap_rel_def,CompilerLibTheory.el_check_def] >>
  simp[EL_LENGTH_APPEND_rwt,ADD1] >>
  rpt strip_tac >> res_tac >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[] >>
  qmatch_assum_rename_tac`MEM (a,b) X`["X"] >>
  TRY(
    map_every qexists_tac[`b`,`a`] >>
    simp[]) >>
  strip_tac >>
  fs[option_case_NONE_F] >>
  metis_tac[optionTheory.SOME_11])

val Cenv_bs_FUPDATE_LIST_CTDec = store_thm("Cenv_bs_FUPDATE_LIST_CTDec",
  ``∀vs rd menv s env rmenv cenv sz csz bs bvs bs' env' cenv' sz'.
  Cenv_bs rd menv s env rmenv cenv sz csz bs ∧
  (bs' = bs with stack := bvs ++ bs.stack) ∧
  EVERY2 (Cv_bv (mk_pp rd bs')) vs bvs ∧
  (env' = vs++env) ∧
  (cenv' = (REVERSE(GENLIST(λm. CTDec(LENGTH bs.stack+m))(LENGTH vs)))++cenv) ∧
  (sz' = sz + LENGTH vs)
  ⇒
  Cenv_bs rd menv s env' rmenv cenv' sz' csz bs'``,
  Induct >- ( simp[LENGTH_NIL] ) >>
  rw[] >>
  rw[GENLIST,REVERSE_SNOC] >> simp[ADD1] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac Cenv_bs_FUPDATE_CTDec >>
  qexists_tac`bs with stack := ys ++ bs.stack` >>
  simp[bc_state_component_equality] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    simp[] >>
    qexists_tac`cenv`>>
    qexists_tac`bs` >> simp[] >>
    qexists_tac`ys` >> simp[] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  reverse conj_tac >- fs[EVERY2_EVERY] >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  HINT_EXISTS_TAC >>
  simp[])

val Cenv_bs_perm = store_thm("Cenv_bs_perm",
  ``∀rd menv s env rmenv cenv sz csz bs cenv' env'.
  Cenv_bs rd menv s env rmenv cenv sz csz bs ∧
  LENGTH env' = LENGTH env ∧
  LENGTH cenv' = LENGTH cenv ∧
  PERM (ZIP(env,cenv)) (ZIP(env',cenv'))
  ⇒
  Cenv_bs rd menv s env' rmenv cenv' sz csz bs``,
  simp[Cenv_bs_def,env_renv_def,EVERY2_EVERY] >>
  rw[] >>
  fs[EVERY_MEM] >>
  metis_tac[PERM_MEM_EQ])

(*TODO: MOVE *)
val PERM_ZIP = store_thm("PERM_ZIP",
  ``∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. l1 = ZIP(a,b) ∧ l2 = ZIP(c,d) ∧ LENGTH a = LENGTH b ∧ LENGTH c = LENGTH d ⇒
    PERM a c ∧ PERM b d``,
  ho_match_mp_tac PERM_IND >>
  conj_tac >- (
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] ) >>
  conj_tac >- (
    Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    metis_tac[PERM_MONO]) >>
  conj_tac >- (
    ntac 2 Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LENGTH a = LENGTH b`[] >>
    pop_assum mp_tac >>
    qmatch_assum_rename_tac`LENGTH c = LENGTH d`[] >>
    strip_tac >>
    Cases_on`a`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`b`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`c`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`d`>>fs[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  `∀l. l = ZIP (MAP FST l, MAP SND l)` by (
    simp[ZIP_MAP] >>
    simp[LIST_EQ_REWRITE,EL_MAP] ) >>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS])

val PERM_BIJ = store_thm("PERM_BIJ",
  ``∀l1 l2. PERM l1 l2 ⇒ ∃f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1))``,
  ho_match_mp_tac PERM_IND >> simp[BIJ_EMPTY] >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(f i)` >>
    simp[EL_CONS,PRE_SUB1] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- ( Cases >> simp[] ) >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(g i)` >>
    conj_tac >- ( Cases >> simp[] ) >>
    conj_tac >- ( Cases >> simp[] ) >>
    ( Cases >> simp[] )) >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))` >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))` >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[])) >>
  ntac 2 (rw[LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  fs[LENGTH_GENLIST] >>
  qexists_tac`f o f'` >>
  simp[combinTheory.o_DEF] >>
  fs[BIJ_IFF_INV] >>
  qexists_tac`g' o g` >>
  simp[combinTheory.o_DEF] )

(*
val PERM_BIJ_IFF = store_thm("PERM_BIJ_IFF",
  ``∀l1 f l2. BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1)⇒
             PERM l1 l2``,
  Induct >- simp[] >>
  simp[PERM_CONS_EQ_APPEND] >>

  rw[GENLIST_CONS,combinTheory.o_DEF] >>
  simp[PERM_CONS_EQ_APPEND] >>
  qexists_tac`EL (f 0) (h::l1)::GENLIST (λi. EL (? i) l1) (LENGTH l1)

val env_rs_perm = store_thm("env_rs_perm",
  ``∀menv cenv env rs csz rd cs bs env' rs' renv'.
    env_rs menv cenv env rs csz rd cs bs ∧
    rs' = rs with renv := renv' ∧
    LENGTH env' = LENGTH env ∧
    LENGTH renv' = LENGTH rs.renv ∧
    PERM (ZIP (env,rs.renv)) (ZIP(env',renv'))
    ⇒
    env_rs menv cenv env' rs' csz rd cs bs``,
  simp[env_rs_def] >> rw[] >>
  HINT_EXISTS_TAC >> simp[] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`Cs` >>
  rfs[] >> fs[] >>
  `LENGTH env = LENGTH rs.renv` by fs[LIST_EQ_REWRITE] >>
  imp_res_tac PERM_BIJ >> rfs[BIJ_IFF_INV] >>
  qexists_tac`GENLIST (λi. EL (f i) Cenv) (LENGTH env)` >>
  `LENGTH Cenv = LENGTH env` by fs[EVERY2_EVERY,env_to_Cenv_MAP] >>
  conj_tac >- (
    rfs[EVERY2_EVERY,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rpt strip_tac >> first_x_assum match_mp_tac >>
    simp[MEM_ZIP] >>
    qexists_tac`f n` >>
    simp[EL_MAP] >>
    rpt AP_TERM_TAC >>
    rfs[LIST_EQ_REWRITE,EL_ZIP] ) >>
  conj_tac >- (
    fs[closed_Clocs_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,LIST_EQ_REWRITE,MEM_GENLIST] >>
    rfs[EL_GENLIST,EL_ZIP] >>
    `LENGTH Cenv = LENGTH env` by fs[EVERY2_EVERY,env_to_Cenv_MAP] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    fs[closed_vlabs_def,EVERY_GENLIST,vlabs_list_MAP,MEM_GENLIST] >>
    fsrw_tac[DNF_ss][] >>
    reverse conj_tac >- metis_tac[MEM_EL] >>
    fs[EVERY_MEM] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    match_mp_tac EQ_SYM >>
    simp[MAP_EQ_EVERY2] >>
    simp[EVERY2_EVERY,EVERY_GENLIST,EL_ZIP] >>
    metis_tac[LIST_EQ_REWRITE,MEM_EL,EL_MAP] ) >>
  match_mp_tac Cenv_bs_perm >>
  qexists_tac`Cenv` >>
  qexists_tac`MAP (CTDec o SND) rs.renv` >>
  simp[] >>
  match_mp_tac PERM_BIJ_IFF >>
  qexists_tac`f` >>
  simp[BIJ_IFF_INV] >>
  conj_tac >- metis_tac[] >>
  simp[LIST_EQ_REWRITE,EL_ZIP,EL_MAP] >>
  fs[LIST_EQ_REWRITE] >> rfs[EL_ZIP] )
*)

val new_decs_renv_def = Define`
  (new_decs_renv _ [] = []) ∧
  (new_decs_renv z (d::ds) =
   let vs = new_dec_vs d in
   let n = LENGTH vs in
    new_decs_renv (z+n) ds ++ ZIP(vs,GENLIST($+ z)n))`

val evaluate_dec_new_dec_vs = store_thm("evaluate_dec_new_dec_vs",
  ``∀mn menv (cenv:envC) s env dec res.
    evaluate_dec mn menv cenv s env dec res ⇒
    ∀tds vs. (SND res = Rval (tds,vs)) ⇒ MAP FST vs = new_dec_vs dec``,
  ho_match_mp_tac evaluate_dec_ind >>
  simp[LibTheory.emp_def] >> rw[] >>
  imp_res_tac pmatch_dom >> fs[])

val evaluate_decs_closed_context = store_thm("evaluate_decs_closed_context",
  ``∀mn menv cenv s env ds res. evaluate_decs mn menv cenv s env ds res ⇒
      closed_context menv cenv s env ∧
      FV_decs ds ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
      decs_cns mn ds ⊆ cenv_dom cenv
    ⇒
      let env' = case SND(SND res) of Rval(e)=>(e++env) | _ => env in
      closed_context menv ((FST(SND res))++cenv) (FST res) env'``,
  ho_match_mp_tac evaluate_decs_ind >>
  simp[LibTheory.emp_def] >>
  conj_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    fs[FV_decs_def,decs_cns_def] >>
    imp_res_tac evaluate_dec_closed_context >>
    fs[] >> fs[LET_THM] ) >>
  simp[SemanticPrimitivesTheory.combine_dec_result_def,LibTheory.merge_def] >>
  rpt gen_tac >> rpt strip_tac >>
  qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`,`s'`,`Rval (new_tds,new_env)`]mp_tac evaluate_dec_closed_context >>
  simp[] >> strip_tac >>
  Cases_on`r`>>fs[]>- (
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,decs_cns_def] >>
    imp_res_tac evaluate_dec_new_dec_cns >> fs[] >>
    pop_assum(assume_tac o AP_TERM``LIST_TO_SET:string id list -> string id set``) >>
    imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
    pop_assum(assume_tac o AP_TERM``LIST_TO_SET:string list -> string set``) >>
    fsrw_tac[DNF_ss][MEM_MAP,EXTENSION, cenv_dom_def] >>
    metis_tac[]) >>
  qpat_assum`P ⇒ Q`mp_tac>>
  discharge_hyps>-(
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,decs_cns_def] >>
    metis_tac[]) >>
  strip_tac >>
  qsuff_tac`closed_context menv (new_tds' ++ new_tds ++ cenv) s3 (new_env ++ env)` >- (
    rw[closed_context_def] >> fs[] >>
    fs[toIntLangProofsTheory.closed_under_cenv_def,closed_under_menv_def] >>
    metis_tac[] ) >>
  first_x_assum match_mp_tac >>
  fs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,decs_cns_def] >>
  imp_res_tac evaluate_dec_new_dec_cns >> fs[] >>
  pop_assum(assume_tac o AP_TERM``LIST_TO_SET:string id list -> string id set``) >>
  imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
  pop_assum(assume_tac o AP_TERM``LIST_TO_SET:string list -> string set``) >>
  fsrw_tac[DNF_ss][cenv_dom_def,MEM_MAP,EXTENSION] >>
  metis_tac[]);

val EVERY2_REVERSE1 = store_thm("EVERY2_REVERSE1",
  ``∀l1 l2. EVERY2 R l1 (REVERSE l2) ⇔ EVERY2 R (REVERSE l1) l2``,
  rpt gen_tac >> EQ_TAC >>
  simp[EVERY2_EVERY] >> rpt strip_tac >>
  ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] >>
  simp[REVERSE_ZIP])

val vlabs_list_REVERSE = store_thm("vlabs_list_REVERSE",
  ``∀ls. vlabs_list (REVERSE ls) = vlabs_list ls``,
  Induct >> simp[vlabs_list_APPEND] >> metis_tac[UNION_COMM])

val compile_decs_thm = store_thm("compile_decs_thm",
  ``∀mn menv cenv s env decs res.
    evaluate_decs mn menv cenv s env decs res ⇒
    ∃ck. ∀rmenv ct m renv rsz cs ct' m' rsz' cs' code rs csz rd bs bc0.
    compile_decs mn rmenv ct m renv rsz cs decs = (ct',m',rsz',cs')
    ∧ cs'.out = REVERSE code ++ cs.out
    ∧ (∀i tds. i < LENGTH decs ∧ (EL i decs = Dtype tds) ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i decs) ++ cenv) tds)
    ∧ closed_context menv cenv s env
    ∧ FV_decs decs ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
    ∧ decs_cns mn decs ⊆ cenv_dom cenv
    ∧ env_rs menv cenv env rs csz rd (ck,s) (bs with code := bc0)
    ∧ rmenv = MAP SND o_f rs.rmenv
    ∧ renv = MAP (CTDec o SND) rs.renv
    ∧ rsz = rs.rsz
    ∧ rs.rnext_label = cs.next_label
    ∧ rs.contab = ct
    ∧ m.bvars = MAP FST env
    ∧ m.mvars = MAP FST o_f alist_to_fmap menv
    ∧ m.cnmap = cmap ct
    ∧ bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ IS_SOME bs.clock
    ∧ good_labels rs.rnext_label bc0
    ⇒
    case SND(SND res) of
    | Rval env' =>
      ∃bvs rf rd'.
      let s' = FST res in
      let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ code); stack := bvs++bs.stack; refs := rf; clock := SOME 0|> in
      let n = rsz' - rsz in
      let rs' = rs with <|rnext_label := cs'.next_label
                         ;contab := ct'
                         ;renv := ZIP(TAKE n m'.bvars,GENLIST(λi. rsz+n-1-i)n) ++ rs.renv
                         ;rsz := rsz'
                         |> in
      bc_next^* bs bs'
      ∧ env_rs menv (FST(SND res)++cenv) (env'++env) rs' csz rd' (0,s') bs'
    | Rerr(Rraise err) =>
      ∀ig h0 sp st0.
        bs.stack = ig ++ StackPtr h0::CodePtr sp::st0
      ∧ bs.handler = LENGTH st0 + 1
      ∧ csz = LENGTH st0
      ⇒
      ∃bv rf rd' Cs'.
      let s' = FST res in
      let bs' = bs with <|pc := sp; stack := bv::st0; handler := h0; refs := rf; clock := SOME 0|> in
      bc_next^* bs bs'
      ∧ err_bv err bv
      ∧ LENGTH s ≤ LENGTH s'
      ∧ LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap ct') s') Cs'
      ∧ s_refs rd' (0,Cs') bs'
      ∧ DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm))
      ∧ rd.sm ≼ rd'.sm
      ∧ rd.cls ⊑ rd'.cls
      ∧ EVERY all_vlabs Cs'
      ∧ (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd (MAP SND o_f rs.rmenv) (bc0++code) cd)
      ∧ BIGUNION (IMAGE all_Clocs (set Cs')) ⊆ count (LENGTH Cs')
    | _ => T``,
  ho_match_mp_tac evaluate_decs_ind >>
  strip_tac >- (
    simp[compile_decs_def] >>
    simp[decs_cns_def,FV_decs_def,Once SWAP_REVERSE,LibTheory.emp_def] >>
    rpt gen_tac >>
    qexists_tac`0` >>
    rpt gen_tac >>
    strip_tac >>
    map_every qexists_tac [`[]`,`bs.refs`,`rd`] >>
    simp[] >>
    simp[new_decs_renv_def] >>
    `bs.clock = SOME 0` by (
      Cases_on`bs.clock`>>fs[env_rs_def,LET_THM,Cenv_bs_def,s_refs_def] ) >>
    conj_tac >- (
      simp[Once RTC_CASES1] >>
      disj1_tac >>
      simp[bc_state_component_equality] ) >>
    qmatch_abbrev_tac`env_rs menv cenv env rs' rsz rd cks bs'` >>
    `rs' = rs ∧ bs' = bs` by (
      simp[Abbr`rs'`,Abbr`bs'`,bc_state_component_equality,compiler_state_component_equality] ) >>
    simp[]) >>
  strip_tac >- (
    simp[compile_decs_def] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac compile_dec_thm >>
    qexists_tac`ck` >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`rmenv = MAP SND o_f rs.rmenv` >>
    Q.PAT_ABBREV_TAC`renv:ctenv = MAP x rs.renv` >>
    qabbrev_tac`p = compile_dec rmenv m renv rs.rsz cs d` >>
    PairCases_on`p`>>fs[]>>
    Cases_on`e = Rtype_error`>>simp[]>>
    `∃vs. p0 = SOME vs` by (
      Cases_on`d`>>fs[compile_dec_def,LET_THM,markerTheory.Abbrev_def]>>
      last_x_assum mp_tac >>
      simp[Once evaluate_dec_cases] ) >>
    simp[] >>
    strip_tac >>
    qspecl_then[`rmenv`,`m`,`renv`,`rs.rsz`,`cs`,`d`]mp_tac compile_dec_append_out >>
    simp[] >>
    `LENGTH renv = LENGTH env` by (
      simp[Abbr`renv`] >>
      fs[env_rs_def,LET_THM,LIST_EQ_REWRITE]) >>
    simp[] >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
      metis_tac[prove(``∀mn x v y. Short v ≠ Long mn x ∧ (Short x = Short y ⇒ x = y)``,rw[])] ) >>
    disch_then(qx_choosel_then[`c0`]strip_assume_tac) >>
    first_x_assum(qspecl_then[`m`,`cs`,`SOME vs`,`p1`,`rs`,`rd`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`bs with code := bc0++c0`,`bc0`,`csz`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      rfs[FV_decs_def,decs_cns_def] >> metis_tac[] ) >>
    Cases_on`e`>>simp[]>>
    strip_tac >> rpt strip_tac >>
    first_x_assum(qspec_then`ig`mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`bv`,`rf`,`rd'`,`Cs'`]strip_assume_tac) >>
    map_every qexists_tac[`bv`,`rf`,`rd'`] >>
    simp[] >>
    qmatch_assum_abbrev_tac`compile_decs mn rmenv ct m1 renv1 rsz1 cs1 ds = X` >>
    rfs[] >> fs[] >>
    qspecl_then[`ds`,`mn`,`rmenv`,`ct`,`m1`,`renv1`,`rsz1`,`cs1`]mp_tac compile_decs_append_out >>
    simp[Abbr`X`] >>
    discharge_hyps >- (
      simp[Abbr`renv1`,Abbr`m1`] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
      metis_tac[prove(``∀mn x v y. Short v ≠ Long mn x ∧ (Short x = Short y ⇒ x = y)``,rw[])] ) >>
    simp[Abbr`cs1`] >>
    qspecl_then[`vs`,`p1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
    simp[] >>
    disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
    simp[Once SWAP_REVERSE_SYM] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    qexists_tac`Cs'` >> simp[] >>
    conj_tac >- (
      match_mp_tac RTC_bc_next_append_code >>
      qexists_tac`bs with code := bc0 ++ c0` >>
      HINT_EXISTS_TAC >>
      simp[bc_state_component_equality]) >>
    conj_tac >- (
      qmatch_abbrev_tac `EVERY2 syneq vs1 Cs'` >>
      qmatch_assum_abbrev_tac `EVERY2 syneq vs2 Cs'` >>
      qsuff_tac`vs1 = vs2` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac(CONJUNCT1(CONJUNCT2 v_to_Cv_SUBMAP)) >>
      imp_res_tac evaluate_dec_all_cns >>
      rfs[decs_cns_def] >>
      pop_assum mp_tac >>
      discharge_hyps >- fs[closed_context_def,closed_under_cenv_def] >>
      strip_tac >>
      `cenv_dom cenv ⊆ FDOM (cmap rs.contab)` by (
        fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF] ) >>
      conj_tac >- (
        simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF] >>
        fs[SUBSET_DEF] >> metis_tac[] ) >>
      qmatch_assum_abbrev_tac`compile_decs mn xrmenv xct xm xrenv xrsz xcs ds = X` >>
      qspecl_then[`ds`,`mn`,`xrmenv`,`xct`,`xm`,`xrenv`,`xrsz`,`xcs`]mp_tac compile_decs_contab >>
      simp[Abbr`xm`,Abbr`X`,Abbr`xct`] >> strip_tac >>
      qspecl_then[`d::ds`,`mn`,`rs.contab`,`cenv`]mp_tac decs_to_contab_cmap_SUBMAP >>
      simp[decs_to_contab_def] >>
      disch_then match_mp_tac >>
      fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF] ) >>
    conj_tac >- (
      Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd X Y` >>
      match_mp_tac s_refs_append_code >>
      qexists_tac`bs0 with code := bc0 ++ c0` >>
      simp[Abbr`bs0`,bc_state_component_equality] ) >>
    rw[] >>
    REWRITE_TAC[Once(GSYM APPEND_ASSOC)] >>
    match_mp_tac code_env_cd_append >>
    rw[] >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    fsrw_tac[DNF_ss][between_labels_def,good_labels_def,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    `FILTER is_Label c1 = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[]) >>
    simp[] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  rpt gen_tac >>
  simp[compile_decs_def] >>
  strip_tac >>
  imp_res_tac compile_dec_thm >>
  qexists_tac`ck + ck'` >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac`rmenv = MAP SND o_f rs.rmenv` >>
  qabbrev_tac`renv = MAP (CTDec o SND) rs.renv` >>
  qspecl_then[`rmenv`,`m`,`renv`,`rs.rsz`,`cs`,`d`]mp_tac compile_dec_append_out >>
  qabbrev_tac`p = compile_dec rmenv m renv rs.rsz cs d` >>
  `LENGTH renv = LENGTH env` by (
    rpt (rator_x_assum`env_rs`mp_tac) >>
    unabbrev_all_tac >>
    rpt (pop_assum kall_tac) >>
    simp[env_rs_def,LET_THM,LIST_EQ_REWRITE] >> rw[] ) >>
  PairCases_on`p`>>simp[] >>
  discharge_hyps >- (
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
    qpat_assum`∀x. x ∈ FV_dec d ⇒ P`mp_tac >>
    rpt (pop_assum kall_tac) >>
    rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
  disch_then(qx_choosel_then[`c0`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`rmenv`,`m`,`renv`,`rs.rsz`,`cs`]mp_tac) >>
  simp[] >>
  `bs.clock = SOME (ck + ck')` by (
    Cases_on`bs.clock`>>fs[] >>
    rator_x_assum`env_rs`mp_tac >>
    pop_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    simp[env_rs_def] >>
    rw[Cenv_bs_def,s_refs_def] ) >>
  disch_then(qspecl_then[`rs`,`rd`,`bs with <| code := bc0 ++ c0; clock := SOME ck'|>`,`bc0`,`csz`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,decs_cns_def] >>
    match_mp_tac env_rs_change_clock >>
    qexists_tac`ck+ck',s` >>
    simp[] >>
    TRY HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] >>
    qexists_tac`bs with <|stack := st0; code := bc0|>` >>
    simp[bc_state_component_equality] ) >>
  disch_then(qx_choosel_then[`Cws`,`bvs`,`rf`,`rd'`,`Cs'`]strip_assume_tac) >>
  fs[] >>
  qmatch_abbrev_tac`G` >>
  qpat_assum`X = (ct',m',rsz',cs')`mp_tac >>
  Q.PAT_ABBREV_TAC`vs:string list = option_CASE X Y Z` >>
  Q.PAT_ABBREV_TAC`m1 = exp_to_Cexp_state_bvars_fupd X Y` >>
  Q.PAT_ABBREV_TAC`renv1 = GENLIST X Y ++ renv` >>
  Q.PAT_ABBREV_TAC`rsz1 = X + rs.rsz` >>
  Q.PAT_ABBREV_TAC`cs1 = compile_news p1 X Y` >>
  Q.PAT_ABBREV_TAC`ct1 = dec_to_contab X Y d` >>
  qabbrev_tac`n = LENGTH vs` >>
  strip_tac >>
  first_x_assum(qspecl_then[`m1`,`cs1`]mp_tac) >>
  qabbrev_tac`rs1 = rs with <|contab := ct1
                             ;renv := ZIP(vs,GENLIST (λi. rs.rsz+n-1-i) n)++rs.renv
                             ;rsz := rsz1
                             ;rnext_label := cs1.next_label|>` >>
  disch_then(qspec_then`rs1`mp_tac o CONV_RULE(RESORT_FORALL_CONV((op@) o List.partition (equal "rs" o fst o dest_var)))) >>
  simp[Abbr`rs1`] >>
  Q.PAT_ABBREV_TAC`ls = MAP (CTDec o SND) Z` >>
  `ls ++ renv = renv1` by (
    simp[Abbr`ls`,Abbr`renv1`,Abbr`m1`,TAKE_APPEND1,MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF]) >>
  simp[] >>
  qspecl_then[`vs`,`p1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Once SWAP_REVERSE_SYM] >>
  `LENGTH renv1 = LENGTH m1.bvars ∧ {x | Short x ∈ FV_decs decs} ⊆ set m1.bvars` by (
    qunabbrev_tac`G` >> rpt BasicProvers.VAR_EQ_TAC >>
    simp[Abbr`m1`,Abbr`ls`,Abbr`n`] >>
    simp[Abbr`vs`] >>
    Cases_on`d`>>
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_decs_def,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
    rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
  qspecl_then[`decs`,`mn`,`rmenv`,`ct1`,`m1`,`renv1`,`rsz1`,`cs1`]mp_tac compile_decs_append_out >>
  simp[] >>
  simp[Once SWAP_REVERSE_SYM] >>
  disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
  simp[] >>
  qmatch_abbrev_tac`H ⇒ G` >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
  first_x_assum(qspecl_then[`bs1 with code := bc0 ++ c0 ++ c1`,`bc0 ++ c0`]mp_tac) >>
  simp[Abbr`bs1`] >>
  `vs = MAP FST new_env` by (
    simp[Abbr`n`,Abbr`vs`,Abbr`G`,Abbr`H`] >>
    Cases_on`d`>>fs[]>>
    fs[Once evaluate_dec_cases] >>
    rfs[LibTheory.emp_def] ) >>
  `LENGTH bvs = n` by (
    simp[Abbr`n`,Abbr`vs`,Abbr`G`,Abbr`H`] >>
    rpt (rator_x_assum`EVERY2`mp_tac) >>
    simp[EVERY2_EVERY,vs_to_Cvs_MAP]) >>
  simp[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1'` >>
  `bs1' = bs1 with code := bc0 ++ c0` by (
    simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] ) >>
  qunabbrev_tac`H` >>
  disch_then(qspecl_then[`csz`,`rd'`,`bs2 with <| code := bs.code; clock := SOME ck|>`]mp_tac) >>
  simp[] >>
  simp[Abbr`bs2`] >>
  discharge_hyps >- (
    simp[LibTheory.merge_def,Abbr`m1`] >>
    conj_tac >- (
      simp[LibTheory.merge_def] >>
      rpt strip_tac >>
      last_x_assum(qspec_then`SUC i`mp_tac) >>
      simp[decs_to_cenv_def,Abbr`G`] >>
      imp_res_tac evaluate_dec_dec_to_cenv >>
      fs[] ) >>
    conj_tac >- (
      simp[LibTheory.merge_def] >>
      qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`,`s'`,`Rval(new_tds,new_env)`]mp_tac evaluate_dec_closed_context >>
      simp[] >>
      disch_then match_mp_tac >>
      fs[FV_decs_def,decs_cns_def] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      Cases>>simp[]>>
      strip_tac >> res_tac >> fs[] >>
      metis_tac[] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,decs_cns_def,Abbr`G`] >>
      rpt strip_tac >> res_tac >>
      imp_res_tac evaluate_dec_new_dec_cns >> fs[] >>
      fs [cenv_dom_def, MEM_MAP] >>
      metis_tac[MEM_MAP] ) >>
    reverse conj_asm2_tac >- (
      fsrw_tac[DNF_ss][good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,between_labels_def,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
      `FILTER is_Label c1 = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[] ) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    map_every qunabbrev_tac[`G`,`bs0`,`bs1'`] >>
    rator_x_assum`env_rs`mp_tac >>
    rator_x_assum`s_refs`mp_tac >>
    simp[] >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    rpt strip_tac >>
    match_mp_tac env_rs_append_code >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd X Y` >>
    qexists_tac`bs0 with code := bc0 ++ c0` >>
    simp[bc_state_component_equality,Abbr`bs0`] >>
    reverse conj_tac >- (
      fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      metis_tac[] ) >>
    Cases_on`new_tds = []` >- (
      simp[] >>
      `ct1 = rs.contab` by (
        simp[Abbr`ct1`] >>
        Cases_on`d`>>fs[dec_to_contab_def] >>
        fs[Once evaluate_dec_cases] >>
        qpat_assum`[] = X`mp_tac >>
        simp[SemanticPrimitivesTheory.build_tdefs_def,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,FORALL_PROD,UNCURRY,EXISTS_PROD] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        simp[FOLDL_number_constructors_thm] >>
        Q.PAT_ABBREV_TAC`ll = FLAT (MAP (SND o SND) l)` >>
        strip_tac >>
        `ll = []` by (
          simp[Abbr`ll`,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,EXISTS_PROD] >>
          metis_tac[] ) >>
        simp[number_constructors_def] ) >>
      simp[] >>
      fs[env_rs_def,LET_THM] >>
      rfs[] >> fs[] >>
      qexists_tac`Cmenv` >>
      simp[MAP_ZIP] >>
      simp[Abbr`rsz1`] >>
      simp[TAKE_APPEND1,TAKE_LENGTH_ID_rwt] >>
      qexists_tac`REVERSE Cws ++ Cenv` >>
      qexists_tac`Cs'` >>
      fs[vs_to_Cvs_MAP] >>
      conj_tac >- (
        match_mp_tac EVERY2_APPEND_suff >>
        simp[] >>
        simp[env_to_Cenv_MAP] >>
        fs[MAP_MAP_o,MAP_REVERSE] >>
        metis_tac[EVERY2_REVERSE1]) >>
      conj_tac >- (
        fs[closed_Clocs_def] >>
        `LENGTH Cs ≤ LENGTH Cs'` by (
          fs[EVERY2_EVERY] >> metis_tac[] ) >>
        full_simp_tac list_ss [SUBSET_DEF,IN_COUNT] >>
        metis_tac[LESS_LESS_EQ_TRANS] ) >>
      conj_tac >- (
        fs[closed_vlabs_def,vlabs_list_APPEND,EVERY_REVERSE,vlabs_list_REVERSE] >>
        rw[] >> TRY(metis_tac[]) >>
        match_mp_tac code_env_cd_append >>
        fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] ) >>
      qunabbrev_tac`renv1` >>
      Q.PAT_ABBREV_TAC`renw:ctenv = GENLIST X n` >>
      (*
      match_mp_tac Cenv_bs_perm >>
      map_every qexists_tac [`REVERSE Cws ++ Cenv`,`REVERSE renw ++ renv`] >>
      reverse conj_tac >- (
        simp[] >>
        conj_asm1_tac >- simp[Abbr`renw`] >>
        `LENGTH Cws = n` by fs[EVERY2_EVERY] >>
        `LENGTH renw = LENGTH Cws` by simp[Abbr`renw`] >>
        `LENGTH Cenv = LENGTH renv` by fs[EVERY2_EVERY,env_to_Cenv_MAP] >>
        qmatch_abbrev_tac`PERM (ZIP(A++B,C++D))(ZIP(E++B,G++D))` >>
        `ZIP(A++B,C++D)=ZIP(A,C)++ZIP(B,D)` by (
          match_mp_tac(GSYM ZIP_APPEND) >>
          metis_tac[LENGTH_REVERSE] ) >>
        pop_assum SUBST1_TAC >>
        `ZIP(E++B,G++D)=ZIP(E,G)++ZIP(B,D)` by (
          match_mp_tac(GSYM ZIP_APPEND) >>
          metis_tac[LENGTH_REVERSE] ) >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[CONJUNCT2 PERM_APPEND_IFF] >>
        map_every qunabbrev_tac[`A`,`C`] >>
        metis_tac[REVERSE_ZIP,PERM_REVERSE_EQ,PERM_REFL] ) >>
      *)
      match_mp_tac Cenv_bs_FUPDATE_LIST_CTDec >>
      simp[Abbr`renw`] >>
      map_every qexists_tac[`REVERSE Cws`,`Cenv`,`renv`,`LENGTH bs.stack`] >>
      simp[REVERSE_GENLIST,PRE_SUB1] >>
      Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd x y` >>
      qexists_tac`bs0 with stack := bs.stack` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      `n = LENGTH Cws` by ( simp[Abbr`n`] >> fs[EVERY2_EVERY] ) >>
      simp[] >>
      reverse conj_tac >- (
        conj_tac >- (
          match_mp_tac EVERY2_REVERSE >>
          simp[] ) >>
        simp[LIST_EQ_REWRITE] ) >>
      match_mp_tac Cenv_bs_with_irr >>
      qexists_tac`bs with <|code := bc0 ++ c0; refs := rf; clock := SOME ck|>` >>
      simp[] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac[`rd`,`ck+ck',Cs`,`bs with code := bc0 ++ c0`,`rf`,`SOME ck`] >>
      simp[bc_state_component_equality] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_append_code >>
        qexists_tac`bs with code := bc0` >>
        simp[bc_state_component_equality] >>
        fsrw_tac[ARITH_ss][] ) >>
      fs[s_refs_def,Abbr`bs1`,good_rd_def] ) >>
    `new_env = []` by (
      Cases_on`d`>>fs[Once evaluate_dec_cases,LibTheory.emp_def] ) >>
    simp[] >>
    match_mp_tac env_rs_change_store >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd X Y` >>
    map_every qexists_tac[`rd`,`ck,s`,`bs0 with <|refs:=bs.refs;clock:=SOME ck|>`] >>
    simp[Abbr`bs0`,bc_state_component_equality] >>
    qexists_tac`Cs'`>>simp[] >>
    reverse conj_tac >- (
      conj_tac >- (
        match_mp_tac s_refs_with_irr >>
        qexists_tac`bs1 with <| code := bc0 ++ c0; clock := SOME ck|>` >>
        simp[Abbr`bs1`] >>
        `n = 0` by fs[Abbr`n`] >>
        fs[s_refs_def,good_rd_def] ) >>
      qmatch_abbrev_tac `EVERY2 syneq vs1 Cs'` >>
      qmatch_assum_abbrev_tac `EVERY2 syneq vs2 Cs'` >>
      qsuff_tac`vs1 = vs2` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac(CONJUNCT1(CONJUNCT2 v_to_Cv_SUBMAP)) >>
      imp_res_tac evaluate_dec_all_cns >>
      rfs[decs_cns_def] >>
      pop_assum mp_tac >>
      discharge_hyps >- fs[closed_context_def,closed_under_cenv_def] >>
      strip_tac >>
      `cenv_dom cenv ⊆ FDOM (cmap rs.contab)` by (
        fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF] ) >>
      conj_tac >- (
        simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF] >>
        fs[SUBSET_DEF] >> metis_tac[] ) >>
      qspecl_then[`[d]`,`mn`,`rs.contab`,`cenv`]mp_tac decs_to_contab_cmap_SUBMAP >>
      simp[decs_to_contab_def] >>
      disch_then match_mp_tac >>
      fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF,decs_to_cenv_def] >>
      last_x_assum(qspec_then`0`mp_tac) >>
      simp[decs_to_cenv_def] >> strip_tac >>
      Cases_on`mn`>>fs[AstTheory.mk_id_def] >> metis_tac[] ) >>
    match_mp_tac env_rs_change_clock >>
    qexists_tac`ck+ck',s` >> simp[] >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd x y` >>
    qexists_tac`bs0 with clock := bs.clock` >>
    simp[Abbr`bs0`,bc_state_component_equality] >>
    match_mp_tac env_rs_with_bs_irr >>
    qexists_tac`bs with code := bc0 ++ c0` >>
    simp[] >> fs[] >>
    `n = 0` by rfs[EVERY2_EVERY,Abbr`n`] >> fs[LENGTH_NIL] >>
    simp[Abbr`rsz1`] >>
    match_mp_tac env_rs_with_irr >>
    qexists_tac`rs with contab := ct1` >>
    simp[] >>
    match_mp_tac env_rs_append_code >>
    qexists_tac`bs with code := bc0` >>
    simp[bc_state_component_equality] >>
    fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    match_mp_tac decs_contab_thm >>
    map_every qexists_tac [`mn`,`[d]`,`cenv`,`rs`] >>
    simp[decs_to_cenv_def,Abbr`ct1`,decs_to_contab_def] >>
    imp_res_tac evaluate_dec_dec_to_cenv >> fs[] >>
    last_x_assum(qspec_then`0`mp_tac) >>
    simp[decs_to_cenv_def] >> strip_tac >>
    Cases_on`mn`>>fs[AstTheory.mk_id_def] >> metis_tac[] ) >>
  Cases_on`r`>>fs[] >- (
    simp[LibTheory.merge_def,Abbr`G`,SemanticPrimitivesTheory.combine_dec_result_def] >>
    disch_then(qx_choosel_then[`bvs2`,`rf2`,`rd2`]strip_assume_tac) >>
    map_every qexists_tac[`bvs2++REVERSE bvs`,`rf2`,`rd2`] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
      qmatch_abbrev_tac`bc_next^* bs bs4'` >>
      `bs4' = bs4` by (
        simp[Abbr`bs4`,Abbr`bs4'`,bc_state_component_equality] ) >>
      pop_assum SUBST1_TAC >> qunabbrev_tac`bs4'` >>
      qmatch_assum_abbrev_tac`bc_next^* bs1 bs3'` >>
      qspecl_then[`bs1`,`bs3'`]mp_tac RTC_bc_next_add_clock >> simp[] >>
      disch_then(qspec_then`ck`mp_tac) >>
      simp[Abbr`bs1`,Abbr`bs3'`] >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
      qspecl_then[`bs0`,`bs1'`]mp_tac RTC_bc_next_add_clock >> simp[] >>
      disch_then(qspec_then`ck`mp_tac) >>
      simp[Abbr`bs1`,Abbr`bs0`] >>
      qmatch_abbrev_tac`bc_next^* bs0 bs1 ⇒ bc_next^* bs9 bs2 ⇒ Z` >> rw[] >>
      `bc_next^* bs (bs1 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs0`,`bs1`] >>
        simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
      `bc_next^* (bs1 with code := bs.code) (bs2 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs9`,`bs2`] >>
        simp[Abbr`bs9`,Abbr`bs2`,bc_state_component_equality,Abbr`bs1`] ) >>
      `bs3 = bs2 with code := bs.code` by (
        simp[Abbr`bs3`,Abbr`bs2`] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    qmatch_abbrev_tac`env_rs menv xcenv xenv xrs xzz rd2 xcs xbs` >>
    qmatch_assum_abbrev_tac`env_rs menv xcenv xenv yrs xzz rd2 xcs ybs` >>
    `xbs = ybs` by (
      simp[Abbr`ybs`,Abbr`xbs`,bc_state_component_equality] ) >>
    `xrs = yrs` by (
      simp[Abbr`yrs`,Abbr`xrs`,compiler_state_component_equality,Abbr`rsz1`] >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      Q.PAT_ABBREV_TAC`fd:string list =  FLAT X` >>
      simp[GENLIST_APPEND] >>
      simp[ZIP_APPEND] >>
      simp[Abbr`m1`,TAKE_APPEND1] >>
      simp[Abbr`n`,TAKE_LENGTH_ID_rwt]) >>
    simp[] ) >>
  Cases_on`e`>>simp[Abbr`G`,SemanticPrimitivesTheory.combine_dec_result_def] >>
  strip_tac >> rpt strip_tac >>
  first_x_assum(qspec_then`REVERSE bvs ++ ig`mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`bv`,`rf2`,`rd2`,`Cs2`]strip_assume_tac) >>
  map_every qexists_tac[`bv`,`rf2`,`rd2`,`Cs2`] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
  reverse conj_tac >- metis_tac[IS_PREFIX_TRANS] >>
  reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
  reverse conj_tac >- (
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
  qmatch_abbrev_tac`bc_next^* bs bs4'` >>
  `bs4' = bs4` by simp[Abbr`bs4`,Abbr`bs4'`,bc_state_component_equality] >>
  `bc_next^* bs (bs1 with <|code := bs.code; clock := SOME ck|>)` by (
    match_mp_tac RTC_bc_next_append_code >>
    qexists_tac`bs with code := bs1.code` >>
    qexists_tac`bs1 with clock := SOME ck` >>
    simp[bc_state_component_equality,Abbr`bs1`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    qspecl_then[`bs0`,`bs1`]mp_tac RTC_bc_next_add_clock >>
    simp[] >>
    disch_then(qspec_then`ck`mp_tac) >>
    simp[Abbr`bs1`,Abbr`bs0`] >> strip_tac >>
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    map_every qexists_tac[`bs0`,`bs1`] >>
    simp[bc_state_component_equality,Abbr`bs0`,Abbr`bs1`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bs1`,`bs2`]mp_tac RTC_bc_next_add_clock >>
  simp[] >>
  disch_then(qspec_then`ck`mp_tac) >>
  simp[Abbr`bs1`,Abbr`bs2`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs25` >>
  `bc_next^* bs25 bs3` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs2'`,`bs3'`] >>
    simp[Abbr`bs25`,Abbr`bs2'`,Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def] )

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val evaluate_decs_new_decs_vs = store_thm("evaluate_decs_new_decs_vs",
  ``∀mn menv cenv s env decs res.
    evaluate_decs mn menv cenv s env decs res ⇒
    ∀env'. SND (SND res) = Rval env' ⇒ MAP FST env' = new_decs_vs decs``,
  ho_match_mp_tac evaluate_decs_ind >>
  simp[LibTheory.emp_def,SemanticPrimitivesTheory.combine_dec_result_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  simp[LibTheory.merge_def] >>
  metis_tac[evaluate_dec_new_dec_vs,SND])

val new_decs_renv_vs = store_thm("new_decs_renv_vs",
  ``∀decs rsz. MAP FST (new_decs_renv rsz decs) = new_decs_vs decs``,
  Induct >> simp[new_decs_renv_def] >> simp[MAP_ZIP])

val env_renv_shift = store_thm("env_renv_shift",
  ``∀rd sz bs env renv sz' bs' renv' st' ls ls'.
      env_renv rd sz bs env renv
      ∧ bs' = bs with stack := st'
      ∧ renv = MAP CTDec ls
      ∧ renv' = MAP CTDec ls'
      ∧ EVERY2 (λi i'. i < LENGTH bs.stack ⇒ i' < LENGTH st' ∧ EL i' (REVERSE st') = EL i (REVERSE bs.stack)) ls ls'
      ⇒
      env_renv rd sz' bs' env renv'``,
  rw[env_renv_def] >>
  fs[EVERY2_EVERY,EVERY_MEM] >>
  rpt(qpat_assum`X = Y`mp_tac) >> ntac 2 strip_tac >>
  fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
  fs[CompilerLibTheory.el_check_def,option_case_NONE_F])

val compile_decs_wrap_thm = store_thm("compile_decs_wrap_thm",
  ``∀mn menv cenv s env decs res.
    evaluate_decs mn menv cenv s env decs res
    ∧ FV_decs decs ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
    ∧ (∀i tds. i < LENGTH decs ∧ (EL i decs = Dtype tds) ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i decs) ++ cenv) tds)
    ∧ closed_context menv cenv s env
    ∧ decs_cns mn decs ⊆ cenv_dom cenv
    ⇒
    ∀rs. ∃ck ct renv cs. compile_decs_wrap mn rs decs = (ct,renv,cs) ∧
    ∀rd bs bc0.
    env_rs menv cenv env rs (LENGTH bs.stack) rd (ck,s) (bs with code := bc0)
    ∧ bs.code = bc0 ++ (REVERSE cs.out)
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ IS_SOME bs.clock
    ∧ good_labels rs.rnext_label bc0
    ⇒
    case SND (SND res) of
    | Rval env' =>
      ∃bvs rf rd'.
      let s' = FST res in
      let cenv' = FST (SND res) in
      let bs' = bs with <|pc := next_addr bs.inst_length bs.code; stack := bvs++bs.stack; refs := rf; clock := SOME 0
                         (*;output := if IS_NONE mn then REVERSE(print_envE env')++bs.output else bs.output*)|> in
      let rs' = rs with <|contab := ct; rnext_label := cs.next_label; renv := renv++rs.renv; rsz := rs.rsz+LENGTH renv|> in
      bc_next^* bs bs'
      ∧ env_rs menv (cenv'++cenv) (env'++env) rs' (LENGTH bs.stack) rd' (0,s') bs'
    | Rerr (Rraise err) =>
      ∃bv rf rd'.
      let s' = FST res in
      let cenv' = decs_to_cenv mn decs in
      let bs' = bs with <|pc := 0; stack := bv::bs.stack; refs := rf; clock := SOME 0|> in
      let rs' = rs with <|contab := ct; rnext_label := cs.next_label|> in
      bc_next^* bs bs'
      ∧ err_bv err bv
      ∧ env_rs menv (cenv'++cenv) env rs' (LENGTH bs.stack) rd' (0,s') (bs' with stack := bs.stack)
    | _ => T``,
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >>
  simp[compile_decs_wrap_def] >>
  Q.PAT_ABBREV_TAC`rmenv = MAP SND o_f rs.rmenv` >>
  Q.PAT_ABBREV_TAC`m = exp_to_Cexp_state_bvars_fupd x y` >>
  Q.PAT_ABBREV_TAC`renv:ctenv = MAP X Y` >>
  Q.PAT_ABBREV_TAC`rsz = rs.rsz+x` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd (K [x;z]) y` >>
  Q.PAT_ABBREV_TAC`ct = rs.contab` >>
  `LENGTH renv = LENGTH m.bvars` by (
    simp[Abbr`renv`,Abbr`m`] ) >>
  qabbrev_tac`p = compile_decs mn rmenv ct m renv rsz cs decs` >>
  PairCases_on`p`>>simp[] >>
  Q.PAT_ABBREV_TAC`ct' = (p0,p1,p2)` >>
  Q.PAT_ABBREV_TAC`renv':(string,num)alist = ZIP X` >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X p5` >>
  Q.PAT_ABBREV_TAC`cs2 = compile_news Y 0 Z` >>
  imp_res_tac compile_decs_thm >>
  qexists_tac`ck` >>
  rpt gen_tac >> strip_tac >>
  qmatch_abbrev_tac`G` >>
  qspecl_then[`decs`,`mn`,`rmenv`,`ct`,`m`,`renv`,`rsz`,`cs`]mp_tac compile_decs_append_out >>
  `{x | Short x ∈ FV_decs decs} ⊆ set m.bvars` by (
    simp[Abbr`m`,Abbr`G`] >>
    first_x_assum(qspec_then`rmenv`kall_tac) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
    rw[] >> res_tac >> fs[] >>
    fs[env_rs_def,LET_THM] >>
    metis_tac[MEM_MAP,FST,pairTheory.PAIR_EQ,pairTheory.pair_CASES] ) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`rmenv`,`ct`,`m`,`renv`,`rsz`,`cs`]mp_tac) >>
  simp[] >>
  qspecl_then[`TAKE (p4-rsz) p3.bvars`,`cs1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
  simp[] >>
  disch_then(qx_choosel_then[`c3`]strip_assume_tac) >>
  qabbrev_tac`c0 = [PushPtr (Addr 0);PushExc]` >>
  qmatch_assum_abbrev_tac`p4 = rsz + n` >>
  qabbrev_tac`c2 = [Stack (Cons tuple_cn n); PopExc; Stack (Pops 1)]` >>
  `bs.code = bc0 ++ c0 ++ c1 ++ c2 ++ c3` by (
    simp[Abbr`cs1`,Abbr`cs`,Abbr`c0`,Abbr`c2`] ) >>
  pop_assum mp_tac >>
  qpat_assum`bs.code = X`kall_tac >>
  strip_tac >>
  qabbrev_tac`hdl = LENGTH bs.stack+1` >>
  qabbrev_tac`h0 = bs.handler` >>
  qabbrev_tac`bs0 = bs with <| pc := next_addr bs.inst_length (bc0++c0); stack := StackPtr h0::CodePtr 0::bs.stack; handler := hdl |>` >>
  `bc_next^* bs bs0` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC 0)` >>
    simp[NRC] >>
    `bc_fetch bs = SOME (PushPtr (Addr 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0 ++ TAKE 0 c0` >>
      simp[Abbr`c0`] ) >>
    simp[Once bc_eval1_thm] >>
    simp[bc_eval1_def,bc_find_loc_def,bump_pc_def] >>
    qmatch_abbrev_tac`bc_next bs1 bs0` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0 ++ TAKE 1 c0` >>
      simp[Abbr`bs1`,Abbr`c0`,SUM_APPEND,FILTER_APPEND] ) >>
    simp[bc_eval1_thm] >>
    simp[bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,Abbr`bs0`,bc_state_component_equality,Abbr`hdl`,Abbr`c0`,SUM_APPEND,FILTER_APPEND] ) >>
  disch_then(qspecl_then[`rs with rsz := rsz`,`LENGTH bs.stack`,`rd`,`bs0 with code := bc0++c0++c1`,`bc0 ++ c0`]mp_tac) >>
  simp[Abbr`bs0`] >>
  `good_labels rs.rnext_label (bc0 ++ c0)` by (
    fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,Abbr`c0`] ) >>
  discharge_hyps >- (
    simp[Abbr`cs`,Abbr`m`] >>
    conj_asm1_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs with <|code := bc0++c0; stack := StackPtr h0::CodePtr 0::bs.stack|>` >>
      simp[] >>
      match_mp_tac env_rs_append_code >>
      qexists_tac`bs with <|code := bc0; stack := StackPtr h0::CodePtr 0::bs.stack|>` >>
      simp[bc_state_component_equality] >>
      fs[good_labels_def] >>
      rator_x_assum`env_rs`mp_tac >>
      qunabbrev_tac`rsz` >>
      rpt(pop_assum kall_tac) >>
      simp[env_rs_def] >> rw[] >>
      rpt HINT_EXISTS_TAC >>
      simp[] >>
      REWRITE_TAC[TWO,ADD1,ADD_ASSOC] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <|stack:=CodePtr 0::bs.stack;code:= bc0|>` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <|code:= bc0|>` >>
      simp[bc_state_component_equality] >>
      rfs[] ) >>
    fs[env_rs_def,LET_THM] ) >>
  PairCases_on`res`>>fs[] >>
  strip_tac >>
  simp[Abbr`G`] >>
  Cases_on`res2`>>fs[]>-(
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_next^* (bs1 with code := bs.code) (bs2 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2`] >>
      simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
    `n = LENGTH bvs` by (
      simp[Abbr`n`] >>
      fs[env_rs_def,LET_THM,Abbr`bs2`,Abbr`rsz`] >>
      rfs[] >> fsrw_tac[ARITH_ss][] ) >>
    `bc_next^* (bs2 with code := bs.code)
      (bs2 with <|code := bs.code; pc := next_addr bs.inst_length (bc0 ++ c0 ++ c1 ++ c2)
                 ;stack := Block tuple_cn (REVERSE bvs)::bs.stack
                 ;handler := bs.handler|>)` by (
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC(SUC 0))` >>
      simp[NRC] >>
      qho_match_abbrev_tac`∃bs3. bc_next bs0 bs3 ∧ P bs3` >>
      `bc_fetch bs0 = SOME (Stack(Cons tuple_cn n))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`,Abbr`c2`] >>
        qexists_tac`bc0++c0++c1` >>
        simp[Abbr`bs2`] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs0`,bc_eval_stack_def] >>
      simp[Abbr`bs2`,TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
      simp[Abbr`P`] >>
      qho_match_abbrev_tac`∃bs3. bc_next bs0 bs3 ∧ P bs3` >>
      `bc_fetch bs0 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`] >>
        qexists_tac`bc0++c0++c1++(TAKE 1 c2)` >>
        simp[Abbr`c2`,SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,Abbr`hdl`,EL_APPEND2,bump_pc_def,TAKE_APPEND2,REVERSE_APPEND] >>
      simp[Abbr`P`] >>
      qho_match_abbrev_tac`bc_next bs0 bs3` >>
      `bc_fetch bs0 = SOME (Stack(Pops 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`] >>
        qexists_tac`bc0++c0++c1++(TAKE 2 c2)` >>
        simp[Abbr`c2`,SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_eval_stack_def,Abbr`bs0`,Abbr`bs3`,bc_state_component_equality,Abbr`h0`,Abbr`c2`,SUM_APPEND,FILTER_APPEND] ) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1'` >>
    `bs1' = bs1 with code := bs.code` by (
      simp[Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
    qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
    `bc_next^* bs bs3'` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    pop_assum mp_tac >>
    simp[Abbr`bs3'`,Abbr`bs2`,Abbr`bs2'`,Abbr`bs1`,Abbr`bs1'`] >>
    rpt(qpat_assum`bc_next^* X Y`kall_tac) >> pop_assum kall_tac >>
    strip_tac >> qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    first_x_assum(qspecl_then[`bs1`]mp_tac) >>
    simp[Abbr`bs1`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    map_every qexists_tac[`bvs`,`rf`,`rd''`] >>
    conj_tac >- (
      qmatch_abbrev_tac`bc_next^* bs bs2'` >>
      `bs2' = bs2` by (
        simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,Abbr`cs1`,SUM_APPEND,FILTER_APPEND,Abbr`cs`,REVERSE_APPEND,Abbr`c2`]) >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    qmatch_assum_abbrev_tac`env_rs menv cenv2 renv2 rs2 st0 rd2 ck2 bss2` >>
    qmatch_abbrev_tac`env_rs menv cenv2 renv2 rs3 st0 rd2 ck2 bss3` >>
    rator_x_assum`env_rs`mp_tac >>
    `rs2.contab = ct'` by simp[Abbr`rs2`] >>
    `rs3.contab = ct'` by simp[Abbr`rs3`] >>
    `rs2.rmenv = rs.rmenv` by simp[Abbr`rs2`] >>
    `rs3.rmenv = rs.rmenv` by simp[Abbr`rs3`] >>
    `rs3.rsz = LENGTH renv' + rs.rsz` by simp[Abbr`rs3`] >>
    `rs3.renv = renv' ++ rs.renv` by simp[Abbr`rs3`] >>
    `bss3.code = bs.code` by simp[Abbr`bss3`] >>
    `bss3.stack = bvs ++ bs.stack` by simp[Abbr`bss3`] >>
    simp[env_rs_def] >> strip_tac >>
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    conj_tac >- (
      fs[closed_vlabs_def,Abbr`bss2`] >>
      REWRITE_TAC[prove(``bc0 ++ c0 ++ c1 ++ c2 ++ c3:bc_inst list = bc0 ++ c0 ++ c1 ++ (c2 ++ c3)``,rw[])] >>
      qabbrev_tac`ll = c2 ++ c3` >>
      `FILTER is_Label ll = []` by (
        simp[FILTER_EQ_NIL,Abbr`ll`,Abbr`c2`] >>
        fs[EVERY_MEM] ) >>
      `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0 ++ c1))` by (
        fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,good_labels_def,between_labels_def,MEM_FILTER,EVERY_MEM,between_def,MEM_MAP,is_Label_rwt] >>
        simp[Abbr`c0`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >>
        fs[Abbr`cs`] >> DECIDE_TAC ) >>
      rpt strip_tac >>
      match_mp_tac code_env_cd_append >>
      simp[] >> fs[FILTER_APPEND] ) >>
    conj_tac >- (
      simp[Abbr`renv2`,Abbr`renv'`,MAP_ZIP,TAKE_APPEND1,TAKE_LENGTH_ID_rwt] >>
      imp_res_tac evaluate_decs_new_decs_vs >> fs[] >>
      fs[env_rs_def,LET_THM] ) >>
    conj_tac >- ( fs[env_rs_def,LET_THM] ) >>
    conj_tac >- (
      simp[Abbr`renv'`,Abbr`st0`] >>
      fs[env_rs_def,LET_THM] ) >>
    match_mp_tac Cenv_bs_append_code >>
    qexists_tac`bss3 with code := bss2.code` >>
    simp[Abbr`bss3`,Abbr`bss2`,bc_state_component_equality] >>
    qmatch_assum_abbrev_tac`Cenv_bs rd2 Cmenv Cs2 Cenv rmenv renvx rs2.rsz st0 sbs2` >>
    match_mp_tac Cenv_bs_with_irr >>
    qexists_tac`sbs2 with stack := bvs++bs.stack` >>
    simp[Abbr`sbs2`] >>
    fs[Cenv_bs_def] >>
    simp[CONJ_ASSOC] >>
    reverse conj_tac >- (
      match_mp_tac s_refs_with_irr >>
      HINT_EXISTS_TAC >> simp[] )>>
    reverse conj_tac >- (
      rator_x_assum`fmap_rel`mp_tac >>
      simp[DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt,ADD1,Abbr`hdl`]) >>
    rator_x_assum`env_renv`mp_tac >>
    simp[Abbr`rs2`,Abbr`renvx`,MAP_ZIP,MAP_GENLIST,Abbr`renv'`] >>
    simp[Abbr`rsz`] >>
    Q.PAT_ABBREV_TAC`renv1:ctenv = GENLIST X Y` >>
    qunabbrev_tac`renv2` >>
    Q.PAT_ABBREV_TAC`renv2:ctenv = GENLIST X Y` >>
    simp[Abbr`st0`] >>
    strip_tac >>
    `∀n. MEM (CTDec n) renv ⇒ n < LENGTH (bs with code := bc0).stack` by (
      rpt strip_tac >>
      match_mp_tac (GEN_ALL Cenv_bs_CTDec_bound) >>
      rator_x_assum`env_rs`mp_tac >>
      simp[env_rs_def,Abbr`renv`] >>
      fs[MEM_MAP,GSYM MAP_MAP_o] >>
      metis_tac[MEM_MAP] ) >>
    match_mp_tac env_renv_shift >>
    qmatch_assum_abbrev_tac`env_renv rd2 sz2 bss2 Cenv (renv1++renv)` >>
    map_every qexists_tac [`sz2`,`bss2`,`renv1++renv`] >>
    simp[bc_state_component_equality,Abbr`bss2`] >>
    qunabbrev_tac`renv` >>
    qunabbrev_tac`renv1` >>
    qunabbrev_tac`renv2` >>
    simp[GSYM MAP_MAP_o,GSYM MAP_GENLIST] >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    Q.PAT_ABBREV_TAC`ls:num list = GENLIST X Y ++ Z` >>
    Q.PAT_ABBREV_TAC`ls':num list = GENLIST X Y ++ Z` >>
    map_every qexists_tac[`ls`,`ls'`] >> simp[] >>
    fs[MEM_MAP] >>
    simp[Abbr`ls`,Abbr`ls'`,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    qx_gen_tac`z` >> strip_tac >>
    `rs.rsz = LENGTH bs.stack` by fs[env_rs_def,LET_THM] >>
    Cases_on`z<LENGTH bvs`>>simp[EL_APPEND1,EL_APPEND2,REVERSE_APPEND,Abbr`sz2`,Abbr`hdl`,EL_MAP,ADD1] (*>- (
      simp[EL_CONS,PRE_SUB1] ) >>*) >>
    fsrw_tac[DNF_ss][MEM_EL,Abbr`m`] >>
    Q.PAT_ABBREV_TAC`m = z - X` >>
    `m < LENGTH rs.renv` by simp[Abbr`m`] >>
    res_tac >>
    simp[EL_APPEND1]) >>
  Cases_on`e`>>fs[] >>
  first_x_assum(qspec_then`[]`mp_tac) >> simp[] >> strip_tac >>
  map_every qexists_tac[`bv`,`rf`,`rd''`] >> simp[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* (bs1 with code := bs.code) (bs2 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs1`,`bs2`] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1'` >>
  `(bs1 with code := bs.code) = bs1'` by (
    simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] ) >>
  conj_tac >- (
    qmatch_abbrev_tac`bc_next^* bs bs2'` >>
    `bs2' = bs2 with code := bs.code` by (
      simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] ) >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  `ct' = decs_to_contab mn ct decs` by metis_tac[compile_decs_contab,FST] >>
  match_mp_tac env_rs_with_bs_irr >>
  qexists_tac`bs with <|refs:=rf;clock:=SOME 0|>` >>
  simp[] >>
  match_mp_tac env_rs_change_store >>
  map_every qexists_tac[`rd`,`ck,s`,`bs`] >>
  simp[bc_state_component_equality] >>
  qexists_tac`Cs'` >> fs[] >>
  simp[CONJ_ASSOC] >>
  `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0 ++ c1))` by (
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,good_labels_def,between_labels_def,MEM_FILTER,EVERY_MEM,between_def,MEM_MAP,is_Label_rwt] >>
    simp[Abbr`c0`] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >>
    fs[Abbr`cs`] >> DECIDE_TAC ) >>
  qabbrev_tac`ll = c2 ++ c3` >>
  `FILTER is_Label ll = []` by (
    simp[FILTER_EQ_NIL,Abbr`ll`,Abbr`c2`] >>
    fs[EVERY_MEM] ) >>
  reverse conj_tac >- (
    rw[] >>
    REWRITE_TAC[prove(``bc0 ++ c0 ++ c1 ++ c2 ++ c3:bc_inst list = bc0 ++ c0 ++ c1 ++ (c2 ++ c3)``,rw[])] >>
    match_mp_tac code_env_cd_append >>
    fs[FILTER_APPEND,Abbr`ll`] ) >>
  reverse conj_tac >- (
    match_mp_tac s_refs_append_code >>
    qexists_tac`bs with <|refs:=rf;clock:=SOME 0;code:=bs2.code|>` >>
    simp[Abbr`bs2`,bc_state_component_equality] >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  match_mp_tac env_rs_append_code >>
  qexists_tac`bs with code := bc0` >>
  simp[bc_state_component_equality] >>
  fs[FILTER_APPEND,Abbr`ll`] >>
  match_mp_tac decs_contab_thm >>
  map_every qexists_tac[`mn`,`decs`] >>
  simp[] >>
  qexists_tac`rs with rnext_label := cs1.next_label` >>
  simp[compiler_state_component_equality] >>
  match_mp_tac env_rs_with_irr >>
  HINT_EXISTS_TAC >>
  simp[])

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"]

val top_cns_def = Define`
  (top_cns (Tdec d) = dec_cns d) ∧
  (top_cns (Tmod mn _ ds) = decs_cns (SOME mn) ds)`
val _ = export_rewrites["top_cns_def"]

val new_top_cns_def = Define`
  (new_top_cns (Tdec d) = set (new_dec_cns d)) ∧
  (new_top_cns (Tmod _ _ ds) = new_decs_cns ds)`
val _ = export_rewrites["new_top_cns_def"]

val compile_decs_wrap_append_out = store_thm("compile_decs_wrap_append_out",
  ``∀mn rs ds. let (ct,renv,cs) = compile_decs_wrap mn rs ds in
      {x | Short x ∈ FV_decs ds} ⊆ set (MAP FST rs.renv)
      ⇒
      between_labels cs.out rs.rnext_label cs.next_label
      ∧ MAP SND renv = REVERSE(GENLIST (λi. rs.rsz+i) (LENGTH renv))``,
  simp[compile_decs_wrap_def] >>
  rw[] >>
  Q.PAT_ABBREV_TAC`rmenv = MAP SND o_f rs.rmenv` >>
  Q.PAT_ABBREV_TAC`m = exp_to_Cexp_state_bvars_fupd x y` >>
  Q.PAT_ABBREV_TAC`renv:ctenv = MAP X Y` >>
  Q.PAT_ABBREV_TAC`rsz = rs.rsz+x` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd (K [x;z]) y` >>
  Q.PAT_ABBREV_TAC`ct = rs.contab` >>
  qabbrev_tac`p = compile_decs mn rmenv ct m renv rsz cs ds` >>
  PairCases_on`p`>>simp[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X p5` >>
  strip_tac >>
  qspecl_then[`ds`,`mn`,`rmenv`,`ct`,`m`,`renv`,`rsz`,`cs`]mp_tac compile_decs_append_out >>
  simp[] >>
  discharge_hyps >- (
    simp[Abbr`m`,Abbr`renv`] ) >>
  strip_tac >>
  qspecl_then[`TAKE (p4-rsz) p3.bvars`,`cs1`,`0`]mp_tac(INST_TYPE[alpha|->``:string``] compile_news_thm) >>
  simp[] >>
  simp[Abbr`cs1`] >> rw[] >> simp[] >- (
    fsrw_tac[DNF_ss][between_labels_def,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND
                    ,EVERY_REVERSE,EVERY_MEM,MAP_REVERSE,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def,Abbr`cs`] >>
    `FILTER is_Label code' = []` by (
      srw_tac[DNF_ss][FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] ) >>
    simp[]) >>
  simp[MAP_ZIP] >>
  simp[REVERSE_GENLIST,PRE_SUB1] >>
  simp[LIST_EQ_REWRITE])

val closed_top_def = Define`
  closed_top menv cenv s env top ⇔
    closed_context menv cenv s env ∧
    FV_top top ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
    top_cns top ⊆ cenv_dom cenv`

val compile_print_vals_thm = store_thm("compile_print_vals_thm",
  ``∀vs i cs. let cs' = compile_print_vals i vs cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
         ∧ cs'.next_label = cs.next_label
         ∧ EVERY ($~ o is_Label) code ∧
    ∀bs bc0 bvs st0.
    bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.stack = bvs ++ st0
    ∧ i + LENGTH vs ≤ LENGTH bvs
    ⇒
    let bs' = bs with <|pc := next_addr bs.inst_length (bc0++code)
                       ;output := bs.output ++ print_bv_list bs.cons_names vs (TAKE (LENGTH vs) (DROP i bvs))|> in
    bc_next^* bs bs'``,
  Induct >> simp[compile_print_vals_def] >- (
    simp[Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >>
    disj1_tac >>
    simp[bc_state_component_equality] )>>
  simp[FOLDL_emit_thm] >>
  qx_gen_tac`v` >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  first_x_assum(qspecl_then[`i+1`,`cs1`]mp_tac) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE] >>
  simp[EVERY_MAP] >> fs[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  qmatch_assum_abbrev_tac`(compile_print_vals (i+1) vs cs1').next_label = X` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  fs[Abbr`cs1'`] >> pop_assum kall_tac >>
  rpt gen_tac >>
  strip_tac >>
  fs[IMPLODE_EXPLODE_I] >>
  `bs.code = bc0 ++ (MAP PrintC ("val "++v++" = ")) ++ [Stack(Load i);Print] ++ c1` by (
    simp[] ) >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc:=next_addr bs.inst_length (bc0++l1)
                          ;output:=STRCAT bs.output ("val "++v++" = ")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`"val "++v++" = "`>>
    qexists_tac`bc0` >>
    simp[Abbr`l1`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  `bc_fetch bs1 = SOME (Stack (Load i))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0++l1` >>
    simp[Abbr`l2`] ) >>
  `bc_next^* bs1 (bs1 with <|pc:=next_addr bs.inst_length(bc0++l1++l2)
                            ;output := STRCAT bs1.output (print_bv bs.cons_names (EL i bvs))|>)` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC 0)` >>
    simp[NRC] >>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def,EL_APPEND1]>>
    simp[Abbr`P`]>>
    qmatch_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++[HD l2]` >>
      simp[Abbr`bs1`,Abbr`l2`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def]>>
    simp[Abbr`bs1`,Abbr`bs2`]>>
    simp[bc_state_component_equality,IMPLODE_EXPLODE_I] >>
    simp[FILTER_APPEND,SUM_APPEND,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  pop_assum mp_tac >>
  rpt(qpat_assum`bc_next^* a Y`kall_tac) >>
  first_x_assum(qspecl_then[`bs2`,`bc0++l1++l2`,`bvs`]mp_tac) >>
  simp[Abbr`bs2`,Abbr`bs1`,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  strip_tac >>
  qmatch_abbrev_tac`bc_next^* bs bs2'` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,Abbr`l1`] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    REWRITE_TAC[Once ADD_SYM] >>
    simp[TAKE_SUM] >>
    simp[DROP_DROP] >>
    `TAKE 1 (DROP i bvs) = [EL i bvs]` by (
      qpat_assum`X ≤ LENGTH bvs`mp_tac >>
      rpt (pop_assum kall_tac) >>
      qid_spec_tac`vs` >>
      qid_spec_tac`i` >>
      Induct_on`bvs`>>simp[] >>
      rw[] >>
      simp[EL_CONS,PRE_SUB1] >>
      first_x_assum match_mp_tac >>
      pop_assum mp_tac >>
      simp[ADD1] >> strip_tac >>
      qexists_tac`vs` >>
      simp[] ) >>
    simp[print_bv_str_def]) >>
  metis_tac[RTC_TRANSITIVE,transitive_def] )

val _ = Parse.overload_on("print_ctor",``λx. STRCAT (id_to_string (Short x)) " = <constructor>"``)
val _ = Parse.overload_on("print_ctors",``λls. FLAT (MAP (λ(x,y). print_ctor x) ls)``)

val compile_print_ctors_thm = store_thm("compile_print_ctors_thm",
  ``∀ls cs. let cs' = compile_print_ctors ls cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
      ∧ EVERY ($~ o is_Label) code
      ∧ cs'.next_label = cs.next_label ∧
      ∀bs bc0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ⇒
      let bs' = bs with <|pc := next_addr bs.inst_length bs.code
           ; output := STRCAT bs.output (print_ctors ls)|> in
      bc_next^* bs bs'``,
  Induct >- (
    simp[compile_print_ctors_def,Once SWAP_REVERSE] >>
    rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  simp[compile_print_ctors_def,FOLDL_emit_thm,IMPLODE_EXPLODE_I] >>
  rw[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd x y` >>
  first_x_assum(qspec_then`cs1`mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE,EVERY_MAP] >> fs[] >>
  qmatch_assum_abbrev_tac`(compile_print_ctors ls cs1).next_label = X` >>
  qmatch_abbrev_tac`((compile_print_ctors ls cs1').next_label = X) ∧ Y` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  simp[Abbr`X`,Abbr`Y`] >>
  rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc := next_addr bs.inst_length (bc0++l1++l2)
                          ;output := bs.output ++ (x0++" = <constructor>")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`x0 ++ " = <constructor>"` >>
    qexists_tac`bc0` >>
    simp[Abbr`l1`,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++l1++l2`]mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
  qmatch_abbrev_tac`bc_next^* bs bs3` >>
  `bs2 = bs3` by (
    simp[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality,SemanticPrimitivesTheory.id_to_string_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val compile_print_dec_thm = store_thm("compile_print_dec_thm",
  ``∀d cs. let cs' = compile_print_dec d cs in
      ∃code. cs'.out = REVERSE code ++ cs.out
        ∧ EVERY ($~ o is_Label) code
        ∧ cs'.next_label = cs.next_label ∧
      ∀bs bc0 bvs st0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ bs.stack = bvs ++ st0
      ∧ LENGTH bvs = LENGTH (new_dec_vs d)
      ⇒
      let str =
        case d of
        | Dtype ts => print_envC (build_tdefs NONE ts)
        | d => print_bv_list bs.cons_names (new_dec_vs d) bvs in
      let bs' = bs with
        <|pc := next_addr bs.inst_length (bc0++code)
         ;output := bs.output ++ str|> in
      bc_next^* bs bs'``,
  Cases >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`pat_bindings p []`,`0`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bvs`]mp_tac) >>
    simp[TAKE_LENGTH_ID_rwt] )
  >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    Q.PAT_ABBREV_TAC`vs:string list = MAP X l` >>
    qspecl_then[`vs`,`0`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bvs`]mp_tac) >>
    `vs = MAP FST l` by (
      simp[Abbr`vs`,MAP_EQ_f,FORALL_PROD] ) >>
    simp[TAKE_LENGTH_ID_rwt]) >>
  simp[] >>
  simp[compile_print_dec_def] >>
  Induct_on`l` >- (
    simp[compile_print_types_def,Once SWAP_REVERSE] >>
    simp[print_envC_def,SemanticPrimitivesTheory.build_tdefs_def,LENGTH_NIL] >>
    rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  simp[compile_print_types_def] >>
  gen_tac >>
  qspecl_then[`x2`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  first_x_assum(qspec_then`compile_print_ctors x2 cs`mp_tac) >>
  simp[] >>
  disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
  simp[] >>
  simp[Once SWAP_REVERSE] >>
  rpt strip_tac >>
  last_x_assum(qspecl_then[`bs with code := bc0 ++ c1`,`bc0`]mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
  `bc_next^* bs (bs1 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs0`,`bs1`] >>
    simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
  first_x_assum(qspecl_then[`bs1 with code := bs.code`]mp_tac) >>
  simp[Abbr`bs1`] >>
  simp[LENGTH_NIL] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1`,Abbr`bs1'`] ) >>
  qmatch_abbrev_tac`bc_next^* bs bs2'` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`] >>
    simp[bc_state_component_equality] >>
    simp[SemanticPrimitivesTheory.build_tdefs_def,print_envC_def] >>
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    simp[UNCURRY,AstTheory.mk_id_def] >>
    simp[LAMBDA_PROD] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val compile_top_append_code = store_thm("compile_top_append_code",
  ``∀rs top.
      {x | Short x ∈ FV_top top} ⊆ set (MAP FST rs.renv)
      ⇒
      between_labels (SND(SND(compile_top rs top))) rs.rnext_label (FST(compile_top rs top)).rnext_label ∧
      ((FST(SND(compile_top rs top))).rnext_label = (FST(compile_top rs top)).rnext_label)``,
   gen_tac >> Cases >> strip_tac >>
   simp[compile_top_def,UNCURRY,FOLDL_emit_thm] >- (
     qmatch_assum_rename_tac`{x | Short x ∈ FV_top (Tmod mn spec ds)} ⊆ X`["X"] >>
     qspecl_then[`SOME mn`,`rs`,`ds`]mp_tac compile_decs_wrap_append_out >>
     qabbrev_tac`p  = compile_decs_wrap (SOME mn) rs ds` >>
     PairCases_on`p`>> simp[] >>
     discharge_hyps >- fs[] >>
     simp[] >> strip_tac >>
     fs[between_labels_def,IMPLODE_EXPLODE_I] >>
     simp_tac std_ss [REVERSE_APPEND] >>
     simp_tac std_ss [FILTER_APPEND] >>
     simp_tac std_ss [FILTER] >>
     simp_tac std_ss [FILTER_REVERSE] >>
     Q.PAT_ABBREV_TAC`ls = FILTER is_Label (X::Y)` >>
     `ls = []` by (
       simp[Abbr`ls`,FILTER_EQ_NIL,EVERY_MAP] ) >>
     simp[] >>
     Q.PAT_ABBREV_TAC`ll = FILTER is_Label X` >>
     `ll = []` by (
       simp[Abbr`ll`,FILTER_EQ_NIL,EVERY_MAP] ) >>
     simp[] ) >>
   qspecl_then[`NONE`,`rs`,`[d]`]mp_tac compile_decs_wrap_append_out >>
   qabbrev_tac`p  = compile_decs_wrap NONE rs [d]` >>
   PairCases_on`p`>> simp[] >>
   fs[FV_decs_def] >>
   qspecl_then[`d`,`p4`]mp_tac compile_print_dec_thm >>
   simp[] >> strip_tac >> simp[] >> strip_tac >>
   fs[between_labels_def,FILTER_APPEND,FILTER_REVERSE] >>
   `FILTER is_Label code = []` by (
     simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] ) >>
   simp[])

val labels_tac =
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,FILTER_REVERSE,good_labels_def,between_labels_def
                  ,MEM_FILTER,EVERY_MEM,between_def,MEM_MAP,is_Label_rwt] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC

val Cenv_bs_change_csz = store_thm("Cenv_bs_change_csz",
  ``∀rd menv s env rmenv renv rsz csz bs csz'.
     Cenv_bs rd menv s env rmenv renv rsz csz bs
     ∧ csz' ≤ LENGTH bs.stack
     ∧ (∀env x. env ∈ FRANGE rmenv ∧ MEM x env ⇒
         el_check x (REVERSE (DROP (LENGTH bs.stack - csz) bs.stack)) =
         el_check x (REVERSE (DROP (LENGTH bs.stack - csz') bs.stack)))
     ⇒
     Cenv_bs rd menv s env rmenv renv rsz csz' bs``,
  rw[Cenv_bs_def] >>
  fs[fmap_rel_def] >> rw[] >>
  first_x_assum(qspec_then`x`mp_tac) >>
  rw[] >>
  fs[env_renv_def,option_case_NONE_F] >>
  rfs[EVERY2_EVERY] >>
  fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  rw[] >>
  first_x_assum(qspecl_then[`rmenv ' x`,`EL n (rmenv ' x)`]mp_tac) >>
  discharge_hyps >- (
    simp[IN_FRANGE,MEM_EL] >>
    metis_tac[] ) >>
  rfs[EL_MAP] >> metis_tac[])

val env_rs_change_csz = store_thm("env_rs_change_csz",
  ``∀menv cenv env rs cz rd cs bs cz'.
     env_rs menv cenv env rs cz rd cs bs
     ∧ cz' ≤ LENGTH bs.stack
     ∧ (∀env x. env ∈ FRANGE (MAP SND o_f rs.rmenv) ∧ MEM x env ⇒
         el_check x (REVERSE (DROP (LENGTH bs.stack - cz) bs.stack)) =
         el_check x (REVERSE (DROP (LENGTH bs.stack - cz') bs.stack)))
     ⇒
     env_rs menv cenv env rs cz' rd cs bs``,
  rw[env_rs_def] >> fs[LET_THM] >>
  rpt HINT_EXISTS_TAC >>
  qexists_tac`Cs` >>
  simp[] >>
  match_mp_tac Cenv_bs_change_csz >>
  simp[] >> metis_tac[])

(*
val env_rs_add_empty_menv = store_thm("env_rs_add_empty_menv",
  ``∀menv cenv env rs cz rd cs bs mn.
     env_rs menv cenv env rs cz rd cs bs
     ∧ mn ∉ FDOM rs.rmenv
     ⇒
     env_rs menv cenv env (rs with rmenv := rs.rmenv |+ (mn,[])) cz rd cs bs``,
  rw[env_rs_def] >> fs[LET_THM] >>
  rpt HINT_EXISTS_TAC >>
  qexists_tac`Cs` >>
  simp[] >> rfs[] >> fs[] >>
  `cmnv = (MAP SND o_f rs.rmenv) |+ (mn,[])` by (
    qunabbrev_tac`cmnv` >>
    REWRITE_TAC[GSYM o_f_DOMSUB] >>
    metis_tac[FUPDATE_PURGE] ) >>
  conj_tac >- (
    fs[closed_vlabs_def] >>
    code_env_cd_def
    (* this looks hard ! *)
*)

val SND_pat_to_Cpat_ignore_mvars = store_thm("SND_pat_to_Cpat_ignore_mvars",
  ``(∀p m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ SND(pat_to_Cpat m' p) = SND(pat_to_Cpat m p)) ∧
    (∀ps m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ SND(pats_to_Cpats m' ps) = SND(pats_to_Cpats m ps))``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``) >>
  simp[ToIntLangTheory.pat_to_Cpat_def] >>
  simp[UNCURRY] >>
  rw[] >- metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST] >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[toIntLangProofsTheory.FST_pat_to_Cpat_bvars,FST] >>
  metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST])

val FST_pat_to_Cpat_ignore_mvars = store_thm("FST_pat_to_Cpat_ignore_mvars",
  ``(∀p m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ FST(pat_to_Cpat m' p) = FST(pat_to_Cpat m p) with mvars := m'.mvars) ∧
    (∀ps m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ FST(pats_to_Cpats m' ps) = FST(pats_to_Cpats m ps) with mvars := m'.mvars)``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``) >>
  simp[ToIntLangTheory.pat_to_Cpat_def] >>
  simp[UNCURRY] >>
  rw[ToIntLangTheory.exp_to_Cexp_state_component_equality])

val exp_to_Cexp_mvars_SUBMAP = store_thm("exp_to_Cexp_mvars_SUBMAP",
  ``(∀m exp m'.
      (∀mn x. Long mn x ∈ FV exp ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
      m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ∧ m.mvars ⊑  m'.mvars ⇒
            exp_to_Cexp m' exp = exp_to_Cexp m exp) ∧
    (∀m ds m'.
      (∀mn x. Long mn x ∈ FV_defs (set (MAP (Short o FST) ds)) ds ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
      m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ∧ m.mvars ⊑ m'.mvars ⇒
      defs_to_Cdefs m' ds = defs_to_Cdefs m ds) ∧
  (∀m pes m'.
    (∀mn x. Long mn x ∈ FV_pes pes ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
     m'.bvars = m.bvars ∧
     m'.cnmap = m.cnmap ∧
     m.mvars ⊑ m'.mvars ⇒
    pes_to_Cpes m' pes = pes_to_Cpes m pes) ∧
   (∀m es m'.
    (∀mn x. Long mn x ∈ FV_list es ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
     m'.bvars = m.bvars ∧
     m'.cnmap = m.cnmap ∧
     m.mvars ⊑ m'.mvars ⇒
     exps_to_Cexps m' es = exps_to_Cexps m es)``,
  ho_match_mp_tac exp_to_Cexp_ind >>
  simp[exp_to_Cexp_def] >>
  conj_tac >- (
    rw[] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac FLOOKUP_SUBMAP >> fs[] ) >>
  conj_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fsrw_tac[DNF_ss][FV_defs_MAP,EXISTS_PROD] >>
    fsrw_tac[DNF_ss][MEM_MAP] ) >>
  conj_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fsrw_tac[DNF_ss][FV_defs_MAP,EXISTS_PROD,MEM_MAP] >>
    metis_tac[] ) >>
  rw[] >>
  simp[UNCURRY] >>
  conj_tac >- metis_tac[SND_pat_to_Cpat_cnmap] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >>
  qabbrev_tac`x = pat_to_Cpat m p` >>
  PairCases_on`x`>>fs[]>>
  conj_tac >- (
    metis_tac[toIntLangProofsTheory.FST_pat_to_Cpat_bvars,FST] ) >>
  metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST] )

val v_to_Cv_mvars_SUBMAP = store_thm("v_to_Cv_mvars_SUBMAP",
  ``(∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ closed menv v ∧ mv = (MAP FST o_f alist_to_fmap menv) ∧ mv ⊑ mv' ⇒ v_to_Cv mv' m v = v_to_Cv mv m v) ∧
    (∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ EVERY (closed menv) v ∧ mv = (MAP FST o_f alist_to_fmap menv)∧ mv ⊑ mv' ⇒ vs_to_Cvs mv' m v = vs_to_Cvs mv m v) ∧
    (∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ EVERY (closed menv) (MAP SND v) ∧ mv = (MAP FST o_f alist_to_fmap menv)∧ mv ⊑ mv' ⇒ env_to_Cenv mv' m v = env_to_Cenv mv m v)``,
  ho_match_mp_tac v_to_Cv_ind >>
  simp[v_to_Cv_def] >>
  conj_tac >- (
    rw[] >> fs[] >- (
      first_x_assum match_mp_tac >>
      fs[Once closed_cases] ) >>
    AP_TERM_TAC >>
    match_mp_tac (CONJUNCT1 exp_to_Cexp_mvars_SUBMAP) >>
    simp[] >>
    fs[Once closed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,FLOOKUP_DEF] >>
    rw[] >>
    first_x_assum(qspec_then`Long mn x`mp_tac) >>
    simp[] >>
    strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    qexists_tac`y`>>simp[] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    qmatch_assum_rename_tac`mn = FST z`[] >>
    PairCases_on`z` >>
    pop_assum(qspecl_then[`z1`,`z0`]mp_tac) >>
    simp[] >> strip_tac >>
    imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
    fs[] ) >>
  rw[] >- (
    first_x_assum match_mp_tac >>
    fs[Once closed_cases] ) >>
  match_mp_tac (CONJUNCT1 (CONJUNCT2 exp_to_Cexp_mvars_SUBMAP)) >>
  simp[] >>
  fs[Once closed_cases] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,FLOOKUP_DEF] >>
  rw[] >>
  fsrw_tac[DNF_ss][FV_defs_MAP,UNCURRY] >>
  qmatch_assum_rename_tac`MEM d defs`[] >>
  PairCases_on`d`>>fs[] >>
  first_x_assum(qspecl_then[`d0`,`d1`,`d2`]mp_tac) >>
  simp[] >>
  disch_then(qspec_then`Long mn x`mp_tac) >>
  simp[] >>
  strip_tac >>
  HINT_EXISTS_TAC >> simp[] >>
  qmatch_assum_rename_tac`x = FST z`[] >>
  qexists_tac`z`>>simp[] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  qmatch_assum_rename_tac`mn = FST w`[] >>
  PairCases_on`w` >>
  pop_assum(qspecl_then[`w1`,`w0`]mp_tac) >>
  simp[] >> strip_tac >>
  imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  fs[] )

val env_renv_append_imp = store_thm("env_renv_append_imp",
  ``∀rd sz bs l1 l2 l3 l4. env_renv rd sz bs (l1 ++ l2) (l3 ++ l4) ∧ LENGTH l1 = LENGTH l3 ∧ LENGTH l2 = LENGTH l4 ⇒
    env_renv rd sz bs l1 l3 ∧ env_renv rd sz bs l2 l4``,
  rw[] >>
  fs[env_renv_def] >>
  metis_tac[EVERY2_APPEND])

val env_renv_syneq = store_thm("env_renv_syneq",
  ``∀rd sz bs l1 l2 l3.
    env_renv rd sz bs l2 l3 ∧ LIST_REL syneq l2 l1
    ⇒
    env_renv rd sz bs l1 l3``,
  rw[] >>
  fs[env_renv_def,option_case_NONE_F] >> rw[] >>
  fs[EVERY2_EVERY,EVERY_MEM] >> rfs[] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[] >>
  fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  rw[] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  first_x_assum(qspec_then`n`mp_tac) >>
  simp[] >> rw[] >> simp[] >>
  metis_tac[Cv_bv_syneq])

val vlabs_menv_FUPDATE = store_thm("vlabs_menv_FUPDATE",
  ``vlabs_menv (fm |+ kv) = vlabs_menv (fm \\ (FST kv)) ∪ vlabs_list (SND kv)``,
  simp[vlabs_menv_def] >>
  simp_tac(srw_ss()++DNF_ss)[Once EXTENSION,IN_FRANGE] >>
  Cases_on`kv` >>
  simp[DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM] >>
  metis_tac[])

val code_env_cd_SUBMAP = store_thm("code_env_cd_SUBMAP",
  ``code_env_cd menv code cd ∧ menv ⊑ menv' ⇒
    code_env_cd menv' code cd``,
  PairCases_on`cd` >>
  rw[code_env_cd_def] >>
  good_cd_def
  compile_mvars_SUBMAP

val env_rs_shift_to_menv = store_thm("env_rs_shift_to_menv",
  ``∀menv cenv env rs cz rd cs bs mn new old rnew rold rs' menv' cz'.
     env_rs menv cenv env rs cz rd cs bs
     ∧ closed_context menv cenv (SND cs) env
     ∧ mn ∉ FDOM rs.rmenv
     ∧ env = new ++ old
     ∧ rs.renv = rnew ++ rold
     ∧ LENGTH old = LENGTH rold
     ∧ rs' = rs with <| rmenv := rs.rmenv |+ (mn,rnew); renv := rold |>
     ∧ menv' = ((mn,new)::menv)
     ∧ cz' = LENGTH bs.stack
     ⇒
     env_rs menv' cenv old rs' cz' rd cs bs``,
  rw[env_rs_def] >> fs[LET_THM] >>
  fs[env_to_Cenv_MAP] >> rfs[] >>
  qmatch_assum_abbrev_tac`LIST_REL syneq (MAP (v_to_Cv mv0 m) (SND cs)) Cs` >>
  `mv0 ⊑ mv` by (
    simp[Abbr`mv0`,Abbr`mv`,Abbr`fmv`] >>
    qpat_assum`x = MAP FST o_f y`(assume_tac o SYM) >>
    simp[] >>
    simp[SUBMAP_DEF] >>
    ntac 2 strip_tac >>
    simp[FAPPLY_FUPDATE_THM] >>
    `x ∈ FDOM rs.rmenv` by (
      fs[GSYM fmap_EQ] ) >>
    rw[]>>fs[] >>
    simp[DOMSUB_FAPPLY_THM] ) >>
  `vs_to_Cvs mv m (SND cs) = vs_to_Cvs mv0 m (SND cs)` by (
    match_mp_tac (CONJUNCT1 (CONJUNCT2 v_to_Cv_mvars_SUBMAP)) >>
    qexists_tac`menv` >> simp[] >>
    fs[closed_context_def] ) >>
  fs[vs_to_Cvs_MAP] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  `MAP FST rnew = MAP FST new ∧ MAP FST rold = MAP FST old` by (
    metis_tac[APPEND_LENGTH_EQ,LENGTH_MAP,APPEND_11_LENGTH] ) >>
  qexists_tac`Cs` >> simp[] >>
  qmatch_assum_abbrev_tac`EVERY2 syneq (l1 ++ l2) Cenv` >>
  `Cenv = TAKE (LENGTH new) Cenv ++ DROP (LENGTH new) Cenv` by metis_tac[TAKE_DROP] >>
  qmatch_assum_abbrev_tac`Cenv = l3 ++ l4` >>
  qexists_tac`l4` >>
  `LENGTH l1 = LENGTH l3 ∧ LENGTH l2 = LENGTH l4` by (
    qpat_assum`Cenv = X`(assume_tac o SYM) >>
    fs[EVERY2_EVERY] >>
    `LENGTH new ≤ LENGTH Cenv`  by (
      fsrw_tac[ARITH_ss][Abbr`l1`] ) >>
    simp[Abbr`l1`,Abbr`l3`] >>
    `LENGTH old ≤ LENGTH Cenv`  by (
      fsrw_tac[ARITH_ss][Abbr`l2`] ) >>
    qpat_assum`LENGTH old = X`(assume_tac o SYM) >>
    simp[Abbr`l2`,Abbr`l4`] >> fs[] >> simp[]) >>
  `LIST_REL syneq l1 l3 ∧ LIST_REL syneq l2 l4` by (
    metis_tac[EVERY2_APPEND] ) >>
  `Cenv0 = l2` by  (
    simp[Abbr`l2`,Abbr`Cenv0`,GSYM MAP_MAP_o,GSYM vs_to_Cvs_MAP] >>
    match_mp_tac (CONJUNCT1 (CONJUNCT2 v_to_Cv_mvars_SUBMAP)) >>
    qexists_tac`menv` >>
    fs[closed_context_def] ) >>
  simp[] >>
  qexists_tac`Cmenv |+ (mn,TAKE (LENGTH new) Cenv)`>>simp[] >>
  `env_to_Cenv mv m new = env_to_Cenv mv0 m new` by (
    match_mp_tac (CONJUNCT2 (CONJUNCT2 v_to_Cv_mvars_SUBMAP)) >>
    qexists_tac`menv` >>
    fs[closed_context_def] ) >>
  conj_asm1_tac >-(
    fs[fmap_rel_def,Abbr`Cmenv0`,Abbr`fmv`] >>
    qx_gen_tac`x` >>
    Cases_on`x=mn`>>simp[FAPPLY_FUPDATE_THM]>-(
      simp[env_to_Cenv_MAP])>>
    strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >>
    Q.PAT_ABBREV_TAC`ee = alist_to_fmap menv ' x` >>
    `env_to_Cenv mv m ee = env_to_Cenv mv0 m ee` by (
      match_mp_tac (CONJUNCT2 (CONJUNCT2 v_to_Cv_mvars_SUBMAP)) >>
      qexists_tac`menv` >>
      fs[closed_context_def] >>
      fs[Abbr`ee`,EVERY_MEM] >>
      first_x_assum match_mp_tac >>
      simp[MEM_MAP,EXISTS_PROD] >>
      qexists_tac`x` >>
      match_mp_tac alist_to_fmap_FAPPLY_MEM >>
      simp[]) >>
    simp[] ) >>
  conj_tac >- (
    fs[closed_Clocs_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >>
    fs[IN_FRANGE,DOMSUB_FAPPLY_THM] >>
    rfs[] >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    fs[closed_vlabs_def] >>
    conj_tac >- (
      simp[all_vlabs_menv_def,IN_FRANGE,GSYM LEFT_FORALL_IMP_THM] >>
      fs[all_vlabs_menv_def] >>
      qx_gen_tac`k` >>
      Cases_on`k=mn`>>simp[FAPPLY_FUPDATE_THM] >>
      metis_tac[IN_FRANGE] ) >>
    fs[vlabs_list_APPEND] >>
    simp[vlabs_menv_FUPDATE] >>
    `Cmenv \\ mn = Cmenv` by (
      match_mp_tac DOMSUB_NOT_IN_DOM >>
      fs[fmap_rel_def] >>
      fs[GSYM fmap_EQ,Abbr`mv0`] ) >>
    simp[] >>

    qsuff_tac`∀cd. code_env_cd (MAP SND o_f rs.rmenv) bs.code cd ⇒
                   code_env_cd cmnv bs.code cd`>-metis_tac[] >>
    simp[Abbr`cmnv`] >>
    REWRITE_TAC[Once (GSYM o_f_DOMSUB)] >>
    REWRITE_TAC[GSYM FUPDATE_PURGE] >>

    cheat ) >>
  conj_tac >- (
    simp[Abbr`mv`,Abbr`fmv`] >>
    simp[Abbr`mv0`] >>
    ONCE_REWRITE_TAC[GSYM o_f_DOMSUB] >>
    qpat_assum`X = Y o_f Z` SUBST1_TAC >>
    rw[] ) >>
  conj_tac >- (
    simp[SUM_IMAGE_THM] >>
    qmatch_abbrev_tac`LENGTH rnew + (b + c:num) ≤ d` >>
    qmatch_abbrev_tac`a + (b + c) ≤ d` >>
    qmatch_assum_abbrev_tac`a + b + e ≤ d` >>
    qsuff_tac `c ≤ e` >- DECIDE_TAC >>
    simp[Abbr`c`,Abbr`e`] >>
    match_mp_tac SUM_IMAGE_SUBSET_LE >>
    simp[] >>
    simp[SUBSET_DEF] >>
    metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_DEF] ) >>
  rator_x_assum`Cenv_bs`mp_tac >>
  simp[Cenv_bs_def] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`env_renv rd sz bs (l3 ++ l4) (l5 ++ l6)` >>
  qspecl_then[`rd`,`sz`,`bs`,`l3`,`l4`,`l5`,`l6`]mp_tac env_renv_append_imp >>
  discharge_hyps >- (
    simp[Abbr`l5`,Abbr`l6`] >>
    qpat_assum`Cenv = X`(assume_tac o SYM) >>
    fs[EVERY2_EVERY] >>
    `LENGTH new ≤ LENGTH Cenv`  by (
      fsrw_tac[ARITH_ss][Abbr`l1`] ) >>
    simp[Abbr`l1`,Abbr`l3`] >>
    `LENGTH old ≤ LENGTH Cenv`  by (
      fsrw_tac[ARITH_ss][Abbr`l2`] ) >>
    qpat_assum`LENGTH old = X`(assume_tac o SYM) >>
    simp[Abbr`l2`,Abbr`l4`] >> fs[] >> simp[] >>
    fs[LIST_EQ_REWRITE] ) >>
  simp[] >> strip_tac >>
  rator_x_assum`fmap_rel`mp_tac >>
  simp[fmap_rel_def] >> strip_tac >>
  conj_asm1_tac >- (
    simp[Abbr`cmnv`,Abbr`Cmenv0`,Abbr`fmv`] >>
    fs[fmap_rel_def] >>
    simp[EXTENSION] >>
    metis_tac[] ) >>
  gen_tac >> Cases_on`x=mn` >> simp[] >- (
    simp[FAPPLY_FUPDATE_THM] >>
    simp[Abbr`cmnv`,MAP_MAP_o] >>
    simp[env_to_Cenv_MAP] >>
    match_mp_tac env_renv_syneq >>
    qexists_tac`l3` >>
    reverse conj_tac >- (
      match_mp_tac EVERY2_syneq_sym_all_vlabs >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      fs[closed_vlabs_def,EVERY_MEM] >>
      fs[all_vlabs_menv_def,env_to_Cenv_MAP,EVERY_MEM] >>
      metis_tac[MEM_EL] ) >>
    match_mp_tac env_renv_shift >>
    map_every qexists_tac[`sz`,`bs`,`l5`] >>
    simp[] >>
    simp[bc_state_component_equality] >>
    simp[Abbr`l5`,GSYM MAP_MAP_o] >>
    ntac 2 (qexists_tac`MAP SND rnew`) >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP,EL_REVERSE,PRE_SUB1] ) >>
  strip_tac >>
  simp[FAPPLY_FUPDATE_THM] >>
  simp[Abbr`cmnv`,FAPPLY_FUPDATE_THM] >>
  REWRITE_TAC[GSYM o_f_DOMSUB] >>
  simp[DOMSUB_FAPPLY_THM] >>
  first_x_assum(qspec_then`x`mp_tac) >>
  rfs[] >>
  strip_tac >>
  match_mp_tac env_renv_shift >>
  qexists_tac`0` >>
  qmatch_assum_abbrev_tac`env_renv rd 0 bss xx yy` >>
  map_every qexists_tac[`bss`,`yy`] >>
  simp[Abbr`bss`,bc_state_component_equality] >>
  simp[Abbr`yy`] >>
  ntac 2 (qexists_tac`MAP SND (rs.rmenv ' x)`) >>
  simp[] >>
  simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP,EL_REVERSE,PRE_SUB1] >>
  simp[EL_DROP])

val closed_context_append = store_thm("closed_context_append",
  ``∀menv cenv s env cenv' env'.
    closed_context menv cenv s env  ∧
    EVERY (closed menv) (MAP SND env') ∧
    (∀v. MEM v (MAP SND env') ⇒ all_cns v ⊆ cenv_dom (cenv' ++ cenv)) ∧
    (∀v. MEM v (MAP SND env') ⇒ all_locs v ⊆ count (LENGTH s))
    ⇒
    closed_context menv (cenv' ++ cenv) s (env' ++ env)``,
  rpt gen_tac >>
  simp[closed_context_def] >> strip_tac >>
  fs[closed_under_cenv_def,closed_under_menv_def] >>
  conj_tac >- (
    `cenv_dom cenv ⊆ cenv_dom (cenv' ++ cenv)` by (
      fsrw_tac[DNF_ss][SUBSET_DEF, cenv_dom_def] ) >>
    metis_tac[SUBSET_TRANS] ) >>
  metis_tac[])

val closed_context_extend_cenv = store_thm("closed_context_extend_cenv",
  ``∀menv cenv s env cenv'.
      closed_context menv cenv s env ⇒
      closed_context menv (cenv'++cenv) s env``,
  rw[closed_context_def] >> fs[] >>
  fs[toIntLangProofsTheory.closed_under_cenv_def] >>
  fsrw_tac[DNF_ss][cenv_dom_def, SUBSET_DEF] >>
  metis_tac[]);

val compile_top_thm = store_thm("compile_top_thm",
  ``∀menv cenv s env top res. evaluate_top menv cenv s env top res ⇒
      closed_top menv cenv s env top
      ∧ (∀mn spec ds. top = Tmod mn spec ds ⇒
           ∀i ts. i < LENGTH ds ∧ EL i ds = Dtype ts ⇒ check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv) ts)
      ⇒
     ∀rs. ∃ck. ∀rss rsf rd bc bs bc0.
      env_rs menv cenv env rs (LENGTH bs.stack) rd (ck,s) (bs with code := bc0) ∧
      (compile_top rs top = (rss,rsf,bc)) ∧
      (bs.code = bc0 ++ REVERSE bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      IS_SOME bs.clock ∧
      good_labels rs.rnext_label bc0
      ⇒
      case res of (s',cenv',Rval(menv',env')) =>
        ∃bs' rd'.
        bc_next^* bs bs' ∧
        bs'.pc = next_addr bs'.inst_length (bc0 ++ bc) ∧
        bs'.output = bs.output ++ (print_result top cenv' (Rval(menv',env'))) ∧
        env_rs (menv'++menv) (cenv'++cenv) (env'++env) rss (LENGTH bs'.stack) rd' (0,s') bs'
      | (s',cenv',Rerr(Rraise err)) =>
        ∃bv bs' rd'.
        let menv' = case top of Tmod mn _ _ => (mn,[])::menv | _ => menv in
        bc_next^*bs bs' ∧
        bs'.stack = bv::bs.stack ∧
        bs'.pc = 0 ∧
        bs'.output = bs.output ∧
        err_bv err bv ∧
        env_rs menv' (top_to_cenv top++cenv) env rsf (LENGTH bs.stack) rd' (0,s') (bs' with stack := bs.stack)
      | (s',_) => T``,
  PURE_REWRITE_TAC[closed_top_def] >>
  ho_match_mp_tac evaluate_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    gen_tac >>
    fs[evaluate_dec_decs] >>
    qspecl_then[`NONE`,`menv`,`cenv`,`s`,`env`,`[d]`,`s2,new_tds,Rval new_env`]mp_tac compile_decs_wrap_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[FV_decs_def,decs_cns_def,decs_to_cenv_def] >>
      rw[] >> fs[Once evaluate_decs_cases] >>
      fs[Once evaluate_dec_cases] ) >>
    disch_then(qspec_then`rs`strip_assume_tac) >>
    qexists_tac`ck` >> rpt gen_tac >> strip_tac >>
    rfs[compile_top_def,LET_THM] >>
    qspecl_then[`d`,`cs`]mp_tac compile_print_dec_thm >>
    simp[] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    rw[] >> fs[] >>
    first_x_assum(qspecl_then[`rd`,`bs with code := bc0 ++ REVERSE cs.out`,`bc0`]mp_tac) >>
    simp[LibTheory.emp_def] >>
    disch_then(qx_choosel_then[`bvs`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    first_x_assum(qspecl_then[`bs2 with code := bs.code`,`bc0++REVERSE cs.out`,`bvs`]mp_tac) >>
    simp[Abbr`bs2`] >>
    discharge_hyps >- (
      imp_res_tac evaluate_decs_new_decs_vs >> fs[] >>
      fs[env_rs_def,LET_THM] >>
      fs[Cenv_bs_def] >> rfs[] >>
      fs[LIST_EQ_REWRITE] ) >>
    simp[print_result_def] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
    `bc_next^* bs bs2` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2'`] >>
      simp[Abbr`bs1`,Abbr`bs2'`,Abbr`bs2`,bc_state_component_equality] ) >>
    qexists_tac`bs3` >>
    qexists_tac`rd'` >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    conj_tac >- (
      simp[Abbr`bs3`,SUM_APPEND,FILTER_APPEND,FILTER_REVERSE,MAP_REVERSE,SUM_REVERSE] ) >>
    reverse conj_asm2_tac >- (
      match_mp_tac env_rs_append_code >>
      qexists_tac`bs3 with code := bs2'.code` >>
      simp[Abbr`bs3`,Abbr`bs2'`,bc_state_component_equality] >>
      reverse conj_tac >- (
        qspecl_then[`NONE`,`rs`,`[d]`]mp_tac compile_decs_wrap_append_out >>
        simp[] >>
        discharge_hyps >- (
          fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP] >>
          rw[] >> res_tac >> fs[MEM_FLAT,MEM_MAP] >> rw[] >> fs[MEM_MAP] >>
          fs[env_rs_def,LET_THM] >> metis_tac[MEM_MAP] ) >>
        strip_tac >>
        `FILTER is_Label c2 = []` by (
          simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] ) >>
        labels_tac ) >>
      qmatch_assum_abbrev_tac`env_rs menv cenvx envx rsx zx rd' cx bsx` >>
      qmatch_abbrev_tac`env_rs menv cenvx envx rsx yx rd' cx bsy` >>
      match_mp_tac env_rs_change_csz >>
      qexists_tac`zx` >>
      reverse conj_tac >- (
        conj_tac >- (
          unabbrev_all_tac >> simp[] ) >>
        simp[Abbr`bsy`] >>
        simp[Abbr`rsx`] >>
        simp[Abbr`zx`,Abbr`yx`,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
        simp[IN_FRANGE,GSYM AND_IMP_INTRO,GSYM LEFT_FORALL_IMP_THM] >>
        rator_x_assum`env_rs`mp_tac >>
        simp[env_rs_def] >> strip_tac >>
        rator_x_assum`Cenv_bs`mp_tac >>
        simp[Cenv_bs_def] >> strip_tac >>
        rator_x_assum`fmap_rel`mp_tac >>
        simp[fmap_rel_def] >> strip_tac >>
        rpt gen_tac >> strip_tac >>
        first_x_assum(qspec_then`k`mp_tac) >>
        simp[] >>
        simp[env_renv_def,option_case_NONE_F,MAP_MAP_o] >>
        strip_tac >> simp[MEM_EL] >> strip_tac >>
        rator_x_assum`EVERY2`mp_tac >>
        simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
        strip_tac >>
        disch_then(qspec_then`n`mp_tac) >>
        simp[] >> simp[EL_MAP] >>
        simp[Abbr`bsx`,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
        strip_tac >>
        fs[CompilerLibTheory.el_check_def] >>
        simp[REVERSE_APPEND,EL_APPEND1] ) >>
      match_mp_tac env_rs_with_bs_irr >>
      HINT_EXISTS_TAC >>
      simp[Abbr`bsx`,Abbr`bsy`] ) >>
    simp[Abbr`bs3`] >>
    last_x_assum mp_tac >>
    simp[Once evaluate_decs_cases] >>
    simp[Once evaluate_decs_cases] >>
    simp[LibTheory.emp_def,LibTheory.merge_def,SemanticPrimitivesTheory.combine_dec_result_def] >>
    strip_tac >>
    imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
    rator_x_assum`evaluate_dec`mp_tac >>
    reverse(Cases_on`d`)>>simp[Once evaluate_dec_cases,LibTheory.emp_def] >> rw[]
      >- simp[print_envE_def] >> (
    qmatch_assum_abbrev_tac`MAP FST new_env = new_dec_vs d` >>
    simp[print_envC_def] >>
    match_mp_tac print_bv_list_print_envE >>
    fs[new_dec_vs_def,Abbr`d`] >>
    rator_x_assum`env_rs`mp_tac >>
    simp[env_rs_def] >>
    strip_tac >>
    fs[env_to_Cenv_MAP] >>
    qmatch_assum_abbrev_tac`EVERY2 syneq (MAP (v_to_Cv mv cm) s2) Cs` >>
    qmatch_assum_abbrev_tac`EVERY2 syneq (MAP vtc new_env ++ MAP vtc env) Cenv` >>
    map_every qexists_tac[`mv`,`mk_pp rd' bs2`,`MAP SND new_env`,`cm`,`TAKE (LENGTH new_env) Cenv`] >>
    simp[CONJ_ASSOC] >>
    reverse conj_asm2_tac >- (
      match_mp_tac LIST_EQ_MAP_PAIR >>
      simp[MAP_ZIP] >>
      TRY(qunabbrev_tac`new_env`) >>
      simp[MAP_ZIP,build_rec_env_dom] >>
      simp[MAP_ZIP,build_rec_env_MAP] >>
      imp_res_tac pmatch_dom >> fs[] >>
      metis_tac[MAP_ZIP,LIST_EQ_REWRITE,LENGTH_MAP]) >>
    reverse conj_tac >- (
      TRY(qunabbrev_tac`new_env`) >>
      simp[build_rec_env_MAP] >>
      imp_res_tac pmatch_dom >> fs[] >>
      fs[LIST_EQ_REWRITE] ) >>
    conj_tac >- (
      simp[MAP_MAP_o] >>
      qmatch_assum_abbrev_tac`EVERY2 R (l1 ++ l2) Cenv` >>
      `Cenv = (TAKE (LENGTH new_env) Cenv) ++ DROP (LENGTH new_env) Cenv` by metis_tac[TAKE_DROP] >>
      qmatch_assum_abbrev_tac`Cenv = l3 ++ l4` >>
      `LENGTH l1 = LENGTH l3 ∧ LENGTH l2 = LENGTH l4` by (
        unabbrev_all_tac >> simp[] >>
        fs[EVERY2_EVERY] >> simp[] ) >>
      metis_tac[EVERY2_APPEND] ) >>
    rator_x_assum`Cenv_bs`mp_tac >>
    simp[Cenv_bs_def,env_renv_def,option_case_NONE_F] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`EVERY2 R Cenv (l1 ++ l2)` >>
    `Cenv = (TAKE (LENGTH new_env) Cenv) ++ DROP (LENGTH new_env) Cenv` by metis_tac[TAKE_DROP] >>
    qmatch_assum_abbrev_tac`Cenv = l3 ++ l4` >>
    `LENGTH l1 = LENGTH l3 ∧ LENGTH l2 = LENGTH l4` by (
      unabbrev_all_tac >> simp[] >>
      fs[EVERY2_EVERY] >> simp[] >>
      fs[LIST_EQ_REWRITE] >> rfs[] >> fs[] >>
      fs[LET_THM,env_rs_def,LIST_EQ_REWRITE] >>
      fsrw_tac[ARITH_ss][]) >>
    `LIST_REL R l3 l1` by metis_tac[EVERY2_APPEND] >>
    pop_assum mp_tac >>
    `LENGTH l3 = LENGTH bvs` by (
      fs[Abbr`bs2'`] >>
      qpat_assum`x + y = LENGTH bvs + z`mp_tac >>
      fs[env_rs_def,LET_THM] >>
      simp[Abbr`l3`] >>
      metis_tac[LENGTH_MAP] ) >>
    simp[Abbr`R`,Abbr`l1`,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    rpt strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >>
    `LENGTH renv = LENGTH bvs` by metis_tac[LENGTH_MAP] >>
    simp[EL_MAP] >>
    qmatch_assum_abbrev_tac`compile_decs_wrap mn rs ds = X` >>
    qspecl_then[`mn`,`rs`,`ds`]mp_tac compile_decs_wrap_append_out >>
    simp[Abbr`X`] >>
    discharge_hyps >- (
      last_x_assum mp_tac >>
      last_x_assum mp_tac >>
      fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP,Abbr`ds`] >>
      rw[] >> res_tac >> fs[MEM_FLAT,MEM_MAP] >> rw[] >> fs[MEM_MAP] >>
      fs[env_rs_def,LET_THM] >> metis_tac[MEM_MAP] ) >>
    strip_tac >>
    `SND (EL n renv) = EL n (MAP SND renv)` by ( simp[EL_MAP] ) >>
    pop_assum SUBST1_TAC >>
    simp[EL_REVERSE,CompilerLibTheory.el_check_def,PRE_SUB1,EL_APPEND1] >>
    `rs.rsz = LENGTH bs.stack` by fs[env_rs_def,LET_THM] >>
    simp[] >>
    simp[Abbr`bs2`] )) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    strip_tac >> gen_tac >>
    Cases_on`err=Rtype_error`>>simp[] >>
    imp_res_tac evaluate_dec_err_cenv_emp >>
    fs[evaluate_dec_decs] >>
    qspecl_then[`NONE`,`menv`,`cenv`,`s`,`env`,`[d]`,`s2,[],Rerr err`]mp_tac compile_decs_wrap_thm >>
    simp[] >>
    discharge_hyps >- (
      simp[FV_decs_def,decs_cns_def,decs_to_cenv_def] >>
      rw[] >> fs[Once evaluate_decs_cases] >>
      fs[Once evaluate_dec_cases] ) >>
    disch_then(qspec_then`rs`strip_assume_tac) >>
    qexists_tac`ck` >> rpt gen_tac >> strip_tac >>
    rfs[compile_top_def,LET_THM] >>
    qspecl_then[`d`,`cs`]mp_tac compile_print_dec_thm >>
    simp[] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    rw[] >> fs[] >>
    first_x_assum(qspecl_then[`rd`,`bs with code := bc0 ++ REVERSE cs.out`,`bc0`]mp_tac) >>
    simp[LibTheory.emp_def] >>
    Cases_on`err`>>simp[]>>
    disch_then(qx_choosel_then[`bv`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_next^* bs (bs2 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2`] >>
      simp[Abbr`bs1`,bc_state_component_equality,Abbr`bs2`] ) >>
    map_every qexists_tac[`bv`,`bs2 with code := bs.code`,`rd'`] >>
    simp[Abbr`bs2`] >>
    simp[top_to_cenv_def] >>
    rfs[decs_to_cenv_def] >>
    match_mp_tac env_rs_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] >>
    `FILTER is_Label c2 = []` by (
      fsrw_tac[DNF_ss][FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] ) >>
    qspecl_then[`NONE`,`rs`,`[d]`]mp_tac compile_decs_wrap_append_out >>
    simp[] >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP] >>
      rw[] >> res_tac >> fs[MEM_FLAT,MEM_MAP] >> rw[] >> fs[MEM_MAP] >>
      fs[env_rs_def,LET_THM] >> metis_tac[MEM_MAP] ) >>
    strip_tac >>
    labels_tac ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    strip_tac >> gen_tac >>
    qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`s2,new_tds,Rval new_env`]mp_tac compile_decs_wrap_thm >>
    simp[] >>
    disch_then(qspec_then`rs`strip_assume_tac) >>
    qexists_tac`ck` >> rpt gen_tac >> strip_tac >>
    rfs[compile_top_def,LET_THM] >>
    rw[] >> fs[FOLDL_emit_thm] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ REVERSE cs.out ++ ppc1 ++ ppc2` >>
    first_x_assum(qspecl_then[`rd`,`bs with code := bc0 ++ REVERSE cs.out`,`bc0`]mp_tac) >>
    simp[LibTheory.emp_def] >>
    disch_then(qx_choosel_then[`bvs`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_next^* bs (bs2 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2`] >>
      simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs3` >>
    `bc_next^* bs3 (bs3 with <| pc := next_addr bs.inst_length bs.code; output := STRCAT bs.output ("structure "++mn++" = <structure>") |>)` by (
      match_mp_tac MAP_PrintC_thm >>
      simp[Abbr`bs3`] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc0++REVERSE cs.out` >>
      simp[Abbr`ppc1`,Abbr`ppc2`] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`[]` >>
      simp[] >>
      simp[Abbr`bs2`,bc_state_component_equality] >>
      simp[Once SWAP_REVERSE,IMPLODE_EXPLODE_I] >>
      rpt AP_TERM_TAC  >>
      simp[] ) >>
    qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
    qexists_tac`bs4` >>
    qexists_tac`rd'` >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    conj_tac >- (
      simp[Abbr`bs4`,Abbr`ppc1`,Abbr`ppc2`,Abbr`bs3`,Abbr`bs2`] >>
      REWRITE_TAC[FILTER_APPEND,SUM_APPEND,IMPLODE_EXPLODE_I,REVERSE_APPEND,FILTER_REVERSE,MAP_APPEND,MAP_REVERSE,SUM_REVERSE] >>
      EVAL_TAC >>
      simp[] ) >>
    reverse conj_asm2_tac >- (
      match_mp_tac env_rs_append_code >>
      qexists_tac`bs4 with code := bs2.code` >>
      simp[Abbr`bs4`,Abbr`bs2`,Abbr`bs3`,bc_state_component_equality] >>
      reverse conj_tac >- (
        qspecl_then[`SOME mn`,`rs`,`ds`]mp_tac compile_decs_wrap_append_out >>
        simp[] >>
        discharge_hyps >- (
          fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP] >>
          rw[] >> res_tac >> fs[MEM_FLAT,MEM_MAP] >> rw[] >> fs[MEM_MAP] >>
          fs[env_rs_def,LET_THM] >> metis_tac[MEM_MAP] ) >>
        strip_tac >>
        `FILTER is_Label ppc1 = [] ∧ FILTER is_Label ppc2 = []` by (
          simp[FILTER_EQ_NIL,Abbr`ppc1`,Abbr`ppc2`] >> fs[EVERY_MEM,MEM_MAP,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] ) >>
        labels_tac ) >>
      ntac 2 (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd x y` >>
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs0 with <|output := bs.output; pc := next_addr bs.inst_length (bc0 ++ REVERSE cs.out)|>` >>
      simp[Abbr`bs0`] >>
      match_mp_tac env_rs_shift_to_menv >>
      simp[] >>
      rator_x_assum`env_rs`mp_tac >>
      Q.PAT_ABBREV_TAC`rs1 = compiler_state_contab_fupd x y` >>
      strip_tac >>
      qexists_tac`rs1` >>
      qexists_tac`LENGTH bs.stack` >>
      qexists_tac`renv` >>
      simp[Abbr`rs1`,compiler_state_component_equality] >>
      reverse conj_tac >- (
        fs[env_rs_def,LET_THM,LIST_EQ_REWRITE] >>
        fs[GSYM fmap_EQ] >>
        qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`s2,new_tds,Rval new_env`]mp_tac evaluate_decs_closed_context >>
        simp[]) >>
      match_mp_tac env_rs_with_bs_irr >>
      HINT_EXISTS_TAC >>
      simp[] ) >>
    simp[print_result_def,Abbr`bs4`]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> ntac 2 strip_tac >> gen_tac >>
    qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`s2,new_tds,Rerr err`]mp_tac compile_decs_wrap_thm >>
    simp[] >>
    disch_then(qspec_then`rs`strip_assume_tac) >>
    qexists_tac`ck` >> rpt gen_tac >> strip_tac >>
    Cases_on`err`>>fs[]>>
    rfs[compile_top_def,LET_THM] >>
    rw[] >> fs[FOLDL_emit_thm] >>
    first_x_assum(qspecl_then[`rd`,`bs with code := bc0 ++ REVERSE cs.out`,`bc0`]mp_tac) >>
    simp[LibTheory.emp_def] >>
    disch_then(qx_choosel_then[`bv`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_next^* bs (bs2 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2`] >>
      simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
    map_every qexists_tac[`bv`,`bs2 with code := bs.code`,`rd'`] >>
    simp[Abbr`bs2`] >>
    match_mp_tac env_rs_append_code >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd x y` >>
    qexists_tac`bs0 with code := bc0 ++ REVERSE cs.out` >>
    simp[Abbr`bs0`,bc_state_component_equality] >>
    reverse conj_tac >- (
      REWRITE_TAC[FILTER_APPEND] >>
      EVAL_TAC >>
      REWRITE_TAC[FILTER_MAP,IMPLODE_EXPLODE_I] >>
      Q.PAT_ABBREV_TAC`l1 = MAP PrintC ls` >>
      `l1 = []` by (
        simp[MAP_EQ_NIL,Abbr`l1`,FILTER_EQ_NIL] ) >>
      simp[REV_REVERSE_LEM,FILTER_REVERSE] >>
      simp[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] >>
      qspecl_then[`SOME mn`,`rs`,`ds`]mp_tac compile_decs_wrap_append_out >>
      simp[] >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP] >>
        rw[] >> res_tac >> fs[MEM_FLAT,MEM_MAP] >> rw[] >> fs[MEM_MAP] >>
        fs[env_rs_def,LET_THM] >> metis_tac[MEM_MAP] ) >>
      strip_tac >>
      fs[between_labels_def,good_labels_def] >>
      simp[MEM_FILTER,is_Label_rwt] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[top_to_cenv_def] >>
    match_mp_tac env_rs_shift_to_menv >>
    qmatch_assum_abbrev_tac`env_rs menv cenx env rsx zx rd' csx bsx` >>
    map_every qexists_tac[`menv`,`env`,`rsx`,`zx`,`mn`,`[]`,`[]`] >>
    simp[Abbr`rsx`,compiler_state_component_equality,Abbr`zx`,Abbr`bsx`] >>
    reverse conj_tac >- (
      fs[env_rs_def,LET_THM,LIST_EQ_REWRITE,GSYM fmap_EQ,EXTENSION] >>
      metis_tac[]) >>
    simp[Abbr`csx`] >>
    imp_res_tac evaluate_decs_closed_context >>
    fs[Abbr`cenx`,LET_THM] >>
    imp_res_tac evaluate_decs_to_cenv >>
    simp[] >>
    metis_tac[closed_context_extend_cenv,APPEND_ASSOC] ) >>
  simp[])

val compile_dec_divergence = store_thm("compile_dec_divergence",
  ``∀mn menv cenv s env d rs csz rd ck bs bc0 m cs vso cs' code. (∀r. ¬evaluate_dec mn menv cenv s env d r) ∧
      closed_context menv cenv s env ∧
      FV_dec d ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
      dec_cns d ⊆ cenv_dom cenv ∧
      env_rs menv cenv env rs csz rd (ck,s) (bs with code := bc0)
      ∧ m.bvars = MAP FST env
      ∧ m.mvars = MAP FST o_f alist_to_fmap menv
      ∧ m.cnmap = cmap rs.contab
      ∧ rs.rnext_label = cs.next_label ∧
      (compile_dec (MAP SND o_f rs.rmenv) m (MAP (CTDec o SND) rs.renv) rs.rsz cs d = (vso,cs')) ∧
      (cs'.out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      IS_SOME bs.clock ∧
      good_labels rs.rnext_label bc0
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0``,
    rw[closed_context_def,good_labels_def] >>
    Cases_on`∃ts. d = Dtype ts` >- (
      rw[] >> fs[Once evaluate_dec_cases,FORALL_PROD] >>
      metis_tac[] ) >>
    Cases_on`d`>>fs[]>>rw[]>>fs[Once evaluate_dec_cases,FORALL_PROD] >- (
      Cases_on`ALL_DISTINCT (pat_bindings p [])`>>fs[] >>
      Cases_on`∃r. evaluate F menv cenv (0,s) env e r` >> fs[] >- (
        PairCases_on`r` >>
        Cases_on`r2`>>fs[] >- (
          Cases_on`pmatch cenv r1 p a emp`>>fs[] >>
          metis_tac[] ) >>
        metis_tac[] ) >>
      fs[big_clocked_unclocked_equiv_timeout] >>
      fs[compile_dec_def,LET_THM] >>
      pop_assum(qspec_then`ck`strip_assume_tac) >>
      qabbrev_tac`vars = pat_bindings p[]` >>
      qabbrev_tac`exp = Con NONE (MAP (Var o Short) (REVERSE vars))` >>
      `evaluate T menv cenv(ck,s) env (Mat e [(p,exp)]) ((0,s'),Rerr Rtimeout_error)` by (
        rw[Once evaluate_cases] >> disj2_tac >> rw[] ) >>
      qabbrev_tac`rmenv = (MAP SND o_f rs.rmenv)` >>
      qabbrev_tac`renv = (MAP (CTDec o SND) rs.renv)` >>
      qspecl_then[`rmenv`,`m`,`renv`,`rs.rsz`,`cs`,`vars`,`λb. Mat e [(p,b)]`]mp_tac compile_fake_exp_thm >>
      simp[] >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >>
        conj_tac >- (
          rw[] >> res_tac >> fs[Abbr`exp`,FV_list_MAP,MEM_MAP] >> rw[] >> fs[] >> metis_tac[] ) >>
        simp[Abbr`renv`] >>
        fs[env_rs_def,LET_THM,LIST_EQ_REWRITE] ) >>
      strip_tac >>
      first_x_assum(qspecl_then[`menv`,`cenv`,`env`,`ck,s`,`0,s'`,`Rerr Rtimeout_error`]mp_tac) >>
      simp[] >>
      disch_then(qspecl_then[`rs`,`csz`,`rd`,`bs`,`bc0`]mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        qunabbrev_tac`vars` >>
        fs[markerTheory.Abbrev_def,FV_list_MAP] >>
        fsrw_tac[DNF_ss][cenv_dom_def, SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD,all_cns_list_MAP] >>
        fs[good_labels_def] >> rfs[]) >>
      metis_tac[] ) >>
    Cases_on`ALL_DISTINCT (MAP (λ(x,y,z). x) l)`>>fs[])

val evaluate_decs_divergence_take = store_thm("evaluate_decs_divergence_take",
  ``∀ds mn menv cenv s env.
    (∀res. ¬ evaluate_decs mn menv cenv s env ds res)
    ⇒
    ∃n s' cenv' env'.
    n < LENGTH ds ∧
    evaluate_decs mn menv cenv s env (TAKE n ds) (s',cenv',Rval env') ∧
    (∀res. ¬ evaluate_dec mn menv (cenv'++cenv) s' (env'++env) (EL n ds) res)``,
  Induct >>
  simp[Once evaluate_decs_cases] >>
  qx_gen_tac`d` >> rpt strip_tac >>
  Cases_on`∃res. evaluate_dec mn menv cenv s env d res` >- (
    fs[] >>
    PairCases_on`res`>>fs[] >>
    Cases_on`res1`>>fs[]>-(
      PairCases_on`a`>>fs[]>>
      fsrw_tac[DNF_ss][] >>
      first_x_assum(qspecl_then[`mn`,`menv`,`merge a0 cenv`,`res0`,`merge a1 env`]mp_tac) >>
      simp[FORALL_PROD] >>
      discharge_hyps >- metis_tac[] >>
      strip_tac >>
      qexists_tac`SUC n` >>
      simp[] >>
      simp[Once evaluate_decs_cases] >>
      fsrw_tac[DNF_ss][] >>
      qexists_tac`s'` >>
      simp[SemanticPrimitivesTheory.combine_dec_result_def] >>
      qexists_tac`merge env' a1` >>
      qexists_tac`res0` >>
      qexists_tac`cenv'` >>
      qexists_tac`a0` >>
      qexists_tac`a1` >>
      qexists_tac`Rval env'` >>
      simp[] >>
      fs[LibTheory.merge_def] ) >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[] ) >>
  qexists_tac`0` >>
  simp[] >>
  simp[Once evaluate_decs_cases,LibTheory.emp_def,LibTheory.merge_def] >>
  metis_tac[] )

(*
val compile_decs_folds = store_thm("compile_decs_folds",
 ``compile_decs mn rmenv ct m renv rsz cs decs =
   compile_decs mn rmenv
     (decs_to_contab mn (TAKE n decs))
     (decs_to_m (TAKE n decs))
     (GENLIST 
     (compile_decs mn rmenv ct m renv rsz cs (TAKE n decs))
FOLDL_TAKE
FOLDR_TAKE
print_apropos``FOLDL f a (TAKE n l)``
*)


val evaluate_decs_divergence = store_thm("evaluate_decs_divergence",
  ``∀ds mn menv cenv s env.
    (∀res. ¬ evaluate_decs mn menv cenv s env ds res)
    ⇒
    ∃d ds'.
    d ::ds' = ds ∧
    ∀res. evaluate_dec mn menv cenv s env d res ⇒
    ∃s' cenv' env'. res = (s',Rval (cenv',env')) ∧
    ∀res. ¬ evaluate_decs mn menv (cenv'++cenv) s' (env'++env) ds' res``,
  Induct >> simp[Once evaluate_decs_cases] >>
  qx_gen_tac`d` >> rpt strip_tac >>
  PairCases_on`res`>>fs[] >>
  Cases_on`res1`>>fs[]>-(
    PairCases_on`a`>>fs[]>>
    fsrw_tac[DNF_ss][] >>
    fs[LibTheory.merge_def,FORALL_PROD] >>
    metis_tac[] ) >>
  metis_tac[])

val evaluate_dec_determ = store_thm("evaluate_dec_determ",
  ``∀mn menv (cenv:envC) s env d r1.
    evaluate_dec mn menv cenv s env d r1 ⇒
    ∀r2. evaluate_dec mn menv cenv s env d r2 ⇒ r2 = r1``,
  ho_match_mp_tac evaluate_dec_ind >>
  rpt conj_tac >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac big_exp_determ >> fs[] )

val evaluate_decs_determ = store_thm("evaluate_decs_determ",
  ``∀mn menv cenv s env ds res.
    evaluate_decs mn menv cenv s env ds res ⇒
    ∀r2. evaluate_decs mn menv cenv s env ds r2 ⇒ r2 = res``,
  ho_match_mp_tac evaluate_decs_ind >>
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac evaluate_dec_determ >> fs[] >>
  fs[LibTheory.merge_def,SemanticPrimitivesTheory.combine_dec_result_def] >>
  res_tac >> fs[])

val compile_decs_divergence = store_thm("compile_decs_divergence",
  ``∀decs mn rmenv ct m renv rsz cs.
    let (ct',m',rsz',cs') = compile_decs mn rmenv ct m renv rsz cs decs in
    ∀menv cenv s env rs csz rd ck bs bc0 code.
    (∀res. ¬evaluate_decs mn menv cenv s env decs res)
    ∧ cs'.out = REVERSE code ++ cs.out
    ∧ FV_decs decs ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
    ∧ (∀i tds. i < LENGTH decs ∧ (EL i decs = Dtype tds) ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i decs) ++ cenv) tds)
    ∧ decs_cns mn decs ⊆ cenv_dom cenv
    ∧ closed_context menv cenv s env
    ∧ env_rs menv cenv env rs csz rd (ck,s) (bs with code := bc0)
    ∧ rmenv = MAP SND o_f rs.rmenv
    ∧ renv = MAP (CTDec o SND) rs.renv
    ∧ rsz = rs.rsz
    ∧ ct = rs.contab
    ∧ m.bvars = MAP FST env
    ∧ m.mvars = MAP FST o_f alist_to_fmap menv
    ∧ m.cnmap = cmap rs.contab
    ∧ rs.rnext_label = cs.next_label
    ∧ bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ IS_SOME bs.clock
    ∧ good_labels rs.rnext_label bc0
    ⇒
    ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0``,
  Induct >- (
    simp[Once evaluate_decs_cases,UNCURRY] ) >>
  qx_gen_tac`d` >> rw[] >>
  qmatch_assum_abbrev_tac`compile_decs mn rmenv ct m renv rsz cs (d::decs) = X` >> qunabbrev_tac`X` >>
  qabbrev_tac`p = compile_dec rmenv m renv rsz cs d` >>
  PairCases_on`p` >>
  qpat_assum`X = (Y,z)`mp_tac >>
  rw[compile_decs_def,LET_THM] >>
  qabbrev_tac`ct1 = dec_to_contab mn ct d` >>
  qmatch_assum_abbrev_tac`compile_decs mn rmenv ct1 m1 renv1 rsz1 cs1 decs = X` >> qunabbrev_tac`X` >>
  first_x_assum(qspecl_then[`mn`,`rmenv`,`ct1`,`m1`,`renv1`,`rsz1`,`cs1`]mp_tac) >>
  simp[] >>
  qmatch_assum_abbrev_tac`Abbrev(cs1 = compile_news p1 0 vs)` >>
  qspecl_then[`vs`,`p1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  qspecl_then[`rmenv`,`m`,`renv`,`rsz`,`cs`,`d`]mp_tac compile_dec_append_out >>
  simp[] >>
  `LENGTH renv = LENGTH env` by (
    fs[env_rs_def,LET_THM,LIST_EQ_REWRITE,Abbr`renv`] ) >>
  discharge_hyps >- (
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FV_decs_def,MEM_FLAT] >>
    rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
  disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
  qspecl_then[`decs`,`mn`,`rmenv`,`ct1`,`m1`,`renv1`,`rsz1`,`cs1`]mp_tac compile_decs_append_out >>
  simp[] >>
  discharge_hyps >- (
    simp[Abbr`renv1`,Abbr`m1`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FV_decs_def,MEM_FLAT] >>
    rw[] >> res_tac >> fs[Abbr`vs`] >>
    Cases_on`p0`>>fs[]>>rw[]>>
    metis_tac[] ) >>
  disch_then(qx_choosel_then[`c3`]strip_assume_tac) >>
  Cases_on`∀res. ¬ evaluate_dec mn menv cenv s env d res` >- (
    qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`]mp_tac compile_dec_divergence >> simp[] >>
    disch_then(qspecl_then[`rs`,`csz`,`rd`,`ck`,`bs with code := bc0 ++ c2`,`bc0`,`m`,`cs`]mp_tac) >> simp[] >>
    discharge_hyps >- fs[FV_decs_def,decs_cns_def] >>
    disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
    strip_tac >>
    qexists_tac`bs1 with code := bs.code` >>
    conj_tac >- (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs with code := bc0++c2`,`bs1`] >>
      simp[bc_state_component_equality] >>
      imp_res_tac RTC_bc_next_preserves >> simp[] >>
      fs[Once SWAP_REVERSE_SYM] ) >>
    simp[] >>
    fs[bc_fetch_def] >>
    fs[Once SWAP_REVERSE_SYM] >>
    match_mp_tac bc_fetch_aux_append_code >>
    match_mp_tac bc_fetch_aux_append_code >>
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  fs[Once SWAP_REVERSE_SYM] >>
  imp_res_tac evaluate_decs_divergence >>
  fs[] >> rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum(qspec_then`res`mp_tac) >> simp[] >>
  PairCases_on`res`>>simp[] >> strip_tac >>
  disch_then(qspecl_then[`menv`,`cenv'++cenv`,`res0`,`env'++env`]mp_tac) >> simp[] >>
  qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`,`res0,res1`]mp_tac compile_dec_thm >>
  simp[] >>
  disch_then(qx_choosel_then[`ck2`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`m`,`cs`,`p0`,`p1`,`rs`,`rd`,`bs with <|code := bc0 ++ c2; clock := SOME ck2|>`,`bc0`]mp_tac) >> simp[] >>
  disch_then(qspec_then`csz`mp_tac)>>simp[] >>
  discharge_hyps >- (
    fs[FV_decs_def,decs_cns_def] >>
    match_mp_tac env_rs_change_clock >>
    qexists_tac`ck,s` >> simp[] >>
    HINT_EXISTS_TAC >> simp[bc_state_component_equality] ) >>
  disch_then(qx_choosel_then[`Cvs`,`bvs`,`rf`,`rd2`,`Cs2`]strip_assume_tac) >>
  qabbrev_tac`rs1 = rs with <|contab := ct1
                             ;renv := ZIP(vs,GENLIST (λi. rs.rsz+(LENGTH vs)-1-i) (LENGTH vs))++rs.renv
                             ;rsz := rsz1
                             ;rnext_label := p1.next_label|>` >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
  first_x_assum(qspecl_then[`bs1 with code := bc0++c2++c1`,`bc0++c2`]mp_tac) >>
  simp[Abbr`bs1`] >>
  imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
  `LENGTH bvs = LENGTH vs` by (
    fs[EVERY2_EVERY,vs_to_Cvs_MAP] >>
    Cases_on`p0`>>fs[Abbr`vs`] >> rfs[] >> fs[] >>
    fs[LIST_EQ_REWRITE] ) >>
  rfs[] >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
  disch_then(qspecl_then[`rs1`,`csz`,`rd2`,`ck`,`bs3 with <|code := bs.code; clock := SOME ck|>`,`bc0++c2++c1`]mp_tac) >>
  simp[Abbr`bs3`] >>
  discharge_hyps >- (
    (* this whole thing should be pulled out as a separate theorem, and re-used from compile_decs_thm *)
    simp[Abbr`m1`] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][FV_decs_def,SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      Cases>>simp[]>>
      strip_tac >> res_tac >> fs[] >>
      qpat_assum`MAP FST env' = X`(assume_tac o SYM)>>fs[MEM_MAP,FORALL_PROD] >>
      metis_tac[] ) >>
    conj_tac >- (
      rpt strip_tac >>
      last_x_assum(qspec_then`SUC i`mp_tac) >>
      simp[decs_to_cenv_def] >>
      imp_res_tac evaluate_dec_dec_to_cenv >>
      fs[] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][MEM_MAP, cenv_dom_def,SUBSET_DEF,decs_cns_def] >>
      rpt strip_tac >> res_tac >>
      imp_res_tac evaluate_dec_new_dec_cns >> fs[] >>
      metis_tac[MEM_MAP] ) >>
    conj_tac >- (
      qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`,`res0`,`Rval(cenv',env')`]mp_tac evaluate_dec_closed_context >>
      simp[] >>
      disch_then match_mp_tac >>
      fs[FV_decs_def,decs_cns_def] ) >>
    simp[CONJ_ASSOC] >>
    reverse conj_asm2_tac >- (
      fsrw_tac[DNF_ss][good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,between_labels_def,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
      `FILTER is_Label c1 = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[] ) >>
      rw[Abbr`rs1`] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    reverse conj_tac >- simp[Abbr`rs1`] >>
    reverse conj_tac >- simp[Abbr`rs1`] >>
    reverse conj_tac >- ( simp[Abbr`vs`] >> Cases_on`d`>>simp[] ) >>
    reverse conj_tac >- simp[Abbr`rs1`] >>
    reverse conj_tac >- (
      simp[Abbr`rs1`,Abbr`renv1`] >>
      simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF,Abbr`rsz1`] ) >>
    reverse conj_tac >- (
      simp[Abbr`rs1`,Abbr`renv1`] >>
      simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF,Abbr`rsz1`] ) >>
    reverse conj_tac >- (
      simp[Abbr`rs1`,Abbr`renv1`] >>
      simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF,Abbr`rsz1`] ) >>
    rator_x_assum`env_rs`mp_tac >>
    rator_x_assum`s_refs`mp_tac >>
    simp[] >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    rpt strip_tac >>
    match_mp_tac env_rs_append_code >>
    qunabbrev_tac`bs0` >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd X Y` >>
    qexists_tac`bs0 with code := bc0 ++ c2` >>
    simp[bc_state_component_equality,Abbr`bs0`] >>
    reverse conj_tac >- (
      fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      metis_tac[] ) >>
    Cases_on`cenv' = []` >- (
      simp[] >>
      `ct1 = rs.contab` by (
        simp[Abbr`ct1`] >>
        Cases_on`d`>>fs[dec_to_contab_def] >>
        fs[Once evaluate_dec_cases,LibTheory.emp_def] >>
        qpat_assum`[] = X`mp_tac >>
        simp[SemanticPrimitivesTheory.build_tdefs_def,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,FORALL_PROD,UNCURRY,EXISTS_PROD] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        simp[FOLDL_number_constructors_thm] >>
        Q.PAT_ABBREV_TAC`ll = FLAT (MAP (SND o SND) l)` >>
        strip_tac >>
        `ll = []` by (
          simp[Abbr`ll`,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,EXISTS_PROD] >>
          metis_tac[] ) >>
        simp[number_constructors_def] ) >>
      simp[] >>
      fs[env_rs_def,LET_THM] >>
      rfs[Abbr`rs1`] >> fs[] >>
      qexists_tac`Cmenv` >>
      simp[MAP_ZIP] >>
      simp[Abbr`rsz1`] >>
      simp[TAKE_APPEND1,TAKE_LENGTH_ID_rwt] >>
      qexists_tac`REVERSE Cvs ++ Cenv` >>
      qexists_tac`Cs2` >>
      fs[vs_to_Cvs_MAP] >>
      conj_tac >- (
        match_mp_tac EVERY2_APPEND_suff >>
        simp[] >>
        simp[env_to_Cenv_MAP] >>
        fs[MAP_MAP_o,MAP_REVERSE] >>
        metis_tac[EVERY2_REVERSE1]) >>
      conj_tac >- (
        fs[closed_Clocs_def] >>
        `LENGTH Cs ≤ LENGTH Cs2` by (
          fs[EVERY2_EVERY] >> metis_tac[] ) >>
        full_simp_tac list_ss [SUBSET_DEF,IN_COUNT] >>
        metis_tac[LESS_LESS_EQ_TRANS] ) >>
      conj_tac >- (
        fs[closed_vlabs_def,vlabs_list_APPEND,EVERY_REVERSE,vlabs_list_REVERSE] >>
        rw[] >> TRY(metis_tac[]) >>
        match_mp_tac code_env_cd_append >>
        fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] ) >>
      qunabbrev_tac`renv1` >>
      conj_asm1_tac >- (
        simp[Abbr`vs`] >>
        Cases_on`d`>>simp[] ) >>
      simp[MAP_GENLIST] >>
      Q.PAT_ABBREV_TAC`renw:ctenv = GENLIST X y` >>
      match_mp_tac Cenv_bs_FUPDATE_LIST_CTDec >>
      simp[Abbr`renw`] >>
      map_every qexists_tac[`REVERSE Cvs`,`Cenv`,`renv`,`LENGTH bs.stack`] >>
      simp[REVERSE_GENLIST,PRE_SUB1] >>
      Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd x y` >>
      qexists_tac`bs0 with stack := bs.stack` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      `LENGTH (new_dec_vs d) = LENGTH Cvs` by ( simp[] >> fs[EVERY2_EVERY] ) >>
      simp[] >>
      reverse conj_tac >- (
        conj_tac >- (
          match_mp_tac EVERY2_REVERSE >>
          simp[] ) >>
        simp[LIST_EQ_REWRITE] ) >>
      match_mp_tac Cenv_bs_with_irr >>
      qexists_tac`bs with <|code := bc0 ++ c2; refs := rf; clock := SOME ck|>` >>
      simp[] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac[`rd`,`ck,Cs`,`bs with code := bc0 ++ c2`,`rf`,`SOME ck`] >>
      simp[bc_state_component_equality] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_append_code >>
        qexists_tac`bs with code := bc0` >>
        simp[bc_state_component_equality] >>
        fsrw_tac[ARITH_ss][] ) >>
      fs[s_refs_def,good_rd_def] ) >>
    `env' = []` by (
      Cases_on`d`>>fs[Once evaluate_dec_cases,LibTheory.emp_def] ) >>
    simp[] >>
    match_mp_tac env_rs_change_store >>
    Q.PAT_ABBREV_TAC`bs0 = bc_state_stack_fupd X Y` >>
    map_every qexists_tac[`rd`,`ck,s`,`bs0 with <|refs:=bs.refs;clock:=SOME ck|>`] >>
    simp[Abbr`bs0`,bc_state_component_equality] >>
    qexists_tac`Cs2`>>simp[] >>
    reverse conj_tac >- (
      conj_tac >- (
        match_mp_tac s_refs_with_irr >>
        Q.PAT_ABBREV_TAC`bs1 = bc_state_stack_fupd x y` >>
        qmatch_assum_abbrev_tac`s_refs rd2 (0,Cs2) bs0` >>
        qexists_tac`bs0 with <| code := bc0 ++ c2; clock := SOME ck|>` >>
        simp[Abbr`bs0`,Abbr`bs1`] >>
        fs[s_refs_def,good_rd_def] ) >>
      simp[Abbr`rs1`] >>
      qmatch_abbrev_tac `EVERY2 syneq vs1 Cs2` >>
      qmatch_assum_abbrev_tac `EVERY2 syneq vs2 Cs'` >>
      qsuff_tac`vs1 = vs2` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac(CONJUNCT1(CONJUNCT2 v_to_Cv_SUBMAP)) >>
      imp_res_tac evaluate_dec_all_cns >>
      rfs[decs_cns_def] >>
      pop_assum mp_tac >>
      discharge_hyps >- fs[closed_context_def,closed_under_cenv_def] >>
      strip_tac >>
      `cenv_dom cenv ⊆ FDOM (cmap rs.contab)` by (
        fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF] ) >>
      conj_tac >- (
        simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF] >>
        fs[SUBSET_DEF] >> metis_tac[] ) >>
      qspecl_then[`[d]`,`mn`,`rs.contab`,`cenv`]mp_tac decs_to_contab_cmap_SUBMAP >>
      simp[decs_to_contab_def] >>
      disch_then match_mp_tac >>
      fs[env_rs_def,SET_EQ_SUBSET,SUBSET_DEF,decs_to_cenv_def] >>
      last_x_assum(qspec_then`0`mp_tac) >>
      simp[decs_to_cenv_def] >> strip_tac >>
      Cases_on`mn`>>fs[AstTheory.mk_id_def] >> metis_tac[] ) >>
    match_mp_tac env_rs_with_bs_irr >>
    qexists_tac`bs with code := bc0 ++ c2` >>
    simp[] >> fs[] >>
    `vs = []` by (
      simp[Abbr`vs`] >>
      Cases_on`d`>>simp_tac(srw_ss())[] ) >>
    `bvs = []` by (
      rfs[EVERY2_EVERY] >>
      metis_tac[LENGTH_NIL] ) >>
    fs[LENGTH_NIL] >>
    simp[Abbr`rsz1`] >>
    `bs.clock = SOME ck` by (
      Cases_on`bs.clock`>>fs[]>>
      fs[env_rs_def,LET_THM,Cenv_bs_def,s_refs_def] ) >>
    simp[] >>
    match_mp_tac env_rs_with_irr >>
    qexists_tac`rs with contab := ct1` >>
    qpat_assum`[] = x`(assume_tac o SYM) >>
    simp[Abbr`rs1`] >>
    match_mp_tac env_rs_append_code >>
    qexists_tac`bs with code := bc0` >>
    simp[bc_state_component_equality] >>
    fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    match_mp_tac decs_contab_thm >>
    map_every qexists_tac [`mn`,`[d]`,`cenv`,`rs`] >>
    simp[decs_to_cenv_def,Abbr`ct1`,decs_to_contab_def] >>
    imp_res_tac evaluate_dec_dec_to_cenv >> fs[] >>
    last_x_assum(qspec_then`0`mp_tac) >>
    simp[decs_to_cenv_def] >> strip_tac >>
    Cases_on`mn`>>fs[AstTheory.mk_id_def] >> metis_tac[] ) >>
  disch_then(qx_choosel_then[`bs3`]strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
  `bc_next^* (bs with <|clock := SOME (ck+ck2)|>) (bs2 with <| code := bs.code; clock := SOME ck|>)` by (
    qspecl_then[`bs0`,`bs1`]mp_tac RTC_bc_next_add_clock >> simp[] >>
    disch_then(qspec_then`ck`mp_tac) >>
    strip_tac >>
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* x y` >>
    map_every qexists_tac[`x`,`y`] >>
    simp[Abbr`x`,Abbr`y`] >>
    simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality,Abbr`bs2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs4 bs3` >>
  `bc_next^* (bs2 with <|code := bs.code; clock := SOME ck|>) bs4` by (
    qmatch_assum_abbrev_tac`bc_next^* bs2 bs5` >>
    qspecl_then[`bs2`,`bs5`]mp_tac RTC_bc_next_add_clock >> simp[] >>
    disch_then(qspec_then`ck`strip_assume_tac) >>
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* x y` >>
    map_every qexists_tac[`x`,`y`] >>
    simp[Abbr`x`,Abbr`y`] >>
    simp[Abbr`bs2`,Abbr`bs4`,Abbr`bs5`,bc_state_component_equality] ) >>
  `bc_next^* (bs with <|clock := SOME (ck+ck2)|>) bs3` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  `bc_eval (bs with clock := SOME (ck+ck2)) = SOME bs3` by (
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
    simp[] >> simp[bc_eval1_thm,bc_eval1_def] ) >>
  qspecl_then[`bs with clock := SOME (ck+ck2)`,`bs3`]mp_tac RTC_bc_next_less_timeout >>
  simp[] >>
  disch_then(qspec_then`ck`mp_tac) >>
  simp[] >>
  `bs with clock := SOME ck = bs` by (
    simp[bc_state_component_equality] >>
    Cases_on`bs.clock`>>fs[env_rs_def,LET_THM,Cenv_bs_def,s_refs_def] ) >>
  metis_tac[])

val compile_decs_wrap_divergence = store_thm("compile_decs_wrap_divergence",
  ``∀mn menv cenv s env decs rs uct urenv cs' ck bs bc0 csz rd.
      (∀res. ¬evaluate_decs mn menv cenv s env decs res)
      ∧ compile_decs_wrap mn rs decs = (uct,urenv,cs')
      ∧ FV_decs decs ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv
      ∧ (∀i tds.  i < LENGTH decs ∧ EL i decs = Dtype tds ⇒ check_dup_ctors mn (decs_to_cenv mn (TAKE i decs) ++ cenv) tds)
      ∧ closed_context menv cenv s env
      ∧ decs_cns mn decs ⊆ cenv_dom cenv
      ∧ env_rs menv cenv env rs (LENGTH bs.stack) rd (ck,s) (bs with code := bc0)
      ∧ bs.code = bc0 ++ REVERSE cs'.out
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ IS_SOME bs.clock
      ∧ good_labels rs.rnext_label bc0
      ⇒
      ∃bs'.
      bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0``,
  rpt gen_tac >>
  simp[compile_decs_wrap_def] >>
  Q.PAT_ABBREV_TAC`rmenv = MAP SND o_f rs.rmenv` >>
  Q.PAT_ABBREV_TAC`m = exp_to_Cexp_state_bvars_fupd x y` >>
  Q.PAT_ABBREV_TAC`renv:ctenv = MAP X Y` >>
  Q.PAT_ABBREV_TAC`rsz = rs.rsz+x` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd (K [x;z]) y` >>
  Q.PAT_ABBREV_TAC`ct = rs.contab` >>
  `LENGTH renv = LENGTH m.bvars` by (
    simp[Abbr`renv`,Abbr`m`] ) >>
  qabbrev_tac`p = compile_decs mn rmenv ct m renv rsz cs decs` >>
  PairCases_on`p`>>simp[] >>
  Q.PAT_ABBREV_TAC`ct' = (p0,p1,p2)` >>
  Q.PAT_ABBREV_TAC`renv':(string,num)alist = ZIP X` >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X p5` >>
  Q.PAT_ABBREV_TAC`cs2 = compile_news Y 0 Z` >>
  strip_tac >>
  mp_tac(SPEC_ALL compile_decs_divergence) >>
  simp[] >>
  disch_then(qspecl_then[`menv`,`cenv`,`s`,`env`]mp_tac) >>
  simp[] >>
  qmatch_abbrev_tac`G` >>
  qspecl_then[`decs`,`mn`,`rmenv`,`ct`,`m`,`renv`,`rsz`,`cs`]mp_tac compile_decs_append_out >>
  `{x | Short x ∈ FV_decs decs} ⊆ set m.bvars` by (
    simp[Abbr`m`,Abbr`G`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
    rw[] >> res_tac >> fs[] >>
    fs[env_rs_def,LET_THM] >>
    metis_tac[MEM_MAP,FST,pairTheory.PAIR_EQ,pairTheory.pair_CASES] ) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  qspecl_then[`TAKE (p4-rsz) p3.bvars`,`cs1`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_news_thm) >>
  simp[] >>
  disch_then(qx_choosel_then[`c3`]strip_assume_tac) >>
  qabbrev_tac`c0 = [PushPtr (Addr 0);PushExc]` >>
  qmatch_assum_abbrev_tac`p4 = rsz + n` >>
  qabbrev_tac`c2 = [Stack (Cons tuple_cn n); PopExc; Stack (Pops 1)]` >>
  `bs.code = bc0 ++ c0 ++ c1 ++ c2 ++ c3` by (
    simp[Abbr`cs1`,Abbr`cs`,Abbr`c0`,Abbr`c2`] ) >>
  pop_assum mp_tac >>
  qpat_assum`bs.code = X`kall_tac >>
  strip_tac >>
  qabbrev_tac`hdl = LENGTH bs.stack+1` >>
  qabbrev_tac`h0 = bs.handler` >>
  qabbrev_tac`bs0 = bs with <| pc := next_addr bs.inst_length (bc0++c0); stack := StackPtr h0::CodePtr 0::bs.stack; handler := hdl |>` >>
  `bc_next^* bs bs0` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC 0)` >>
    simp[NRC] >>
    `bc_fetch bs = SOME (PushPtr (Addr 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0 ++ TAKE 0 c0` >>
      simp[Abbr`c0`] ) >>
    simp[Once bc_eval1_thm] >>
    simp[bc_eval1_def,bc_find_loc_def,bump_pc_def] >>
    qmatch_abbrev_tac`bc_next bs1 bs0` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0 ++ TAKE 1 c0` >>
      simp[Abbr`bs1`,Abbr`c0`,SUM_APPEND,FILTER_APPEND] ) >>
    simp[bc_eval1_thm] >>
    simp[bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,Abbr`bs0`,bc_state_component_equality,Abbr`hdl`,Abbr`c0`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[Abbr`G`] >>
  disch_then(qspecl_then[`rs with rsz := rsz`,`LENGTH bs.stack`,`rd`,`ck`,`bs0 with code := bc0++c0++c1`,`bc0 ++ c0`]mp_tac) >>
  simp[Abbr`bs0`] >>
  `good_labels rs.rnext_label (bc0 ++ c0)` by (
    fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,Abbr`c0`] ) >>
  discharge_hyps >- (
    simp[Abbr`cs`,Abbr`m`] >>
    conj_asm1_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs with <|code := bc0++c0; stack := StackPtr h0::CodePtr 0::bs.stack|>` >>
      simp[] >>
      match_mp_tac env_rs_append_code >>
      qexists_tac`bs with <|code := bc0; stack := StackPtr h0::CodePtr 0::bs.stack|>` >>
      simp[bc_state_component_equality] >>
      fs[good_labels_def] >>
      rator_x_assum`env_rs`mp_tac >>
      qunabbrev_tac`rsz` >>
      rpt(pop_assum kall_tac) >>
      simp[env_rs_def] >> rw[] >>
      rpt HINT_EXISTS_TAC >>
      simp[] >>
      REWRITE_TAC[TWO,ADD1,ADD_ASSOC] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <|stack:=CodePtr 0::bs.stack;code:= bc0|>` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <|code:= bc0|>` >>
      simp[bc_state_component_equality] >>
      rfs[] ) >>
    fs[env_rs_def,LET_THM] ) >>
  disch_then(qx_choosel_then[`bs2`]strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs0` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* bs0 (bs2 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs1`,`bs2`] >>
    simp[bc_state_component_equality,Abbr`bs0`,Abbr`bs1`] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  `bc_fetch (bs2 with code := bs.code) = SOME Tick` by (
    fs[bc_fetch_def] >>
    match_mp_tac bc_fetch_aux_append_code >>
    match_mp_tac bc_fetch_aux_append_code >>
    imp_res_tac RTC_bc_next_preserves >> fs[Abbr`bs1`] ) >>
  qexists_tac`bs2 with code := bs.code` >>
  simp[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val EXISTS_LIST_EQ_MAP = store_thm("EXISTS_LIST_EQ_MAP",
  ``∀ls f. EVERY (λx. ∃y. x = f y) ls ⇒ ∃l. ls = MAP f l``,
  Induct >> simp[] >> rw[] >> res_tac >> qexists_tac`y::l`>>simp[])

val compile_top_divergence = store_thm("compile_top_divergence",
  ``∀menv cenv s env top rs rd ck bc0 bs ss sf code. (∀res. ¬evaluate_top menv cenv s env top res) ∧
      closed_top menv cenv s env top ∧
      (∀mn spec ds.  top = Tmod mn spec ds ⇒
         ∀i ts.  i < LENGTH ds ∧ EL i ds = Dtype ts ⇒ check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv) ts) ∧
      env_rs menv cenv env rs (LENGTH bs.stack) rd (ck,s) (bs with code := bc0) ∧
      (compile_top rs top = (ss,sf,code)) ∧
      bs.code = bc0 ++ REVERSE code ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      IS_SOME bs.clock ∧
      good_labels rs.rnext_label bc0
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0``,
  rw[closed_top_def] >>
  Cases_on`top`>- (
    fs[Once evaluate_top_cases] >>
    qmatch_assum_rename_tac`compile_top rs (Tmod mn specs ds) = X`["X"] >>
    Cases_on`∃r. evaluate_decs (SOME mn) menv cenv s env ds r`>>fs[]>-(
      PairCases_on`r`>>fs[]>>
      Cases_on`r2`>>fs[]>>
      TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
      metis_tac[] ) >>
    qabbrev_tac`p = compile_decs_wrap (SOME mn) rs ds` >>
    PairCases_on`p` >>
    fs[compile_top_def,LET_THM] >>
    fs[FOLDL_emit_thm] >>
    qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`rs`]mp_tac compile_decs_wrap_divergence >>
    simp[] >>
    qmatch_assum_abbrev_tac`pc ++ p4.out = code` >>
    disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`rd`]mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[bc_state_component_equality,Abbr`bs0`] >>
      BasicProvers.VAR_EQ_TAC >> simp[] >>
      imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[bc_fetch_def] >>
    BasicProvers.VAR_EQ_TAC >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    simp[REVERSE_APPEND] >>
    match_mp_tac bc_fetch_aux_append_code >>
    simp[] ) >>
  fs[Once evaluate_top_cases] >>
  Cases_on`∃r. evaluate_decs NONE menv cenv s env [d] r`>>fs[]>-(
    `∃res. r = (FST r,(case res of Rval (x,y) => x | Rerr _ => []),map_result SND res)` by (
      PairCases_on`r`>>simp[]>>
      Cases_on`r2` >- (
        qexists_tac`Rval (r1,a)` >> simp[] ) >>
      qexists_tac`Rerr e` >> simp[] >>
      Cases_on`d`>>fs[Once evaluate_decs_cases,LibTheory.emp_def,LibTheory.merge_def] >>
      fs[Once evaluate_decs_cases,LibTheory.merge_def,LibTheory.emp_def] >>
      fs[Once evaluate_dec_cases,LibTheory.merge_def,LibTheory.emp_def] >>
      fs[SemanticPrimitivesTheory.combine_dec_result_def] ) >>
    `evaluate_dec NONE menv cenv s env d (FST r,res)` by metis_tac[evaluate_dec_decs] >>
    Cases_on`res`>>fs[] >>
    TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
    metis_tac[] ) >>
  qabbrev_tac`p = compile_decs_wrap NONE rs [d]` >>
  PairCases_on`p` >>
  fs[compile_top_def,LET_THM] >>
  qspecl_then[`NONE`,`menv`,`cenv`,`s`,`env`,`[d]`,`rs`]mp_tac compile_decs_wrap_divergence >>
  simp[] >>
  qspecl_then[`d`,`p4`]mp_tac compile_print_dec_thm >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`code = pc ++ p4.out` >>
  disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`rd`]mp_tac) >>
  simp[FV_decs_def] >>
  discharge_hyps >- (
    simp[decs_to_cenv_def,decs_cns_def] >> rw[] >>
    fs[Once evaluate_dec_cases] >>
    spose_not_then strip_assume_tac >> fs[] >>
    fs[Once evaluate_decs_cases] >>
    fs[Once evaluate_dec_cases] ) >>
  disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
  `bc_next^* bs (bs1 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    map_every qexists_tac[`bs0`,`bs1`] >>
    simp[bc_state_component_equality,Abbr`bs0`] >>
    BasicProvers.VAR_EQ_TAC >> simp[] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[bc_fetch_def] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac RTC_bc_next_preserves >> fs[] >>
  simp[REVERSE_APPEND] >>
  match_mp_tac bc_fetch_aux_append_code >>
  simp[] )

(*
val env_rs_ALOOKUP_same = store_thm("env_rs_ALOOKUP_same",
  ``∀menv cenv env rs rd s bs env'.
    env_rs menv cenv env rs rd s bs ∧ (ALOOKUP env' = ALOOKUP env) ⇒
    env_rs menv cenv env' rs rd s bs``,
  simp[env_rs_def] >> rw[] >>
  REWRITE_TAC[GSYM FDOM_alist_to_fmap] >>
  pop_assum mp_tac >>
  REWRITE_TAC[CONJUNCT1(GSYM ALOOKUP_EQ_FLOOKUP)] >>
  REWRITE_TAC[EXTENSION] >>
  REWRITE_TAC[FUN_EQ_THM] >>
  REWRITE_TAC[FLOOKUP_DEF] >>
  metis_tac[optionTheory.NOT_SOME_NONE])

val ALOOKUP_APPEND_same = store_thm("ALOOKUP_APPEND_same",
  ``∀l1 l2 l. (ALOOKUP l1 = ALOOKUP l2) ==> ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l)``,
  rw[ALOOKUP_APPEND,FUN_EQ_THM])

val ALOOKUP_ALL_DISTINCT_PERM_same = store_thm("ALOOKUP_ALL_DISTINCT_PERM_same",
  ``∀l1 l2. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) (MAP FST l2) ∧ (set l1 = set l2) ⇒ (ALOOKUP l1 = ALOOKUP l2)``,
  simp[EXTENSION] >>
  rw[FUN_EQ_THM] >>
  Cases_on`ALOOKUP l2 x` >- (
    imp_res_tac ALOOKUP_FAILS >>
    imp_res_tac MEM_PERM >>
    fs[FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
    metis_tac[ALOOKUP_FAILS] ) >>
  qmatch_assum_rename_tac`ALOOKUP l2 x = SOME p`[] >>
  imp_res_tac ALOOKUP_MEM >>
  `ALL_DISTINCT (MAP FST l2)` by (
    metis_tac[ALL_DISTINCT_PERM]) >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  metis_tac[])

val ALL_DISTINCT_PERM_ALOOKUP_ZIP = store_thm("ALL_DISTINCT_PERM_ALOOKUP_ZIP",
  ``∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))``,
  rw[EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1`[] >>
    imp_res_tac PERM_LENGTH >> fs[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ x = EL m l2` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    rw[ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1`[] >>
  imp_res_tac PERM_LENGTH >>
  fs[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  qexists_tac`m` >>
  simp[EL_MAP] >>
  Cases_on`EL m l1`>>simp[ALOOKUP_APPEND] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    metis_tac[MEM_EL] ) >>
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF])
*)

val env_rs_empty = store_thm("env_rs_empty",
  ``bs.stack = [] ∧ (∀n. bs.clock = SOME n ⇒ n = ck) ∧ rd.sm = [] ∧ rd.cls = FEMPTY ∧ cs = init_compiler_state ⇒
    env_rs [] [] [] cs 0 rd (ck,[]) bs``,
  simp[env_rs_def,init_compiler_state_def,intLangExtraTheory.good_cmap_def,FLOOKUP_UPDATE
      ,good_contab_def,IntLangTheory.tuple_cn_def,toIntLangProofsTheory.cmap_linv_def] >>
  simp[pmatchTheory.env_to_Cenv_MAP,intLangExtraTheory.all_vlabs_menv_def
      ,intLangExtraTheory.vlabs_menv_def,pred_setTheory.SUM_IMAGE_THM
      ,closed_Clocs_def,closed_vlabs_def] >>
  strip_tac >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_DEF,semanticsExtraTheory.cenv_dom_def])

val env_rs_remove_clock = store_thm("env_rs_remove_clock",
   ``∀menv cenv env rs cz rd cs bs cs' ck' bs'.
     env_rs menv cenv env rs cz rd cs bs ∧ cs' = (ck',SND cs) ∧
     bs' = bs with clock := NONE ⇒
     env_rs menv cenv env rs cz rd cs' bs'``,
  rw[env_rs_def] >> fs[LET_THM] >>
  rpt HINT_EXISTS_TAC >>
  qexists_tac`Cs` >> simp[] >>
  match_mp_tac Cenv_bs_change_store >>
  map_every qexists_tac[`rd`,`FST cs,Cs`,`bs`,`bs.refs`,`NONE`] >>
  simp[bc_state_component_equality] >> rfs[] >>
  fs[Cenv_bs_def,s_refs_def,good_rd_def])

val _ = export_theory()
