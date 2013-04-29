open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory pred_setTheory relationTheory arithmeticTheory whileTheory pairTheory quantHeuristicsLib lcsymtacs
open miniMLExtraTheory miscTheory intLangTheory expToCexpTheory compileTerminationTheory compileCorrectnessTheory bytecodeTerminationTheory bytecodeExtraTheory bytecodeEvalTheory pmatchTheory  labelClosuresTheory
open miscLib MiniMLTerminationTheory finite_mapTheory sortingTheory
val _ = new_theory"repl"

val good_contab_def = Define`
  good_contab (m,w,n) =
    fmap_linv m w`

val env_rs_def = Define`
  env_rs env rs c rd s bs =
    (rs.rbvars = MAP FST env) ∧
    good_code_env c ∧
    FDOM c ⊆ count rs.rnext_label ∧
    let Cenv = env_to_Cenv (cmap rs.contab) env in
    Cenv_bs c rd s Cenv rs.renv rs.rsz bs`

(* TODO: move *)
val Cevaluate_mono_c = store_thm("Cevaluate_mono_c",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
       ∀c'. c ⊑ c' ⇒ Cevaluate c' s env exp res) ∧
    (∀c s env es res. Cevaluate_list c s env es res ⇒
       ∀c'. c ⊑ c' ⇒ Cevaluate_list c' s env es res)``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[]) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_cases] >>
    disj1_tac >>
    map_every qexists_tac[`s'`,`cenv`,`defs`,`n`] >> simp[] >>
    Cases_on`EL n defs`>>TRY(PairCases_on`x`)>>fs[] >>
    fs[LET_THM,UNCURRY] >>
    metis_tac[SUBMAP_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ))

val label_closures_Cexp_pred = store_thm("label_closures_Cexp_pred",
  ``(∀ez j e. Cexp_pred e ⇒ Cexp_pred(FST(label_closures ez j e))) ∧
    (∀ez j es. EVERY Cexp_pred es ⇒ EVERY Cexp_pred (FST(label_closures_list ez j es))) ∧
    (∀(ez:num) (j:num) (nz:num) (k:num) (defs:(num#Cexp)list). T)``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( ntac 2 (rw[EVERY_MEM]) ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- (
    simp[UNCURRY] >>
    rw[] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    fs[] >>
    first_x_assum match_mp_tac >>
    metis_tac[pairTheory.pair_CASES,SND] ) >>
  strip_tac >- ( rw[] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( ntac 2 (rw[EVERY_MEM]) >> fs[]) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ))

(*
val syneq_exp_Cexp_pred = store_thm("syneq_exp_Cexp_pred",
  ``(∀c z1 z2 V e1 e2. syneq_exp c z1 z2 V e1 e2 ⇒ Cexp_pred e1 ⇒ Cexp_pred e2) ∧
    (∀c z1 z2 V defs1 defs2 U. syneq_defs c z1 z2 V defs1 defs2 U ⇒
      EVERY Cexp_pred (MAP (SND o OUTL) (FILTER ISL defs1)) ⇒
      ∀n1 n2. n1 < LENGTH defs1 ∧ U n1 n2 ∧ n2 < LENGTH defs2 ∧ ISL (EL n2 defs2) ⇒ Cexp_pred (SND (OUTL (EL n2 defs2))))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM,EVERY2_EVERY,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM] >>
    syneq_exp_rules
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> Cases >> rw[EVERY_MEM] >>
    PairCases_on`x`>>TRY(Cases_on`x'`)>>fs[]) >>
  strip_tac >- (
    rw[EVERY_MEM,EVERY2_EVERY,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`y`>>fs[]>>
    PairCases_on`x`>>fs[]
*)

val transitive_LESS = store_thm("transitive_LESS",
  ``transitive ($< : (num->num->bool))``,
  rw[transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀c d s. let s' = FOLDL (cce_aux d) s c in
     ALL_DISTINCT (MAP FST c) ∧
     EVERY (combin$C $< s.next_label) (MAP FST c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP FST c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let (l,cd) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile d (MAP CTEnv cd.ccenv) (TCTail cd.az 0) 0 (cs i) cd.body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   Induct >- (
     simp[Once SWAP_REVERSE,code_env_code_def,FEVERY_DEF] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`d`,`MAP CTEnv p1.ccenv`,`TCTail p1.az 0`,`0`,`s0`,`p1.body`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   qpat_assum`∀j k. P`kall_tac >>
   Q.PAT_ABBREV_TAC`s1 = compile d X Y Z A B` >>
   first_x_assum(qspecl_then[`d`,`s1`]mp_tac) >>
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

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀s c. let (d,s') = compile_code_env s c in
      (d = alist_to_fmap c) ∧
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      EVERY (between s.next_label s'.next_label)
        (MAP dest_Label (FILTER is_Label code)) ∧
      code_env_code d code ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0)
        ⇒
        bc_next^* bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >>
  rw[]

  compile_code_env_def
  cce_aux_def

val Cv_bv_c_SUBMAP = store_thm("Cv_bv_c_SUBMAP",
  ``∀pp.
    (∀Cv bv. Cv_bv pp Cv bv ⇒ ∀rd c l2a c'. (pp = (rd,c,l2a)) ∧ c ⊑ c' ⇒ Cv_bv (rd,c',l2a) Cv bv) ∧
    (∀benv cd env defs. benv_bvs pp benv cd env defs ⇒
      ∀rd c l2a c'. (pp = (rd,c,l2a)) ∧ c ⊑ c' ⇒ benv_bvs (rd,c',l2a) benv cd env defs)``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >>
  PairCases_on`pp` >> simp[] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fs[SUBMAP_DEF,FLOOKUP_DEF] >>
    qexists_tac`l` >> simp[] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Once Cv_bv_cases] )

val s_refs_c_SUBMAP = store_thm("s_refs_c_SUBMAP",
  ``∀c rd s bs c'. s_refs c rd s bs ∧ c ⊑ c' ⇒ s_refs c' rd s bs``,
  rw[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY]
    >- metis_tac[Cv_bv_c_SUBMAP] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  metis_tac[Cv_bv_c_SUBMAP])

val Cenv_bs_c_SUBMAP = store_thm("Cenv_bs_c_SUBMAP",
  ``∀c rd s Cenv renv sz bs c'.
      Cenv_bs c rd s Cenv renv sz bs ∧ c ⊑ c' ⇒
      Cenv_bs c' rd s Cenv renv sz bs``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,option_case_NONE_F] >>
  metis_tac[Cv_bv_c_SUBMAP,s_refs_c_SUBMAP])

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv s c env exp s' v rd rs rs' bc0 bc bs bs'.
      exp_pred exp ∧
      evaluate cenv s env exp (s', Rval v) ∧
      EVERY closed s ∧
      EVERY closed (MAP (FST o SND) env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      closed_under_cenv cenv env s ∧
      (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_locs v ⊆ count (LENGTH s)) ∧
      LENGTH s' ≤ LENGTH rd.sm ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      set (MAP FST cenv) ⊆ FDOM (cmap rs.contab) ∧
      good_contab rs.contab ∧
      env_rs env rs c rd (MAP (v_to_Cv (cmap rs.contab)) s) (bs with code := bc0) ∧
      (repl_exp rs exp = (rs',bc)) ∧
      (bs.code = bc0 ++ bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label bc0)
      ⇒
      ∃bv rf rd' c'.
      let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc);
                          stack := bv :: bs.stack; refs := rf|> in
      bc_next^* bs bs' ∧
      (v_to_ov rd'.sm v = bv_to_ov (FST(SND(rs'.contab))) bv) ∧
      env_rs env rs' c' rd' (MAP (v_to_Cv (cmap rs'.contab)) s') bs'``,
  rpt gen_tac >>
  simp[repl_exp_def,compile_Cexp_def,GSYM LEFT_FORALL_IMP_THM] >>
  Q.PAT_ABBREV_TAC`Ce0 = exp_to_Cexp X exp` >>
  Q.PAT_ABBREV_TAC`p = label_closures Y X Ce0` >>
  PairCases_on`p`>>simp[]>> strip_tac >>
  qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`] mp_tac (CONJUNCT1 exp_to_Cexp_thm1) >>
  simp[] >>
  disch_then (qspec_then `cmap rs.contab` mp_tac) >>
  fs[env_rs_def] >>
  simp[FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qx_gen_tac [`Cs'0`,`Cv0`] >> strip_tac >>
  `Cexp_pred Ce0` by PROVE_TAC[exp_pred_Cexp_pred] >>
  qspecl_then[`LENGTH env`,`rs.rnext_label`,`Ce0`]mp_tac(CONJUNCT1 label_closures_thm) >>
  discharge_hyps >- (
    simp[Abbr`Ce0`] >>
    match_mp_tac free_vars_exp_to_Cexp_matchable >>
    simp[] ) >>
  simp[] >> strip_tac >>
  qpat_assum`X = (rs',bc)`mp_tac >>
  Q.PAT_ABBREV_TAC`cce = compile_code_env X Y` >>
  `Cexp_pred p0` by metis_tac[label_closures_Cexp_pred,FST] >>
  qmatch_assum_abbrev_tac `Cevaluate FEMPTY Cs Cenv Ce0 (Cs'0, Rval Cv0)` >>
  qmatch_assum_rename_tac`body_count Ce = 0`[] >>
  qabbrev_tac`Cc = c ⊌ alist_to_fmap p1` >>
  `Cevaluate Cc Cs Cenv Ce0 (Cs'0, Rval Cv0)` by (
    match_mp_tac (MP_CANON (CONJUNCT1 Cevaluate_mono_c)) >>
    qexists_tac`FEMPTY`>>simp[SUBMAP_FEMPTY] ) >>
  qspecl_then[`Cc`,`Cs`,`Cenv`,`Ce0`,`(Cs'0,Rval Cv0)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
  `LENGTH Cenv = LENGTH env` by simp[Abbr`Cenv`,env_to_Cenv_MAP] >>
  simp[] >> disch_then(qspecl_then[`$=`,`Cs`,`Cenv`,`Ce`]mp_tac) >> simp[] >>
  discharge_hyps >- (
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_c_SUBMAP)) >>
      qexists_tac`alist_to_fmap p1` >>
      simp[Abbr`Cc`,Abbr`Ce0`] >>
      conj_tac >- (
        match_mp_tac SUBMAP_FUNION >>
        disj2_tac >> simp[] >>
        simp_tac(srw_ss()++DNF_ss)[DISJOINT_DEF,EXTENSION,MEM_GENLIST] >>
        gen_tac >> disj2_tac >>
        spose_not_then strip_assume_tac >>
        fsrw_tac[ARITH_ss][env_rs_def,SUBSET_DEF] >>
        res_tac >> DECIDE_TAC ) >>
      rfs[] ) >>
    conj_tac >- (
      rpt strip_tac >>
      match_mp_tac (MP_CANON syneq_c_SUBMAP) >>
      qexists_tac`FEMPTY` >>
      simp[Abbr`Cc`,SUBMAP_FEMPTY,Abbr`Cenv`,env_to_Cenv_MAP,EL_MAP] ) >>
    simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    rpt strip_tac >>
    match_mp_tac (MP_CANON syneq_c_SUBMAP) >>
    qexists_tac`FEMPTY` >>
    fs[Abbr`Cs`,EL_MAP,SUBMAP_FEMPTY] ) >>
  simp_tac(srw_ss()++DNF_ss)[FORALL_PROD] >>
  map_every qx_gen_tac[`Cs'`,`Cv`] >>
  strip_tac >>
  simp[UNCURRY] >>
  rw[] >> simp[] >> fs[LET_THM] >>
  Q.PAT_ABBREV_TAC`tf = X:call_context` >>
  qspecl_then[`FST cce`,`rs.renv`,`tf`,`rs.rsz`,`SND cce`,`Ce`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
  fs[Abbr`tf`] >>
  simp[REVERSE_APPEND] >>
  qspecl_then[`Cc`,`Cs`,`Cenv`,`Ce`,`(Cs',Rval Cv)`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>

  disch_then(qspecl_then[`rd`,`SND cce`,`rs.renv`,`rs.rsz`,`bs1`,`bc0 ++ REVERSE (SND cce).out`,`REVERSE bc`,`bc0 ++ REVERSE (SND cce).out`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`Cenv`,Abbr`Cs`,env_to_Cenv_MAP,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE,combinTheory.o_DEF,all_Clocs_v_to_Cv] >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
    conj_tac >- (
      simp[code_env_code_def,FILTER_APPEND,ALL_DISTINCT_APPEND,Abbr`Cc`] >>
      cheat ) >>
    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Ce0`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      simp[] >>
      fs[Cenv_bs_def,EVERY2_EVERY] ) >>
    conj_tac >- (
      fs[env_to_Cenv_MAP,combinTheory.o_DEF] >>
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac`bs with code := bc0` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_c_SUBMAP >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Cc`,SUBMAP_FUNION] ) >>
    fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_MAP] >>
    cheat ) >>
  disch_then(qspecl_then[`REVERSE bc`,`mp_tac o CONJUNCT1)

  simp[FORALL_PROD,GSYM LEFT_FORALL_IMP_THM]
  fs[compile_code_env_def,LET_THM] >>
  qmatch_assum_abbrev_tac `Cevaluate Cc Cd Cs Cenv Ce (Cs', Rval Cv)` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd X Y` >>
  Q.PAT_ABBREV_TAC`d = X:closure_data` >>
  Q.PAT_ABBREV_TAC`tf = X:call_context` >>
  qho_match_abbrev_tac `∃bv rfs. bc_next^* bs (bs1 bv rfs) ∧ P bv rfs` >>
  qabbrev_tac`bs0 = bs with pc := next_addr bs.inst_length (bc0 ++ (REVERSE cs.out))` >>
  qspecl_then[`d`,`rs.renv`,`tf`,`rs.rsz`,`cs`,`Ce`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
  `bc_next^* bs bs0` by (
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC 0` >>
    rw[] >>
    rw[bc_eval1_thm] >>
    `bc_fetch bs = SOME (Jump (Lab rs.rnext_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >>
      fs[Abbr`cs`] ) >>
    rw[bc_eval1_def] >>
    rw[bc_find_loc_def] >>
    rw[Abbr`bs0`,bc_state_component_equality] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    rfs[FILTER_APPEND] >>
    fs[Abbr`cs`,FILTER_APPEND,SUM_APPEND] >>
    qexists_tac `LENGTH bc0 + 1` >>
    fs[REVERSE_APPEND] >>
    simp_tac std_ss [GSYM APPEND_ASSOC] >>
    simp_tac (std_ss++ARITH_ss) [EL_APPEND2] >>
    simp_tac pure_ss [ONE,EL] >>
    EVAL_TAC >>
    simp[REV_REVERSE_LEM] >>
    simp_tac (std_ss++ARITH_ss) [TAKE_APPEND2] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    fsrw_tac[][ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt] >>
    fsrw_tac[QUANT_INST_ss[std_qp]][] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP] >>
    fsrw_tac[ARITH_ss][between_def] >>
    fs[FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fs[GSYM ADD1,GSYM LESS_EQ] >>
    metis_tac[prim_recTheory.LESS_REFL,LESS_TRANS] ) >>
  `∃bv rfs. bc_next^* bs0 (bs1 bv rfs) ∧ P bv rfs` by (
    qspecl_then[`Cc`,`Cd`,`Cs`,`Cenv`,`Ce`,`Cs', Rval Cv`]mp_tac (CONJUNCT1 compile_val) >>
    fs[] >>
    disch_then (qspecl_then[`sm`,`cls`,`cs`,`d`,`rs.renv`,`rs.rsz`,`bs0`,`bc0 ++ REVERSE cs.out`,`REVERSE bc`,`bc0 ++ REVERSE cs.out`] mp_tac) >>
    simp[Abbr`bs0`,Abbr`P`] >>
    `d.ecs = FEMPTY` by rw[Abbr`d`] >> simp[good_ecs_def] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- cheat >> (* need to assume source language has distinct binders and show that exp_to_Cexp preserves that *)
      conj_tac >- cheat >> (* need to assume source language has distinct binders and show that exp_to_Cexp preserves that *)
      conj_tac >- (
        fsrw_tac[DNF_ss][Abbr`Cenv`,SUBSET_DEF,Abbr`Cs`] >>
        gen_tac >> simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
        simp[env_to_Cenv_MAP] >>
        simp[SIMP_RULE(srw_ss())[UNCURRY,LAMBDA_PROD](Q.ISPEC`v_to_Cv (cmap rs.contab) o FST`alist_to_fmap_MAP_values)] >>
        ho_match_mp_tac IN_FRANGE_o_f_suff >>
        simp[all_Clocs_v_to_Cv] >>
        PROVE_TAC[] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][Abbr`Cs`,SUBSET_DEF,FRANGE_store_to_Cstore,MEM_MAP,all_Clocs_v_to_Cv] >>
        PROVE_TAC[] ) >>
      simp[Cexp_pred_free_labs] >>
      fs[env_rs_def,LET_THM] >>
      fs[Abbr`Cc`,Abbr`Cd`,good_code_env_def,FEVERY_DEF] >>
      conj_tac >- cheat >> (* need to assume something about sm *)
      conj_tac >- cheat >> (* need to assume something about cls *)
      fs[Abbr`Ce`] >>
      reverse conj_asm2_tac >- (
        conj_tac >- (
          fs[Cenv_bs_def,fmap_rel_def,Abbr`Cenv`] >>
          fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
          srw_tac[ETA_ss][] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_append_code >>
          Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
          qexists_tac `bs with <| pc := pc; code := bc0|>` >>
          rw[Abbr`cs`,bc_state_component_equality,Cenv_bs_with_pc] >>
          cheat (* need to fix env_rs_def *)) >>
        fs[Abbr`cs`,FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
        fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
        conj_tac >- (spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        rw[] >> res_tac >> DECIDE_TAC) >>
      fs[] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(mp_tac o CONJUNCT1) >>
    disch_then(qspecl_then[`REVERSE bc`,`[]`]mp_tac) >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`bv`] >>
    rw[LET_THM,Abbr`bs1`,REVERSE_APPEND] >>
    map_every qexists_tac [`bv`,`rf`] >> rw[] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) (DRESTRICT sm (FDOM Cs')) (v_to_Cv (cmap rs.contab) v)` >>
    `count (LENGTH s') = FDOM Cs'` by fs[fmap_rel_def] >> fs[] >>
    conj_tac >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac (CONJUNCT1 v_to_Cv_ov) >>
      qabbrev_tac`ct=rs.contab` >>
      PairCases_on`ct` >> fs[good_contab_def] >>
      qspecl_then[`cenv`,`s`,`env`,`exp`,`s',Rval v`]mp_tac (CONJUNCT1 evaluate_all_cns) >>
      fs[good_cmap_def] >>
      fs[SUBSET_DEF] >>
      metis_tac[] ) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) (DRESTRICT sm (FDOM Cs')) Cv` >>
    conj_tac >- (
      match_mp_tac syneq_ov >>
      metis_tac[syneq_sym] ) >>
    match_mp_tac (MP_CANON Cv_bv_ov) >>
    metis_tac[FST] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

set_trace"goalstack print goal at top"0

(* must read an expression followed by all space until the start of another
   expression (or end of string) *)
val parse_def = Define`
  (parse : string -> (t exp # string) option) s = ARB`

val _ = Hol_datatype`
  swhile_result = Terminate of 'a | Diverge`

val _ = Hol_datatype`
  swhile_step_result = Success of 'a | Fail of 'b`

val SWHILE_def = Define`
  SWHILE f x = case OWHILE (ISL o f) (OUTL o f) x of NONE => Diverge | SOME y => Terminate (OUTR (f y))`

val SWHILE_thm = store_thm("SWHILE_thm",
  ``SWHILE f x = case f x of INL x => SWHILE f x | INR y => Terminate y``,
  rw[SWHILE_def] >> Cases_on `f x` >> rw[Once OWHILE_THM])

val intersperse_def = Define`
  (intersperse _ [] = []) ∧
  (intersperse _ [x] = [x]) ∧
  (intersperse a (x::xs) = x::a::intersperse a xs)`

val ov_to_string_def = tDefine "ov_to_string"`
  (ov_to_string (OLit (IntLit i)) = if i < 0 then "-"++(num_to_dec_string (Num (-i)))
                                             else num_to_dec_string (Num i)) ∧
  (ov_to_string (OLit (Bool T)) = "true") ∧
  (ov_to_string (OLit (Bool F)) = "false") ∧
  (ov_to_string (OConv cn vs) = cn++"("++CONCAT(intersperse "," (MAP ov_to_string vs))++")") ∧
  (ov_to_string OFn = "fn")`
  (WF_REL_TAC`measure ov_size` >>
   gen_tac >> Induct >> rw[CompileTheory.ov_size_def] >>
   res_tac >> srw_tac[ARITH_ss][])

(*
``ov_to_string (OConv "Cons" [OLit(IntLit (-3));OConv "Nil"[]]) = X ``
rw[ov_to_string_def,intersperse_def,
   ASCIInumbersTheory.num_to_dec_string_def,
   ASCIInumbersTheory.n2s_def,
   ASCIInumbersTheory.HEX_def,
   Once numposrepTheory.n2l_def ]
*)

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := ARB |>`

val repl_def = Define`
  repl s = SWHILE
   (λ(rs,bs,inp:string,out:string).
     if inp = "" then INR (Success out) else
     case parse inp of NONE => INR (Fail "parse error") |
     SOME (exp,inp) =>
       (* typecheck? *)
       let (rs',bc) = repl_exp rs exp in
       let bs' = bs with <|code := bs.code ++ bc;
                           pc := next_addr bs.inst_length bs.code|> in
       case SWHILE (λbs.
         if bs.pc = next_addr bs.inst_length (bs.code ++ bc) then INR (Success bs)
         else case bc_eval1 bs of NONE => INR (Fail "runtime error") | SOME bs => INL bs)
         bs'
       of | Diverge => INR (Fail "divergence")
          | Terminate (Fail s) => INR (Fail s)
          | Terminate (Success bs'') =>
       (* let vals = extract_bindings rs' bs'' in *)
       let v = HD bs''.stack in
       INL (rs',bs'',inp,(out ++ "\n" ++ (ov_to_string (bv_to_ov (FST (SND rs'.contab)) v)))))
  (init_repl_state,init_bc_state,s,"")`

val _ = export_theory()
