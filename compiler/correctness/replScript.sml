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
    code_env_code c c bs.code ∧
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
  ``(∀ez j e. Cexp_pred e ⇒ Cexp_pred(FST(label_closures ez j e)) ∧
              EVERY (Cexp_pred o closure_data_body) (MAP SND (FST(SND(label_closures ez j e))))) ∧
    (∀ez j es. EVERY Cexp_pred es ⇒ EVERY Cexp_pred (FST(label_closures_list ez j es)) ∧
               EVERY (Cexp_pred o closure_data_body) (MAP SND (FST(SND(label_closures_list ez j es))))) ∧
    (∀ez j nz k defs.
    EVERY Cexp_pred (MAP SND defs) ⇒
    EVERY (Cexp_pred o closure_data_body) (MAP SND(FST(SND(label_closures_defs ez j nz k defs)))))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[EVERY_MEM] >> rw[UNCURRY] >>
    simp[EVERY_MEM]) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- (
    simp[UNCURRY] >> rw[] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    fsrw_tac[DNF_ss][EVERY_MAP] >>
    first_x_assum match_mp_tac >>
    metis_tac[pairTheory.pair_CASES,SND] ) >>
  strip_tac >- (
    simp[UNCURRY] >>
    rw[] >>
    PairCases_on`def`>>fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[EVERY_MEM,EVERY_MAP] >> rw[UNCURRY] >> simp[EVERY_MEM] >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[pairTheory.pair_CASES,SND] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- (
    simp[UNCURRY,EVERY_MAP] >>
    rw[] >>
    fsrw_tac[DNF_ss][] >>
    first_x_assum match_mp_tac >>
    PairCases_on`def`>>fs[]>>
    TRY(simp[bind_fv_def]>>NO_TAC)>>
    metis_tac[pairTheory.pair_CASES,SND]))

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
      ALL_DISTINCT (MAP FST c) ∧
      EVERY (Cexp_pred o closure_data_body) (MAP SND c) ∧
      EVERY (combin$C $< s.next_label) (MAP FST c) ∧
      good_code_env (alist_to_fmap c)
      ⇒
      (d = alist_to_fmap c) ∧
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      ALL_DISTINCT (FILTER is_Label code) ∧
      EVERY (λn. MEM n (MAP FST c) ∨ between s.next_label s'.next_label n)
        (MAP dest_Label (FILTER is_Label code)) ∧
      code_env_code d d code ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP FST c)) ⇒ l1 < l2)
        ⇒
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  qspecl_then[`c`,`d`,`s''`]mp_tac FOLDL_cce_aux_thm >>
  simp[Abbr`s''`] >>
  discharge_hyps >- (
    fsrw_tac[ARITH_ss][EVERY_MEM] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER,Abbr`l`] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP] >>
    res_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def,Abbr`l`] >>
    reverse conj_tac >- (disj2_tac >> DECIDE_TAC) >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    rw[] >> res_tac >>
    TRY(metis_tac[]) >>
    disj2_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    simp[code_env_code_def,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
    conj_asm1_tac >- (
      fs[EVERY_MAP,EVERY_FILTER] >>
      fs[EVERY_MEM] >>
      spose_not_then strip_assume_tac >>
      res_tac >>
      fs[between_def,MEM_MAP] >- (
        res_tac >> DECIDE_TAC ) >>
      fs[Abbr`l`] >> DECIDE_TAC ) >>
    simp[FEVERY_DEF,Abbr`d`,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    qx_gen_tac`i` >> strip_tac >>
    first_x_assum(qspec_then`i`mp_tac) >>
    simp[UNCURRY] >> strip_tac >>
    `alist_to_fmap c ' (FST (EL i c)) = SND (EL i c)` by (
      match_mp_tac alistTheory.ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
      match_mp_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
      simp[MEM_EL] >> PROVE_TAC[] ) >>
    simp[] >>
    qexists_tac`cs i`>>simp[] >>
    qexists_tac`Jump (Lab l)::bc0` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP] >>
    fsrw_tac[DNF_ss][MEM_EL] ) >>
  rpt gen_tac >>
  strip_tac >>
  `bc_fetch bs = SOME (Jump (Lab l))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[Abbr`l`,EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

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

val compile_closures_c_SUBMAP = store_thm("compile_closures_c_SUBMAP",
  ``∀d env sz s defs d'. free_labs_defs defs ⊆ FDOM d ∧ d ⊑ d' ⇒ (compile_closures d' env sz s defs = compile_closures d env sz s defs)``,
  rw[compile_closures_def,LET_THM] >>
  AP_TERM_TAC >>
  match_mp_tac FOLDL_CONG >>
  simp[] >>
  Cases >> Cases >>
  simp[push_lab_def] >>
  fsrw_tac[DNF_ss][SUBMAP_DEF,SUBSET_DEF] >>
  strip_tac >>
  match_mp_tac EQ_SYM >>
  AP_TERM_TAC >>
  first_x_assum match_mp_tac >>
  first_x_assum match_mp_tac >>
  HINT_EXISTS_TAC >>
  simp[])

val compile_c_SUBMAP = store_thm("compile_c_SUBMAP",
  ``(∀d env t sz s e d'. free_labs e ⊆ FDOM d ∧ d ⊑ d' ⇒ (compile d' env t sz s e = compile d env t sz s e)) ∧
    (∀d env t sz e n s m d'. free_labs e ⊆ FDOM d ∧ d ⊑ d' ⇒ (compile_bindings d' env t sz e n s m = compile_bindings d env t sz e n s m)) ∧
    (∀d env sz s es d'. free_labs_list es ⊆ FDOM d ∧ d ⊑ d' ⇒ (compile_nts d' env sz s es = compile_nts d env sz s es))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def] >>
    `s'' = s'` suffices_by metis_tac[] >>
    unabbrev_all_tac >>
    match_mp_tac compile_closures_c_SUBMAP >>
    simp[] ) >>
  strip_tac >- (
    rw[compile_def] >>
    AP_TERM_TAC >>
    match_mp_tac compile_closures_c_SUBMAP >>
    simp[] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >> rw[compile_def,LET_THM] ) >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >> rw[compile_def,LET_THM] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def])

val code_env_code_append = store_thm("code_env_code_append",
  ``∀c d code code'. code_env_code c d code ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒
    code_env_code c d (code ++ code')``,
  simp[code_env_code_def,FEVERY_DEF] >> rw[] >>
  res_tac >> HINT_EXISTS_TAC >> simp[] >>
  qexists_tac`bc0`>>simp[])

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
  `EVERY (Cexp_pred o closure_data_body) (MAP SND p1) ∧ Cexp_pred p0` by metis_tac[label_closures_Cexp_pred,FST,SND] >>
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
  qpat_assum`Abbrev(cce = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`s0 = X with out := []` >>
  strip_tac >>
  qspecl_then[`s0`,`p1`]mp_tac compile_code_env_thm >>
  simp[UNCURRY] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST,Abbr`s0`] ) >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`tf = X:call_context` >>
  qspecl_then[`FST cce`,`rs.renv`,`tf`,`rs.rsz`,`SND cce`,`Ce`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
  fs[Abbr`tf`] >>
  simp[REVERSE_APPEND] >>
  first_x_assum(qspecl_then[`bs`,`bc0`]mp_tac) >>
  simp[Abbr`s0`] >>
  discharge_hyps >- (
    simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM,is_Label_rwt] >>
    fs[EVERY_FILTER,is_Label_rwt,EVERY_MEM] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  qspecl_then[`Cc`,`Cs`,`Cenv`,`Ce`,`(Cs',Rval Cv)`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>
  disch_then(qspecl_then[`rd`,`SND cce`,`rs.renv`,`rs.rsz`,`bs1`,`bc0 ++ REVERSE (SND cce).out`,`REVERSE bc`,`bc0 ++ REVERSE (SND cce).out`]mp_tac) >>
  `code_env_code Cc Cc (bc0 ++ REVERSE (SND cce).out)` by (
    simp[Abbr`Cenv`,Abbr`Cs`,env_to_Cenv_MAP,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE,combinTheory.o_DEF,all_Clocs_v_to_Cv,Abbr`bs1`] >>
    simp[code_env_code_def,FILTER_APPEND,ALL_DISTINCT_APPEND,Abbr`Cc`] >>
    conj_tac >- (
      match_mp_tac good_code_env_FUNION >>
      fs[env_rs_def,code_env_code_def] >>
      simp[DISJOINT_DEF,EXTENSION,MEM_GENLIST] >>
      gen_tac >> spose_not_then strip_assume_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][EVERY_MAP,EVERY_FILTER,is_Label_rwt,MEM_FILTER,MEM_GENLIST,between_def] >>
      fsrw_tac[DNF_ss][EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    rfs[env_rs_def,code_env_code_def] >>
    rfs[FEVERY_DEF] >>
    gen_tac >>
    Cases_on`x ∈ FDOM c`>>simp[FUNION_DEF] >- (
      last_x_assum(qspec_then`x`mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac`cs` >>
      Q.PAT_ABBREV_TAC`cp = compile X Y Z A B C` >>
      qmatch_assum_abbrev_tac`cq.out = cc ++ cs.out` >>
      `cp = cq` by (
        map_every qunabbrev_tac[`cp`,`cq`] >>
        match_mp_tac (CONJUNCT1 compile_c_SUBMAP) >>
        simp[SUBMAP_FUNION] >>
        fs[good_code_env_def,IN_FRANGE] >>
        metis_tac[] ) >>
      simp[] >> qexists_tac`bc0'` >> simp[] ) >>
    strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac`cs` >>
    Q.PAT_ABBREV_TAC`cp = compile X Y Z A B C` >>
    qmatch_assum_abbrev_tac`cq.out = cc ++ cs.out` >>
    `cp = cq` by (
      map_every qunabbrev_tac[`cp`,`cq`] >>
      match_mp_tac (CONJUNCT1 compile_c_SUBMAP) >>
      conj_tac >- (
        rfs[good_code_env_def,IN_FRANGE] >>
        metis_tac[] ) >>
      match_mp_tac SUBMAP_FUNION >>
      simp[IN_DISJOINT] >> disj2_tac >>
      gen_tac >> spose_not_then strip_assume_tac >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_GENLIST,SUBSET_DEF] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    simp[] >>
    qexists_tac`bc0 ++ bc0'` >>
    simp[FILTER_APPEND] >>
    fs[EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
    fsrw_tac[DNF_ss][EVERY_MEM] >>
    rw[] >> res_tac >> fs[MEM_GENLIST] >>
    DECIDE_TAC ) >>
  discharge_hyps >- (
    simp[Abbr`Cenv`,Abbr`Cs`,env_to_Cenv_MAP,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE,combinTheory.o_DEF,all_Clocs_v_to_Cv,Abbr`bs1`] >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
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
      qmatch_assum_abbrev_tac`bc_next bs bs1` >>
      qexists_tac`bs1 with code := bc0 ++ code` >>
      simp[bc_state_component_equality,Abbr`bs1`] >>
      match_mp_tac Cenv_bs_append_code >>
      Q.PAT_ABBREV_TAC`pc = SUM (MAP X Y)` >>
      qexists_tac`bs with <| pc := pc ; code := bc0 |>` >>
      simp[bc_state_component_equality,Cenv_bs_with_pc] >>
      match_mp_tac Cenv_bs_c_SUBMAP >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Cc`,SUBMAP_FUNION] ) >>
    fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,MEM_MAP,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,MEM_GENLIST] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  disch_then(qspecl_then[`REVERSE bc`]mp_tac o CONJUNCT1) >>
  qmatch_assum_abbrev_tac`X.out = bc ++ (SND cce).out` >>
  Q.PAT_ABBREV_TAC`Y = compile Cc A B C D E` >>
  `Y = X` by (
    map_every qunabbrev_tac[`X`,`Y`] >>
    match_mp_tac (CONJUNCT1 compile_c_SUBMAP) >>
    rfs[] >>
    simp[Abbr`Cc`] >>
    match_mp_tac SUBMAP_FUNION >>
    simp[DISJOINT_DEF,EXTENSION] >>
    fs[SUBSET_DEF,MEM_GENLIST] >>
    disj2_tac >> spose_not_then strip_assume_tac >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  simp[Abbr`bs1`] >>
  simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
  map_every qx_gen_tac[`rf`,`rd'`,`bv`] >> strip_tac >>
  map_every qexists_tac[`bv`,`rf`,`rd'`,`Cc`] >>
  conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  conj_tac >- (
    match_mp_tac EQ_TRANS >>
    qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm Cv` >>
    conj_tac >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac EQ_TRANS >>
      qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm (v_to_Cv (cmap rs.contab) v)` >>
      conj_tac >- (
        match_mp_tac EQ_SYM >>
        match_mp_tac EQ_TRANS >>
        qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm Cv0` >>
        conj_tac >- (
          match_mp_tac (CONJUNCT1 syneq_ov) >>
          HINT_EXISTS_TAC >> simp[] ) >>
        match_mp_tac (CONJUNCT1 syneq_ov) >>
        HINT_EXISTS_TAC >> simp[] ) >>
      match_mp_tac (CONJUNCT1 v_to_Cv_ov) >>
      qabbrev_tac`ct=rs.contab` >>
      PairCases_on`ct` >> fs[good_contab_def] >>
      qspecl_then[`cenv`,`s`,`env`,`exp`,`s',Rval v`]mp_tac (CONJUNCT1 evaluate_all_cns) >>
      fs[good_cmap_def,closed_under_cenv_def] >>
      fs[SUBSET_DEF,MEM_MAP,EXISTS_PROD] >>
      metis_tac[]) >>
    match_mp_tac (MP_CANON Cv_bv_ov) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  conj_tac >- (
    match_mp_tac code_env_code_append >>
    rfs[Abbr`cce`] >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    simp[MEM_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
    fsrw_tac[DNF_ss][EVERY_MAP,EVERY_FILTER,is_Label_rwt,MEM_GENLIST,between_def] >>
    fsrw_tac[DNF_ss][EVERY_MEM] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    rfs[Abbr`Cc`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  match_mp_tac Cenv_bs
  fs[Cenv_bs_def]
  DB.find"Cenv_bs"
  Cenv_bs

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
