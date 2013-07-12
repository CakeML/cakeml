open HolKernel bossLib boolLib boolSimps lcsymtacs ml_translatorLib ml_translatorTheory miscLib rich_listTheory
open compilerTerminationTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory ml_repl_stepTheory oneshotTheory compile_oneshotTheory sideTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeTerminationTheory
val _ = new_theory"oneshotProofs"

val _ = Globals.max_print_depth := 25

val _ = translation_extends"ml_repl_step"

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

val compiled1 = ONCE_REWRITE_RULE[GSYM bootstrap_result_def]compiled

val [ct,m,renv,rsz,cs] =
compiled1 |> concl |> lhs |> rator |> rand |> strip_pair

val FV_decs_oneshot_decs = prove(``FV_decs oneshot_decs = {Short "input"}``,cheat)
val decs_cns_oneshot_decs = prove(``decs_cns NONE oneshot_decs = {}``,cheat)
val check_dup_ctors_oneshot_decs = prove(``
(∀i tds.
    i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i oneshot_decs))
              tds)``, cheat)

val no_closures_all_vlabs = store_thm("no_closures_all_vlabs",
  ``∀v. ¬contains_closure v ⇒ all_vlabs (v_to_Cv mv m v)``,
  ho_match_mp_tac contains_closure_ind >>
  simp[contains_closure_def,compilerTerminationTheory.v_to_Cv_def] >>
  simp[pmatchTheory.vs_to_Cvs_MAP,EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM])

val no_closures_vlabs = store_thm("no_closures_vlabs",
  ``∀v. ¬contains_closure v ⇒ vlabs (v_to_Cv mv m v) = {}``,
  ho_match_mp_tac contains_closure_ind >>
  simp[compilerTerminationTheory.v_to_Cv_def,contains_closure_def] >>
  simp[contains_closure_def,compilerTerminationTheory.v_to_Cv_def,intLangExtraTheory.vlabs_list_MAP] >>
  simp[pmatchTheory.vs_to_Cvs_MAP,EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,miscTheory.IMAGE_EQ_SING])

val no_closures_Cv_bv = store_thm("no_closures_Cv_bv",
  ``∀Cv. no_closures Cv ⇒ ∀bv pp pp'. (FST pp').sm = (FST pp).sm ∧ Cv_bv pp Cv bv ⇒ Cv_bv pp' Cv bv``,
  ho_match_mp_tac compilerTerminationTheory.no_closures_ind >>
  simp[] >> rw[] >>
  TRY (
    simp[Once Cv_bv_cases] >>
    fs[Once Cv_bv_cases] >>
    NO_TAC) >>
  REWRITE_TAC[Once Cv_bv_cases] >>
  simp[] >>
  pop_assum mp_tac >>
  REWRITE_TAC[Once Cv_bv_cases] >>
  simp[] >> rw[] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[MEM_EL])

val no_closures_no_locs_Cv_bv = store_thm("no_closures_no_locs_Cv_bv",
  ``∀Cv. no_closures Cv ∧ all_Clocs Cv = {} ⇒ ∀bv pp pp'. Cv_bv pp Cv bv ⇒ Cv_bv pp' Cv bv``,
  ho_match_mp_tac compilerTerminationTheory.no_closures_ind >>
  simp[] >> rw[] >>
  TRY (
    simp[Once Cv_bv_cases] >>
    fs[Once Cv_bv_cases] >>
    NO_TAC) >>
  REWRITE_TAC[Once Cv_bv_cases] >> simp[] >>
  pop_assum mp_tac >>
  REWRITE_TAC[Once Cv_bv_cases] >> simp[] >> rw[] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  PairCases_on`pp`>>fs[]>>
  fs[miscTheory.IMAGE_EQ_SING] >>
  simp[EXISTS_PROD] >>
  metis_tac[MEM_EL])

val no_closures_v_to_Cv = store_thm("no_closures_v_to_Cv",
  ``∀v mv m. no_closures (v_to_Cv mv m v) ⇔ ¬contains_closure v``,
  ho_match_mp_tac contains_closure_ind >>
  simp[v_to_Cv_def,contains_closure_def] >>
  simp[pmatchTheory.vs_to_Cvs_MAP,EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM])

(*
val no_locs_Cv_bv = store_thm("no_locs_Cv_bv",
``∀Cv bv. all_Clocs Cv = {} ⇒ ∀bv pp pp'. (FST pp').cls = (FST pp).cls ∧ (SND pp') = SND pp ∧  Cv_bv pp Cv bv ⇒ Cv_bv pp' Cv bv``,
  ho_match_mp_tac intLangExtraTheory.all_Clocs_ind >>
  simp[] >> rw[] >>
  TRY (
    simp[Once Cv_bv_cases] >>
    fs[Once Cv_bv_cases] >>
    NO_TAC) >>
  >- (
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >>
    pop_assum mp_tac >>
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >> rw[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    PairCases_on`pp`>>PairCases_on`pp'`>>fs[]>>
    fs[miscTheory.IMAGE_EQ_SING] >>
    simp[EXISTS_PROD] >>
    metis_tac[MEM_EL])
  >- (
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >>
    pop_assum mp_tac >>
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >> rw[] >>
    PairCases_on`pp'`>>fs[]>>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    PairCases_on`pp`>>PairCases_on`pp'`>>fs[]>>
    fs[miscTheory.IMAGE_EQ_SING] >>
    simp[EXISTS_PROD] >>
    metis_tac[MEM_EL])
*)

val result_state = EVAL``let (ct,m,renv,rsz,cs) = bootstrap_result in (rsz,LENGTH m.bvars,m.bvars)``

val HD_new_vs_oneshot_decs = prove(
  ``∃xs. new_decs_vs oneshot_decs = "it"::xs``,
  simp[oneshot_decs_def] >>
  simp[pat_bindings_def])

val oneshot_thm = store_thm("oneshot_thm",
  ``∀i s cenv env.
      evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧
      closed [] i ∧ all_cns i = {} ∧ all_locs i = {} ∧ ¬(contains_closure i)
      ⇒
      let (ct,m,renv,rsz,cs) = bootstrap_result in
      ∀bs bi pp.
        bs.code = REVERSE cs.out
      ∧ bs.pc = 0
      ∧ bs.stack = [bi]
      ∧ bs.clock = NONE
      ∧ Cv_bv pp (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i) bi
      ⇒ ∃bs' Cv bv st rd.
        bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ bs'.stack = bv::st
      ∧ syneq (v_to_Cv FEMPTY (cmap ct) (THE (lookup "it" env))) Cv
      ∧ Cv_bv (mk_pp rd bs') Cv bv``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`[]`,`[]`,`[("input",i)]`,`oneshot_decs`,`(s,cenv,Rval env)`]mp_tac compile_decs_thm >>
  simp[compile_decs_FOLDL] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  disch_then(qspecl_then[`^m`,`^cs`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))) >>
  disch_then(qspecl_then[`init_compiler_state with <|renv:=[("input",0)];rsz:=1|>`,`0`,`<|sm:=[];cls:=FEMPTY|>`
                        ,`bs with <|clock := SOME ck|>`]mp_tac) >>
  assume_tac(prove(``init_compiler_state.rmenv = FEMPTY``,rw[CompilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.renv = []``,rw[CompilerTheory.init_compiler_state_def])) >>
  simp[compiled1] >>
  disch_then(qspecl_then[`[]`,`REVERSE cs.out`]mp_tac) >>
  simp[FV_decs_oneshot_decs,decs_cns_oneshot_decs,check_dup_ctors_oneshot_decs] >>
  discharge_hyps >- (
    conj_tac >- (
      simp[closed_context_def,closed_under_cenv_def,closed_under_menv_def] ) >>
    conj_tac >- (
      simp[env_rs_def] >>
      assume_tac (GEN_ALL env_rs_empty) >>
      fs[env_rs_def,LET_THM] >>
      pop_assum(qspecl_then[`<|sm:=[];cls:=FEMPTY|>`,`ARB`,`<|stack:=[];clock:=NONE|>`]mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac`env_to_Cenv FEMPTY (cmap init_compiler_state.contab) [("input",i)]` >>
      simp[] >>
      simp[Once pmatchTheory.env_to_Cenv_MAP] >>
      simp[closed_Clocs_def,closed_vlabs_def] >>
      conj_tac >- ( simp[all_Clocs_v_to_Cv] ) >>
      conj_tac >- (
        simp[pmatchTheory.env_to_Cenv_MAP,no_closures_all_vlabs] >>
        simp[intLangExtraTheory.all_vlabs_menv_def,intLangExtraTheory.vlabs_menv_def] >>
        simp[no_closures_vlabs] ) >>
      simp[Cenv_bs_def] >>
      simp[s_refs_def,good_rd_def,finite_mapTheory.FEVERY_DEF] >>
      simp[env_renv_def,CompilerLibTheory.el_check_def,pmatchTheory.env_to_Cenv_MAP] >>
      match_mp_tac (MP_CANON no_closures_no_locs_Cv_bv) >>
      simp[no_closures_v_to_Cv] >>
      simp[all_Clocs_v_to_Cv] >>
      metis_tac[] ) >>
    simp[good_labels_def] ) >>
  strip_tac >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  qmatch_assum_abbrev_tac`RTC bc_next bs1 bs2` >>
  `bc_next^* (bs1 with code := bs.code) (bs2 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs1`,`bs2`] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
  qmatch_assum_abbrev_tac`RTC bc_next bs1 bs2` >>
  qexists_tac`bs2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
    `bs1 = bs` by (
      simp[Abbr`bs1`,bc_state_component_equality] ) >>
    fs[] >>
    `bc_fetch bs2 = NONE` by (
      simp[bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      imp_res_tac RTC_bc_next_preserves >> fs[] >>
      simp[Abbr`bs2`] ) >>
    simp[bc_eval1_thm,bc_eval1_def] ) >>
  conj_tac >- simp[Abbr`bs2`] >>
  rator_x_assum`env_rs`mp_tac >>
  simp[env_rs_def] >> strip_tac >>
  rator_x_assum`Cenv_bs`mp_tac >>
  simp[Cenv_bs_def] >> strip_tac >>
  rator_x_assum`env_renv`mp_tac >>
  simp[env_renv_def] >>
  `rsz = 371 ∧ LENGTH m.bvars = 371 ∧ ∃junk. m.bvars = "it"::junk` by (
    mp_tac result_state >> simp[] ) >>
  simp[MAP_ZIP,MAP_GENLIST] >>
  Cases_on`bvs`>>fs[] >>
  simp[EVERY2_EVERY,miscTheory.option_case_NONE_F] >>
  simp[EVERY_MEM,GSYM AND_IMP_INTRO,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  strip_tac >>
  disch_then(qspec_then`0`mp_tac) >>
  simp[] >>
  simp[GENLIST_CONS] >>
  simp[CompilerLibTheory.el_check_def] >>
  imp_res_tac evaluate_decs_new_decs_vs >> fs[] >>
  assume_tac HD_new_vs_oneshot_decs >> fs[] >>
  Cases_on`env`>>fs[] >>
  simp[REVERSE_APPEND,EL_APPEND1,EL_APPEND2,ADD1] >>
  qmatch_assum_rename_tac`FST p = "it"`[]>>
  PairCases_on`p` >> fs[] >>
  fs[pmatchTheory.env_to_Cenv_MAP] >>
  strip_tac >>
  simp[Abbr`bs2`] >>
  HINT_EXISTS_TAC >>
  simp[] >>
  qexists_tac`rd'` >>
  simp[])

val _ = export_theory()
