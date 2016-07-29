open preamble
     compilerTheory
     semanticsTheory targetSemTheory
     evalPropsTheory funBigStepEquivTheory typeSoundTheory bigClockTheory
     pegSoundTheory pegCompleteTheory
     inferSoundTheory inferCompleteTheory
     backendProofTheory

val _ = new_theory"compilerProof";

val config_ok_def = Define`
  config_ok (cc:α compiler$config) mc ⇔
    env_rel prim_tenv cc.inferencer_config.inf_env ∧
    prim_tdecs = convert_decls cc.inferencer_config.inf_decls ∧
    cc.backend_config.source_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).source_conf ∧
    cc.backend_config.mod_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).mod_conf ∧
    cc.backend_config.clos_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).clos_conf ∧
    0 < cc.backend_config.clos_conf.max_app ∧
    backendProof$conf_ok cc.backend_config mc`;

val initial_condition_def = Define`
  initial_condition (st:'ffi top_state) (cc:α compiler$config) mc ⇔
    (st.sem_st,st.sem_env) = THE (prim_sem_env st.sem_st.ffi) ∧
    type_sound_invariants (NONE:(unit,v) semanticPrimitives$result option) (st.tdecs,st.tenv,st.sem_st,st.sem_env) ∧
    env_rel st.tenv cc.inferencer_config.inf_env ∧
    st.tdecs = convert_decls cc.inferencer_config.inf_decls ∧
    cc.backend_config.source_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).source_conf ∧
    cc.backend_config.mod_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).mod_conf ∧
    cc.backend_config.clos_conf = ((prim_config cc.backend_config.clos_conf.max_app):α backend$config).clos_conf ∧
    0 < cc.backend_config.clos_conf.max_app ∧
    backendProof$conf_ok cc.backend_config mc`;

val parse_prog_correct = Q.store_thm("parse_prog_correct",
  `parse_prog = parse`,
  simp[FUN_EQ_THM] \\ gen_tac
  \\ simp[parse_def,cmlParseTheory.parse_prog_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ simp[]
  \\ conj_tac
  >- (
    rpt strip_tac
    \\ drule completeness
    \\ simp[]
    \\ strip_tac
    \\ assume_tac cmlPEGTheory.PEG_wellformed
    \\ drule (GEN_ALL pegexecTheory.peg_eval_executed)
    \\ qmatch_asmsub_abbrev_tac`peg_eval _ (s,e) r`
    \\ disch_then(qspecl_then[`s`,`r`,`e`]mp_tac)
    \\ simp[Abbr`e`,GSYM cmlPEGTheory.pnt_def]
    \\ strip_tac
    \\ simp[cmlParseTheory.destResult_def,Abbr`r`]
    \\ simp[ETA_AX,OPTION_BIND_SOME] )
  \\ qmatch_goalsub_abbrev_tac`opt = NONE`
  \\ Cases_on`opt`\\fs[markerTheory.Abbrev_def]
  \\ strip_tac
  \\ assume_tac cmlPEGTheory.PEG_wellformed
  \\ drule (GEN_ALL pegexecTheory.peg_eval_executed)
  \\ qmatch_asmsub_abbrev_tac`peg_exec cmlPEG e s`
  \\ qmatch_asmsub_abbrev_tac`destResult r`
  \\ Cases_on`r` \\ fs[cmlParseTheory.destResult_def]
  \\ qmatch_asmsub_rename_tac`pegexec$Result r`
  \\ disch_then(qspecl_then[`s`,`r`,`e`]mp_tac)
  \\ fs[markerTheory.Abbrev_def]
  \\ impl_tac >- (
      metis_tac[pegTheory.start_IN_Gexprs,
                SIMP_CONV (srw_ss()) [cmlPEGTheory.cmlPEG_def]``cmlPEG.start``])
  \\ strip_tac
  \\ rveq
  \\ fs[cmlPEGTheory.pnt_def]
  \\ qmatch_asmsub_rename_tac`SOME p`
  \\ Cases_on`p`
  \\ drule peg_sound
  \\ strip_tac \\ rveq \\ simp[]
  \\ Cases_on`ptree_TopLevelDecs pt`\\simp[]
  \\ strip_tac \\ fs[]
  \\ metis_tac[]);

val infertype_prog_correct = Q.store_thm("infertype_prog_correct",
  `env_rel st.tenv c.inf_env ∧
   st.tdecs = convert_decls c.inf_decls ∧
   st.sem_st.defined_mods = st.tdecs.defined_mods ∧
   consistent_decls st.sem_st.defined_types decls_no_sig ∧
   weak_decls_only_mods decls_no_sig st.tdecs
   ⇒
   ∃c'. infertype_prog c p = if can_type_prog st p then SOME c' else NONE`,
  strip_tac
  \\ simp[inferTheory.infertype_prog_def]
  \\ simp[can_type_prog_def]
  \\ qmatch_goalsub_abbrev_tac`FST pp`
  \\ Cases_on`pp` \\ fs[markerTheory.Abbrev_def]
  \\ pop_assum (assume_tac o SYM)
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    ntac 4 BasicProvers.TOP_CASE_TAC
    \\ simp[]
    \\ drule infer_prog_sound
    \\ disch_then drule
    \\ strip_tac
    \\ conj_tac >- ( drule type_no_dup_mods \\ fs[] )
    \\ conj_tac
    >- (
      match_mp_tac (GEN_ALL type_no_dup_top_types)
      \\ asm_exists_tac \\ simp[]
      \\ asm_exists_tac \\ simp[]
      \\ rfs[] )
    \\ asm_exists_tac
    \\ simp[] )
  \\ simp[]
  \\ spose_not_then strip_assume_tac
  \\ `∃a b c d. new_tenv = (a,b,c,d)` by metis_tac[PAIR]
  \\ rveq
  \\ drule (SIMP_RULE(srw_ss())[GSYM AND_IMP_INTRO]infer_prog_complete) (* TODO: why is AND_IMP_INTRO necessary? *)
  \\ disch_then drule
  \\ disch_then(qspec_then`init_infer_state`mp_tac)
  \\ strip_tac \\ fs[]);

val compile_correct_gen = Q.store_thm("compile_correct_gen",
  `∀(st:'ffi top_state) (cc:α compiler$config) prelude input mc.
    initial_condition st cc mc ⇒
    case compiler$compile cc prelude input of
    | Failure ParseError => semantics st prelude input = CannotParse
    | Failure TypeError => semantics st prelude input = IllTyped
    | Failure CompileError => T (* see theorem about to_lab to avoid CompileError *)
    | Success (bytes,ffi_limit) =>
      ∃behaviours.
        (semantics st prelude input = Execute behaviours) ∧
        ∀ms.
          installed (bytes,cc.backend_config,st.sem_st.ffi,ffi_limit,mc,ms) ⇒
            machine_sem mc st.sem_st.ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about to_data to avoid extend_with_resource_limit *)`,
  rpt strip_tac
  \\ simp[compilerTheory.compile_def]
  \\ simp[parse_prog_correct]
  \\ BasicProvers.CASE_TAC
  \\ simp[semantics_def]
  \\ fs[initial_condition_def]
  \\ drule (GEN_ALL infertype_prog_correct)
  \\ simp[]
  \\ disch_then(qspec_then`prelude++x`mp_tac)
  \\ rator_assum`type_sound_invariants`(strip_assume_tac o SIMP_RULE std_ss [typeSoundInvariantsTheory.type_sound_invariants_def])
  \\ rfs[]
  \\ disch_then drule \\ simp[]
  \\ strip_tac \\ simp[]
  \\ IF_CASES_TAC \\ fs[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ rpt strip_tac
  \\ (backendProofTheory.compile_correct
      |> SIMP_RULE std_ss [LET_THM,UNCURRY]
      |> GEN_ALL
      |> drule)
  \\ simp[]
  \\ simp[GSYM AND_IMP_INTRO]
  \\ simp[RIGHT_FORALL_IMP_THM]
  \\ impl_tac >- metis_tac[]
  \\ impl_tac >- metis_tac[]
  \\ simp[GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ simp[GSYM AND_IMP_INTRO] (* TODO: why is this necessary? *)
  \\ disch_then drule
  \\ disch_then(qspec_then`st.sem_st.ffi`mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars["ffi"])))
  \\ qpat_assum`_ = THE _`(assume_tac o SYM)
  \\ simp[]
  \\ disch_then (match_mp_tac o MP_CANON)
  \\ conj_tac >- fs []
  \\ fs[can_type_prog_def]
  \\ Cases_on`prog_diverges st.sem_env st.sem_st (prelude ++ x)`
  >- metis_tac[semanticsPropsTheory.prog_diverges_semantics_prog]
  \\ drule whole_prog_type_soundness
  \\ rfs[]
  \\ `∃a b c d. new_tenv = (a,b,c,d)` by metis_tac[PAIR]
  \\ rveq
  \\ disch_then drule
  \\ strip_tac
  \\ simp[semantics_prog_def,evaluate_prog_with_clock_def]
  \\ gen_tac \\ pairarg_tac \\ fs[]
  \\ imp_res_tac functional_evaluate_prog
  \\ qpat_assum`_ ⇒ _`mp_tac
  \\ simp[PULL_EXISTS]
  \\ rfs[bigStepTheory.evaluate_whole_prog_def]
  \\ Cases_on`r' = Rerr (Rabort Rtimeout_error)` \\ fs[]
  \\ imp_res_tac prog_unclocked_ignore \\ fs[] \\ rfs[]
  \\ first_x_assum(qspec_then`st.sem_st.clock`mp_tac)
  \\ simp[with_same_clock] \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ imp_res_tac determTheory.prog_determ
  \\ fs[]);

val code_installed_def = Define `
  code_installed (bytes,cc,ffi,ffi_limit,mc,ms) =
    installed (bytes,cc.backend_config,ffi,ffi_limit,mc,ms)`

val compile_correct = Q.store_thm("compile_correct",
  `∀(ffi:'ffi ffi_state) prelude input (cc:α compiler$config) mc.
    config_ok cc mc ⇒
    case compiler$compile cc prelude input of
    | Failure ParseError => semantics_init ffi prelude input = CannotParse
    | Failure TypeError => semantics_init ffi prelude input = IllTyped
    | Failure CompileError => T (* see theorem about to_lab to avoid CompileError *)
    | Success (bytes,ffi_limit) =>
      ∃behaviours.
        (semantics_init ffi prelude input = Execute behaviours) ∧
        ∀ms.
          code_installed (bytes,cc,ffi,ffi_limit,mc,ms) ⇒
            machine_sem mc ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about to_data to avoid extend_with_resource_limit *)`,
  rw[initSemEnvTheory.semantics_init_def,code_installed_def]
  \\ qmatch_goalsub_abbrev_tac`semantics$semantics st`
  \\ `(FST(THE(prim_sem_env ffi))).ffi = ffi` by simp[initSemEnvTheory.prim_sem_env_eq]
  \\ Q.ISPEC_THEN`st`mp_tac compile_correct_gen
  \\ fs[Abbr`st`]
  \\ disch_then match_mp_tac
  \\ fs[initial_condition_def,config_ok_def]
  \\ qpat_assum`prim_tdecs = _`(SUBST1_TAC o SYM)
  \\ Cases_on`THE (prim_sem_env ffi)`
  \\ match_mp_tac prim_type_sound_invariants
  \\ simp[]);

val _ = export_theory();
