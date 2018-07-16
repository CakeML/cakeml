open preamble
     compilerTheory
     semanticsTheory targetSemTheory
     evaluatePropsTheory typeSoundTheory
     pegSoundTheory pegCompleteTheory
     inferSoundTheory inferCompleteTheory
     backendProofTheory

val _ = new_theory"compilerProof";

val config_ok_def = Define`
  config_ok (cc:α compiler$config) mc ⇔
    env_rel prim_tenv cc.inferencer_config ∧
    ¬cc.input_is_sexp ∧
    ¬cc.exclude_prelude ∧
    ¬cc.skip_type_inference ∧
    backend_config_ok cc.backend_config ∧ mc_conf_ok mc ∧ mc_init_ok cc.backend_config mc`;

val initial_condition_def = Define`
  initial_condition (st:'ffi semantics$state) (cc:α compiler$config) mc ⇔
    (st.sem_st,st.sem_env) = THE (prim_sem_env st.sem_st.ffi) ∧
    (?ctMap.
      type_sound_invariant st.sem_st st.sem_env ctMap FEMPTY {} st.tenv ∧
      FRANGE ((SND o SND) o_f ctMap) ⊆ st.type_ids (* TODO: is this OK? *)) ∧
    env_rel st.tenv cc.inferencer_config ∧
    (* TODO: are these consistent (with the rest)? necessary? *)
    st.type_ids = count start_type_id ∧
    set_tids_tenv (count start_type_id) st.tenv ∧
    inf_set_tids_ienv (count start_type_id) cc.inferencer_config ∧
    (* -- *)
    ¬cc.input_is_sexp ∧
    ¬cc.exclude_prelude ∧
    ¬cc.skip_type_inference ∧
    backend_config_ok cc.backend_config ∧ mc_conf_ok mc ∧ mc_init_ok cc.backend_config mc`;

val parse_prog_correct = Q.store_thm("parse_prog_correct",
  `parse_prog = parse`,
  simp[FUN_EQ_THM] \\ gen_tac
  \\ simp[parse_def,cmlParseTheory.parse_prog_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ simp[]
  \\ conj_tac
  >- (
    (* some = SOME case *)
    rpt strip_tac
    \\ drule completeness
    \\ simp[MAP_MAP_o]
    \\ strip_tac
    \\ assume_tac cmlPEGTheory.PEG_wellformed
    \\ drule (GEN_ALL pegexecTheory.peg_eval_executed)
    \\ qmatch_asmsub_abbrev_tac`peg_eval _ (s,e) r`
    \\ disch_then(qspecl_then[`s`,`r`,`e`]mp_tac)
    \\ simp[Abbr`e`,GSYM cmlPEGTheory.pnt_def]
    \\ strip_tac
    \\ simp[cmlParseTheory.destResult_def,Abbr`r`]
    \\ simp[ETA_AX,OPTION_BIND_SOME])
  (* some = NONE case *)
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
  \\ qpat_x_assum`Result r = _`(assume_tac o SYM)
  \\ Cases_on`r` \\ fs[cmlParseTheory.destResult_def]
  \\ rveq
  \\ drule peg_sound
  \\ strip_tac \\ rveq \\ simp[]
  \\ Cases_on`ptree_TopLevelDecs pt`\\simp[]
  \\ strip_tac \\ fs[MAP_MAP_o]
  \\ metis_tac[]);

val infertype_prog_correct = Q.store_thm("infertype_prog_correct",
  `env_rel st.tenv ienv ∧
   st.type_ids = count start_type_id ∧
   inf_set_tids_ienv (count start_type_id) ienv ∧
   set_tids_tenv (count start_type_id) st.tenv
   ⇒
   ∃c' x. infertype_prog ienv p = if can_type_prog st p then Success c' else Failure x`,
  strip_tac
  \\ simp[inferTheory.infertype_prog_def,
          ml_monadBaseTheory.run_def,ml_monadBaseTheory.st_ex_bind_def]
  \\ qmatch_goalsub_abbrev_tac`infer_ds ienv p st0`
  \\ Cases_on`infer_ds ienv p st0`
  \\ simp[can_type_prog_def,Abbr`st0`]
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    drule(CONJUNCT2 infer_d_sound)
    \\ disch_then drule
    \\ simp[inferTheory.init_infer_state_def]
    \\ strip_tac
    \\ CASE_TAC \\ fs[]
    \\ pop_assum mp_tac \\ fs[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[set_ids_def, IN_DISJOINT])
  \\ CASE_TAC \\ fs[]
  \\ drule (GEN_ALL infer_ds_complete)
  \\ disch_then drule
  \\ qmatch_asmsub_abbrev_tac`infer_ds _ _ st1`
  \\ disch_then(qspec_then`st1`mp_tac)
  \\ fs[Abbr`st1`, inferTheory.init_infer_state_def]
  \\ rfs[DISJOINT_SYM]);

val compile_correct_gen = Q.store_thm("compile_correct_gen",
  `∀(st:'ffi semantics$state) (cc:α compiler$config) prelude input mc data_sp cbspace.
    initial_condition st cc mc ⇒
    case compiler$compile cc prelude input of
    | Failure ParseError => semantics st prelude input = CannotParse
    | Failure (TypeError e) => semantics st prelude input = IllTyped
    | Failure CompileError => T (* see theorem about to_lab to avoid CompileError *)
    | Failure (ConfigError e) => T (* configuration string is malformed *)
    | Success (code,data,c) =>
      ∃behaviours.
        (semantics st prelude input = Execute behaviours) ∧
        ∀ms.
          installed code cbspace data data_sp c.ffi_names st.sem_st.ffi
            (heap_regs cc.backend_config.stack_conf.reg_names) mc ms
            ⇒
            machine_sem mc st.sem_st.ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about to_data to avoid extend_with_resource_limit *)`,
  rpt strip_tac
  \\ simp[compilerTheory.compile_def]
  \\ simp[parse_prog_correct]
  \\ BasicProvers.CASE_TAC
  \\ fs[initial_condition_def]
  \\ BasicProvers.CASE_TAC
  \\ simp[semantics_def]
  \\ fs[initial_condition_def]
  \\ drule (GEN_ALL infertype_prog_correct)
  \\ simp[]
  \\ disch_then(qspec_then`prelude++x`mp_tac)
  \\ qhdtm_assum`type_sound_invariant`
       (strip_assume_tac o SIMP_RULE std_ss [typeSoundInvariantsTheory.type_sound_invariant_def])
  \\ rfs[]
  \\ strip_tac \\ simp[]
  \\ IF_CASES_TAC \\ fs[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ BasicProvers.CASE_TAC \\ simp[]
  \\ rpt strip_tac
  \\ (backendProofTheory.compile_correct
      |> SIMP_RULE std_ss [LET_THM,UNCURRY]
      |> GEN_ALL
      |> drule)
  \\ simp[]
  \\ disch_then(qspec_then`st.sem_st.ffi`mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars["ffi"])))
  \\ qpat_x_assum`_ = THE _`(assume_tac o SYM)
  \\ simp [AC CONJ_COMM CONJ_ASSOC]
  \\ disch_then (match_mp_tac o MP_CANON)
  \\ simp [RIGHT_EXISTS_AND_THM]
  \\ fs[can_type_prog_def]
  \\ reverse conj_tac >- metis_tac[]
  \\ strip_tac
  \\ drule semantics_type_sound
  \\ disch_then drule \\ simp[]
  \\ simp[typeSoundInvariantsTheory.type_sound_invariant_def]
  \\ asm_exists_tac \\ rw[]
  \\ fs[typeSoundInvariantsTheory.consistent_ctMap_def]
  \\ qexists_tac`FEMPTY` \\ fs[]
  \\ reverse conj_tac >- metis_tac[]
  \\ fs[IN_DISJOINT]
  \\ CCONTR_TAC \\ fs[SUBSET_DEF] \\ rfs[]
  \\ metis_tac[]);

val compile_correct = Q.store_thm("compile_correct",
  `∀(ffi:'ffi ffi_state) prelude input (cc:α compiler$config) mc data_sp cbspace.
    config_ok cc mc ⇒
    case compiler$compile cc prelude input of
    | Failure ParseError => semantics_init ffi prelude input = CannotParse
    | Failure (TypeError e) => semantics_init ffi prelude input = IllTyped
    | Failure CompileError => T (* see theorem about to_lab to avoid CompileError *)
    | Failure (ConfigError e) => T (* configuration string is malformed *)
    | Success (code,data,c) =>
      ∃behaviours.
        (semantics_init ffi prelude input = Execute behaviours) ∧
        ∀ms.
          installed code cbspace data data_sp c.ffi_names ffi (heap_regs cc.backend_config.stack_conf.reg_names) mc ms ⇒
            machine_sem mc ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about to_data to avoid extend_with_resource_limit *)`,
  rw[primSemEnvTheory.semantics_init_def]
  \\ qmatch_goalsub_abbrev_tac`semantics$semantics st`
  \\ `(FST(THE(prim_sem_env ffi))).ffi = ffi` by simp[primSemEnvTheory.prim_sem_env_eq]
  \\ Q.ISPEC_THEN`st`mp_tac compile_correct_gen
  \\ fs[Abbr`st`]
  \\ disch_then match_mp_tac
  \\ fs[initial_condition_def,config_ok_def]
  \\ Cases_on`THE (prim_sem_env ffi)` \\ fs[]
  \\ reverse conj_tac >- cheat
  \\ match_mp_tac prim_type_sound_invariants
  \\ simp[]);

val _ = export_theory();
