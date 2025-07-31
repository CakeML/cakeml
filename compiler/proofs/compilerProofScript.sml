(*
  Prove top-level correctness theorem for complete compiler, i.e. the
  combination of parsing, type inference, compiler backend.
*)
Theory compilerProof
Ancestors
  compiler semantics targetSem evaluateProps typeSound
  typeSoundInvariants pegSound pegComplete infer inferSound
  inferComplete inferProps envRel backendProof
Libs
  preamble

val _ = diminish_srw_ss ["ABBREV"]

Definition config_ok_def:
  config_ok (cc:α compiler$config) mc ⇔
    env_rel prim_tenv cc.inferencer_config ∧
    inf_set_tids_ienv prim_type_ids cc.inferencer_config ∧ (* TODO: ok? *)
    ¬cc.input_is_sexp ∧
    ¬cc.exclude_prelude ∧
    ¬cc.skip_type_inference ∧
    ¬cc.only_print_types ∧
    ¬cc.only_print_sexp ∧
    backend_config_ok cc.backend_config ∧
    mc_conf_ok mc ∧ mc_init_ok cc.backend_config mc
End

Definition initial_condition_def:
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
    ¬cc.only_print_types ∧
    ¬cc.only_print_sexp ∧
    backend_config_ok cc.backend_config ∧
    mc_conf_ok mc ∧ mc_init_ok cc.backend_config mc
End

Theorem parse_prog_correct:
  (parse_prog s = Failure y1 y2 ⇒ parse s = NONE) ∧
  (parse_prog s = Success x1 a x2 ⇒ parse s = SOME a)
Proof
  metis_tac[parserProofTheory.parse_prog_correct0]
QED

Theorem infertype_prog_correct:
   env_rel st.tenv ienv ∧
   st.type_ids = count start_type_id ∧
   inf_set_tids_ienv (count start_type_id) ienv ∧
   set_tids_tenv (count start_type_id) st.tenv
   ⇒
   ∃c' x. infertype_prog ienv p = if can_type_prog st p then Success c' else Failure x
Proof
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
  \\ rfs[DISJOINT_SYM]
QED

Theorem compile_tap_compile:
  ∀conf p res td.
    backend_passes$compile_tap conf p = (res,td) ⇒
    backend$compile conf p = res
Proof
  metis_tac [backend_passesTheory.compile_alt,FST]
QED

Definition read_limits_def:
  read_limits cc mc ms = backendProof$read_limits cc.backend_config mc ms
End

Definition is_safe_for_space_def:
  is_safe_for_space ffi cc = backendProof$is_safe_for_space ffi cc.backend_config
End

Theorem compile_correct_gen:
   ∀(st:'ffi semantics$state) (cc:α compiler$config) prelude input mc data_sp cbspace.
    initial_condition st cc mc ⇒
    case FST (compiler$compile cc prelude input) of
    | Failure (ParseError e) => semantics st prelude input = CannotParse
    | Failure (TypeError e) => semantics st prelude input = IllTyped
    | Failure AssembleError => T (* see theorem about to_lab to avoid AssembleError *)
    | Failure (ConfigError e) => T (* configuration string is malformed *)
    | Success (code,data,c) =>
      ∃behaviours source_decs.
        (semantics st prelude input = Execute behaviours) ∧
        parse (lexer_fun input) = SOME source_decs ∧
        ∀ms.
          installed code cbspace data data_sp c.lab_conf.ffi_names
            (heap_regs cc.backend_config.stack_conf.reg_names) mc c.lab_conf.shmem_extra ms
            ⇒
            machine_sem mc st.sem_st.ffi ms ⊆
              extend_with_resource_limit'
                (is_safe_for_space st.sem_st.ffi cc
                   (prelude ++ source_decs) (read_limits cc mc ms))
                behaviours
Proof
  rpt strip_tac
  \\ simp[compilerTheory.compile_def,read_limits_def,is_safe_for_space_def]
  \\ qpat_abbrev_tac `tt = if _ then _ else _`
  \\ BasicProvers.CASE_TAC
  \\ fs[initial_condition_def,Abbr`tt`]
  \\ fs[parse_cml_input_def]
  \\ BasicProvers.CASE_TAC
  \\ fs[initial_condition_def]
  \\ imp_res_tac parse_prog_correct
  \\ simp[semantics_def]
  \\ drule (GEN_ALL infertype_prog_correct)
  \\ simp[]
  \\ rename [‘infertype_prog cc.inferencer_config (_ ++ x45)’]
  \\ disch_then(qspec_then`prelude++x45`mp_tac)
  \\ qhdtm_assum`type_sound_invariant`
       (strip_assume_tac o
        SIMP_RULE std_ss [typeSoundInvariantsTheory.type_sound_invariant_def])
  \\ rfs[]
  \\ strip_tac \\ simp[]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[semantics_def]
  \\ rpt (BasicProvers.CASE_TAC \\ simp[])
  \\ fs[]
  \\ drule compile_tap_compile
  \\ rpt strip_tac
  \\ (backendProofTheory.compile_correct'
      |> SIMP_RULE std_ss [LET_THM,UNCURRY]
      |> Q.INST [‘ev’|->‘NONE’]
      |> REWRITE_RULE [add_eval_state_def]
      |> GEN_ALL
      |> drule)
  \\ simp[]
  \\ disch_then(qspec_then`st.sem_st.ffi`mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars["ffi"])))
  \\ qpat_x_assum`_ = THE _`(assume_tac o SYM)
  \\ simp [AC CONJ_COMM CONJ_ASSOC]
  \\ disch_then (match_mp_tac o MP_CANON)
  \\ simp [RIGHT_EXISTS_AND_THM]
  \\ fs[can_type_prog_def,opt_eval_config_wf_def]
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
  \\ metis_tac[]
QED

Theorem compile_correct_lemma:
  ∀(ffi:'ffi ffi_state) prelude input (cc:α compiler$config) mc data_sp cbspace.
    config_ok cc mc ⇒
    case FST (compiler$compile cc prelude input) of
    | Failure (ParseError e) => semantics_init ffi prelude input = CannotParse
    | Failure (TypeError e) => semantics_init ffi prelude input = IllTyped
    | Failure AssembleError => T (* see theorem about to_lab to avoid AssembleError *)
    | Failure (ConfigError e) => T (* configuration string is malformed *)
    | Success (code,data,c) =>
      ∃behaviours source_decs.
        (semantics_init ffi prelude input = Execute behaviours) ∧
        parse (lexer_fun input) = SOME source_decs ∧
        ∀ms.
          installed code cbspace data data_sp c.lab_conf.ffi_names (heap_regs cc.backend_config.stack_conf.reg_names) mc c.lab_conf.shmem_extra ms ⇒
            machine_sem mc ffi ms ⊆
              extend_with_resource_limit'
                (is_safe_for_space ffi cc
                   (prelude ++ source_decs) (read_limits cc mc ms))
                behaviours
Proof
  rw[semantics_init_def]
  \\ qmatch_goalsub_abbrev_tac`semantics$semantics st`
  \\ `(FST(THE(prim_sem_env ffi))).ffi = ffi` by simp[primSemEnvTheory.prim_sem_env_eq]
  \\ Q.ISPEC_THEN`st`mp_tac compile_correct_gen
  \\ fs[Abbr`st`]
  \\ disch_then match_mp_tac
  \\ fs[initial_condition_def,config_ok_def]
  \\ Cases_on`THE (prim_sem_env ffi)` \\ fs[]
  \\ reverse conj_tac >- (
    conj_asm1_tac >- (
      EVAL_TAC
      \\ rewrite_tac[SUBSET_DEF]
      \\ EVAL_TAC
      \\ strip_tac
      \\ strip_tac \\ rveq \\ EVAL_TAC )
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ rpt conj_tac \\ Cases \\ EVAL_TAC \\ rewrite_tac[]
      \\ gen_tac
      \\ pairarg_tac
      \\ rveq
      \\ EVAL_TAC
      \\ rewrite_tac[bool_case_eq, SOME_11, PAIR_EQ]
      \\ rewrite_tac[CONV_RULE (LAND_CONV SYM_CONV) bool_case_eq, SOME_11, PAIR_EQ]
      \\ strip_tac \\ rveq \\ EVAL_TAC
      >- rw[]
      \\ fs[] )
    \\ fs[])
  \\ match_mp_tac primSemEnvTheory.prim_type_sound_invariants
  \\ simp[]
QED

Theorem compile_correct_safe_for_space:
  ∀(ffi:'ffi ffi_state) prelude input (cc:α compiler$config) mc data_sp cbspace code data c c'.
    config_ok cc mc ⇒
    compiler$compile cc prelude input = (Success (code,data,c), c') ⇒
      ∃behaviours source_decs.
        (semantics_init ffi prelude input = Execute behaviours) ∧
        parse (lexer_fun input) = SOME source_decs ∧
        ∀ms.
          is_safe_for_space ffi cc (prelude ++ source_decs)              (* cost semantics *)
            (read_limits cc mc ms) ∧
          installed code cbspace data data_sp c.lab_conf.ffi_names
            (heap_regs cc.backend_config.stack_conf.reg_names) mc c.lab_conf.shmem_extra ms ⇒
          machine_sem mc ffi ms = behaviours                             (* <-- equality *)
Proof
  rw [] \\ mp_tac (SPEC_ALL compile_correct_lemma) \\ fs []
  \\ strip_tac \\ fs [] \\ rw []
  \\ fs [semanticsPropsTheory.extend_with_resource_limit'_def]
  \\ first_x_assum drule
  \\ fs [semanticsTheory.semantics_init_def]
  \\ imp_res_tac (MP_CANON semanticsPropsTheory.semantics_deterministic)
  \\ pop_assum mp_tac
  \\ impl_tac THEN1
   (fs [semanticsPropsTheory.state_invariant_def]
    \\ qspec_then `{}` mp_tac (primSemEnvTheory.prim_type_sound_invariants
                             |> INST_TYPE [alpha|->``:'ffi``])
    \\ Cases_on `THE (prim_sem_env ffi)` \\ fs [] \\ metis_tac [])
  \\ strip_tac \\ rveq \\ fs []
  \\ `?x. machine_sem mc ffi ms x` by metis_tac [targetPropsTheory.machine_sem_total]
  \\ fs [SUBSET_DEF,IN_DEF,EXTENSION]
  \\ metis_tac []
QED

Theorem compile_correct = Q.prove(`
  ∀(ffi:'ffi ffi_state) prelude input (cc:α compiler$config) mc data_sp cbspace.
    config_ok cc mc ⇒
    case FST (compiler$compile cc prelude input) of
    | Failure (ParseError e) => semantics_init ffi prelude input = CannotParse
    | Failure (TypeError e) => semantics_init ffi prelude input = IllTyped
    | Failure AssembleError => T (* see theorem about to_lab to avoid AssembleError *)
    | Failure (ConfigError e) => T (* configuration string is malformed *)
    | Success (code,data,c) =>
      ∃behaviours.
        (semantics_init ffi prelude input = Execute behaviours) ∧
        ∀ms.
          installed code cbspace data data_sp c.lab_conf.ffi_names
            (heap_regs cc.backend_config.stack_conf.reg_names) mc c.lab_conf.shmem_extra ms ⇒
          machine_sem mc ffi ms ⊆
            extend_with_resource_limit behaviours
          (* see the compile_correct_safe_for_space version above
             for the one without the ⊆ and extend_with_resource_limit *)`,
  rw [] \\ mp_tac (SPEC_ALL compile_correct_lemma)
  \\ fs [] \\ TOP_CASE_TAC \\ fs []
  \\ rename [‘(Success a,_)’]
  \\ PairCases_on `a` \\ fs [] \\ strip_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ rw []
  \\ match_mp_tac SUBSET_TRANS
  \\ asm_exists_tac \\ fs [semanticsPropsTheory.extend_with_resource_limit'_SUBSET])
  |> check_thm;

Theorem type_config_ok:
   env_rel prim_tenv infer$init_config ∧
   inf_set_tids_ienv prim_type_ids infer$init_config
Proof
  rw [env_rel_def, inf_set_tids_ienv_def, ienv_ok_def, ienv_val_ok_def,
      tenv_ok_def, tenv_ctor_ok_def, tenv_abbrev_ok_def, env_rel_sound_def,
      env_rel_complete_def, init_config_def, primTypesTheory.prim_tenv_def,
      typeSystemTheory.lookup_var_def] >>
  TRY (Cases_on `x`) >>
  rw [namespaceTheory.nsLookupMod_def] >>
  simp [primTypesTheory.prim_type_ids_def, inf_set_tids_subset_def] >>
  rpt (
    irule namespacePropsTheory.nsAll_nsBind >>
    rw [unconvert_t_def, inf_set_tids_def,typeSystemTheory.check_freevars_def]) >>
  rw [typeSystemTheory.prim_type_nums_def]
QED

