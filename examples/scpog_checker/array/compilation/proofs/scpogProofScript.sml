(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory scpogProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  x64_config cnf_scpogSem scpog scpog_list scpog_arrayFullProg
  scpog_parsing scpogCompile
Libs
  preamble blastLib

val cake_scpog_io_events_def = new_specification("cake_scpog_io_events_def",["cake_scpog_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_scpog_sem,cake_scpog_output) = cake_scpog_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_scpog_not_fail,cake_scpog_sem_sing) = cake_scpog_sem
  |> SRULE [scpog_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem x64_backend_config_ok':
  backend_config_ok (set_asm_conf x64_config' x64_config)
Proof
  simp[backend_config_ok_def,backendTheory.set_asm_conf_def,x64_config'_def]>>
  rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[x64_configTheory.x64_backend_config_def]
  >- (EVAL_TAC>> blastLib.FULL_BBLAST_TAC)
  >- names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ EVAL_TAC>>fs[]
  \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ fs[]
QED

Theorem x64_init_ok':
   is_x64_machine_config mc ⇒
    mc_init_ok (set_asm_conf x64_config' x64_config) mc
Proof
  rw[mc_init_ok_def] \\
  fs[is_x64_machine_config_def] \\
  EVAL_TAC
QED

Theorem set_asm_conf_stack_conf:
  (set_asm_conf x y).stack_conf = x.stack_conf
Proof
  EVAL_TAC
QED

Theorem x64_config'_stack_conf:
  x64_config'.stack_conf = x64_backend_config.stack_conf
Proof
  EVAL_TAC
QED

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 scpog_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_scpog_not_fail
  |> C MATCH_MP x64_backend_config_ok'
  |> REWRITE_RULE[set_asm_conf_stack_conf,x64_config'_stack_conf]
  |> REWRITE_RULE[cake_scpog_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok'))
  |> DISCH(#1(dest_imp(concl x64_init_ok')))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_scpog_compiled_thm =
  CONJ compile_correct_applied cake_scpog_output
  |> DISCH_ALL
  (* |> check_thm *)

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # 64 backend$config))
    mc ms
  <=>
    ?cbspace data_sp.
      is_x64_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        (heap_regs x64_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
End

Definition cake_scpog_code_def:
  cake_scpog_code = (code, data, info)
End

(* A standard run of cake_scpog satisfying all the default assumptions *)
Definition cake_scpog_run_def:
  cake_scpog_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_scpog_code mc ms
End

Theorem machine_code_sound:
  cake_scpog_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_scpog_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (cake_scpog_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 3 then
    out ≠ strlit "" ⇒
    ∃mv ncl vs fml scpsteps
      res arr1 arr2.
      let pc = mk_pc mv ncl vs in
        get_prob fs (EL 1 cl) = SOME (mv,ncl,vs,fml) ∧
        get_scpog fs (EL 2 cl) = SOME scpsteps ∧
        check_scp_final_list scpsteps pc arr1 init_sc arr2 = SOME res ∧
        if out = strlit "s VERIFIED UNSAT\n" then
          res = INL () ∧
          {w | sat_fml w (set fml)} = ∅
        else
          ∃r scp.
          res = INR (r,scp) ∧
          out = strlit "s VERIFIED CPOG REPRESENTATION\n" ∧
          models (get_data_vars pc) (sat_scp F r scp) =
          models (get_data_vars pc) {w | sat_fml w (set fml)} ∧
          decomposable_scp F r scp ∧ deterministic_scp F r scp
  else
    out = strlit ""
Proof
  strip_tac>>
  fs[installed_x64_def,cake_scpog_code_def,cake_scpog_run_def]>>
  drule cake_scpog_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  Cases_on`cl`>>fs[]
  >- (
    (* 0 arg *)
    fs[]>>
    qexists_tac`err`>>rw[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  TOP_CASE_TAC >> fs[] >- (
    qexists_tac`err`>>rw[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  TOP_CASE_TAC
  >- (
    qexists_tac`strlit ""` >>
    qexists_tac`err`>>rw[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* 2 arg *)
    fs[check_unsat_2_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    PairCases_on`x`>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>gvs[]
    >- (
      qexists_tac`strlit ""`>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    rename1` add_stdout _ (print_result res)`>>
    qexists_tac`print_result res`>>
    qexists_tac`strlit ""`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    gvs[get_prob_def,get_scpog_def]>>
    strip_tac>>
    first_assum (irule_at Any)>>
    drule_at Any check_scp_final_list_sound>>
    impl_tac >- (
      drule parse_ext_dimacs_toks_props>>
      strip_tac>>
      rw[mk_pc_def,good_pc_def]
      >- (
        simp[get_data_vars_def]>>
        TOP_CASE_TAC>>gvs[])>>
      ‘lpr$wf_clause = scpog$wf_clause’ by
        (simp [FUN_EQ_THM,
               lprTheory.wf_clause_def,
               scpogTheory.wf_clause_def]) >>
      gvs[]
      )>>
    TOP_CASE_TAC>>simp[print_result_def]>>
    TOP_CASE_TAC>>simp[print_result_def])>>
  qexists_tac`err`>>rw[]>>
  metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]
QED
