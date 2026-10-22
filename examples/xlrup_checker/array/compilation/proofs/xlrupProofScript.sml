(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory xlrupProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof cnf_ext
  xlrup xlrup_list xlrup_arrayFullProg xlrup_parsing xlrupCompile
Libs
  preamble

val cake_xlrup_terminate = UNDISCH_ALL check_unsat_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [xlrup_array_compiled];

Theorem cake_xlrup_compiled_thm =
  MATCH_MP compile_correct (cj 1 xlrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 cake_xlrup_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_xlrup_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # num list # backend$config))
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

Definition cake_xlrup_code_def:
  cake_xlrup_code = (code, data, info)
End

(* A standard run of cake_xlrup satisfying all the default assumptions *)
Definition cake_xlrup_run_def:
  cake_xlrup_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_xlrup_code mc ms
End

Theorem machine_code_sound:
  cake_xlrup_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 2 then
    if inFS_fname fs (EL 1 cl)
    then
      case parse_cnf_ext (all_lines_file fs (EL 1 cl)) of
        NONE => out = «»
      | SOME fml => out = concat (print_cnf_ext fml)
    else out = «»
  else if LENGTH cl = 3 then
    if out = «s VERIFIED UNSAT\n» then
      inFS_fname fs (EL 1 cl) ∧
      ∃f.
        parse_cnf_ext (all_lines_file fs (EL 1 cl)) = SOME f ∧
        sols f = {}
    else out = «»
  else
    out = «»
Proof
  strip_tac>>
  fs[installed_x64_def,cake_xlrup_code_def,cake_xlrup_run_def]>>
  drule_all cake_xlrup_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  fs[check_unsat_sem_def]>>
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
    (* 1 arg *)
    fs[check_unsat_1_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    qexists_tac`«»` >>
    simp[STD_streams_stderr,add_stdo_nil])>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* 2 arg *)
    fs[check_unsat_2_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`«»`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`«»`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`«»`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`«»`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    qexists_tac`«s VERIFIED UNSAT\n»` >>
    qexists_tac`«»`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    simp[parse_cnf_ext_def]>>
    drule parse_cnf_ext_toks_nz_lit>>
    strip_tac>>
    drule (GEN_ALL xlrup_arrayProgTheory.check_xlrups_unsat_list_sound)>>
    simp[]>>
    rename1`sols (cfml,xfml,bfml)`>>
    impl_tac >- (
      drule parse_xlrups_wf>>
      fs[EVERY_MEM,conv_cfml_def,MEM_MAP,wf_clause_def,PULL_EXISTS,conv_bfml_def]>>
      rw[]>>
      first_x_assum drule>>
      rw[]>>CCONTR_TAC>>fs[]>>first_x_assum drule>>
      rename1`nz_lit l`>>
      Cases_on`l`>>fs[conv_lit_def])>>
    rw[sols_def,EXTENSION,sat_fml_def]>>
    qpat_x_assum`EVERY _ xfml` kall_tac>>
    drule conv_cfml_sound>>
    rw[]>>gvs[])>>
  qexists_tac`err`>>rw[]>>
  metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]
QED
