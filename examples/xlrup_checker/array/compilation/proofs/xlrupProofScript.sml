(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     cnf_extTheory xlrupTheory xlrup_listTheory xlrup_arrayFullProgTheory
     xlrup_parsingTheory xlrupCompileTheory;

val _ = new_theory"xlrupProof";

val cake_xlrup_io_events_def = new_specification("cake_xlrup_io_events_def",["cake_xlrup_io_events"],
  check_unsat_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_xlrup_sem,cake_xlrup_output) = cake_xlrup_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_xlrup_not_fail,cake_xlrup_sem_sing) = cake_xlrup_sem
  |> SRULE [xlrup_array_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 xlrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_xlrup_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_xlrup_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_xlrup_compiled_thm =
  CONJ compile_correct_applied cake_xlrup_output
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
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_xlrup_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (cake_xlrup_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 2 then
    if inFS_fname fs (EL 1 cl)
    then
      case parse_cnf_ext (all_lines fs (EL 1 cl)) of
        NONE => out = strlit ""
      | SOME fml => out = concat (print_cnf_ext fml)
    else out = strlit ""
  else if LENGTH cl = 3 then
    if out = strlit "s VERIFIED UNSAT\n" then
      inFS_fname fs (EL 1 cl) ∧
      ∃f.
        parse_cnf_ext (all_lines fs (EL 1 cl)) = SOME f ∧
        sols f = {}
    else out = strlit ""
  else
    out = strlit ""
Proof
  strip_tac>>
  fs[installed_x64_def,cake_xlrup_code_def,cake_xlrup_run_def]>>
  drule cake_xlrup_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
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
    qexists_tac`strlit ""` >>
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
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    qexists_tac`strlit "s VERIFIED UNSAT\n"` >>
    qexists_tac`strlit ""`>> simp[]>>
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

val _ = export_theory();
