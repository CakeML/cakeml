(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     cnfProgTheory
     satSemTheory cnfCompileTheory;

val _ = new_theory"cnfProof";

val main_io_events_def = new_specification("main_io_events_def",["main_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (main_sem,main_output) = main_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (main_not_fail,main_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail main_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct cnf_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP main_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[main_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val main_compiled_thm =
  CONJ compile_correct_applied main_output
  |> DISCH_ALL
  (* |> check_thm *)
  |> curry save_thm "main_compiled_thm";

(* Prettifying the standard parts of all the theorems *)
val installed_x64_def = Define `
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
        (heap_regs x64_backend_config.stack_conf.reg_names) mc ms
    `;

val main_code_def = Define `
  main_code = (code, data, config)
  `;

(* A standard run of cake_lpr satisfying all the default assumptions *)
val cake_lpr_run_def = Define`
  cake_lpr_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 main_code mc ms`

Theorem machine_code_sound:
  cake_lpr_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (main_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (main_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if out = strlit "s VERIFIED UNSAT\n" then
    LENGTH cl = 3 ∧
    inFS_fname fs (EL 1 cl) ∧
    ∃fml.
      parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
      unsatisfiable (interp fml)
  else out = strlit ""
Proof
  strip_tac>>
  fs[installed_x64_def,main_code_def,cake_lpr_run_def]>>
  drule main_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  every_case_tac>>fs[]
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_2_sem_def,success_string_def]>>
    IF_CASES_TAC>>fs[get_fml_def])>>
  metis_tac[]
QED

val _ = export_theory();
