(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     satSemTheory lprTheory lpr_listTheory lpr_arrayPackingProgTheory
     lpr_parsingTheory lpr_arrayPackingCompileTheory lpr_composeProgTheory
     lpr_listTheory packingTheory;

val _ = new_theory"lpr_arrayPackingProof";

val main_io_events_def = new_specification("main_io_events_def",["main_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (main_sem,main_output) = main_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (main_not_fail,main_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail main_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct lpr_packing_compiled
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

(* A standard run of packing satisfying all the default assumptions *)
val packing_run_def = Define`
  packing_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 main_code mc ms`

Theorem parse_numbers_imp:
  parse_numbers rs ks cs = SOME (r,k,c) ⇒
  c ≥ 1 ∧ c ≤ k
Proof
  rw[parse_numbers_def]>>
  every_case_tac>>fs[]
QED

Theorem machine_code_sound:
  packing_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (main_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (main_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 4 then
    case parse_numbers (EL 1 cl) (EL 2 cl) (EL 3 cl) of
      SOME (r,k,c) =>
        ∃fml.
          out = concat (print_dimacs fml) ∧
          (unsatisfiable (interp fml) ⇒
            ∀f. ¬ is_plane_packing_col f k)
    | NONE => out = strlit ""
  else out = strlit ""
Proof
  strip_tac>>
  fs[installed_x64_def,main_code_def,packing_run_def]>>
  drule main_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  Cases_on`cl`>>fs[]
  >- (
    (* 0 arg *)
    fs[CommandLineProofTheory.wfcl_def])>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  reverse (TOP_CASE_TAC>>fs[])
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  simp[check_unsat_3_sem_def]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  PairCases_on`x`>>simp[]>>
  qmatch_goalsub_abbrev_tac`add_stdout fs ls`>>
  qexists_tac`ls`>>qexists_tac`strlit ""`>>
  `add_stderr fs (strlit "") = fs` by
    (match_mp_tac (GEN_ALL add_stdo_nil)>>
    metis_tac[STD_streams_stderr])>>
  simp[Abbr`ls`]>>
  drule parse_numbers_imp>>
  strip_tac>>
  metis_tac[unsat_is_plane_packing]
QED

val _ = export_theory();
