(*
  Compose the LPR semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     lprTheory parsingTheory lprProgTheory lprCompileTheory

val _ = new_theory"lprProof";

val check_unsat_io_events_def = new_specification("check_unsat_io_events_def",["check_unsat_io_events"],
  check_unsat_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (check_unsat_sem,check_unsat_output) = check_unsat_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (check_unsat_not_fail,check_unsat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail check_unsat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct lpr_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP check_unsat_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[check_unsat_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val check_unsat_compiled_thm =
  CONJ compile_correct_applied check_unsat_output
  |> DISCH_ALL
  |> check_thm
  |> curry save_thm "check_unsat_compiled_thm";

(* Standard prettifying (see readerProgProof) *)
val installed_x64_def = Define `
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # 64 backend$config))
    ffi mc ms
  <=>
    ?cbspace data_sp.
      is_x64_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        ffi
        (heap_regs x64_backend_config.stack_conf.reg_names) mc ms
    `;

val check_unsat_code_def = Define `
  check_unsat_code = (code, data, config)
  `;

Theorem machine_code_sound:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ⇒
  installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (check_unsat_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    if out = strlit "s VERIFIED UNSAT\n" then
      LENGTH cl = 3 ∧ inFS_fname fs (EL 1 cl) ∧
      ∃mv fml.
        parse_dimacs (all_lines fs (EL 1 cl)) = SOME (mv,fml) ∧
        unsatisfiable (interp fml)
    else
      if LENGTH cl = 2 ∧ inFS_fname fs (EL 1 cl)
      then
        case parse_dimacs (all_lines fs (EL 1 cl)) of
          NONE => out = strlit ""
        | SOME (mv,fml) => out = concat (print_dimacs fml)
      else
        out = strlit ""
Proof
  ntac 2 strip_tac>>
  fs[installed_x64_def,check_unsat_code_def]>>
  drule check_unsat_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[check_unsat_sem_def]>>
  reverse IF_CASES_TAC>>fs[] >- (
    (* LENGTH cl = 2 *)
    reverse IF_CASES_TAC>>fs[] >- (
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    reverse IF_CASES_TAC>>fs[] >- (
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]>- (
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]>>
    qexists_tac`strlit ""` >>
    simp[STD_streams_stderr,add_stdo_nil]>>
    simp[print_dimacs_def,print_header_line_def]>>
    qmatch_goalsub_abbrev_tac` (strlit"p cnf " ^ a ^ b ^ c)`>>
    qmatch_goalsub_abbrev_tac` _ :: d`>>
    EVAL_TAC
  )>>
  (* LENGTH cl = 3 *)
  reverse IF_CASES_TAC>>fs[] >-
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]>-
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]>>
  reverse IF_CASES_TAC>>fs[] >-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  TOP_CASE_TAC>>fs[]>-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  reverse IF_CASES_TAC >> fs[] >-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  qexists_tac`strlit "s VERIFIED UNSAT\n"` >> qexists_tac`strlit ""`>> rw[]
  >-
    metis_tac[STD_streams_stderr,add_stdo_nil]>>
  drule parse_dimacs_wf_bound>>
  drule parse_lpr_wf>>
  metis_tac[check_lpr_unsat_sound]
QED

Theorem machine_code_sound_parse_print:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ⇒
  installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)} ∧
  (* If we start with a well-formed formula, and put it into the file *)
  wf_fml fml ∧ inFS_fname fs (EL 1 cl) ∧ all_lines fs (EL 1 cl) = print_dimacs fml ⇒
  ∃out err.
    extract_fs fs (check_unsat_io_events cl fs) = SOME (add_stdout (add_stderr fs err) out) ∧
    (* Then if the output is "s VERIFIED UNSAT\n" that formula was also unsatisfiable *)
    if out = strlit "s VERIFIED UNSAT\n" then
      LENGTH cl = 3 ∧ unsatisfiable (interp fml)
    else
      if LENGTH cl = 2 then
        ∃fml'.
        interp fml = interp fml' ∧ out = concat (print_dimacs fml')
      else out = strlit ""
Proof
  rw[]>>
  drule machine_code_sound>>
  rpt(disch_then drule>>simp[])>>
  strip_tac>>
  asm_exists_tac>> simp[] >>
  IF_CASES_TAC
  >- (
    drule parse_dimacs_print_dimacs>> rw[]>>
    fs[interp_def]>>
    rw[]) >>
  fs[]>> rw[] >> fs[]>>
  drule parse_dimacs_print_dimacs>> rw[]>> fs[]>>
  qexists_tac`fml'`>> simp[interp_def]
QED

val _ = export_theory();
