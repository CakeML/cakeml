(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     satSemTheory lprTheory lpr_listTheory lpr_arrayProgTheory
     lpr_parsingTheory lpr_arrayCompileTheory lpr_composeProgTheory;

val _ = new_theory"lpr_arrayProof";

val check_unsat_io_events_def = new_specification("check_unsat_io_events_def",["check_unsat_io_events"],
  check_unsat_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (check_unsat_sem,check_unsat_output) = check_unsat_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (check_unsat_not_fail,check_unsat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail check_unsat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct lpr_array_compiled
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
  (* |> check_thm *)
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

Theorem concat_success_str:
  ∀a b c. concat [strlit "s VERIFIED INTERVALS COVER 0-"; toString (d:num); strlit "\n"] ≠ success_str a b c
Proof
  rw[]>>
  simp[success_str_def,expected_prefix_def]>>
  simp[mlstringTheory.concat_def]>>
  qmatch_goalsub_abbrev_tac`STRING #"I" (STRING #"N" lss)`>>
  qmatch_goalsub_abbrev_tac`STRING #"R" (STRING #"A" lsss)`>>
  EVAL_TAC
QED

Theorem check_lines_success_str:
  check_lines a b c d = INR y ⇒
  y = concat [strlit "s VERIFIED INTERVALS COVER 0-"; toString d; strlit "\n"] ∧
  ∀a b c. y ≠ success_str a b c
Proof
  simp[check_lines_def]>>
  every_case_tac>>rw[]>>
  metis_tac[concat_success_str]
QED

Theorem machine_code_sound:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ⇒
  installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (check_unsat_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 2 then
    if inFS_fname fs (EL 1 cl)
    then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        NONE => out = strlit ""
      | SOME fml => out = concat (print_dimacs fml)
    else out = strlit ""
  else if LENGTH cl = 3 then
    if out = strlit "s VERIFIED UNSAT\n" then
      inFS_fname fs (EL 1 cl) ∧
      ∃fml.
        parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
        unsatisfiable (interp fml)
    else out = strlit ""
  else if LENGTH cl = 4 then
    if out = strlit "s VERIFIED TRANSFORMATION\n" then
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 3 cl) ∧
    ∃fml fml2.
      parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
      parse_dimacs (all_lines fs (EL 3 cl)) = SOME fml2 ∧
      (satisfiable (interp fml) ⇒ satisfiable (interp fml2))
    else out = strlit ""
  else if LENGTH cl = 5 then
    if ∃cnf_md5 proof_md5 rng. out = success_str cnf_md5 proof_md5 rng then
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
    inFS_fname fs (EL 4 cl) ∧
    out = success_str
      (implode (md5 (THE (file_content fs (EL 1 cl)))))
      (implode (md5 (THE (file_content fs (EL 2 cl))))) (EL 3 cl) ∧
    ∃i j fml pf.
      parse_rng (EL 3 cl) = SOME (i,j) ∧
      parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
      parse_proof (all_lines fs (EL 2 cl)) = SOME pf ∧
      i ≤ j ∧ j ≤ LENGTH pf ∧
      (satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
       satisfiable (interp (run_proof fml (TAKE j pf))))
    else if ?n:num. out = concat [strlit "s VERIFIED INTERVALS COVER 0-"; toString n; strlit "\n"] then
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧ inFS_fname fs (EL 4 cl) ∧
    EL 3 cl = strlit "-check" ∧
    check_lines (implode (md5 (THE (file_content fs (EL 1 cl))))) (implode (md5 (THE (file_content fs (EL 2 cl)))))
        (all_lines fs (EL 4 cl)) (LENGTH (all_lines fs (EL 2 cl))) = INR out
    else out = strlit ""
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
    simp[parse_dimacs_def]>>
    match_mp_tac (GEN_ALL check_lpr_unsat_list_sound)>>
    asm_exists_tac>>simp[]>>
    CONJ_TAC >- (
      match_mp_tac (GEN_ALL parse_dimacs_wf)>>simp[parse_dimacs_def]>>
      qexists_tac`all_lines fs h'`>>fs[])>>
    metis_tac[parse_lpr_wf])>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* 3 arg *)
    fs[check_unsat_3_sem_def]>>
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
    qexists_tac`strlit "s VERIFIED TRANSFORMATION\n"` >>
    qexists_tac`strlit ""`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    fs[parse_dimacs_def]>>
    match_mp_tac (GEN_ALL check_lpr_sat_equiv_list_sound)>>
    asm_exists_tac>>simp[]>>
    CONJ_TAC >- (
      match_mp_tac (GEN_ALL parse_dimacs_wf)>>simp[parse_dimacs_def]>>
      qexists_tac`all_lines fs h'`>>fs[])>>
    metis_tac[parse_lpr_wf])>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* 4 arg *)
    `∀a b c. success_str a b c ≠ strlit ""` by (rw[]>>EVAL_TAC)>>
    `∀n:num. concat [strlit "s VERIFIED INTERVALS COVER 0-" ; toString n; strlit"\n"]  ≠ strlit ""` by
      (rw[]>>
      qmatch_goalsub_abbrev_tac`_ :: lss`>>
      EVAL_TAC)>>
    fs[check_unsat_4_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[] >>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit""`>>qexists_tac`err`>>rw[]>>
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
    TOP_CASE_TAC>>fs[]
    (* -check option*)
    >- (
      reverse IF_CASES_TAC
      >- (
        qexists_tac`strlit ""`>>simp[]>>
        qexists_tac`err`>>rw[]>>
        metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
      TOP_CASE_TAC
      >- (
        qexists_tac`strlit ""`>>simp[]>>
        qexists_tac`err`>>rw[]>>
        metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
      qexists_tac`y`>>qexists_tac`strlit ""`>>simp[]>>
      CONJ_TAC >-
        metis_tac[STD_streams_stderr,add_stdo_nil]>>
      drule check_lines_success_str>>
      simp[]>> rw[]
      >- metis_tac[]
      >-  (fs[parse_rng_or_check_def]>>
        qpat_x_assum`_=SOME (INL _)` mp_tac>>IF_CASES_TAC>>fs[])>>
      drule parse_proof_toks_LENGTH>>
      rw[]>>
      metis_tac[])>>
    TOP_CASE_TAC>>fs[]>>
    reverse IF_CASES_TAC
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
    qmatch_goalsub_abbrev_tac`success_str a b c`>>
    qexists_tac`success_str a b c`>>
    qexists_tac`strlit ""`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    reverse IF_CASES_TAC>- (
      rw[]>>
      metis_tac[])>>
    fs[parse_dimacs_def,parse_proof_def]>>
    rw[]>>fs[]>>
    fs[parse_rng_or_check_def]>>
    qpat_x_assum`_ = SOME (INR _)` mp_tac>>
    IF_CASES_TAC>>fs[]>>
    strip_tac>>
    match_mp_tac (GEN_ALL check_lpr_range_list_sound)>>
    `x1 + 1 = LENGTH x2 +1 ` by (
      fs[parse_dimacs_toks_def]>>
      qpat_x_assum `_ = SOME (x0,x1,x2)` mp_tac>>
      rpt (pop_assum kall_tac)>>
      every_case_tac>>fs[]>>
      drule LENGTH_parse_dimacs_body>>
      rw[]>> simp[])>>
    pop_assum SUBST_ALL_TAC>>
    asm_exists_tac>>simp[]>>
    fs[GSYM parse_proof_def]>>
    drule parse_proof_wf_proof>>
    drule parse_lpr_wf>>
    simp[]>>
    `parse_dimacs (all_lines fs h') = SOME x2` by
      fs[parse_dimacs_def]>>
    drule parse_dimacs_wf>>simp[])>>
  qexists_tac`err`>>rw[]>>
  metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]
QED

Theorem run_proof_empty:
  run_proof fml [] = fml
Proof
  EVAL_TAC
QED

Theorem par_check_sound:
  EVERY (λ(cl,fs,mc,ms,i,j).
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
    installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ∧
    LENGTH cl = 5 ∧
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
    all_lines fs (EL 1 cl) = fmlstr ∧
    all_lines fs (EL 2 cl) = pfstr ∧
    EL 3 cl = toString i ^ «-» ^ toString j
  ) nodes ∧
  parse_dimacs fmlstr = SOME fml ∧ parse_proof pfstr = SOME pf ∧
  interval_cover 0 (LENGTH pf) (MAP (λ(cl,fs,mc,ms,i,j). (i,j)) nodes)
  ⇒
  EVERY (λ(cl,fs,mc,ms,i,j).
    machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)}) nodes ∧
  (
    EVERY (λ(cl,fs,mc,ms,i,j).
      extract_fs fs (check_unsat_io_events cl fs) =
        SOME (add_stdout fs
          (success_str
          (implode (md5 (THE (file_content fs (EL 1 cl)))))
          (implode (md5 (THE (file_content fs (EL 2 cl))))) (EL 3 cl)))
    ) nodes ⇒
    (satisfiable (interp fml) ⇒
     satisfiable (interp (run_proof fml pf)))
  )
Proof
  strip_tac>>
  `EVERY (λ(cl,fs,mc,ms,i,j).
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (check_unsat_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out = success_str
      (implode (md5 (THE (file_content fs (EL 1 cl)))))
      (implode (md5 (THE (file_content fs (EL 2 cl))))) (EL 3 cl) ⇒
      i ≤ j ∧ j ≤ LENGTH pf ∧
      (satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
       satisfiable (interp (run_proof fml (TAKE j pf)))))) nodes` by
    (fs[EVERY_MEM,FORALL_PROD]>>
    rw[]>>first_x_assum drule>>
    strip_tac>>
    drule machine_code_sound>> rpt(disch_then drule)>>
    simp[]>>  rpt(disch_then drule)>>
    rw[]>>
    asm_exists_tac>>simp[]>>
    pop_assum mp_tac>>every_case_tac>>
    fs[parse_rng_toString]>>
    `∀a b c. success_str a b c ≠ strlit ""` by (rw[]>>EVAL_TAC)>>
    metis_tac[])>>
  CONJ_TAC >- (
    pop_assum mp_tac>>match_mp_tac MONO_EVERY>>
    simp[FORALL_PROD]>>
    metis_tac[])>>
  rw[]>>
  drule interval_cover_satisfiable>>
  disch_then(qspecl_then[`pf`,`fml`] mp_tac)>>
  impl_tac>-(
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS,run_proof_empty]>>
    rw[]>>rpt (first_x_assum drule)>>
    rw[]>>
    gs[SOME_11]>>
    drule STD_streams_stdout>>rw[]>>
    drule add_stdout_inj>>
    metis_tac[stdout_add_stderr])>>
  simp[]
QED

val check_successful_def = Define`
  check_successful fmlstr pfstr (i:num,j:num) =
  ∃cl fs mc ms.
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
    installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ∧
    LENGTH cl = 5 ∧
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
    all_lines fs (EL 1 cl) = fmlstr ∧
    all_lines fs (EL 2 cl) = pfstr ∧
    EL 3 cl = toString i ^ «-» ^ toString j ∧
    extract_fs fs (check_unsat_io_events cl fs) =
      SOME (add_stdout fs
        (success_str
          (implode (md5 (THE (file_content fs (EL 1 cl)))))
          (implode (md5 (THE (file_content fs (EL 2 cl))))) (EL 3 cl)))`

Theorem par_check_sound_2:
  parse_dimacs fmlstr = SOME fml ∧ parse_proof pfstr = SOME pf ∧
  interval_cover 0 (LENGTH pf) ranges ∧
  EVERY (check_successful fmlstr pfstr) ranges ⇒
  (satisfiable (interp fml) ⇒ satisfiable (interp (run_proof fml pf)))
Proof
  rw[]>>
  drule interval_cover_satisfiable>>
  disch_then(qspecl_then[`pf`,`fml`] mp_tac)>>
  impl_tac>-(
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS,run_proof_empty]>>
    rw[]>>first_x_assum drule>>
    simp[check_successful_def]>>rw[]>>
    drule machine_code_sound>> rpt(disch_then drule)>>
    simp[]>>  rpt(disch_then drule)>>
    rw[]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]
    >- (
      rw[]>>
      drule STD_streams_stdout>>rw[]>>
      drule add_stdout_inj>>
      disch_then drule>>
      rw[stdout_add_stderr]>>
      fs[parse_rng_toString])>>
    drule STD_streams_stdout>>rw[]>>
    drule add_stdout_inj>>
    disch_then drule>>
    rw[]>>
    metis_tac[stdout_add_stderr])>>
  simp[]
QED

Theorem parse_proof_LENGTH:
  parse_proof ls = SOME pf ⇒
  LENGTH pf = LENGTH ls
Proof
  simp[parse_proof_def]>>
  rw[]>>
  drule parse_proof_toks_LENGTH>>
  simp[]
QED

Theorem success_str_inj:
  success_str a b c = success_str a b d ⇒ c = d
Proof
  rw[success_str_def,expected_prefix_def]>>
  pop_assum mp_tac>>
  EVAL_TAC>>
  rw[]>>simp[]>>
  every_case_tac>>fs[]
QED

val check_successful_par_def = Define`
  check_successful_par fmlstr pfstr =
  ∃outstr.
    (∃cl fs mc ms.
      wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
      installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ∧
      LENGTH cl = 5 ∧
      inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
      all_lines fs (EL 1 cl) = fmlstr ∧
      all_lines fs (EL 2 cl) = pfstr ∧
      all_lines fs (EL 4 cl) = outstr ∧
      extract_fs fs (check_unsat_io_events cl fs) =
        SOME (add_stdout fs
          (concat [«s VERIFIED INTERVALS COVER 0-» ; toString (LENGTH pfstr); «\n»]))) ∧
    ∀out. MEM out outstr ⇒
    (∃cl fs mc ms i j.
      wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
      installed_x64 check_unsat_code (basis_ffi cl fs) mc ms ∧
      LENGTH cl = 5 ∧
      inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
      all_lines fs (EL 1 cl) = fmlstr ∧
      all_lines fs (EL 2 cl) = pfstr ∧
      EL 3 cl = toString i ^ «-» ^ toString j ∧
      extract_fs fs (check_unsat_io_events cl fs) = SOME (add_stdout fs out))`

Theorem MEM_get_ranges:
  ∀ls prefix ranges i j.
  get_ranges prefix ls = INR ranges ∧
  MEM (i,j) ranges ⇒
  MEM (prefix ^ (toString i ^ «-» ^ toString j) ^ strlit"\n") ls
Proof
  Induct>>rw[get_ranges_def]>>
  every_case_tac>>fs[]>>rw[]>>
  fs[get_range_def]>>
  every_case_tac>>fs[]>>rw[]>>
  cheat
QED

Theorem lines_of_inj:
  lines_of (strlit c) = lines_of (strlit d) ⇒ c = d
Proof
  cheat
QED

Theorem par_check_sound_3:
  parse_dimacs fmlstr = SOME fml ∧ parse_proof pfstr = SOME pf ∧
  check_successful_par fmlstr pfstr ⇒
  (satisfiable (interp fml) ⇒ satisfiable (interp (run_proof fml pf)))
Proof
  rw[check_successful_par_def]>>
  drule machine_code_sound>> rpt(disch_then drule)>>
  simp[]>>  rpt(disch_then drule)>>
  rw[]>>
  drule STD_streams_stdout>>rw[]>>
  drule add_stdout_inj>>
  disch_then drule>>
  simp[stdout_add_stderr]>>
  rw[]>>fs[concat_success_str]>>
  ntac 2 (pop_assum mp_tac)>>
  reverse IF_CASES_TAC>>fs[]
  >-
    metis_tac[]>>
  rw[]>>
  drule lpr_composeProgTheory.check_lines_correct>>
  rw[]>>
  qpat_x_assum`satisfiable _` mp_tac>>
  match_mp_tac (GEN_ALL par_check_sound_2)>>
  asm_exists_tac>> simp[]>>
  asm_exists_tac>> simp[]>>
  drule parse_proof_LENGTH>>
  rw[]>>
  asm_exists_tac>> simp[]>>
  rw[EVERY_MEM]>>
  Cases_on`e`>>fs[]>>
  `MEM (q,r) ranges` by fs[SUBSET_DEF]>>
  drule MEM_get_ranges>>
  disch_then drule>>
  simp[GSYM success_str_def]>>
  strip_tac>>
  first_x_assum drule>>
  rw[]>>
  simp[check_successful_def]>>
  rpt(asm_exists_tac>>simp[])>>
  drule machine_code_sound>>
  rpt(disch_then drule)>>simp[]>>
  rpt(disch_then drule)>>simp[]>>
  strip_tac>>fs[]>>
  qmatch_asmsub_abbrev_tac`add_stdout fs' ss`>>
  `ss = out` by
    (drule STD_streams_stdout>>rw[]>>
    drule add_stdout_inj>>
    disch_then drule>>
    rw[stdout_add_stderr])>>
  unabbrev_all_tac>>fs[]>>
  pop_assum sym_sub_tac>>
  pop_assum mp_tac>>
  reverse IF_CASES_TAC
  >- metis_tac[]>>
  fs[]>>strip_tac>>
  fs[success_str_inj]>>
  `consistentFS fs` by
    (fs[fsFFIPropsTheory.consistentFS_def,fsFFIPropsTheory.wfFS_def]>>
    metis_tac[])>>
  drule inFS_fname_file_content>> disch_then imp_res_tac >>
  `consistentFS fs'` by
    (fs[fsFFIPropsTheory.consistentFS_def,fsFFIPropsTheory.wfFS_def]>>
    metis_tac[])>>
  drule inFS_fname_file_content>> disch_then imp_res_tac >>
  imp_res_tac all_lines_lines_of>>
  fs[]>>
  imp_res_tac lines_of_inj>>rw[]>>
  drule success_str_inj>>
  simp[]
QED

val _ = export_theory();
