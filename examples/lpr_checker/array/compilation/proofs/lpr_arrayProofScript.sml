(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     satSemTheory lprTheory lpr_listTheory lpr_arrayProgTheory
     parsingTheory lpr_arrayCompileTheory;

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

Theorem fml_rel_check_lpr_list:
  ∀steps fml fmlls inds fmlls' inds' Clist.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
  EVERY wf_lpr steps ∧
  check_lpr_list steps fmlls inds Clist = SOME (fmlls', inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lpr steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lpr_list_def,check_lpr_def]>>
  ntac 7 strip_tac>>
  ntac 3 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_lpr_step_list>>
  rpt (disch_then drule)>>
  disch_then (qspec_then `h` mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  match_mp_tac check_lpr_step_wf_fml>>
  metis_tac[]
QED

Theorem fml_rel_FOLDL_resize_update_list:
  fml_rel x
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
Proof
  rw[fml_rel_def]>>
  reverse(rw[])
  >- (
    CCONTR_TAC>>fs[]>>
    `?y. lookup x' x = SOME y` by
      (Cases_on`lookup x' x`>>fs[])>>
    fs[GSYM MEM_toSortedAList]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM (x',y) (REVERSE (toSortedAList x))` by
      fs[MEM_REVERSE]>>
    drule LENGTH_FOLDR_resize_update_list2>>
    simp[]>>
    metis_tac[])>>
  `ALL_DISTINCT (MAP FST (toSortedAList x))` by
    fs[ALL_DISTINCT_MAP_FST_toSortedAList]>>
  drule FOLDL_resize_update_list_lookup>>
  simp[ALOOKUP_toSortedAList]
QED

Theorem ind_rel_FOLDL_resize_update_list:
  ind_rel
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
  (MAP FST (toSortedAList x))
Proof
  simp[ind_rel_def,FOLDL_FOLDR_REVERSE]>>
  `∀z. MEM z (MAP FST (toSortedAList x)) ⇔ MEM z (MAP FST (REVERSE (toSortedAList x)))` by
    simp[MEM_MAP]>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`MAP FST ls`>>
  rpt(pop_assum kall_tac)>>
  Induct_on`ls`>>rw[]
  >-
    metis_tac[EL_REPLICATE]>>
  Cases_on`h`>>fs[]>>
  fs[IS_SOME_EXISTS]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    strip_tac>>
    IF_CASES_TAC>>simp[])
  >>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC>>simp[EL_APPEND_EQN]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

Theorem check_lpr_unsat_list_sound:
  check_lpr_unsat_list lpr
    (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
    (MAP FST (toSortedAList x)) Clist ∧
  wf_fml x ∧ EVERY wf_lpr lpr ∧ EVERY ($= w8z) Clist ⇒
  unsatisfiable (interp x)
Proof
  rw[check_lpr_unsat_list_def]>>
  every_case_tac>>fs[]>>
  assume_tac (fml_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac (ind_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  drule fml_rel_check_lpr_list>>
  rpt(disch_then drule)>>
  strip_tac>>
  drule check_lpr_sound>>
  rpt(disch_then drule)>>
  drule fml_rel_is_unsat_list  >>
  rpt(disch_then drule)>>
  metis_tac[is_unsat_sound,unsatisfiable_def]
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
    if out = strlit "s UNSATISFIABLE\n" then
      (LENGTH cl = 3 ∨ LENGTH cl = 4) ∧ inFS_fname fs (EL 1 cl) ∧
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
  TOP_CASE_TAC>- (
    fs[]>>
    qexists_tac`strlit ""`>>simp[]>>
    qexists_tac`err`>>rw[]
    >-
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    fs[parse_arguments_def]>>
    every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  TOP_CASE_TAC >>fs[]>>
  reverse IF_CASES_TAC>>fs[] >- (
    qexists_tac`strlit ""`>>simp[]>>
    qexists_tac`err`>>rw[]
    >-
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    fs[parse_arguments_def]>>
    every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  TOP_CASE_TAC>>fs[]
  >-
     metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* print DIMACS case *)
    qexists_tac`concat (print_dimacs r')`>>
    qexists_tac`strlit ""` >>
    simp[STD_streams_stderr,add_stdo_nil]>>
    simp[print_dimacs_def]>>
    `?x. cl = [x;q]` by
      (fs[parse_arguments_def]>>every_case_tac>>fs[]>>
      Cases_on`cl`>>fs[])>>
    fs[]>>
    simp[print_header_line_def]>>
    qmatch_goalsub_abbrev_tac` (strlit"p cnf " ^ a ^ b ^ c)`>>
    qmatch_goalsub_abbrev_tac` _ :: d`>>
    EVAL_TAC)>>
  TOP_CASE_TAC>>fs[]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    qexists_tac`strlit ""`>>simp[]>>
    qexists_tac`err`>>rw[]
    >-
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    fs[parse_arguments_def]>>
    every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  TOP_CASE_TAC>>fs[]
  >- (
    qexists_tac`strlit ""`>>simp[]>>
    qexists_tac`err`>>rw[]
    >-
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    fs[parse_arguments_def]>>
    every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  reverse IF_CASES_TAC >> fs[] >- (
    qexists_tac`strlit ""`>>simp[]>>
    qexists_tac`err`>>rw[]
    >-
      metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    fs[parse_arguments_def]>>
    every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  (* the actual interesting case *)
  qexists_tac`strlit "s UNSATISFIABLE\n"` >> qexists_tac`strlit ""`>> simp[]>>
  CONJ_TAC >-
    metis_tac[STD_streams_stderr,add_stdo_nil]>>
  PURE_REWRITE_TAC[CONJ_ASSOC]>>
  CONJ_TAC>-
    (fs[parse_arguments_def]>>every_case_tac>>fs[]>>
    Cases_on`cl`>>fs[])>>
  drule (check_lpr_unsat_list_sound)>>simp[]>>
  disch_then match_mp_tac>>
  metis_tac[parse_dimacs_wf_bound,parse_lpr_wf]
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
    (* Then if the output is "s UNSATISFIABLE" that formula was also unsatisfiable *)
    if out = strlit "s UNSATISFIABLE\n" then
      (LENGTH cl = 3 ∨ LENGTH cl = 4) ∧ unsatisfiable (interp fml)
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
