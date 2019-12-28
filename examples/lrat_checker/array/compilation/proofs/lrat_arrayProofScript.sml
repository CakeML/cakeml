(*
  Compose the LRAT semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     lratTheory lrat_arrayProgTheory
     parsingTheory lrat_arrayCompileTheory

val _ = new_theory"lrat_arrayProof";

val check_unsat_io_events_def = new_specification("check_unsat_io_events_def",["check_unsat_io_events"],
  check_unsat_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (check_unsat_sem,check_unsat_output) = check_unsat_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (check_unsat_not_fail,check_unsat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail check_unsat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct lrat_array_compiled
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

Theorem fml_rel_check_lrat_list:
  ∀steps fml fmlls inds fmlls' inds'.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  check_lrat_list steps fmlls inds = (fmlls', SOME inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lrat steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lrat_list_def,check_lrat_def]>>
  ntac 6 strip_tac>>
  ntac 2 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_lrat_step_list>>
  rpt (disch_then drule)>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem LENGTH_FOLDR_LUPDATE[simp]:
  ∀ll.
  LENGTH (FOLDR (λx acc. (λ(i,v). LUPDATE (SOME v) i acc) x) (REPLICATE n NONE) ll) = n
Proof
  Induct>>simp[FORALL_PROD]
QED

Theorem LENGTH_FOLDL_LUPDATE[simp]:
  ∀ll.
  LENGTH (FOLDL (λacc (i,v). LUPDATE (SOME v) i acc) (REPLICATE n NONE) ll) = n
Proof
  simp[FOLDL_FOLDR_REVERSE]
QED

Theorem FOLDL_LUPDATE_lookup:
  ∀ls x.
  EVERY (λi. i < n) (MAP FST ls) ∧
  ALL_DISTINCT (MAP FST ls) ∧
  x < n ⇒
  EL x (FOLDL (λacc (i,v). LUPDATE (SOME v) i acc) (REPLICATE n NONE) ls) =
    ALOOKUP ls x
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>- simp[EL_REPLICATE,FORALL_PROD]>>
  simp[FORALL_PROD]>>rw[]>>
  simp[EL_LUPDATE]
QED

Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  `SORTED $< (MAP FST (toSortedAList t))` by
    simp[SORTED_MAP_FST_toSortedAList]>>
  pop_assum mp_tac>>
  match_mp_tac SORTED_ALL_DISTINCT>>
  simp[irreflexive_def]
QED

Theorem check_lrat_unsat_list_sound:
  EVERY (λi. i < n) (MAP FST (toSortedAList x)) ∧
  wf_fml x ⇒
  check_lrat_unsat_list lrat
    (FOLDL (λacc (i,v). LUPDATE (SOME v) i acc) (REPLICATE n NONE) (toSortedAList x))
    (MAP FST (toSortedAList x)) ⇒
  unsatisfiable (interp x)
Proof
  rw[check_lrat_unsat_list_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac fml_rel_check_lrat_list>>
  pop_assum mp_tac >>
  impl_keep_tac >- (
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
    first_x_assum drule>>
    fs[IS_SOME_EXISTS,EL_LUPDATE]>>
    every_case_tac>>fs[])>>
  disch_then (qspec_then`x` mp_tac)>>
  impl_keep_tac >- (
    simp[fml_rel_def]>>
    drule (GEN_ALL FOLDL_LUPDATE_lookup)>>
    simp[ALL_DISTINCT_MAP_FST_toSortedAList]>>
    fs[ALOOKUP_toSortedAList]>>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS,MEM_toSortedAList]>>
    rw[NOT_SOME_NONE]>>
    Cases_on`lookup x'' x`>>fs[])>>
  rw[]>>
  drule check_lrat_sound>>
  disch_then drule>>
  rw[]>>
  drule fml_rel_is_unsat_list  >>
  fs[]>>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
  disch_then drule>>
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
    if out = strlit "UNSATISFIABLE\n" then
      LENGTH cl = 4 ∧ inFS_fname fs (EL 1 cl) ∧
      ∃fml.
        parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
        unsatisfiable (interp fml)
    else
      out = strlit "" ∨
      LENGTH cl = 2 ∧ inFS_fname fs (EL 1 cl) ∧
      ∃fml.
        parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
        out = concat (print_dimacs fml)
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
    qexists_tac`concat (print_dimacs x)`>>
    qexists_tac`strlit ""` >>
    simp[STD_streams_stderr,add_stdo_nil]>>
    simp[print_dimacs_def]>>
    qmatch_goalsub_abbrev_tac` (strlit"p cnf " ^ a ^ b ^ c)`>>
    qmatch_goalsub_abbrev_tac` _ :: d`>>
    EVAL_TAC
  ) >>
  (* LENGTH cl = 4 *)
  reverse IF_CASES_TAC>>fs[] >-
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]>-
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]>-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  reverse IF_CASES_TAC>>fs[] >-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  reverse IF_CASES_TAC>>fs[] >-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  TOP_CASE_TAC>>fs[]>-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  reverse IF_CASES_TAC >> fs[] >-
    (qexists_tac`strlit ""`>> simp[]>>
    metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil])>>
  qexists_tac`strlit "UNSATISFIABLE\n"` >> qexists_tac`strlit ""`>> rw[]
  >-
    metis_tac[STD_streams_stderr,add_stdo_nil]>>
  drule parse_dimacs_wf>>
  strip_tac>>
  metis_tac[check_lrat_unsat_list_sound]
QED

val _ = export_theory();
