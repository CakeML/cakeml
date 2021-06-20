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

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml n ls acc) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls)
  else lookup i acc
Proof
  Induct>>rw[build_fml_def]
  >- (
    `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
    simp[])
  >- fs[]
  >- (
    `i-n=0`by fs[]>>
    simp[lookup_insert])>>
  simp[lookup_insert]
QED

Theorem SORTED_range:
  SORTED  $< ls ∧
  (∀i. MEM i ls ⇔ a ≤ i ∧ i < b) ⇒
  ls = GENLIST ($+ a) (b-a)
Proof
  rw[]>>
  match_mp_tac (SORTED_PERM_EQ |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO])>>
  qexists_tac`$<`>>
  CONJ_ASM1_TAC>>
  simp[antisymmetric_def]>>
  CONJ_ASM1_TAC>-
    simp[SORTED_GENLIST_PLUS]>>
  fs[]>>
  `irreflexive ($< : num -> num -> bool)` by
    simp[irreflexive_def]>>
  imp_res_tac SORTED_ALL_DISTINCT>>
  rfs[]>>
  match_mp_tac PERM_ALL_DISTINCT>>
  fs[MEM_GENLIST]>>
  rw[EQ_IMP_THM]>>
  qexists_tac`x-a`>>simp[]
QED

Theorem MAP_FST_LIST_EQ:
  ALL_DISTINCT (MAP FST l1) ∧
  MAP FST l1 = MAP FST l2 ∧
  (∀x. ALOOKUP l1 (x:num) = ALOOKUP l2 x)
  ⇒ l1 = l2
Proof
  rw[]>>rw[LIST_EQ_REWRITE]>-
    metis_tac[LENGTH_MAP]>>
  `ALOOKUP l1 (FST (EL x l1)) = SOME (SND (EL x l1))` by
    (match_mp_tac ALOOKUP_ALL_DISTINCT_EL>>
    fs[])>>
  `ALOOKUP l2 (FST (EL x l2)) = SOME (SND (EL x l2))` by
    (match_mp_tac ALOOKUP_ALL_DISTINCT_EL>>
    fs[]>>metis_tac[LENGTH_MAP])>>
  rfs[LIST_EQ_REWRITE,EL_MAP,LENGTH_MAP]>>
  fs[EL_MAP]>>
  first_x_assum drule>>
  Cases_on`EL x l1`>> Cases_on`EL x l2`>>fs[]
QED

Theorem ALOOKUP_enumerate:
  ∀ls k x.
  ALOOKUP (enumerate k ls) x =
  if k ≤ x ∧ x < LENGTH ls + k then SOME (EL (x-k) ls) else NONE
Proof
  Induct>>rw[miscTheory.enumerate_def]>>
  `x-k = SUC(x-(k+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem toSortedAList_build_fml_enumerate:
  toSortedAList (build_fml 1 ls LN) = enumerate 1 ls
Proof
  `MAP FST (toSortedAList (build_fml 1 ls LN)) = GENLIST ($+ 1) (LENGTH ls+1 -1)` by
    (match_mp_tac SORTED_range>>
    simp[SORTED_toSortedAList,MEM_MAP,EXISTS_PROD,MEM_toSortedAList]>>
    simp[lookup_build_fml,lookup_def])>>
  match_mp_tac MAP_FST_LIST_EQ>>
  fs[MAP_FST_enumerate]>>
  CONJ_ASM1_TAC
  >-(
    pop_assum sym_sub_tac>>
    simp[ALL_DISTINCT_MAP_FST_toSortedAList])>>
  rw[]>>
  simp[ALOOKUP_toSortedAList,lookup_build_fml,ALOOKUP_enumerate,lookup_def]
QED

Theorem MAP_SND_enumerate:
  MAP SND (enumerate k ls) = ls
Proof
  rw[LIST_EQ_REWRITE,LENGTH_enumerate,EL_MAP,EL_enumerate]
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
  if out = strlit "s VERIFIED UNSAT\n" then
    LENGTH cl = 3 ∧ inFS_fname fs (EL 1 cl) ∧
    ∃fml.
      parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
      unsatisfiable (interp fml)
  else if out = strlit "s VERIFIED TRANSFORMATION\n" then
    LENGTH cl = 4 ∧ inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 3 cl) ∧
    ∃fml fml2.
      parse_dimacs (all_lines fs (EL 1 cl)) = SOME fml ∧
      parse_dimacs (all_lines fs (EL 3 cl)) = SOME fml2 ∧
      (satisfiable (interp fml) ⇒ satisfiable (interp fml2))
  else if LENGTH cl = 2 then
    if inFS_fname fs (EL 1 cl)
    then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        NONE => out = strlit ""
      | SOME fml => out = concat (print_dimacs fml)
    else
      out = strlit ""
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
  >-(
    (* 1 arg *)
    fs[check_unsat_1_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      Cases_on`cl`>>rfs[])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def])>>
    PairCases_on`x`>>fs[]>>
    qexists_tac`concat (print_dimacs_toks x2)`>>
    qexists_tac`strlit ""` >>
    simp[STD_streams_stderr,add_stdo_nil]>>
    simp[parse_dimacs_def,print_dimacs_def,toSortedAList_build_fml_enumerate,MAP_SND_enumerate]>>
    simp[print_dimacs_toks_def]>>
    simp[print_header_line_def]>>
    qmatch_goalsub_abbrev_tac` (strlit"p cnf " ^ a ^ b ^ c)`>>
    qmatch_goalsub_abbrev_tac` _ :: d`>>
    EVAL_TAC)>>
  TOP_CASE_TAC>>fs[]
  >- (
    (* 2 arg *)
    fs[check_unsat_2_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      Cases_on`cl`>>rfs[])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def])>>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    qexists_tac`strlit "s VERIFIED UNSAT\n"` >>
    qexists_tac`strlit ""`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    fs[parse_dimacs_def]>>
    fs[GSYM toSortedAList_build_fml_enumerate]>>
    drule (check_lpr_unsat_list_sound)>>simp[]>>
    disch_then match_mp_tac>>
    CONJ_TAC >- (
      match_mp_tac (GEN_ALL parse_dimacs_wf)>>simp[parse_dimacs_def]>>
      qexists_tac`all_lines fs h'`>>fs[])>>
    metis_tac[parse_lpr_wf])>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    qexists_tac`err`>>rw[]
    >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    Cases_on`cl`>>rfs[])
  >>
    (* 3 arg *)
    fs[check_unsat_3_sem_def]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      Cases_on`cl`>>rfs[])>>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def])>>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    PairCases_on`x`>>fs[]>>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    TOP_CASE_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    reverse IF_CASES_TAC>>fs[]
    >- (
      qexists_tac`strlit ""`>>simp[]>>
      qexists_tac`err`>>rw[]
      >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      fs[parse_dimacs_def]) >>
    qexists_tac`strlit "s VERIFIED TRANSFORMATION\n"` >>
    qexists_tac`strlit ""`>> simp[]>>
    CONJ_TAC >-
      metis_tac[STD_streams_stderr,add_stdo_nil]>>
    fs[parse_dimacs_def]>>
    fs[GSYM toSortedAList_build_fml_enumerate]>>
    drule (check_lpr_sat_equiv_list_sound)>>simp[]>>
    `IMAGE interp_cclause (set x2') =
      interp (build_fml 1 x2' LN)` by
      (simp[interp_def,values_def,lookup_build_fml]>>
      AP_TERM_TAC>>
      rw[EXTENSION,lookup_def]>>
      simp[MEM_EL]>>
      rw[EQ_IMP_THM]
      >- (qexists_tac`n+1`>>simp[])>>
      qexists_tac`n-1`>>simp[])>>
    simp[]>>
    rw[]>>fs[]>>
    first_x_assum match_mp_tac>>
    CONJ_TAC >- (
      match_mp_tac (GEN_ALL parse_dimacs_wf)>>simp[parse_dimacs_def]>>
      qexists_tac`all_lines fs h'`>>fs[])>>
    metis_tac[parse_lpr_wf]
QED

val _ = export_theory();
