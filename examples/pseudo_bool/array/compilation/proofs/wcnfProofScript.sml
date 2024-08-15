(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     wcnfProgTheory
     wcnfCompileTheory;

val _ = new_theory"wcnfProof";

val cake_pb_wcnf_io_events_def = new_specification("cake_pb_wcnf_io_events_def",["cake_pb_wcnf_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_pb_wcnf_sem,cake_pb_wcnf_output) = cake_pb_wcnf_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_pb_wcnf_not_fail,cake_pb_wcnf_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cake_pb_wcnf_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 wcnf_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_pb_wcnf_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_pb_wcnf_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val cake_pb_wcnf_compiled_thm =
  CONJ compile_correct_applied cake_pb_wcnf_output
  |> DISCH_ALL
  (* |> check_thm *)
  |> curry save_thm "cake_pb_wcnf_compiled_thm";

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
        (heap_regs x64_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
    `;

val cake_pb_wcnf_code_def = Define `
  cake_pb_wcnf_code = (code, data, info)
  `;

(* A standard run of cake_pb_wcnf
  satisfying all the default assumptions *)
val cake_pb_wcnf_run_def = Define`
  cake_pb_wcnf_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_wcnf_code mc ms`

Theorem machine_code_sound:
  cake_pb_wcnf_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_pb_wcnf_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (cake_pb_wcnf_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ strlit"" ⇒
      (
        (LENGTH cl = 2 ∧
        ∃wfml.
          get_fml fs (EL 1 cl) = SOME wfml ∧
          out = concat (print_pbf (full_encode wfml))) ∨
        (LENGTH cl = 3 ∧
        ∃wfml bounds.
          get_fml fs (EL 1 cl) = SOME wfml ∧
          out = print_maxsat_str bounds ∧
          maxsat_sem wfml bounds) ∨
        (LENGTH cl = 4 ∧
        ∃wfml wfmlt bounds iseqopt.
          get_fml fs (EL 1 cl) = SOME wfml ∧
          get_fml fs (EL 3 cl) = SOME wfmlt ∧
          out = print_maxsat_str bounds ^
          print_maxsat_output_str iseqopt ∧
          maxsat_sem wfml bounds ∧
          maxsat_output_sem wfml wfmlt iseqopt)
      )
    )
Proof
  strip_tac>>
  fs[installed_x64_def,cake_pb_wcnf_code_def,cake_pb_wcnf_run_def]>>
  drule cake_pb_wcnf_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  every_case_tac>>fs[]
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_3_sem_def,get_fml_def]>>
    strip_tac>>gvs[]>>
    metis_tac[])
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_2_sem_def,get_fml_def]>>
    strip_tac>>gvs[]>>
    metis_tac[])
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_1_sem_def,get_fml_def]>>
    strip_tac>>gvs[]>>
    every_case_tac>>fs[])>>
  metis_tac[]
QED

val chk = machine_code_sound |> check_thm;

(* Showing how to specialize the main theorem *)

Theorem strcat_cancel:
  a = b ∧ a ^ y = b ^ z ⇒
  y = z
Proof
  EVAL_TAC>>rw[]>>
  every_case_tac>>fs[]
QED

Theorem isSuffix_STRCAT:
  isSuffix x (y ^ x)
Proof
  rw[mlstringTheory.isSuffix_def]>>
  Cases_on`x`>>Cases_on`y`>>
  simp[mlstringTheory.strlit_STRCAT]>>
  DEP_REWRITE_TAC[mlstringTheory.isStringThere_SEG]>>
  rw[]>>
  gvs[SEG_TAKE_DROP]>>
  simp[DROP_LENGTH_APPEND]
QED

Theorem strcat_isSuffix:
  x ^ y = a ^ b ⇒
  isSuffix y b ∨ isSuffix b y
Proof
  map_every Cases_on [`x`,`y`,`a`,`b`]>>
  simp[mlstringTheory.strlit_STRCAT,listTheory.APPEND_EQ_APPEND]>>rw[]>>
  metis_tac[isSuffix_STRCAT,mlstringTheory.strlit_STRCAT]
QED

Theorem strcat_isSuffixL:
  x ^ y = a ⇒
  isSuffix y a
Proof
  `a = a ^ strlit ""` by
    (Cases_on`a`>>EVAL_TAC)>>
  rw[]>>
  metis_tac[isSuffix_STRCAT]
QED

Theorem isSuffix_exists:
  isSuffix x y ⇒
  ∃z. y = z ^ x
Proof
  rw[mlstringTheory.isSuffix_def]>>
  Cases_on`x`>>Cases_on`y`>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[mlstringTheory.isStringThere_SEG]>>
  rw[]>>
  gvs[SEG_TAKE_DROP]>>
  qexists_tac`strlit (TAKE (STRLEN s' − STRLEN s) s')`>>
  simp[mlstringTheory.strlit_STRCAT]>>
  rename1`l ≤ STRLEN s'`>>
  pop_assum SUBST_ALL_TAC>>simp[GSYM TAKE_SUM]
QED

Theorem machine_code_sound_equiopt:
  cake_pb_wcnf_run cl fs mc ms ⇒
  ∃out err.
    extract_fs fs (cake_pb_wcnf_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (
    LENGTH cl = 4 ∧
    isSuffix «s VERIFIED OUTPUT EQUIOPTIMAL\n» out ⇒
      ∃wfml wfml'.
        get_fml fs (EL 1 cl) = SOME wfml ∧
        get_fml fs (EL 3 cl) = SOME wfml' ∧
        opt_cost wfml = opt_cost wfml'
    )
Proof
  rw[]>>
  drule machine_code_sound>>rw[]>>
  first_x_assum (irule_at Any)>>
  rw[]>>drule isSuffix_exists>>
  pop_assum kall_tac>>
  strip_tac>>
  rename1`pref ^ _`>>
  gvs[]>>
  `pref ^ «s VERIFIED OUTPUT EQUIOPTIMAL\n» ≠ «»` by
    (EVAL_TAC>>
    rw[])>>
  gvs[]>>
  `iseqopt` by
    (drule strcat_isSuffix>>
    simp[wcnfProgTheory.print_maxsat_output_str_def]>>
    IF_CASES_TAC>>simp[]>>
    EVAL_TAC)>>
  gvs[wcnfProgTheory.maxsat_output_sem_def]
QED

val _ = export_theory();
