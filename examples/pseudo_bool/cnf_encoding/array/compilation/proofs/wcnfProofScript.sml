(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory wcnfProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  wcnfProg wcnfCompile
Libs
  preamble

val cake_pb_wcnf_terminate = UNDISCH_ALL main_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [wcnf_compiled];

Theorem cake_pb_wcnf_compiled_thm =
  MATCH_MP compile_correct (cj 1 wcnf_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 cake_pb_wcnf_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_pb_wcnf_terminate)
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

Definition cake_pb_wcnf_code_def:
  cake_pb_wcnf_code = (code, data, info)
End

(* A standard run of cake_pb_wcnf
  satisfying all the default assumptions *)
Definition cake_pb_wcnf_run_def:
  cake_pb_wcnf_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_wcnf_code mc ms
End

Theorem machine_code_sound:
  cake_pb_wcnf_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ «» ⇒
      (
        (LENGTH cl = 2 ∧
        ∃wfml.
          get_fml fs (EL 1 cl) = SOME wfml ∧
          out = concat (print_prob (mk_prob (full_encode wfml)))) ∨
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
  drule_all cake_pb_wcnf_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
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
  `a = a ^ «»` by
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
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
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
  first_x_assum (qspec_then `ext` mp_tac)>>rw[]>>
  first_x_assum (irule_at Any)>>
  conj_tac >- fs[]>>
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
