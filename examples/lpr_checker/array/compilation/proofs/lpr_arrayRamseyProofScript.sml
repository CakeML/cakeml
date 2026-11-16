(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory lpr_arrayRamseyProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof satSem
  lpr lpr_list lpr_arrayRamseyProg lpr_parsing
  lpr_arrayRamseyCompile lpr_composeProg lpr_list ramsey
Libs
  preamble

val check_unsat_terminate = UNDISCH_ALL check_unsat_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [lpr_ramsey_compiled];

Theorem check_unsat_compiled_thm =
  MATCH_MP compile_correct (cj 1 lpr_ramsey_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 check_unsat_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 check_unsat_terminate)
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

Definition check_unsat_code_def:
  check_unsat_code = (code, data, info)
End

(* A standard run of ramsey satisfying all the default assumptions *)
Definition ramsey_run_def:
  ramsey_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 check_unsat_code mc ms
End

Theorem TL_eq_hd_exists:
  TL cl = ls ⇒
  (ls ≠ [] ⇒ ∃x. cl = x :: ls)
Proof
  Cases_on`cl`>>rw[]
QED

Theorem machine_code_sound:
  ramsey_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
  (out ≠ «» ⇒
    if LENGTH cl = 1 then
      out = concat (print_dimacs (enc ()))
    else if LENGTH cl = 2 then
      out = «s VERIFIED UNSAT\n» ∧
      ramsey_number 4 = 18
    else F)
Proof
  strip_tac>>
  fs[installed_x64_def,check_unsat_code_def,ramsey_run_def]>>
  drule_all check_unsat_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  qexists_tac`out`>>
  qexists_tac`err`>>
  fs[check_unsat_sem_def]>>
  pop_assum mp_tac>>
  fs[CasePred "list"]>> strip_tac>> gvs[]>>
  drule TL_eq_hd_exists>> simp[]>>strip_tac>>gvs[]
  >- ( (* encoding *)
    Cases_on`cl`>>fs[CommandLineProofTheory.wfcl_def]>>
    fs[check_unsat_0_sem_def])
  >- ( (* proof given *)
    rw[]>>gvs[check_unsat_1_sem_def]>>
    match_mp_tac ramsey_eq>>simp[not_is_ramsey_4_17]>>
    match_mp_tac ramsey_lpr_correct>>
    match_mp_tac (GEN_ALL lpr_arrayParsingProgTheory.check_lpr_unsat_list_sound)>>
    fs[enc_def]>>
    asm_exists_tac>>simp[]>>
    metis_tac[ramsey_lpr_wf])
QED
