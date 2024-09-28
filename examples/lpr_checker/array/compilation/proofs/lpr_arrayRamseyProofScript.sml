(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     satSemTheory lprTheory lpr_listTheory lpr_arrayRamseyProgTheory
     lpr_parsingTheory lpr_arrayRamseyCompileTheory lpr_composeProgTheory
     lpr_listTheory ramseyTheory;

val _ = new_theory"lpr_arrayRamseyProof";

val check_unsat_io_events_def = new_specification("check_unsat_io_events_def",["check_unsat_io_events"],
  check_unsat_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (check_unsat_sem,check_unsat_output) = check_unsat_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (check_unsat_not_fail,check_unsat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail check_unsat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 lpr_ramsey_compiled)
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

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
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
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (check_unsat_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (check_unsat_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  (out ≠ strlit "" ⇒
    if LENGTH cl = 1 then
      out = concat (print_dimacs (enc ()))
    else if LENGTH cl = 2 then
      out = strlit "s VERIFIED UNSAT\n" ∧
      ramsey_number 4 = 18
    else F)
Proof
  strip_tac>>
  fs[installed_x64_def,check_unsat_code_def,ramsey_run_def]>>
  drule check_unsat_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>>
  strip_tac>>
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

val _ = export_theory();
