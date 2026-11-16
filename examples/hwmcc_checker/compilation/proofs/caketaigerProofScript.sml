(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory caketaigerProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  x64_config caketaigerProgProof caketaigerCompile
Libs
  preamble

Theorem x64_config'_eq[local]:
  x64_config' = x64_backend_config
Proof
  simp[x64_config'_def]
QED

val caketaiger_terminate = UNDISCH_ALL main_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [caketaiger_compiled];

Theorem caketaiger_compiled_thm =
  MATCH_MP compile_correct (cj 1 caketaiger_compiled |> REWRITE_RULE[x64_config'_eq])
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 caketaiger_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 caketaiger_terminate)
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

Definition caketaiger_code_def:
  caketaiger_code = (code, data, info)
End

(* A standard run of caketaiger satisfying all the default assumptions *)
Definition caketaiger_run_def:
  caketaiger_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 caketaiger_code mc ms
End

Theorem machine_code_sound:
  caketaiger_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃fs' out.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout fs' out) ∧
    stdout fs = stdout fs' ∧
    main_sem cl fs fs' out
Proof
  strip_tac>>
  fs[installed_x64_def,caketaiger_code_def,caketaiger_run_def]>>
  drule_at (Pos last) caketaiger_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`ext`,`data_sp`,`cl`,`cbspace`] mp_tac)>>
  simp[]>>strip_tac>>
  qexists_tac`io_events`>>simp[]>>
  metis_tac[]
QED
