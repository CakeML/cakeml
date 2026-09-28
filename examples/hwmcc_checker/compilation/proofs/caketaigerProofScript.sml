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

val caketaiger_io_events_def = new_specification("caketaiger_io_events_def",["caketaiger_io_events"],
  main_semantics |> Q.GENL[`ext`,`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (caketaiger_sem,caketaiger_output) = caketaiger_io_events_def |> SPEC_ALL
  |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR;
val (caketaiger_not_fail,caketaiger_sem_sing) = caketaiger_sem
  |> SRULE [caketaiger_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR;

Theorem x64_config'_eq[local]:
  x64_config' = x64_backend_config
Proof
  simp[x64_config'_def]
QED

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 caketaiger_compiled |> REWRITE_RULE[x64_config'_eq])
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP caketaiger_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[caketaiger_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem caketaiger_compiled_thm =
  CONJ compile_correct_applied caketaiger_output
  |> DISCH_ALL
  |> check_thm

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # backend$config))
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
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (caketaiger_io_events ext cl fs)} ∧
  ∃fs' out.
    extract_fs ext (cl,fs) (caketaiger_io_events ext cl fs) =
      SOME (add_stdout fs' out) ∧
    stdout fs = stdout fs' ∧
    main_sem cl fs fs' out
Proof
  strip_tac>>
  fs[installed_x64_def,caketaiger_code_def,caketaiger_run_def]>>
  drule_at (Pos last) caketaiger_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`ext`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>>
  rw[]>>simp[]>>
  metis_tac[]
QED
