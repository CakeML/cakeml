(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory mcnfProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  mcnfProg mcnfCompile
Libs
  preamble

val cake_pb_mcnf_io_events_def = new_specification("cake_pb_mcnf_io_events_def",["cake_pb_mcnf_io_events"],
  main_semantics |> Q.GENL[`ext`,`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_pb_mcnf_sem,cake_pb_mcnf_output) = cake_pb_mcnf_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_pb_mcnf_not_fail,cake_pb_mcnf_sem_sing) = cake_pb_mcnf_sem
  |> SRULE [mcnf_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 mcnf_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_pb_mcnf_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_pb_mcnf_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_pb_mcnf_compiled_thm =
  CONJ compile_correct_applied cake_pb_mcnf_output
  |> DISCH_ALL
  (* |> check_thm *)

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

Definition cake_pb_mcnf_code_def:
  cake_pb_mcnf_code = (code, data, info)
End

(* A standard run of cake_pb_mcnf
  satisfying all the default assumptions *)
Definition cake_pb_mcnf_run_def:
  cake_pb_mcnf_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_mcnf_code mc ms
End

Theorem machine_code_sound:
  cake_pb_mcnf_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_pb_mcnf_io_events ext cl fs)} ∧
  ∃out err.
    extract_fs ext (cl,fs) (cake_pb_mcnf_io_events ext cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ «» ⇒
      (
        (LENGTH cl = 2 ∧
        ∃mfml.
          get_mfml fs (EL 1 cl) = SOME mfml ∧
          out = concat (print_mo_prob (full_encode_mcnf mfml))) ∨
        (LENGTH cl = 3 ∧
        ∃mfml vs.
          get_mfml fs (EL 1 cl) = SOME mfml ∧
          out = print_front_str vs ∧
          mcnf_sem mfml vs)
      )
    )
Proof
  strip_tac>>
  fs[installed_x64_def,cake_pb_mcnf_code_def,cake_pb_mcnf_run_def]>>
  drule_at (Pos last) cake_pb_mcnf_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`ext`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  every_case_tac>>fs[]
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_2_sem_def,get_mfml_def]>>
    strip_tac>>gvs[]>>
    metis_tac[])
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_1_sem_def,get_mfml_def]>>
    strip_tac>>gvs[]>>
    every_case_tac>>fs[])>>
  metis_tac[]
QED

val chk = machine_code_sound |> check_thm;

(* Specialized to a run that reports a verified Pareto frontier *)
Theorem machine_code_sound_front:
  cake_pb_mcnf_run cl fs mc ms ⇒
  ∃out err.
    extract_fs ext (cl,fs) (cake_pb_mcnf_io_events ext cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (
    LENGTH cl = 3 ∧ out ≠ «» ⇒
      ∃mfml vs.
        get_mfml fs (EL 1 cl) = SOME mfml ∧
        out = print_front_str vs ∧
        set vs = nondom_costs mfml
    )
Proof
  rw[]>>
  drule machine_code_sound>>rw[]>>
  first_x_assum (qspec_then `ext` mp_tac)>>rw[]>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  gvs[mcnfProgTheory.mcnf_sem_def]>>
  metis_tac[]
QED
