(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory distrupProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  distrupCompile distrup_fullProg
Libs
  preamble

val distrup_terminate = semantics_prog_distrup_prog
  |> REWRITE_RULE [GSYM (UNDISCH (Q.INST [‘prog’ |-> ‘distrup_prog’]
                                    ml_progTheory.semantics_dec_list_eq))]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> DISCH_ALL |> SRULE [distrup_array_compiled];

Theorem distrup_compiled_thm =
  MATCH_MP compile_correct (cj 1 distrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 distrup_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 distrup_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm

Definition compiled_code_installed_def:
  compiled_code_installed mc ms ⇔
    ∃cbspace data_sp.
      is_x64_machine_config mc ∧
      installed code cbspace data data_sp info.lab_conf.ffi_names
                (heap_regs x64_backend_config.stack_conf.reg_names) mc
                info.lab_conf.shmem_extra ms
End

Overload custom_ffi = “λ(inputs,tb). custom_ffi (State Step inputs tb)”;

Theorem compiled_code_produces_events_ok:
  compiled_code_installed mc ms ⇒
  ∀inputs.
    ∃events.
      machine_sem mc (custom_ffi inputs) ms ⊆
      extend_with_resource_limit {Terminate Success events} ∧
      full_events_ok init_st events
Proof
  rw [compiled_code_installed_def,FORALL_PROD] >>
  drule_all distrup_compiled_thm >>
  simp []
QED
