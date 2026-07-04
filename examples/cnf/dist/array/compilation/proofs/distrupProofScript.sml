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

val not_fail = MATCH_MP semantics_prog_Terminate_not_Fail semantics_prog_distrup_prog |> cj 1;
val sem_sing = MATCH_MP semantics_prog_Terminate_not_Fail semantics_prog_distrup_prog |> cj 2;

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 distrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> Q.GEN ‘ffi’ |> Q.ISPEC ‘custom_ffi (State Step inputs tb)’
  |> C MATCH_MP not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> C MATCH_MP (UNDISCH x64_machine_config_ok)
  |> C MATCH_MP (UNDISCH x64_init_ok)
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO, sem_sing]

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
  drule_all compile_correct_applied >>
  metis_tac [full_events_ok_main_events]
QED
