(*
  End-to-end correctness of Scheme compiler
*)
Theory scheme_to_machine_code_correct
Ancestors
  scheme_ast scheme_semantics scheme_to_cake
  scheme_to_cakeProof primSemEnv primTypes
  scheme_compileCorrect ffi semantics evaluate
  lab_to_targetProof backendProof
Libs
  preamble

(* avoid wasting time printing *)
val _  = (max_print_depth := 30);

Theorem prim_sem_env_eq[local]:
  prim_sem_env scheme_out_oracle =
  SOME (init_state scheme_out_oracle, init_env)
Proof
  fs [ml_progTheory.init_env_def] \\ EVAL_TAC
QED

Theorem compile_correct_inst[local] =
  backendProofTheory.compile_correct
  |> Q.GEN ‘ffi’ |> Q.ISPEC ‘scheme_out_oracle’
  |> SRULE [prim_sem_env_eq,LET_DEF]
  |> Q.INST [‘prog’|->‘cml_prog’];

Theorem scheme_to_machine_code_value_terminates:
  scheme_semantics_prog prog (STerminate v) ∧
  static_scope_check prog = INR prog ∧
  codegen prog = INR cml_prog
  ⇒
  compile c cml_prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok c ∧ mc_conf_ok mc ∧ mc_init_ok c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
            (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
  ⇒
  machine_sem mc scheme_out_oracle ms
  ⊆
  extend_with_resource_limit {Terminate Success [v_to_string v]}
Proof
  strip_tac
  \\ dxrule_all scheme_semantics_preservation_value_terminates
  \\ simp [] \\ rpt strip_tac
  \\ dxrule semanticsPropsTheory.semantics_prog_Terminate_not_Fail
  \\ strip_tac
  \\ drule_at (Pos last) compile_correct_inst
  \\ disch_then drule
  \\ impl_tac >- simp []
  \\ simp []
QED

Theorem scheme_to_machine_code_exception_terminates:
  scheme_semantics_prog prog (SError s) ∧
  static_scope_check prog = INR prog ∧
  codegen prog = INR cml_prog
  ⇒
  compile c cml_prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok c ∧ mc_conf_ok mc ∧ mc_init_ok c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
            (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
  ⇒
  machine_sem mc scheme_out_oracle ms
  ⊆
  extend_with_resource_limit {Terminate Success [IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) (explode s)) []]}
Proof
  strip_tac
  \\ dxrule_all scheme_semantics_preservation_exception_terminates
  \\ simp [] \\ rpt strip_tac
  \\ dxrule semanticsPropsTheory.semantics_prog_Terminate_not_Fail
  \\ strip_tac
  \\ drule_at (Pos last) compile_correct_inst
  \\ disch_then drule
  \\ impl_tac >- simp []
  \\ simp []
QED

val _ = check_thm scheme_to_machine_code_value_terminates; (* asserts that no proof was cheated *)
val _ = check_thm scheme_to_machine_code_exception_terminates;
