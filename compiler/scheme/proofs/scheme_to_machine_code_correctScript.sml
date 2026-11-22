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

(* without an eval state, the eval oracle does not affect the semantics *)
Theorem evaluate_prog_with_clock_eval_oracle[local]:
  s.eval_state = NONE ⇒
  evaluate_prog_with_clock (s with eval_oracle := eo) env k p =
  evaluate_prog_with_clock s env k p
Proof
  rw [evaluate_prog_with_clock_def]
  \\ Cases_on ‘evaluate_decs (s with clock := k) env p’
  \\ drule (cj 3 evaluatePropsTheory.eval_no_eval_oracle)
  \\ simp []
  \\ disch_then (qspec_then ‘eo’ mp_tac)
  \\ ‘s with <|eval_oracle := eo; clock := k|> =
      s with <|clock := k; eval_oracle := eo|>’
    by simp [semanticPrimitivesTheory.state_component_equality]
  \\ simp []
QED

Theorem semantics_determ_eval_oracle[local]:
  s.eval_state = NONE ⇒
  semantics_determ (s with eval_oracle := eo) env p =
  semantics_determ s env p
Proof
  rw [FUN_EQ_THM] \\ Cases_on ‘x’
  \\ simp [semantics_determ_def, evaluate_prog_with_clock_eval_oracle]
QED

Theorem semantics_prog_sing[local]:
  (∀po. semantics_determ (s with ptr_eq_oracle := po) env p b) ∧
  s.eval_state = NONE ⇒
  (semantics_prog s env p Fail ⇔ b = Fail) ∧ semantics_prog s env p = {b}
Proof
  strip_tac
  \\ ‘∀po eo.
        semantics_determ (s with <|ptr_eq_oracle := po; eval_oracle := eo|>)
          env p =
        semantics_determ (s with ptr_eq_oracle := po) env p’
    by (rpt gen_tac
        \\ ‘s with <|ptr_eq_oracle := po; eval_oracle := eo|> =
            (s with ptr_eq_oracle := po) with eval_oracle := eo’
          by simp [semanticPrimitivesTheory.state_component_equality]
        \\ pop_assum SUBST1_TAC
        \\ irule semantics_determ_eval_oracle \\ simp [])
  \\ rw [semantics_prog_def, FUN_EQ_THM]
  \\ metis_tac [semanticsPropsTheory.semantics_determ_deterministic]
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
  compile asm_conf c cml_prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok asm_conf c ∧ mc_conf_ok mc ∧ mc_init_ok asm_conf c mc ∧
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
  \\ dxrule semantics_prog_sing
  \\ impl_tac >- EVAL_TAC
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
  compile asm_conf c cml_prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok asm_conf c ∧ mc_conf_ok mc ∧ mc_init_ok asm_conf c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
            (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
  ⇒
  machine_sem mc scheme_out_oracle ms
  ⊆
  extend_with_resource_limit {Terminate Success [IO_event (ExtCall «scheme_out») (MAP (n2w o ORD) (explode s)) []]}
Proof
  strip_tac
  \\ dxrule_all scheme_semantics_preservation_exception_terminates
  \\ simp [] \\ rpt strip_tac
  \\ dxrule semantics_prog_sing
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ drule_at (Pos last) compile_correct_inst
  \\ disch_then drule
  \\ impl_tac >- simp []
  \\ simp []
QED

Theorem scheme_to_machine_code_diverges:
  scheme_semantics_prog prog SDiverge ∧
  static_scope_check prog = INR prog ∧
  codegen prog = INR cml_prog
  ⇒
  compile asm_conf c cml_prog = SOME (bytes,bitmaps,c') ∧
  backend_config_ok asm_conf c ∧ mc_conf_ok mc ∧ mc_init_ok asm_conf c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
            (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
  ⇒
  machine_sem mc scheme_out_oracle ms
  ⊆
  extend_with_resource_limit {Diverge [||]}
Proof
  strip_tac
  \\ dxrule_all scheme_semantics_preservation_diverges
  \\ simp [] \\ rpt strip_tac
  \\ dxrule semantics_prog_sing
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ drule_at (Pos last) compile_correct_inst
  \\ disch_then drule
  \\ impl_tac >- simp []
  \\ simp []
QED

(* asserts that no proof was cheated *)
val _ = check_thm scheme_to_machine_code_value_terminates;
val _ = check_thm scheme_to_machine_code_exception_terminates;
val _ = check_thm scheme_to_machine_code_diverges;
