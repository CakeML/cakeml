(*
  For ASL-derived ARMv8, prove that the compiler configuration is well formed,
  and instantiate the compiler correctness theorem.
*)
Theory arm8_asl_configProof
Ancestors
  backendProof arm8_configProof arm8_config arm8_asl_targetProof
Libs
  preamble

Definition is_arm8_asl_machine_config_def:
  is_arm8_asl_machine_config mc ⇔
  mc.target = arm8_asl_target ∧
  mc.len_reg = 1  ∧
  mc.ptr_reg = 0 ∧
  mc.len2_reg = 3  ∧
  mc.ptr2_reg = 2 ∧
  mc.callee_saved_regs = [19;20;21;22;23;24;25;26;27;28]
End

Theorem arm8_asl_machine_config_ok:
  is_arm8_asl_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def, is_arm8_asl_machine_config_def]
  >- EVAL_TAC
  >- simp[arm8_asl_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC >>
  assume_tac arm8_asl_encoder_correct >>
  gvs[asmPropsTheory.encoder_correct_def, asmPropsTheory.target_ok_def]
QED

Theorem arm8_asl_init_ok:
  is_arm8_asl_machine_config mc ⇒ mc_init_ok arm8_config arm8_backend_config mc
Proof
  rw[mc_init_ok_def] >> gvs[is_arm8_asl_machine_config_def] >> EVAL_TAC
QED

val is_arm8_asl_machine_config_mc = arm8_asl_init_ok |> concl |> dest_imp |> #1

Theorem arm8_asl_compile_correct =
  compile_correct
  |> Q.GENL[`asm_conf`,`c`,`mc`]
  |> Q.ISPECL[`arm8_config`, `arm8_backend_config`, `^(rand is_arm8_asl_machine_config_mc)`]
  |> ADD_ASSUM is_arm8_asl_machine_config_mc
  |> SIMP_RULE (srw_ss()) [arm8_backend_config_ok,UNDISCH arm8_asl_machine_config_ok,UNDISCH arm8_asl_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
