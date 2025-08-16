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
  is_arm8_asl_machine_config mc ⇒ mc_init_ok arm8_backend_config mc
Proof
  rw[mc_init_ok_def] >> gvs[is_arm8_asl_machine_config_def] >> EVAL_TAC
QED

Theorem arm8_asl_compile_correct:
  is_arm8_asl_machine_config mc ∧
  compile arm8_backend_config prog = SOME (bytes, bitmaps, config') ⇒
    let (s,env) = THE (prim_sem_env ffi) in
    ¬semantics_prog s env prog Fail ∧
    installed bytes cbspace bitmaps data_sp config'.lab_conf.ffi_names (1,3) mc config'.lab_conf.shmem_extra ms
    ⇒ machine_sem mc ffi ms ⊆
        extend_with_resource_limit (semantics_prog s env prog)
Proof
  rw[] >>
  qspecl_then [
    `prog`,`ms`,`mc`,`ffi`,`data_sp`,`cbspace`,`config'`,
    `arm8_backend_config`,`bytes`,`bitmaps`] assume_tac $ GEN_ALL compile_correct >>
  gvs[] >> pairarg_tac >> gvs[] >>
  rw[] >>
  first_x_assum irule >> simp[] >>
  map_every (irule_at Any)
    [arm8_asl_init_ok, arm8_backend_config_ok, arm8_asl_machine_config_ok] >>
  simp[arm8_backend_config_def, heap_regs_def, arm8_names_def,
       tlookup_def, lookup_def]
QED
