(*
  For ARMv7, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)
open preamble backendProofTheory
     arm7_configTheory arm7_targetProofTheory
open blastLib;

val _ = new_theory"arm7_configProof";

val is_arm7_machine_config_def = Define`
  is_arm7_machine_config mc ⇔
  mc.target = arm7_target ∧
  mc.len_reg = 1  ∧
  mc.ptr_reg = 0 ∧
  mc.len2_reg = 3  ∧
  mc.ptr2_reg = 2 ∧
  mc.callee_saved_regs = [8;10;11]`;

val _ = computeLib.add_funs [arm7_names_def];

val names_tac =
  simp[tlookup_bij_iff, arm7_names_def] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem arm7_backend_config_ok:
  backend_config_ok arm7_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >> TRY(fs[arm7_backend_config_def]>>NO_TAC)
  >- (EVAL_TAC>> blastLib.FULL_BBLAST_TAC)
  >- (EVAL_TAC >> fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def])
  >- (EVAL_TAC >> fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def])
  >- (EVAL_TAC >> fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def])
  >- (EVAL_TAC >> fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def])
  >- names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ EVAL_TAC>>fs[]
  \\ simp [armTheory.EncodeARMImmediate_def,
           Once (GSYM wordsTheory.word_mul_n2w)]
  \\ qabbrev_tac `w = n2w n : word32`
  \\ `w <=+ 255w` by simp [Abbr `w`, wordsTheory.word_ls_n2w]
  \\ NTAC 16
       (simp [Once armTheory.EncodeARMImmediate_aux_def]
        \\ rw [boolTheory.COND_RAND])
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem arm7_machine_config_ok:
  is_arm7_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_arm7_machine_config_def]
  >- EVAL_TAC
  >- simp[arm7_targetProofTheory.arm7_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,arm7_encoder_correct]
QED

Theorem arm7_init_ok:
  is_arm7_machine_config mc ⇒
    mc_init_ok arm7_backend_config mc
Proof
  rw[mc_init_ok_def] \\
  fs[is_arm7_machine_config_def] \\
  EVAL_TAC
QED

val is_arm7_machine_config_mc = arm7_init_ok |> concl |> dest_imp |> #1

val arm7_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`arm7_backend_config`, `^(rand is_arm7_machine_config_mc)`]
  |> ADD_ASSUM is_arm7_machine_config_mc
  |> SIMP_RULE (srw_ss()) [arm7_backend_config_ok,UNDISCH arm7_machine_config_ok,UNDISCH arm7_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
  |> curry save_thm"arm7_compile_correct";

val _ = export_theory();
