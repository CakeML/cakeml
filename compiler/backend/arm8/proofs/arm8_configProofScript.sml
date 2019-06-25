(*
  For ARMv8, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)
open preamble backendProofTheory
     arm8_configTheory arm8_targetProofTheory
open blastLib;

val _ = new_theory"arm8_configProof";

val is_arm8_machine_config_def = Define`
  is_arm8_machine_config mc ⇔
  mc.target = arm8_target ∧
  mc.len_reg =1  ∧
  mc.ptr_reg = 0 ∧
  mc.len2_reg =3  ∧
  mc.ptr2_reg = 2 ∧
  mc.callee_saved_regs = [27;28;29]`;

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem arm8_backend_config_ok:
    backend_config_ok arm8_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm8_backend_config_def]
  >- (EVAL_TAC>> blastLib.FULL_BBLAST_TAC)
  >- names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ simp[GSYM word_mul_n2w]>>
  srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
  qpat_abbrev_tac`w = n2w n`>>fs[]>>
  `w <= 255w ∧ 0w ≤ w` by
    (fs[Abbr`w`]>>
    dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
    fs[]>>
    match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>EVAL_TAC>>
  blastLib.BBLAST_PROVE_TAC
QED

Theorem arm8_machine_config_ok:
   is_arm8_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_arm8_machine_config_def]
  >- EVAL_TAC
  >- simp[arm8_targetProofTheory.arm8_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,arm8_encoder_correct]
QED

Theorem arm8_init_ok:
   is_arm8_machine_config mc ⇒
    mc_init_ok arm8_backend_config mc
Proof
  rw[mc_init_ok_def] \\
  fs[is_arm8_machine_config_def] \\
  EVAL_TAC
QED

val is_arm8_machine_config_mc = arm8_init_ok |> concl |> dest_imp |> #1

val arm8_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`arm8_backend_config`, `^(rand is_arm8_machine_config_mc)`]
  |> ADD_ASSUM is_arm8_machine_config_mc
  |> SIMP_RULE (srw_ss()) [arm8_backend_config_ok,UNDISCH arm8_machine_config_ok,UNDISCH arm8_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
  |> curry save_thm"arm8_compile_correct";

val _ = export_theory();
