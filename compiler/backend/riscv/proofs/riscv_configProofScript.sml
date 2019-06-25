(*
  For RISC-V, prove that the compiler configuration is well formed,
  and instantiate the compiler correctness theorem.
*)
open preamble backendProofTheory
     riscv_configTheory riscv_targetProofTheory
open blastLib;

val _ = new_theory"riscv_configProof";

val is_riscv_machine_config_def = Define`
  is_riscv_machine_config mc ⇔
  mc.target = riscv_target ∧
  mc.len_reg = 11  ∧
  mc.ptr_reg = 10 ∧
  mc.len2_reg = 13  ∧
  mc.ptr2_reg = 12 ∧
  mc.callee_saved_regs = [25;26;27]`;

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem riscv_backend_config_ok:
    backend_config_ok riscv_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[riscv_backend_config_def]
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
  \\ EVAL_TAC>>fs[]
  \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ fs[]
QED

Theorem riscv_machine_config_ok:
   is_riscv_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_riscv_machine_config_def]
  >- EVAL_TAC
  >- simp[riscv_targetProofTheory.riscv_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.encoder_correct_def,asmPropsTheory.target_ok_def,riscv_encoder_correct]
QED

Theorem riscv_init_ok:
   is_riscv_machine_config mc ⇒
    mc_init_ok riscv_backend_config mc
Proof
  rw[mc_init_ok_def] \\
  fs[is_riscv_machine_config_def] \\
  EVAL_TAC
QED

val is_riscv_machine_config_mc = riscv_init_ok |> concl |> dest_imp |> #1

val riscv_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`riscv_backend_config`, `^(rand is_riscv_machine_config_mc)`]
  |> ADD_ASSUM is_riscv_machine_config_mc
  |> SIMP_RULE (srw_ss()) [riscv_backend_config_ok,UNDISCH riscv_machine_config_ok,UNDISCH riscv_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
  |> curry save_thm"riscv_compile_correct";

val _ = export_theory();
