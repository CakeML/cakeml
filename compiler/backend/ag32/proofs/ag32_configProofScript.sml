(*
  For ag32, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)
open preamble backendProofTheory ag32_configTheory
     ag32_targetProofTheory open blastLib;

val _ = new_theory"ag32_configProof";

val is_ag32_machine_config_def = Define`
  is_ag32_machine_config mc ⇔
  mc.target = ag32_target ∧
  mc.ptr_reg = 1 ∧
  mc.len_reg = 2  ∧
  mc.ptr2_reg = 3 ∧
  mc.len2_reg = 4  ∧
  mc.callee_saved_regs = [60;61;62]`;

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem ag32_backend_config_ok:
    backend_config_ok ag32_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  \\ fs[ag32_backend_config_def,asmTheory.offset_ok_def,
        alignmentTheory.aligned_0,tlookup_bij_iff]
  \\ fs[ag32_backend_config_def,ag32_targetTheory.ag32_config_def,asmTheory.offset_ok_def,
        alignmentTheory.aligned_0,tlookup_bij_iff]
  THEN1 blastLib.FULL_BBLAST_TAC
  THEN1 names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ EVAL_TAC>>fs[]
  \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO]
QED

Theorem ag32_machine_config_ok:
   is_ag32_machine_config mc ⇒ mc_conf_ok mc
Proof
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_ag32_machine_config_def]
  >- EVAL_TAC
  >- simp[ag32_encoder_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.encoder_correct_def,
       asmPropsTheory.target_ok_def,ag32_encoder_correct]
QED

Theorem ag32_init_ok:
   is_ag32_machine_config mc ⇒
    mc_init_ok ag32_backend_config mc
Proof
  rw[mc_init_ok_def]
  \\ fs[is_ag32_machine_config_def]
  \\ EVAL_TAC
QED

val is_ag32_machine_config_mc = ag32_init_ok |> concl |> dest_imp |> #1

val ag32_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`ag32_backend_config`, `^(rand is_ag32_machine_config_mc)`]
  |> ADD_ASSUM is_ag32_machine_config_mc
  |> SIMP_RULE (srw_ss()) [ag32_backend_config_ok,UNDISCH ag32_machine_config_ok,UNDISCH ag32_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
  |> curry save_thm"ag32_compile_correct";

val _ = export_theory();
