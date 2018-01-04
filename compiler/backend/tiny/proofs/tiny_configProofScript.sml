open preamble backendProofTheory
     tiny_configTheory tiny_targetProofTheory
open blastLib;

val _ = new_theory"tiny_configProof";

val is_tiny_machine_config_def = Define`
  is_tiny_machine_config mc ⇔
  mc.target = tiny_target ∧
  mc.ptr_reg = 1 ∧
  mc.len_reg = 2  ∧
  mc.ptr2_reg = 3 ∧
  mc.len2_reg = 4  ∧
  mc.callee_saved_regs = [60;61;62]`;

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val tiny_config_addr_offset_lemma = prove(
  ``tiny_config.addr_offset = (0xFFFFFF54w(* can be smaller *), 31w) /\
    (tiny_config.valid_imm (INL Add) i ⇔ 0xFFFFFFE0w ≤ i ∧ i < 1024w) /\
    (tiny_config.valid_imm (INL Sub) i ⇔ 0xFFFFFFE0w ≤ i ∧ i < 1024w)``,
  cheat); (* the offsets need to be a bit larger... *)

val tiny_backend_config_ok = Q.store_thm("tiny_backend_config_ok",`
  backend_config_ok tiny_backend_config`,
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  \\ fs[tiny_backend_config_def,(*tiny_targetTheory.tiny_config_def,*)asmTheory.offset_ok_def,
        alignmentTheory.aligned_0,tlookup_bij_iff,tiny_config_addr_offset_lemma]
  \\ fs[tiny_backend_config_def,tiny_targetTheory.tiny_config_def,asmTheory.offset_ok_def,
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
  \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO]);

val tiny_machine_config_ok = Q.store_thm("tiny_machine_config_ok",
  `is_tiny_machine_config mc ⇒ mc_conf_ok mc`,
  rw[lab_to_targetProofTheory.mc_conf_ok_def,is_tiny_machine_config_def]
  >- EVAL_TAC
  >- simp[tiny_targetProofTheory.tiny_backend_correct]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- metis_tac[asmPropsTheory.backend_correct_def,
       asmPropsTheory.target_ok_def,tiny_backend_correct]);

val tiny_init_ok = Q.store_thm("tiny_init_ok",
  `is_tiny_machine_config mc ⇒
    mc_init_ok tiny_backend_config mc`,
  rw[mc_init_ok_def]
  \\ fs[is_tiny_machine_config_def]
  \\ EVAL_TAC);

val is_tiny_machine_config_mc = tiny_init_ok |> concl |> dest_imp |> #1

val tiny_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`tiny_backend_config`, `^(rand is_tiny_machine_config_mc)`]
  |> ADD_ASSUM is_tiny_machine_config_mc
  |> SIMP_RULE (srw_ss()) [tiny_backend_config_ok,UNDISCH tiny_machine_config_ok,UNDISCH tiny_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL
  |> curry save_thm"tiny_compile_correct";

val _ = export_theory();
