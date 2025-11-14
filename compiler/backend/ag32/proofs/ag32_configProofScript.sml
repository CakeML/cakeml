(*
  For ag32, prove that the compiler configuration is well formed, and
  instantiate the compiler correctness theorem.
*)
Theory ag32_configProof
Ancestors
  lab_to_targetProof backendProof ag32_config ag32_targetProof
Libs
  preamble blastLib

Definition is_ag32_machine_config_def:
  is_ag32_machine_config mc ⇔
  mc.target = ag32_target ∧
  mc.ptr_reg = 1 ∧
  mc.len_reg = 2  ∧
  mc.ptr2_reg = 3 ∧
  mc.len2_reg = 4  ∧
  mc.callee_saved_regs = [60;61;62]
End

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

Theorem ag32_compile_correct =
  compile_correct
  |> Q.GENL[`c`,`mc`]
  |> Q.ISPECL[`ag32_backend_config`, `^(rand is_ag32_machine_config_mc)`]
  |> ADD_ASSUM is_ag32_machine_config_mc
  |> SIMP_RULE (srw_ss()) [ag32_backend_config_ok,UNDISCH ag32_machine_config_ok,UNDISCH ag32_init_ok]
  |> CONV_RULE (ONCE_DEPTH_CONV(EVAL o (assert(same_const``heap_regs``o fst o strip_comb))))
  |> DISCH_ALL

Theorem get_shmem_info_LENGTH:
  ∀xs c l1 l2.
    get_shmem_info xs c l1 l2 = (t1,t2) ∧ LENGTH l1 = LENGTH l2 ⇒
    LENGTH t1 = LENGTH t2
Proof
  ho_match_mp_tac lab_to_targetTheory.get_shmem_info_ind \\ rw []
  \\ gvs [lab_to_targetTheory.get_shmem_info_def]
  \\ pairarg_tac \\ gvs []
QED

Theorem IMP_EVERY_list_add_if_fresh[local]:
  ∀xs x p. p x ∧ EVERY p xs ⇒ EVERY p (list_add_if_fresh x xs)
Proof
  Induct \\ gvs [lab_to_targetTheory.list_add_if_fresh_def] \\ rw []
QED

Theorem find_ffi_names_ExtCall:
  ∀xs. EVERY (λx. ∃i. ExtCall i = x) (find_ffi_names xs)
Proof
  ho_match_mp_tac lab_to_targetTheory.find_ffi_names_ind
  \\ rpt strip_tac
  \\ asm_rewrite_tac [lab_to_targetTheory.find_ffi_names_def,EVERY_DEF]
  \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘a’ \\ gvs []
  \\ irule IMP_EVERY_list_add_if_fresh \\ gvs []
QED

Theorem MAP_ExtCall_ffinames:
  ∀xs.
    EVERY (λx. ∃i. ExtCall i = x) xs ⇒
    xs = MAP ExtCall (ffinames_to_string_list xs)
Proof
  Induct \\ gvs [backendTheory.ffinames_to_string_list_def]
  \\ Cases \\ gvs [backendTheory.ffinames_to_string_list_def]
QED

Theorem compile_imp_ffi_names:
  backend$compile c p = SOME (b,d,c1) ∧
  c1.lab_conf.shmem_extra = [] ∧ f ≠ [] ∧
  c.lab_conf.ffi_names = NONE ∧
  ffinames_to_string_list (the [] c1.lab_conf.ffi_names) = f ⇒
  c1.lab_conf.ffi_names = SOME (MAP ExtCall f)
Proof
  Cases_on ‘c1.lab_conf.ffi_names’
  \\ gvs [miscTheory.the_def,backendTheory.ffinames_to_string_list_def]
  \\ gvs [backendTheory.compile_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [oneline backendTheory.attach_bitmaps_def, AllCaseEqs()]
  \\ strip_tac \\ gvs []
  \\ gvs [lab_to_targetTheory.compile_def]
  \\ gvs [lab_to_targetTheory.compile_lab_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule get_shmem_info_LENGTH \\ gvs [] \\ rw []
  \\ irule MAP_ExtCall_ffinames
  \\ gvs [find_ffi_names_ExtCall]
QED
