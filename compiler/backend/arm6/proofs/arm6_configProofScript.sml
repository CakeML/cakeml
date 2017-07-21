open preamble backendProofTheory
     arm6_configTheory arm6_targetProofTheory
open blastLib;

val _ = new_theory"arm6_configProof";

val arm6_machine_config_def = Define`
  arm6_machine_config = <|target:= arm6_target ; len_reg:=1  ; ptr_reg := 0 ; callee_saved_regs := [8;10;11]|>`

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val arm6_conf_ok = Q.store_thm("arm6_conf_ok",`
  conf_ok arm6_backend_config arm6_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm6_machine_config_def,arm6_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>>
    fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def]>> NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
       (EVAL_TAC>>FULL_BBLAST_TAC)
    >- (simp [arm6_machine_config_def, arm6_targetTheory.arm6_target_def,
              arm6_targetTheory.arm6_config_def,
              arm6_targetTheory.valid_immediate_def,
              armTheory.EncodeARMImmediate_def,
              Once (GSYM wordsTheory.word_mul_n2w)]
        \\ qabbrev_tac `w = n2w n : word32`
        \\ `w <=+ 255w` by simp [Abbr `w`, wordsTheory.word_ls_n2w]
        \\ NTAC 16
             (simp [Once armTheory.EncodeARMImmediate_aux_def]
              \\ rw [boolTheory.COND_RAND])
        \\ blastLib.FULL_BBLAST_TAC)
    >- (simp [arm6_machine_config_def, arm6_targetTheory.arm6_target_def,
              arm6_targetTheory.arm6_config_def,
              arm6_targetTheory.valid_immediate_def,
              armTheory.EncodeARMImmediate_def,
              Once (GSYM wordsTheory.word_mul_n2w)]
        \\ qabbrev_tac `w = n2w n : word32`
        \\ `w <=+ 255w` by simp [Abbr `w`, wordsTheory.word_ls_n2w]
        \\ NTAC 16
             (simp [Once armTheory.EncodeARMImmediate_aux_def]
              \\ rw [boolTheory.COND_RAND])
        \\ blastLib.FULL_BBLAST_TAC)
    \\ fs [stack_removeTheory.store_offset_def,
           stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)>>
  rpt (pop_assum mp_tac)>>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>fs[]);

val _ = export_theory();
