open preamble
open configTheory
open backendProofTheory
open configTheory

open x64_targetProofTheory arm6_targetProofTheory arm8_targetProofTheory riscv_targetProofTheory mips_targetProofTheory

open wordsLib blastLib

val _ = new_theory"configProof";

val names_tac =
  simp[tlookup_bij_iff]
  \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val x64_machine_config_def = Define`
  x64_machine_config = <|target:= x64_target; len_reg:=6 ; ptr_reg := 7 ; callee_saved_regs := [12;13;14]|>`

val x64_conf_ok = Q.store_thm("x64_conf_ok",`
  conf_ok x64_compiler_config x64_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[x64_machine_config_def,x64_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>>NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
      (EVAL_TAC>>fs[]>>
      match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>
      fs[])
    >-
      (EVAL_TAC>>fs[]>>
      match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>
      fs[])
    >>
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)>>
  rpt (pop_assum mp_tac) >>
  fs[markerTheory.Abbrev_def]>>EVAL_TAC>>fs[]);

val arm6_machine_config_def = Define`
  arm6_machine_config = <|target:= arm6_target ; len_reg:=1  ; ptr_reg := 0 ; callee_saved_regs := [8;10;11]|>`

val arm6_conf_ok = Q.store_thm("arm6_conf_ok",`
  conf_ok arm_compiler_config arm6_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm6_machine_config_def,arm6_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>>
    fs[armTheory.EncodeARMImmediate_def,Once armTheory.EncodeARMImmediate_aux_def]>> NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
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

val arm8_machine_config_def = Define`
  arm8_machine_config = <|target:= arm8_target ; len_reg:=1  ; ptr_reg := 0 ; callee_saved_regs := [27;28;29]|>`

val arm8_conf_ok = Q.store_thm("arm8_conf_ok",`
  conf_ok arm8_compiler_config arm8_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm8_machine_config_def,arm8_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>> NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >>
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >>
  rpt (pop_assum mp_tac)>>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val riscv_machine_config_def = Define`
  riscv_machine_config = <|target:= riscv_target; len_reg:= 11 ; ptr_reg :=10 ; callee_saved_regs := [25;26;27]|>`

val riscv_conf_ok = Q.store_thm("riscv_conf_ok",`
  conf_ok riscv_compiler_config riscv_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >- fs[riscv_machine_config_def,riscv_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>> NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >>
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >>
  rpt (pop_assum mp_tac)>>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val mips_machine_config_def = Define`
  mips_machine_config = <|target:= mips_target; len_reg:=5  ; ptr_reg := 4 ; callee_saved_regs := [21;22;23]|>`

val mips_conf_ok = Q.store_thm("mips_conf_ok",`
  conf_ok mips_compiler_config mips_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >- fs[mips_machine_config_def,mips_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>> NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >-
      (simp[GSYM word_mul_n2w]>>
      srw_tac [wordsLib.WORD_MUL_LSL_ss][]>>
      qpat_abbrev_tac`w = n2w n`>>fs[]>>
      `w <= 255w ∧ 0w ≤ w` by
        (fs[Abbr`w`]>>
        dep_rewrite.DEP_REWRITE_TAC[word_le_n2w]>>
        fs[]>>
        match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>EVAL_TAC>>
      blastLib.BBLAST_PROVE_TAC)
    >>
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >>
  rpt(pop_assum mp_tac)>>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val _ = export_theory();
