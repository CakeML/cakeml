open preamble
open configTheory
open backendProofTheory
open configTheory

open x64_targetProofTheory arm6_targetProofTheory arm8_targetProofTheory riscv_targetProofTheory mips_targetProofTheory

open wordsLib blastLib

val _ = new_theory"configProof";

val find_name_id = Q.store_thm("find_name_id",
  `x ∉ domain names
   ⇒ find_name names x = x`,
  rw[stack_namesTheory.find_name_def]
  \\ fs[domain_lookup] \\ CASE_TAC \\ fs[]);

val find_name_bij_suff = Q.store_thm("find_name_bij_suff",
  `set (toList names) = domain names ⇒
   BIJ (find_name names) UNIV UNIV`,
  strip_tac
  \\ match_mp_tac BIJ_support
  \\ qexists_tac`domain names`
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[stack_namesTheory.find_name_def]
    \\ CASE_TAC \\ fs[domain_lookup])
  \\ `set (toList names) = IMAGE (find_name names) (domain names)`
  by (
    pop_assum kall_tac
    \\ simp[EXTENSION,stack_namesTheory.find_name_def,MEM_toList,domain_lookup]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (qexists_tac`k` \\ fs[])
    \\ metis_tac[] )
  \\ match_mp_tac (MP_CANON CARD_IMAGE_ID_BIJ)
  \\ fs[] \\ rw[] \\ fs[EXTENSION]
  \\ metis_tac[]);

val find_name_bij_iff = Q.store_thm("find_name_bij_iff",
  `BIJ (find_name names) UNIV UNIV ⇔
   set (toList names) = domain names`,
  rw[EQ_IMP_THM,find_name_bij_suff]
  \\ fs[BIJ_IFF_INV]
  \\ rw[EXTENSION,domain_lookup,MEM_toList]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`k=x` >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ `find_name names x = x`
    by (
      simp[stack_namesTheory.find_name_def]
      \\ CASE_TAC \\ fs[] )
    \\ `find_name names k = x`
    by ( simp[stack_namesTheory.find_name_def] )
    \\ metis_tac[] )
  \\ Cases_on`x=v` >- metis_tac[]
  \\ spose_not_then strip_assume_tac
  \\ `find_name names x = v`
  by ( simp[stack_namesTheory.find_name_def] )
  \\ `∀k. find_name names k ≠ x`
  by (
    rw[stack_namesTheory.find_name_def]
    \\ CASE_TAC \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[])
  \\ metis_tac[] )

val names_tac =
  simp[find_name_bij_iff]
  \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val x64_machine_config_def = Define`
  x64_machine_config = <|target:= x64_target; len_reg:=6 ; ptr_reg := 7 ; callee_saved_regs := [12;13;14]|>`

val INDEX_FIND_CONS_EQ_SOME = store_thm("INDEX_FIND_CONS_EQ_SOME",
  ``(INDEX_FIND n f (x::xs) = SOME y) <=>
    (f x /\ (y = (n,x))) \/
    (~f x /\ (INDEX_FIND (n+1) f xs = SOME y))``,
  fs [INDEX_FIND_def] \\ rw [] \\ Cases_on `y` \\ fs [ADD1] \\ metis_tac []);

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
