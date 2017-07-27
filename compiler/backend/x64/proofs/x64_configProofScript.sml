open preamble backendProofTheory
open x64_configTheory x64_targetProofTheory
open blastLib;

val _ = new_theory"x64_configProof";

val x64_machine_config_def = Define`
  x64_machine_config = <|target:= x64_target; len_reg:=6 ; ptr_reg := 7 ; callee_saved_regs := [12;13;14]|>`;

val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val x64_conf_ok = Q.store_thm("x64_conf_ok",`
  conf_ok x64_backend_config x64_machine_config`,
  simp[conf_ok_def,lower_conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[x64_machine_config_def,x64_backend_correct]
  >- names_tac
  >-
    (rw[conf_constraint_def]>>
    TRY(EVAL_TAC>>fs[]>>NO_TAC)>>
    fs[stack_removeTheory.max_stack_alloc_def]
    >-
      (EVAL_TAC>>
      blastLib.FULL_BBLAST_TAC)
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

val _ = export_theory();
