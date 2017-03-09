open preamble word_removeTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_removeProof";

(* semantics *)
val alloc_termdep_code_frame = Q.prove(`
  alloc c names (s with <|termdep:=d;code:=l|>) =
  (FST (alloc c names s),SND(alloc c names s) with <|termdep:=d;code:=l|>)`,
  full_simp_tac(srw_ss())[alloc_def]>>TOP_CASE_TAC>>
  full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,gc_def,set_store_def]>>
  ntac 3(FULL_CASE_TAC>>full_simp_tac(srw_ss())[])
  >-
    (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[pop_env_def]>>
  ntac 3(FULL_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def])>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[has_space_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])|>INST_TYPE[beta|->alpha,gamma|->beta,delta|->alpha]

val get_vars_termdep_code_frame = Q.prove(`
  ∀ls.
  get_vars ls s = get_vars ls (s with <|termdep:=0;code:=l|>)`,
  Induct>>full_simp_tac(srw_ss())[get_vars_def,get_var_def])

val word_exp_termdep_code_frame = Q.prove(`
  ∀s exp.
  word_exp s exp = word_exp (s with <|termdep:=0;code:=l|>) exp`,
  ho_match_mp_tac word_exp_ind>>
  full_simp_tac(srw_ss())[word_exp_def,LET_THM,mem_load_def]>>
  full_simp_tac(srw_ss())[EVERY_MAP,EVERY_MEM]>>srw_tac[][]>>
  AP_THM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC>> AP_TERM_TAC>>
  full_simp_tac(srw_ss())[MAP_EQ_f])

val tac = (full_simp_tac(srw_ss())[GSYM word_exp_termdep_code_frame]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality,set_store_def,mem_store_def])

val push_env_code = Q.prove(`
  (push_env x handler s).code = s.code`,
  Cases_on`handler`>>TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def])

val pop_env_termdep_code_frame = Q.prove(`
  pop_env (r' with <|termdep:=0; code:=l|>) =
  lift (λs. s with <|termdep:=0;code:=l|>) (pop_env r')`,
  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])

val word_remove_correct = Q.store_thm("word_remove_correct",`
  ∀prog st res rst.
  (!n v p. lookup n st.code = SOME (v,p) ==>
         lookup n l = SOME (v,remove_must_terminate p)) ∧
  evaluate(prog,st) = (res,rst) ∧
  res ≠ SOME Error ⇒
  ∃clk.
  evaluate(remove_must_terminate prog,st with <|clock:=st.clock+clk;termdep:=0;code:=l|>) = (res,rst with <|termdep:=0;code:=l|>)`,
  recInduct evaluate_ind>>
  full_simp_tac(srw_ss())[evaluate_def,remove_must_terminate_def,state_component_equality,call_env_def,get_var_def,set_var_def,dec_clock_def]>>srw_tac[][]
  >-
    (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac alloc_const>>
    simp[alloc_termdep_code_frame,state_component_equality])
  >-
    (simp[GSYM get_vars_termdep_code_frame]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[set_vars_def,state_component_equality]>>rev_full_simp_tac(srw_ss())[])
  >-
    (Cases_on`i`>>full_simp_tac(srw_ss())[inst_def,state_component_equality,assign_def,GSYM word_exp_termdep_code_frame,get_var_def,GSYM get_vars_termdep_code_frame,LET_THM]>>
    rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[set_var_def,state_component_equality,mem_load_def,get_var_def,mem_store_def]))
  >- tac
  >- tac
  >- tac
  >- (tac>>FULL_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality])
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (*hard*)
    (qpat_x_assum`A=(res,rst)`mp_tac>>simp[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    rveq>>
    res_tac>>
    imp_res_tac evaluate_dec_clock>>full_simp_tac(srw_ss())[]>>
    imp_res_tac evaluate_add_clock>>full_simp_tac(srw_ss())[]>>
    pop_assum kall_tac>>
    first_x_assum(qspec_then`s.clock` assume_tac)>>
    metis_tac[])
  >-
    (qpat_x_assum`A=(res,rst)`mp_tac>>simp[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>-
      (strip_tac>>full_simp_tac(srw_ss())[]>>
      imp_res_tac evaluate_code_const>>
      full_simp_tac(srw_ss())[]>>
      imp_res_tac evaluate_add_clock>>
      rev_full_simp_tac(srw_ss())[]>>pop_assum kall_tac>>
      qexists_tac`clk+clk'`>>ntac 2 strip_tac>>
      pop_assum(qspec_then`clk'` assume_tac)>>full_simp_tac(srw_ss())[ADD_COMM]>>
      `s.clock + (clk+clk') = clk'+(clk+s.clock)` by simp[]>>
      full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      simp[])
    >>
      srw_tac[][]>>full_simp_tac(srw_ss())[]>>
      qexists_tac`clk`>>full_simp_tac(srw_ss())[ADD_COMM])
  >- tac
  >- (tac>>full_simp_tac(srw_ss())[jump_exc_def]>>tac)
  >-
    (Cases_on`ri`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    ntac 5(TOP_CASE_TAC>>full_simp_tac(srw_ss())[]))
  >-
    (fs[domain_lookup,EXISTS_PROD] \\ res_tac \\ fs[]
     \\ fs[state_component_equality] )
  >- (
     ntac 6(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[LET_THM]>>pairarg_tac>>full_simp_tac(srw_ss())[state_component_equality]>>
    rveq>>full_simp_tac(srw_ss())[])
  >>
    simp[markerTheory.Abbrev_def]>>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    simp[evaluate_def,GSYM get_vars_termdep_code_frame]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac `newprog = find_code dest aret l`>>
    `newprog = SOME (q,remove_must_terminate r)` by
      (Cases_on`ret`>>Cases_on`dest`>>
      unabbrev_all_tac>>full_simp_tac(srw_ss())[find_code_def,add_ret_loc_def]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      res_tac>>
      rveq>>full_simp_tac(srw_ss())[]>>
      metis_tac[NOT_NONE_SOME])>>
    simp[]>>
    TOP_CASE_TAC>-
      (TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      TOP_CASE_TAC>>full_simp_tac(srw_ss())[]
      >-
        (strip_tac>>qexists_tac`0`>>full_simp_tac(srw_ss())[call_env_def,state_component_equality])
      >>
      EVERY_CASE_TAC>>srw_tac[][]>>
      first_x_assum(qspecl_then[`SOME x'`,`r'`] assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
      qexists_tac`clk`>>simp[dec_clock_def,call_env_def]>>
      `clk + s.clock -1 = s.clock -1 + clk` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])>>
    ntac 7 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>-
      (srw_tac[][]>>qexists_tac`0`>>full_simp_tac(srw_ss())[call_env_def,state_component_equality])>>
    ntac 3 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
    >-
      (ntac 3 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
      Cases_on`handler`>>TRY(PairCases_on`x'''`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rev_full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      imp_res_tac evaluate_code_const>>
      imp_res_tac pop_env_code_gc_fun_clock>>
      full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      qexists_tac`clk+clk'`>>
      imp_res_tac evaluate_add_clock>>
      full_simp_tac(srw_ss())[]>>
      pop_assum kall_tac>>
      pop_assum (qspec_then`clk'` mp_tac)>>simp[]>>
      full_simp_tac(srw_ss())[pop_env_termdep_code_frame,set_var_def]>>
      full_simp_tac(srw_ss())[ADD_COMM])
    >-
      (Cases_on`handler`>>TRY(PairCases_on`x''`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rev_full_simp_tac(srw_ss())[]
      >-
        (srw_tac[][]>>qexists_tac`clk`>>
        `s.clock -1 + clk = clk + s.clock-1`by DECIDE_TAC>>
        rveq>>full_simp_tac(srw_ss())[])
      >>
        ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
        imp_res_tac evaluate_code_const>>
        imp_res_tac pop_env_code_gc_fun_clock>>
        full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        qexists_tac`clk+clk'`>>
        imp_res_tac evaluate_add_clock>>
        full_simp_tac(srw_ss())[]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum (qspec_then`clk'` mp_tac)>>simp[]>>
        full_simp_tac(srw_ss())[ADD_COMM,set_var_def])
    >>
      Cases_on`handler`>>TRY(PairCases_on`x''`)>>full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rev_full_simp_tac(srw_ss())[]>>strip_tac>>
      qexists_tac`clk`>>
      `s.clock -1 + clk = clk + s.clock-1`by DECIDE_TAC>>
      rveq>>full_simp_tac(srw_ss())[])

(* syntactic preservation all in one go *)
val convs = [flat_exp_conventions_def,full_inst_ok_less_def,every_inst_def,post_alloc_conventions_def,call_arg_convention_def,wordLangTheory.every_stack_var_def,wordLangTheory.every_var_def,extract_labels_def]

val remove_must_terminate_conventions = Q.store_thm("remove_must_terminate_conventions",`
  ∀p c k.
  let comp = remove_must_terminate p in
  (flat_exp_conventions p ⇒ flat_exp_conventions comp) ∧
  (full_inst_ok_less c p ⇒ full_inst_ok_less c comp) ∧
  (post_alloc_conventions k p ⇒ post_alloc_conventions k comp) ∧
  (every_inst two_reg_inst p ⇒ every_inst two_reg_inst comp) ∧
  (extract_labels p = extract_labels comp)`,
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>fs convs>>
  TRY
  (rename1`args = A`>>
  Cases_on`ret`>>fs[]>>
  PairCases_on`x`>>fs[]>>
  Cases_on`h`>>fs[]>- metis_tac[]>>
  PairCases_on`x`>>fs[]>>
  metis_tac[])>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[])

val _ = export_theory();
