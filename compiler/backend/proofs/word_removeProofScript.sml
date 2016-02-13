open preamble BasicProvers word_removeTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_removeProof";

val alloc_termdep_code_frame = prove(``
  alloc c names (s with <|termdep:=d;code:=l|>) =
  (FST (alloc c names s),SND(alloc c names s) with <|termdep:=d;code:=l|>)``,
  fs[alloc_def]>>TOP_CASE_TAC>>
  fs[push_env_def,env_to_list_def,LET_THM,gc_def,set_store_def]>>
  ntac 3(FULL_CASE_TAC>>fs[])
  >-
    (EVERY_CASE_TAC>>fs[])>>
  FULL_CASE_TAC>>fs[pop_env_def]>>
  ntac 3(FULL_CASE_TAC>>fs[call_env_def])>>
  FULL_CASE_TAC>>fs[has_space_def]>>
  EVERY_CASE_TAC>>fs[])|>INST_TYPE[beta|->alpha,gamma|->beta,delta|->alpha]

val get_vars_termdep_code_frame = prove(``
  ∀ls.
  get_vars ls s = get_vars ls (s with <|termdep:=0;code:=l|>)``,
  Induct>>fs[get_vars_def,get_var_def])

val word_exp_termdep_code_frame = prove(``
  ∀s exp.
  word_exp s exp = word_exp (s with <|termdep:=0;code:=l|>) exp``,
  ho_match_mp_tac word_exp_ind>>
  fs[word_exp_def,LET_THM,mem_load_def]>>
  fs[EVERY_MAP,EVERY_MEM]>>rw[]>>
  AP_TERM_TAC>>AP_TERM_TAC>>
  fs[MAP_EQ_f])

val tac = (fs[GSYM word_exp_termdep_code_frame]>>EVERY_CASE_TAC>>fs[state_component_equality,set_store_def,mem_store_def])

val push_env_code = prove(``
  (push_env x handler s).code = s.code``,
  Cases_on`handler`>>TRY(PairCases_on`x'`)>>fs[push_env_def,LET_THM,env_to_list_def])

val pop_env_termdep_code_frame = prove(``
  pop_env (r' with <|termdep:=0; code:=l|>) =
  lift (λs. s with <|termdep:=0;code:=l|>) (pop_env r')``,
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[])

val word_remove_correct = store_thm("word_remove_correct",``
  ∀prog st res rst.
  (!n v p. lookup n st.code = SOME (v,p) ==>
         lookup n l = SOME (v,remove_must_terminate p)) ∧
  evaluate(prog,st) = (res,rst) ∧
  res ≠ SOME Error ⇒
  ∃clk.
  evaluate(remove_must_terminate prog,st with <|clock:=st.clock+clk;termdep:=0;code:=l|>) = (res,rst with <|termdep:=0;code:=l|>)``,
  recInduct evaluate_ind>>
  fs[evaluate_def,remove_must_terminate_def,state_component_equality,call_env_def,get_var_def,set_var_def,dec_clock_def]>>rw[]
  >-
    (EVERY_CASE_TAC>>fs[]>>
    imp_res_tac alloc_const>>
    simp[alloc_termdep_code_frame,state_component_equality])
  >-
    (simp[GSYM get_vars_termdep_code_frame]>>
    EVERY_CASE_TAC>>
    fs[set_vars_def,state_component_equality]>>rfs[])
  >-
    (Cases_on`i`>>fs[inst_def,state_component_equality,assign_def,GSYM word_exp_termdep_code_frame,get_var_def]>>
    rpt(TOP_CASE_TAC>>fs[set_var_def,state_component_equality,mem_load_def,get_var_def,mem_store_def]))
  >- tac
  >- tac
  >- tac
  >- (tac>>FULL_CASE_TAC>>fs[state_component_equality])
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (*hard*)
    (qpat_assum`A=(res,rst)`mp_tac>>simp[]>>
    split_pair_tac>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    strip_tac>>fs[]>>
    rveq>>
    res_tac>>
    imp_res_tac evaluate_dec_clock>>fs[]>>
    imp_res_tac evaluate_add_clock>>fs[]>>
    pop_assum kall_tac>>
    first_x_assum(qspec_then`s.clock` assume_tac)>>
    metis_tac[])
  >-
    (qpat_assum`A=(res,rst)`mp_tac>>simp[]>>
    split_pair_tac>>fs[]>>
    IF_CASES_TAC>>fs[]>-
      (strip_tac>>fs[]>>
      imp_res_tac evaluate_code_const>>
      fs[]>>
      imp_res_tac evaluate_add_clock>>
      rfs[]>>pop_assum kall_tac>>
      qexists_tac`clk+clk'`>>ntac 2 strip_tac>>
      pop_assum(qspec_then`clk'` assume_tac)>>fs[ADD_COMM]>>
      `s.clock + (clk+clk') = clk'+(clk+s.clock)` by simp[]>>
      fs[]>>rw[]>>
      simp[])
    >>
      rw[]>>fs[]>>
      qexists_tac`clk`>>fs[ADD_COMM])
  >- tac
  >- (tac>>fs[jump_exc_def]>>tac)
  >-
    (Cases_on`ri`>>fs[get_var_imm_def,get_var_def]>>
    ntac 5(TOP_CASE_TAC>>fs[]))
  >-
    (ntac 6(TOP_CASE_TAC>>fs[])>>
    fs[LET_THM]>>split_pair_tac>>fs[state_component_equality]>>
    rveq>>fs[])
  >>
    simp[markerTheory.Abbrev_def]>>
    qpat_assum`A=(res,rst)` mp_tac>>
    simp[evaluate_def,GSYM get_vars_termdep_code_frame]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    qpat_abbrev_tac `newprog = find_code dest aret l`>>
    `newprog = SOME (q,remove_must_terminate r)` by
      (Cases_on`ret`>>Cases_on`dest`>>
      unabbrev_all_tac>>fs[find_code_def,add_ret_loc_def]>>
      EVERY_CASE_TAC>>fs[add_ret_loc_def]>>
      res_tac>>
      rveq>>fs[]>>
      metis_tac[NOT_NONE_SOME])>>
    simp[]>>
    TOP_CASE_TAC>-
      (TOP_CASE_TAC>>fs[]>>
      TOP_CASE_TAC>>fs[]
      >-
        (strip_tac>>qexists_tac`0`>>fs[call_env_def,state_component_equality])
      >>
      EVERY_CASE_TAC>>rw[]>>
      first_x_assum(qspecl_then[`SOME x'`,`r'`] assume_tac)>>rfs[]>>
      qexists_tac`clk`>>simp[dec_clock_def,call_env_def]>>
      `clk + s.clock -1 = s.clock -1 + clk` by DECIDE_TAC>>
      fs[])>>
    ntac 7 (TOP_CASE_TAC>>fs[])>-
      (rw[]>>qexists_tac`0`>>fs[call_env_def,state_component_equality])>>
    ntac 3 (TOP_CASE_TAC>>fs[])
    >-
      (ntac 3 (TOP_CASE_TAC>>fs[])>>
      Cases_on`handler`>>TRY(PairCases_on`x'''`)>>fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rfs[]>>rw[]>>
      imp_res_tac evaluate_code_const>>
      imp_res_tac pop_env_code_clock>>
      fs[]>>rfs[]>>
      qexists_tac`clk+clk'`>>
      imp_res_tac evaluate_add_clock>>
      fs[]>>
      pop_assum kall_tac>>
      pop_assum (qspec_then`clk'` mp_tac)>>simp[]>>
      fs[pop_env_termdep_code_frame,set_var_def]>>
      fs[ADD_COMM])
    >-
      (Cases_on`handler`>>TRY(PairCases_on`x''`)>>fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rfs[]
      >-
        (rw[]>>qexists_tac`clk`>>
        `s.clock -1 + clk = clk + s.clock-1`by DECIDE_TAC>>
        rveq>>fs[])
      >>
        ntac 2 (TOP_CASE_TAC>>fs[])>>rw[]>>
        imp_res_tac evaluate_code_const>>
        imp_res_tac pop_env_code_clock>>
        fs[]>>rfs[]>>
        qexists_tac`clk+clk'`>>
        imp_res_tac evaluate_add_clock>>
        fs[]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum (qspec_then`clk'` mp_tac)>>simp[]>>
        fs[ADD_COMM,set_var_def])
    >>
      Cases_on`handler`>>TRY(PairCases_on`x''`)>>fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def,call_env_def]>>rfs[]>>strip_tac>>
      qexists_tac`clk`>>
      `s.clock -1 + clk = clk + s.clock-1`by DECIDE_TAC>>
      rveq>>fs[])

val _ = export_theory();
