open preamble word_removeTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_removeProof";

val compile_state_def = Define`
  compile_state clk c s =
    s with <|
      clock := s.clock+clk;
      termdep := 0;
      code := map (I ## remove_must_terminate) s.code;
      compile_oracle := (I ## (MAP (I ## I ## remove_must_terminate))) o s.compile_oracle;
      compile := c
    |>`;

val compile_state_const = Q.store_thm("compile_state_const[simp]",
  `(compile_state clk c s).locals = s.locals ∧
   (compile_state clk c s).permute = s.permute ∧
   (compile_state clk c s).ffi = s.ffi ∧
   (compile_state clk c s).code_buffer = s.code_buffer ∧
   (compile_state clk c s).data_buffer = s.data_buffer ∧
   (compile_state clk c s).code = map (I ## remove_must_terminate) s.code ∧
   (compile_state clk c s).clock = s.clock + clk ∧
   (compile_state clk c s).termdep = 0 ∧
   (compile_state clk c s).compile_oracle = (I ## (MAP (I ## I ## remove_must_terminate))) o s.compile_oracle ∧
   (compile_state clk c s).compile = c ∧
   (compile_state clk c s).stack = s.stack ∧
   (compile_state clk c s).store = s.store ∧
   (compile_state clk c s).fp_regs = s.fp_regs ∧
   (compile_state clk c s).memory = s.memory ∧
   (compile_state clk c s).mdomain = s.mdomain ∧
   (compile_state clk c s).be = s.be ∧
   (compile_state clk c s).gc_fun = s.gc_fun ∧
   (compile_state clk c s).handler = s.handler`,
  EVAL_TAC);

val find_code_map_I = Q.store_thm("find_code_map_I[simp]",
  `find_code d l (map (I ## f) t) = OPTION_MAP (I ## f) (find_code d l t)`,
  Cases_on`d` \\ rw[find_code_def,lookup_map]
  \\ rpt(TOP_CASE_TAC \\ fs[]));

val compile_state_update = Q.store_thm("compile_state_update[simp]",
  `compile_state clk c s with stack updated_by f1 = compile_state clk c (s with stack updated_by f1) ∧
   compile_state clk c s with permute updated_by f2 = compile_state clk c (s with permute updated_by f2) ∧
   compile_state clk c s with ffi updated_by f10 = compile_state clk c (s with ffi updated_by f10) ∧
   compile_state clk c s with data_buffer updated_by f9 = compile_state clk c (s with data_buffer updated_by f9) ∧
   compile_state clk c s with code_buffer updated_by f8 = compile_state clk c (s with code_buffer updated_by f8) ∧
   compile_state clk c s with memory updated_by f7 = compile_state clk c (s with memory updated_by f7) ∧
   compile_state clk c s with locals updated_by f6 = compile_state clk c (s with locals updated_by f6) ∧
   compile_state clk c s with memory updated_by f5 = compile_state clk c (s with memory updated_by f5) ∧
   compile_state clk c s with store updated_by f4 = compile_state clk c (s with store updated_by f4) ∧
   compile_state clk c s with fp_regs updated_by f11 = compile_state clk c (s with fp_regs updated_by f11) ∧
   compile_state clk c s with handler updated_by f3 = compile_state clk c (s with handler updated_by f3)`,
  EVAL_TAC);

val get_var_compile_state = Q.store_thm("get_var_compile_state[simp]",
  `get_var x (compile_state clk c s) = get_var x s`,
  EVAL_TAC);

val get_fp_var_compile_state = Q.store_thm("get_fp_var_compile_state[simp]",
  `get_fp_var x (compile_state clk c s) = get_fp_var x s`,
  EVAL_TAC);

val get_vars_compile_state = Q.store_thm("get_vars_compile_state[simp]",
  `∀xs s. get_vars xs (compile_state clk c s) = get_vars xs s`,
  Induct \\ rw[get_vars_def]);

val set_var_compile_state = Q.store_thm("set_var_compile_state[simp]",
  `set_var x y (compile_state clk c s) = compile_state clk c (set_var x y s)`,
  rw[set_var_def]);

val set_fp_var_compile_state = Q.store_thm("set_fp_var_compile_state[simp]",
  `set_fp_var x y (compile_state clk c s) = compile_state clk c (set_fp_var x y s)`,
  rw[set_fp_var_def]);

val set_vars_compile_state = Q.store_thm("set_vars_compile_state[simp]",
  `set_vars xs ys (compile_state clk c s) = compile_state clk c (set_vars xs ys s)`,
  EVAL_TAC);

val set_store_compile_state = Q.store_thm("set_store_compile_state[simp]",
  `set_store x y (compile_state clk c s) = compile_state clk c (set_store x y s)`,
  EVAL_TAC);

val push_env_compile_state = Q.store_thm("push_env_compile_state[simp]",
  `push_env env h (compile_state clk c s) = compile_state clk c (push_env env h s)`,
  Cases_on`h` \\ TRY(PairCases_on`x`) \\ rw[push_env_def,UNCURRY]);

val pop_env_compile_state = Q.store_thm("pop_env_compile_state[simp]",
  `pop_env (compile_state clk c s) = OPTION_MAP (compile_state clk c) (pop_env s)`,
  rw[pop_env_def] \\ ntac 4 (CASE_TAC \\ fs[]));

val call_env_compile_state = Q.store_thm("call_env_compile_state[simp]",
  `call_env x (compile_state clk c z) = compile_state clk c (call_env x z)`,
  EVAL_TAC);

val has_space_compile_state = Q.store_thm("has_space_compile_state[simp]",
  `has_space n (compile_state clk c s) = has_space n s`,
  EVAL_TAC);

val gc_compile_state = Q.store_thm("gc_compile_state[simp]",
  `gc (compile_state clk c s) = OPTION_MAP (compile_state clk c) (gc s)`,
  rw[gc_def] \\ ntac 4 (CASE_TAC \\ simp[]));

val alloc_compile_state = Q.store_thm("alloc_compile_state[simp]",
  `alloc w names (compile_state clk c s) = (I ## compile_state clk c) (alloc w names s)`,
  rw[alloc_def] \\ ntac 6 (CASE_TAC \\ fs[]));

val mem_load_compile_state = Q.store_thm("mem_load_compile_state[simp]",
  `mem_load w (compile_state clk c s) = mem_load w s`,
  EVAL_TAC);

val mem_store_compile_state = Q.store_thm("mem_store_compile_state[simp]",
  `mem_store x y (compile_state clk c s) = OPTION_MAP (compile_state clk c) (mem_store x y s)`,
  rw[mem_store_def]);

val word_exp_compile_state = Q.store_thm("word_exp_compile_state[simp]",
  `∀s y.  word_exp (compile_state clk c s) y = word_exp s y`,
  recInduct word_exp_ind
  \\ rw[word_exp_def]
  \\ fsrw_tac[ETA_ss][]
  \\ `MAP (word_exp (compile_state clk c s)) wexps = MAP (word_exp s) wexps`
  by fs[MAP_EQ_f] \\ fs[]);

val assign_compile_state = Q.store_thm("assign_compile_state[simp]",
  `assign x y (compile_state clk c s) = OPTION_MAP (compile_state clk c) (assign x y s)`,
  rw[assign_def] \\ CASE_TAC \\ fs[]);

val inst_compile_state = Q.store_thm("inst_compile_state[simp]",
  `inst i (compile_state clk c s) = OPTION_MAP (compile_state clk c) (inst i s)`,
  rw[inst_def] \\ rpt(TOP_CASE_TAC \\ fs[]) \\ fs[]);

val compile_state_dec_clock = Q.store_thm("compile_state_dec_clock[simp]",
  `s.clock ≠ 0 ⇒ (compile_state clk c (dec_clock s) = dec_clock (compile_state clk c s))`,
  EVAL_TAC \\ rw[state_component_equality]);

val jump_exc_compile_state = Q.store_thm("jump_exc_compile_state[simp]",
  `jump_exc (compile_state clk c s) = OPTION_MAP (compile_state clk c ## I) (jump_exc s)`,
  rw[jump_exc_def] \\ ntac 5 (CASE_TAC \\ fs[]));

val get_var_imm_compile_state = Q.store_thm("get_var_imm_compile_state[simp]",
  `get_var_imm x (compile_state clk c s) = get_var_imm x s`,
  Cases_on`x` \\ rw[get_var_imm_def]);

val push_env_case_handler = Q.store_thm("push_env_case_handler[simp]",
  `push_env x (case handler of NONE => NONE | SOME (v,prog,l1,l2) => SOME (v, f prog, l1,l2)) = push_env x handler`,
  CASE_TAC \\ rw[push_env_def]
  \\ split_pair_case_tac \\ rw[push_env_def,FUN_EQ_THM]);

val word_remove_correct = Q.store_thm("word_remove_correct",
  `∀prog st res rst.
    evaluate (prog,st) = (res,rst) ∧
    st.compile = (λcfg. c cfg o (MAP (I ## I ## remove_must_terminate))) ∧
    res ≠ SOME Error ⇒
    ∃clk.
      evaluate (remove_must_terminate prog, compile_state clk c st) =
        (res, compile_state 0 c rst)`,
  recInduct evaluate_ind
  \\ rw[evaluate_def,remove_must_terminate_def]
  \\ TRY ( (* Seq *)
    qmatch_goalsub_rename_tac`remove_must_terminate _` \\
    pairarg_tac \\ fs[] \\
    reverse(fs[case_eq_thms] \\ rveq \\ fs[])
    >- ( qexists_tac`clk` \\ fs[] \\ NO_TAC ) \\
    qpat_x_assum`(res,rst) = _`(assume_tac o SYM) \\ fs[] \\
    `s1.compile = s.compile` by (imp_res_tac evaluate_consts \\ fs[]) \\ fs[] \\
    qexists_tac`clk + clk'` \\ fs[] \\
    imp_res_tac (GEN_ALL evaluate_add_clock) \\ fs[] \\
    first_x_assum(qspec_then`clk'`mp_tac) \\ fs[] \\
    fs[compile_state_def] \\ NO_TAC )
  \\ TRY ( (* MustTerminate *)
    qmatch_goalsub_rename_tac`remove_must_terminate _` \\
    pairarg_tac \\ fs[] \\
    fs[case_eq_thms] \\ rveq \\ fs[] \\
    qpat_x_assum`evaluate(p,_) = _`kall_tac \\
    drule evaluate_dec_clock \\ fs[] \\ strip_tac \\
    drule (GEN_ALL evaluate_add_clock) \\ fs[] \\
    disch_then(qspec_then`s.clock`mp_tac) \\
    strip_tac \\
    fs[compile_state_def] \\
    qexists_tac`clk + MustTerminate_limit (:'a) - s1.clock` \\
    fs[] \\ NO_TAC)
  \\ TRY ( (* Install *)
    fs[case_eq_thms] \\ rveq \\
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\
    fs[case_eq_thms] \\ rveq \\ fs[] \\
    fs[shift_seq_def] \\
    qexists_tac`0` \\
    simp[compile_state_def,state_component_equality,FUN_EQ_THM,map_union,map_fromAList] \\
    rpt(AP_TERM_TAC ORELSE AP_THM_TAC) \\ simp[FUN_EQ_THM,FORALL_PROD] \\ NO_TAC)
  \\ TRY ( (* Call *)
    qmatch_goalsub_rename_tac`find_code` \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    qpat_x_assum`_ = (res,rst)`mp_tac \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[]
    >- (
      fs[case_eq_thms] \\
      strip_tac \\ fs[] \\ rveq
      >- metis_tac[]
      \\ rfs[]
      \\ fs[compile_state_def,dec_clock_def,call_env_def]
      \\ qexists_tac`clk` \\ fs[] )
    \\ split_pair_case_tac \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[] \\
      qexists_tac`0` \\ fs[] \\
      fs[add_ret_loc_def] ) \\
    fs[add_ret_loc_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    rfs[] \\
    TOP_CASE_TAC \\ fs[] \\ rveq \\
    simp[Once case_eq_thms]
    >- (
      simp[Once case_eq_thms]
      \\ strip_tac \\ fs[]
      \\ rveq \\ fs[]
      \\ pop_assum mp_tac
      \\ IF_CASES_TAC \\ fs[]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ imp_res_tac pop_env_const
      \\ imp_res_tac evaluate_consts \\ fs[] \\ rfs[]
      \\ qexists_tac`clk + clk'`
      \\ imp_res_tac evaluate_add_clock \\ fs[]
      \\ pop_assum kall_tac
      \\ first_x_assum(qspec_then`clk'`mp_tac)
      \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sa`
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sb`
      \\ `sa = sb` by (
        unabbrev_all_tac
        \\ simp[dec_clock_def]
        \\ simp[state_component_equality] )
      \\ rw[]
      \\ fs[compile_state_def] )
    >- (
      strip_tac \\ fs[] \\ rveq \\ fs[]
      >- (
        fs[dec_clock_def]
        \\ qexists_tac`clk` \\ fs[]
        \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sa`
        \\ qmatch_asmsub_abbrev_tac`remove_must_terminate _,sb`
        \\ `sa = sb` by ( unabbrev_all_tac \\ simp[state_component_equality] )
        \\ rw[] )
      \\ split_pair_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ pop_assum mp_tac \\ simp[Once case_eq_thms]
      \\ simp[Once case_eq_thms]
      \\ strip_tac \\ rveq \\ fs[]
      \\ pop_assum(assume_tac o SYM) \\ fs[]
      \\ imp_res_tac evaluate_consts \\ fs[] \\ rfs[]
      \\ qexists_tac`clk + clk'`
      \\ imp_res_tac evaluate_add_clock \\ fs[]
      \\ pop_assum kall_tac
      \\ first_x_assum(qspec_then`clk'`mp_tac)
      \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sa`
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sb`
      \\ `sa = sb` by (
        unabbrev_all_tac
        \\ simp[dec_clock_def]
        \\ simp[state_component_equality] )
      \\ rw[]
      \\ fs[compile_state_def] )
    \\ strip_tac \\ rveq \\ fs[]
    \\ fs[dec_clock_def]
    \\ qexists_tac`clk` \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`remove_must_terminate _,sa`
    \\ qmatch_asmsub_abbrev_tac`remove_must_terminate _,sb`
    \\ `sa = sb` by ( unabbrev_all_tac \\ simp[state_component_equality] )
    \\ rw[] \\ NO_TAC )
  \\ fs[case_eq_thms] \\ rveq
  \\ fs[domain_map]
  \\ rpt(pairarg_tac \\ fs[])
  \\ metis_tac[]);

(*
=======
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
    rpt(TOP_CASE_TAC>>
    full_simp_tac(srw_ss())[set_var_def,state_component_equality,mem_load_def,get_var_def,mem_store_def,get_fp_var_def,set_fp_var_def]))
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
     rpt(TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
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
>>>>>>> origin/master
*)

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
