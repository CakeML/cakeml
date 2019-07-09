(*
  Correctness proof for word_remove
*)
open preamble word_removeTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_removeProof";

val _ = set_grammar_ancestry["word_remove","wordSem","wordProps"];

val compile_state_def = Define`
  compile_state clk c s =
    s with <|
      clock := s.clock+clk;
      termdep := 0;
      code := map (I ## remove_must_terminate) s.code;
      compile_oracle := (I ## (MAP (I ## I ## remove_must_terminate))) o s.compile_oracle;
      compile := c
    |>`;

Theorem compile_state_const[simp]:
   (compile_state clk c s).locals = s.locals ∧
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
   (compile_state clk c s).handler = s.handler
Proof
  EVAL_TAC
QED

Theorem find_code_map_I[simp]:
   find_code d l (map (I ## f) t) = OPTION_MAP (I ## f) (find_code d l t)
Proof
  Cases_on`d` \\ rw[find_code_def,lookup_map]
  \\ rpt(TOP_CASE_TAC \\ fs[])
QED

Theorem compile_state_update[simp]:
   compile_state clk c s with stack updated_by f1 = compile_state clk c (s with stack updated_by f1) ∧
   compile_state clk c s with permute updated_by f2 = compile_state clk c (s with permute updated_by f2) ∧
   compile_state clk c s with ffi updated_by f10 = compile_state clk c (s with ffi updated_by f10) ∧
   compile_state clk c s with data_buffer updated_by f9 = compile_state clk c (s with data_buffer updated_by f9) ∧
   compile_state clk c s with code_buffer updated_by f8 = compile_state clk c (s with code_buffer updated_by f8) ∧
   compile_state clk c s with memory updated_by f7 = compile_state clk c (s with memory updated_by f7) ∧
   compile_state clk c s with locals updated_by f6 = compile_state clk c (s with locals updated_by f6) ∧
   compile_state clk c s with memory updated_by f5 = compile_state clk c (s with memory updated_by f5) ∧
   compile_state clk c s with store updated_by f4 = compile_state clk c (s with store updated_by f4) ∧
   compile_state clk c s with fp_regs updated_by f11 = compile_state clk c (s with fp_regs updated_by f11) ∧
   compile_state clk c s with handler updated_by f3 = compile_state clk c (s with handler updated_by f3)
Proof
  EVAL_TAC
QED

Theorem get_var_compile_state[simp]:
   get_var x (compile_state clk c s) = get_var x s
Proof
  EVAL_TAC
QED

Theorem get_fp_var_compile_state[simp]:
   get_fp_var x (compile_state clk c s) = get_fp_var x s
Proof
  EVAL_TAC
QED

Theorem get_vars_compile_state[simp]:
   ∀xs s. get_vars xs (compile_state clk c s) = get_vars xs s
Proof
  Induct \\ rw[get_vars_def]
QED

Theorem set_var_compile_state[simp]:
   set_var x y (compile_state clk c s) = compile_state clk c (set_var x y s)
Proof
  rw[set_var_def]
QED

Theorem set_fp_var_compile_state[simp]:
   set_fp_var x y (compile_state clk c s) = compile_state clk c (set_fp_var x y s)
Proof
  rw[set_fp_var_def]
QED

Theorem set_vars_compile_state[simp]:
   set_vars xs ys (compile_state clk c s) = compile_state clk c (set_vars xs ys s)
Proof
  EVAL_TAC
QED

Theorem set_store_compile_state[simp]:
   set_store x y (compile_state clk c s) = compile_state clk c (set_store x y s)
Proof
  EVAL_TAC
QED

Theorem push_env_compile_state[simp]:
   push_env env h (compile_state clk c s) = compile_state clk c (push_env env h s)
Proof
  Cases_on`h` \\ TRY(PairCases_on`x`) \\ rw[push_env_def,UNCURRY]
QED

Theorem pop_env_compile_state[simp]:
   pop_env (compile_state clk c s) = OPTION_MAP (compile_state clk c) (pop_env s)
Proof
  rw[pop_env_def] \\ ntac 4 (CASE_TAC \\ fs[])
QED

Theorem call_env_compile_state[simp]:
   call_env x (compile_state clk c z) = compile_state clk c (call_env x z)
Proof
  EVAL_TAC
QED

Theorem has_space_compile_state[simp]:
   has_space n (compile_state clk c s) = has_space n s
Proof
  EVAL_TAC
QED

Theorem gc_compile_state[simp]:
   gc (compile_state clk c s) = OPTION_MAP (compile_state clk c) (gc s)
Proof
  rw[gc_def] \\ ntac 4 (CASE_TAC \\ simp[])
QED

Theorem alloc_compile_state[simp]:
   alloc w names (compile_state clk c s) = (I ## compile_state clk c) (alloc w names s)
Proof
  rw[alloc_def] \\ ntac 6 (CASE_TAC \\ fs[])
QED

Theorem mem_load_compile_state[simp]:
   mem_load w (compile_state clk c s) = mem_load w s
Proof
  EVAL_TAC
QED

Theorem mem_store_compile_state[simp]:
   mem_store x y (compile_state clk c s) = OPTION_MAP (compile_state clk c) (mem_store x y s)
Proof
  rw[mem_store_def]
QED

Theorem word_exp_compile_state[simp]:
   ∀s y.  word_exp (compile_state clk c s) y = word_exp s y
Proof
  recInduct word_exp_ind
  \\ rw[word_exp_def]
  \\ fsrw_tac[ETA_ss][]
  \\ `MAP (word_exp (compile_state clk c s)) wexps = MAP (word_exp s) wexps`
  by fs[MAP_EQ_f] \\ fs[]
QED

Theorem assign_compile_state[simp]:
   assign x y (compile_state clk c s) = OPTION_MAP (compile_state clk c) (assign x y s)
Proof
  rw[assign_def] \\ CASE_TAC \\ fs[]
QED

Theorem inst_compile_state[simp]:
   inst i (compile_state clk c s) = OPTION_MAP (compile_state clk c) (inst i s)
Proof
  rw[inst_def] \\ rpt(TOP_CASE_TAC \\ fs[]) \\ fs[]
QED

Theorem compile_state_dec_clock[simp]:
   s.clock ≠ 0 ⇒ (compile_state clk c (dec_clock s) = dec_clock (compile_state clk c s))
Proof
  EVAL_TAC \\ rw[state_component_equality]
QED

Theorem jump_exc_compile_state[simp]:
   jump_exc (compile_state clk c s) = OPTION_MAP (compile_state clk c ## I) (jump_exc s)
Proof
  rw[jump_exc_def] \\ ntac 5 (CASE_TAC \\ fs[])
QED

Theorem get_var_imm_compile_state[simp]:
   get_var_imm x (compile_state clk c s) = get_var_imm x s
Proof
  Cases_on`x` \\ rw[get_var_imm_def]
QED

Theorem push_env_case_handler[simp]:
   push_env x (case handler of NONE => NONE | SOME (v,prog,l1,l2) => SOME (v, f prog, l1,l2)) = push_env x handler
Proof
  CASE_TAC \\ rw[push_env_def]
  \\ split_pair_case_tac \\ rw[push_env_def,FUN_EQ_THM]
QED

Theorem word_remove_correct:
   ∀prog st res rst.
    evaluate (prog,st) = (res,rst) ∧
    st.compile = (λcfg. c cfg o (MAP (I ## I ## remove_must_terminate))) ∧
    res ≠ SOME Error ⇒
    ∃clk.
      evaluate (remove_must_terminate prog, compile_state clk c st) =
        (res, compile_state 0 c rst)
Proof
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
  \\ metis_tac[]
QED

(* syntactic preservation all in one go *)
val convs = [flat_exp_conventions_def, full_inst_ok_less_def,
  every_inst_def, post_alloc_conventions_def, call_arg_convention_def,
  wordLangTheory.every_stack_var_def, wordLangTheory.every_var_def,
  extract_labels_def]

Theorem remove_must_terminate_conventions:
    ∀p c k.
  let comp = remove_must_terminate p in
  (flat_exp_conventions p ⇒ flat_exp_conventions comp) ∧
  (full_inst_ok_less c p ⇒ full_inst_ok_less c comp) ∧
  (post_alloc_conventions k p ⇒ post_alloc_conventions k comp) ∧
  (every_inst two_reg_inst p ⇒ every_inst two_reg_inst comp) ∧
  (extract_labels p = extract_labels comp)
Proof
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
  metis_tac[]
QED

val _ = export_theory();
