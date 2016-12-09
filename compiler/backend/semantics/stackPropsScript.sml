open preamble stackSemTheory stack_namesTheory

val _ = new_theory"stackProps";

val set_store_const = Q.store_thm("set_store_const[simp]",
  `(set_store x y z).ffi = z.ffi ∧
   (set_store x y z).clock = z.clock ∧
   (set_store x y z).use_alloc = z.use_alloc ∧
   (set_store x y z).use_store = z.use_store ∧
   (set_store x y z).use_stack = z.use_stack ∧
   (set_store x y z).code = z.code ∧
   (set_store x y z).be = z.be ∧
   (set_store x y z).gc_fun = z.gc_fun ∧
   (set_store x y z).mdomain = z.mdomain ∧
   (set_store x y z).bitmaps = z.bitmaps`,
  EVAL_TAC);

val set_store_with_const = Q.store_thm("set_store_with_const[simp]",
  `set_store x y (z with clock := a) = set_store x y z with clock := a`,
  EVAL_TAC);

val set_var_const = Q.store_thm("set_var_const[simp]",
  `(set_var x y z).ffi = z.ffi ∧
   (set_var x y z).clock = z.clock ∧
   (set_var x y z).use_alloc = z.use_alloc ∧
   (set_var x y z).use_store = z.use_store ∧
   (set_var x y z).use_stack = z.use_stack ∧
   (set_var x y z).code = z.code ∧
   (set_var x y z).be = z.be ∧
   (set_var x y z).gc_fun = z.gc_fun ∧
   (set_var x y z).mdomain = z.mdomain ∧
   (set_var x y z).bitmaps = z.bitmaps ∧
   (set_var x y z).stack = z.stack ∧
   (set_var x y z).stack_space = z.stack_space`,
  EVAL_TAC);

val set_var_with_const = Q.store_thm("set_var_with_const[simp]",
  `set_var x y (z with clock := k) = set_var x y z with clock := k ∧
   set_var x y (z with stack_space := k) = set_var x y z with stack_space := k`,
  EVAL_TAC);

val get_var_imm_with_const = Q.store_thm("get_var_imm_with_const[simp]",
  `get_var_imm x (y with clock := k) = get_var_imm x y`,
  Cases_on`x`>>EVAL_TAC);

val empty_env_const = Q.store_thm("empty_env_const[simp]",
  `(empty_env x).ffi = x.ffi ∧
   (empty_env x).clock = x.clock ∧
   (empty_env z).use_alloc = z.use_alloc ∧
   (empty_env z).use_store = z.use_store ∧
   (empty_env z).use_stack = z.use_stack ∧
   (empty_env z).code = z.code ∧
   (empty_env z).be = z.be ∧
   (empty_env z).gc_fun = z.gc_fun ∧
   (empty_env z).mdomain = z.mdomain ∧
   (empty_env z).bitmaps = z.bitmaps`,
  EVAL_TAC)

val empty_env_with_const = Q.store_thm("empty_env_with_const[simp]",
  `empty_env (x with clock := y) = empty_env x with clock := y`,
  EVAL_TAC);

val alloc_const = Q.store_thm("alloc_const",
  `alloc w s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.bitmaps = s.bitmaps`,
  srw_tac[][alloc_def,gc_def,LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val gc_with_const = Q.store_thm("gc_with_const[simp]",
  `gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x)`,
   srw_tac[][gc_def] >> every_case_tac >> full_simp_tac(srw_ss())[]);

val alloc_with_const = Q.store_thm("alloc_with_const[simp]",
  `alloc x (y with clock := z) = (I ## (λs. s with clock := z))(alloc x y)`,
  srw_tac[][alloc_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);

val mem_load_with_const = Q.store_thm("mem_load_with_const[simp]",
  `mem_load x (y with clock := k) = mem_load x y`,
  EVAL_TAC)

val mem_load_with_const = Q.store_thm("mem_load_with_const[simp]",
  `mem_store x y (z with clock := k) = OPTION_MAP(λs. s with clock := k)(mem_store x y z)`,
  EVAL_TAC >> srw_tac[][]);

val word_exp_with_const = Q.store_thm("word_exp_with_const[simp]",
  `∀s y k. word_exp (s with clock := k) y = word_exp s y`,
  ho_match_mp_tac word_exp_ind >> srw_tac[][word_exp_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[EVERY_MEM,EXISTS_MEM] >>
  unabbrev_all_tac >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS] >>
  res_tac >> full_simp_tac(srw_ss())[IS_SOME_EXISTS] >> full_simp_tac(srw_ss())[] >>
  rpt AP_TERM_TAC >>
  simp[MAP_EQ_f]);

val assign_with_const = Q.store_thm("assign_with_const[simp]",
  `assign x y (s with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y s)`,
  srw_tac[][assign_def] >> every_case_tac >> full_simp_tac(srw_ss())[]);

val inst_const = Q.store_thm("inst_const",
  `inst i s = SOME t ⇒
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.bitmaps = s.bitmaps`,
  Cases_on`i`>>srw_tac[][inst_def,assign_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[set_var_def,word_exp_def,LET_THM] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[mem_store_def] >> srw_tac[][] >>
  fs[get_vars_def]>>every_case_tac>>fs[state_component_equality]);

val inst_with_const = Q.store_thm("inst_with_const[simp]",
  `inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s)`,
  srw_tac[][inst_def] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[get_var_def] >> rveq >> full_simp_tac(srw_ss())[]>>
  fs[get_vars_def,get_var_def]>>every_case_tac>>fs[]);

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).ffi = s.ffi ∧
   (dec_clock z).use_alloc = z.use_alloc ∧
   (dec_clock z).use_store = z.use_store ∧
   (dec_clock z).use_stack = z.use_stack ∧
   (dec_clock z).code = z.code ∧
   (dec_clock z).be = z.be ∧
   (dec_clock z).gc_fun = z.gc_fun ∧
   (dec_clock z).mdomain = z.mdomain ∧
   (dec_clock z).bitmaps = z.bitmaps`,
  EVAL_TAC);

val evaluate_consts = Q.store_thm("evaluate_consts",
  `!c s r s1.
      evaluate (c,s) = (r,s1) ==>
      s1.use_alloc = s.use_alloc /\
      s1.use_store = s.use_store /\
      s1.use_stack = s.use_stack /\
      s1.code = s.code /\
      s1.be = s.be /\
      s1.gc_fun = s.gc_fun /\
      s1.mdomain = s.mdomain /\
      s1.bitmaps = s.bitmaps`,
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt gen_tac >>
  rpt (
    (strip_tac >> CHANGED_TAC(imp_res_tac alloc_const) >> full_simp_tac(srw_ss())[]) ORELSE
    (strip_tac >> CHANGED_TAC(imp_res_tac inst_const) >> full_simp_tac(srw_ss())[]) ORELSE
    (strip_tac >> var_eq_tac >> rveq >> full_simp_tac(srw_ss())[]) ORELSE
    (CASE_TAC >> full_simp_tac(srw_ss())[]) ORELSE
    (pairarg_tac >> simp[])));

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events ∧
    (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac alloc_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac inst_const >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[set_var_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY (CHANGED_TAC(full_simp_tac(srw_ss())[ffiTheory.call_FFI_def]) >>
       every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_add_clock = Q.store_thm("evaluate_add_clock",
  `∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM] >>
  TRY (
    rename1`find_code dest (_ \\ _)` >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
      BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
    ntac 3 BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    reverse BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >- (
      BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
      BasicProvers.FULL_CASE_TAC >> full_simp_tac(srw_ss())[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
    qpat_x_assum`_ = (_,_)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> strip_tac >> rveq >>
    fsrw_tac[ARITH_ss][] >> rveq >>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
    NO_TAC) >>
  TRY (
    rename1`find_code` >>
    full_simp_tac(srw_ss())[get_var_def] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rveq >> fsrw_tac[ARITH_ss][dec_clock_def] >>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
  TRY (
    rename1`While`
    \\ BasicProvers.TOP_CASE_TAC \\ fs[get_var_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ pairarg_tac \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ pairarg_tac \\ fs[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[] \\ rfs[]
    \\ fsrw_tac[ARITH_ss][dec_clock_def] ) >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >>
  TRY BasicProvers.TOP_CASE_TAC \\ fs[get_var_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >>
  full_simp_tac(srw_ss())[get_var_def] >> rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac alloc_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac inst_const >> full_simp_tac(srw_ss())[] >>
  fsrw_tac[ARITH_ss][dec_clock_def] >>
  TRY (
    rename1`call_FFI` >>
    pairarg_tac >> full_simp_tac(srw_ss())[] >> rveq >> simp[] ) >>
  metis_tac[]);

val with_clock_ffi = Q.store_thm("with_clock_ffi",
  `(s with clock := k).ffi = s.ffi`,
  EVAL_TAC);

val evaluate_add_clock_io_events_mono = Q.store_thm("evaluate_add_clock_io_events_mono",
  `∀e s.
     (SND(evaluate(e,s))).ffi.io_events ≼ (SND(evaluate(e,s with clock := s.clock + extra))).ffi.io_events ∧
     (IS_SOME((SND(evaluate(e,s))).ffi.final_event) ⇒
      (SND(evaluate(e,s with clock := s.clock + extra))).ffi =
      (SND(evaluate(e,s))).ffi)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM,get_var_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY (
    rename1`While`
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fsrw_tac[ARITH_ss][dec_clock_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ imp_res_tac evaluate_io_events_mono \\ fs[]
    \\ imp_res_tac evaluate_add_clock \\ fs[]
    \\ qmatch_assum_rename_tac`evaluate (c1,s) = (res1,_)`
    \\ Cases_on`res1=NONE` \\fs[]
    \\ rpt(first_x_assum(qspec_then`extra`mp_tac))\\ simp[]
    \\ TRY (
      strip_tac \\ CHANGED_TAC rveq \\ fs[]
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ metis_tac[evaluate_io_events_mono,PAIR,with_clock_ffi] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ metis_tac[IS_PREFIX_TRANS,evaluate_io_events_mono,PAIR,with_clock_ffi] ) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[dec_clock_def] >>
  rveq >> fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])>> full_simp_tac(srw_ss())[] >>
  TRY(
    CHANGED_TAC(simp[ffiTheory.call_FFI_def,get_var_def]) >>
    every_case_tac >> full_simp_tac(srw_ss())[get_var_def] >>
    rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[]) >>
  metis_tac[IS_PREFIX_TRANS,evaluate_io_events_mono,PAIR]);

val clock_neutral_def = Define `
  (clock_neutral (Seq p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral (LocValue _ _ _) <=> T) /\
  (clock_neutral (Halt _) <=> T) /\
  (clock_neutral (Inst _) <=> T) /\
  (clock_neutral (Skip) <=> T) /\
  (clock_neutral (If _ _ _ p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral r <=> F)`

val inst_clock_neutral = Q.prove(
  `(inst i s = SOME t ==> inst i (s with clock := k) = SOME (t with clock := k)) /\
    (inst i s = NONE ==> inst i (s with clock := k) = NONE)`,
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF]
  \\ srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def]
  \\ srw_tac[][state_component_equality]);

val inst_clock_neutral_ffi = Q.prove(
  `(inst i s = SOME t ==> inst i (s with ffi := k) = SOME (t with ffi := k)) /\
    (inst i s = NONE ==> inst i (s with ffi := k) = NONE)`,
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,state_component_equality]>>
  reverse full_case_tac>>fs[]>>
  TRY
    (qmatch_goalsub_abbrev_tac`get_vars _ _`>>
    fs[get_vars_def,get_var_def]>>
    rpt (BasicProvers.TOP_CASE_TAC>>fs[state_component_equality]))
  \\ rpt (srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def]
  \\ srw_tac[][state_component_equality]));

val evaluate_clock_neutral = Q.store_thm("evaluate_clock_neutral",
  `!prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,s with clock := c) = (res,t with clock := c)`,
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with clock := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]);

val evaluate_ffi_neutral = Q.store_thm("evaluate_ffi_neutral",
  `!prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,s with ffi := c) = (res,t with ffi := c)`,
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[empty_env_def])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral_ffi \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with ffi := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]);

val semantics_Terminate_IMP_PREFIX = Q.store_thm("semantics_Terminate_IMP_PREFIX",
  `semantics start s1 = Terminate x l ==> isPREFIX s1.ffi.io_events l`,
  full_simp_tac(srw_ss())[semantics_def,LET_DEF] \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac evaluate_io_events_mono \\ full_simp_tac(srw_ss())[]);

val semantics_Diverge_IMP_LPREFIX = Q.store_thm("semantics_Diverge_IMP_LPREFIX",
  `semantics start s1 = Diverge l ==> LPREFIX (fromList s1.ffi.io_events) l`,
  simp[semantics_def] >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> srw_tac[][] >>
  qmatch_abbrev_tac`LPREFIX l1 (build_lprefix_lub l2)` >>
  `l1 ∈ l2 ∧ lprefix_chain l2` suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_def] >>
  conj_tac >- (
    unabbrev_all_tac >> simp[] >>
    qexists_tac`0`>>full_simp_tac(srw_ss())[evaluate_def] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  simp[Abbr`l2`] >>
  simp[Once(GSYM o_DEF),IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  simp[prefix_chain_def,PULL_EXISTS] >>
  qx_genl_tac[`k1`,`k2`] >>
  qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
  simp[LESS_EQ_EXISTS] >>
  metis_tac[evaluate_add_clock_io_events_mono,
            EVAL``(s with clock := k).clock``,
            EVAL``((s with clock := k) with clock := k2) = (s with clock := k2)``]);

val map_bitmap_length = Q.store_thm("map_bitmap_length",`
  ∀a b c x y z.
  map_bitmap a b c = SOME(x,y,z) ⇒
  LENGTH c = LENGTH x + LENGTH z ∧
  LENGTH x = LENGTH a`,
  Induct>>rw[]>>
  Cases_on`b`>>TRY(Cases_on`h`)>>Cases_on`c`>>
  fs[map_bitmap_def]>>
  TRY(qpat_x_assum`A=x` (SUBST_ALL_TAC o SYM))>>
  TRY(qpat_x_assum`A=y` (SUBST_ALL_TAC o SYM))>>
  fs[LENGTH_NIL]>>
  pop_assum mp_tac>>every_case_tac>>rw[]>>res_tac>>
  fs[]>>DECIDE_TAC);

val dec_stack_length = Q.store_thm("dec_stack_length",`
  ∀bs enc orig_stack new_stack.
  dec_stack bs enc orig_stack = SOME new_stack ⇒
  LENGTH orig_stack = LENGTH new_stack`,
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  fs[stackSemTheory.dec_stack_def,LENGTH_NIL]>>rw[]>>
  pop_assum mp_tac>>
  Cases_on`w`>>fs[full_read_bitmap_def]>>
  every_case_tac>>fs[]>>
  rw[]>>
  imp_res_tac map_bitmap_length>>
  simp[]>>metis_tac[])

val extract_labels_def = Define`
  (extract_labels (Call ret dest h) =
    (case ret of
      NONE => []
    | SOME (ret_handler,_,l1,l2) =>
      let ret_rest = extract_labels ret_handler in
    (case h of
      NONE => [(l1,l2)] ++ ret_rest
    | SOME (prog,l1',l2') =>
      let h_rest = extract_labels prog in
      [(l1,l2);(l1',l2')]++ret_rest++h_rest))) ∧
  (extract_labels (While _ _ _ s1) = extract_labels s1) ∧
  (extract_labels (Seq s1 s2) =
    extract_labels s1 ++ extract_labels s2) ∧
  (extract_labels (If cmp r1 ri e2 e3) =
    (extract_labels e2 ++ extract_labels e3)) ∧
  (extract_labels _ = [])`

val find_code_IMP_get_labels = Q.store_thm("find_code_IMP_get_labels",
  `find_code d r code = SOME e ==>
    get_labels e SUBSET loc_check code`,
  Cases_on `d`
  \\ fs [stackSemTheory.find_code_def,SUBSET_DEF,IN_DEF,
         loc_check_def,FORALL_PROD]
  \\ every_case_tac \\ fs []
  \\ metis_tac []);

(* asm_ok out of stack_names *)
val stack_asm_ok_def = Define`
  (stack_asm_ok c ((Inst i):'a stackLang$prog) ⇔ asm$inst_ok i c) ∧
  (stack_asm_ok c (Seq p1 p2) ⇔ stack_asm_ok c p1 ∧ stack_asm_ok c p2) ∧
  (stack_asm_ok c (If cmp n r p p') ⇔ stack_asm_ok c p ∧ stack_asm_ok c p') ∧
  (stack_asm_ok c (While cmp n r p) ⇔ stack_asm_ok c p) ∧
  (stack_asm_ok c (Raise n) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Return n _) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Call r tar h) ⇔
    (case tar of INR r => r < c.reg_count ∧ ¬MEM r c.avoid_regs | _ => T) ∧
    case r of
      (SOME (p,_,_,_) => stack_asm_ok c p ∧
      case h of
      SOME (p',_,_) => stack_asm_ok c p'
      | _ => T)
    | _ => T) ∧
  (stack_asm_ok c _ ⇔  T)`

val reg_name_def = Define`
  reg_name r c ⇔
  r < c.reg_count - LENGTH (c.avoid_regs)`

(* inst requirements just before stack_names *)

val reg_imm_name_def = Define`
  (reg_imm_name b (Reg r) c ⇔ reg_name r c) ∧
  (reg_imm_name b (Imm w) c ⇔ c.valid_imm b w)`

val arith_name_def = Define`
  (arith_name (Binop b r1 r2 ri) (c:'a asm_config) ⇔
    (c.two_reg_arith ⇒ r1 = r2 ∨ b = Or ∧ ri = Reg r2) ∧ reg_name r1 c ∧
    reg_name r2 c ∧ reg_imm_name (INL b) ri c) ∧
  (arith_name (Shift l r1 r2 n) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    (n = 0 ⇒ l = Lsl) ∧ n < dimindex (:α)) ∧
  (arith_name (Div r1 r2 r3) c ⇔
    (reg_name r1 c ∧ reg_name r2 c ∧ reg_name r3 c ∧
    c.ISA ∈ {ARMv8; MIPS; RISC_V})) ∧
  (arith_name (LongMul r1 r2 r3 r4) c ⇔
    reg_name r1 c ∧ reg_name r2 c ∧ reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = x86_64 ⇒ r1 = 4 ∧ r2 = 0 ∧ r3 = 0) ∧
    (c.ISA = ARMv6 ⇒ r1 ≠ r2) ∧
    (c.ISA = ARMv8 ∨ c.ISA = RISC_V ⇒ r1 ≠ r3 ∧ r1 ≠ r4)) ∧
  (arith_name (LongDiv r1 r2 r3 r4 r5) c ⇔
    c.ISA = x86_64 ∧ r1 = 0 ∧ r2 = 4 ∧ r3 = 0 ∧ r4 = 4 ∧
    reg_name r5 c) ∧
  (arith_name (AddCarry r1 r2 r3 r4) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = MIPS ∨ c.ISA = RISC_V ⇒ r1 ≠ r3 ∧ r1 ≠ r4))`

val addr_name_def = Define`
  addr_name (Addr r w) c ⇔ reg_name r c ∧ addr_offset_ok w c`

val inst_name_def = Define`
  (inst_name c (Const r w) ⇔ reg_name r c) ∧
  (inst_name c (Mem m r a) ⇔ reg_name r c ∧ addr_name a c) ∧
  (inst_name c (Arith x) ⇔ arith_name x c) ∧
  (inst_name _ _ = T)`

val stack_asm_name_def = Define`
  (stack_asm_name c ((Inst i):'a stackLang$prog) ⇔ inst_name c i) ∧
  (stack_asm_name c (Seq p1 p2) ⇔ stack_asm_name c p1 ∧ stack_asm_name c p2) ∧
  (stack_asm_name c (If cmp n r p p') ⇔ stack_asm_name c p ∧ stack_asm_name c p') ∧
  (stack_asm_name c (While cmp n r p) ⇔ stack_asm_name c p) ∧
  (stack_asm_name c (Raise n) ⇔ reg_name n c) ∧
  (stack_asm_name c (Return n _) ⇔ reg_name n c) ∧
  (stack_asm_name c (Call r tar h) ⇔
    (case tar of INR r => reg_name r c | _ => T) ∧
    case r of
      (SOME (p,_,_,_) => stack_asm_name c p ∧
      case h of
      SOME (p',_,_) => stack_asm_name c p'
      | _ => T)
    | _ => T) ∧
  (stack_asm_name c _ ⇔  T)`

val fixed_names_def = Define`
  fixed_names names c =
  if c.ISA = x86_64 then
    find_name names 4 = 2 ∧
    find_name names 0 = 0
  else T`

val stack_asm_remove_def = Define`
  (stack_asm_remove c ((Get n s):'a stackLang$prog) ⇔ reg_name n c) ∧
  (stack_asm_remove c (Set s n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackStore n n0) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackStoreAny n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (StackLoad n n0) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackLoadAny n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (StackGetSize n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackSetSize n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (BitmapLoad n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (Seq p1 p2) ⇔ stack_asm_remove c p1 ∧ stack_asm_remove c p2) ∧
  (stack_asm_remove c (If cmp n r p p') ⇔ stack_asm_remove c p ∧ stack_asm_remove c p') ∧
  (stack_asm_remove c (While cmp n r p) ⇔ stack_asm_remove c p) ∧
  (stack_asm_remove c (Call r tar h) ⇔
    (case r of
      (SOME (p,_,_,_) => stack_asm_remove c p ∧
      case h of
      SOME (p',_,_) => stack_asm_remove c p'
      | _ => T)
    | _ => T)) ∧
  (stack_asm_remove c _ ⇔  T)`

val _ = export_theory();
