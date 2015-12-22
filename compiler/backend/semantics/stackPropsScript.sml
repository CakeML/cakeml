open preamble stackSemTheory

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
   (set_store x y z).mdomain = z.mdomain`,
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
   (set_var x y z).mdomain = z.mdomain`,
  EVAL_TAC);

val set_var_with_const = Q.store_thm("set_var_with_const[simp]",
  `set_var x y (z with clock := k) = set_var x y z with clock := k`,
  EVAL_TAC);

val empty_env_const = Q.store_thm("empty_env_const[simp]",
  `(empty_env x).ffi = x.ffi ∧
   (empty_env x).clock = x.clock ∧
   (empty_env z).use_alloc = z.use_alloc ∧
   (empty_env z).use_store = z.use_store ∧
   (empty_env z).use_stack = z.use_stack ∧
   (empty_env z).code = z.code ∧
   (empty_env z).be = z.be ∧
   (empty_env z).gc_fun = z.gc_fun ∧
   (empty_env z).mdomain = z.mdomain`,
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
    t.mdomain = s.mdomain`,
  rw[alloc_def,gc_def,LET_THM] >>
  every_case_tac >> fs[] >> rw[]);

val gc_with_const = Q.store_thm("gc_with_const[simp]",
  `gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x)`,
   rw[gc_def] >> every_case_tac >> fs[]);

val alloc_with_const = Q.store_thm("alloc_with_const[simp]",
  `alloc x (y with clock := z) = (I ## (λs. s with clock := z))(alloc x y)`,
  rw[alloc_def] >> every_case_tac >> fs[] >> rfs[]);

val mem_load_with_const = Q.store_thm("mem_load_with_const[simp]",
  `mem_load x (y with clock := k) = mem_load x y`,
  EVAL_TAC)

val mem_load_with_const = Q.store_thm("mem_load_with_const[simp]",
  `mem_store x y (z with clock := k) = OPTION_MAP(λs. s with clock := k)(mem_store x y z)`,
  EVAL_TAC >> rw[]);

val word_exp_with_const = Q.store_thm("word_exp_with_const[simp]",
  `∀s y k. word_exp (s with clock := k) y = word_exp s y`,
  ho_match_mp_tac word_exp_ind >> rw[word_exp_def] >>
  every_case_tac >> fs[] >>
  fs[EVERY_MEM,EXISTS_MEM] >>
  unabbrev_all_tac >>
  fs[MEM_MAP,PULL_EXISTS] >>
  res_tac >> fs[IS_SOME_EXISTS] >> fs[] >>
  rpt AP_TERM_TAC >>
  simp[MAP_EQ_f]);

val assign_with_const = Q.store_thm("assign_with_const[simp]",
  `assign x y (s with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y s)`,
  rw[assign_def] >> every_case_tac >> fs[]);

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
    t.mdomain = s.mdomain`,
  Cases_on`i`>>rw[inst_def,assign_def] >>
  every_case_tac >> fs[set_var_def,word_exp_def,LET_THM] >> rw[] >>
  fs[mem_store_def] >> rw[]);

val inst_with_const = Q.store_thm("inst_with_const[simp]",
  `inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s)`,
  rw[inst_def] >>
  CASE_TAC >> fs[] >>
  every_case_tac >> fs[get_var_def] >> rveq >> fs[]);

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).ffi = s.ffi ∧
   (dec_clock z).use_alloc = z.use_alloc ∧
   (dec_clock z).use_store = z.use_store ∧
   (dec_clock z).use_stack = z.use_stack ∧
   (dec_clock z).code = z.code ∧
   (dec_clock z).be = z.be ∧
   (dec_clock z).gc_fun = z.gc_fun ∧
   (dec_clock z).mdomain = z.mdomain`,
  EVAL_TAC);

val evaluate_consts = store_thm("evaluate_consts",
  ``!c s r s1.
      evaluate (c,s) = (r,s1) ==>
      s1.use_alloc = s.use_alloc /\
      s1.use_store = s.use_store /\
      s1.use_stack = s.use_stack /\
      s1.code = s.code /\
      s1.be = s.be /\
      s1.gc_fun = s.gc_fun /\
      s1.mdomain = s.mdomain``,
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt gen_tac >>
  rpt (
    (strip_tac >> CHANGED_TAC(imp_res_tac alloc_const) >> fs[]) ORELSE
    (strip_tac >> CHANGED_TAC(imp_res_tac inst_const) >> fs[]) ORELSE
    (strip_tac >> var_eq_tac >> rveq >> fs[]) ORELSE
    (CASE_TAC >> fs[]) ORELSE
    (split_pair_tac >> simp[])));

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events ∧
    (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  recInduct evaluate_ind >>
  rw [evaluate_def] >>
  every_case_tac >> fs[LET_THM] >>
  TRY split_pair_tac >> fs[] >>
  imp_res_tac alloc_const >> fs[] >>
  imp_res_tac inst_const >> fs[] >>
  fs[set_var_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[] >>
  TRY (CHANGED_TAC(fs[ffiTheory.call_FFI_def]) >>
       every_case_tac >> fs[] >> rw[] ) >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_add_clock = Q.store_thm("evaluate_add_clock",
  `∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)`,
  recInduct evaluate_ind >>
  rw[evaluate_def] >> fs[LET_THM] >>
  TRY (
    qcase_tac`get_var_imm` >> cheat ) >>
  TRY (
    qcase_tac`find_code` >> cheat ) >>
  TRY split_pair_tac >> fs[] >>
  every_case_tac >> fs[] >> rveq >>
  fs[get_var_def] >> rveq >> fs[] >>
  imp_res_tac alloc_const >> fs[] >>
  imp_res_tac inst_const >> fs[] >>
  fsrw_tac[ARITH_ss][dec_clock_def] >>
  TRY (
    qcase_tac`call_FFI` >>
    split_pair_tac >> fs[] >> rveq >> simp[] ) >>
  metis_tac[]);

val clock_neutral_def = Define `
  (clock_neutral (Seq p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral (LocValue _ _ _) <=> T) /\
  (clock_neutral (Halt _) <=> T) /\
  (clock_neutral (Inst _) <=> T) /\
  (clock_neutral (Skip) <=> T) /\
  (clock_neutral (If _ _ _ p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral r <=> F)`

val inst_clock_neutral = prove(
  ``(inst i s = SOME t ==> inst i (s with clock := k) = SOME (t with clock := k)) /\
    (inst i s = NONE ==> inst i (s with clock := k) = NONE)``,
  Cases_on `i` \\ fs [inst_def,assign_def,word_exp_def,set_var_def,LET_DEF]
  \\ rw [state_component_equality]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [word_exp_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [word_exp_def]
  \\ fs [mem_load_def,get_var_def,mem_store_def]
  \\ rw [state_component_equality]);

val evaluate_clock_neutral = store_thm("evaluate_clock_neutral",
  ``!prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,s with clock := c) = (res,t with clock := c)``,
  recInduct evaluate_ind \\ rw [] \\ fs []
  \\ fs [evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ fs [] \\ rw [] \\ fs [])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral \\ fs [])
  THEN1 (Cases_on `evaluate (c1,s)` \\ fs [LET_THM] \\ every_case_tac \\ fs[])
  \\ `get_var_imm ri (s with clock := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ fs [get_var_imm_def,get_var_def])
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]);

val _ = export_theory();
