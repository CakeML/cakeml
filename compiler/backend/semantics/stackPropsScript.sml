open preamble stackSemTheory

val _ = new_theory"stackProps";

val set_store_const = Q.store_thm("set_store_const[simp]",
  `(set_store x y z).ffi = z.ffi ∧
   (set_store x y z).use_alloc = z.use_alloc ∧
   (set_store x y z).use_store = z.use_store ∧
   (set_store x y z).use_stack = z.use_stack ∧
   (set_store x y z).code = z.code ∧
   (set_store x y z).be = z.be ∧
   (set_store x y z).gc_fun = z.gc_fun ∧
   (set_store x y z).mdomain = z.mdomain`,
  EVAL_TAC);

val set_var_const = Q.store_thm("set_var_const[simp]",
  `(set_var x y z).ffi = z.ffi ∧
   (set_var x y z).use_alloc = z.use_alloc ∧
   (set_var x y z).use_store = z.use_store ∧
   (set_var x y z).use_stack = z.use_stack ∧
   (set_var x y z).code = z.code ∧
   (set_var x y z).be = z.be ∧
   (set_var x y z).gc_fun = z.gc_fun ∧
   (set_var x y z).mdomain = z.mdomain`,
  EVAL_TAC);

val empty_env_const = Q.store_thm("empty_env_const[simp]",
  `(empty_env x).ffi = x.ffi ∧
   (empty_env z).use_alloc = z.use_alloc ∧
   (empty_env z).use_store = z.use_store ∧
   (empty_env z).use_stack = z.use_stack ∧
   (empty_env z).code = z.code ∧
   (empty_env z).be = z.be ∧
   (empty_env z).gc_fun = z.gc_fun ∧
   (empty_env z).mdomain = z.mdomain`,
  EVAL_TAC)

val alloc_const = Q.store_thm("alloc_const",
  `alloc w s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain`,
  rw[alloc_def,gc_def,LET_THM] >>
  every_case_tac >> fs[] >> rw[]);

val inst_const = Q.store_thm("inst_const",
  `inst i s = SOME t ⇒
    t.ffi = s.ffi ∧
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
  cheat);

val _ = export_theory();
