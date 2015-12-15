open preamble stackSemTheory

val _ = new_theory"stackProps";

val set_store_const = Q.store_thm("set_store_const[simp]",
  `(set_store x y z).ffi = z.ffi`,
  EVAL_TAC);

val empty_env_const = Q.store_thm("empty_env_const[simp]",
  `(empty_env x).ffi = x.ffi`,
  EVAL_TAC)

val alloc_ffi = Q.store_thm("alloc_ffi",
  `alloc w s = (r,t) ⇒ t.ffi = s.ffi`,
  rw[alloc_def,gc_def,LET_THM] >>
  every_case_tac >> fs[] >> rw[]);

val inst_ffi = Q.store_thm("inst_ffi",
  `inst i s = SOME t ⇒ t.ffi = s.ffi`,
  Cases_on`i`>>rw[inst_def,assign_def] >>
  every_case_tac >> fs[set_var_def,word_exp_def,LET_THM] >> rw[] >>
  fs[mem_store_def] >> rw[]);

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).ffi = s.ffi`,
  EVAL_TAC);

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
  imp_res_tac alloc_ffi >> fs[] >>
  imp_res_tac inst_ffi >> fs[] >>
  fs[set_var_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[] >>
  TRY (CHANGED_TAC(fs[ffiTheory.call_FFI_def]) >>
       every_case_tac >> fs[] >> rw[] ) >>
  metis_tac[IS_PREFIX_TRANS]);

val _ = export_theory();
