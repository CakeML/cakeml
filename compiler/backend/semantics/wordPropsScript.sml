open preamble BasicProvers
     wordLangTheory wordSemTheory

(*
Main lemmas:
0) Clock lemmas
1) Swapping stack for one with identical values (but different keys)
2) Swapping the permutation
3) Effect of extra locals
4) Some properties of every_var etc.
*)

val _ = new_theory "wordProps";

(* evaluate clock monotonicity *)

val set_store_const = Q.store_thm("set_store_const[simp]",
  `(set_store x y z).clock = z.clock ∧
   (set_store x y z).ffi = z.ffi`,
  EVAL_TAC);

val set_store_with_const = Q.store_thm("set_store_with_const[simp]",
  `(set_store x y (z with clock := k)) = set_store x y z with clock := k`,
  EVAL_TAC)

val push_env_const = Q.store_thm("push_env_const[simp]",
  `(push_env x y z).clock = z.clock ∧
   (push_env x y z).ffi = z.ffi`,
  Cases_on`y`>>simp[push_env_def,UNCURRY] >>
  qcase_tac`SOME p` >>
  PairCases_on`p` >>
  rw[push_env_def] >> rw[]);

val push_env_with_const = Q.store_thm("push_env_with_const[simp]",
  `(push_env x y (z with clock := k) = push_env x y z with clock := k) ∧
   (push_env x y (z with locals := l) = push_env x y z with locals := l)`,
  Cases_on`y`>>rw[push_env_def] >- simp[state_component_equality] >>
  qcase_tac`SOME p` >>
  PairCases_on`p` >>
  rw[push_env_def] >> simp[state_component_equality]);

val pop_env_const = Q.store_thm("pop_env_const",
  `pop_env x = SOME y ⇒
   y.clock = x.clock /\
   y.ffi = x.ffi`,
   rw[pop_env_def] >>
   every_case_tac >> fs[] >> rw[]);

val pop_env_with_const = Q.store_thm("pop_env_with_const[simp]",
  `pop_env (z with clock := k) = OPTION_MAP (λs. s with clock := k) (pop_env z) ∧
   pop_env (z with locals := l) = pop_env z`,
  rw[pop_env_def] >> every_case_tac >> fs[]);

val call_env_const = Q.store_thm("call_env_const[simp]",
  `(call_env x y).clock = y.clock ∧
   (call_env x y).ffi = y.ffi`,
  EVAL_TAC)

val call_env_with_const = Q.store_thm("call_env_with_const[simp]",
  `call_env x (y with clock := k) = call_env x y with clock := k`,
  EVAL_TAC)

val has_space_with_const = Q.store_thm("has_space_with_const[simp]",
  `has_space x (y with clock := k) = has_space x y`,
  EVAL_TAC)

val gc_const = Q.store_thm("gc_const",
  `gc x = SOME y ⇒
   y.clock = x.clock ∧
   y.ffi = x.ffi`,
  simp[gc_def] >>
  every_case_tac >> fs[] >> rw[] >> rw[]);

val gc_with_const = Q.store_thm("gc_with_const[simp]",
  `gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x) ∧
   gc (x with locals := l) = OPTION_MAP (λs. s with locals := l) (gc x)`,
  EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC);

val alloc_const = Q.store_thm("alloc_const",
  `alloc c names s = (r,s') ⇒
   s'.clock = s.clock ∧
   s'.ffi = s.ffi`,
  rw[alloc_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac pop_env_const >> fs[] >>
  imp_res_tac gc_const >> fs[]);

val alloc_with_const = Q.store_thm("alloc_with_const[simp]",
  `alloc c names (s with clock := k) =
   (λ(r,s). (r,s with clock := k)) (alloc c names s)`,
  rw[alloc_def] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[] >> rw[] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[]);

val get_var_with_const = Q.store_thm("get_var_with_const[simp]",
  `get_var x (y with clock := k) = get_var x y`,
  EVAL_TAC)

val get_vars_with_const = Q.store_thm("get_vars_with_const[simp]",
  `get_vars x (y with clock := k) = get_vars x y`,
  Induct_on`x`>>rw[get_vars_def]);

val set_var_const = Q.store_thm("set_var_const[simp]",
  `(set_var x y z).clock = z.clock ∧
   (set_var x y z).ffi = z.ffi ∧
   (set_var x y z).stack = z.stack`,
  EVAL_TAC)

val set_var_with_const = Q.store_thm("set_var_with_const[simp]",
  `set_var x y (z with clock := k) = set_var x y z with clock := k`,
  EVAL_TAC);

val set_vars_const = Q.store_thm("set_vars_const[simp]",
  `(set_vars x y z).clock = z.clock ∧
   (set_vars x y z).ffi = z.ffi`,
  EVAL_TAC);

val set_vars_with_const = Q.store_thm("set_vars_with_const[simp]",
  `set_vars x y (z with clock := k) = set_vars x y z with clock := k`,
  EVAL_TAC);

val mem_load_with_const = Q.store_thm("mem_load_with_const[simp]",
  `mem_load x (y with clock := k) = mem_load x y`,
  EVAL_TAC);

val mem_store_const = Q.store_thm("mem_store_const",
  `mem_store x y z = SOME a ⇒
   a.clock = z.clock ∧
   a.ffi = z.ffi`,
  EVAL_TAC >> rw[] >> rw[]);

val mem_store_with_const = Q.store_thm("mem_store_with_const[simp]",
  `mem_store x z (y with clock := k) = OPTION_MAP (λs. s with clock := k) (mem_store x z y)`,
  EVAL_TAC >> every_case_tac >> simp[]);

val word_exp_with_const = Q.store_thm("word_exp_with_const[simp]",
  `∀x y k. word_exp (x with clock := k) y = word_exp x y`,
  recInduct word_exp_ind >>
  rw[word_exp_def] >>
  every_case_tac >> fs[] >>
  unabbrev_all_tac >>
  fs[EVERY_MEM,EXISTS_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS,MAP_MAP_o,o_DEF] >>
  res_tac >> rfs[] >>
  AP_TERM_TAC >> simp[MAP_EQ_f]);

val assign_const = Q.store_thm("assign_const",
  `assign x y z = SOME a ⇒
   a.clock = z.clock ∧
   a.ffi = z.ffi`,
  EVAL_TAC >> every_case_tac >> fs[] >> rw[] >> rw[]);

val assign_with_const = Q.store_thm("assign_with_const[simp]",
  `assign x y (z with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y z)`,
  EVAL_TAC >> every_case_tac >> EVAL_TAC >> fs[]);

val inst_with_const = Q.store_thm("inst_with_const[simp]",
  `inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s)`,
  rw[inst_def] >> every_case_tac >> fs[]);

val inst_const = Q.store_thm("inst_const",
  `inst i s = SOME s' ⇒
   s'.clock = s.clock ∧
   s'.ffi = s.ffi`,
  rw[inst_def] >>
  every_case_tac >>fs[] >>
  imp_res_tac assign_const >> fs[] >> rw[] >>
  imp_res_tac mem_store_const >> fs[] >> rw[]);

val jump_exc_const = Q.store_thm("jump_exc_const",
  `jump_exc s = SOME (x,y) ⇒
   x.clock = s.clock ∧
   x.ffi = s.ffi`,
  EVAL_TAC >> every_case_tac >> EVAL_TAC >> rw[] >> rw[]);

val jump_exc_with_const = Q.store_thm("jump_exc_with_const[simp]",
  `jump_exc (s with clock := k) = OPTION_MAP (λ(s,t). (s with clock := k, t)) (jump_exc s)`,
  EVAL_TAC >> every_case_tac >> EVAL_TAC);

val get_var_imm_with_const = Q.store_thm("get_var_imm_with_const[simp]",
  `get_var_imm x (y with clock := k) = get_var_imm x y`,
  Cases_on`x`>>EVAL_TAC);

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).ffi = s.ffi`,
  EVAL_TAC)

val evaluate_add_clock = Q.store_thm("evaluate_add_clock",
  `∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)`,
  recInduct evaluate_ind >>
  rw[evaluate_def] >>
  TRY CASE_TAC >> fs[] >> rveq >> fs[] >> rveq >>
  TRY CASE_TAC >> fs[] >>
  TRY CASE_TAC >> fs[] >> rveq >> fs[] >> rveq >>
  TRY (
    qcase_tac`find_code _ (add_ret_loc _ _)` >>
    Cases_on`get_vars args s`>>fs[]>>
    Cases_on`find_code dest (add_ret_loc (SOME x) x') s.code`>>fs[]>>
    PairCases_on`x''`>>PairCases_on`x`>>fs[]>>
    Cases_on`cut_env x1 s.locals`>>fs[]>>
    qpat_assum`A=(r,s')` mp_tac>>
    rpt(IF_CASES_TAC>>fs[])>>
    full_case_tac>>fs[]>>Cases_on`q`>>TRY(Cases_on `x''`)>>
    fsrw_tac[ARITH_ss][dec_clock_def]>>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>
    every_case_tac >> fs[] >> rveq >> fs[] >>
    rfs[] >> fs[] >>
    imp_res_tac pop_env_const >> fs[] >>
    rfs[] >> rveq >> fs[] >> rw[] >>
    fs[])>>
  TRY (
    qcase_tac`find_code _ (add_ret_loc _ _)` >>
    Cases_on`get_vars args s`>>fs[]>>
    Cases_on`find_code dest (add_ret_loc ret x') s.code`>>fs[]>>
    Cases_on`ret`>>fs[]>>
    PairCases_on`x''`>>fs[]>>
    PairCases_on`x'''`>>fs[]>>
    Cases_on`cut_env x'''1 s.locals`>>fs[]>>
    qpat_assum`A=(r,s')` mp_tac>>
    rpt(IF_CASES_TAC>>fs[])>>
    Cases_on`evaluate (x''1,call_env x''0 (push_env x'' (SOME x) (dec_clock s)))`>>Cases_on`q`>>TRY(Cases_on`x'''`)>>
    fsrw_tac[ARITH_ss][dec_clock_def]>>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>rw[]>>
    every_case_tac >> fs[] >> rveq >> fs[] >>
    rfs[] >> fs[] >>
    imp_res_tac pop_env_const >> fs[] >>
    rfs[] >> rveq >> fs[] >> rw[] >>
    fs[])>>
  fs[LET_THM,dec_clock_def] >>
  TRY split_pair_tac >> fs[] >> rveq >> fs[] >>
  imp_res_tac alloc_const >> fs[] >>
  imp_res_tac inst_const >> fs[] >>
  imp_res_tac mem_store_const >> fs[] >>
  simp[state_component_equality,dec_clock_def] >>
  fs[ffiTheory.call_FFI_def,LET_THM] >>
  every_case_tac >> fs[] >> rveq >> fs[] >> rveq >>
  simp[state_component_equality,dec_clock_def] >>
  imp_res_tac jump_exc_const >> fs[] >>
  rfs[] >>fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>rveq>>fs[]>>
  metis_tac[]);

(*This allows one to "count" the number of ticks made by a program*)
val tac = EVERY_CASE_TAC>>fs[state_component_equality]
val tac2 =
  strip_tac>>rveq>>fs[]>>
  imp_res_tac evaluate_clock>>fs[]>>
  `¬ (s.clock ≤ r'.clock)` by DECIDE_TAC>>fs[]>>
  `s.clock -1 -r'.clock = s.clock - r'.clock-1` by DECIDE_TAC>>fs[]

val evaluate_dec_clock = Q.store_thm("evaluate_dec_clock",
  `∀prog st res rst.
  evaluate(prog,st) = (res,rst) ⇒
  evaluate(prog,st with clock:=st.clock-rst.clock) = (res,rst with clock:=0)`,
  recInduct evaluate_ind >>rw[evaluate_def]>>fs[call_env_def,dec_clock_def]
  >- (tac>>imp_res_tac alloc_const>>fs[])
  >- tac
  >- (TOP_CASE_TAC>>fs[]>> assume_tac inst_const>>tac)
  >- tac
  >- tac
  >- tac
  >- (tac>>imp_res_tac mem_store_const>>fs[])
  >- DECIDE_TAC
  >- `F`by DECIDE_TAC
  >- (fs[state_component_equality]>>DECIDE_TAC)
  >- (rw[]>>fs[state_component_equality,LET_THM])
  >-
    (qpat_assum`A=(res,rst)` mp_tac>>simp[]>>split_pair_tac>>fs[]>>
    IF_CASES_TAC>>fs[]
    >-
      (strip_tac>>fs[]>>
      imp_res_tac evaluate_clock>>fs[]>>
      imp_res_tac evaluate_add_clock>>fs[]>>
      first_x_assum(qspec_then`s1'.clock - rst.clock` mp_tac)>>simp[])
    >>
      strip_tac>>fs[])
  >- tac
  >- (tac>>imp_res_tac jump_exc_const>>fs[])
  >- tac
  >- (tac>>fs[cut_env_def,LET_THM]>>split_pair_tac>>fs[state_component_equality]>>rveq>>fs[])
  >>
    qpat_assum`A=(res,rst)` mp_tac>>
    ntac 5 (TOP_CASE_TAC>>fs[])
    >-
      (ntac 3 (TOP_CASE_TAC>>fs[state_component_equality])>>
      TOP_CASE_TAC>>fs[]>>
      tac2>>
      first_x_assum(qspec_then`r'` assume_tac)>>rfs[])
    >>
      ntac 7 (TOP_CASE_TAC>>fs[])>-
        (strip_tac>>rveq>>fs[])>>
      ntac 2 (TOP_CASE_TAC>>fs[])>-
        tac2>>
      TOP_CASE_TAC
      >-
        (TOP_CASE_TAC>-tac2>>
        TOP_CASE_TAC>-tac2>>
        reverse TOP_CASE_TAC>-
          (tac2>>imp_res_tac pop_env_const>>
          rveq>>fs[])>>
        strip_tac>>fs[]>>
        rfs[]>>
        imp_res_tac evaluate_clock>>fs[]>>
        imp_res_tac evaluate_add_clock>>fs[]>>
        imp_res_tac pop_env_const>>rveq>>fs[]>>
        first_x_assum(qspec_then`r'.clock-rst.clock` kall_tac)>>
        first_x_assum(qspec_then`r'.clock-rst.clock` mp_tac)>>
        simp[])
      >-
        (TOP_CASE_TAC>-tac2>>
        ntac 3 (TOP_CASE_TAC>>fs[])>>
        TOP_CASE_TAC>-tac2>>
        reverse TOP_CASE_TAC>- tac2>>
        strip_tac>>fs[]>>
        rfs[]>>
        imp_res_tac evaluate_clock>>fs[]>>
        imp_res_tac evaluate_add_clock>>fs[]>>
        imp_res_tac pop_env_const>>rveq>>fs[]>>
        first_x_assum(qspec_then`r'.clock-rst.clock` kall_tac)>>
        first_x_assum(qspec_then`r'.clock-rst.clock` mp_tac)>>
        simp[])
      >>
        tac2)

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events ∧
    (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  recInduct evaluate_ind >> ntac 5 strip_tac >>
  rpt conj_tac >>
  rpt gen_tac >>
  fs [evaluate_def] >>
  rpt gen_tac >>
  rpt (pop_assum mp_tac) >>
  rpt (TOP_CASE_TAC >> fs []) >>
  rpt (disch_then strip_assume_tac ORELSE gen_tac) >> fs [] >>
  rveq >> fs[] >>
  imp_res_tac alloc_const >> fs[] >>
  imp_res_tac inst_const >> fs[] >>
  imp_res_tac mem_store_const >> fs[] >>
  imp_res_tac jump_exc_const >> fs[] >>
  imp_res_tac pop_env_const >> fs[] >>
  fs [LET_THM] >>
  TRY (split_pair_tac >> fs[] >> every_case_tac >> fs []) >>
  rveq >> fs[] >>
  TRY (CHANGED_TAC(fs[ffiTheory.call_FFI_def]) >>
       every_case_tac >> fs[] >> rw[] ) >>
  metis_tac[IS_PREFIX_TRANS]);

val with_clock_ffi = Q.store_thm("with_clock_ffi",
  `(s with clock := y).ffi = s.ffi`,
  EVAL_TAC)

val evaluate_add_clock_io_events_mono = Q.store_thm("evaluate_add_clock_io_events_mono",
  `∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events ∧
    (IS_SOME((SND(evaluate(exps,s))).ffi.final_event) ⇒
     (SND(evaluate(exps,s with clock := s.clock + extra))).ffi =
     (SND(evaluate(exps,s))).ffi)`,
  recInduct evaluate_ind >>
  rw[evaluate_def,LET_THM] >>
  TRY (
    qcase_tac`find_code` >>
    Cases_on`get_vars args s`>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on`ret`>>fs[] >- (
      every_case_tac >> fs[] >> rveq >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      imp_res_tac evaluate_add_clock >> fs[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])) >>
    (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
    qpat_abbrev_tac`opt = find_code _ _ _` >>
    Cases_on`opt`>>fs[markerTheory.Abbrev_def]>>
    (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
    Cases_on`cut_env names' s.locals`>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >> rveq >>
    IF_CASES_TAC >> fs[] >>
    TRY IF_CASES_TAC >> fs[] >>
    CASE_TAC >> fs[] >> rveq >>
    imp_res_tac evaluate_add_clock >> fs[] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >> rfs[] >>
    TRY(
      (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
      qmatch_assum_rename_tac`z ≠ SOME TimeOut ⇒ _` >>
      Cases_on`z=SOME TimeOut`>>fs[]>-(
        every_case_tac >> fs[] >>
        rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        imp_res_tac pop_env_const >> rveq >> fs[] >>
        metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >>
      every_case_tac >> fs[] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      imp_res_tac pop_env_const >> rveq >> fs[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    every_case_tac >> fs[] >> rfs[] >> rveq >> fs[] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >>
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    imp_res_tac pop_env_const >> rveq >> fs[] >> rfs[] >>
    metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
  TRY (
    qcase_tac`find_code` >>
    Cases_on`get_vars args s`>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on`ret`>>fs[] >- (
      every_case_tac >> fs[] >> rveq >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      imp_res_tac evaluate_add_clock >> fs[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])) >>
    (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
    qpat_abbrev_tac`opt = find_code _ _ _` >>
    Cases_on`opt`>>fs[markerTheory.Abbrev_def]>>
    (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
    Cases_on`cut_env names' s.locals`>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >>
    CASE_TAC >> fs[] >> rveq >>
    IF_CASES_TAC >> fs[] >>
    TRY IF_CASES_TAC >> fs[] >>
    TRY (
      (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
      (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
      imp_res_tac evaluate_add_clock >> fs[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      qpat_assum`z ≠ SOME TimeOut ⇒ _`mp_tac >>
      qmatch_assum_rename_tac`z ≠ SOME TimeOut ⇒ _` >>
      Cases_on`z=SOME TimeOut`>>fs[]>-(
        strip_tac >>
        every_case_tac >> fs[] >> rfs[] >>
        rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >> fs[] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        imp_res_tac pop_env_const >> rveq >> fs[] >> rfs[] >>
        metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >> fs[] >>
      every_case_tac >> fs[] >> rfs[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >> fs[] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      imp_res_tac pop_env_const >> rveq >> fs[] >> rfs[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    TRY(
      (fn g => subterm split_pair_case_tac (#2 g) g) >> fs[] >>
      imp_res_tac evaluate_add_clock >> fs[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >>
      every_case_tac >> fs[] >> rfs[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >> fs[] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      imp_res_tac pop_env_const >> rveq >> fs[] >> rfs[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    every_case_tac >> fs[] >> rfs[] >> rveq >> fs[] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> rw[] >>
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    imp_res_tac pop_env_const >> rveq >> fs[] >> rfs[] >>
    metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
  every_case_tac >> fs[] >>
  rpt (split_pair_tac >> fs[]) >>
  every_case_tac >> fs[] >>
  imp_res_tac evaluate_add_clock >> fs[] >>
  rveq >> fs[] >>
  imp_res_tac evaluate_io_events_mono >> rfs[] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]);

(* -- *)

val get_vars_length_lemma = store_thm("get_vars_length_lemma",
  ``!ls s y. get_vars ls s = SOME y ==>
           LENGTH y = LENGTH ls``,
  Induct>>fs[get_vars_def]>>
  Cases_on`get_var h s`>>fs[]>>
  Cases_on`get_vars ls s`>>fs[]>>
  metis_tac[LENGTH])

(*--Stack Swap Lemma--*)

(*Stacks look the same except for the keys (e.g. recoloured and in order)*)
val s_frame_val_eq_def = Define`
  (s_frame_val_eq (StackFrame ls NONE) (StackFrame ls' NONE)
     <=> MAP SND ls = MAP SND ls') /\
  (s_frame_val_eq (StackFrame ls (SOME y)) (StackFrame ls' (SOME y'))
     <=> MAP SND ls = MAP SND ls' /\ y=y') /\
  (s_frame_val_eq _ _ = F)`

val s_val_eq_def = Define`
  (s_val_eq [] [] = T) /\
  (s_val_eq (x::xs) (y::ys) = (s_val_eq xs ys /\
                                    s_frame_val_eq x y)) /\
  (s_val_eq _ _ = F)`

(*Stacks look the same except for the values (e.g. result of gc)*)
val s_frame_key_eq_def = Define`
  (s_frame_key_eq (StackFrame ls NONE) (StackFrame ls' NONE)
     <=> MAP FST ls = MAP FST ls') /\
  (s_frame_key_eq (StackFrame ls (SOME y)) (StackFrame ls' (SOME y'))
     <=> MAP FST ls = MAP FST ls' /\ y=y') /\
  (s_frame_key_eq _ _ = F)`

val s_key_eq_def = Define`
  (s_key_eq [] [] = T) /\
  (s_key_eq (x::xs) (y::ys) = (s_key_eq xs ys /\
                                    s_frame_key_eq x y)) /\
  (s_key_eq _ _ = F)`

(*Reflexive*)
val s_key_eq_refl = store_thm( "s_key_eq_refl",
  ``!ls .s_key_eq ls ls = T``,
   Induct >> rw[s_key_eq_def]>>
   Cases_on`h`>> Cases_on`o'`>>rw[s_frame_key_eq_def])

val s_val_eq_refl = store_thm( "s_val_eq_refl",
  ``!ls.s_val_eq ls ls = T``,
  Induct >> rw[s_val_eq_def]>>
  Cases_on`h`>> Cases_on`o'`>>rw[s_frame_val_eq_def])

(*transitive*)
val s_frame_key_eq_trans = prove(
  ``!a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
            s_frame_key_eq a c``,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  fs[s_frame_key_eq_def])

val s_key_eq_trans = store_thm("s_key_eq_trans",
  ``!a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c``,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>fs[s_key_eq_def]>>
  rw[]>>metis_tac[s_frame_key_eq_trans])

val s_frame_val_eq_trans = prove(
  ``!a b c. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
            s_frame_val_eq a c``,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  fs[s_frame_val_eq_def])

val s_val_eq_trans = prove(
  ``!a b c. s_val_eq a b /\ s_val_eq b c ==>
            s_val_eq a c``,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>fs[s_val_eq_def]>>
  rw[]>>metis_tac[s_frame_val_eq_trans])

(*Symmetric*)
val s_frame_key_eq_sym = prove(
  ``!a b. s_frame_key_eq a b <=> s_frame_key_eq b a``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>fs[s_frame_key_eq_def,EQ_SYM_EQ])

val s_key_eq_sym = store_thm("s_key_eq_sym",
  ``!a b. s_key_eq a b <=> s_key_eq b a``,
  Induct>> Cases_on`b`>>fs[s_key_eq_def]>>
  strip_tac>>metis_tac[s_frame_key_eq_sym])

val s_frame_val_eq_sym = prove(
   ``!a b. s_frame_val_eq a b <=> s_frame_val_eq b a``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>fs[s_frame_val_eq_def,EQ_SYM_EQ])

val s_val_eq_sym = store_thm("s_val_eq_sym",
  ``!a b. s_val_eq a b <=> s_val_eq b a``,
  Induct>> Cases_on`b`>>fs[s_val_eq_def]>>
  strip_tac>>metis_tac[s_frame_val_eq_sym])

val s_frame_val_and_key_eq = prove(
  ``!s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>
  fs[s_frame_val_eq_def,s_frame_key_eq_def,LIST_EQ_MAP_PAIR])

val s_val_and_key_eq = store_thm("s_val_and_key_eq",
  ``!s t. s_val_eq s t /\ s_key_eq s t ==> s =t``,
  Induct>-
    (Cases>>fs[s_val_eq_def])>>
  rw[]>>
  Cases_on`t`>>fs[s_val_eq_def,s_key_eq_def,s_frame_val_and_key_eq])

val dec_stack_stack_key_eq = prove(
  ``!wl st st'. dec_stack wl st = SOME st' ==> s_key_eq st st'``,
  ho_match_mp_tac dec_stack_ind>>rw[dec_stack_def]>>
  fs[s_key_eq_def]>>
  every_case_tac>>fs[]>>rw[]>>fs[dec_stack_def]>>rw[]>>
  Cases_on `handler`>>
  fs [s_key_eq_def,s_frame_key_eq_def,MAP_ZIP,NOT_LESS])

(*gc preserves the stack_key relation*)
val gc_s_key_eq = store_thm("gc_s_key_eq",
  ``!s x. gc s = SOME x ==> s_key_eq s.stack x.stack``,
  rw[gc_def] >>fs[LET_THM]>>every_case_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  fs[state_component_equality]>>rfs[])

val s_val_eq_enc_stack = prove(
  ``!st st'. s_val_eq st st' ==> enc_stack st = enc_stack st'``,
  Induct>>Cases_on`st'`>>fs[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`h'`>>Cases_on`o''`>>Cases_on`o'`>>
  fs[s_frame_val_eq_def,enc_stack_def])

val s_val_eq_dec_stack = prove(
  ``!q st st' x. s_val_eq st st' /\ dec_stack q st = SOME x ==>
    ?y. dec_stack q st' = SOME y /\ s_val_eq x y``,
   ho_match_mp_tac dec_stack_ind >> rw[] >>
   Cases_on`st'`>>fs[s_val_eq_def,s_val_eq_refl]>>
   Cases_on`h`>>fs[dec_stack_def]>>
   pop_assum mp_tac>>CASE_TAC >>
   first_x_assum(qspecl_then [`t`,`x'`] assume_tac)>> rfs[]>>
   strip_tac>>pop_assum (SUBST1_TAC o SYM)>>
   fs[s_frame_val_eq_def,s_val_eq_def]>>
   `LENGTH l' = LENGTH l` by
    (Cases_on `handler` \\ Cases_on `o'` \\ fs [s_frame_val_eq_def]
     \\ metis_tac[LENGTH_MAP]) \\ fs [NOT_LESS]
   \\ Cases_on `handler` \\ Cases_on `o'` \\ fs[s_frame_val_eq_def,s_val_eq_def]
   \\ fs [MAP_ZIP,LENGTH_TAKE])

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)
val gc_s_val_eq = store_thm("gc_s_val_eq",
  ``!s x st y. s_val_eq s.stack st /\
             gc s = SOME y ==>
      ?z. gc (s with stack := st) = SOME (y with stack := z) /\
          s_val_eq y.stack z /\ s_key_eq z st``,
  rw[gc_def]>>fs[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>fs[]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> fs[]>>
  strip_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`y'`>>fs[state_component_equality]>>rfs[])

(*Slightly more general theorem allows the unused locals to be differnt*)
val gc_s_val_eq_word_state = store_thm("gc_s_val_eq_word_state",
  ``!s tlocs tstack y.
          s_val_eq s.stack tstack /\
          gc s = SOME y ==>
    ?zlocs zstack.
          gc (s with <|stack:=tstack;locals:=tlocs|>) =
          SOME (y with <|stack:=zstack;locals:=zlocs|>) /\
          s_val_eq y.stack zstack /\ s_key_eq zstack tstack``,
  rw[gc_def]>>fs[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>fs[]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> fs[]>>
  strip_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`tlocs`>>
  Q.EXISTS_TAC`y'`>>
  fs[state_component_equality]>>rfs[])

(*Most generalised gc_s_val_eq*)
val gc_s_val_eq_gen = store_thm ("gc_s_val_eq_gen",
``
  !s t s'.
  s.gc_fun = t.gc_fun ∧
  s.memory = t.memory ∧
  s.mdomain = t.mdomain ∧
  s.store = t.store ∧
  s_val_eq s.stack t.stack ∧
  gc s = SOME s' ⇒
  ?t'.
  gc t = SOME t' ∧
  s_val_eq s'.stack t'.stack ∧
  s_key_eq t.stack t'.stack ∧
  t'.memory = s'.memory ∧
  t'.store = s'.store`` ,
  rw[]>>
  fs[gc_def,LET_THM]>>
  IMP_RES_TAC s_val_eq_enc_stack>>
  every_case_tac>>rfs[]>>
  IMP_RES_TAC s_val_eq_dec_stack>>fs[]>>
  qpat_assum`A=s'` (SUBST_ALL_TAC o SYM)>>
  IMP_RES_TAC dec_stack_stack_key_eq>>fs[]>>
  metis_tac[s_val_eq_sym])

(*pushing and popping maintain the stack_key relation*)
val push_env_pop_env_s_key_eq = store_thm("push_env_pop_env_s_key_eq",
  ``!s t x opt. s_key_eq (push_env x opt s).stack t.stack ==>
              ?y. (pop_env t = SOME y /\
                   s_key_eq s.stack y.stack)``,
  rw[]>>Cases_on`opt`>>TRY(PairCases_on`x'`)>>
  fs[push_env_def]>>fs[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  fs[s_key_eq_def,pop_env_def]>>every_case_tac>>
  fs[])

val get_vars_stack_swap = prove(
  ``!l s t. s.locals = t.locals ==>
    get_vars l s = get_vars l t``,
  Induct>>fs[get_vars_def,get_var_def]>>
  rw[]>> every_case_tac>>
  metis_tac[NOT_NONE_SOME,SOME_11])

val get_vars_stack_swap_simp = prove(
  ``!args. get_vars args (s with stack := xs) = get_vars args s``,
  `(s with stack:=xs).locals = s.locals` by fs[]>>
  metis_tac[get_vars_stack_swap])

val s_val_eq_length = store_thm("s_val_eq_length",
  ``!s t. s_val_eq s t ==> LENGTH s = LENGTH t``,
  Induct>>Cases>>fs[s_val_eq_def,LENGTH]>>
  Cases>>fs[s_val_eq_def])

val s_key_eq_length = store_thm("s_key_eq_length",
  ``!s t. s_key_eq s t ==> LENGTH s = LENGTH t``,
  Induct>>Cases>>fs[s_key_eq_def,LENGTH]>>
  Cases>>fs[s_key_eq_def])

val s_val_eq_APPEND = prove(
  ``!s t x y. (s_val_eq s t /\ s_val_eq x y)==> s_val_eq (s++x) (t++y)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def])

val s_val_eq_REVERSE = prove(
  ``!s t. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def,s_val_eq_APPEND])

val s_val_eq_TAKE = prove(
  ``!s t n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def]>>IF_CASES_TAC>>
  fs[s_val_eq_def])

val s_val_eq_LAST_N = prove(
  ``!s t n. s_val_eq s t
    ==> s_val_eq (LAST_N n s) (LAST_N n t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[LAST_N_def]>>fs[s_val_eq_def]>>
  `s_val_eq [x] [y]` by fs[s_val_eq_def]>>
  `s_val_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    fs[s_val_eq_APPEND,s_val_eq_REVERSE]>>
  IMP_RES_TAC s_val_eq_TAKE>>
  metis_tac[s_val_eq_REVERSE])

val s_key_eq_APPEND = prove(
  ``!s t x y. (s_key_eq s t /\ s_key_eq x y)==> s_key_eq (s++x) (t++y)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def])

val s_key_eq_REVERSE = prove(
  ``!s t. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def,s_key_eq_APPEND])

val s_key_eq_TAKE = prove(
  ``!s t n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def]>>IF_CASES_TAC>>
  fs[s_key_eq_def])

val s_key_eq_LAST_N = prove(
  ``!s t n. s_key_eq s t
    ==> s_key_eq (LAST_N n s) (LAST_N n t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[LAST_N_def]>>fs[s_key_eq_def]>>
  `s_key_eq [x] [y]` by fs[s_key_eq_def]>>
  `s_key_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    fs[s_key_eq_APPEND,s_key_eq_REVERSE]>>
  IMP_RES_TAC s_key_eq_TAKE>>
  metis_tac[s_key_eq_REVERSE])

val s_key_eq_tail = store_thm("s_key_eq_tail",
 ``!a b c d. s_key_eq (a::b) (c::d) ==> s_key_eq b d``,
  fs[s_key_eq_def])

val s_val_eq_tail = prove(
 ``!a b c d. s_val_eq (a::b) (c::d) ==> s_val_eq b d``,
  fs[s_val_eq_def])

val s_key_eq_LAST_N_exists = prove(
  ``!s t n e y xs. s_key_eq s t /\
    LAST_N n s = StackFrame e (SOME y)::xs
    ==> ?e' ls. LAST_N n t = StackFrame e' (SOME y)::ls
        /\ MAP FST e' = MAP FST e
        /\ s_key_eq xs ls``,
   rpt strip_tac>>
   IMP_RES_TAC s_key_eq_LAST_N>>
   first_x_assum (qspec_then `n` assume_tac)>> rfs[]>>
   Cases_on`LAST_N n t`>>
   fs[s_key_eq_def]>>
   Cases_on`h`>>Cases_on`o'`>>fs[s_frame_key_eq_def])

val s_val_eq_LAST_N_exists = store_thm("s_val_eq_LAST_N_exists",
  ``!s t n e y xs. s_val_eq s t /\
   LAST_N n s = StackFrame e (SOME y)::xs
    ==> ?e' ls. LAST_N n t = StackFrame e' (SOME y)::ls
       /\ MAP SND e' = MAP SND e
       /\ s_val_eq xs ls``,
  rpt strip_tac>>
  IMP_RES_TAC s_val_eq_LAST_N>>
  first_x_assum (qspec_then `n` assume_tac)>> rfs[]>>
  Cases_on`LAST_N n t`>>
  fs[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`o'`>>fs[s_frame_val_eq_def])

val LAST_N_LENGTH_cond = store_thm("LAST_N_LENGTH_cond",
  ``!n xs. n = LENGTH xs ==> LAST_N n xs =xs``,
  metis_tac[LAST_N_LENGTH] )

val handler_eq = prove(
  ``x with handler := x.handler = x``, fs[state_component_equality])

(*Stack is irrelevant to word_exp*)
val word_exp_stack_swap = prove(
  ``!s e st. word_exp s e = word_exp (s with stack:=st) e``,
  ho_match_mp_tac word_exp_ind>>
  rw[word_exp_def]>-
  (first_x_assum(qspec_then `st` SUBST1_TAC)>>
  every_case_tac>>fs[mem_load_def])>-
  (`ws = ws'` by
  (bossLib.UNABBREV_ALL_TAC>>
  fs[MEM_MAP,EVERY_MEM,MAP_EQ_f])>>fs[])>>
  every_case_tac>>fs[])

(*Stack swap theorem for evaluate*)
val evaluate_stack_swap = store_thm("evaluate_stack_swap",``
  !c s.
      case evaluate (c,s) of
      | (SOME Error,s1) => T
      | (SOME TimeOut,s1) => s1.stack = [] /\ s1.locals = LN /\
                             (!xs. s_val_eq s.stack xs ==>
                                   evaluate(c,s with stack := xs) =
                                        (SOME TimeOut, s1))
      | (SOME NotEnoughSpace,s1) => s1.stack = [] /\ s1.locals = LN /\
                                    (!xs. s_val_eq s.stack xs ==>
                                          evaluate(c,s with stack := xs) =
                                               (SOME NotEnoughSpace, s1))
                             (*for both errors,
                               the stack and locs should also be [] so the swapped stack
                               result should be exactly the same*)
      | (SOME (Exception x y),s1) =>
            (s.handler<LENGTH s.stack) /\ (*precondition for jump_exc*)
            (?e n ls lss.
                (LAST_N (s.handler+1) s.stack = StackFrame e (SOME n)::ls) /\
                (MAP FST e = MAP FST lss /\
                   s1.locals = fromAList lss) /\
                (s_key_eq s1.stack ls) /\ (s1.handler = case n of(a,b,c)=>a) /\
                (!xs e' ls'.
                           (LAST_N (s.handler+1) xs =
                             StackFrame e' (SOME n):: ls') /\
                           (s_val_eq s.stack xs) ==> (*this implies n=n'*)
                           ?st locs.
                           (evaluate (c,s with stack := xs) =
                              (SOME (Exception x y),
                               s1 with <| stack := st;
                                          handler := case n of (a,b,c) => a;
                                          locals := locs |>) /\
                            (?lss'. MAP FST e' = MAP FST lss' /\
                               locs = fromAList lss' /\
                               MAP SND lss = MAP SND lss')/\
                            s_val_eq s1.stack st /\ s_key_eq ls' st)))
      (*NONE, SOME Result cases*)
      | (res,s1) => (s_key_eq s.stack s1.stack) /\ (s1.handler = s.handler) /\
                    (!xs. s_val_eq s.stack xs ==>
                          ?st. evaluate (c,s with stack := xs) =
                                (res, s1 with stack := st)  /\
                                s_val_eq s1.stack st /\
                                s_key_eq xs st)``,
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]
  >-(*Skip*)
    (fs[evaluate_def,s_key_eq_refl]>>rw[]>>HINT_EXISTS_TAC>>fs[s_key_eq_refl])
  >-(*Alloc*)
    (fs[evaluate_def,alloc_def]>>reverse every_case_tac>>
    (every_case_tac>>
    IMP_RES_TAC gc_s_key_eq>>
    IMP_RES_TAC push_env_pop_env_s_key_eq>>
    `s_key_eq s.stack y.stack` by fs[set_store_def]>>
    fs[SOME_11]>>TRY(CONJ_TAC>>rw[]>-
      (qpat_assum`gc a = SOME b` mp_tac>>
      qpat_assum`pop_env a = b` mp_tac>>
      fs[pop_env_def,gc_def,push_env_def,set_store_def
        ,LET_THM,env_to_list_def]>>
      every_case_tac>>fs[s_key_eq_def,s_frame_key_eq_def]>>
      rw[]>>fs[]))>> TRY(fs[call_env_def,fromList2_def]>>rw[])>>
    full_case_tac>>fs[get_var_def]>>
    full_case_tac>>
    Q.MATCH_ASSUM_ABBREV_TAC `gc a = y`>>
    Q.MATCH_ASSUM_ABBREV_TAC `gc b = SOME x'`>>
    `s_val_eq b.stack a.stack /\ b with stack:=a.stack = a` by
      (fs[push_env_def,LET_THM,env_to_list_def,set_store_def]>>
      bossLib.UNABBREV_ALL_TAC>>
      fs[s_val_eq_def,s_frame_val_eq_def,s_val_eq_sym])>>
    Q.UNABBREV_TAC `y`>>
    IMP_RES_TAC gc_s_val_eq>>rfs[]>>
    Q.UNABBREV_TAC`b`>>Q.UNABBREV_TAC`a`>>
    fs[push_env_def,set_store_def,LET_THM,env_to_list_def]>>
    Cases_on`x'.stack`>>
    Cases_on`z'`>>fs[s_key_eq_def,state_component_equality]>>
    `h=h'` by (
      fs[s_val_eq_def,s_key_eq_def]>>
      `s_frame_key_eq h' h` by metis_tac[s_frame_key_eq_trans]>>
      metis_tac[s_frame_val_and_key_eq,s_frame_key_eq_sym])>>
    fs[pop_env_def] >>Cases_on`h'`>>Cases_on`o'`>>fs[s_frame_key_eq_def]>>
    fs[state_component_equality]>>
    fs[has_space_def])>-fs[state_component_equality]>>
    Q.EXISTS_TAC`t'`>>
    fs[state_component_equality]>>
    metis_tac[s_val_eq_def,s_key_eq_sym])
  >-(*Move*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_vars_def,s_key_eq_refl]>>
    rpt strip_tac>>HINT_EXISTS_TAC>>
    assume_tac get_vars_stack_swap_simp>>
    fs[s_key_eq_refl])
  >-(*Inst*)
    (fs[evaluate_def,inst_def,assign_def]>>
    every_case_tac>>fs[set_var_def,s_key_eq_refl]>>
    srw_tac [] []>>fs[set_var_def,s_key_eq_refl]>>
    every_case_tac>>fs[set_var_def,s_key_eq_refl]>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,mem_store_def]>>
    srw_tac [] []>>fs[set_var_def,s_key_eq_refl,get_var_def,mem_load_def]>>
    HINT_EXISTS_TAC>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Assign*)
    (fs[evaluate_def]>>every_case_tac>>fs[set_var_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Get*)
    (fs[evaluate_def]>>every_case_tac>>fs[set_var_def,s_key_eq_refl]>>
    fs[set_store_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Set*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_store_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Store*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[mem_store_def,state_component_equality,s_key_eq_refl]>>
    rpt strip_tac>>HINT_EXISTS_TAC>>
    fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,get_var_def,
       state_component_equality])
  >- (*Tick*)
    (fs[evaluate_def]>>every_case_tac>- fs[call_env_def,fromList2_def] >>
    fs[dec_clock_def,s_key_eq_refl]>>
    rpt strip_tac>>Q.EXISTS_TAC`xs`>>fs[s_key_eq_refl])
  >- (*MustTerminate*)
    (fs[evaluate_def]>>
    LET_ELIM_TAC>> every_case_tac>>fs[]>>
    TRY(rw[]>>res_tac>>simp[]>>metis_tac[])
    >-
      (qexists_tac`lss`>>simp[]>>
      rw[]>>res_tac>>simp[]>>
      metis_tac[])
    >>
    ntac 5 strip_tac>>
    res_tac>>
    rfs[]>>simp[])
  >-(*Seq*)
    (fs[evaluate_def]>>
    Cases_on`evaluate(c',s)`>>
    fs[LET_THM]>>
    IF_CASES_TAC>-
      (*q = NONE*)
      (every_case_tac>>
      fs[s_key_eq_trans]>> TRY
        (qho_match_abbrev_tac`A ∧ ∀xs. P xs` >> unabbrev_all_tac >> simp[] >>
        CONJ_TAC>-metis_tac[s_key_eq_trans]>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>
        first_x_assum(qspec_then `st` assume_tac)>>rfs[]>>
        HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>-
        (ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LAST_N_exists)>>
        (*get the result stack from first eval*)
        IMP_RES_TAC s_key_eq_length>>fs[]>>
        first_x_assum(qspecl_then [`r.stack`,`s.stack`,`s.handler+1`,`e`,`n`,`ls`] assume_tac)>>
        `s_key_eq r.stack s.stack` by rw[s_key_eq_sym]>>
        fs[]>>rfs[]>>Q.EXISTS_TAC`lss`>>
        simp[]>>CONJ_TAC>-metis_tac[s_key_eq_trans]>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>
        rfs[]>>
        IMP_RES_TAC s_key_eq_LAST_N_exists>>
        last_x_assum(qspecl_then [`st`,`e'''`,`ls'''`] assume_tac)>>
        rfs[]>>
        HINT_EXISTS_TAC>>
        Q.EXISTS_TAC`fromAList lss'`>>
        fs[]>>
        CONJ_TAC>- (Q.EXISTS_TAC`lss'`>>fs[])>>
        metis_tac[s_key_eq_trans])>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>rfs[])>>
      Cases_on`q`>>fs[]>>
      Cases_on`x`>>fs[]>>
      rpt strip_tac>-
        (first_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>HINT_EXISTS_TAC>>
        fs[])>-
      (Q.EXISTS_TAC`lss`>>fs[]>>
      rpt strip_tac>>
      first_x_assum (qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
      HINT_EXISTS_TAC>>
      Q.EXISTS_TAC`fromAList lss'`>>fs[]>>
      Q.EXISTS_TAC`lss'`>>fs[])>>
      first_x_assum (qspec_then `xs` assume_tac)>> rfs[]>>HINT_EXISTS_TAC>>fs[])
  >-(*Return*)
    (fs[evaluate_def]>> every_case_tac>>
    fs[call_env_def,s_key_eq_refl]>>
    rpt strip_tac>>fs[get_var_def]>>HINT_EXISTS_TAC>>
    fs[state_component_equality,s_key_eq_refl])
  >-(*Raise*)
    (fs[evaluate_def]>>every_case_tac>>fs[get_var_def,jump_exc_def]>>
    qpat_assum `(a = SOME x)` mp_tac>>
    every_case_tac>>fs[state_component_equality]>>
    strip_tac>> Q.EXISTS_TAC `l`>>
    fs[EQ_SYM_EQ,s_key_eq_refl]>>
    rpt strip_tac>>
    IMP_RES_TAC s_val_eq_length>>fs[EQ_SYM_EQ,state_component_equality]>>
    fs[s_key_eq_refl]>>
    `s.handler + 1<= LENGTH s.stack` by metis_tac[arithmeticTheory.LESS_OR,arithmeticTheory.ADD1]>>
    rpt (qpat_assum `a = LAST_N b c` (ASSUME_TAC o SYM))>>
    IMP_RES_TAC s_val_eq_LAST_N>>
    first_x_assum(qspec_then `s.handler+1` assume_tac)>>rfs[]>>
    IMP_RES_TAC s_val_eq_tail>>
    fs[s_val_eq_def,s_frame_val_eq_def]>>
    Q.EXISTS_TAC`e'`>>fs[])
  >-(*If*)
    (fs[evaluate_def]>>
    ntac 4 full_case_tac>>fs[]>>
    Cases_on`word_cmp cmp c''' c`>> fs[]>>
    every_case_tac>>
    fs[s_key_eq_trans]>>rw[]>>
    TRY(last_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>
    fs[get_var_def]>>Cases_on`ri`>>fs[get_var_imm_def,get_var_def]>>
    HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>>
    qexists_tac`lss`>>fs[]>>rw[]>>
    IMP_RES_TAC s_val_eq_LAST_N_exists>>
    last_x_assum(qspecl_then [`xs`,`e'''`,`ls'''`] assume_tac)>>
    Cases_on`ri`>>rfs[get_var_def,get_var_imm_def]>>
    HINT_EXISTS_TAC>>fs[]>>
    qexists_tac`fromAList lss'`>>fs[]>>
    qexists_tac`lss'`>>fs[])
  >-(*FFI*)
    (fs[evaluate_def]>>
    every_case_tac>>Cases_on`call_FFI s.ffi ffi_index x'`>>fs[LET_THM]>>
    rw[]>>fs[get_var_def]>>
    metis_tac[s_key_eq_refl])
  >-(*Call*)
  (fs[evaluate_def]>>
  Cases_on`get_vars args s`>> fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`find_code dest (add_ret_loc ret x) s.code`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  Cases_on`ret`>>fs[]
  >-
    (*Tail Call*)
    (Cases_on`handler`>>fs[]>>
    every_case_tac>>
    fs[dec_clock_def,call_env_def,fromList2_def]>>
    TRY (ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspec_then `xs` (assume_tac))>>rfs[]>>
    Q.EXISTS_TAC`st`>>
    fs[state_component_equality,s_key_eq_refl])>>
    Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[state_component_equality]>>
    Q.EXISTS_TAC`lss'`>>fs[])
  >>
    (*Returning call*)
    PairCases_on`x'`>> fs[]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on`cut_env x'1 s.locals`>>fs[]>>
    Cases_on`s.clock=0`>-
      (fs[call_env_def,fromList2_def]>>rw[]>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[])>>
    fs[]>>
    Cases_on`evaluate (r,call_env q (push_env x' handler (dec_clock s)))`>>
    Cases_on`q'`>>fs[]>>Cases_on`x''`>>fs[]
    >-
      (*Result*)
      (fs[get_vars_stack_swap_simp]>>
      IF_CASES_TAC>>fs[]>>
      full_case_tac>>
      IF_CASES_TAC>>
      fs[set_var_def,call_env_def]>>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>fs[dec_clock_def,SOME_11]>>
      Cases_on`evaluate(x'2,x'' with locals:=insert x'0 w0 x''.locals)`>>fs[]>>
      Cases_on`q'`>>TRY(Cases_on`x'''`)>>fs[]>>rfs[]>>
      `s_key_eq s.stack x''.stack` by fs[EQ_SYM_EQ]>>fs[]>>
      (*Inductive Result and None*)
      TRY
      (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
      CONJ_TAC>- metis_tac[s_key_eq_trans]>>CONJ_ASM1_TAC>-
      (Cases_on`handler`>>
      TRY(PairCases_on`x'''`)>>
      fs[push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
      Cases_on`r'.stack`>>fs[s_key_eq_def]>>Cases_on`h`>>Cases_on`o'`>>
      TRY(PairCases_on`x'''`)>>
      fs[s_frame_key_eq_def]>>
      fs[state_component_equality]>>rfs[])>>
      ntac 2 strip_tac>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
      Cases_on`handler`>>
      (TRY(PairCases_on`x'''`)>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      last_x_assum(qspec_then `frame::xs` assume_tac)>>
      rfs[]>>
      `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
      Cases_on`st`>>fs[s_key_eq_def]>>
      Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o'`>>fs[]>>
      fs[state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rfs[]>>
      TRY(Cases_on`x'''`>>
          `x''.stack = t'` by fs[EQ_SYM_EQ]>>fs[]>>rfs[])>>
      Q.EXISTS_TAC`st`>> fs[state_component_equality]
      >-
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r' with <|locals := insert x'0 w0 x''.locals; stack := t|>` by
          fs[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        rw[]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])
      >>
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r' with <|locals := insert x'0 w0 x''.locals; stack := t; handler:=s.handler|>` by
          fs[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        rw[]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])))
      (*Exceptions*)
      >-
        (`s.handler = x''.handler` by
          (Cases_on`handler`>>
          TRY(PairCases_on`x'''`)>>
          fs[push_env_def,LET_THM,env_to_list_def]>>
          Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
          Cases_on`h`>>Cases_on`o'`>>TRY(PairCases_on`x'''`)>>
          fs[s_frame_key_eq_def]>>
          fs[state_component_equality])>>
        CONJ_ASM1_TAC >- metis_tac[s_key_eq_length]>>
        `s_key_eq x''.stack s.stack` by metis_tac[s_key_eq_sym]>>
        IMP_RES_TAC s_key_eq_LAST_N_exists>>
        fs[]>>
        (*check*)
        qexists_tac`lss`>>fs[]>>
        CONJ_TAC>-
          metis_tac[s_key_eq_trans]
        >>
        rpt strip_tac>>fs[]>>
        `!a. s_val_eq (a::s.stack) (a::xs)` by
         (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
          Cases_on`o'`>>fs[s_frame_val_eq_def])>>
        Cases_on`handler`>>
        TRY(PairCases_on`x'''`)>>
        fs[push_env_def,LET_THM,env_to_list_def]>>
        qpat_abbrev_tac `frame = StackFrame A B`>>
        first_x_assum (qspec_then `frame` assume_tac)>>
        last_x_assum(qspec_then `frame::xs` assume_tac)>>
        rfs[]>>
        `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
        Cases_on`st`>>fs[s_key_eq_def]>>
        Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
        `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                              s_frame_val_and_key_eq,s_val_eq_def]>>
        Cases_on`h'`>>Cases_on`o'`>>
        fs[Abbr`frame`,s_frame_key_eq_def]>>
        TRY(PairCases_on`x'''`)>>
        fs[state_component_equality]>>
        IMP_RES_TAC s_val_eq_tail>>
        first_x_assum(qspec_then `t` assume_tac)>> rfs[]>>
        IMP_RES_TAC s_key_eq_LAST_N_exists>>
        first_x_assum(qspecl_then[`e''''`,`ls''''`] assume_tac)>>rfs[]
        >-
          (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
           r' with <|locals := insert x'0 w0 x''.locals; stack := t|>` by
             fs[state_component_equality]>>
          fs[PULL_EXISTS]>>
          HINT_EXISTS_TAC>>fs[]>>
          qexists_tac`lss'`>>fs[]>>
          metis_tac[s_key_eq_trans])
        >>
          (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
          r' with <|locals := insert x'0 w0 x''.locals; stack := t; handler:=x'''0|>` by
            fs[state_component_equality]>>
          fs[PULL_EXISTS]>>
          HINT_EXISTS_TAC>>fs[]>>
          qexists_tac`lss'`>>fs[]>>
          metis_tac[s_key_eq_trans]))
      (*The rest*)
      >>
      (ntac 2 strip_tac>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
      Cases_on`handler`>>
      TRY(PairCases_on`x'''`)>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      last_x_assum(qspec_then `frame::xs` assume_tac)>>
      rfs[]>>
      `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
      Cases_on`st`>>fs[s_key_eq_def]>>
      Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o'`>>
      fs[Abbr`frame`,s_frame_key_eq_def]>>
      TRY(PairCases_on`x'''`)>>
      fs[state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rfs[]
      >-
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
         r' with <|locals := insert x'0 w0 x''.locals; stack := t|>` by
        fs[state_component_equality]>>
        fs[])
      >>
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r' with <|locals := insert x'0 w0 x''.locals; stack := t; handler:=s.handler|>` by
          fs[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        rw[]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])))
     >-
     (*Exception*)
     (Cases_on`handler`>>fs[]>-
       (*no handler*)
       (fs[call_env_def,push_env_def,env_to_list_def,dec_clock_def,LET_THM]>>
       CONJ_ASM1_TAC>-
       (IMP_RES_TAC prim_recTheory.LESS_LEMMA1>>
       qpat_assum `LAST_N a as=b` mp_tac>>simp[]>>
       qpat_abbrev_tac `frame = StackFrame a b`>>
       `LENGTH s.stack+1 = LENGTH (frame::s.stack) ` by fs[arithmeticTheory.ADD1]>>
       pop_assum SUBST1_TAC>> fs[LAST_N_LENGTH]>>
       Q.UNABBREV_TAC`frame`>>fs[option_nchotomy])>>
       fs[GEN_ALL LAST_N_TL]>>
       Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
       assume_tac get_vars_stack_swap_simp>>
       first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
       qpat_abbrev_tac `frame = StackFrame a b`>>
       `s.handler < LENGTH xs` by (IMP_RES_TAC s_val_eq_length>>fs[])>>
       first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
       IMP_RES_TAC (GEN_ALL LAST_N_TL)>>
       last_x_assum(qspec_then `frame` assume_tac)>>
       fs[]>> rfs[]>>
       `s_val_eq (frame::s.stack) (frame::xs)` by
         metis_tac[s_val_eq_def,s_frame_val_eq_def] >>
       fs[]>> HINT_EXISTS_TAC>>
       Q.EXISTS_TAC`fromAList lss'`>>fs[state_component_equality]>>
       Q.EXISTS_TAC`lss'`>>fs[])>>
       (*handler*)
       PairCases_on`x''`>>
       fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
       every_case_tac>>rfs[set_var_def]>>fs[]>>
       `r'.handler = s.handler` by
       (`LENGTH s.stack +1 =
        LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         fs[LAST_N_LENGTH]>>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
       TRY
         (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
         (ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC>-
         (`LENGTH s.stack +1 =
           LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         fs[LAST_N_LENGTH]>>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
         rpt strip_tac>>
         assume_tac get_vars_stack_swap_simp>>
         first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
         qpat_abbrev_tac`frame = StackFrame c d`>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
         IMP_RES_TAC s_val_eq_LAST_N_exists>>
         `LENGTH s.stack = LENGTH xs` by fs[s_val_eq_length] >>
         first_x_assum(qspec_then`frame::xs` assume_tac)>>rfs[]>>
         first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
         `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
          LENGTH s.stack +1 = LENGTH (frame::xs)` by
           fs[arithmeticTheory.ADD1,s_val_eq_length]>>
          fs[LAST_N_LENGTH_cond]>>
          `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
          `lss = lss'` by fs[LIST_EQ_MAP_PAIR]>>
          fs[]>>
          last_x_assum(qspec_then `st` assume_tac)>>
          rfs[]>>HINT_EXISTS_TAC>>
          metis_tac[s_key_eq_trans,handler_eq]))>-
          (CONJ_TAC >- (
          `LENGTH s.stack +1 =
           LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           `LENGTH ls = LENGTH r'.stack` by fs[s_key_eq_length]>>
           fs[])>>
           IMP_RES_TAC s_key_eq_LAST_N_exists>>
           Q.EXISTS_TAC`e''`>>
           Q.EXISTS_TAC`n`>>
           Q.EXISTS_TAC`ls''`>>
           fs[]>>
           Q.EXISTS_TAC`lss'`>>
          (*check*)
           CONJ_TAC>-
           (`LENGTH s.stack +1 =
             LENGTH (StackFrame (list_rearrange (s.permute 0)
             (QSORT key_val_compare (toAList x')))
             (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           `LENGTH ls = LENGTH r'.stack` by fs[s_key_eq_length]>>
           fs[EQ_SYM_EQ])>>
           fs[]>>
           CONJ_TAC>- metis_tac[s_key_eq_trans]>>
           rpt strip_tac>>
           assume_tac get_vars_stack_swap_simp>>
           first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
           qpat_abbrev_tac`frame = StackFrame c d`>>
           `s_val_eq (frame::s.stack) (frame::xs)` by
             metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
           IMP_RES_TAC s_val_eq_LAST_N_exists>>
           pop_assum kall_tac>>
           first_x_assum(qspec_then `frame::xs` assume_tac)>>
           rfs[]>>
           `LENGTH s.stack = LENGTH xs` by fs[s_val_eq_length] >>
           first_x_assum(qspecl_then [`frame::xs`,`e''''`,`ls''''`] assume_tac)>>
           rfs[]>>
           `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
            LENGTH s.stack +1 = LENGTH (frame::xs)` by
             fs[arithmeticTheory.ADD1,s_val_eq_length]>>
           fs[LAST_N_LENGTH_cond]>>
           `MAP FST lss = MAP FST lss''` by metis_tac[EQ_SYM_EQ]>>
           `lss'' = lss` by fs[LIST_EQ_MAP_PAIR]>>
           fs[]>>
           IMP_RES_TAC s_key_eq_LAST_N_exists>>
           first_x_assum (qspecl_then [`st`,`e'''''''`,`ls'''''''`] assume_tac)>>
           rfs[]>>
           fs[handler_eq]>>
           HINT_EXISTS_TAC>>Q.EXISTS_TAC`fromAList lss'''`>>
           fs[handler_eq]>>
           CONJ_TAC >-
             metis_tac[handler_eq]>>
           CONJ_TAC>-
            (Q.EXISTS_TAC`lss'''`>>fs[])>>
           metis_tac[s_key_eq_trans])>>
           (*TimeOut*)
           rpt strip_tac>>
           assume_tac get_vars_stack_swap_simp>>
           first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
           qpat_abbrev_tac`frame = StackFrame c d`>>
           `s_val_eq (frame::s.stack) (frame::xs)` by
             metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
           IMP_RES_TAC s_val_eq_LAST_N_exists>>
           `LENGTH s.stack = LENGTH xs` by fs[s_val_eq_length] >>
           first_x_assum(qspec_then`frame::xs` assume_tac)>>rfs[]>>
           first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
           `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
            LENGTH s.stack +1 = LENGTH (frame::xs)` by
              fs[arithmeticTheory.ADD1,s_val_eq_length]>>
            fs[LAST_N_LENGTH_cond]>>
            `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
            `lss = lss'` by fs[LIST_EQ_MAP_PAIR]>>
            pop_assum (SUBST1_TAC o SYM)>>
            fs[]>>
            first_x_assum(qspec_then `st` assume_tac)>>
            rfs[]>>
            metis_tac[handler_eq])>>
    (*Cleanup...*)
    ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` SUBST1_TAC)>>simp[]>>
    `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
     Cases_on`handler`>>TRY(PairCases_on`x''`)>>
     fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def]>>
     qpat_abbrev_tac `frame = StackFrame ls n`>>
     first_x_assum (qspec_then `frame` assume_tac)>>
     first_x_assum(qspec_then `frame::xs` assume_tac)>>
     rfs[call_env_def]>>
     `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]))

(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)

val ignore_inc = prove(``
  ∀perm:num->num->num.
  (λn. perm(n+0)) = perm``,rw[FUN_EQ_THM])

val ignore_perm = prove(``
  ∀st. st with permute := st.permute = st`` ,
  rw[]>>fs[state_component_equality])

val get_vars_perm = store_thm("get_vars_perm",``
  ∀args.get_vars args (st with permute:=perm) = get_vars args st``,
  Induct>>rw[get_vars_def,get_var_def])

val pop_env_perm = store_thm("pop_env_perm",``
  pop_env (rst with permute:=perm) =
  (case pop_env rst of
    NONE => NONE
  | SOME rst' => SOME (rst' with permute:=perm))``,
  fs[pop_env_def]>>every_case_tac>>
  fs[state_component_equality])

val gc_perm = prove(``
  gc st = SOME x ⇒
  gc (st with permute:=perm) = SOME (x with permute := perm)``,
  fs[gc_def,LET_THM]>>every_case_tac>>
  fs[state_component_equality])

val get_var_perm = store_thm("get_var_perm",``
  get_var n (st with permute:=perm) =
  (get_var n st)``,fs[get_var_def])

val get_var_imm_perm = store_thm("get_var_imm_perm",``
  get_var_imm n (st with permute:=perm) =
  (get_var_imm n st)``,
  Cases_on`n`>>
  fs[get_var_imm_def,get_var_perm])

val set_var_perm = store_thm("set_var_perm",``
  set_var v x (s with permute:=perm) =
  (set_var v x s) with permute:=perm``,
  fs[set_var_def])

val get_vars_perm = prove(``
  ∀ls. get_vars ls (st with permute:=perm) =
  (get_vars ls st)``,
  Induct>>fs[get_vars_def,get_var_perm])

val set_vars_perm = prove(``
  ∀ls. set_vars ls x (st with permute := perm) =
       (set_vars ls x st) with permute:=perm``,
  fs[set_vars_def])

val word_state_rewrites = prove(``
  (st with clock:=A) with permute:=B =
  (st with <|clock:=A ;permute:=B|>)``,
  fs[])

val perm_assum_tac = (first_x_assum(qspec_then`perm`assume_tac)>>
          fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
          qexists_tac`λx. if x = 0 then st.permute 0 else perm' (x-1)`>>
          fs[call_env_def]>>
          `(λn. perm' n) = perm'` by fs[FUN_EQ_THM]>>
          simp[]);

val word_exp_perm = store_thm("word_exp_perm",``
  ∀s exp. word_exp (s with permute:=perm) exp =
          word_exp s exp``,
  ho_match_mp_tac word_exp_ind>>rw[word_exp_def]
  >-
    (every_case_tac>>fs[mem_load_def])
  >>
    `ws=ws'` by
      (unabbrev_all_tac>>
      fs[MAP_EQ_f])>>
    fs[])

val mem_store_perm = prove(``
  mem_store a (w:'a word_loc) (s with permute:=perm) =
  case mem_store a w s of
    NONE => NONE
  | SOME x => SOME(x with permute:=perm)``,
  fs[mem_store_def]>>every_case_tac>>
  fs[state_component_equality])

val jump_exc_perm = prove(``
  jump_exc (st with permute:=perm) =
  case jump_exc st of
    NONE => NONE
  | SOME (x,l1,l2) => SOME (x with permute:=perm,l1,l2)``,
  fs[jump_exc_def]>>
  every_case_tac>>
  fs[state_component_equality]);

(*For any target result permute, we can find an initial permute such that the resulting permutation is the same*)
val permute_swap_lemma = store_thm("permute_swap_lemma",``
  ∀prog st perm.
  let (res,rst) = evaluate(prog,st) in
    res ≠ SOME Error  (*Provable without this assum*)
    ⇒
    ∃perm'. evaluate(prog,st with permute := perm') =
    (res,rst with permute:=perm)``,
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>>fs[evaluate_def]
  >-
    metis_tac[ignore_perm]
  >-
    (fs[alloc_def]>>
    qexists_tac`λx. if x = 0 then st.permute 0 else perm (x-1)`>>
    fs[get_var_perm]>>
    full_case_tac>>full_case_tac>>fs[]
    >-
      (Cases_on`x`>>fs[])
    >>
    full_case_tac>>fs[]>>
    Cases_on`gc (push_env x NONE (set_store AllocSize (Word c) st))`>>
    fs[push_env_def,env_to_list_def,LET_THM,set_store_def]>>
    imp_res_tac gc_perm>>fs[pop_env_perm]>>
    ntac 3 (full_case_tac>>fs[])>>
    fs[has_space_def]>>
    IF_CASES_TAC>>
    fs[state_component_equality,FUN_EQ_THM,call_env_def])
  >-
    (qexists_tac`perm`>>fs[get_vars_perm]>>
    ntac 2 (full_case_tac>>fs[])>>
    fs[set_vars_perm])
  >-
    (qexists_tac`perm`>>
    fs[inst_def,assign_def]>>every_case_tac>>
    fs[set_var_perm,word_exp_perm,get_var_perm,mem_store_perm,mem_load_def]>>
    rfs[]>>fs[]>>
    metis_tac[word_exp_perm,state_component_equality])
  >-
    (fs[word_exp_perm]>>every_case_tac>>
    fs[set_var_perm]>>
    metis_tac[state_component_equality])
  >-
    (every_case_tac>>fs[set_var_perm]>>
    metis_tac[state_component_equality])
  >-
    (fs[word_exp_perm]>>every_case_tac>>
    fs[set_store_def]>>
    qexists_tac`perm`>>fs[state_component_equality])
  >-
    (fs[word_exp_perm]>>every_case_tac>>
    fs[get_var_perm,mem_store_perm]>>
    metis_tac[state_component_equality])
  >-
    (qexists_tac`perm`>>
    every_case_tac>>fs[dec_clock_def,call_env_def]>>
    fs[state_component_equality])
  >- (*MustTerminate*)
    (fs[LET_THM]>>
    qpat_assum`A=(res,rst)` mp_tac>>
    TOP_CASE_TAC>>simp[]>>
    split_pair_tac>>simp[]>>
    TOP_CASE_TAC>>simp[]>>rw[]>>
    first_x_assum(qspec_then`perm` assume_tac)>>fs[]>>
    split_pair_tac>>fs[]>>rfs[]>>
    qexists_tac`perm'`>>simp[])
  >- (*Seq*)
    (fs[evaluate_def,LET_THM]>>
    Cases_on`evaluate(prog,st)`>>fs[]>>
    Cases_on`q`>>fs[]
    >-
      (last_x_assum(qspec_then `perm` assume_tac)>>fs[]>>
      last_x_assum(qspec_then `perm'` assume_tac)>>fs[]>>
      qexists_tac`perm''`>>fs[])
    >>
      first_x_assum(qspecl_then[`perm`]assume_tac)>>rfs[]>>
      Cases_on`x`>>fs[]>>
      qexists_tac`perm'`>>fs[]>>
      qpat_assum`A=res`(SUBST1_TAC o SYM)>>fs[])
  >-
    (fs[get_var_perm]>>every_case_tac>>
    fs[call_env_def,state_component_equality])
  >-
    (fs[get_var_perm]>>every_case_tac>>
    fs[jump_exc_perm]>>metis_tac[state_component_equality])
  >-
    (Cases_on`ri`>>
    fs[get_var_perm,get_var_imm_def]>>every_case_tac>>fs[]
    >>
      fs[LET_THM])
  >- (*FFI*)
    (qexists_tac`perm`>>
    fs[get_var_perm]>>
    every_case_tac>>Cases_on`call_FFI st.ffi ffi_index x'`>>
    fs[LET_THM,state_component_equality])
  >- (*Call*)
    (fs[evaluate_def,LET_THM]>>
    fs[get_vars_perm]>>
    ntac 5 (TOP_CASE_TAC>>fs[])
    >- (*Tail Call*)
      (every_case_tac>>
      TRY(qexists_tac`perm`>>
        fs[state_component_equality,call_env_def]>>NO_TAC)>>
      Cases_on`x'`>>
      fs[dec_clock_def]>>
      first_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
      qexists_tac`perm'`>>
      fs[state_component_equality,call_env_def]>>
      qpat_assum`A=res`(SUBST1_TAC o SYM)>>fs[])
    >>
      ntac 5 TOP_CASE_TAC>>fs[]>>
      ntac 2 (TOP_CASE_TAC>>fs[])
      >-
        (fs[call_env_def]>>
        qexists_tac`perm`>>fs[state_component_equality])
      >>
      Cases_on`evaluate(r,call_env q (push_env x'
              handler (dec_clock st)))`>>
      Cases_on`q'''''`>>fs[]>>
      Cases_on`x''`>>fs[]
      >-
        (qpat_assum`A=(res,rst)` mp_tac>>
        IF_CASES_TAC>>fs[]>>
        full_case_tac>>fs[]>>
        IF_CASES_TAC>>fs[]>>
        Cases_on`evaluate(q''',set_var q' w0 x'')`>>
        Cases_on`q'''''`>>
        TRY(Cases_on`x'''`)>>
        fs[]>>rw[]>>
        first_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
        first_x_assum(qspec_then`perm'`assume_tac)>>fs[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        Cases_on`handler`>>TRY(PairCases_on`x'''`)>>
        fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM,call_env_def]>>
        `(λn. perm'' n) = perm''` by fs[FUN_EQ_THM]>>
        fs[state_component_equality,call_env_def]>>
        fs[pop_env_perm]>>fs[set_var_perm])
      >-
        (full_case_tac>>fs[]
        >-
          (perm_assum_tac>>
          qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[])
        >>
        PairCases_on`x''`>>fs[]>>
        qpat_assum`A=(res,rst)`mp_tac>>
        ntac 2 (IF_CASES_TAC>>fs[])>>
        rw[]>>
        Cases_on`res = SOME Error`>>fs[]>>
        last_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
        first_x_assum(qspec_then`perm'`assume_tac)>>fs[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
        `(λn. perm'' n) = perm''` by fs[FUN_EQ_THM]>>
        fs[state_component_equality,call_env_def]>>
        fs[set_var_perm])
      >>
        perm_assum_tac>>
        Cases_on`handler`>>TRY(PairCases_on`x''`)>>
        fs[push_env_def,env_to_list_def,LET_THM,dec_clock_def]>>
        qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[]));

(*Monotonicity*)
val every_var_inst_mono = store_thm("every_var_inst_mono",``
  ∀P inst Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_inst P inst
  ⇒
  every_var_inst Q inst``,
  ho_match_mp_tac every_var_inst_ind>>rw[every_var_inst_def]>>
  Cases_on`ri`>>fs[every_var_imm_def])

val every_var_exp_mono = store_thm("every_var_exp_mono",``
  ∀P exp Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_exp P exp
  ⇒
  every_var_exp Q exp``,
  ho_match_mp_tac every_var_exp_ind>>rw[every_var_exp_def]>>
  fs[EVERY_MEM])

val every_name_mono = store_thm("every_name_mono",``
  ∀P names Q.
  (∀x. P x ⇒ Q x) ∧
  every_name P names ⇒ every_name Q names``,
  rw[every_name_def]>>
  metis_tac[EVERY_MONOTONIC])

val every_var_mono = store_thm("every_var_mono",``
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_var P prog
  ⇒
  every_var Q prog``,
  ho_match_mp_tac every_var_ind>>rw[every_var_def]>>
  TRY(Cases_on`ret`>>fs[]>>PairCases_on`x`>>Cases_on`h`>>fs[]>>TRY(Cases_on`x`)>>fs[])>>
  TRY(Cases_on`r`>>fs[])>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  metis_tac[EVERY_MONOTONIC,every_var_inst_mono,every_var_exp_mono,every_name_mono])

(*Conjunct*)
val every_var_inst_conj = store_thm("every_var_inst_conj",``
  ∀P inst Q.
  every_var_inst P inst ∧ every_var_inst Q inst ⇔
  every_var_inst (λx. P x ∧ Q x) inst``,
  ho_match_mp_tac every_var_inst_ind>>rw[every_var_inst_def]>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  metis_tac[])

val every_var_exp_conj = store_thm("every_var_exp_conj",``
  ∀P exp Q.
  every_var_exp P exp ∧ every_var_exp Q exp ⇔
  every_var_exp (λx. P x ∧ Q x) exp``,
  ho_match_mp_tac every_var_exp_ind>>rw[every_var_exp_def]>>
  fs[EVERY_MEM]>>
  metis_tac[])

val every_name_conj = store_thm("every_name_conj",``
  ∀P names Q.
  every_name P names ∧ every_name Q names ⇔
  every_name (λx. P x ∧ Q x) names``,
  rw[every_name_def]>>
  metis_tac[EVERY_CONJ])

val every_var_conj = store_thm("every_var_conj",``
  ∀P prog Q.
  every_var P prog  ∧ every_var Q prog ⇔
  every_var (λx. P x ∧ Q x) prog``,
  ho_match_mp_tac every_var_ind>>rw[every_var_def]>>
  TRY(Cases_on`ret`>>fs[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>fs[])>>
  TRY(Cases_on`x`>>fs[])>>
  TRY(Cases_on`r`>>fs[])>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  TRY(metis_tac[EVERY_CONJ,every_var_inst_conj,every_var_exp_conj,every_name_conj]))

(*Similar lemmas about every_stack_var*)
val every_var_imp_every_stack_var = store_thm("every_var_imp_every_stack_var",``
  ∀P prog.
  every_var P prog ⇒ every_stack_var P prog``,
  ho_match_mp_tac every_stack_var_ind>>
  rw[every_stack_var_def,every_var_def]>>
  Cases_on`ret`>>
  Cases_on`h`>>fs[]>>
  PairCases_on`x`>>fs[]>>
  Cases_on`x'`>>Cases_on`r`>>fs[])

val every_stack_var_mono = store_thm("every_stack_var_mono",``
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_stack_var P prog
  ⇒
  every_stack_var Q prog``,
  ho_match_mp_tac every_stack_var_ind>>rw[every_stack_var_def]>>
  TRY(Cases_on`ret`>>fs[]>>PairCases_on`x`>>Cases_on`h`>>fs[]>>TRY(Cases_on`x`>>Cases_on`r`>>fs[]))>>
  metis_tac[every_name_mono])

val every_stack_var_conj = store_thm("every_stack_var_conj",``
  ∀P prog Q.
  every_stack_var P prog  ∧ every_stack_var Q prog ⇔
  every_stack_var (λx. P x ∧ Q x) prog``,
  ho_match_mp_tac every_stack_var_ind>>rw[every_stack_var_def]>>
  TRY(Cases_on`ret`>>fs[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>fs[])>>
  TRY(Cases_on`x`>>Cases_on`r`>>fs[])>>
  TRY(metis_tac[EVERY_CONJ,every_name_conj]))

(*Recursor for instructions since we use it a lot when flattening*)
val every_inst_def = Define`
  (every_inst P (Inst i) ⇔ P i) ∧
  (every_inst P (Seq p1 p2) ⇔ (every_inst P p1 ∧ every_inst P p2)) ∧
  (every_inst P (If cmp r1 ri c1 c2) ⇔ every_inst P c1 ∧ every_inst P c2) ∧
  (every_inst P (MustTerminate n p) ⇔ every_inst P p) ∧
  (every_inst P (Call ret dest args handler)
    ⇔ (case ret of
        NONE => T
      | SOME (n,names,ret_handler,l1,l2) => every_inst P ret_handler ∧
      (case handler of
        NONE => T
      | SOME (n,h,l1,l2) => every_inst P h))) ∧
  (every_inst P prog ⇔ T)`

(* Locals extend lemma *)
val locals_rel_def = Define`
  locals_rel temp (s:'a word_loc num_map) t ⇔ (∀x. x < temp ⇒ lookup x s = lookup x t)`

val locals_rel_word_exp = store_thm("locals_rel_word_exp",``
  ∀s exp w.
  every_var_exp (λx. x < temp) exp ∧
  word_exp s exp = SOME w ∧
  locals_rel temp s.locals loc ⇒
  word_exp (s with locals:=loc) exp = SOME w``,
  ho_match_mp_tac word_exp_ind>>rw[]>>
  fs[word_exp_def,every_var_exp_def,locals_rel_def]
  >-
    (every_case_tac>>
    res_tac>>fs[])
  >-
    (qpat_assum`A= SOME w` mp_tac>>full_case_tac>>fs[mem_load_def])
  >-
    (qpat_assum`A= SOME w` mp_tac>>
    LET_ELIM_TAC>>
    Cases_on`EVERY IS_SOME ws`>>fs[]>>
    `ws = ws'` by
      (unabbrev_all_tac>>
      fs[LIST_EQ,MAP_EQ_f,EVERY_MEM,MEM_MAP,IS_SOME_EXISTS]>>rw[]>>
      res_tac>>fs[])>>
    metis_tac[])
  >>
    every_case_tac>>res_tac>>fs[])

val locals_rel_get_vars  = store_thm("locals_rel_get_vars",``
  ∀ls vs.
  get_vars ls st = SOME vs ∧
  EVERY (λx. x < temp) ls ∧
  locals_rel temp st.locals loc ⇒
  get_vars ls (st with locals:= loc) = SOME vs``,
  Induct>>fs[get_vars_def]>>rw[]>>
  qpat_assum`A=SOME vs` mp_tac>>ntac 2 full_case_tac>>rw[]>>
  res_tac>>fs[get_var_def,locals_rel_def]>>
  res_tac>>
  fs[])

val locals_rel_alist_insert = store_thm("locals_rel_alist_insert",``
  ∀ls vs s t.
  locals_rel temp s t ∧
  EVERY (λx. x < temp) ls ⇒
  locals_rel temp (alist_insert ls vs s) (alist_insert ls vs t)``,
  ho_match_mp_tac alist_insert_ind>>fs[alist_insert_def,locals_rel_def]>>
  rw[]>>
  Cases_on`x'=ls`>>fs[lookup_insert])

val locals_rel_get_var = store_thm("locals_rel_get_var",``
  r < temp ∧
  get_var r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var r (st with locals:=loc) = SOME x``,
  fs[get_var_def,locals_rel_def]>>
  metis_tac[])

val locals_rel_get_var_imm = store_thm("locals_rel_get_var_imm",``
  every_var_imm (λx.x<temp) r ∧
  get_var_imm r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var_imm r (st with locals:=loc) = SOME x``,
  Cases_on`r`>>fs[get_var_imm_def,every_var_imm_def]>>
  metis_tac[locals_rel_get_var])

val locals_rel_set_var = prove(``
  ∀n s t.
  locals_rel temp s t ⇒
  locals_rel temp (insert n v s) (insert n v t)``,
  rw[]>>fs[locals_rel_def,lookup_insert])

val locals_rel_cut_env = prove(``
  locals_rel temp loc loc' ∧
  every_name (λx. x < temp) names ∧
  cut_env names loc = SOME x ⇒
  cut_env names loc' = SOME x``,
  rw[locals_rel_def,cut_env_def,SUBSET_DEF,every_name_def]>>
  fs[EVERY_MEM,toAList_domain]
  >- metis_tac[domain_lookup]
  >>
  fs[lookup_inter]>>rw[]>>every_case_tac>>
  fs[domain_lookup]>>res_tac>>
  metis_tac[option_CLAUSES])

(*Extra temporaries not mentioned in program
  do not affect evaluation*)

val srestac = qpat_assum`A=res`sym_sub_tac>>fs[]

val locals_rel_evaluate_thm = store_thm("locals_rel_evaluate_thm",``
  ∀prog st res rst loc temp.
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ∧
  every_var (λx.x < temp) prog ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  case res of
    NONE => locals_rel temp rst.locals loc'
  |  SOME _ => rst.locals = loc'``,
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>
  fs[evaluate_def,LET_THM]
  >-
    (srestac>>metis_tac[])
  >-
    (qpat_assum `A = (res,rst)` mp_tac>> ntac 2 full_case_tac>>
    fs[every_var_def]>>
    imp_res_tac locals_rel_get_vars>>
    fs[set_vars_def]>>imp_res_tac locals_rel_alist_insert>>
    fs[state_component_equality]>>
    rw[]>>fs[]>>metis_tac[])
  >-
    (Cases_on`i`>>fs[inst_def,every_var_def,every_var_inst_def]
    >-
      (srestac>>metis_tac[])
    >-
      (fs[assign_def,word_exp_def,set_var_def]>>
      imp_res_tac locals_rel_set_var>>
      fs[state_component_equality]>>
      srestac>>metis_tac[])
    >-
      (Cases_on`a`>>fs[assign_def]>>
      qpat_assum`A=(res,rst)` mp_tac>>
      qpat_abbrev_tac`A = word_exp B C`>>
      Cases_on`A`>>fs[markerTheory.Abbrev_def]>>rw[]>>
      pop_assum (assume_tac o SYM)>>
      imp_res_tac locals_rel_word_exp>>
      fs[every_var_exp_def,every_var_inst_def]>>
      TRY(Cases_on`r`)>>rfs[every_var_exp_def,every_var_imm_def]>>
      fs[set_var_def]>>
      metis_tac[locals_rel_set_var])
    >>
      Cases_on`a`>>Cases_on`m`>>fs[assign_def]>>
      qpat_assum`A=(res,rst)` mp_tac>>
      qpat_abbrev_tac`A = word_exp B C`>>
      Cases_on`A`>>fs[markerTheory.Abbrev_def]>>
      TRY (ntac 2 full_case_tac>>fs[])>>
      rw[]>>
      qpat_assum `SOME x = A` (assume_tac o SYM)>>
      imp_res_tac locals_rel_word_exp>>
      imp_res_tac locals_rel_get_var>>
      fs[every_var_exp_def,every_var_inst_def]>>
      rfs[every_var_exp_def,every_var_imm_def]>>
      fs[set_var_def,mem_store_def,mem_load_def]>>
      fs[state_component_equality]>>
      metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>fs[every_var_def]>>
    rfs[state_component_equality,set_var_def]>>
    qpat_assum`A=rst.locals` sym_sub_tac>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>fs[set_var_def,state_component_equality,set_var_def]>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>fs[every_var_def]>>
    rfs[state_component_equality,set_store_def]>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>fs[every_var_def]>>
    imp_res_tac locals_rel_get_var>>fs[]>>
    rfs[state_component_equality,mem_store_def]>>
    metis_tac[])
  >-
    (fs[PULL_FORALL,GSYM AND_IMP_INTRO]>>
    qpat_assum`A=(res,rst)` mp_tac>>
    IF_CASES_TAC>>simp[]>>
    split_pair_tac>>simp[]>>
    IF_CASES_TAC>>simp[]>>
    first_x_assum(qspec_then`p` mp_tac)>>
    simp[prog_size_def]>>rw[]>>fs[every_var_def]>>
    res_tac>>fs[]>>
    first_x_assum(qspec_then`loc` mp_tac)>>
    pop_assum kall_tac>>
    simp[]>>strip_tac>>
    simp[]>>
    metis_tac[])
  >-
    (*Call*)
    (Cases_on`get_vars l st`>>fs[every_var_def]>>
    imp_res_tac locals_rel_get_vars>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code`>>
    TRY(PairCases_on`x'`)>>fs[]>>
    Cases_on`o'`>>fs[]
    >-(*Tail Call*)
      (fs[call_env_def,dec_clock_def]>>
      IF_CASES_TAC>>fs[state_component_equality,locals_rel_def]>>
      CASE_TAC>>fs[])
    >>
      PairCases_on`x'`>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      Cases_on`cut_env x'1' st.locals`>>fs[]>>
      imp_res_tac locals_rel_cut_env>>fs[]>>
      IF_CASES_TAC>-
        (fs[call_env_def,state_component_equality,locals_rel_def]>>
        CASE_TAC>>fs[])
      >>
      fs[]>>qpat_assum`A=(res,rst)` mp_tac>>
      qpat_abbrev_tac`st = call_env B C`>>
      qpat_abbrev_tac`st' = call_env B C`>>
      `st' = st''` by
        (unabbrev_all_tac>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        fs[call_env_def,push_env_def,dec_clock_def,push_env_def,LET_THM,env_to_list_def,state_component_equality])>>
      every_case_tac>>rw[]>>
      fs[state_component_equality,locals_rel_def])
  >-
    (fs[PULL_FORALL,GSYM AND_IMP_INTRO]>>Cases_on`evaluate (p,st)`>>fs[]>>
    first_assum(qspec_then`p` mp_tac)>>
    first_x_assum(qspec_then`p0` mp_tac)>>
    `q ≠ SOME Error` by (every_case_tac >> fs[])>>
    simp[prog_size_def]>>rw[]>>fs[every_var_def]>>res_tac>>
    simp[]>>IF_CASES_TAC>>fs[state_component_equality]>>
    res_tac>>
    first_x_assum(qspec_then`loc` assume_tac)>>rfs[locals_rel_def])
  >-
    (fs[PULL_FORALL,GSYM AND_IMP_INTRO]>>
    qpat_assum`A=(res,rst)`mp_tac >> ntac 4 (full_case_tac>>fs[])>>
    IF_CASES_TAC>>rw[]>>
    imp_res_tac locals_rel_get_var>>imp_res_tac locals_rel_get_var_imm>>
    fs[every_var_def]>>rfs[]
    >-
      (first_x_assum(qspec_then`p`mp_tac)>>fs[GSYM PULL_FORALL]>>
      discharge_hyps>- (fs[prog_size_def]>>DECIDE_TAC)>>strip_tac>>
      res_tac>>fs[])
    >>
      (first_x_assum(qspec_then`p0`mp_tac)>>fs[GSYM PULL_FORALL]>>
      discharge_hyps>- (fs[prog_size_def]>>DECIDE_TAC)>>strip_tac>>
      res_tac>>fs[]))
  >-
    (*alloc*)
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rfs[every_var_def]>>
    fs[alloc_def]>>qpat_assum`A=(res,rst)` mp_tac>>
    ntac 6 (full_case_tac>>fs[])>>rw[]>>
    imp_res_tac locals_rel_cut_env>>
    fs[]>>
    qpat_assum` A = SOME x'` mp_tac>>
    fs[push_env_def,set_store_def,LET_THM,env_to_list_def,gc_def]>>
    full_case_tac>>TRY(PairCases_on`x''`)>>TRY(PairCases_on`x''''`)>>
    fs[]>>full_case_tac>>fs[pop_env_def]>>rw[]>>
    fs[state_component_equality,locals_rel_def]>>
    CASE_TAC>>fs[call_env_def]>>
    CASE_TAC>>fs[call_env_def]>>
    qpat_assum`A=x''` sym_sub_tac>>fs[])
  >-
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rfs[every_var_def]>>
    fs[jump_exc_def,state_component_equality,locals_rel_def]>>
    metis_tac[])
  >-
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rfs[every_var_def]>>
    fs[call_env_def,state_component_equality,locals_rel_def])
  >-
    (IF_CASES_TAC>>fs[call_env_def,state_component_equality,dec_clock_def]>>
    srestac>>fs[]>>metis_tac[])
  >>
    (qpat_assum `A = (res,rst)` mp_tac>> ntac 5 full_case_tac>>
    fs[every_var_def]>>
    imp_res_tac locals_rel_get_var>>imp_res_tac locals_rel_cut_env>>
    fs[]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    Cases_on`res`>>fs[]))

val mem_list_rearrange = store_thm("mem_list_rearrange",``
  ∀ls x f. MEM x (list_rearrange f ls) ⇔ MEM x ls``,
  fs[MEM_EL]>>rw[wordSemTheory.list_rearrange_def]>>
  imp_res_tac BIJ_IFF_INV>>
  fs[BIJ_DEF,INJ_DEF,SURJ_DEF]>>
  rw[EQ_IMP_THM]>>fs[EL_GENLIST]
  >- metis_tac[]>>
  qexists_tac `g n`>>fs[])

val lookup_fromList2 = store_thm("lookup_fromList2",
  ``!l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE``,
  recInduct SNOC_INDUCT \\ rw []
  THEN1 (EVAL_TAC \\ fs [lookup_def])
  THEN1 (EVAL_TAC \\ fs [lookup_def])
  \\ fs [fromList2_def,FOLDL_SNOC]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [GSYM fromList2_def,FOLDL_SNOC]
  \\ fs [lookup_insert,lookup_fromList,DIV_LT_X]
  \\ `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ fs [FOLDL]
    \\ fs [MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])
  \\ fs [] \\ rw []
  \\ fs [GSYM DIV_LT_X,EL_SNOC]
  \\ fs [MULT_DIV,SNOC_APPEND,EL_LENGTH_APPEND,EVEN_MOD2,MOD_EQ_0]
  \\ TRY decide_tac
  \\ fs [DIV_LT_X]
  \\ `n = LENGTH l * 2 + 1` by decide_tac
  \\ fs [MOD_TIMES]);

val _ = export_theory();
