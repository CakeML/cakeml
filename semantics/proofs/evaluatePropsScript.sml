open preamble evaluateTheory;
open terminationTheory
open semanticPrimitivesPropsTheory;

val _ = new_theory"evaluateProps"

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   ffi.io_events ≼ ffi'.io_events ∧
   (IS_SOME ffi.final_event ⇒ ffi' = ffi)`,
  srw_tac[][do_app_cases] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][])

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀(s:'ffi state) e exp.
      s.ffi.io_events ≼ (FST (evaluate s e exp)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate s e exp)).ffi = s.ffi)) ∧
   (∀(s:'ffi state) e v pes errv.
      s.ffi.io_events ≼ (FST (evaluate_match s e v pes errv)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate_match s e v pes errv)).ffi = s.ffi))`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  TRY (
    rename1`op ≠ Opapp` >>
    imp_res_tac do_app_io_events_mono >>
    metis_tac[IS_PREFIX_TRANS] ) >>
  TRY (
    rename1`op = Opapp` >>
    rev_full_simp_tac(srw_ss())[dec_clock_def] >>
    metis_tac[IS_PREFIX_TRANS] ) >>
  metis_tac[IS_PREFIX_TRANS,FST])

val evaluate_io_events_mono_imp = Q.store_thm("evaluate_io_events_mono_imp",
  `(∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi))`,
  metis_tac[PAIR,FST,evaluate_io_events_mono])

val evaluate_decs_io_events_mono = Q.prove(
  `∀mn s e d.
     s.ffi.io_events ≼ (FST (evaluate_decs mn s e d)).ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ (FST (evaluate_decs mn s e d)).ffi = s.ffi)`,
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,evaluate_io_events_mono,FST]);

val evaluate_decs_io_events_mono_imp = Q.store_thm("evaluate_decs_io_events_mono_imp",
  `∀m s e p s' r.
     evaluate_decs m s e p = (s',r) ⇒
     s.ffi.io_events ≼ s'.ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  metis_tac[PAIR,FST,evaluate_decs_io_events_mono])

val evaluate_tops_io_events_mono = Q.prove(
  `∀s e p.
     s.ffi.io_events ≼ (FST (evaluate_tops s e p)).ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ (FST (evaluate_tops s e p)).ffi = s.ffi)`,
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,evaluate_decs_io_events_mono,FST])

val evaluate_tops_io_events_mono_imp = Q.store_thm("evaluate_tops_io_events_mono_imp",
  `∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     s.ffi.io_events ≼ s'.ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  metis_tac[PAIR,FST,evaluate_tops_io_events_mono]);

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `(!(s:'ffi state) env es s' r extra.
    evaluate s env es = (s',r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (s with clock := s.clock + extra) env es =
    (s' with clock := s'.clock + extra,r)) ∧
   (!(s:'ffi state) env v pes err_v s' r extra.
    evaluate_match s env v pes err_v = (s', r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate_match (s with clock := s.clock + extra) env v pes err_v =
      (s' with clock := s'.clock + extra,r))`,
 (* The proof is fragile about generated names, but I don't see how to make it
  * robust without significant effort *)
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >- (
   Cases_on `evaluate s env [e1]`
   >> Cases_on `r'`
   >> fs []
   >> Cases_on `evaluate q env (e2::es)`
   >> Cases_on `r'`
   >> fs []
   >> rw [])
 >- (
   Cases_on `evaluate s env [e]`
   >> Cases_on `r'`
   >> fs []
   >> rw [])
 >- (
   Cases_on `evaluate s env [e]`
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >> Cases_on `e'`
   >> fs []
   >> rw []
   >> fs [])
 >- (
   Cases_on `evaluate s env (REVERSE es)`
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >> CASE_TAC
   >> fs [])
 >- (
   CASE_TAC
   >> fs [])
 >- (
   Cases_on `evaluate s env (REVERSE es)`
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >- (
     every_case_tac
     >> fs []
     >> rfs [dec_clock_def]
     >> first_x_assum (qspec_then `extra` mp_tac)
     >> simp [])
   >- (
     fs []
     >> CASE_TAC
     >> fs []
     >> every_case_tac
     >> fs []
     >> rw []))
 >- (
   Cases_on `evaluate s env [e1]`
   >> fs []
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >> rw []
   >> CASE_TAC
   >> fs []
   >> every_case_tac
   >> fs [])
 >- (
   Cases_on `evaluate s env [e1]`
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >> every_case_tac
   >> fs []
   >> rw [])
 >- (
   Cases_on `evaluate s env [e]`
   >> Cases_on `r'`
   >> fs []
   >> rw [])
 >- (
   Cases_on `evaluate s env [e1]`
   >> Cases_on `r'`
   >> fs []
   >> rw []
   >> every_case_tac
   >> fs []
   >> rw [])
 >- (
   CASE_TAC
   >> fs []));

val list_result_eq_Rval = Q.store_thm("list_result_eq_Rval[simp]",
  `list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v`,
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM])

val list_result_eq_Rerr = Q.store_thm("list_result_eq_Rerr[simp]",
  `list_result r = Rerr e ⇔ r = Rerr e`,
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM])

val result_rel_list_result = Q.store_thm("result_rel_list_result[simp]",
  `result_rel (LIST_REL R) Q (list_result r1) (list_result r2) ⇔
   result_rel R Q r1 r2`,
  Cases_on`r1`>>srw_tac[][PULL_EXISTS]);

val list_result_inj = Q.store_thm("list_result_inj",
  `list_result x = list_result y ⇒ x = y`,
  Cases_on`x`>>Cases_on`y`>>EVAL_TAC)

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[list_result_eq_Rval] >> srw_tac[][])

val evaluate_nil = Q.store_thm("evaluate_nil[simp]",
  `∀(s:'ffi state) env. evaluate s env [] = (s,Rval [])`,
 rw [evaluate_def]);

val evaluate_sing = Q.store_thm("evaluate_sing",
  `∀(s:'ffi state) env e s' vs. evaluate s env [e] = (s',Rval vs) ⇒ ∃v. vs = [v]`,
 rw []
 >> imp_res_tac evaluate_length
 >> Cases_on `vs`
 >> fs []
 >> Cases_on `t`
 >> fs []);

val evaluate_cons = Q.store_thm ("evaluate_cons",
 `∀(s:'ffi state) env e es.
   evaluate s env (e::es) =
     case evaluate s env [e] of
     | (s', Rval vs) =>
      (case evaluate s' env es of
       | (s'', Rval vs') => (s'', Rval (vs++vs'))
       | err => err)
     | err => err`,
 Cases_on `es`
 >> rw [evaluate_def]
 >- every_case_tac
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate _ _ _ = (st',r)`
 >> Cases_on `r`
 >> simp []
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate _ _ (e'::es) = (st'',r)`
 >> Cases_on `r`
 >> simp []
 >> drule evaluate_sing
 >> rw []);

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[list_result_eq_Rval] >> srw_tac[][])

val evaluate_decs_nil = Q.store_thm("evaluate_decs_nil[simp]",
  `∀mn (s:'ffi state) env. evaluate_decs mn s env [] = (s,[],Rval [])`,
 rw [evaluate_decs_def]);

val evaluate_decs_cons = Q.store_thm ("evaluate_decs_cons",
 `∀mn (s:'ffi state) env d ds.
   evaluate_decs mn s env (d::ds) =
     case evaluate_decs mn s env [d] of
     | (s', ctors, Rval new_vals) =>
      (case evaluate_decs mn s' (extend_dec_env new_vals ctors env) ds of
       | (s'', ctors', r) => (s'', ctors'++ctors, combine_dec_result new_vals r)
       | err => err)
     | err => err`,
 Cases_on `ds`
 >> rw [evaluate_decs_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_decs _ _ _ _ = (s',ctors,r)`
 >> Cases_on `r`
 >> simp [semanticPrimitivesTheory.combine_dec_result_def]);

val evaluate_tops_nil = Q.store_thm("evaluate_tops_nil[simp]",
  `∀(s:'ffi state) env. evaluate_tops s env [] = (s,([],[]),Rval ([],[]))`,
 rw [evaluate_tops_def]);

val evaluate_tops_cons = Q.store_thm ("evaluate_tops_cons",
 `∀(s:'ffi state) env top tops.
   evaluate_tops s env (top::tops) =
     case evaluate_tops s env [top] of
     | (s', ctors, Rval (new_mods, new_vals)) =>
      (case evaluate_tops s' (extend_top_env new_mods new_vals ctors env) tops of
       | (s'', ctors', r) => (s'', merge_alist_mod_env ctors' ctors, combine_mod_result new_mods new_vals r)
       | err => err)
     | err => err`,
 Cases_on `tops`
 >> rw [evaluate_tops_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_tops _ _ _ = (s',ctors,r)`
 >> Cases_on `r`
 >> simp [semanticPrimitivesTheory.combine_mod_result_def]
 >> split_pair_case_tac
 >> simp []);

val evaluate_match_list_result = Q.store_thm("evaluate_match_list_result",
  `evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'`,
  Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]);

val evaluate_decs_add_to_clock = Q.store_thm("evaluate_decs_add_to_clock",
  `!m s e p s' c r extra.
   evaluate_decs m s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs m (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
  ho_match_mp_tac evaluate_decs_ind
  >> rw [evaluate_decs_def]
  >- (
    pop_assum mp_tac
    >> pop_assum mp_tac
    >> CASE_TAC
    >> CASE_TAC
    >> CASE_TAC
    >> fs []
    >> rw []
    >> fs []
    >> pop_assum mp_tac
    >> pop_assum mp_tac
    >> split_pair_case_tac
    >> rw []
    >> fs []
    >> Cases_on `r'`
    >> fs []
    >> Cases_on `e'`
    >> fs [semanticPrimitivesTheory.combine_dec_result_def])
  >- (
    every_case_tac
    >> fs []
    >> rw []
    >> imp_res_tac evaluate_add_to_clock
    >> fs []
    >> rw []
    >> fs []
    >> rw [])
  >> rw []);

val evaluate_tops_add_to_clock = Q.store_thm("evaluate_tops_add_to_clock",
 `!s e p s' c r extra.
   evaluate_tops s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_tops (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   pop_assum mp_tac
   >> pop_assum mp_tac
   >> split_pair_case_tac
   >> fs []
   >> CASE_TAC
   >> simp []
   >> fs []
   >- (
     CASE_TAC
     >> fs []
     >> split_pair_case_tac
     >> simp []
     >> rw []
     >> Cases_on `r''`
     >> fs [semanticPrimitivesTheory.combine_mod_result_def])
   >- (
     rw []
     >> fs []))
 >- (
   every_case_tac
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_decs_add_to_clock
   >> fs [])
 >- (
   every_case_tac
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_decs_add_to_clock
   >> fs []
   >> rw []));

  val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)
val lemma = DECIDE``x ≠ 0n ⇒ x - 1 + y = x + y - 1``

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀(s:'ffi state) e d extra.
     (FST(evaluate s e d)).ffi.io_events ≼
     (FST(evaluate (s with clock := s.clock + extra) e d)).ffi.io_events ∧
     (IS_SOME(FST(evaluate s e d)).ffi.final_event ⇒
      (FST(evaluate s e d)).ffi =
      (FST(evaluate (s with clock := s.clock + extra) e d)).ffi)) ∧
   (∀(s:'ffi state) e v d er extra.
     (FST(evaluate_match s e v d er)).ffi.io_events ≼
     (FST(evaluate_match (s with clock := s.clock + extra) e v d er)).ffi.io_events ∧
     (IS_SOME(FST(evaluate_match s e v d er)).ffi.final_event ⇒
      (FST(evaluate_match s e v d er)).ffi =
      (FST(evaluate_match (s with clock := s.clock + extra) e v d er)).ffi))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`op = Opapp` >>
    every_case_tac >> full_simp_tac(srw_ss())[dec_clock_def] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    TRY(first_x_assum(qspec_then`extra`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>NO_TAC)>>
    imp_res_tac evaluate_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac do_app_io_events_mono >>
    metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,IS_PREFIX_TRANS,lemma] ) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  metis_tac[IS_PREFIX_TRANS,FST,PAIR,evaluate_io_events_mono])

val evaluate_decs_add_to_clock_io_events_mono = Q.store_thm("evaluate_decs_add_to_clock_io_events_mono",
  `∀m s e d.
    (FST(evaluate_decs m s e d)).ffi.io_events ≼
    (FST(evaluate_decs m (s with clock := s.clock + extra) e d)).ffi.io_events ∧
    (IS_SOME(FST(evaluate_decs m s e d)).ffi.final_event ⇒
     (FST(evaluate_decs m s e d)).ffi =
     (FST(evaluate_decs m (s with clock := s.clock + extra) e d)).ffi)`,
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def,LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_decs_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[IS_PREFIX_TRANS]) >>
  metis_tac[evaluate_add_to_clock_io_events_mono,FST])

val evaluate_tops_add_to_clock_io_events_mono = Q.store_thm("evaluate_tops_add_to_clock_io_events_mono",
  `∀s e p extra.
   (FST(evaluate_tops s e p)).ffi.io_events ≼
   (FST(evaluate_tops (s with clock := s.clock + extra) e p)).ffi.io_events ∧
   (IS_SOME(FST(evaluate_tops s e p)).ffi.final_event ⇒
    (FST(evaluate_tops s e p)).ffi =
    (FST(evaluate_tops (s with clock := s.clock + extra) e p)).ffi)`,
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_tops_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_tops_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[IS_PREFIX_TRANS]) >>
  metis_tac[evaluate_decs_add_to_clock_io_events_mono,FST])

val with_clock_clock = Q.prove(
  `(s with clock := k).clock = k`,
  EVAL_TAC);

val with_clock_with_clock = Q.prove(
  `((s with clock := k1) with clock := k2) = s with clock := k2`,
  EVAL_TAC)

val evaluate_prog_ffi_mono_clock = Q.store_thm("evaluate_prog_ffi_mono_clock",
  `∀k1 k2 s e p.
    k1 ≤ k2 ⇒
    (FST (evaluate_prog (s with clock := k1) e p)).ffi.io_events ≼
    (FST (evaluate_prog (s with clock := k2) e p)).ffi.io_events ∧
    (IS_SOME (FST (evaluate_prog (s with clock := k1) e p)).ffi.final_event ⇒
      (FST (evaluate_prog (s with clock := k1) e p)).ffi =
      (FST (evaluate_prog (s with clock := k2) e p)).ffi)`,
  srw_tac[][evaluate_prog_def] >>
  qabbrev_tac`ss = s with clock := k1` >>
  `∃s1 c r. evaluate_tops ss e p = (s1,c,r)` by metis_tac[PAIR] >>
  full_simp_tac(srw_ss())[LESS_EQ_EXISTS,Abbr`ss`] >>
  metis_tac[evaluate_tops_add_to_clock_io_events_mono,FST,with_clock_clock,with_clock_with_clock])

val evaluate_state_unchanged = Q.store_thm ("evaluate_state_unchanged",
 `(!(st:'ffi state) env es st' r.
    evaluate st env es = (st', r)
    ⇒
    st'.defined_types = st.defined_types ∧
    st'.defined_mods = st.defined_mods) ∧
  (!(st:'ffi state) env v pes err_v st' r.
    evaluate_match st env v pes err_v = (st', r)
    ⇒
    st'.defined_types = st.defined_types ∧
    st'.defined_mods = st.defined_mods)`,
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def]);

val evaluate_decs_state_unchanged = Q.store_thm ("evaluate_decs_state_unchanged",
 `!mn st env ds st' new_ctors r.
  evaluate_decs mn st env ds = (st',new_ctors,r)
  ⇒
  st.defined_mods = st'.defined_mods`,
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> every_case_tac
 >> fs []
 >> rw []
 >> metis_tac [evaluate_state_unchanged]);

val _ = export_theory();
