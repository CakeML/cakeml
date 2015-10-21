open preamble funBigStepTheory funBigStepEquivTheory bigClockTheory determTheory;
open terminationTheory

val _ = new_theory"funBigStepProps"

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   ffi.io_events ≼ ffi'.io_events ∧
   (IS_SOME ffi.final_event ⇒ ffi' = ffi)`,
  rw[evalPropsTheory.do_app_cases] >>
  fs[ffiTheory.call_FFI_def] >>
  every_case_tac >> fs[] >> rw[])

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀(s:'ffi state) e exp.
      s.ffi.io_events ≼ (FST (evaluate s e exp)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate s e exp)).ffi = s.ffi)) ∧
   (∀(s:'ffi state) e v pes errv.
      s.ffi.io_events ≼ (FST (evaluate_match s e v pes errv)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate_match s e v pes errv)).ffi = s.ffi))`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  rw[terminationTheory.evaluate_def] >>
  every_case_tac >> fs[] >>
  TRY (
    qcase_tac`op ≠ Opapp` >>
    imp_res_tac do_app_io_events_mono >>
    metis_tac[IS_PREFIX_TRANS] ) >>
  TRY (
    qcase_tac`op = Opapp` >>
    rfs[dec_clock_def] >>
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
  rw[evaluate_decs_def] >>
  every_case_tac >> fs[] >>
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
  rw[evaluate_tops_def] >>
  every_case_tac >> fs[] >>
  metis_tac[IS_PREFIX_TRANS,evaluate_decs_io_events_mono,FST])

val evaluate_tops_io_events_mono_imp = Q.store_thm("evaluate_tops_io_events_mono_imp",
  `∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     s.ffi.io_events ≼ s'.ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  metis_tac[PAIR,FST,evaluate_tops_io_events_mono])

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `evaluate s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)`,
  rw[] >>
  imp_res_tac functional_evaluate_list >>
  imp_res_tac add_to_counter >> rfs[] >>
  Cases_on`evaluate (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_list >>
  metis_tac[big_exp_determ,PAIR_EQ])

val list_result_eq_Rval = Q.store_thm("list_result_eq_Rval",
  `list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v`,
  Cases_on`r`>>rw[list_result_def,EQ_IMP_THM])

val list_result_eq_Rerr = Q.store_thm("list_result_eq_Rerr",
  `list_result r = Rerr e ⇔ r = Rerr e`,
  Cases_on`r`>>rw[list_result_def,EQ_IMP_THM])

val list_result_inj = Q.store_thm("list_result_inj",
  `list_result x = list_result y ⇒ x = y`,
  Cases_on`x`>>Cases_on`y`>>EVAL_TAC)

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1)`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def,LENGTH_NIL] >> rw[] >>
  every_case_tac >> fs[list_result_eq_Rval] >> rw[])

val evaluate_match_list_result = Q.store_thm("evaluate_match_list_result",
  `evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'`,
  Cases_on`r` >> rw[] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> fs[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]);

val evaluate_match_add_to_clock = Q.store_thm("evaluate_match_add_to_clock",
  `evaluate_match s e v p er = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_match (s with clock := s.clock + extra) e v p er =
   (s' with clock := s'.clock + extra,r)`,
  rw[] >>
  imp_res_tac evaluate_match_list_result >> rw[] >>
  imp_res_tac functional_evaluate_match >>
  imp_res_tac add_to_counter >> rfs[] >>
  fs[list_result_eq_Rerr] >> rfs[] >>
  simp[functional_evaluate_match]);

val evaluate_decs_add_to_clock = Q.store_thm("evaluate_decs_add_to_clock",
  `evaluate_decs m s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs m (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
  rw[] >>
  imp_res_tac functional_evaluate_decs >>
  imp_res_tac decs_add_to_counter >> rfs[] >>
  Cases_on`evaluate_decs m (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_decs >>
  metis_tac[decs_determ,PAIR_EQ])

val evaluate_tops_add_to_clock = Q.store_thm("evaluate_tops_add_to_clock",
  `evaluate_tops s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_tops (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
  rw[] >>
  imp_res_tac functional_evaluate_tops >>
  imp_res_tac prog_add_to_counter >> rfs[] >>
  Cases_on`evaluate_tops (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_tops >>
  metis_tac[prog_determ,PAIR_EQ])

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
  rw[evaluate_def,LET_THM] >>
  TRY (
    qcase_tac`op = Opapp` >>
    every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
    TRY(first_x_assum(qspec_then`extra`strip_assume_tac)>>rfs[]>>NO_TAC)>>
    cheat) >>
  every_case_tac >> fs[] >>
  imp_res_tac evaluate_add_to_clock >> fs[] >> rw[] >>
  imp_res_tac evaluate_match_add_to_clock >> fs[] >> rw[] >>
  imp_res_tac evaluate_io_events_mono_imp >> fs[] >> rw[] >>
  metis_tac[IS_PREFIX_TRANS,FST,PAIR,evaluate_io_events_mono])

val evaluate_decs_add_to_clock_io_events_mono = Q.store_thm("evaluate_decs_add_to_clock_io_events_mono",
  `∀m s e d.
    (FST(evaluate_decs m s e d)).ffi.io_events ≼
    (FST(evaluate_decs m (s with clock := s.clock + extra) e d)).ffi.io_events ∧
    (IS_SOME(FST(evaluate_decs m s e d)).ffi.final_event ⇒
     (FST(evaluate_decs m s e d)).ffi =
     (FST(evaluate_decs m (s with clock := s.clock + extra) e d)).ffi)`,
  ho_match_mp_tac evaluate_decs_ind >>
  rw[evaluate_decs_def,LET_THM] >>
  every_case_tac >> fs[] >>
  imp_res_tac evaluate_decs_add_to_clock >> fs[] >> rw[] >>
  imp_res_tac evaluate_decs_io_events_mono_imp >> fs[] >> rw[] >>
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
  rw[evaluate_tops_def] >>
  every_case_tac >> fs[] >>
  imp_res_tac evaluate_tops_add_to_clock >> fs[] >> rw[] >>
  imp_res_tac evaluate_tops_io_events_mono_imp >> fs[] >> rw[] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[IS_PREFIX_TRANS]) >>
  metis_tac[evaluate_decs_add_to_clock_io_events_mono,FST])

val with_clock_clock = Q.prove(
  `(s with clock := k).clock = k`,
  EVAL_TAC)
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
  rw[evaluate_prog_def] >>
  qabbrev_tac`ss = s with clock := k1` >>
  `∃s1 c r. evaluate_tops ss e p = (s1,c,r)` by metis_tac[PAIR] >>
  fs[LESS_EQ_EXISTS,Abbr`ss`] >>
  metis_tac[evaluate_tops_add_to_clock_io_events_mono,FST,with_clock_clock,with_clock_with_clock])

val _ = export_theory()
