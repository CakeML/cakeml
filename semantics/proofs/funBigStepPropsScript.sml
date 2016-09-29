open preamble funBigStepTheory funBigStepEquivTheory bigClockTheory determTheory;
open terminationTheory

val _ = new_theory"funBigStepProps"

val call_FFI_rel_def = Define `
  call_FFI_rel s1 s2 <=> ?n bytes t. call_FFI s1 n bytes = (s2,t)`;

val io_events_mono_def = Define`
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (IS_SOME s1.final_event ⇒ s2 = s1) ∧
    (s2.final_event = NONE ∧ s2.io_events = s1.io_events ⇒ s2 = s1)`;

val io_events_mono_refl = Q.store_thm("io_events_mono_refl[simp]",
  `io_events_mono ffi ffi`,
  rw[io_events_mono_def]);

val io_events_mono_trans = Q.store_thm("io_events_mono_trans",
  `io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3`,
  rw[io_events_mono_def]
  \\ metis_tac[IS_PREFIX_TRANS, IS_PREFIX_ANTISYM]);

val call_FFI_rel_io_events_mono = Q.store_thm("call_FFI_rel_io_events_mono",
  `∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2`,
  REWRITE_TAC[io_events_mono_def] \\
  ho_match_mp_tac RTC_INDUCT
  \\ simp[call_FFI_rel_def,ffiTheory.call_FFI_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[IS_PREFIX_APPEND]);

val do_app_call_FFI_rel = Q.store_thm("do_app_call_FFI_rel",
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'`,
  srw_tac[][evalPropsTheory.do_app_cases] >> rw[] >>
  match_mp_tac RTC_SUBSET >> rw[call_FFI_rel_def] >>
  metis_tac[]);

val evaluate_call_FFI_rel = Q.store_thm("evaluate_call_FFI_rel",
  `(∀(s:'ffi state) e exp.
      RTC call_FFI_rel s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      RTC call_FFI_rel s.ffi (FST (evaluate_match s e v pes errv)).ffi)`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  TRY (
    rename1`op ≠ Opapp` >>
    imp_res_tac do_app_call_FFI_rel >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  TRY (
    rename1`op = Opapp` >>
    rev_full_simp_tac(srw_ss())[dec_clock_def] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def,FST])

val evaluate_call_FFI_rel_imp = Q.store_thm("evaluate_call_FFI_rel_imp",
  `(∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi)`,
  metis_tac[PAIR,FST,evaluate_call_FFI_rel])

val evaluate_decs_call_FFI_rel = Q.prove(
  `∀mn s e d.
     RTC call_FFI_rel s.ffi (FST (evaluate_decs mn s e d)).ffi`,
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,evaluate_call_FFI_rel,FST]);

val evaluate_decs_call_FFI_rel_imp = Q.store_thm("evaluate_decs_call_FFI_rel_imp",
  `∀m s e p s' r.
     evaluate_decs m s e p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi`,
  metis_tac[PAIR,FST,evaluate_decs_call_FFI_rel])

val evaluate_tops_call_FFI_rel = Q.prove(
  `∀s e p.
     RTC call_FFI_rel s.ffi (FST (evaluate_tops s e p)).ffi`,
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,evaluate_decs_call_FFI_rel,FST])

val evaluate_tops_call_FFI_rel_imp = Q.store_thm("evaluate_tops_call_FFI_rel_imp",
  `∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi`,
  metis_tac[PAIR,FST,evaluate_tops_call_FFI_rel])

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'`,
  metis_tac[do_app_call_FFI_rel,call_FFI_rel_io_events_mono])

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀(s:'ffi state) e exp.
      io_events_mono s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      io_events_mono s.ffi (FST (evaluate_match s e v pes errv)).ffi)`,
  metis_tac[evaluate_call_FFI_rel,call_FFI_rel_io_events_mono]);

val evaluate_io_events_mono_imp = Q.store_thm("evaluate_io_events_mono_imp",
  `(∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      io_events_mono s.ffi s'.ffi)`,
  metis_tac[PAIR,FST,evaluate_io_events_mono])

val evaluate_decs_io_events_mono = Q.prove(
  `∀mn s e d.
     io_events_mono s.ffi (FST (evaluate_decs mn s e d)).ffi`,
  metis_tac[evaluate_decs_call_FFI_rel,call_FFI_rel_io_events_mono]);

val evaluate_decs_io_events_mono_imp = Q.store_thm("evaluate_decs_io_events_mono_imp",
  `∀m s e p s' r.
     evaluate_decs m s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi`,
  metis_tac[PAIR,FST,evaluate_decs_io_events_mono])

val evaluate_tops_io_events_mono = Q.prove(
  `∀s e p.
     io_events_mono s.ffi (FST (evaluate_tops s e p)).ffi`,
  metis_tac[evaluate_tops_call_FFI_rel,call_FFI_rel_io_events_mono])

val evaluate_tops_io_events_mono_imp = Q.store_thm("evaluate_tops_io_events_mono_imp",
  `∀s e p s' r.
     evaluate_tops s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi`,
  metis_tac[PAIR,FST,evaluate_tops_io_events_mono])

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `evaluate s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)`,
  srw_tac[][] >>
  imp_res_tac functional_evaluate_list >>
  imp_res_tac add_to_counter >> rev_full_simp_tac(srw_ss())[] >>
  Cases_on`evaluate (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_list >>
  metis_tac[big_exp_determ,PAIR_EQ])

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

val evaluate_match_list_result = Q.store_thm("evaluate_match_list_result",
  `evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'`,
  Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]);

val evaluate_match_add_to_clock = Q.store_thm("evaluate_match_add_to_clock",
  `evaluate_match s e v p er = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_match (s with clock := s.clock + extra) e v p er =
   (s' with clock := s'.clock + extra,r)`,
  srw_tac[][] >>
  imp_res_tac evaluate_match_list_result >> srw_tac[][] >>
  imp_res_tac functional_evaluate_match >>
  imp_res_tac add_to_counter >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[list_result_eq_Rerr] >> rev_full_simp_tac(srw_ss())[] >>
  simp[functional_evaluate_match]);

val evaluate_decs_add_to_clock = Q.store_thm("evaluate_decs_add_to_clock",
  `evaluate_decs m s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs m (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
  srw_tac[][] >>
  imp_res_tac functional_evaluate_decs >>
  imp_res_tac decs_add_to_counter >> rev_full_simp_tac(srw_ss())[] >>
  Cases_on`evaluate_decs m (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_decs >>
  metis_tac[decs_determ,PAIR_EQ])

val evaluate_tops_add_to_clock = Q.store_thm("evaluate_tops_add_to_clock",
  `evaluate_tops s e p = (s',c,r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_tops (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,c,r)`,
  srw_tac[][] >>
  imp_res_tac functional_evaluate_tops >>
  imp_res_tac prog_add_to_counter >> rev_full_simp_tac(srw_ss())[] >>
  Cases_on`evaluate_tops (s with clock := s.clock + extra) e p` >>
  Cases_on`r'` >>
  imp_res_tac functional_evaluate_tops >>
  metis_tac[prog_determ,PAIR_EQ])

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)
val lemma = DECIDE``x ≠ 0n ⇒ x - 1 + y = x + y - 1``

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀(s:'ffi state) e d extra.
     io_events_mono (FST(evaluate s e d)).ffi
     (FST(evaluate (s with clock := s.clock + extra) e d)).ffi) ∧
   (∀(s:'ffi state) e v d er extra.
     io_events_mono (FST(evaluate_match s e v d er)).ffi
     (FST(evaluate_match (s with clock := s.clock + extra) e v d er)).ffi)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`op = Opapp` >>
    every_case_tac >> full_simp_tac(srw_ss())[dec_clock_def] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    TRY(first_x_assum(qspec_then`extra`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>NO_TAC)>>
    imp_res_tac evaluate_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac do_app_io_events_mono >>
    metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,io_events_mono_trans,lemma] ) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_match_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  metis_tac[io_events_mono_trans,FST,PAIR,evaluate_io_events_mono])

val evaluate_decs_add_to_clock_io_events_mono = Q.store_thm("evaluate_decs_add_to_clock_io_events_mono",
  `∀m s e d.
    io_events_mono
    (FST(evaluate_decs m s e d)).ffi
    (FST(evaluate_decs m (s with clock := s.clock + extra) e d)).ffi`,
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def,LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_decs_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[io_events_mono_trans]) >>
  metis_tac[evaluate_add_to_clock_io_events_mono,FST])

val evaluate_tops_add_to_clock_io_events_mono = Q.store_thm("evaluate_tops_add_to_clock_io_events_mono",
  `∀s e p extra.
   io_events_mono (FST(evaluate_tops s e p)).ffi
   (FST(evaluate_tops (s with clock := s.clock + extra) e p)).ffi`,
  ho_match_mp_tac evaluate_tops_ind >>
  srw_tac[][evaluate_tops_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_tops_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_tops_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(
    last_x_assum(qspec_then`extra`mp_tac) >> simp[] >>
    metis_tac[io_events_mono_trans]) >>
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
    io_events_mono
    (FST (evaluate_prog (s with clock := k1) e p)).ffi
    (FST (evaluate_prog (s with clock := k2) e p)).ffi`,
  srw_tac[][evaluate_prog_def] >>
  qabbrev_tac`ss = s with clock := k1` >>
  `∃s1 c r. evaluate_tops ss e p = (s1,c,r)` by metis_tac[PAIR] >>
  full_simp_tac(srw_ss())[LESS_EQ_EXISTS,Abbr`ss`] >>
  metis_tac[evaluate_tops_add_to_clock_io_events_mono,FST,with_clock_clock,with_clock_with_clock])

val _ = export_theory()
