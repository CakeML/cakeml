open preamble evaluateTheory;
open namespaceTheory namespacePropsTheory;
open terminationTheory
open semanticPrimitivesTheory;
open semanticPrimitivesPropsTheory;

val _ = new_theory"evaluateProps"

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

val io_events_mono_antisym = Q.store_thm("io_events_mono_antisym",
  `io_events_mono s1 s2 ∧ io_events_mono s2 s1 ⇒ s1 = s2`,
  rw[io_events_mono_def]
  \\ Cases_on`s1.final_event` \\ rfs[]
  \\ Cases_on`s2.final_event` \\ rfs[]
  \\ imp_res_tac IS_PREFIX_ANTISYM
  \\ rfs[]);

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
  srw_tac[][do_app_cases] >> rw[] >>
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

val evaluate_add_to_clock_lemma = Q.prove(
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

val evaluate_add_to_clock = save_thm("evaluate_add_to_clock",
  CONJUNCT1 evaluate_add_to_clock_lemma);
val evaluate_match_add_to_clock = save_thm("evaluate_match_add_to_clock",
  CONJUNCT2 evaluate_add_to_clock_lemma);

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

val evaluate_decs_nil = Q.store_thm("evaluate_decs_nil[simp]",
  `∀mn (s:'ffi state) env.
    evaluate_decs mn s env [] = (s,Rval <| v := nsEmpty; c := nsEmpty |>)`,
 rw [evaluate_decs_def]);

val evaluate_decs_cons = Q.store_thm ("evaluate_decs_cons",
 `∀mn (s:'ffi state) env d ds.
   evaluate_decs mn s env (d::ds) =
     case evaluate_decs mn s env [d] of
     | (s1, Rval env1) =>
      (case evaluate_decs mn s1 (extend_dec_env env1 env) ds of
       | (s2, r) => (s2, combine_dec_result env1 r)
       | err => err)
     | err => err`,
 Cases_on `ds`
 >> rw [evaluate_decs_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_decs _ _ _ _ = (s1,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]);

val evaluate_tops_nil = Q.store_thm("evaluate_tops_nil[simp]",
  `∀(s:'ffi state) env. evaluate_tops s env [] = (s,Rval <| v := nsEmpty; c := nsEmpty |>)`,
 rw [evaluate_tops_def]);

val evaluate_tops_cons = Q.store_thm ("evaluate_tops_cons",
 `∀(s:'ffi state) env top tops.
   evaluate_tops s env (top::tops) =
     case evaluate_tops s env [top] of
     | (s1, Rval env1) =>
      (case evaluate_tops s1 (extend_dec_env env1 env) tops of
       | (s2, r) => (s2, combine_dec_result env1 r)
       | err => err)
     | err => err`,
 Cases_on `tops`
 >> rw [evaluate_tops_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_tops _ _ _ = (s1,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]);

val evaluate_match_list_result = Q.store_thm("evaluate_match_list_result",
  `evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'`,
  Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]);

val evaluate_decs_add_to_clock = Q.store_thm("evaluate_decs_add_to_clock",
  `!m s e p s' r extra.
   evaluate_decs m s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs m (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)`,
  ho_match_mp_tac evaluate_decs_ind
  >> rw [evaluate_decs_def]
  >- (
    pop_assum mp_tac
    >> pop_assum mp_tac
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
    >> fs [combine_dec_result_def])
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
 `!s e p s' r extra.
   evaluate_tops s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_tops (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)`,
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   split_pair_case_tac
   >> fs []
   >> split_pair_case_tac
   >> fs []
   >> every_case_tac
   >> fs []
   >> rpt var_eq_tac
   >> simp []
   >> rfs [combine_dec_result_def]
   >> fs []
   >> Cases_on `r'`
   >> Cases_on `r''`
   >> simp []
   >> rfs []
   >> fs [])
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
   >> rfs []
   >> fs []
   >> rw []));

val add_lemma = Q.prove (
 `!(k:num) k'. ?extra. k = k' + extra ∨ k' = k + extra`,
 intLib.ARITH_TAC);

val with_clock_with_clock = Q.prove (
`((s with clock := x) with clock := y) = s with clock := y`,
 rw []);

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)

val tac1 =
  metis_tac[result_distinct,result_11,evaluate_tops_add_to_clock,
            error_result_11,error_result_distinct,option_nchotomy,
            abort_distinct,pair_CASES,FST,with_clock_ffi,
            PAIR_EQ,IS_SOME_EXISTS,SOME_11,NOT_SOME_NONE,SND,PAIR, add_lemma,
            state_component_equality, with_clock_with_clock]

val evaluate_prog_clock_determ = Q.store_thm ("evaluate_prog_clock_determ",
`!s e p s1 r1 s2 r2 k1 k2.
  evaluate_prog (s with clock := k1) e p = (s1,r1) ∧
  evaluate_prog (s with clock := k2) e p = (s2,r2)
  ⇒
  case (r1,r2) of
  | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
    T
  | (Rerr (Rabort Rtimeout_error), _) =>
    k1 < k2
  | (_, Rerr (Rabort Rtimeout_error)) =>
    k2 < k1
  | _ =>
    s1.ffi = s2.ffi ∧ r1 = r2`,
 rw []
 >> Cases_on `r2 = Rerr (Rabort Rtimeout_error)`
 >> Cases_on `r1 = Rerr (Rabort Rtimeout_error)`
 >> fs []
 >> fs []
 >> fs []
 >> rw []
 >- (
   `k2 < k1` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> fs [evaluate_prog_def]
   >> every_case_tac
   >> fs []
   >> `?extra. k2 = k1 + extra` by intLib.ARITH_TAC
   >> qpat_x_assum `evaluate_tops _ _ _ = _` mp_tac
   >> drule evaluate_tops_add_to_clock
   >> rw [])
 >- (
   `k1 < k2` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> fs [evaluate_prog_def]
   >> every_case_tac
   >> fs []
   >> `?extra. k1 = k2 + extra` by intLib.ARITH_TAC
   >> drule evaluate_tops_add_to_clock
   >> fs []
   >> qexists_tac `extra`
   >> simp [])
 >- (
   fs [evaluate_prog_def]
   >> qpat_x_assum `(if _ then _ else _) = _` mp_tac
   >> CASE_TAC
   >> rw []
   >> rw []
   >> qspecl_then [`k1`, `k2`] strip_assume_tac add_lemma
   >> var_eq_tac
   >| [
     drule evaluate_tops_add_to_clock
       >> simp []
       >> disch_then (qspec_then `extra` mp_tac)
       >> rw [],
     qpat_x_assum `evaluate_tops _ _ _ = _` mp_tac
       >> drule evaluate_tops_add_to_clock
       >> simp []
       >> disch_then (qspec_then `extra` mp_tac)
       >> rw []]
   >> every_case_tac
   >> fs []
   >> rw []));

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
  EVAL_TAC);

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
  `∃s1 r. evaluate_tops ss e p = (s1,r)` by metis_tac[PAIR] >>
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
 `!mn st env ds st' r.
  evaluate_decs mn st env ds = (st',r)
  ⇒
  st.defined_mods = st'.defined_mods`,
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> every_case_tac
 >> fs []
 >> rw []
 >> metis_tac [evaluate_state_unchanged]);

val evaluate_ffi_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate s''' env' exp' = (s'',r') ∧
   s'''.ffi = s'.ffi ∧ s''.ffi = s.ffi
   ⇒ s'.ffi = s.ffi`,
  rw[] \\
  imp_res_tac evaluate_io_events_mono_imp \\ fs[] \\
  metis_tac[io_events_mono_antisym]);

val evaluate_match_ffi_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate_match s' env' v pes errv  = (s'',r') ∧
   s''.ffi = s.ffi ⇒ s'.ffi = s.ffi`,
  rw[] \\
  imp_res_tac evaluate_io_events_mono_imp \\ fs[] \\
  metis_tac[io_events_mono_antisym]);

val result_CASE_fst_cong = Q.prove(
  `result_CASE r (λa. (c,f a)) (λb. (c,g b)) =
   (c, result_CASE r (λa. f a) (λb. g b))`,
  Cases_on`r` \\ fs[]);

val option_CASE_fst_cong = Q.prove(
  `option_CASE r (c,f) (λb. (c,g b)) =
   (c, option_CASE r f (λb. g b))`,
  Cases_on`r` \\ fs[]);

val evaluate_state_const = CONJUNCT1 evaluate_state_unchanged

val evaluate_ffi_intro = Q.store_thm("evaluate_ffi_intro",`
  (∀(s:'a state) env e s' r.
     evaluate s env e = (s',r) ∧
     s'.ffi = s.ffi ∧ s.ffi.final_event = NONE
     ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs
       ⇒
       evaluate t env e = (t with <| clock := s'.clock; refs := s'.refs |>, r)) ∧
  (∀(s:'a state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ∧
     s'.ffi = s.ffi ∧ s.ffi.final_event = NONE
     ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs
       ⇒
       evaluate_match t env v pes errv = (t with <| clock := s'.clock; refs := s'.refs |>, r))`,
  ho_match_mp_tac evaluate_ind
  \\ rw[]
  >- ( rfs[evaluate_def] \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[result_CASE_fst_cong]
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_abbrev_tac`evaluate t1 _ (_::_) = _`
    \\ rfs[]
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def] \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[]
    \\ first_x_assum(qspec_then`t`mp_tac) \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_match_ffi_sandwich]
    \\ fs[] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate_match t1`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- fs[state_component_equality]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC
    \\ fs[option_CASE_fst_cong,result_CASE_fst_cong] )
  >- (
    rfs[evaluate_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      \\ TOP_CASE_TAC \\ fs[]
      >- ( strip_tac \\ rveq \\ fs[] )
      \\ strip_tac \\ fs[]
      \\ rename1`evaluate (dec_clock s1) _ _ = _`
      \\ `s1.ffi = s.ffi`
      by (
        imp_res_tac evaluate_ffi_sandwich
        \\ rfs[dec_clock_def] )
      \\ fs[]
      \\ rfs[dec_clock_def] \\ fs[]
      \\ qmatch_goalsub_abbrev_tac`evaluate t1 _ [_]`
      \\ first_x_assum(qspec_then`t1`mp_tac)
      \\ fs[Abbr`t1`]
      \\ imp_res_tac evaluate_state_const \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq \\ rfs[]
      \\ imp_res_tac do_app_NONE_ffi
      \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ rveq \\ fs[]
    \\ imp_res_tac do_app_io_events_mono
    \\ imp_res_tac evaluate_io_events_mono_imp
    \\ imp_res_tac io_events_mono_antisym \\ fs[]
    \\ imp_res_tac do_app_SOME_ffi_same \\ fs[]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate t1 _ [_]`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate t1 _ [_]`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_match_ffi_sandwich]
    \\ fs[] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate_match t1`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate t1 _ [_]`
    \\ first_x_assum(qspec_then`t1`mp_tac)
    \\ simp[Abbr`t1`]
    \\ imp_res_tac evaluate_state_const \\ fs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ fs[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- rw[state_component_equality]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[state_component_equality] ))

val _ = export_theory();
