(*
  Properties of the operational semantics.
*)

open preamble evaluateTheory
     namespaceTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory;
open terminationTheory

val _ = new_theory"evaluateProps";

Theorem call_FFI_LENGTH
  `(call_FFI st index conf x = FFI_return new_st new_bytes) ==>
    (LENGTH x = LENGTH new_bytes)`
  (fs[ffiTheory.call_FFI_def] \\ every_case_tac \\ rw[] \\ fs[LENGTH_MAP]);

val call_FFI_rel_def = Define `
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t`;

Theorem call_FFI_rel_consts
  `call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)`
  (rw[call_FFI_rel_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ fs[CaseEq"bool",CaseEq"oracle_result"]
  \\ rw[]);

Theorem RTC_call_FFI_rel_consts
  `∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)`
  (once_rewrite_tac[EQ_SYM_EQ]
  \\ match_mp_tac RTC_lifts_equalities
  \\ rw[call_FFI_rel_consts]);

val dest_IO_event_def = Define`
  dest_IO_event (IO_event s c b) = (s,c,b)`;
val _ = export_rewrites["dest_IO_event_def"];

val io_events_mono_def = Define`
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)`;

Theorem io_events_mono_refl[simp]
  `io_events_mono ffi ffi`
  (rw[io_events_mono_def]);

Theorem io_events_mono_trans
  `io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3`
  (rw[io_events_mono_def]
  \\ metis_tac[IS_PREFIX_TRANS, IS_PREFIX_ANTISYM]);

Theorem io_events_mono_antisym
  `io_events_mono s1 s2 ∧ io_events_mono s2 s1 ⇒ s1 = s2`
  (rw[io_events_mono_def]
  \\ imp_res_tac IS_PREFIX_ANTISYM
  \\ rfs[]);

Theorem call_FFI_rel_io_events_mono
  `∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2`
  (REWRITE_TAC[io_events_mono_def] \\
  ho_match_mp_tac RTC_INDUCT
  \\ simp[call_FFI_rel_def,ffiTheory.call_FFI_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[IS_PREFIX_APPEND]);

Theorem do_app_call_FFI_rel
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'`
  (srw_tac[][do_app_cases] >> rw[] >>
  FULL_CASE_TAC
  >- (match_mp_tac RTC_SUBSET >> rw[call_FFI_rel_def] >> fs[] >> every_case_tac
      >> fs[] >> metis_tac[])
  >- fs[]);

Theorem evaluate_call_FFI_rel
  `(∀(s:'ffi state) e exp.
      RTC call_FFI_rel s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      RTC call_FFI_rel s.ffi (FST (evaluate_match s e v pes errv)).ffi) ∧
   (∀(s:'ffi state) e ds.
      RTC call_FFI_rel s.ffi (FST (evaluate_decs s e ds)).ffi)`
  (ho_match_mp_tac terminationTheory.full_evaluate_ind >>
  srw_tac[][terminationTheory.full_evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  TRY (
    rename1`op ≠ Opapp` >>
    imp_res_tac do_app_call_FFI_rel >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  TRY (
    rename1`op = Opapp` >>
    rev_full_simp_tac(srw_ss())[dec_clock_def] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  rfs [] >> fs [dec_clock_def] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,FST]);

Theorem evaluate_call_FFI_rel_imp
  `(∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e p s' r.
      evaluate_decs s e p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi)`
  (metis_tac[PAIR,FST,evaluate_call_FFI_rel]);

Theorem evaluate_decs_call_FFI_rel_imp
  `∀s e p s' r.
     evaluate_decs s e p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi`
  (metis_tac [evaluate_call_FFI_rel_imp]);

Theorem do_app_io_events_mono
  `do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'`
  (metis_tac[do_app_call_FFI_rel,call_FFI_rel_io_events_mono])

Theorem evaluate_io_events_mono
  `(∀(s:'ffi state) e exp.
      io_events_mono s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      io_events_mono s.ffi (FST (evaluate_match s e v pes errv)).ffi) ∧
   (∀s e d.
      io_events_mono s.ffi (FST (evaluate_decs s e d)).ffi)`
  (metis_tac[evaluate_call_FFI_rel,call_FFI_rel_io_events_mono]);

Theorem evaluate_io_events_mono_imp
  `(∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e p s' r.
     evaluate_decs s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi)`
  (metis_tac[PAIR,FST,evaluate_io_events_mono])

Theorem evaluate_decs_io_events_mono_imp
  `∀s e p s' r.
     evaluate_decs s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi`
  (metis_tac[evaluate_io_events_mono_imp])

val is_clock_io_mono_def = Define
  `is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ (!clk. case f (s with clock := clk) of (s'', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))`;

Theorem is_clock_io_mono_return
  `is_clock_io_mono (\s. (s,Rval r)) s`
  (fs [is_clock_io_mono_def])

Theorem is_clock_io_mono_err
  `is_clock_io_mono (\s. (s,Rerr r)) s`
  (fs [is_clock_io_mono_def])

Theorem pair_CASE_eq_forall
  `(case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)`
  (Cases_on `x` \\ fs []);

Theorem is_clock_io_mono_bind
  `is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s`
  (fs [is_clock_io_mono_def]
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC, CASE_TAC])
  \\ fs []
  \\ conj_tac \\ (TRY (irule io_events_mono_trans \\ metis_tac []))
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC, CASE_TAC])
  \\ fs [pair_CASE_eq_forall]
  \\ FIRST_X_ASSUM drule
  \\ rpt DISCH_TAC
  \\ fs []
  (* many cases *)
  \\ Cases_on (`SND (f s) = Rerr (Rabort Rtimeout_error)`)
  \\ Cases_on (`SND (f (s with clock := clk)) = Rerr (Rabort Rtimeout_error)`)
  \\ rpt (FIRST (map CHANGED_TAC [DISCH_TAC, fs [], rfs [], rveq]))
  \\ TRY (irule io_events_mono_trans \\ metis_tac [])
  (* back to one case *)
  \\ FIRST_X_ASSUM drule
  \\ rpt (FIRST (map CHANGED_TAC [DISCH_TAC, fs [], rfs [], rveq,
        fs [EQ_IMP_THM]])));

Theorem is_clock_io_mono_check
  `(~ (s.clock = 0) ==> is_clock_io_mono f (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f (dec_clock s)) s`
  (fs [is_clock_io_mono_def, dec_clock_def]
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ fs [pair_CASE_eq_forall]
  \\ FIRST_X_ASSUM drule
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ Cases_on `r' = Rerr (Rabort Rtimeout_error)` \\ fs []);

Theorem is_clock_io_mono_refs_lemma
  `is_clock_io_mono (\s'. f (s.refs) s') s
    ==> is_clock_io_mono (\s'. f (s'.refs) s') s`
  (fs [is_clock_io_mono_def]);

Theorem is_clock_io_mono_do_app
  `is_clock_io_mono (\st'. case do_app (st.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) => (st' with <|refs := refs; ffi := ffi|>,
        list_result r)) st`
  (fs [is_clock_io_mono_def]
  \\ rpt (CASE_TAC ORELSE CHANGED_TAC (fs []) ORELSE strip_tac)
  \\ metis_tac [do_app_io_events_mono]);

Theorem is_clock_io_mono_evaluate
  `(!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s)`
  (ho_match_mp_tac full_evaluate_ind
  \\ rpt strip_tac \\ fs [full_evaluate_def,combine_dec_result_def]
  \\ TRY (fs [is_clock_io_mono_def] \\ NO_TAC)
  \\ TRY (CASE_TAC \\ fs [is_clock_io_mono_def] \\ NO_TAC)
  \\ rpt (FIRST ([strip_tac] @ map ho_match_mp_tac [is_clock_io_mono_bind,
        is_clock_io_mono_check]
    @ [CHANGED_TAC (fs [is_clock_io_mono_return, is_clock_io_mono_err,
            is_clock_io_mono_do_app]),
        CASE_TAC,
        CHANGED_TAC (ho_match_mp_tac is_clock_io_mono_refs_lemma)]))
  \\ fs [full_evaluate_def,combine_dec_result_def]);

Theorem is_clock_io_mono_evaluate_decs
  `!s e p. is_clock_io_mono (\s. evaluate_decs s e p) s`
  (fs [is_clock_io_mono_evaluate]);

Theorem is_clock_io_mono_extra
  `(!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r)`
  (DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ rpt DISCH_TAC
  \\ rpt (CHANGED_TAC (fs [semanticPrimitivesPropsTheory.with_same_clock])));

Theorem is_clock_io_mono_extra_mono
  `(!s. is_clock_io_mono f s)
    ==> io_events_mono (FST(f s)).ffi
     (FST(f (s with clock := s.clock + extra))).ffi`
  (DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ CASE_TAC);

fun mk_extra_lemmas mp_rule monad_rule
  = BODY_CONJUNCTS monad_rule
    |> map (BETA_RULE o MATCH_MP mp_rule o Q.GEN `s`)
fun prove_extra mp_rule monad_rule
  = simp_tac bool_ss (mk_extra_lemmas mp_rule monad_rule)

Theorem evaluate_add_to_clock
  `!(s:'ffi state) env es s' r extra.
    evaluate s env es = (s',r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (s with clock := s.clock + extra) env es =
    (s' with clock := s'.clock + extra,r)`
  (prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate);

Theorem evaluate_match_add_to_clock
  `!(s:'ffi state) env v pes err_v s' r extra.
    evaluate_match s env v pes err_v = (s', r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate_match (s with clock := s.clock + extra) env v pes err_v =
      (s' with clock := s'.clock + extra,r)`
  (prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate);

Theorem list_result_eq_Rval[simp]
  `list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v`
  (Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM])

Theorem list_result_eq_Rerr[simp]
  `list_result r = Rerr e ⇔ r = Rerr e`
  (Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM])

Theorem result_rel_list_result[simp]
  `result_rel (LIST_REL R) Q (list_result r1) (list_result r2) ⇔
   result_rel R Q r1 r2`
  (Cases_on`r1`>>srw_tac[][PULL_EXISTS]);

Theorem list_result_inj
  `list_result x = list_result y ⇒ x = y`
  (Cases_on`x`>>Cases_on`y`>>EVAL_TAC)

Theorem evaluate_length
  `(∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T)`
  (ho_match_mp_tac full_evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[list_result_eq_Rval] >> srw_tac[][])

Theorem evaluate_nil[simp]
  `∀(s:'ffi state) env. evaluate s env [] = (s,Rval [])`
 (rw [evaluate_def]);

Theorem evaluate_sing
  `∀(s:'ffi state) env e s' vs. evaluate s env [e] = (s',Rval vs) ⇒ ∃v. vs = [v]`
 (rw []
 >> imp_res_tac evaluate_length
 >> Cases_on `vs`
 >> fs []
 >> Cases_on `t`
 >> fs []);

Theorem evaluate_cons:
  ∀(s:'ffi state) env e es.
   evaluate s env (e::es) =
     case evaluate s env [e] of
     | (s', Rval vs) =>
      (case evaluate s' env es of
       | (s'', Rval vs') => (s'', Rval (vs++vs'))
       | err => err)
     | err => err
Proof
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
 >> rw [] \\ rw[]);

Theorem evaluate_decs_nil[simp]
  `∀(s:'ffi state) env.
    evaluate_decs s env [] = (s,Rval <| v := nsEmpty; c := nsEmpty |>)`
 (rw [evaluate_decs_def]);

Theorem evaluate_decs_cons
 `∀(s:'ffi state) env d ds.
   evaluate_decs s env (d::ds) =
     case evaluate_decs s env [d] of
     | (s1, Rval env1) =>
      (case evaluate_decs s1 (extend_dec_env env1 env) ds of
       | (s2, r) => (s2, combine_dec_result env1 r)
       | err => err)
     | err => err`
 (Cases_on `ds`
 >> rw [evaluate_decs_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_decs _ _ _ = (s1,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]);

Theorem evaluate_match_list_result
  `evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'`
  (Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]);

val evaluate_decs_lemmas
  = BODY_CONJUNCTS is_clock_io_mono_evaluate_decs
    |> map (BETA_RULE o MATCH_MP is_clock_io_mono_extra o Q.GEN `s`)

Theorem evaluate_decs_add_to_clock
  `!s e p s' r extra.
   evaluate_decs s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)`
  (simp_tac bool_ss evaluate_decs_lemmas);

val add_lemma = Q.prove (
 `!(k:num) k'. ?extra. k = k' + extra ∨ k' = k + extra`,
 intLib.ARITH_TAC);

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC);

Theorem evaluate_decs_clock_determ
`!s e p s1 r1 s2 r2 k1 k2.
  evaluate_decs (s with clock := k1) e p = (s1,r1) ∧
  evaluate_decs (s with clock := k2) e p = (s2,r2)
  ⇒
  case (r1,r2) of
  | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
    T
  | (Rerr (Rabort Rtimeout_error), _) =>
    k1 < k2
  | (_, Rerr (Rabort Rtimeout_error)) =>
    k2 < k1
  | _ =>
    s1.ffi = s2.ffi ∧ r1 = r2`
 (rw []
 >> Cases_on `r2 = Rerr (Rabort Rtimeout_error)`
 >> Cases_on `r1 = Rerr (Rabort Rtimeout_error)`
 >> fs []
 >> fs []
 >> fs []
 >> rw []
 >- (
   `k2 < k1` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> `?extra. k2 = k1 + extra` by intLib.ARITH_TAC
   >> qpat_x_assum `evaluate_decs _ _ _ = _` mp_tac
   >> drule evaluate_decs_add_to_clock
   >> rw [])
 >- (
   `k1 < k2` suffices_by (every_case_tac >> fs [])
   >> CCONTR_TAC
   >> `?extra. k1 = k2 + extra` by intLib.ARITH_TAC
   >> drule evaluate_decs_add_to_clock
   >> fs []
   >> qexists_tac `extra`
   >> simp [])
 >- (
   every_case_tac >>
   fs [] >>
   rw [] >>
   `(?extra. k1 = k2 + extra) ∨ (?extra. k2 = k1 + extra)`
   by intLib.ARITH_TAC >>
   rw [] >>
   imp_res_tac evaluate_decs_add_to_clock >>
   fs [] >>
   rw []))

Theorem evaluate_add_to_clock_io_events_mono
  `(∀(s:'ffi state) e d extra.
     io_events_mono (FST(evaluate s e d)).ffi
     (FST(evaluate (s with clock := s.clock + extra) e d)).ffi) ∧
   (∀(s:'ffi state) e v d er extra.
     io_events_mono (FST(evaluate_match s e v d er)).ffi
     (FST(evaluate_match (s with clock := s.clock + extra) e v d er)).ffi)`
  (prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate);

Theorem evaluate_decs_add_to_clock_io_events_mono
  `∀s e d.
    io_events_mono
    (FST(evaluate_decs s e d)).ffi
    (FST(evaluate_decs (s with clock := s.clock + extra) e d)).ffi`
  (prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate_decs);

Theorem evaluate_decs_ffi_mono_clock
  `∀k1 k2 s e p.
    k1 ≤ k2 ⇒
    io_events_mono
    (FST (evaluate_decs (s with clock := k1) e p)).ffi
    (FST (evaluate_decs (s with clock := k2) e p)).ffi`
  (metis_tac [is_clock_io_mono_evaluate_decs
    |> Q.SPEC `s with clock := k1`
    |> SIMP_RULE (srw_ss ()) [is_clock_io_mono_def, pair_CASE_def]]);

(* due to Eval this is no longer true
Theorem evaluate_state_unchanged
 `(!(st:'ffi state) env es st' r.
    evaluate st env es = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp) ∧
  (!(st:'ffi state) env v pes err_v st' r.
    evaluate_match st env v pes err_v = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp)`
 (ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def]);
*)

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

val evaluate_decs_ffi_sandwich = Q.prove(
  `evaluate_decs s env ds = (s',r) ∧
   evaluate_decs s' env' ds'  = (s'',r') ∧
   s''.ffi = s.ffi ⇒ s'.ffi = s.ffi`,
  rw[] \\
  imp_res_tac evaluate_io_events_mono_imp \\ fs[] \\
  metis_tac[io_events_mono_antisym]);

val evaluate_decs_alt_ffi_sandwich = Q.prove(
  `evaluate s env ds = (s',r) ∧
   evaluate_decs (s' with clock := c) env' ds'  = (s'',r') ∧
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

Theorem evaluate_next_type_stamp_mono
  `(evaluate (s:'ffi state) env es = (s',res1) ==>
    s.next_type_stamp ≤ s'.next_type_stamp) /\
   (evaluate_match (s:'ffi state) env v pes err_v = (s',res2) ==>
    s.next_type_stamp ≤ s'.next_type_stamp) /\
   (evaluate_decs (s:'ffi state) env ds = (s',res3) ==>
    s.next_type_stamp ≤ s'.next_type_stamp)`
 (rpt conj_tac \\ strip_tac
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT2 |> SPEC_ALL)
  \\ fs [is_clock_io_mono_def] \\ rfs []);

Theorem evaluate_next_exn_stamp_mono
  `(evaluate (s:'ffi state) env es = (s',res1) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp) /\
   (evaluate_match (s:'ffi state) env v pes err_v = (s',res2) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp) /\
   (evaluate_decs (s:'ffi state) env ds = (s',res3) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp)`
 (rpt conj_tac \\ strip_tac
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT2 |> SPEC_ALL)
  \\ fs [is_clock_io_mono_def] \\ rfs []);

val evaluate_next_type_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate s''' env' exp' = (s'',r') ∧
   s'''.next_type_stamp = s'.next_type_stamp ∧
   s''.next_type_stamp = s.next_type_stamp
   ⇒ s'.next_type_stamp = s.next_type_stamp`,
  rw[] \\ imp_res_tac evaluate_next_type_stamp_mono \\ fs []);

val evaluate_match_next_type_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate_match s''' env' x1 x2 x3 = (s'',r') ∧
   s'''.next_type_stamp = s'.next_type_stamp ∧
   s''.next_type_stamp = s.next_type_stamp
   ⇒ s'.next_type_stamp = s.next_type_stamp`,
  rw[] \\ imp_res_tac evaluate_next_type_stamp_mono \\ fs []);

val evaluate_decs_next_type_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate_decs s''' env' ds = (s'',r') ∧
   s'''.next_type_stamp = s'.next_type_stamp ∧
   s''.next_type_stamp = s.next_type_stamp
   ⇒ s'.next_type_stamp = s.next_type_stamp`,
  rw[] \\ imp_res_tac evaluate_next_type_stamp_mono \\ fs []);

val evaluate_decs_decs_next_type_stamp_sandwich = Q.prove(
  `evaluate_decs s env exp = (s',r) ∧
   evaluate_decs s''' env' ds = (s'',r') ∧
   s'''.next_type_stamp = s'.next_type_stamp ∧
   s''.next_type_stamp = s.next_type_stamp
   ⇒ s'.next_type_stamp = s.next_type_stamp`,
  rw[] \\ imp_res_tac evaluate_next_type_stamp_mono \\ fs []);

val evaluate_next_exn_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate s''' env' exp' = (s'',r') ∧
   s'''.next_exn_stamp = s'.next_exn_stamp ∧
   s''.next_exn_stamp = s.next_exn_stamp
   ⇒ s'.next_exn_stamp = s.next_exn_stamp`,
  rw[] \\ imp_res_tac evaluate_next_exn_stamp_mono \\ fs []);

val evaluate_match_next_exn_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate_match s''' env' x1 x2 x3 = (s'',r') ∧
   s'''.next_exn_stamp = s'.next_exn_stamp ∧
   s''.next_exn_stamp = s.next_exn_stamp
   ⇒ s'.next_exn_stamp = s.next_exn_stamp`,
  rw[] \\ imp_res_tac evaluate_next_exn_stamp_mono \\ fs []);

val evaluate_decs_next_exn_stamp_sandwich = Q.prove(
  `evaluate s env exp = (s',r) ∧
   evaluate_decs s''' env' ds = (s'',r') ∧
   s'''.next_exn_stamp = s'.next_exn_stamp ∧
   s''.next_exn_stamp = s.next_exn_stamp
   ⇒ s'.next_exn_stamp = s.next_exn_stamp`,
  rw[] \\ imp_res_tac evaluate_next_exn_stamp_mono \\ fs []);

val evaluate_decs_decs_next_exn_stamp_sandwich = Q.prove(
  `evaluate_decs s env exp = (s',r) ∧
   evaluate_decs s''' env' ds = (s'',r') ∧
   s'''.next_exn_stamp = s'.next_exn_stamp ∧
   s''.next_exn_stamp = s.next_exn_stamp
   ⇒ s'.next_exn_stamp = s.next_exn_stamp`,
  rw[] \\ imp_res_tac evaluate_next_exn_stamp_mono \\ fs []);

Theorem evaluate_ffi_intro `
  (∀(s:'a state) env e s' r.
     evaluate s env e = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs ∧
       t.next_type_stamp = s.next_type_stamp ∧
       t.next_exn_stamp = s.next_exn_stamp
       ⇒
       evaluate t env e = (t with <| clock := s'.clock; refs := s'.refs;
                                     next_type_stamp := s'.next_type_stamp;
                                     next_exn_stamp := s'.next_exn_stamp |>, r)) ∧
  (∀(s:'a state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs ∧
       t.next_type_stamp = s.next_type_stamp ∧
       t.next_exn_stamp = s.next_exn_stamp
       ⇒
       evaluate_match t env v pes errv = (t with <| clock := s'.clock; refs := s'.refs;
                                     next_type_stamp := s'.next_type_stamp;
                                     next_exn_stamp := s'.next_exn_stamp |>, r)) ∧
  (∀(s:'a state) env ds s' r.
     evaluate_decs s env ds = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀(t:'b state).
       t.clock = s.clock ∧ t.refs = s.refs ∧
       t.next_type_stamp = s.next_type_stamp ∧
       t.next_exn_stamp = s.next_exn_stamp
       ⇒
       evaluate_decs t env ds = (t with <| clock := s'.clock; refs := s'.refs;
                                     next_type_stamp := s'.next_type_stamp;
                                     next_exn_stamp := s'.next_exn_stamp |>, r))`
  (ho_match_mp_tac full_evaluate_ind
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
    \\ every_case_tac >> fs[])
  >- (
    rfs[evaluate_def] \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[] \\ fs[]
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
    \\ fs[] \\ rfs[])
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- fs[state_component_equality]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC
    \\ fs[option_CASE_fst_cong,result_CASE_fst_cong]
    \\ rw[]
    \\ rfs[]
    \\ pop_assum mp_tac
    \\ impl_tac >- (every_case_tac \\ fs[])
    \\ rw[])
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
      \\ rfs[dec_clock_def] \\ fs[] )
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      reverse (Cases_on `?a1 a2. a = [a1;a2]`)
      >-
       (Cases_on `a` \\ fs [] \\ rename [`a = [_]`]
        \\ Cases_on `a` \\ fs [] \\ rename [`a <> []`]
        \\ Cases_on `a` \\ fs [])
      \\ fs [] \\ rveq \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      >- (rw [] \\ fs [])
      \\ TOP_CASE_TAC \\ fs [] \\ fs [dec_clock_def]
      \\ Cases_on `r'` \\ fs []
      \\ rw [] \\ fs []
      \\ drule (GEN_ALL evaluate_decs_alt_ffi_sandwich)
      \\ disch_then drule \\ fs [])
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
    \\ rw[state_component_equality])
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
    \\ fs[] \\ rfs[] )
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
    \\ fs[] \\ rfs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_match_ffi_sandwich]
    \\ fs[] \\ rfs[] )
  >- (
    rfs[evaluate_def]
    \\ qpat_x_assum`_ = (_,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- ( strip_tac \\ rveq \\ fs[] )
    \\ strip_tac \\ fs[]
    \\ rename1`evaluate s _ _ = (s1,_)`
    \\ `s1.ffi = s.ffi` by metis_tac[evaluate_ffi_sandwich]
    \\ fs[] \\ rfs[] )
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
    \\ rw[state_component_equality] )
  >- (
    rfs[evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- rw[state_component_equality]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[state_component_equality] )
  >- (
    rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ Cases_on `evaluate_decs s env [d1]` \\ fs []
    \\ reverse (Cases_on `r'`) \\ fs []
    >- (rveq \\ fs [])
    \\ Cases_on `evaluate_decs q (extend_dec_env a env) (d2::ds)` \\ fs []
    \\ rveq \\ fs []
    \\ `q'.ffi = s.ffi` by metis_tac[evaluate_decs_ffi_sandwich]
    \\ `q.ffi = s.ffi` by metis_tac[evaluate_decs_ffi_sandwich]
    \\ fs [] \\ Cases_on `r'` \\ fs [combine_dec_result_def])
  >- (
    rfs[full_evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs []
    >- rw[state_component_equality]
    \\ Cases_on `evaluate s env [e]` \\ fs []
    \\ Cases_on `r'` \\ fs []
    \\ rw [] \\ fs [])
  >- (
    rfs[full_evaluate_def]
    \\ rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def]
    \\ reverse TOP_CASE_TAC \\ fs []
    >- rw[state_component_equality]
    \\ rw [] \\ fs []
    \\ rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ rw[state_component_equality] )
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ Cases_on `evaluate_decs s env ds` \\ fs []
    \\ rveq \\ fs []
    \\ Cases_on `r'` \\ fs [])
  >- (
    rfs[full_evaluate_def] \\ rw []
    \\ Cases_on `evaluate_decs s env ds` \\ fs []
    \\ reverse (Cases_on `r'`) \\ fs []
    >- (rveq \\ fs [])
    \\ `q.ffi = s.ffi` by metis_tac[evaluate_decs_ffi_sandwich]
    \\ fs [] ));

Theorem evaluate_set_next_type_stamp `
  (∀(s0:'a state) env xs s1 res k.
     evaluate s0 env xs = (s1,res) /\
     s1.next_type_stamp = s0.next_type_stamp ==>
     evaluate (s0 with next_type_stamp := k) env xs =
              (s1 with next_type_stamp := k,res)) ∧
  (∀(s0:'a state) env v pes errv s1 res k.
     evaluate_match s0 env v pes errv = (s1,res) ∧
     s1.next_type_stamp = s0.next_type_stamp ==>
     evaluate_match (s0 with next_type_stamp := k) env v pes errv =
                    (s1 with next_type_stamp := k,res)) ∧
  (∀(s0:'a state) env ds s1 res k.
     evaluate_decs s0 env ds = (s1,res) ∧
     s1.next_type_stamp = s0.next_type_stamp ==>
     evaluate_decs (s0 with next_type_stamp := k) env ds =
                   (s1 with next_type_stamp := k,res))`
  (ho_match_mp_tac full_evaluate_ind
  \\ fs [full_evaluate_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC
    \\ rw [] \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_next_type_stamp_sandwich])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC \\ rw [] \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ rw [] \\ rfs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_match_next_type_stamp_sandwich])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ rw [] \\ rfs [])
  >- (
    TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ Cases_on `op = Opapp` \\ fs []
    >- (
      TOP_CASE_TAC \\ fs [] \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs [] >- (rw [] \\ fs [])
      \\ strip_tac
      \\ `(dec_clock q).next_type_stamp = q.next_type_stamp` by EVAL_TAC
      \\ `q.next_type_stamp = s0.next_type_stamp` by
           metis_tac [evaluate_next_type_stamp_sandwich] \\ fs []
      \\ fs [dec_clock_def])
    \\ Cases_on `op = Eval` \\ fs []
    >- (
      reverse (Cases_on `?a1 a2. a = [a1;a2]`)
      >-
       (Cases_on `a` \\ fs [] \\ rename [`a = [_]`]
        \\ Cases_on `a` \\ fs [] \\ rename [`a <> []`]
        \\ Cases_on `a` \\ fs [])
      \\ fs [] \\ rveq \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      >- (rw [] \\ fs [])
      \\ TOP_CASE_TAC \\ fs [] \\ fs [dec_clock_def]
      \\ Cases_on `r` \\ fs []
      \\ rw [] \\ fs []
      \\ `(q with clock := q.clock − 1).next_type_stamp =
          q.next_type_stamp` by EVAL_TAC
      \\ `q.next_type_stamp = s0.next_type_stamp`
            by metis_tac [evaluate_decs_next_type_stamp_sandwich]
      \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ PairCases_on `x` \\ fs [] \\ rw [] \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_next_type_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_next_type_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_match_next_type_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_next_type_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_decs_decs_next_type_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs [] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs [] \\ EVAL_TAC )
  >- (
    TOP_CASE_TAC \\ fs [] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_type_stamp = q.next_type_stamp` \\ fs []
    \\ metis_tac [evaluate_decs_decs_next_type_stamp_sandwich] ));

Theorem evaluate_set_next_exn_stamp `
  (∀(s0:'a state) env xs s1 res k.
     evaluate s0 env xs = (s1,res) /\
     s1.next_exn_stamp = s0.next_exn_stamp ==>
     evaluate (s0 with next_exn_stamp := k) env xs =
              (s1 with next_exn_stamp := k,res)) ∧
  (∀(s0:'a state) env v pes errv s1 res k.
     evaluate_match s0 env v pes errv = (s1,res) ∧
     s1.next_exn_stamp = s0.next_exn_stamp ==>
     evaluate_match (s0 with next_exn_stamp := k) env v pes errv =
                    (s1 with next_exn_stamp := k,res)) ∧
  (∀(s0:'a state) env ds s1 res k.
     evaluate_decs s0 env ds = (s1,res) ∧
     s1.next_exn_stamp = s0.next_exn_stamp ==>
     evaluate_decs (s0 with next_exn_stamp := k) env ds =
                   (s1 with next_exn_stamp := k,res))`
  (ho_match_mp_tac full_evaluate_ind
  \\ fs [full_evaluate_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC
    \\ rw [] \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_next_exn_stamp_sandwich])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC \\ rw [] \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ rw [] \\ rfs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_match_next_exn_stamp_sandwich])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ rw [] \\ rfs [])
  >- (
    TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ Cases_on `op = Opapp` \\ fs []
    >- (
      TOP_CASE_TAC \\ fs [] \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs [] >- (rw [] \\ fs [])
      \\ strip_tac
      \\ `(dec_clock q).next_exn_stamp = q.next_exn_stamp` by EVAL_TAC
      \\ `q.next_exn_stamp = s0.next_exn_stamp` by
           metis_tac [evaluate_next_exn_stamp_sandwich] \\ fs []
      \\ fs [dec_clock_def])
    \\ Cases_on `op = Eval` \\ fs []
    >- (
      reverse (Cases_on `?a1 a2. a = [a1;a2]`)
      >-
       (Cases_on `a` \\ fs [] \\ rename [`a = [_]`]
        \\ Cases_on `a` \\ fs [] \\ rename [`a <> []`]
        \\ Cases_on `a` \\ fs [])
      \\ fs [] \\ rveq \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      >- (rw [] \\ fs [])
      \\ TOP_CASE_TAC \\ fs [] \\ fs [dec_clock_def]
      \\ Cases_on `r` \\ fs []
      \\ rw [] \\ fs []
      \\ `(q with clock := q.clock − 1).next_exn_stamp =
          q.next_exn_stamp` by EVAL_TAC
      \\ `q.next_exn_stamp = s0.next_exn_stamp`
            by metis_tac [evaluate_decs_next_exn_stamp_sandwich]
      \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ PairCases_on `x` \\ fs [] \\ rw [] \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_next_exn_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_next_exn_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_match_next_exn_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_next_exn_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs [])
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_decs_decs_next_exn_stamp_sandwich] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs [] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ fs [] \\ rw [] \\ fs [] \\ EVAL_TAC )
  >- (
    TOP_CASE_TAC \\ fs [] )
  >- (
    TOP_CASE_TAC \\ fs []
    \\ reverse TOP_CASE_TAC >- (rw [] \\ fs [])
    \\ fs [] \\ rw [] \\ fs []
    \\ sg `s0.next_exn_stamp = q.next_exn_stamp` \\ fs []
    \\ metis_tac [evaluate_decs_decs_next_exn_stamp_sandwich] ));

Theorem is_clock_io_mono_set_clock
  `is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r)`
  (fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `ck1 + (s.clock − (HD [s';s]).clock)`)
  \\ CASE_TAC
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ metis_tac []);

val evaluate_set_clock_lemmas
  = (BODY_CONJUNCTS is_clock_io_mono_evaluate
    @ BODY_CONJUNCTS is_clock_io_mono_evaluate_decs)
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock);

Theorem evaluate_set_clock
  `!(s:'ffi state) env exps s1 res.
      evaluate s env exps = (s1,res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate (s with clock := ck1) env exps =
                   (s1 with clock := ck,res)`
  (metis_tac evaluate_set_clock_lemmas);

Theorem evaluate_decs_set_clock
  `!s env decs s1 res.
      evaluate_decs s env decs = (s1,res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate_decs (s with clock := ck1) env decs =
                   (s1 with clock := ck,res)`
  (metis_tac evaluate_set_clock_lemmas);

Theorem is_clock_io_mono_minimal
  `is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)`
  (fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ CASE_TAC \\ fs []);

val evaluate_minimal_lemmas = BODY_CONJUNCTS is_clock_io_mono_evaluate
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_minimal);

Theorem evaluate_minimal_clock
  `(!(s:'ffi state) env es s' r k.
    evaluate s env es = (s',r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s''.
      evaluate (s with clock := k) env es =
      (s'',Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)`
  (metis_tac evaluate_minimal_lemmas);

Theorem evaluate_match_minimal_clock
  `(!(s:'ffi state) env v pes err_v s' r k.
    evaluate_match s env v pes err_v = (s',r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s''.
      evaluate_match (s with clock := k) env v pes err_v =
      (s'',Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)`
  (metis_tac evaluate_minimal_lemmas);

Theorem evaluate_set_init_clock
  `evaluate st env xs = (st', res) /\
   res <> Rerr (Rabort Rtimeout_error) ==>
   !k. ?ck res1 st1.
   evaluate (st with clock := k) env xs = (st1, res1) /\
   (res1 = res /\ st1 = (st' with clock := ck) \/
    res1 = Rerr (Rabort Rtimeout_error) /\
    io_events_mono st1.ffi st'.ffi)`
  (rw []
  \\ drule evaluate_set_clock
  \\ disch_then (qspec_then `0` mp_tac) \\ fs [] \\ strip_tac
  \\ Cases_on `ck1 <= k`
  THEN1 (
    fs [LESS_EQ_EXISTS] \\ rveq
    \\ drule evaluate_add_to_clock
    \\ disch_then (qspec_then `p` mp_tac) \\ fs []
    \\ metis_tac [])
  \\ drule evaluate_minimal_clock \\ fs []
  \\ disch_then (qspec_then `k` mp_tac) \\ fs []
  \\ rw [] \\ fs []);

val _ = export_theory();
