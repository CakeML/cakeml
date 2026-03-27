(*
  Properties of the operational semantics.
*)
Theory evaluateProps
Ancestors
  ast evaluate namespace namespaceProps semanticPrimitives
  semanticPrimitivesProps
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Theorem call_FFI_LENGTH:
   (call_FFI st index conf x = FFI_return new_st new_bytes) ==>
    (LENGTH x = LENGTH new_bytes)
Proof
  fs[ffiTheory.call_FFI_def] \\ every_case_tac \\ rw[] \\ fs[LENGTH_MAP]
QED

Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End

Theorem call_FFI_rel_consts:
   call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)
Proof
  rw[call_FFI_rel_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ fs[CaseEq"bool",CaseEq"oracle_result"]
  \\ rw[]
QED

Theorem RTC_call_FFI_rel_consts:
   ∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ (s2.oracle = s1.oracle)
Proof
  once_rewrite_tac[EQ_SYM_EQ]
  \\ match_mp_tac RTC_lifts_equalities
  \\ rw[call_FFI_rel_consts]
QED

Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End

Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End

Theorem io_events_mono_refl[simp]:
   io_events_mono ffi ffi
Proof
  rw[io_events_mono_def]
QED

Theorem io_events_mono_trans:
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3
Proof
  rw[io_events_mono_def]
  \\ metis_tac[IS_PREFIX_TRANS, IS_PREFIX_ANTISYM]
QED

Theorem io_events_mono_antisym:
   io_events_mono s1 s2 ∧ io_events_mono s2 s1 ⇒ s1 = s2
Proof
  rw[io_events_mono_def]
  \\ imp_res_tac IS_PREFIX_ANTISYM
  \\ rfs[]
QED

Theorem call_FFI_rel_io_events_mono:
   ∀s1 s2.
   RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
Proof
  REWRITE_TAC[io_events_mono_def] \\
  ho_match_mp_tac RTC_INDUCT
  \\ simp[call_FFI_rel_def,ffiTheory.call_FFI_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[IS_PREFIX_APPEND]
QED

Theorem do_app_call_FFI_rel:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
Proof
  srw_tac[][do_app_cases,thunk_op_def,AllCaseEqs(),store_alloc_def] >> rw[] >>
  TRY FULL_CASE_TAC >>
  fs[option_case_eq] >>
  rpt (FULL_CASE_TAC \\ fs[]) >>
  match_mp_tac RTC_SUBSET >> rw[call_FFI_rel_def] >> fs[] >> every_case_tac
  >> fs[] >> metis_tac[]
QED

Theorem evaluate_call_FFI_rel:
   (∀(s:'ffi state) e exp.
      RTC call_FFI_rel s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      RTC call_FFI_rel s.ffi (FST (evaluate_match s e v pes errv)).ffi) ∧
   (∀(s:'ffi state) e ds.
      RTC call_FFI_rel s.ffi (FST (evaluate_decs s e ds)).ffi)
Proof
  ho_match_mp_tac full_evaluate_ind >>
  srw_tac[][full_evaluate_def, do_eval_res_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_call_FFI_rel >>
  rev_full_simp_tac(srw_ss())[dec_clock_def] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,FST]
QED

Theorem evaluate_call_FFI_rel_imp:
   (∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi) ∧
   (∀s e p s' r.
      evaluate_decs s e p = (s',r) ⇒
      RTC call_FFI_rel s.ffi s'.ffi)
Proof
  metis_tac[PAIR,FST,evaluate_call_FFI_rel]
QED

Theorem evaluate_decs_call_FFI_rel[local]:
  ∀s e d.
     RTC call_FFI_rel s.ffi (FST (evaluate_decs s e d)).ffi
Proof
  ho_match_mp_tac evaluate_decs_ind >>
  srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,evaluate_call_FFI_rel,FST]
QED

Theorem evaluate_decs_call_FFI_rel_imp:
   ∀s e p s' r.
     evaluate_decs s e p = (s',r) ⇒
     RTC call_FFI_rel s.ffi s'.ffi
Proof
  metis_tac[PAIR,FST,evaluate_decs_call_FFI_rel]
QED

Theorem do_app_io_events_mono:
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
Proof
  metis_tac[do_app_call_FFI_rel,call_FFI_rel_io_events_mono]
QED

Theorem evaluate_io_events_mono:
   (∀(s:'ffi state) e exp.
      io_events_mono s.ffi (FST (evaluate s e exp)).ffi) ∧
   (∀(s:'ffi state) e v pes errv.
      io_events_mono s.ffi (FST (evaluate_match s e v pes errv)).ffi) ∧
   (∀s e d.
      io_events_mono s.ffi (FST (evaluate_decs s e d)).ffi)
Proof
  metis_tac[evaluate_call_FFI_rel,call_FFI_rel_io_events_mono]
QED

Theorem evaluate_io_events_mono_imp:
   (∀s e p s' r.
      evaluate s e p = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ⇒
      io_events_mono s.ffi s'.ffi) ∧
   (∀s e p s' r.
     evaluate_decs s e p = (s',r) ⇒
     io_events_mono s.ffi s'.ffi)
Proof
  metis_tac[PAIR,FST,evaluate_io_events_mono]
QED

Definition is_clock_io_mono_def:
  is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ LENGTH s.refs <= LENGTH s'.refs
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
        ))
End

Theorem is_clock_io_mono_cong:
  s = t ==>
  (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
    f s = g s) ==>
  (is_clock_io_mono f s <=> is_clock_io_mono g t)
Proof
  simp [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_return:
   is_clock_io_mono (\s. (s,Rval r)) s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_err:
   is_clock_io_mono (\s. (s,Rerr r)) s
Proof
  fs [is_clock_io_mono_def]
QED

Theorem pair_CASE_eq_forall:
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
Proof
  Cases_on `x` \\ fs []
QED

Theorem is_clock_io_mono_bind:
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [pair_case_eq] \\ fs []
  \\ simp_tac bool_ss [pair_CASE_eq_forall, pair_case_eq]
  \\ rpt (FIRST [DISCH_TAC, GEN_TAC])
  \\ full_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []
  \\ fsrw_tac [SATISFY_ss] [io_events_mono_trans]
  \\ fs []
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [pair_CASE_eq_forall, pair_case_eq]
  \\ rpt (FIRST [first_x_assum drule, disch_tac,
      drule_then strip_assume_tac (METIS_PROVE [] ``(P ==> Q) ==> P \/ ~ P``)]
    \\ fs [] \\ rfs [])
  \\ fsrw_tac [SATISFY_ss] [io_events_mono_trans]
QED

Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End

Theorem is_clock_io_mono_check:
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s,Rerr (Rabort Rtimeout_error)) else f s) s
Proof
  fs [is_clock_io_mono_def, dec_clock_def, adj_clock_def, with_same_clock]
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ fs [pair_CASE_eq_forall]
  \\ first_x_assum (qspec_then `clk - 1` mp_tac)
  \\ simp []
  \\ rpt (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE CHANGED_TAC (fs []))
  \\ Cases_on `r' = Rerr (Rabort Rtimeout_error)` \\ fs []
QED

Theorem dec_inc_clock:
  dec_clock (adj_clock 1 0 s) = s
Proof
  simp [dec_clock_def, adj_clock_def, with_same_clock]
QED

Theorem do_app_refs_length:
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))
Proof
  rw [] \\ Cases_on `refs_ffi` \\ Cases_on `op`
  \\ gvs [do_app_def,thunk_op_def,AllCaseEqs(),store_assign_def]
  \\ fs [store_assign_def,store_alloc_def]
  \\ rveq \\ fs [] \\ rveq \\ fs[]
QED

Theorem is_clock_io_mono_do_app_simple:
  ! xs (st:'ffi state).
   is_clock_io_mono (\st'.
    case do_app (st'.refs, st'.ffi) op xs of
      NONE => (st', Rerr (Rabort Rtype_error))
    | SOME ((refs,ffi),r) =>
      (st' with<| refs := refs; ffi := ffi |>, list_result r)) st
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (CASE_TAC ORELSE CHANGED_TAC (fs []) ORELSE CHANGED_TAC rveq ORELSE gen_tac)
  \\ imp_res_tac do_app_refs_length \\ gs[]
  \\ metis_tac [do_app_io_events_mono]
QED

Theorem is_clock_io_mono_acc_safe:
  !v g. (!st clk. f (st with clock := clk) = f st) /\
  (f st = v \/ f st <> v) /\
  is_clock_io_mono (\st'. g (f st) st') st ==>
  is_clock_io_mono (\st'. g (f st') st') st
Proof
  rw [is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_if_safe = is_clock_io_mono_acc_safe
  |> ISPEC T |> Q.SPEC `\b st. if b then j st else k st`
  |> SIMP_RULE bool_ss []
Theorem is_clock_io_mono_option_case_safe = is_clock_io_mono_acc_safe
  |> Q.ISPEC `NONE` |> Q.SPEC `\v st. case v of NONE => g st | SOME x => h x st`
  |> SIMP_RULE bool_ss []
Theorem is_clock_io_mono_match_case_safe = is_clock_io_mono_acc_safe
  |> Q.ISPEC `No_match` |> Q.SPEC `\m st. case m of No_match => g st
    | Match_type_error => h st | Match env => j env st`
  |> SIMP_RULE bool_ss []
Theorem is_clock_io_mono_match_case_pair_safe = is_clock_io_mono_acc_safe
  |> Q.ISPEC `No_match` |> Q.SPEC `\m st. (st, case m of No_match => g st
    | Match_type_error => h st | Match env => j env st)`
  |> SIMP_RULE bool_ss []

val step_tac =
  rpt (FIRST ([strip_tac]
    @ map ho_match_mp_tac [is_clock_io_mono_bind, is_clock_io_mono_check]
    @ [CHANGED_TAC (fs [Cong is_clock_io_mono_cong,
                        is_clock_io_mono_return, is_clock_io_mono_err,
                        do_eval_res_def, dec_inc_clock]), TOP_CASE_TAC]));

Theorem is_clock_io_mono_evaluate:
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s)
Proof
 ho_match_mp_tac full_evaluate_ind
 \\ rpt strip_tac \\ fs [full_evaluate_def, combine_dec_result_def]
 \\ TRY (step_tac \\ NO_TAC)
 >- (
  ho_match_mp_tac is_clock_io_mono_bind \\ fs[]
  \\ rpt strip_tac
  \\ ntac 2 (TOP_CASE_TAC
            \\ fs [is_clock_io_mono_return, is_clock_io_mono_err])
  >-  (
    fs[Cong is_clock_io_mono_cong, do_eval_res_def]
    \\ ho_match_mp_tac is_clock_io_mono_bind
    \\ gs[]
    \\ rpt conj_tac
    \\ step_tac \\ gs[is_clock_io_mono_def, fix_clock_def])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ rpt (FIRST [CHANGED_TAC (fs[is_clock_io_mono_return, is_clock_io_mono_err,
                                   is_clock_io_mono_do_app_simple]), CASE_TAC])
    \\ ho_match_mp_tac is_clock_io_mono_check \\ gs[] \\ rpt strip_tac
    \\ res_tac \\ gs[dec_inc_clock])
  >- (
    gvs [AllCaseEqs()]
    \\ step_tac
    \\ fs [is_clock_io_mono_def, dec_clock_def]
    \\ gvs [oneline update_thunk_def, oneline dest_thunk_def, store_assign_def,
            AllCaseEqs()])
  >- (assume_tac (SIMP_RULE std_ss [] is_clock_io_mono_do_app_simple) \\ fs[]))
 >- (step_tac \\ fs[is_clock_io_mono_def])
 >- (step_tac \\ fs[is_clock_io_mono_def])
 \\ step_tac \\ fs[is_clock_io_mono_def]
QED

Theorem is_clock_io_mono_evaluate_decs:
  !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s
Proof
  fs [is_clock_io_mono_evaluate]
QED

Theorem is_clock_io_mono_extra:
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra,r)
Proof
  DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ rpt DISCH_TAC
  \\ rpt (CHANGED_TAC (fs [semanticPrimitivesPropsTheory.with_same_clock]))
QED

Theorem is_clock_io_mono_extra_mono:
   (!s. is_clock_io_mono f s)
    ==> io_events_mono (FST(f s)).ffi
     (FST(f (s with clock := s.clock + extra))).ffi
Proof
  DISCH_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with clock := s.clock + extra`)
  \\ fs [is_clock_io_mono_def]
  \\ CASE_TAC
  \\ rpt (DISCH_TAC ORELSE GEN_TAC)
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s.clock`)
  \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
  \\ CASE_TAC
QED

fun mk_extra_lemmas mp_rule monad_rule
  = BODY_CONJUNCTS monad_rule
    |> map (BETA_RULE o MATCH_MP mp_rule o Q.GEN `s`)
fun prove_extra mp_rule monad_rule
  = simp_tac bool_ss (mk_extra_lemmas mp_rule monad_rule)

Theorem evaluate_add_to_clock:
   !(s:'ffi state) env es s' r extra.
    evaluate s env es = (s',r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (s with clock := s.clock + extra) env es =
    (s' with clock := s'.clock + extra,r)
Proof
  prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate
QED

Theorem evaluate_match_add_to_clock:
   !(s:'ffi state) env v pes err_v s' r extra.
    evaluate_match s env v pes err_v = (s', r) ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate_match (s with clock := s.clock + extra) env v pes err_v =
      (s' with clock := s'.clock + extra,r)
Proof
  prove_extra is_clock_io_mono_extra is_clock_io_mono_evaluate
QED

Theorem list_result_eq_Rval[simp]:
  list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
Proof
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM]
QED

Theorem list_result_eq_Rerr[simp]:
  list_result r = Rerr e ⇔ r = Rerr e
Proof
  Cases_on`r`>>srw_tac[][list_result_def,EQ_IMP_THM]
QED

Theorem result_rel_list_result[simp]:
  result_rel (LIST_REL R) Q (list_result r1) (list_result r2) ⇔
  result_rel R Q r1 r2
Proof
  Cases_on`r1`>>srw_tac[][PULL_EXISTS]
QED

Theorem list_result_inj:
  list_result x = list_result y ⇒ x = y
Proof
  Cases_on`x`>>Cases_on`y`>>EVAL_TAC
QED

Theorem evaluate_length:
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T)
Proof
  ho_match_mp_tac full_evaluate_ind >>
  srw_tac[][evaluate_def,LENGTH_NIL] >> srw_tac[][] >>
  gvs[AllCaseEqs()]
QED

Theorem evaluate_nil[simp]:
   ∀(s:'ffi state) env. evaluate s env [] = (s,Rval [])
Proof
 rw [evaluate_def]
QED

Theorem evaluate_sing:
   ∀(s:'ffi state) env e s' vs. evaluate s env [e] = (s',Rval vs) ⇒ ∃v. vs = [v]
Proof
 rw []
 >> imp_res_tac evaluate_length
 >> Cases_on `vs`
 >> fs []
 >> Cases_on `t`
 >> fs []
QED

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
 >> rw [] >> rw[]
QED

Theorem evaluate_append:
  ∀(s:'ffi state) env xs ys.
   evaluate s env (xs ++ ys) =
     case evaluate s env xs of
     | (s', Rval vs) =>
      (case evaluate s' env ys of
       | (s'', Rval vs') => (s'', Rval (vs++vs'))
       | err => err)
     | err => err
Proof
  Induct_on `xs`
  THEN1
   (rw [] \\ Cases_on `evaluate s env ys` \\ fs []
    \\ Cases_on `r` \\ fs [])
  \\ fs [] \\ once_rewrite_tac [evaluate_cons]
  \\ rw [] \\ Cases_on `evaluate s env [h]` \\ fs []
  \\ Cases_on `r` \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem evaluate_decs_nil[simp]:
   ∀(s:'ffi state) env.
    evaluate_decs s env [] = (s,Rval <| v := nsEmpty; c := nsEmpty |>)
Proof
 rw [evaluate_decs_def]
QED

Theorem evaluate_decs_cons:
  ∀(s:'ffi state) env d ds.
   evaluate_decs s env (d::ds) =
     case evaluate_decs s env [d] of
     | (s1, Rval env1) =>
      (case evaluate_decs s1 (extend_dec_env env1 env) ds of
       | (s2, r) => (s2, combine_dec_result env1 r)
       | err => err)
     | err => err
Proof
 Cases_on `ds`
 >> rw [evaluate_decs_def]
 >> split_pair_case_tac
 >> simp []
 >> rename1 `evaluate_decs _ _ _ = (s1,r)`
 >> Cases_on `r`
 >> simp [combine_dec_result_def, sem_env_component_equality]
QED

Theorem evaluate_decs_append:
  ∀ds1 s env ds2.
    evaluate_decs s env (ds1 ++ ds2) =
    case evaluate_decs s env ds1 of
      (s1,Rval env1) =>
        (case evaluate_decs s1 (extend_dec_env env1 env) ds2 of
           (s2,r) => (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) => (s1,Rerr v7)
Proof
  Induct \\ rw []
  >- (
    rw [extend_dec_env_def, combine_dec_result_def]
    \\ rpt CASE_TAC)
  \\ once_rewrite_tac [evaluate_decs_cons] \\ simp []
  \\ gs [combine_dec_result_def, extend_dec_env_def]
  \\ rpt CASE_TAC \\ gs []
QED

Theorem evaluate_match_list_result:
   evaluate_match s e v p er = (s',r) ⇒
   ∃r'. r = list_result r'
Proof
  Cases_on`r` >> srw_tac[][] >>
  imp_res_tac evaluate_length >|[
    Cases_on`a` >> full_simp_tac(srw_ss())[LENGTH_NIL],all_tac] >>
  metis_tac[list_result_def]
QED

val evaluate_decs_lemmas
  = BODY_CONJUNCTS is_clock_io_mono_evaluate_decs
    |> map (BETA_RULE o MATCH_MP is_clock_io_mono_extra o Q.GEN `s`)

Theorem evaluate_decs_add_to_clock:
   !s e p s' r extra.
   evaluate_decs s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)
Proof
  simp_tac bool_ss evaluate_decs_lemmas
QED

Theorem add_lemma[local]:
  !(k:num) k'. ?extra. k = k' + extra ∨ k' = k + extra
Proof
  intLib.ARITH_TAC
QED

Theorem with_clock_ffi[local]:
  (s with clock := k).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem evaluate_decs_clock_determ:
 !s e p s1 r1 s2 r2 k1 k2.
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
    s1.ffi = s2.ffi ∧ r1 = r2
Proof
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
   rw [])
QED

Theorem evaluate_add_to_clock_io_events_mono:
   (∀(s:'ffi state) e d extra.
     io_events_mono (FST(evaluate s e d)).ffi
     (FST(evaluate (s with clock := s.clock + extra) e d)).ffi) ∧
   (∀(s:'ffi state) e v d er extra.
     io_events_mono (FST(evaluate_match s e v d er)).ffi
     (FST(evaluate_match (s with clock := s.clock + extra) e v d er)).ffi)
Proof
  prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate
QED

Theorem evaluate_decs_add_to_clock_io_events_mono:
   ∀s e d.
    io_events_mono
    (FST(evaluate_decs s e d)).ffi
    (FST(evaluate_decs (s with clock := s.clock + extra) e d)).ffi
Proof
  prove_extra is_clock_io_mono_extra_mono is_clock_io_mono_evaluate_decs
QED

Theorem evaluate_decs_ffi_mono_clock:
   ∀k1 k2 s e p.
    k1 ≤ k2 ⇒
    io_events_mono
    (FST (evaluate_decs (s with clock := k1) e p)).ffi
    (FST (evaluate_decs (s with clock := k2) e p)).ffi
Proof
  metis_tac [is_clock_io_mono_evaluate_decs
    |> Q.SPEC `s with clock := k1`
    |> SIMP_RULE (srw_ss ()) [is_clock_io_mono_def, pair_CASE_def]]
QED

(* due to Eval this is no longer true
Theorem evaluate_state_unchanged:
  (!(st:'ffi state) env es st' r.
    evaluate st env es = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp) ∧
  (!(st:'ffi state) env v pes err_v st' r.
    evaluate_match st env v pes err_v = (st', r)
    ⇒
    st'.next_type_stamp = st.next_type_stamp ∧
    st'.next_exn_stamp = st.next_exn_stamp)
Proof
 ho_match_mp_tac evaluate_ind
 >> rw [evaluate_def]
 >> every_case_tac
 >> fs []
 >> rw [dec_clock_def, shift_fp_opts_def]
QED
*)

Theorem evaluate_next_type_stamp_mono:
   (evaluate (s:'ffi state) env es = (s',res1) ==>
    s.next_type_stamp ≤ s'.next_type_stamp) /\
   (evaluate_match (s:'ffi state) env v pes err_v = (s',res2) ==>
    s.next_type_stamp ≤ s'.next_type_stamp) /\
   (evaluate_decs (s:'ffi state) env ds = (s',res3) ==>
    s.next_type_stamp ≤ s'.next_type_stamp)
Proof
  rpt conj_tac \\ strip_tac
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT2 |> SPEC_ALL)
  \\ fs [is_clock_io_mono_def] \\ rfs []
QED

Theorem evaluate_next_exn_stamp_mono:
   (evaluate (s:'ffi state) env es = (s',res1) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp) /\
   (evaluate_match (s:'ffi state) env v pes err_v = (s',res2) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp) /\
   (evaluate_decs (s:'ffi state) env ds = (s',res3) ==>
    s.next_exn_stamp ≤ s'.next_exn_stamp)
Proof
  rpt conj_tac \\ strip_tac
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT2 |> SPEC_ALL)
  \\ fs [is_clock_io_mono_def] \\ rfs []
QED

Theorem evaluate_case_eqs = LIST_CONJ
  [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
    option_case_eq, list_case_eq, exp_or_val_case_eq, match_result_case_eq]

Theorem evaluate_set_next_stamps:
  (∀(s0:'a state) env xs s1 res.
     evaluate s0 env xs = (s1,res) ==>
     (s1.next_type_stamp = s0.next_type_stamp ==>
        !k. evaluate (s0 with next_type_stamp := k) env xs =
            (s1 with next_type_stamp := k,res)) ∧
     (s1.next_exn_stamp = s0.next_exn_stamp ==>
        !k. evaluate (s0 with next_exn_stamp := k) env xs =
            (s1 with next_exn_stamp := k,res))) ∧
  (∀(s0:'a state) env v pes errv s1 res.
     evaluate_match s0 env v pes errv = (s1,res) ==>
     (s1.next_type_stamp = s0.next_type_stamp ==>
        !k. evaluate_match (s0 with next_type_stamp := k) env v pes errv =
            (s1 with next_type_stamp := k,res)) ∧
     (s1.next_exn_stamp = s0.next_exn_stamp ==>
        !k. evaluate_match (s0 with next_exn_stamp := k) env v pes errv =
            (s1 with next_exn_stamp := k,res))) ∧
  (∀(s0:'a state) env ds s1 res.
     evaluate_decs s0 env ds = (s1,res) ==>
     (s1.next_type_stamp = s0.next_type_stamp ==>
        !k. evaluate_decs (s0 with next_type_stamp := k) env ds =
            (s1 with next_type_stamp := k,res)) ∧
     (s1.next_exn_stamp = s0.next_exn_stamp ==>
        !k. evaluate_decs (s0 with next_exn_stamp := k) env ds =
            (s1 with next_exn_stamp := k,res)))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ fs [full_evaluate_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ strip_tac
  \\ fs [evaluate_case_eqs, dec_clock_def, do_eval_res_def]
  >~ [‘op:op’] >-
   (Cases_on ‘getOpClass op = Force’ >-
      (gvs []
       \\ Cases_on `op` \\ gvs [] \\ Cases_on `t` \\ gvs []
       \\ gvs [AllCaseEqs()]
       \\ imp_res_tac evaluate_next_type_stamp_mono
       \\ imp_res_tac evaluate_next_exn_stamp_mono
       \\ rw []
       \\ fs [build_tdefs_def])
    \\ Cases_on ‘getOpClass op’ \\ fs []
    \\ fs [evaluate_case_eqs, dec_clock_def, do_eval_res_def]
    \\ rveq \\ fs []
    \\ fs [Q.ISPEC `(_, _)` EQ_SYM_EQ]
    \\ rveq \\ fs []
    \\ imp_res_tac evaluate_next_type_stamp_mono
    \\ imp_res_tac evaluate_next_exn_stamp_mono
    \\ rw []
    \\ fs [build_tdefs_def]
    \\ qpat_x_assum `fix_clock _ _ = _` mp_tac
    \\ rpt (TOP_CASE_TAC \\ gs[fix_clock_def])
    \\ rpt strip_tac \\ rveq
    \\ gs[fix_clock_def])
  \\ fs [evaluate_case_eqs, dec_clock_def, do_eval_res_def]
  \\ rveq \\ fs []
  \\ fs [Q.ISPEC `(_, _)` EQ_SYM_EQ]
  \\ rveq \\ fs []
  \\ imp_res_tac evaluate_next_type_stamp_mono
  \\ imp_res_tac evaluate_next_exn_stamp_mono
  \\ rw []
  \\ fs [build_tdefs_def]
  \\ qpat_x_assum `fix_clock _ _ = _` mp_tac
  \\ rpt (TOP_CASE_TAC \\ gs[fix_clock_def])
  \\ rpt strip_tac \\ rveq
  \\ gs[fix_clock_def]
QED

Theorem call_FFI_return_unchanged:
  call_FFI ffi s conf bytes = FFI_return ffi bytes' <=>
  (s = ExtCall «» /\ bytes' = bytes)
Proof
  simp [ffiTheory.call_FFI_def]
  \\ every_case_tac
  \\ simp [ffiTheory.ffi_state_component_equality]
  \\ TRY EQ_TAC
  \\ simp []
QED

Theorem do_app_ffi_unchanged:
  do_app (refs, ffi) op vs = SOME ((refs',ffi),r) ==>
  (∀outcome. r ≠ Rerr (Rabort (Rffi_error outcome))) ==>
  !ffi2. do_app (refs, ffi2) op vs = SOME ((refs',ffi2), r)
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [do_app_cases])
  \\ rw [do_app_def] \\ gvs[thunk_op_def, AllCaseEqs()]
  >- (pairarg_tac \\ gvs [])
  \\ gvs [call_FFI_return_unchanged,
          Q.SPECL [`x`, `ExtCall «»`] ffiTheory.call_FFI_def]
QED

Theorem evaluate_ffi_intro:
  (∀(s:'a state) env e s' r.
     evaluate s env e = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀nffi : 'b ffi_state.
     evaluate (s with ffi := nffi) env e = (s' with ffi := nffi, r)) ∧
  (∀(s:'a state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀nffi : 'b ffi_state.
     evaluate_match (s with ffi := nffi) env v pes errv =
        (s' with ffi := nffi, r)) ∧
  (∀(s:'a state) env ds s' r.
     evaluate_decs s env ds = (s',r) ∧
     s'.ffi = s.ffi ∧
     (∀outcome. r ≠ Rerr(Rabort(Rffi_error outcome)))
     ⇒
     ∀nffi : 'b ffi_state.
     evaluate_decs (s with ffi := nffi) env ds =
        (s' with ffi := nffi, r))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rpt strip_tac \\ fs [full_evaluate_def,combine_dec_result_def]
  \\ gvs [AllCaseEqs(), do_eval_res_def, PULL_EXISTS]
  \\ imp_res_tac evaluate_io_events_mono_imp
  \\ rfs [dec_clock_def]
  \\ TRY (drule_then (drule_then assume_tac) io_events_mono_antisym)
  \\ fs []
  \\ TRY (rename1 ‘_ = Force’
          \\ Cases_on `op` \\ gvs[] \\ Cases_on `t` \\ gvs[]
          \\ gvs [AllCaseEqs()]
          \\ imp_res_tac evaluate_io_events_mono_imp \\ gvs[]
          \\ drule_all io_events_mono_antisym \\ gvs[])
  \\ TRY (imp_res_tac do_app_io_events_mono
          \\ imp_res_tac io_events_mono_trans
          \\ CHANGED_TAC
             (rpt
              (drule_then (drule_then assume_tac) io_events_mono_antisym
               \\ fs [])))
  \\ fsrw_tac [SATISFY_ss] [do_app_NONE_ffi]
  \\ TRY (drule_then (simp o single) do_app_ffi_unchanged)
  \\ TOP_CASE_TAC  \\ gs[state_component_equality]
QED

Theorem is_clock_io_mono_set_clock:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `ck1 + (s.clock − (HD [s';s]).clock)`)
  \\ CASE_TAC
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ metis_tac []
QED

val evaluate_set_clock_lemmas
  = (BODY_CONJUNCTS is_clock_io_mono_evaluate
    @ BODY_CONJUNCTS is_clock_io_mono_evaluate_decs)
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock);

Theorem evaluate_set_clock:
   !(s:'ffi state) env exps s1 res.
      evaluate s env exps = (s1,res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate (s with clock := ck1) env exps =
                   (s1 with clock := ck,res)
Proof
  metis_tac evaluate_set_clock_lemmas
QED

Theorem evaluate_decs_set_clock:
   !s env decs s1 res.
      evaluate_decs s env decs = (s1,res) /\
      res <> Rerr (Rabort Rtimeout_error) ==>
      !ck. ?ck1. evaluate_decs (s with clock := ck1) env decs =
                   (s1 with clock := ck,res)
Proof
  metis_tac evaluate_set_clock_lemmas
QED

Theorem is_clock_io_mono_minimal:
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)
Proof
  fs [is_clock_io_mono_def]
  \\ rpt (FIRST (map CHANGED_TAC [fs [], strip_tac]))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ CASE_TAC \\ fs []
QED

val evaluate_minimal_lemmas = BODY_CONJUNCTS is_clock_io_mono_evaluate
  |> map (BETA_RULE o MATCH_MP is_clock_io_mono_minimal);

Theorem evaluate_minimal_clock:
   (!(s:'ffi state) env es s' r k.
    evaluate s env es = (s',r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s''.
      evaluate (s with clock := k) env es =
      (s'',Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)
Proof
  metis_tac evaluate_minimal_lemmas
QED

Theorem evaluate_match_minimal_clock:
   (!(s:'ffi state) env v pes err_v s' r k.
    evaluate_match s env v pes err_v = (s',r) ∧
    s'.clock = 0 ∧
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    s.clock > k
    ==>
    ?s''.
      evaluate_match (s with clock := k) env v pes err_v =
      (s'',Rerr (Rabort Rtimeout_error)) /\
      io_events_mono s''.ffi s'.ffi)
Proof
  metis_tac evaluate_minimal_lemmas
QED

Theorem evaluate_set_init_clock:
   evaluate st env xs = (st', res) /\
   res <> Rerr (Rabort Rtimeout_error) ==>
   !k. ?ck res1 st1.
   evaluate (st with clock := k) env xs = (st1, res1) /\
   (res1 = res /\ st1 = (st' with clock := ck) \/
    res1 = Rerr (Rabort Rtimeout_error) /\
    io_events_mono st1.ffi st'.ffi)
Proof
  rw []
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
  \\ rw [] \\ fs []
QED

Theorem can_pmatch_all_EVERY:
  can_pmatch_all envC refs ps v <=>
  EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps
Proof
  Induct_on `ps` \\ fs [can_pmatch_all_def]
QED

Theorem same_type_trans:
   same_type t1 t2 /\ same_type t1 t3 ==> same_type t2 t3
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ Cases_on `t3` \\ fs [same_type_def]
QED

Theorem evaluate_refs_length_mono:
  (∀(s:'ffi state) env es s' r.
     evaluate s env es = (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs) ∧
  (∀(s:'ffi state) env v pes err_v s' r.
     evaluate_match s env v pes err_v = (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs)
Proof
  rpt strip_tac
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL)
  \\ assume_tac (is_clock_io_mono_evaluate |> CONJUNCT2 |> CONJUNCT2 |> SPEC_ALL)
  \\ rfs [is_clock_io_mono_def]
QED

Theorem combine_dec_result_eq_Rerr:
  combine_dec_result env r = Rerr e <=> r = Rerr e
Proof
  Cases_on `r` \\ simp [combine_dec_result_def]
QED

Theorem eval_no_eval_simulation:
  (! (s:'ffi state) env exps s' res.
     evaluate s env exps = (s', res) /\
     s.eval_state = NONE /\
     res <> Rerr (Rabort Rtype_error) ==>
     s'.eval_state = NONE /\
     evaluate (s with eval_state := es) env exps =
     (s' with eval_state := es, res))
  /\
  (! (s:'ffi state) env x pes err_x s' res.
     evaluate_match s env x pes err_x = (s', res) /\
     s.eval_state = NONE /\
     res <> Rerr (Rabort Rtype_error) ==>
     s'.eval_state = NONE /\
     evaluate_match (s with eval_state := es) env x pes err_x =
     (s' with eval_state := es, res))
  /\
  (! (s:'ffi state) env decs s' res.
     evaluate_decs s env decs = (s', res) /\
     s.eval_state = NONE /\
     res <> Rerr (Rabort Rtype_error) ==>
     s'.eval_state = NONE /\
     evaluate_decs (s with eval_state := es) env decs =
     (s' with eval_state := es, res))
Proof
  ho_match_mp_tac (name_ind_cases [] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  \\ rveq \\ fs []
  (* useful for development
  \\ TRY (rename [`Case ([App _ _])`] ORELSE cheat)
  *)
  \\ TRY (rename [`Case ([App _ _])`]
    \\ Cases_on ‘getOpClass op = Force’ >- (
      Cases_on `op` \\ gvs[] \\ Cases_on `t` \\ gvs[]
      \\ gvs[AllCaseEqs(), dec_clock_def])
    \\ Cases_on ‘getOpClass op’ \\ gs[]
    \\ rpt (MAP_FIRST (dxrule_then (strip_assume_tac o SIMP_RULE bool_ss []))
      [hd (RES_CANON pair_case_eq), hd (RES_CANON result_case_eq), hd (RES_CANON bool_case_eq)]
    )
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ fs [bool_case_eq, do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ rfs [Q.SPECL [`vs`, `NONE`] do_eval_def]
    \\ fs [dec_clock_def]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ COND_CASES_TAC \\ gs[]
  )
  \\ fs [evaluate_case_eqs]
  \\ rveq \\ fs []
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, combine_dec_result_eq_Rerr, declare_env_def]
QED

Theorem evaluate_ffi_etc_intro:
  evaluate s0 env xs = (s1, res) /\
  (!outcome. res <> Rerr (Rabort (Rffi_error outcome))) /\
  s1.ffi = s0.ffi /\
  s1.next_type_stamp = s0.next_type_stamp /\
  s1.next_exn_stamp = s0.next_exn_stamp /\
  s0.eval_state = NONE /\
  res <> Rerr (Rabort Rtype_error) /\
  s.refs = s0.refs
  ==>
  ?ck1 ck2. evaluate (s with clock := ck1) env xs =
    (s with <| refs := s1.refs; clock := ck2 |>, res)
Proof
  rw []
  \\ dxrule_then (qspec_then `s.ffi` mp_tac) (CONJUNCT1 evaluate_ffi_intro)
  \\ rw []
  \\ dxrule (CONJUNCT1 evaluate_set_next_stamps)
  \\ simp []
  \\ disch_then (qspec_then `s.next_type_stamp` mp_tac o CONJUNCT1)
  \\ rw []
  \\ dxrule (CONJUNCT1 evaluate_set_next_stamps)
  \\ simp []
  \\ disch_then (qspec_then `s.next_exn_stamp` mp_tac o CONJUNCT2)
  \\ rw []
  \\ dxrule (CONJUNCT1 eval_no_eval_simulation)
  \\ simp []
  \\ disch_then (qspec_then `s.eval_state` mp_tac)
  \\ rw []
  \\ qexists_tac `s0.clock`
  \\ qexists_tac `s1.clock`
  \\ dxrule_then irule (Q.prove (`(evaluate a x y = b) /\ a = c /\ b = d
    ==> evaluate c x y = d`, rw []))
  \\ simp [state_component_equality]
QED

Theorem same_type_sym:
  same_type t1 t2 ==> same_type t2 t1
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ fs [same_type_def]
QED

Theorem pmatch_not_type_error_EQ:
  (pmatch envC refs Pany v acc <> Match_type_error <=> T) /\
  (pmatch envC refs (Pvar n) v acc <> Match_type_error <=> T) /\
  (pmatch envC refs (Pcon (SOME name) xs) v acc <> Match_type_error <=>
   ?ys t l stamp.
     v = Conv (SOME t) ys /\
     nsLookup envC name = SOME (l,stamp) /\ LENGTH xs = l /\
     same_type stamp t /\
     (t = stamp ==> l = LENGTH ys /\
                    pmatch_list envC refs xs ys acc <> Match_type_error)) /\
  (pmatch envC refs (Pcon NONE xs) v acc <> Match_type_error <=>
   ?ys. v = Conv NONE ys /\ LENGTH xs = LENGTH ys /\
        pmatch_list envC refs xs ys acc <> Match_type_error) /\
  (pmatch_list envC refs [] [] acc <> Match_type_error <=> T) /\
  (pmatch_list envC refs [] (v::vs) acc <> Match_type_error <=> F) /\
  (pmatch_list envC refs (p::ps) [] acc <> Match_type_error <=> F) /\
  (pmatch_list envC refs (p::ps) (v::vs) acc <> Match_type_error <=>
     pmatch envC refs p v acc <> Match_type_error /\
     (!a. pmatch envC refs p v acc = No_match ==>
          pmatch_list envC refs ps vs acc <> Match_type_error) /\
     (!a. pmatch envC refs p v acc = Match a ==>
          pmatch_list envC refs ps vs a <> Match_type_error))
Proof
  fs [pmatch_def]
  \\ reverse (rw [])
  THEN1 (every_case_tac \\ fs [])
  \\ Cases_on `v` \\ fs [pmatch_def]
  \\ rename [`Conv opt`]
  \\ Cases_on `opt` \\ fs [pmatch_def]
  \\ rw [] \\ fs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ Cases_on `same_type r x` \\ fs []
  \\ Cases_on `LENGTH xs = q` \\ fs []
  \\ fs [semanticPrimitivesTheory.same_ctor_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `LENGTH l = q` \\ fs []
QED

Theorem do_app_ffi_mono:
  do_app (refs,ffi:'ffi ffi_state) op args = SOME ((refs',ffi'),r)
   ⇒
   ?l. ffi'.io_events = ffi.io_events ++ l
Proof
  rw[]
  \\ gvs [semanticPrimitivesPropsTheory.do_app_cases,oneline thunk_op_def,
          AllCaseEqs(),store_alloc_def]
  \\ fs[ffiTheory.call_FFI_def]
  \\ rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
  \\ rveq \\ fs[ffiTheory.ffi_state_component_equality,DROP_LENGTH_NIL]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
QED

Theorem do_app_SOME_ffi_same_oracle_state:
   do_app (refs,ffi:'ffi ffi_state) op args = SOME ((refs',ffi'),r)
   ⇒
   do_app (refs,ffi with io_events := l) op args =
   SOME ((refs',ffi' with io_events := l ++ DROP (LENGTH ffi.io_events) ffi'.io_events),r)
Proof
  simp [Once semanticPrimitivesPropsTheory.do_app_cases]
  \\ rw []
  \\ gvs [do_app_def,oneline thunk_op_def,AllCaseEqs(),store_alloc_def]
  \\ simp [DROP_LENGTH_NIL]
  \\ fs[ffiTheory.call_FFI_def]
  \\ rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
  \\ rveq \\ fs[ffiTheory.ffi_state_component_equality,DROP_LENGTH_NIL]
  \\ rfs[store_assign_def,store_v_same_type_def,store_lookup_def]
  \\ fs[DROP_APPEND,DROP_LENGTH_NIL]
QED

Theorem evaluate_history_irrelevance:
  (!(st:'ffi semanticPrimitives$state) env exp st' res.
    evaluate st env exp = (st',res) ==>
    ?new_io. st'.ffi.io_events = st.ffi.io_events ++ new_io /\
    (!l. evaluate (st with ffi := (st.ffi with io_events := l)) env exp =
    (st' with ffi := (st'.ffi with io_events := l ++ new_io), res))) /\
  (!(st:'ffi semanticPrimitives$state) env v pes err_v st' res.
    evaluate_match st env v pes err_v = (st',res) ==>
    ?new_io. st'.ffi.io_events = st.ffi.io_events ++ new_io /\
    (!l. evaluate_match (st with ffi := (st.ffi with io_events := l)) env
        v pes err_v =
    (st' with ffi := (st'.ffi with io_events := l ++ new_io), res))) /\
  (!(st:'ffi semanticPrimitives$state) env ds st' res.
    evaluate_decs st env ds = (st',res) ==>
    ?new_io. st'.ffi.io_events = st.ffi.io_events ++ new_io /\
    !l. evaluate_decs (st with ffi := (st.ffi with io_events := l)) env ds =
    (st' with ffi := (st'.ffi with io_events := l ++ new_io), res))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw[full_evaluate_def]
  \\ fs [do_eval_res_def,error_result_case_eq,option_case_eq,
         exp_or_val_case_eq,list_case_eq,match_result_case_eq,
         pair_case_eq,result_case_eq,bool_case_eq,AllCaseEqs()]
  \\ rveq \\ fs []
  \\ simp [rich_listTheory.DROP_LENGTH_NIL_rwt]
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, dec_clock_def]
  \\ TRY (drule_then (fn t => simp [t])
       semanticPrimitivesPropsTheory.do_app_NONE_ffi)
  \\ TRY (drule_then (fn t => simp [t])
       do_app_SOME_ffi_same_oracle_state)
  \\ imp_res_tac do_app_ffi_mono
  \\ simp [rich_listTheory.DROP_APPEND2]
  \\ COND_CASES_TAC \\ gs[]
QED

Theorem evaluate_add_history:
  (!(st:'ffi semanticPrimitives$state) env exp st' res.
     evaluate (st with ffi := st.ffi with io_events := []) env exp = (st',res)
     ==>
     evaluate st env exp =
     (st' with ffi:= st'.ffi with io_events := st.ffi.io_events ++ st'.ffi.io_events, res)) ∧
  (!(st:'ffi semanticPrimitives$state) env v pes err_v st' res.
     evaluate_match (st with ffi := st.ffi with io_events := []) env v pes err_v = (st',res)
     ==>
     evaluate_match st env v pes err_v =
     (st' with ffi:= st'.ffi with io_events := st.ffi.io_events ++ st'.ffi.io_events, res))
Proof
  rw []
  \\ imp_res_tac evaluate_history_irrelevance
  \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum (fn t => simp [GSYM t] \\ AP_THM_TAC)
  \\ rpt AP_THM_TAC
  \\ AP_TERM_TAC
  \\ simp [state_component_equality, ffiTheory.ffi_state_component_equality]
QED

Theorem Apps_append:
  ∀xs ys f. Apps f (xs ++ ys) = Apps (Apps f xs) ys
Proof
  Induct \\ gvs [Apps_def]
QED

Theorem evaluate_Apps_Rerr:
  ∀xs f (st:'ffi state) env s1 e.
    evaluate st env xs = (s1,Rerr e) ⇒
    evaluate st env [Apps f (REVERSE xs)] = (s1,Rerr e)
Proof
  Induct >- gvs [evaluate_def]
  \\ simp [Once evaluate_cons,Apps_append,Apps_def]
  \\ qx_gen_tac ‘h’ \\ rpt gen_tac
  \\ gvs [evaluate_def]
  \\ namedCases_on ‘evaluate st env [h]’ ["s' r"] \\ gvs []
  \\ Cases_on ‘r’ \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ strip_tac
  \\ last_x_assum drule
  \\ strip_tac \\ gvs []
QED

Theorem evaluate_Apps_Funs:
  ∀l x ns vs (st: 'ffi state) s1 s2 env env1 e.
    evaluate st env l = (s1,Rval vs) ∧
    evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) ∧
    LENGTH l = LENGTH ns ∧ ns ≠ [] ∧ LENGTH ns ≤ s2.clock ⇒
    evaluate st env [Apps x (REVERSE l)] =
    evaluate
      (s2 with clock := s2.clock - LENGTH ns)
      (env1 with v := nsAppend (alist_to_ns (ZIP (REVERSE ns,vs))) env1.v) [e]
Proof
  Induct using SNOC_INDUCT
  \\ gvs [] \\ rpt gen_tac
  \\ simp [SNOC_APPEND,evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ gvs [] \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘ns’ \\ gvs [Apps_def,Apps_append]
  \\ gvs [REVERSE_APPEND,Apps_def]
  \\ Cases_on ‘l = []’ \\ gvs [evaluate_def,Apps_def]
  >-
   (gvs [do_opapp_def,dec_clock_def]
    \\ imp_res_tac evaluate_sing \\ gvs [Funs_def])
  \\ imp_res_tac evaluate_sing \\ gvs [Funs_def]
  \\ last_x_assum drule
  \\ strip_tac
  \\ irule EQ_TRANS
  \\ pop_assum $ irule_at $ Pos hd
  \\ simp [evaluate_def,do_opapp_def]
  \\ rename [‘Funs t _’]
  \\ Cases_on ‘t’ \\ gvs [Funs_def,evaluate_def]
  \\ qrefine ‘a::as’ \\ gvs []
  \\ irule_at (Pos hd) EQ_REFL
  \\ gvs [dec_clock_def,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [sem_env_component_equality]
  \\ rewrite_tac [GSYM SNOC_APPEND]
  \\ DEP_REWRITE_TAC [ZIP_SNOC]
  \\ gvs [SNOC_APPEND]
  \\ imp_res_tac evaluate_length
  \\ Cases_on ‘env1.v’
  \\ gvs [alist_to_ns_def,nsBind_def,nsAppend_def]
QED

Theorem evaluate_Apps_f_err:
  ∀xs vs (st:'ffi state) envs1 f s1 s2.
    evaluate st env xs = (s1,Rval vs) ∧
    evaluate s1 env [f] = (s2,Rerr r) ⇒
    evaluate st env [Apps f (REVERSE xs)] = (s2,Rerr r)
Proof
  Induct using SNOC_INDUCT
  \\ gvs [evaluate_def,Apps_def]
  \\ simp [evaluate_append,SNOC_APPEND]
  \\ gvs [AllCaseEqs()] \\ rw []
  \\ gvs [Apps_append,Apps_def,REVERSE_APPEND]
  \\ last_x_assum $ irule
  \\ gvs [evaluate_def]
QED

Theorem evaluate_Apps_Funs_timeout:
  ∀l x ns vs (st: 'ffi state) s1 s2 env env1 e.
    evaluate st env l = (s1,Rval vs) ∧
    evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) ∧
    LENGTH l = LENGTH ns ∧ ns ≠ [] ∧ s2.clock < LENGTH ns ⇒
    evaluate st env [Apps x (REVERSE l)] =
      (s2 with clock := 0, Rerr (Rabort Rtimeout_error))
Proof
  Induct using SNOC_INDUCT
  \\ gvs [] \\ rpt gen_tac
  \\ simp [SNOC_APPEND,evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ gvs [] \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘ns’ \\ gvs [Apps_def,Apps_append]
  \\ gvs [REVERSE_APPEND,Apps_def]
  \\ Cases_on ‘l = []’ \\ gvs [evaluate_def,Apps_def]
  >- (gvs [do_opapp_def,dec_clock_def,state_component_equality])
  \\ imp_res_tac evaluate_sing \\ gvs [Funs_def]
  \\ Cases_on ‘s2.clock’
  >-
   (irule evaluate_Apps_f_err \\ gvs []
    \\ gvs [evaluate_def,do_opapp_def]
    \\ gvs [state_component_equality])
  \\ gvs []
  \\ last_x_assum drule
  \\ rename [‘App Opapp [x'; x]’]
  \\ disch_then $ qspec_then ‘App Opapp [x'; x]’ mp_tac
  \\ gvs [evaluate_def,do_opapp_def]
  \\ rename [‘Funs t _’]
  \\ Cases_on ‘t’ \\ gvs [Funs_def,evaluate_def,dec_clock_def]
  \\ disch_then irule
  \\ qrefinel [‘_’,‘_ :: _’] \\ gvs []
  \\ rpt $ irule_at Any EQ_REFL \\ gvs []
QED

Theorem evaluate_Apps:
  ∀xs (st:'ffi state) env s1 s2 vs.
    evaluate st env xs = (s1,Rval vs) ∧
    LENGTH xs = SUC (LENGTH ns) ∧
    nsLookup env.v n = SOME clos_v ∧
    do_opapp [clos_v; LAST vs] = SOME (env1,Funs ns e) ⇒
    evaluate st env [Apps (Var n) (REVERSE xs)] =
    if s1.clock < LENGTH xs then
      (s1 with clock := 0,Rerr (Rabort Rtimeout_error))
    else
      evaluate
        (s1 with clock := s1.clock - LENGTH xs)
        (env1 with v := nsAppend (alist_to_ns (ZIP (REVERSE ns,BUTLAST vs))) env1.v) [e]
Proof
  Cases using SNOC_CASES \\ gvs [REVERSE_SNOC,Apps_def]
  \\ simp [Once SNOC_APPEND]
  \\ simp [evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ rpt strip_tac
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ Cases_on ‘ns = []’
  \\ gvs [Apps_def]
  >-
   (gvs [evaluate_def]
    \\ Cases_on ‘s1.clock’
    \\ gvs [dec_clock_def,Funs_def]
    \\ gvs [state_component_equality])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ Cases_on ‘s1.clock < SUC (LENGTH ns)’ \\ gvs []
  >-
   (Cases_on ‘s1.clock’ \\ gvs []
    >- (irule evaluate_Apps_f_err \\ gvs [evaluate_def]
        \\ gvs [state_component_equality])
    \\ irule EQ_TRANS
    \\ irule_at Any evaluate_Apps_Funs_timeout \\ gvs []
    \\ gvs [evaluate_def]
    \\ Cases_on ‘ns’ \\ gvs [Funs_def,evaluate_def,dec_clock_def]
    \\ qrefinel [‘_ :: _’,‘_’] \\ gvs []
    \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  \\ rewrite_tac [GSYM SNOC_APPEND,FRONT_SNOC]
  \\ irule EQ_TRANS
  \\ irule_at (Pos hd) evaluate_Apps_Funs
  \\ last_x_assum $ irule_at Any
  \\ simp [evaluate_def]
  \\ namedCases_on ‘ns’ ["", "h t"] \\ gvs [Funs_def]
  \\ simp [evaluate_def]
  \\ qexists_tac ‘h::t’ \\ gvs []
  \\ irule_at (Pos hd) EQ_REFL
  \\ gvs [dec_clock_def,ADD1]
QED
