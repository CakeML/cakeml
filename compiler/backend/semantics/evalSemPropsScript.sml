(*
  Properties of evalSem. These are counterparts of properties of the
  source semantics (evaluateProps, semanticsProps).
*)
Theory evalSemProps
Ancestors
  evaluateProps[qualified] semanticPrimitives evalSem
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Theorem concrete_v_list[simp]:
  !xs. concrete_v_list xs = EVERY concrete_v xs
Proof
  Induct \\ simp [concrete_v_def]
QED

Theorem concrete_v_simps[simp]:
  (concrete_v (Litv l) = T) /\
  (concrete_v (Loc b n) = T) /\
  (concrete_v (Conv stmp xs) = EVERY concrete_v xs) /\
  (concrete_v (Vectorv xs) = EVERY concrete_v xs) /\
  (concrete_v (Env id e) = F) /\
  (concrete_v (Closure e2 nm x) = F) /\
  (concrete_v (Recclosure e3 funs nm2) = F)
Proof
  simp [concrete_v_def]
QED

Theorem compiler_agrees_concrete:
  compiler_agrees compiler (id,previous,decs) (compiler_value,bytes,words) ⇒
  concrete_v previous ∧ concrete_v compiler_value
Proof
  namedCases_on ‘compiler (id,previous,decs)’ ["","compiled"]
  >> simp [compiler_agrees_def]
  >> PairCases_on ‘compiled’
  >> namedCases_on ‘v_to_mlstring bytes’ ["","compiled_bytes"]
  >> namedCases_on ‘v_to_word64_list words’ ["","compiled_words"]
  >> simp [compiler_agrees_def]
QED

Theorem evaluate_add_to_clock_all:
  (∀(s:'ffi state) env es s' r.
     evaluate s env es = (s',r) ∧ r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate (s with clock := s.clock + extra) env es =
       (s' with clock := s'.clock + extra,r)) ∧
  (∀(s:'ffi state) env v pes err_v s' r.
     evaluate_match s env v pes err_v = (s',r) ∧
     r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_match (s with clock := s.clock + extra) env v pes err_v =
       (s' with clock := s'.clock + extra,r)) ∧
  (∀(s:'ffi state) env ds s' r.
     evaluate_decs s env ds = (s',r) ∧ r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_decs (s with clock := s.clock + extra) env ds =
       (s' with clock := s'.clock + extra,r))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw [full_evaluate_def]
  \\ gvs [AllCaseEqs(), dec_clock_def, do_eval_res_def]
  \\ qpat_x_assum ‘combine_dec_result _ _ ≠ _’ mp_tac
  \\ rename1 ‘combine_dec_result env1 r1 ≠ _ ⇒ _’
  \\ Cases_on ‘r1’
  \\ gvs [combine_dec_result_def]
QED

Theorem evaluate_io_events_prefix:
  (∀(s:'ffi state) env es s' r.
     evaluate s env es = (s',r) ⇒ s.ffi.io_events ≼ s'.ffi.io_events) ∧
  (∀(s:'ffi state) env v pes err_v s' r.
     evaluate_match s env v pes err_v = (s',r) ⇒
     s.ffi.io_events ≼ s'.ffi.io_events) ∧
  (∀(s:'ffi state) env ds s' r.
     evaluate_decs s env ds = (s',r) ⇒ s.ffi.io_events ≼ s'.ffi.io_events)
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw [full_evaluate_def]
  \\ gvs [dec_clock_def, do_eval_res_def, AllCaseEqs()]
  \\ imp_res_tac evaluatePropsTheory.do_app_io_events_mono
  \\ gvs [evaluatePropsTheory.io_events_mono_def]
  \\ metis_tac [IS_PREFIX_TRANS]
QED

Theorem do_eval_res_with_clock:
  do_eval_res vs (s with clock := c) =
    (FST (do_eval_res vs s) with clock := c, SND (do_eval_res vs s))
Proof
  rw [do_eval_res_def] \\ every_case_tac \\ gvs []
QED

Theorem do_eval_res_IMP:
  do_eval_res vs s = (s1,r) ⇒ s1.clock = s.clock ∧ s1.ffi = s.ffi
Proof
  rw [do_eval_res_def] \\ every_case_tac \\ gvs []
QED

Theorem do_eval_res_not_EvalRun:
  (∀r. s.eval_state ≠ SOME (EvalRun r)) ∧
  (∀r. s.eval_state ≠ SOME (EvalPending r)) ⇒
  do_eval_res vs s =
    case do_eval vs s.eval_state of
    | NONE => (s,Rerr (Rabort Rtype_error))
    | SOME (env1,decs,es1) =>
        (s with <| eval_state := es1
                 ; ptr_eq_oracle := shift_seq 1 s.ptr_eq_oracle |>,
         Rval (env1,decs))
Proof
  rw [do_eval_res_def] \\ every_case_tac \\ gvs []
QED

Theorem evaluate_add_to_clock_io_events_prefix:
  (∀(s:'ffi state) env es s1 r1 s2 r2.
     evaluate s env es = (s1,r1) ∧
     evaluate (s with clock := s.clock + extra) env es = (s2,r2) ⇒
     s1.ffi.io_events ≼ s2.ffi.io_events) ∧
  (∀(s:'ffi state) env v pes err_v s1 r1 s2 r2.
     evaluate_match s env v pes err_v = (s1,r1) ∧
     evaluate_match (s with clock := s.clock + extra) env v pes err_v = (s2,r2) ⇒
     s1.ffi.io_events ≼ s2.ffi.io_events) ∧
  (∀(s:'ffi state) env ds s1 r1 s2 r2.
     evaluate_decs s env ds = (s1,r1) ∧
     evaluate_decs (s with clock := s.clock + extra) env ds = (s2,r2) ⇒
     s1.ffi.io_events ≼ s2.ffi.io_events)
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw [full_evaluate_def]
  \\ gvs [dec_clock_def, do_eval_res_with_clock, AllCaseEqs()]
  \\ imp_res_tac do_eval_res_IMP
  \\ imp_res_tac evaluate_add_to_clock_all
  \\ gvs [do_eval_res_with_clock]
  \\ imp_res_tac evaluate_io_events_prefix
  \\ imp_res_tac IS_PREFIX_TRANS
  \\ gvs []
  \\ imp_res_tac evaluatePropsTheory.do_app_io_events_mono
  \\ gvs [evaluatePropsTheory.io_events_mono_def]
QED

Theorem evaluate_decs_add_to_clock:
   !(s:'ffi state) e p s' r extra.
   evaluate_decs s e p = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_decs (s with clock := s.clock + extra) e p =
   (s' with clock := s'.clock + extra,r)
Proof
  metis_tac [evaluate_add_to_clock_all]
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
  ∀ds1 (s:'ffi state) env ds2.
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

Theorem evaluate_decs_clock_determ:
 !(s:'ffi state) e p s1 r1 s2 r2 k1 k2.
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

Theorem evaluate_decs_ffi_mono_clock:
   ∀k1 k2 (s:'ffi state) e p.
    k1 ≤ k2 ⇒
    (FST (evaluate_decs (s with clock := k1) e p)).ffi.io_events ≼
    (FST (evaluate_decs (s with clock := k2) e p)).ffi.io_events
Proof
  rpt strip_tac
  \\ ‘∃extra. k2 = k1 + extra’ by (qexists_tac ‘k2 − k1’ \\ decide_tac)
  \\ gvs []
  \\ mp_tac (CONJUNCTS evaluate_add_to_clock_io_events_prefix |> last)
  \\ disch_then (qspecl_then [‘s with clock := k1’,‘e’,‘p’] mp_tac)
  \\ Cases_on ‘evaluate_decs (s with clock := k1) e p’
  \\ Cases_on ‘evaluate_decs (s with clock := k1 + extra) e p’
  \\ gvs []
QED

Theorem do_eval_init_NONE[simp]:
  do_eval_init vs NONE (:'a) = NONE
Proof
  simp [do_eval_init_def] \\ every_case_tac
QED

Theorem do_eval_fail_NONE[simp]:
  do_eval_fail vs NONE = NONE
Proof
  simp [do_eval_fail_def]
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
  \\ rpt (rpt gen_tac \\ disch_tac)
  \\ fs [full_evaluate_def]
  \\ rveq \\ fs []
  >~ [‘Case [App _ _]’] >- (
    Cases_on ‘op = ThunkOp ForceThunk’
    >- gvs [AllCaseEqs(), dec_clock_def]
    \\ Cases_on ‘op = PtrEq’
    >- gvs [AllCaseEqs()]
    \\ Cases_on ‘op = Eval’
    >- (
      gvs []
      \\ Cases_on ‘evaluate s env (REVERSE es')’
      \\ rename1 ‘evaluate s env (REVERSE es') = (st1,r1)’
      \\ Cases_on ‘r1’ \\ gvs []
      \\ qpat_x_assum ‘_ = (s',res)’ mp_tac
      \\ simp [do_eval_init_NONE, do_eval_fail_NONE, do_eval_res_def, do_eval_def])
    \\ Cases_on ‘op = Opapp’ \\ gs []
    \\ rpt (MAP_FIRST (dxrule_then (strip_assume_tac o SIMP_RULE bool_ss []))
      [hd (RES_CANON pair_case_eq), hd (RES_CANON result_case_eq),
       hd (RES_CANON bool_case_eq)])
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ fs [bool_case_eq, do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ rfs [Q.SPECL [`vs`, `NONE`] do_eval_def]
    \\ fs [dec_clock_def]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ COND_CASES_TAC \\ gs [])
  \\ fs [evaluatePropsTheory.evaluate_case_eqs]
  \\ rveq \\ fs []
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, evaluatePropsTheory.combine_dec_result_eq_Rerr,
         declare_env_def]
QED

(* top-level semantics *)

Theorem evaluate_prog_io_events_chain:
   lprefix_chain (IMAGE (λk. fromList (FST (evaluate_prog_with_clock
                                       (st:'ffi state) env k prog)).io_events) UNIV)
Proof
  qho_match_abbrev_tac`lprefix_chain (IMAGE (λk. fromList (g k)) UNIV)` >>
  ONCE_REWRITE_TAC[GSYM o_DEF] >>
  REWRITE_TAC[IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  srw_tac[][prefix_chain_def,Abbr`g`,evaluate_prog_with_clock_def] >> srw_tac[][] >>
  metis_tac[LESS_EQ_CASES,evaluate_decs_ffi_mono_clock,FST]
QED

Theorem semantics_determ_total:
   ∀(s:'ffi state) e p. ∃b. semantics_determ s e p b
Proof
  srw_tac[][] >>
  Cases_on`∃k. SND(evaluate_prog_with_clock s e k p) = Rerr (Rabort Rtype_error)`
  >- metis_tac[semantics_determ_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`∃k ffi r.
    evaluate_prog_with_clock s e k p = (ffi,r) ∧
    (r ≠ Rerr (Rabort Rtype_error)) ∧
    (r ≠ Rerr (Rabort Rtimeout_error))`
  >- (fs[semantics_determ_def]
      >> qexists_tac `Terminate
                      (case r of
                      | Rerr(Rabort(Rffi_error outcome)) => FFI_outcome outcome
                      | _ => Success) ffi.io_events`
      >> simp[semantics_determ_def] >> asm_exists_tac
      >> Cases_on `r` >> simp[]
      >> TOP_CASE_TAC >> simp[]
      >> TOP_CASE_TAC >> fs[]) >>
  qexists_tac`Diverge (build_lprefix_lub (IMAGE (λk. fromList (FST (evaluate_prog_with_clock s e k p)).io_events) UNIV))` >>
  simp[semantics_determ_def] >>
  conj_tac >- (
    strip_tac >> fs[] >>
    rpt(first_x_assum(qspec_then`k`mp_tac)) >>
    Cases_on`evaluate_prog_with_clock s e k p`>>simp[]>>
    Cases_on`r`>>simp[]>>
    Cases_on`e'`>>simp[]>>
    Cases_on`a`>>simp[]) >>
  match_mp_tac build_lprefix_lub_thm >>
  MATCH_ACCEPT_TAC evaluate_prog_io_events_chain
QED

Theorem evaluate_prog_with_clock_determ:
  evaluate_prog_with_clock (s:'ffi state) e k1 p = (ffi1,r1) ∧
  evaluate_prog_with_clock s e k2 p = (ffi2,r2) ∧
  r1 ≠ Rerr (Rabort Rtimeout_error) ∧ r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
  ffi1 = ffi2 ∧ r1 = r2
Proof
  simp [evaluate_prog_with_clock_def]
  \\ Cases_on ‘evaluate_decs (s with clock := k1) e p’
  \\ rename1 ‘_ = (t1,res1)’
  \\ Cases_on ‘evaluate_decs (s with clock := k2) e p’
  \\ rename1 ‘_ = (t2,res2)’
  \\ strip_tac
  \\ qspecl_then [‘s’,‘e’,‘p’,‘t1’,‘res1’,‘t2’,‘res2’,‘k1’,‘k2’] mp_tac
       evaluate_decs_clock_determ
  \\ gvs []
  \\ every_case_tac
  \\ gvs []
QED

Theorem evaluate_prog_with_clock_determ_SND:
  SND (evaluate_prog_with_clock (s:'ffi state) e k1 p) ≠ Rerr (Rabort Rtimeout_error) ∧
  SND (evaluate_prog_with_clock s e k2 p) ≠ Rerr (Rabort Rtimeout_error) ⇒
  evaluate_prog_with_clock s e k1 p = evaluate_prog_with_clock s e k2 p
Proof
  Cases_on ‘evaluate_prog_with_clock s e k1 p’
  \\ rename1 ‘_ = (ffi1,r1)’
  \\ Cases_on ‘evaluate_prog_with_clock s e k2 p’
  \\ rename1 ‘_ = (ffi2,r2)’
  \\ rpt strip_tac
  \\ mp_tac evaluate_prog_with_clock_determ
  \\ gvs []
QED

Theorem semantics_determ_deterministic:
   ∀(s:'ffi state) e p b b'.
    semantics_determ s e p b ∧
    semantics_determ s e p b' ⇒
    b = b'
Proof
  rw []
  \\ Cases_on ‘b’
  \\ Cases_on ‘b'’
  \\ fs [semantics_determ_def]
  >- metis_tac [unique_lprefix_lub]
  >- (
    qpat_x_assum ‘∀k. _’ (qspec_then ‘k’ strip_assume_tac)
    \\ gvs [])
  >- (
    qpat_x_assum ‘∀k. _’ (qspec_then ‘k’ strip_assume_tac)
    \\ gvs [])
  >- (
    qpat_x_assum ‘∀k. _’ (qspec_then ‘k’ strip_assume_tac)
    \\ gvs [])
  >- (
    fs [PAIR_FST_SND_EQ]
    \\ ‘SND (evaluate_prog_with_clock s e k p) ≠ Rerr (Rabort Rtimeout_error) ∧
        SND (evaluate_prog_with_clock s e k' p) ≠ Rerr (Rabort Rtimeout_error)’
      by (rpt strip_tac \\ gvs [])
    \\ mp_tac (Q.INST [‘k1’ |-> ‘k’, ‘k2’ |-> ‘k'’] evaluate_prog_with_clock_determ_SND)
    \\ simp []
    \\ strip_tac
    \\ gvs []
    \\ every_case_tac
    \\ gvs [])
  >- (
    fs [PAIR_FST_SND_EQ]
    \\ ‘SND (evaluate_prog_with_clock s e k p) ≠ Rerr (Rabort Rtimeout_error) ∧
        SND (evaluate_prog_with_clock s e k' p) ≠ Rerr (Rabort Rtimeout_error)’
      by (rpt strip_tac \\ gvs [])
    \\ mp_tac (Q.INST [‘k1’ |-> ‘k’, ‘k2’ |-> ‘k'’] evaluate_prog_with_clock_determ_SND)
    \\ simp []
    \\ strip_tac
    \\ gvs []
    \\ every_case_tac
    \\ gvs [])
  >- (
    qpat_x_assum ‘∀k. _’ (qspec_then ‘k’ strip_assume_tac)
    \\ gvs [])
  \\ fs [PAIR_FST_SND_EQ]
  \\ ‘SND (evaluate_prog_with_clock s e k p) ≠ Rerr (Rabort Rtimeout_error) ∧
      SND (evaluate_prog_with_clock s e k' p) ≠ Rerr (Rabort Rtimeout_error)’
    by (rpt strip_tac \\ gvs [])
  \\ mp_tac (Q.INST [‘k1’ |-> ‘k’, ‘k2’ |-> ‘k'’] evaluate_prog_with_clock_determ_SND)
  \\ simp []
  \\ strip_tac
  \\ gvs []
  \\ every_case_tac
  \\ gvs []
QED

(* if every run of p is matched by a run of p' given some extra clock,
   then p' has the same semantics as p *)
Theorem semantics_determ_clock_extra:
  ¬semantics_determ (s:'ffi state) env p Fail ∧
  (∀k. SND (evaluate_prog_with_clock s env k p) ≠ Rerr (Rabort Rtype_error) ⇒
       ∃ck. evaluate_prog_with_clock (s':'ffi state) env' (k + ck) p' =
            evaluate_prog_with_clock s env k p) ⇒
  semantics_determ s' env' p' = semantics_determ s env p
Proof
  strip_tac
  \\ ‘∀b. semantics_determ s env p b ⇒ semantics_determ s' env' p' b’
    suffices_by (
      rw [FUN_EQ_THM]
      \\ eq_tac
      >- (
        strip_tac
        \\ qspecl_then [‘s’,‘env’,‘p’] strip_assume_tac semantics_determ_total
        \\ metis_tac [semantics_determ_deterministic])
      \\ metis_tac [])
  \\ ‘∀k. SND (evaluate_prog_with_clock s env k p) ≠ Rerr (Rabort Rtype_error)’
    by (CCONTR_TAC \\ gvs [semantics_determ_def] \\ metis_tac [])
  \\ Cases
  >~ [‘semantics_determ _ _ _ Fail ⇒ _’] >- gvs []
  >~ [‘Terminate’] >- (
    rw [semantics_determ_def]
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ first_x_assum (qspec_then ‘k’ mp_tac)
    \\ rw []
    \\ qexists_tac ‘k + ck’
    \\ gvs [])
  \\ rw [semantics_determ_def]
  >- (
    qpat_x_assum ‘∀k. _ ⇒ ∃ck. _’ (qspec_then ‘k’ mp_tac)
    \\ impl_tac >- simp []
    \\ strip_tac
    \\ first_x_assum (qspec_then ‘k’ strip_assume_tac)
    \\ gvs [evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ CCONTR_TAC
    \\ qpat_x_assum ‘evaluate_decs (s' with clock := k) _ _ = _’ assume_tac
    \\ drule_then (qspec_then ‘ck’ mp_tac) evaluate_decs_add_to_clock
    \\ simp [])
  \\ irule lprefix_lub_new_chain
  \\ qpat_assum ‘lprefix_lub _ _’ $ irule_at Any
  \\ conj_tac >- simp [evaluate_prog_io_events_chain]
  \\ irule IMP_equiv_lprefix_chain
  \\ simp [evaluate_prog_io_events_chain, lprefix_rel_def, PULL_EXISTS]
  \\ rw []
  >- (
    qpat_x_assum ‘∀k. _ ⇒ ∃ck. _’ (qspec_then ‘k’ mp_tac)
    \\ impl_tac >- fs []
    \\ strip_tac
    \\ qexists_tac ‘k + ck’
    \\ pop_assum SUBST1_TAC
    \\ simp [])
  \\ qpat_x_assum ‘∀k. _ ⇒ ∃ck. _’ (qspec_then ‘k’ mp_tac)
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ qexists_tac ‘k’
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ simp [evaluate_prog_with_clock_def, LPREFIX_fromList, ELIM_UNCURRY,
           from_toList]
  \\ irule evaluate_decs_ffi_mono_clock
  \\ simp []
QED

Theorem semantics_determ_SUBSET_semantics:
  semantics_determ ((s:'ffi state) with ptr_eq_oracle := po) env prog ⊆
  semantics s env prog
Proof
  rw [SUBSET_DEF, IN_DEF, semantics_def]
  \\ first_x_assum $ irule_at Any
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

Theorem do_eval_res_clock:
  (FST (do_eval_res vs s)).clock = s.clock
Proof
  Cases_on ‘do_eval_res vs s’
  \\ imp_res_tac do_eval_res_IMP
  \\ simp []
QED

Theorem evaluate_known_value_list:
  ∀es vs.
    LIST_REL (λe v. ∀s:'ffi state.
      evaluate s env [e] = (s,Rval [v])) es vs ⇒
    ∀s:'ffi state. evaluate s env es = (s,Rval vs)
Proof
  Induct_on ‘es’
  >- simp [evaluate_def]
  >> qx_genl_tac [‘e’,‘vs’]
  >> namedCases_on ‘vs’ ["","value values"]
  >> simp []
  >> strip_tac
  >> qpat_x_assum ‘∀vs. LIST_REL _ es vs ⇒ _’
       (qspec_then ‘values’ mp_tac)
  >> simp []
  >> strip_tac
  >> Cases_on ‘es’
  >> gvs [evaluate_def,fix_clock_def]
QED

Theorem evaluate_let_known_value:
  evaluate (s:'ffi state) env [rhs] = (s,Rval [value]) ⇒
  evaluate s env [Let (SOME name) rhs body] =
  evaluate s (env with v := nsBind name value env.v) [body]
Proof
  strip_tac
  >> simp [cj 13 evaluate_def,namespaceTheory.nsOptBind_def]
QED

Theorem evaluate_letrec_distinct:
  ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ⇒
  evaluate (s:'ffi state) env [Letrec funs body] =
  evaluate s (env with v := build_rec_env funs env env.v) [body]
Proof
  simp [evaluate_def]
QED

Theorem evaluate_letrec_duplicate:
  ¬ALL_DISTINCT (MAP FST funs) ⇒
  evaluate (s:'ffi state) env [Letrec funs body] =
    (s,Rerr (Rabort Rtype_error))
Proof
  strip_tac
  >> simp_tac (srw_ss()) [cj 14 evaluate_def,ELIM_UNCURRY,ETA_AX]
  >> simp []
QED

(* ------------------------------------------------------------------ *
   The pointer equality oracle of the source semantics: without an eval
   state, evaluation only consumes entries of the current epoch. The
   compiler closure runs that way, so closure_ptr_eq is the oracle after
   such a run.
 * ------------------------------------------------------------------ *)

Theorem skip_ptr_eq_0[simp]:
  skip_ptr_eq 0 po = po
Proof
  rw [evaluateTheory.skip_ptr_eq_def, FUN_EQ_THM, APPLY_UPDATE_THM,
      miscTheory.shift_seq_def]
  \\ rw [FUN_EQ_THM]
QED

Theorem skip_ptr_eq_skip_ptr_eq[simp]:
  skip_ptr_eq a (skip_ptr_eq b po) = skip_ptr_eq (a + b) po
Proof
  rw [evaluateTheory.skip_ptr_eq_def, FUN_EQ_THM, APPLY_UPDATE_THM,
      miscTheory.shift_seq_def]
  \\ rw [FUN_EQ_THM]
QED

Theorem ptr_eq_step_skip_ptr_eq:
  (0 =+ shift_seq 1 (po 0)) po = skip_ptr_eq 1 po
Proof
  simp [evaluateTheory.skip_ptr_eq_def]
QED

Theorem shift_seq_skip_ptr_eq[simp]:
  shift_seq 1 (skip_ptr_eq k po) = shift_seq 1 po
Proof
  rw [evaluateTheory.skip_ptr_eq_def, FUN_EQ_THM, APPLY_UPDATE_THM,
      miscTheory.shift_seq_def]
QED

Theorem evaluate_eval_state_NONE_ptr_eq:
  (∀(s:'ffi semanticPrimitives$state) env es s' res.
     evaluate$evaluate s env es = (s',res) ∧ s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     ∃k. s'.ptr_eq_oracle = skip_ptr_eq k s.ptr_eq_oracle) ∧
  (∀(s:'ffi semanticPrimitives$state) env v pes err_v s' res.
     evaluate$evaluate_match s env v pes err_v = (s',res) ∧
     s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     ∃k. s'.ptr_eq_oracle = skip_ptr_eq k s.ptr_eq_oracle) ∧
  (∀(s:'ffi semanticPrimitives$state) env ds s' res.
     evaluate$evaluate_decs s env ds = (s',res) ∧ s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     ∃k. s'.ptr_eq_oracle = skip_ptr_eq k s.ptr_eq_oracle)
Proof
  ho_match_mp_tac evaluateTheory.full_evaluate_ind
  \\ rw [evaluateTheory.full_evaluate_def]
  >>~- ([‘op = Opapp’],
    qpat_x_assum ‘∀s' res. evaluate s env (REVERSE es) = _ ∧ _ ⇒ _’ mp_tac
    \\ Cases_on ‘evaluate s env (REVERSE es)’
    \\ rename1 ‘evaluate s env (REVERSE es) = (st1,r1)’
    \\ simp [] \\ strip_tac
    \\ reverse (Cases_on ‘r1’) >- (gvs [] \\ metis_tac [])
    \\ gvs []
    \\ Cases_on ‘op = Opapp’
    >- (gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
        \\ metis_tac [skip_ptr_eq_skip_ptr_eq, skip_ptr_eq_0])
    \\ Cases_on ‘op = ThunkOp ForceThunk’
    >- (gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
        \\ metis_tac [skip_ptr_eq_skip_ptr_eq, skip_ptr_eq_0])
    \\ Cases_on ‘op = Eval’
    >- (gvs [AllCaseEqs(), evaluateTheory.do_eval_res_def,
             evaluatePropsTheory.do_eval_NONE]
        \\ metis_tac [skip_ptr_eq_skip_ptr_eq, skip_ptr_eq_0])
    \\ Cases_on ‘op = PtrEq’
    >- (gvs [AllCaseEqs(), ptr_eq_step_skip_ptr_eq]
        \\ metis_tac [skip_ptr_eq_skip_ptr_eq, skip_ptr_eq_0])
    \\ gvs [AllCaseEqs()]
    \\ metis_tac [skip_ptr_eq_skip_ptr_eq, skip_ptr_eq_0])
  \\ gvs [AllCaseEqs(), semanticPrimitivesTheory.declare_env_def,
          evaluateTheory.dec_clock_def]
  \\ metis_tac [skip_ptr_eq_0]
QED

Theorem evaluate_clock_0_unique[local]:
  evaluate$evaluate (s with clock := ck1) env es = (s1,r1) ∧ s1.clock = 0 ∧
  r1 ≠ Rerr (Rabort Rtimeout_error) ∧
  evaluate$evaluate (s with clock := ck2) env es = (s2,r2) ∧ s2.clock = 0 ∧
  r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
  s1 = s2 ∧ r1 = r2
Proof
  strip_tac
  \\ Cases_on ‘ck1 ≤ ck2’
  >- (
    qpat_x_assum ‘evaluate (s with clock := ck1) _ _ = _’ assume_tac
    \\ drule_then (qspec_then ‘ck2 - ck1’ mp_tac)
         evaluatePropsTheory.evaluate_add_to_clock
    \\ gvs [] \\ strip_tac
    \\ gvs [semanticPrimitivesTheory.state_component_equality])
  \\ qpat_x_assum ‘evaluate (s with clock := ck2) _ _ = _’ assume_tac
  \\ drule_then (qspec_then ‘ck1 - ck2’ mp_tac)
       evaluatePropsTheory.evaluate_add_to_clock
  \\ gvs [] \\ strip_tac
  \\ gvs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem closure_ptr_eq_thm:
  do_opapp [cl; arg] = SOME (env,exp) ∧ r ≠ Rerr (Rabort Rtimeout_error) ∧
  (∀(s:'ffi semanticPrimitives$state).
     s.eval_state = NONE ∧ s.refs = refs ∧ s.ptr_eq_oracle = po ⇒
     evaluate$evaluate (s with clock := ck) env [exp] =
       (s with <| clock := 0; refs := refs ++ refs';
                  ptr_eq_oracle := po' |>, r)) ⇒
  closure_ptr_eq cl arg refs po (:'ffi) = po'
Proof
  rw [closure_ptr_eq_def]
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- metis_tac []
  \\ rpt strip_tac \\ gvs []
  \\ qabbrev_tac ‘s0 = <| clock := 0; refs := refs; ffi := ARB;
                          next_type_stamp := 0; next_exn_stamp := 0;
                          eval_state := NONE; ptr_eq_oracle := po;
                          eval_oracle := ARB |> : 'ffi semanticPrimitives$state’
  \\ ‘s0.eval_state = NONE ∧ s0.refs = refs ∧ s0.ptr_eq_oracle = po’
    by simp [Abbr ‘s0’]
  \\ last_x_assum drule_all \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ mp_tac (SPEC_ALL evaluate_clock_0_unique
             |> INST_TYPE [alpha |-> “:'ffi”]
             |> Q.INST [‘s’ |-> ‘s0’, ‘ck1’ |-> ‘ck’, ‘ck2’ |-> ‘ck'’,
                        ‘es’ |-> ‘[exp]’,
                        ‘s1’ |-> ‘s0 with <| clock := 0; refs := refs ++ refs';
                                             ptr_eq_oracle := po' |>’,
                        ‘s2’ |-> ‘s0 with <| clock := 0; refs := refs ++ refs'';
                                             ptr_eq_oracle := x |>’,
                        ‘r1’ |-> ‘r’, ‘r2’ |-> ‘r'’])
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

Theorem compiler_reach_trans:
  ∀comp st1 st2. compiler_reach comp st1 st2 ⇒
                 ∀st0. compiler_reach comp st0 st1 ⇒ compiler_reach comp st0 st2
Proof
  ntac 2 gen_tac \\ ho_match_mp_tac compiler_reach_ind \\ rw []
  \\ metis_tac [compiler_reach_step]
QED

Theorem compiler_closure_reach:
  compiler_closure comp dec st0 cl (:'ffi) ∧ compiler_reach comp st0 st1 ⇒
  compiler_closure comp dec st1 cl (:'ffi)
Proof
  rw [compiler_closure_def]
  \\ first_x_assum irule \\ simp []
  \\ irule compiler_reach_trans \\ first_x_assum $ irule_at Any \\ simp []
QED

Theorem compiler_closure_ptr_eq:
  compiler_closure comp dec st0 cl (:'ffi) ∧ compiler_reach comp st0 st_v ∧
  data_v st_v ∧ data_v decs_v ∧ dec decs_v = SOME decs ⇒
  ∃k. closure_ptr_eq cl
        (Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id]; st_v; decs_v])
        refs po (:'ffi) = skip_ptr_eq k po
Proof
  rw [compiler_closure_def]
  \\ first_x_assum (qspecl_then [‘gen’,‘id’,‘st_v’,‘decs_v’,‘decs’] mp_tac)
  \\ simp [] \\ strip_tac
  \\ first_x_assum (qspecl_then [‘refs’,‘po’] strip_assume_tac)
  \\ ‘r ≠ Rerr (Rabort Rtimeout_error)’
    by (Cases_on ‘comp ((gen,id),st_v,decs)’ \\ gvs []
        \\ rename1 ‘_ = SOME x’ \\ PairCases_on ‘x’ \\ gvs [])
  \\ drule_all closure_ptr_eq_thm \\ strip_tac \\ simp []
  \\ qabbrev_tac ‘s0 = <| clock := ck; refs := refs; ffi := ARB;
                          next_type_stamp := 0; next_exn_stamp := 0;
                          eval_state := NONE; ptr_eq_oracle := po;
                          eval_oracle := ARB |> : 'ffi semanticPrimitives$state’
  \\ first_x_assum (qspec_then ‘s0’ mp_tac)
  \\ simp [Abbr ‘s0’] \\ strip_tac
  \\ drule (CONJUNCT1 evaluate_eval_state_NONE_ptr_eq) \\ simp []
QED
