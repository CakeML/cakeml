(*
  Theorems about the clocked big-step semantics. Primarily that they
  are total, and that they have the proper relationship to the
  unclocked version.
*)

open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory determTheory;
open semanticPrimitivesPropsTheory;
open boolSimps;

val _ = new_theory "bigClock";

val evaluate_ind = bigStepTheory.evaluate_ind;
val _ = bring_to_front_overload"evaluate_decs"{Name="evaluate_decs",Thy="bigStep"};

val s = ``s:'ffi state``
val s' = ``s':'ffi state``

Theorem big_unclocked_unchanged[local]:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock)
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >> fs[do_app_cases] >> rw [] >> fs [] >>
  every_case_tac >> fs[] >> rveq >> fs[]
QED

Triviality lemma:
  ((s with clock := c) with <| refs := r; ffi := io |>) =
  s with <| clock := c; refs := r; ffi := io |>
Proof
  rw []
QED

Theorem with_clock_refs:
  !ck. (s with clock := ck).refs = s.refs
Proof
  fs []
QED

Theorem big_unclocked_ignore:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !count st' r.
       r1 = (st', r) ∧
       r ≠ Rerr (Rabort Rtimeout_error)
       ⇒
       evaluate F env (s with clock := count) e (st' with clock := count, r)) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !count st' r.
       r1 = (st', r) ∧
       r ≠ Rerr (Rabort Rtimeout_error)
       ⇒
       evaluate_list F env (s with clock := count) es (st' with clock := count, r)) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !count st' r.
       r1 = (st', r) ∧
       r ≠ Rerr (Rabort Rtimeout_error)
       ⇒
       evaluate_match F env (s with clock := count) v pes err_v (st' with clock := count, r))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  rw [Once evaluate_cases]>>
  fs [] >>
  rw [] >>
  TRY (disj1_tac >>
       qexists_tac `vs` >>
       qexists_tac `s2 with clock := count'` >>
       rw [] >>
       NO_TAC) >>
  rfs [] >>
  metis_tac [with_clock_refs]
QED

Theorem with_clock_with_clock[local]:
  (s with clock := a) with clock := b = (s with clock := b)
Proof
  rw [state_component_equality]
QED

Theorem big_unclocked:
  !s env e s' r count1 count2.
    (evaluate F env ^s e (s', r)
     ⇒
     r ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = s'.clock) ∧
    (evaluate F env (^s with clock := count1) e (s' with clock := count1, r)
     ⇒
     evaluate F env (^s with clock := count2) e (s' with clock := count2, r))
Proof
  rw [] >>
  metis_tac [big_unclocked_ignore, big_unclocked_unchanged, FST, SND, with_clock_with_clock]
QED

Theorem add_to_counter:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !s' r' extra.
       (r1 = (s',r')) ∧
       (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
       (ck = T) ⇒
       evaluate T env (s with clock := s.clock+extra) e ((s' with clock := s'.clock+extra),r')) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r' extra.
       (r1 = (s',r')) ∧
       (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
       (ck = T) ⇒
       evaluate_list T env (s with clock := s.clock+extra) es ((s' with clock := s'.clock+extra),r')) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !s' r' extra.
       (r1 = (s',r')) ∧
       (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
       (ck = T) ⇒
       evaluate_match T env (s with clock := s.clock+extra) v pes err_v ((s' with clock := s'.clock+extra),r'))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >> rw [Once evaluate_cases] >>
  fs[] >> rfs[] >>
  TRY (metis_tac[with_clock_refs]) >>
  disj1_tac >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``evaluate_list`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o (snd o strip_forall o concl)) >>
  simp[] >>
  fsrw_tac[ARITH_ss][] >>
  `extra + s2.clock - 1 = s2.clock -1 + extra` by DECIDE_TAC >>
  metis_tac []
QED

Triviality with_clock_clock:
  (s with clock := a).clock = a
Proof
  rw[]
QED

Theorem add_clock[local]:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = F) ⇒
       ∃c. evaluate T env (s with clock := c) e (s' with clock := 0,r')) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = F) ⇒
       ∃c. evaluate_list T env (s with clock := c) es (s' with clock := 0,r')) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = F) ⇒
       ∃c. evaluate_match T env (s with clock := c) v pes err_v (s' with clock := 0,r'))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  rw [Once evaluate_cases] >>
  srw_tac[DNF_ss][] >> fs[] >>
  TRY(fs[state_component_equality]>>NO_TAC) >>
  TRY (
    srw_tac[DNF_ss][] >> disj1_tac >>
    imp_res_tac (CONJUNCT1 (CONJUNCT2 add_to_counter)) >> fs[] >>
    first_x_assum(qspec_then`c+1`strip_assume_tac)>>
    first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC) >>
  TRY (
    srw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``evaluate_list`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC) >>
  metis_tac [add_to_counter, with_clock_with_clock, with_clock_clock,
             arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_0, with_clock_refs,
             result_distinct, error_result_distinct, result_11]
QED

Theorem clock_monotone[local]:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = T) ⇒
       (s'.clock ≤ s.clock)) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = T) ⇒
       (s'.clock ≤ s.clock)) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !s' r'.
       (r1 = (s',r')) ∧
       (ck = T) ⇒
       (s'.clock ≤ s.clock))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  rw [Once evaluate_cases] >>
  full_simp_tac (srw_ss()++ARITH_ss) []
QED

Triviality with_same_clock:
  (s with clock := s.clock) = s
Proof
  rw[state_component_equality]
QED

Theorem big_clocked_unclocked_equiv:
  !s env e s' r1.
    evaluate F env s e (s', r1) =
    ?c. evaluate T env (s with clock := c) e (s' with clock := 0,r1) ∧
        (r1 ≠ Rerr (Rabort Rtimeout_error)) ∧
        (s.clock = s'.clock)
Proof
  metis_tac [with_clock_clock, with_same_clock, add_clock,
             big_unclocked_ignore, big_unclocked]
QED

Triviality wf_lem:
  WF (($< :(num->num->bool)) LEX measure exp_size)
Proof
  rw [] >>
  match_mp_tac WF_LEX >>
  rw [prim_recTheory.WF_LESS]
QED

Theorem ind[local] =
  SIMP_RULE (srw_ss()) [wf_lem] (Q.ISPEC `(($< :(num->num->bool)) LEX measure exp_size)` WF_INDUCTION_THM);

Theorem eval_list_total[local]:
  ∀^s env l i count'.
  (∀p_1 p_2.
     p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Con i l) ⇒
     ∀^s' env'.
    ∃s1 r1.
      evaluate T env' (s' with clock := p_1) p_2 (s1,r1))
  ⇒
  ?s2 r2. evaluate_list T env (s with clock := count') l (s2,r2)
Proof
  induct_on `l` >>
  rw [] >>
  ONCE_REWRITE_TAC [evaluate_cases] >>
  rw [] >>
  `exp_size h < exp_size (Con i (h::l)) ∧
  exp_size (Con i l) < exp_size (Con i (h::l))`
    by srw_tac [ARITH_ss] [exp_size_def] >>
  `?s1 r1. evaluate T env (s with clock := count') h (s1,r1)`
    by metis_tac [] >>
  `?s2 r2. evaluate_list T env s1 l (s2,r2)`
    by metis_tac [clock_monotone, with_clock_clock, with_same_clock, LESS_OR_EQ, LESS_TRANS] >>
  metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]
QED

Theorem eval_list_total_app[local]:
  ∀^s env es i count'.
  (∀p_1 p_2.
     p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (App op es) ⇒
     ∀^s' env'.
    ∃s1 r1.
      evaluate T env' (s' with clock := p_1) p_2 (s1,r1))
  ⇒
  ?s2 r2. evaluate_list T env (s with clock := count') es (s2,r2)
Proof
  induct_on `es` >>
  rw [] >>
  ONCE_REWRITE_TAC [evaluate_cases] >>
  rw [] >>
  `exp_size h < exp_size (App op (h::es)) ∧
   exp_size (App op es) < exp_size (App op (h::es))`
    by srw_tac [ARITH_ss] [exp_size_def] >>
  `?s1 r1. evaluate T env (s with clock := count') h (s1,r1)`
    by metis_tac [] >>
  `?s2 r2. evaluate_list T env s1 es (s2,r2)`
    by metis_tac [clock_monotone, LESS_OR_EQ, LESS_TRANS, with_clock_clock, with_same_clock] >>
  metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]
QED

Theorem eval_match_total[local]:
  ∀^s env l i count' v err_v.
  (∀p_1 p_2.
     p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Mat e' l) ⇒
     ∀^s env.
    ∃s' r.
      evaluate T env (s with clock := p_1) p_2 (s',r)) ∧
  s.clock ≤ count'
  ⇒
  ?s2 r2. evaluate_match T env s v l err_v (s2,r2)
Proof
  induct_on `l` >>
  rw [] >>
  ONCE_REWRITE_TAC [evaluate_cases] >>
  rw [] >>
  `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
  rw [] >>
  `exp_size e < exp_size (Mat e' ((p,e)::l)) ∧
  exp_size (Mat e' l) < exp_size (Mat e' ((p,e)::l))`
    by srw_tac [ARITH_ss] [exp_size_def] >>
  fs [] >>
  rw [] >>
  `(pmatch env.c s.refs p v [] = Match_type_error) ∨
  (pmatch env.c s.refs p v [] = No_match) ∨
  (?env'. pmatch env.c s.refs p v [] = Match env')`
    by metis_tac [match_result_nchotomy] >>
  rw [] >>
  metis_tac [LESS_TRANS,LESS_OR_EQ,with_same_clock]
QED

Theorem eval_handle_total[local]:
  ∀env ^s l i count' v err_v.
    (∀p_1 p_2.
       p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Handle e' l) ⇒
       ∀^s env.
      ∃s' r.
        evaluate T env (s with clock := p_1) p_2 (s',r)) ∧
    s.clock ≤ count'
    ⇒
    ?s2 r2. evaluate_match T env s v l err_v (s2,r2)
Proof
  induct_on `l` >>
  rw [] >>
  ONCE_REWRITE_TAC [evaluate_cases] >>
  rw [] >>
  `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
  rw [] >>
  `exp_size e < exp_size (Handle e' ((p,e)::l)) ∧
  exp_size (Handle e' l) < exp_size (Handle e' ((p,e)::l))`
    by srw_tac [ARITH_ss] [exp_size_def] >>
  rw [] >>
  fs [] >>
  `(pmatch env.c s.refs p v [] = Match_type_error) ∨
  (pmatch env.c s.refs p v [] = No_match) ∨
  (?env'. pmatch env.c s.refs p v [] = Match env')`
    by metis_tac [match_result_nchotomy] >>
  rw [] >>
  metis_tac [arithmeticTheory.LESS_TRANS,
             LESS_OR_EQ,with_same_clock]
QED

Theorem evaluate_raise_empty_ctor[local]:
  !ck s env x cn.
    ?err. evaluate ck env s (Raise (Con cn [])) (s, Rerr err)
Proof
  ntac 5 (rw [Once evaluate_cases]) >>
  every_case_tac >>
  rw [] >>
  metis_tac [do_con_check_build_conv]
QED

Triviality exp6_size_rev:
  !es. exp6_size (REVERSE es) = exp6_size es
Proof
  RW_TAC std_ss [GSYM exps_size_def, exps_size_thm] >>
  rw [rich_listTheory.MAP_REVERSE, rich_listTheory.SUM_REVERSE]
QED

Theorem big_clocked_total_lem[local]:
  !count_e env s.
    ∃s' r. evaluate T env (s with clock := FST count_e) (SND count_e) (s', r)
Proof
  ho_match_mp_tac ind >>
  rw [] >>
  `?count e. count_e = (count,e)` by (PairCases_on `count_e` >> fs []) >>
  rw [] >>
  fs [Once FORALL_PROD, LEX_DEF_THM] >>
  cases_on `e` >>
  rw [Once evaluate_cases]
  >- ((* Raise *)
      `exp_size e' < exp_size (Raise e')` by srw_tac [ARITH_ss] [exp_size_def] >>
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES])
  >- ((* Handle *)
      `exp_size e' < exp_size (Handle e' l)` by srw_tac [ARITH_ss] [exp_size_def] >>
      rw [] >>
      `?s1 r1. evaluate T env (s with clock := count') e' (s1,r1)` by metis_tac [] >>
      `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
      rw []
      >- (cases_on `err` >>
          fs [] >-
          (`?s2 r2. evaluate_match T env s1 a l a (s2,r2)`
            by metis_tac[eval_handle_total,clock_monotone,with_clock_clock,with_clock_refs] >>
           metis_tac [with_clock_refs]) >-
          metis_tac [])
      >- metis_tac [])
  >- ((* Con *)
      `!i l. exp_size (Con i (REVERSE l)) = exp_size (Con i l)`
             by (rw [exp_size_def] >>
                 metis_tac [exp6_size_rev]) >>
      `?s2 r2. evaluate_list T env (s with clock := count') (REVERSE l) (s2,r2)`
                by metis_tac [eval_list_total] >>
      metis_tac [do_con_check_build_conv, result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES])
  >- ((* Var *)
      cases_on `nsLookup env.v i ` >>
          rw [])
  >- ((* App *)
      `!op es. exp_size (App op (REVERSE es)) = exp_size (App op es)`
             by (rw [exp_size_def] >>
                 metis_tac [exp6_size_rev]) >>
      `?s2 r2. evaluate_list T env (s with clock := count') (REVERSE l) (s2,r2)`
                by metis_tac [pair_CASES, eval_list_total_app] >>
      `(?err. r2 = Rerr err) ∨ (?v. r2 = Rval v)` by (cases_on `r2` >> metis_tac []) >>
      rw [] >-
      metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
      cases_on `o' = Opapp` >> rw[] >- (
        `(do_opapp (REVERSE v) = NONE) ∨ (?env' e2. do_opapp (REVERSE v) = SOME (env',e2))`
                   by metis_tac [optionTheory.option_nchotomy, pair_CASES] >-
        metis_tac[] >>
        cases_on `s2.clock = 0` >>
        rw [] >-
          metis_tac [pair_CASES] >>
        `s2.clock-1 < s2.clock` by srw_tac [ARITH_ss] [] >>
        metis_tac [pair_CASES, clock_monotone, LESS_OR_EQ, LESS_TRANS, with_clock_clock]) >>
      `(do_app (s2.refs,s2.ffi) o' (REVERSE v) = NONE) ∨
       (?s3 e2. do_app (s2.refs,s2.ffi) o' (REVERSE v) = SOME (s3,e2))`
                 by metis_tac [optionTheory.option_nchotomy, pair_CASES] >>
      metis_tac [pair_CASES] )
  >- ((* Log *)
      `exp_size e' < exp_size (Log l e' e0) ∧
       exp_size e0 < exp_size (Log l e' e0)`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      `?s1 r1. evaluate T env (s with clock := count') e' (s1,r1)`
             by metis_tac [] >>
      `?s2 r2. evaluate T env s1 e0 (s2,r2)`
             by metis_tac [with_same_clock, with_clock_clock, clock_monotone, LESS_OR_EQ] >>
      `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
      rw [] >-
      metis_tac [] >>
      `(do_log l v e0 = NONE) ∨ (?lit. do_log l v e0 = SOME (Val lit)) ∨ (do_log l v e0 = SOME (Exp e0))`
                 by (rw [do_log_def] >>
                     every_case_tac >> rw[]) >-
      metis_tac [] >-
      prove_tac [evaluate_rules] >>
      metis_tac [clock_monotone, with_clock_clock, LESS_OR_EQ])
  >- ((* If *)
      `exp_size e' < exp_size (If e' e0 e1) ∧
       exp_size e0 < exp_size (If e' e0 e1) ∧
       exp_size e1 < exp_size (If e' e0 e1)`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      `?s1 r1. evaluate T env (s with clock := count') e' (s1,r1)`
             by metis_tac [] >>
      `?s2 r2. evaluate T env s1 e0 (s2,r2)`
             by metis_tac [clock_monotone, with_clock_clock, with_same_clock, LESS_OR_EQ] >>
      `?s2 r2. evaluate T env s1 e1 (s2,r2)`
             by metis_tac [clock_monotone, with_same_clock, with_clock_clock, LESS_OR_EQ] >>
      `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
      rw [] >-
      metis_tac [] >>
      `(do_if v e0 e1 = NONE) ∨ (do_if v e0 e1 = SOME e0) ∨ (do_if v e0 e1 = SOME e1)`
                  by (rw [do_if_def]) >>
      metis_tac [])
  >- ((* match *)
      `exp_size e' < exp_size (Mat e' l)`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      `?s1 r1. evaluate T env (s with clock := count') e' (s1,r1)`
             by metis_tac [] >>
      `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
      rw [] >-
      metis_tac [] >>
      `?s2 r2. evaluate_match T env s1 v l bind_exn_v (s2,r2)`
                by (match_mp_tac eval_match_total >>
                    metis_tac [LESS_TRANS, with_same_clock, with_clock_clock,
                               clock_monotone, LESS_OR_EQ]) >>
      metis_tac [])
  >- ((* Let *)
     `exp_size e' < exp_size (Let o' e' e0) ∧
       exp_size e0 < exp_size (Let o' e' e0)`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES,
                 clock_monotone, with_clock_clock, with_same_clock, LESS_OR_EQ])
  >- ((* Letrec *)
      `exp_size e' < exp_size (Letrec l e')`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, with_clock_clock])
  >- ((* Tannot *)
     rw [exp_size_def])
  >- ((* Lannot *)
     rw [exp_size_def])
QED

Theorem big_clocked_total:
  !s env e.
    ∃s' r. evaluate T env s e (s', r)
Proof
  metis_tac [big_clocked_total_lem, FST, SND, with_same_clock]
QED

Theorem big_clocked_timeout_0:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !s'.
       (r1 = (s',Rerr (Rabort Rtimeout_error))) ∧
       (ck = T)
       ⇒
       (s'.clock = 0)) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !s'.
       (r1 = (s',Rerr (Rabort Rtimeout_error))) ∧
       (ck = T)
       ⇒
       (s'.clock = 0)) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !s'.
       (r1 = (s',Rerr (Rabort Rtimeout_error))) ∧
       (ck = T)
       ⇒
       (s'.clock = 0))
Proof
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  fs[do_app_cases] >>
  rw [] >>
  fs [] >>
  every_case_tac >> fs[] >> rveq >> fs[]
QED

Theorem big_clocked_unclocked_equiv_timeout:
  !s env e.
    (!r. ¬evaluate F env s e r) =
    (∀c. ?s'. evaluate T env (s with clock := c) e (s',Rerr (Rabort Rtimeout_error)) ∧ s'.clock = 0)
Proof
  rw [] >>
  eq_tac >>
  rw [] >|
  [`?s1 r1. evaluate T env (s with clock := c) e (s1,r1)`
     by metis_tac [big_clocked_total] >>
   metis_tac [big_unclocked_ignore, big_unclocked,big_clocked_timeout_0, with_clock_clock, with_same_clock,
              result_distinct,result_11, error_result_distinct,result_nchotomy, error_result_nchotomy],
   metis_tac [big_exp_determ, pair_CASES, PAIR_EQ, big_unclocked, add_clock]]
QED

Theorem sub_from_counter:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     !count count' s' r'.
       (s.clock = count+extra) ∧
       (r1 = (s',r')) ∧
       s'.clock = count' + extra ∧
       (ck = T) ⇒
       evaluate T env (s with clock := count) e (s' with clock := count',r')) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     !count count' s' r'.
       (s.clock = count+extra) ∧
       (r1 = (s',r')) ∧
       s'.clock = count' + extra ∧
       (ck = T) ⇒
       evaluate_list T env (s with clock := count) es (s' with clock := count',r')) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !count count' s' r'.
       (s.clock = count+extra) ∧
       (r1 = (s',r')) ∧
       s'.clock = count' + extra ∧
       (ck = T) ⇒
       evaluate_match T env (s with clock := count) v pes err_v (s' with clock := count',r'))
Proof
  ho_match_mp_tac evaluate_strongind >>
  rw [] >>
  rw [Once evaluate_cases] >>
  full_simp_tac (srw_ss()++ARITH_ss) [state_component_equality]
  >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``,
                                                                                           with_clock_refs]
  >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``,
                                                                                           with_clock_refs]
  >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``,
                                                                                           with_clock_refs]
  >- (fs [] >>
      disj1_tac >>
      CONV_TAC(STRIP_BINDER_CONV(SOME existential)(move_conj_left(can lhs))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      imp_res_tac clock_monotone >>
      fs [] >>
      `?count'''. s2.clock = count''' + extra`
        by (qexists_tac `s2.clock - extra` >>
            simp []) >>
      qexists_tac `s2 with clock := count'''` >>
      simp [])
  >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
  >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
  >- (fs [] >>
      disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >>
      qexists_tac `s2 with clock := count''` >>
      rw []) >>
  metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``,
                                                                                        with_clock_refs]
QED

Theorem clocked_min_counter:
  !s env e s' r'.
    evaluate T env s e (s',r')
    ⇒
    evaluate T env (s with clock := s.clock - s'.clock) e (s' with clock := 0, r')
Proof
  rw [] >>
  `s'.clock ≤ s.clock` by metis_tac [clock_monotone, PAIR_EQ, FST, SND, pair_CASES] >>
  `s'.clock = 0 + s'.clock ∧ s.clock = (s.clock - s'.clock) + s'.clock:num` by decide_tac >>
  metis_tac [sub_from_counter]
QED

val _ = export_theory ();
