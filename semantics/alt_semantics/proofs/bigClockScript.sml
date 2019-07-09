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

val big_unclocked_unchanged = Q.prove (
`(∀ck env ^s e r1.
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
     s.clock = (FST r1).clock)`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >> fs[do_app_cases] >> rw [] >> fs [] >>
 every_case_tac >> fs[] >> rveq >> fs[]);

val lemma = Q.prove (
`((s with clock := c) with <| refs := r; ffi := io |>) =
 s with <| clock := c; refs := r; ffi := io |>`,
 rw []);

val big_unclocked_ignore = Q.prove (
`(∀ck env ^s e r1.
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
       evaluate_match F env (s with clock := count) v pes err_v (st' with clock := count, r))`,
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
 metis_tac []);

val with_clock_with_clock = Q.prove (
`(s with clock := a) with clock := b = (s with clock := b)`,
 rw [state_component_equality]);

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
  TRY (metis_tac[]) >>
  disj1_tac >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``evaluate_list`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o (snd o strip_forall o concl)) >>
  simp[] >>
  fsrw_tac[ARITH_ss][] >>
  `extra + s2.clock - 1 = s2.clock -1 + extra` by DECIDE_TAC >>
  metis_tac []
QED

val with_clock_clock = Q.prove(
  `(s with clock := a).clock = a`,rw[]);

val add_clock = Q.prove (
  `(∀ck env ^s e r1.
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
     ∃c. evaluate_match T env (s with clock := c) v pes err_v (s' with clock := 0,r'))`,
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
             arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_0,
             result_distinct, error_result_distinct, result_11]);

val clock_monotone = Q.prove (
  `(∀ck env ^s e r1.
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
     (s'.clock ≤ s.clock))`,
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  rw [Once evaluate_cases] >>
  full_simp_tac (srw_ss()++ARITH_ss) []);

val with_same_clock = Q.prove(
  `(s with clock := s.clock) = s`,rw[state_component_equality])

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

val wf_lem = Q.prove (
  `WF (($< :(num->num->bool)) LEX measure exp_size)`,
  rw [] >>
  match_mp_tac WF_LEX >>
  rw [prim_recTheory.WF_LESS]);

val ind = SIMP_RULE (srw_ss()) [wf_lem] (Q.ISPEC `(($< :(num->num->bool)) LEX measure exp_size)` WF_INDUCTION_THM)

val eval_list_total = Q.prove (
  `∀^s env l i count'.
   (∀p_1 p_2.
       p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Con i l) ⇒
       ∀^s' env'.
         ∃s1 r1.
           evaluate T env' (s' with clock := p_1) p_2 (s1,r1))
   ⇒
   ?s2 r2. evaluate_list T env (s with clock := count') l (s2,r2)`,
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
  metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]);

val eval_list_total_app = Q.prove (
  `∀^s env es i count'.
  (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (App op es) ⇒
      ∀^s' env'.
        ∃s1 r1.
          evaluate T env' (s' with clock := p_1) p_2 (s1,r1))
  ⇒
  ?s2 r2. evaluate_list T env (s with clock := count') es (s2,r2)`,
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
  metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]);

val eval_match_total = Q.prove (
  `∀^s env l i count' v err_v.
    (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Mat e' l) ⇒
      ∀^s env.
        ∃s' r.
          evaluate T env (s with clock := p_1) p_2 (s',r)) ∧
    s.clock ≤ count'
   ⇒
   ?s2 r2. evaluate_match T env s v l err_v (s2,r2)`,
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
  metis_tac [LESS_TRANS,LESS_OR_EQ,with_same_clock]);

val eval_handle_total = Q.prove (
  `∀env ^s l i count' v err_v.
    (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Handle e' l) ⇒
      ∀^s env.
        ∃s' r.
          evaluate T env (s with clock := p_1) p_2 (s',r)) ∧
    s.clock ≤ count'
   ⇒
   ?s2 r2. evaluate_match T env s v l err_v (s2,r2)`,
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
             LESS_OR_EQ,with_same_clock]);

val evaluate_raise_empty_ctor = Q.prove (
`!ck s env x cn.
  ?err. evaluate ck env s (Raise (Con cn [])) (s, Rerr err)`,
 ntac 5 (rw [Once evaluate_cases]) >>
 every_case_tac >>
 rw [] >>
 metis_tac [do_con_check_build_conv]);

val exp6_size_rev = Q.prove (
`!es. exp6_size (REVERSE es) = exp6_size es`,
 RW_TAC std_ss [GSYM exps_size_def, exps_size_thm] >>
 rw [rich_listTheory.MAP_REVERSE, rich_listTheory.SUM_REVERSE]);

val big_clocked_total_lem = Q.prove (
  `!count_e env s.
    ∃s' r. evaluate T env (s with clock := FST count_e) (SND count_e) (s', r)`,
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
            by metis_tac[eval_handle_total,clock_monotone,with_clock_clock] >>
           metis_tac []) >-
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
     rw [exp_size_def]));

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
 >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
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
 metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
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

 (*
Theorem dec_evaluate_not_timeout:
 !mn s env d s' r.
  evaluate_dec F mn env s d (s', r) ⇒ r ≠ Rerr (Rabort Rtimeout_error)
Proof
rw [evaluate_dec_cases] >>
metis_tac [big_unclocked]
QED

Theorem dec_unclocked:
 !mn count s env d count' s' r.
  (evaluate_dec F mn env s d (s', r)
   ⇒
   (r ≠ Rerr (Rabort Rtimeout_error)) ∧
   s.clock = s'.clock) ∧
  (evaluate_dec F mn env (s with clock := count) d (s' with clock := count, r)
   =
   evaluate_dec F mn env (s with clock := count') d (s' with clock := count', r))
Proof
 rw [evaluate_dec_cases] >>
 rw [] >>
 fs [state_component_equality] >>
 metis_tac [big_unclocked]
QED

Theorem not_evaluate_dec_timeout:
 ∀mn env s d.
      (∀r. ¬evaluate_dec F mn env s d r) ⇒
      ∃r. evaluate_dec T mn env s d r ∧ (SND r = Rerr (Rabort Rtimeout_error))
Proof
  rpt gen_tac >>
  reverse(Cases_on`d`)>> simp[Once evaluate_dec_cases]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  rw[] >>
  rw[Once evaluate_dec_cases] >>
  fsrw_tac[DNF_ss][] >> rfs[] >> fs[] >>
  fs[] >>
  Cases_on`∃r. evaluate F env s e r` >- (
    fs[] >> PairCases_on`r`>>fs[] >>
    Cases_on`r1`>>fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >> res_tac >>
    metis_tac[match_result_nchotomy] ) >>
  fs [big_clocked_unclocked_equiv_timeout] >>
  metis_tac[with_same_clock]
QED

Theorem dec_clocked_total:
 ∀mn env s d. ∃res. evaluate_dec T mn env s d res
Proof
  rpt gen_tac >>
  reverse(Cases_on`d`)>>simp[Once evaluate_dec_cases] >>
  srw_tac[DNF_ss][] >- metis_tac[] >>
  qspecl_then[`s`,`env`,`e`]strip_assume_tac big_clocked_total >>
  Cases_on`r`>>metis_tac[match_result_nchotomy, pair_CASES]
QED

Theorem dec_clocked_min_counter:
 ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒
    ck ⇒ evaluate_dec ck mn env (s with clock := s.clock - (FST res).clock) d ((FST res) with clock := 0, SND res)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac clocked_min_counter >> rw[] >>
  srw_tac[DNF_ss][] >>
  TRY disj1_tac >>
  metis_tac []
QED

Theorem dec_clocked_unclocked_equiv:
 ∀mn env s1 s2 d r.
   evaluate_dec F mn env s1 d (s2,r) ⇔
   ∃c. evaluate_dec T mn env (s1 with clock := c) d (s2 with clock := 0,r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ∧ s1.clock = s2.clock
Proof
  Cases_on`d`>>simp[evaluate_dec_cases]>>rw[]>>
  fs[big_clocked_unclocked_equiv]>>
  srw_tac[DNF_ss][EQ_IMP_THM]>>
  simp [state_component_equality] >>
  fs [state_component_equality] >>
  metis_tac[]
QED

Theorem dec_sub_from_counter:
   ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒
      ∀extra count count' s' r.
         s.clock = count + extra ∧
         s'.clock = count' + extra ∧
         res = (s',r) ∧ ck ⇒
        evaluate_dec ck mn env (s with clock := count) d (s' with clock := count',r)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[evaluate_dec_cases] >>
  imp_res_tac sub_from_counter >> fs[] >>
  metis_tac[]
QED

Theorem dec_clock_monotone:
 ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒ ck ⇒ (FST res).clock ≤ s.clock
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  imp_res_tac clock_monotone >> fs[]
QED

Theorem dec_add_clock:
   ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒
      ∀s' r.
        res = (s',r) ∧ ¬ck ⇒
          ∃c. evaluate_dec T mn env (s with clock := c) d (s' with clock := 0, r)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac add_clock >> fs[] >>
  metis_tac[]
QED

Theorem dec_add_to_counter:
   ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒
      ∀r2 r3 extra.
         res = (r2,r3) ∧ ck ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_dec T mn env (s with clock := s.clock + extra) d (r2 with clock := r2.clock + extra,r3)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac add_to_counter >> fs[] >>
  metis_tac[]
QED

Theorem dec_unclocked_ignore:
   ∀ck mn env ^s d res. evaluate_dec ck mn env s d res ⇒
     ∀r2 r3 count.
       res = (r2,r3) ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
         evaluate_dec F mn env (s with clock := count) d (r2 with clock := count,r3)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac big_unclocked_ignore >> fs[] >>
  metis_tac[]
QED

Theorem decs_add_clock:
   ∀ck mn env ^s d res. evaluate_decs ck mn env s d res ⇒
     ∀r2 r3.
       res = (r2,r3) ∧ ¬ck ⇒
         ∃c. evaluate_decs T mn env (s with clock := c) d (r2 with clock := 0,r3)
Proof
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_add_clock >> fs[] >-
  metis_tac[] >>
  srw_tac[DNF_ss][] >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  CONV_TAC(STRIP_BINDER_CONV(SOME existential)(move_conj_left(same_const``evaluate_decs`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  imp_res_tac dec_add_to_counter >> fs[] >>
  metis_tac[]
QED

Theorem decs_evaluate_not_timeout:
   !ck mn env ^s ds r.
    evaluate_decs ck mn env s ds r ⇒
      !s' r'. ck = F ∧ r = (s', r') ⇒ r' ≠ Rerr (Rabort Rtimeout_error)
Proof
  ho_match_mp_tac evaluate_decs_ind >>
  rw [] >>
  rw []
  >- (CCONTR_TAC >>
      fs [] >>
      imp_res_tac dec_evaluate_not_timeout >>
      fs []) >>
  cases_on `r` >>
  rw [combine_dec_result_def]
QED

Theorem decs_unclocked:
   !mn c s env ds c' s' r.
    (evaluate_decs F mn env s ds (s',r)
     ⇒
     (r ≠ Rerr (Rabort Rtimeout_error)) ∧
     (s.clock = s'.clock)) ∧
    (evaluate_decs F mn env (s with clock := c)  ds (s' with clock := c,r)
     =
     evaluate_decs F mn env (s with clock := c') ds (s' with clock := c',r))
Proof
  induct_on `ds` >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC [evaluate_decs_cases] >>
  rw[]
  >- rw [state_component_equality]
  >- metis_tac [dec_unclocked]
  >- metis_tac [dec_unclocked]
  >- (res_tac >>
      cases_on `r'` >>
      rw [combine_dec_result_def])
  >- metis_tac [pair_CASES, dec_unclocked]
  >- (eq_tac >>
      rw [] >>
      metis_tac[dec_unclocked,with_clock_with_clock,with_clock_clock,with_same_clock])
QED

Theorem not_evaluate_decs_timeout:
   ∀mn env s ds.
    (∀r. ¬evaluate_decs F mn env s ds r) ⇒
    ∃r. evaluate_decs T mn env s ds r ∧ (SND r = Rerr (Rabort Rtimeout_error))
Proof
  Induct_on`ds` >- ( simp[Once evaluate_decs_cases] ) >>
  rpt gen_tac >>
  simp[Once evaluate_decs_cases] >>
  srw_tac[DNF_ss][] >>
  fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >>
  srw_tac[DNF_ss][Once evaluate_decs_cases] >>
  qspecl_then[`mn`,`env`,`s`,`h`]strip_assume_tac dec_clocked_total >>
  imp_res_tac dec_clocked_min_counter >> fs[] >>
  PairCases_on`res` >> fs[] >>
  Cases_on`res1=Rerr (Rabort Rtimeout_error)`>-metis_tac[]>>
  reverse(Cases_on`∃r. evaluate_dec F mn env s h r`) >> fs[] >- (
    imp_res_tac not_evaluate_dec_timeout >>
    Cases_on`r`>>fs[]>>metis_tac[] ) >>
  PairCases_on`r` >>
  imp_res_tac dec_unclocked >>
  qspecl_then[`mn`,`env`,`s`,`res0 with clock := s.clock`,`h`,`res1`]mp_tac (GSYM dec_clocked_unclocked_equiv) >>
  fs[] >> disch_then (mp_tac o fst o EQ_IMP_RULE) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  reverse(Cases_on`res1`)>>fs[]>-metis_tac[]>>
  fs[]>>
  res_tac >> disj2_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  pop_assum(assume_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars(["s3","new_tds'","r'"])))) >>
  fs[GSYM FORALL_PROD] >>
  qmatch_assum_abbrev_tac`∀p. ¬evaluate_decs F mn envs ss ds p` >>
  `∀p. ¬evaluate_decs F mn envs res0 ds p` by (
    fs[Abbr`ss`,FORALL_PROD] >>
    metis_tac[decs_unclocked,with_same_clock] ) >>
  last_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  PairCases_on`r`>>fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[combine_dec_result_def]
QED

Theorem decs_clocked_total:
   ∀mn env s ds. ∃res. evaluate_decs T mn env s ds res
Proof
  Induct_on`ds`>>simp[Once evaluate_decs_cases] >>
  qx_gen_tac`d` >>
  srw_tac[DNF_ss][] >>
  qspecl_then[`mn`,`env`,`s`,`d`]strip_assume_tac dec_clocked_total >>
  PairCases_on`res` >>
  reverse(Cases_on`res1`)>-metis_tac[] >>
  fs[]>>
  disj2_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[EXISTS_PROD]
QED

Theorem decs_clock_monotone:
   ∀ck mn env ^s d res. evaluate_decs ck mn env s d res ⇒
      ck ⇒ (FST res).clock ≤ s.clock
Proof
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  imp_res_tac dec_clock_monotone >> fsrw_tac[ARITH_ss][]
QED

Theorem decs_sub_from_counter:
   ∀ck mn env ^s d res. evaluate_decs ck mn env s d res ⇒
     ∀extra count count' s0 r0.
        s.clock = count + extra ∧ s0.clock = count' + extra ∧
        res = (s0,r0) ∧ ck ⇒
       evaluate_decs ck mn env (s with clock := count) d (s0 with clock := count',r0)
Proof
  ho_match_mp_tac evaluate_decs_strongind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_sub_from_counter >> fs[] >>
  imp_res_tac dec_clock_monotone >>
  imp_res_tac decs_clock_monotone >>
  fs[] >> rw[] >>
  metis_tac [DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
QED

Theorem decs_clocked_min_counter:
   ∀ck mn env ^s ds res. evaluate_decs ck mn env s ds res ⇒
    ck ⇒ evaluate_decs ck mn env (s with clock := s.clock - (FST res).clock) ds
                ((FST res) with clock := 0, SND res)
Proof
  rw[] >>
  imp_res_tac decs_clock_monotone >>
  PairCases_on`res`>>fs[]>>
  `res0.clock = 0 + res0.clock ∧ s.clock = (s.clock - res0.clock) + res0.clock` by decide_tac >>
  metis_tac[decs_sub_from_counter]
QED

Theorem decs_unclocked_ignore:
   ∀ck mn env ^s d res. evaluate_decs ck mn env s d res ⇒
      ∀r2 r3 count.
        res = (r2,r3) ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_decs F mn env (s with clock := count) d (r2 with clock := count,r3)
Proof
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_unclocked_ignore >> fs[] >>
  Cases_on`r=Rerr (Rabort Rtimeout_error)`>-fs[combine_dec_result_def]>>fs[]>>
  metis_tac[]
QED

Theorem decs_add_to_counter:
   ∀ck mn env ^s d res. evaluate_decs ck mn env s d res ⇒
      ∀r2 r3 extra.
        res = (r2,r3) ∧ ck ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_decs T mn env (s with clock := s.clock + extra) d (r2 with clock := r2.clock + extra,r3)
Proof
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw [Once evaluate_decs_cases] >>
  imp_res_tac dec_add_to_counter >>
  fs [] >>
  rw [] >>
  fs [] >>
  `r ≠ Rerr (Rabort Rtimeout_error)`
        by (Cases_on `r` >>
            fs [combine_dec_result_def]) >>
  fs [] >>
  metis_tac []
QED

Theorem top_evaluate_not_timeout:
 !env s top s' r.
  evaluate_top F env s top (s', r) ⇒ r ≠ Rerr (Rabort Rtimeout_error)
Proof
rw [evaluate_top_cases] >>
metis_tac [dec_evaluate_not_timeout, decs_evaluate_not_timeout]
QED

Theorem top_unclocked:
   !s env top s' r count count'.
    (evaluate_top F env s top (s',r)
     ⇒
     (r ≠ Rerr (Rabort Rtimeout_error)) ∧
     (s.clock = s'.clock)) ∧
    (evaluate_top F env (s with clock := count) top (s' with clock := count,r)
     =
     evaluate_top F env (s with clock := count') top (s' with clock := count',r))
Proof
  reverse (rw [evaluate_top_cases]) >>
  simp [state_component_equality] >>
  simp_tac((srw_ss())++QUANT_INST_ss[record_default_qp])[] >>
  simp[EXISTS_PROD,FORALL_PROD] >>
  metis_tac [dec_unclocked, decs_unclocked]
QED

Theorem not_evaluate_top_timeout:
   ∀env stm top. (∀res. ¬evaluate_top F env stm top res) ⇒
    ∃r. evaluate_top T env stm top r ∧ SND r = Rerr (Rabort Rtimeout_error)
Proof
  Cases_on`top`>>simp[Once evaluate_top_cases]>> srw_tac[DNF_ss][] >>
  simp[Once evaluate_top_cases] >> srw_tac[DNF_ss][] >>
  fs[] >- (
    Cases_on`no_dup_types l`>>fs[] >>
    metis_tac[not_evaluate_decs_timeout,SND,result_nchotomy,pair_CASES]) >>
  metis_tac[not_evaluate_dec_timeout,SND,result_nchotomy,pair_CASES]
QED

Theorem top_clocked_total:
   ∀env s t. ∃res. evaluate_top T env s t res
Proof
  rpt gen_tac >>
  reverse(Cases_on`t`)>>simp[Once evaluate_top_cases] >>
  srw_tac[DNF_ss][] >- (
    qspecl_then[`[]`,`env`,`s`,`d`]strip_assume_tac dec_clocked_total >>
    PairCases_on`res`>>Cases_on`res1`>>metis_tac[pair_CASES] ) >>
  qspecl_then[`[s']`,`env`,`s`,`l`]strip_assume_tac decs_clocked_total >>
  PairCases_on`res`>>fs[]>>
  Cases_on`res1`>>metis_tac[]
QED

Theorem top_clocked_min_counter:
   ∀ck env ^s top res. evaluate_top ck env s top res ⇒
      ck ⇒
        evaluate_top ck env (s with clock := s.clock - (FST res).clock) top
          (FST res with clock := 0,SND res)
Proof
  ho_match_mp_tac evaluate_top_ind >> rw[] >>
  rw[Once evaluate_top_cases] >>
  imp_res_tac dec_clocked_min_counter >> fs[] >>
  imp_res_tac decs_clocked_min_counter >> fs[FMEQ_SINGLE_SIMPLE_DISJ_ELIM] >>
  fs [state_component_equality] >>
  qexists_tac `s2 with clock := 0` >>
  rw []
  >> metis_tac []
QED

Theorem top_add_clock:
 ∀ck env s top s' r.
  evaluate_top ck env s top (s',r) ∧ ¬ck
  ⇒
  ∃c. evaluate_top T env (s with clock := c) top (s' with clock := 0,r)
Proof
 rw[evaluate_top_cases] >>
 imp_res_tac dec_add_clock >>
 imp_res_tac decs_add_clock >>
 fs []
 >- metis_tac []
 >- metis_tac []
 >- (qexists_tac `c` >>
     rw [] >>
     qexists_tac `s2 with clock := 0` >>
     rw []>>
     metis_tac [])
 >- (qexists_tac `c` >>
     rw [] >>
     qexists_tac `s2 with clock := 0` >>
     rw []) >>
 metis_tac []
QED

Theorem top_unclocked_ignore:
 ∀ck env s top s' r c.
  evaluate_top ck env s top (s',r) ∧
  r ≠ Rerr (Rabort Rtimeout_error)
  ⇒
  evaluate_top F env (s with clock := c) top (s' with clock := c, r)
Proof
 rw[evaluate_top_cases] >>
 imp_res_tac dec_unclocked_ignore >>
 imp_res_tac decs_unclocked_ignore >> fs[FMEQ_SINGLE_SIMPLE_DISJ_ELIM] >>
 qexists_tac `s2 with clock := c` >>
 rw []
 >> metis_tac []
QED

Theorem top_clocked_unclocked_equiv:
 ∀env s1 s2 t r.
  evaluate_top F env s1 t (s2,r) ⇔
  ∃c. evaluate_top T env (s1 with clock := c) t (s2 with clock := 0,r) ∧
      r ≠ Rerr (Rabort Rtimeout_error) ∧
      s1.clock = s2.clock
Proof
 simp[FORALL_PROD] >> rw[EQ_IMP_THM] >>
 imp_res_tac top_unclocked >>
 imp_res_tac top_clocked_min_counter >>
 imp_res_tac top_add_clock >>
 imp_res_tac top_unclocked_ignore >> fs[] >>
 rfs [] >>
 metis_tac[with_same_clock]
QED

Theorem top_clock_monotone:
 ∀ck env s d s' r. evaluate_top ck env s d (s',r) ∧ ck ⇒ s'.clock ≤ s.clock
Proof
  rw [evaluate_top_cases] >>
  imp_res_tac dec_clock_monotone >> fs[] >>
  imp_res_tac decs_clock_monotone >> fs[]
QED

Theorem top_sub_from_counter:
 ∀ck env s d s' r extra c c'.
  evaluate_top ck env s d (s',r) ∧
  ck ∧
  s.clock = c + extra ∧
  s'.clock = c' + extra
  ⇒
  evaluate_top ck env (s with clock := c) d (s' with clock := c',r)
Proof
 rw[evaluate_top_cases] >>
 imp_res_tac dec_sub_from_counter >> fs[] >>
 imp_res_tac decs_sub_from_counter >> fs[] >>
 qexists_tac `s2 with clock := c'` >>
 rw []
 >> metis_tac []
QED

Theorem top_add_to_counter:
 ∀env s d s' r extra.
  evaluate_top T env s d (s',r) ∧
  r ≠ Rerr (Rabort Rtimeout_error)
  ⇒
  evaluate_top T env (s with clock := s.clock + extra) d (s' with clock := s'.clock + extra, r)
Proof
 rw[evaluate_top_cases] >>
 imp_res_tac dec_add_to_counter >> fs[] >>
 imp_res_tac decs_add_to_counter >> fs[] >>
 qexists_tac `s2 with clock := s2.clock + extra` >>
 rw [] >>
 metis_tac []
QED

Theorem prog_clock_monotone:
   ∀ck env ^s d res. evaluate_prog ck env s d res ⇒
      ck ⇒ (FST res).clock ≤ s.clock
Proof
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  imp_res_tac top_clock_monotone >> fsrw_tac[ARITH_ss][]
QED

Theorem prog_unclocked:
   !count s env ds count' s' r.
    (evaluate_prog F env s ds (s',r)
     ⇒
     r ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = s'.clock) ∧
    (evaluate_prog F env (s with clock := count) ds (s' with clock := count,r)
     =
     evaluate_prog F env (s with clock := count') ds (s' with clock := count',r))
Proof
  induct_on `ds` >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC [evaluate_prog_cases] >>
  rw []
  >- rw[state_component_equality]
  >- (res_tac >>
      cases_on `r'` >>
      rw [combine_dec_result_def] >>
      Cases_on`a`>>rw[])
  >- metis_tac[top_unclocked]
  >- metis_tac[top_unclocked]
  >- metis_tac[top_unclocked] >>
  eq_tac >> rw [] >>
  metis_tac[top_unclocked,with_clock_with_clock,with_clock_clock,with_same_clock]
QED

Theorem not_evaluate_prog_timeout:
   ∀env s prog. (∀res. ¬evaluate_prog F env s prog res) ⇒
    ∃r. evaluate_prog T env s prog r ∧ SND r = Rerr (Rabort Rtimeout_error)
Proof
  Induct_on`prog` >- simp[Once evaluate_prog_cases] >>
  rpt gen_tac >>
  simp[Once evaluate_prog_cases] >>
  srw_tac[DNF_ss][] >>
  fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >>
  srw_tac[DNF_ss][Once evaluate_prog_cases] >>
  qspecl_then[`env`,`s`,`h`]strip_assume_tac top_clocked_total >>
  imp_res_tac top_clocked_min_counter >> fs[] >>
  PairCases_on`res` >> fs[] >>
  Cases_on`res1=Rerr (Rabort Rtimeout_error)`>-metis_tac[]>>
  reverse(Cases_on`∃r. evaluate_top F env s h r`) >> fs[] >- (
    imp_res_tac not_evaluate_top_timeout >>
    PairCases_on`r`>>fs[]>>metis_tac[] ) >>
  PairCases_on`r` >>
  imp_res_tac top_unclocked >>
  qspecl_then[`env`,`s`,`res0 with clock := s .clock`,`h`,`res1`]mp_tac (GSYM top_clocked_unclocked_equiv) >>
  fs[] >> disch_then (mp_tac o fst o EQ_IMP_RULE) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  reverse(Cases_on`res1`)>>fs[]>-metis_tac[]>>
  fs[]>>
  res_tac >> disj1_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  pop_assum(assume_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["s3","new_tds'"]))) >>
  fs[GSYM FORALL_PROD] >>
  qmatch_assum_abbrev_tac`∀p. ¬evaluate_prog F envs ss ds p` >>
  `∀p. ¬evaluate_prog F envs res0 ds p` by (
    fs[FORALL_PROD] >> metis_tac[prog_unclocked,with_same_clock] ) >>
  last_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  PairCases_on`r`>>fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[combine_dec_result_def]
QED

Theorem not_evaluate_whole_prog_timeout:
   ∀env stm prog.
      (∀res. ¬evaluate_whole_prog F env stm prog res) ⇒
      ∃r. evaluate_whole_prog T env stm prog r ∧
          SND r = Rerr (Rabort Rtimeout_error)
Proof
  rw[FORALL_PROD,EXISTS_PROD,evaluate_whole_prog_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[GSYM EXISTS_PROD,GSYM FORALL_PROD] >>
  metis_tac[not_evaluate_prog_timeout,SND,pair_CASES]
QED

Theorem prog_add_to_counter:
   ∀ck env st prog res.
      evaluate_prog ck env st prog res ⇒
     ∀r2 r3 extra.
       res = (r2,r3) ∧ ck ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
         evaluate_prog T env (st with clock := st.clock + extra) prog (r2 with clock := r2.clock + extra,r3)
Proof
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  rw[Once evaluate_prog_cases] >>
  imp_res_tac top_add_to_counter >>
  fs[] >> rw[] >> fs[] >>
  `r ≠ Rerr (Rabort Rtimeout_error)`
    by (Cases_on`r` >> fs[combine_dec_result_def]) >>
  fs[] >> metis_tac[]
QED
Theorem prog_clock_monotone:
 ∀ck env ^s d res. evaluate_prog ck env s d res ⇒ ck ⇒ (FST res).clock ≤ s.clock
Proof
 ho_match_mp_tac evaluate_prog_ind >> rw[] >>
 imp_res_tac top_clock_monotone >> fsrw_tac[ARITH_ss][]
QED

Theorem prog_sub_from_counter:
   ∀ck env ^s d res. evaluate_prog ck env s d res ⇒
       ∀extra c c' s' r.
          s.clock = c + extra ∧ s'.clock = c' + extra ∧
          res = (s',r) ∧ ck ⇒
         evaluate_prog ck env (s with clock := c) d (s' with clock := c',r)
Proof
  ho_match_mp_tac evaluate_prog_strongind >> rw[] >>
  rw[Once evaluate_prog_cases] >> fs[] >>
  metis_tac[top_sub_from_counter,top_clock_monotone,prog_clock_monotone,FST,
            DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
QED

Theorem prog_clocked_min_counter:
 ∀ck env ^s p res.
  evaluate_prog T env s p res
  ⇒
  evaluate_prog T env (s with clock := s.clock - (FST res).clock) p
                (FST res with clock := 0,SND res)
Proof
  rw[] >>
  imp_res_tac prog_clock_monotone >>
  PairCases_on`res`>>fs[]>>
  `res0.clock = 0 + res0.clock ∧ s.clock = (s.clock - res0.clock) + res0.clock` by decide_tac >>
  metis_tac[prog_sub_from_counter]
QED

Theorem prog_add_clock:
   ∀ck env ^s d res. evaluate_prog ck env s d res ⇒
        ¬ck ⇒
          ∃c. evaluate_prog T env (s with clock := c) d (FST res with clock := 0, SND res)
Proof
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  rw[Once evaluate_prog_cases] >>
  imp_res_tac top_add_clock >> fs[state_component_equality]
  >- (fs [] >>
      imp_res_tac top_add_to_counter >>
      fs [] >>
      rw [] >>
      metis_tac [])
  >- metis_tac[]
QED

Theorem prog_unclocked_ignore:
 ∀ck env ^s d res. evaluate_prog ck env s d res ⇒
    ∀c s' r.
        res = (s',r) ∧ r ≠ Rerr (Rabort Rtimeout_error) ⇒
        evaluate_prog F env (s with clock := c) d (s' with clock := c,r)
Proof
 ho_match_mp_tac evaluate_prog_ind >> rw[] >>
 rw[Once evaluate_prog_cases] >>
 imp_res_tac top_unclocked_ignore >> fs[] >>
 Cases_on`r=Rerr (Rabort Rtimeout_error)`>-fs[combine_dec_result_def]>>fs[]>>
 metis_tac[]
QED

Theorem prog_clocked_unclocked_equiv:
 ∀env s p s' r.
  evaluate_prog F env s p (s',r) ⇔
  ∃c. evaluate_prog T env (s with clock:= c) p (s' with clock := 0, r) ∧
      r ≠ Rerr (Rabort Rtimeout_error) ∧
      s.clock = s'.clock
Proof
 simp[FORALL_PROD] >> rw[EQ_IMP_THM] >>
 imp_res_tac prog_unclocked >>
 imp_res_tac prog_clocked_min_counter >>
 imp_res_tac prog_add_clock >>
 imp_res_tac prog_unclocked_ignore >> fs[] >>
 rfs [] >>
 metis_tac[with_same_clock]
QED
 *)

val _ = export_theory ();
