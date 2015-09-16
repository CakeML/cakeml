(* Theorems about the clocked big-step semantics. Primarily that they are total,
 * and that they have the proper relationship to the unclocked version. *)

open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory evalPropsTheory determTheory;
open boolSimps;

val _ = new_theory "bigClock";

val evaluate_ind = bigStepTheory.evaluate_ind;
val _ = bring_to_front_overload"evaluate_decs"{Name="evaluate_decs",Thy="bigStep"};

val big_unclocked_unchanged = Q.prove (
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
     ck = F
     ⇒
     SND r1 ≠ Rerr (Rabort Rtimeout_error) ∧
     s.clock = (FST r1).clock)`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >> fs[do_app_cases] >> rw [] >> fs []);

val lemma = Q.prove (
`((s with clock := c) with <| refs := r; io := io |>) =
 s with <| clock := c; refs := r; io := io |>`,
 rw []);

val big_unclocked_ignore = Q.prove (
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
     !count st' r.
       r1 = (st', r) ∧
       r ≠ Rerr (Rabort Rtimeout_error)
       ⇒
       evaluate F env (s with clock := count) e (st' with clock := count, r)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
     !count st' r.
       r1 = (st', r) ∧
       r ≠ Rerr (Rabort Rtimeout_error)
       ⇒
       evaluate_list F env (s with clock := count) es (st' with clock := count, r)) ∧
 (∀ck env s v pes err_v r1.
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

val big_unclocked = Q.store_thm ("big_unclocked",
`!s env e s' r env count1 count2.
  (evaluate F env s e (s', r)
   ⇒
   r ≠ Rerr (Rabort Rtimeout_error) ∧
   s.clock = s'.clock) ∧
  (evaluate F env (s with clock := count1) e (s' with clock := count1, r)
   ⇒
   evaluate F env (s with clock := count2) e (s' with clock := count2, r))`,
 rw [] >>
 metis_tac [big_unclocked_ignore, big_unclocked_unchanged, FST, SND, with_clock_with_clock]);

val add_to_counter = Q.store_thm ("add_to_counter",
  `(∀ck env s e r1.
     evaluate ck env s e r1 ⇒
     !s' r' extra.
     (r1 = (s',r')) ∧
     (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
     (ck = T) ⇒
     evaluate T env (s with clock := s.clock+extra) e ((s' with clock := s'.clock+extra),r')) ∧
   (∀ck env s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r' extra.
     (r1 = (s',r')) ∧
     (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
     (ck = T) ⇒
     evaluate_list T env (s with clock := s.clock+extra) es ((s' with clock := s'.clock+extra),r')) ∧
   (∀ck env s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     !s' r' extra.
     (r1 = (s',r')) ∧
     (r' ≠ Rerr (Rabort Rtimeout_error)) ∧
     (ck = T) ⇒
     evaluate_match T env (s with clock := s.clock+extra) v pes err_v ((s' with clock := s'.clock+extra),r'))`,
  ho_match_mp_tac evaluate_ind >>
  rw [] >> rw [Once evaluate_cases] >>
  fs[] >> rfs[] >>
  TRY (metis_tac[]) >>
  disj1_tac >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``evaluate_list`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o (snd o strip_forall o concl)) >>
  simp[] >>
  fsrw_tac[ARITH_ss][] >>
  `extra + s2.clock - 1 = s2.clock -1 + extra` by DECIDE_TAC >>
  metis_tac []);

val with_clock_clock = Q.prove(
  `(s with clock := a).clock = a`,rw[]);

val add_clock = Q.prove (
  `(∀ck env s e r1.
     evaluate ck env s e r1 ⇒
     !s' r'.
     (r1 = (s',r')) ∧
     (ck = F) ⇒
     ∃c. evaluate T env (s with clock := c) e (s' with clock := 0,r')) ∧
   (∀ck env s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r'.
     (r1 = (s',r')) ∧
     (ck = F) ⇒
     ∃c. evaluate_list T env (s with clock := c) es (s' with clock := 0,r')) ∧
   (∀ck env s v pes err_v r1.
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
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``evaluate_list`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC) >>
  metis_tac [add_to_counter, with_clock_with_clock, with_clock_clock,
             arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_0,
             result_distinct, error_result_distinct, result_11]);

val clock_monotone = Q.prove (
  `(∀ck env s e r1.
     evaluate ck env s e r1 ⇒
     !s' r'.
     (r1 = (s',r')) ∧
     (ck = T) ⇒
     (s'.clock ≤ s.clock)) ∧
   (∀ck env s es r1.
     evaluate_list ck env s es r1 ⇒
     !s' r'.
     (r1 = (s',r')) ∧
     (ck = T) ⇒
     (s'.clock ≤ s.clock)) ∧
   (∀ck env s v pes err_v r1.
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

val big_clocked_unclocked_equiv = Q.store_thm ("big_clocked_unclocked_equiv",
  `!s env e s' r1 count1.
    evaluate F env s e (s', r1) =
    ?c. evaluate T env (s with clock := c) e (s' with clock := 0,r1) ∧
          (r1 ≠ Rerr (Rabort Rtimeout_error)) ∧
          (s.clock = s'.clock)`,
  metis_tac [with_clock_clock, with_same_clock, add_clock,
             big_unclocked_ignore, big_unclocked]);

val wf_lem = Q.prove (
  `WF (($< :(num->num->bool)) LEX measure exp_size)`,
  rw [] >>
  match_mp_tac WF_LEX >>
  rw [prim_recTheory.WF_LESS]);

val ind = SIMP_RULE (srw_ss()) [wf_lem] (Q.ISPEC `(($< :(num->num->bool)) LEX measure exp_size)` WF_INDUCTION_THM)

val eval_list_total = Q.prove (
  `∀s env l i count'.
   (∀p_1 p_2.
       p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Con i l) ⇒
       ∀s' env'.
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
  `∀s env es i count'.
  (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (App op es) ⇒
      ∀s' env'.
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
  `∀s env l i count' v err_v.
    (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Mat e' l) ⇒
      ∀s env.
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
  `(pmatch env.c s.refs p v env.v = Match_type_error) ∨
   (pmatch env.c s.refs p v env.v = No_match) ∨
   (?env'. pmatch env.c s.refs p v env.v = Match env')`
              by metis_tac [match_result_nchotomy] >>
  rw [] >>
  metis_tac [LESS_TRANS,LESS_OR_EQ,with_same_clock]);

val eval_handle_total = Q.prove (
  `∀env s l i count' v err_v.
    (∀p_1 p_2.
      p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Handle e' l) ⇒
      ∀s env.
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
  `(pmatch env.c s.refs p v env.v = Match_type_error) ∨
   (pmatch env.c s.refs p v env.v = No_match) ∨
   (?env'. pmatch env.c s.refs p v env.v = Match env')`
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
      cases_on `lookup_var_id i env` >>
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
      `(do_app (s2.refs,s2.io) o' (REVERSE v) = NONE) ∨
       (?s3 e2. do_app (s2.refs,s2.io) o' (REVERSE v) = SOME (s3,e2))`
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
      `?s2 r2. evaluate_match T env s1 v l (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []) (s2,r2)`
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
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, with_clock_clock]));

val big_clocked_total = Q.store_thm ("big_clocked_total",
  `!s env e.
    ∃s' r. evaluate T env s e (s', r)`,
  metis_tac [big_clocked_total_lem, FST, SND, with_same_clock]);

val big_clocked_timeout_0 = Q.store_thm ("big_clocked_timeout_0",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr (Rabort Rtimeout_error))) ∧
   (ck = T)
   ⇒
   (count' = 0)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr (Rabort Rtimeout_error))) ∧
   (ck = T)
   ⇒
   (count' = 0)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr (Rabort Rtimeout_error))) ∧
   (ck = T)
   ⇒
   (count' = 0))`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >>
 fs[do_app_cases] >>
 rw [] >>
 fs [] >>
 TRY (PairCases_on `s'`) >>
 rw []);

val big_clocked_unclocked_equiv_timeout = Q.store_thm ("big_clocked_unclocked_equiv_timeout",
`!s env e count1.
  (!r. ¬evaluate F env (count1,s) e r) = 
  (∀count. ?s'. evaluate T env (count,s) e ((0,s'),Rerr (Rabort Rtimeout_error)))`,
rw [] >>
eq_tac >>
rw [] >|
[`?count1 s1 r1. evaluate T env (count',s) e ((count1,s1),r1)` 
             by metis_tac [big_clocked_total] >>
     metis_tac [big_unclocked_ignore, big_unclocked,big_clocked_timeout_0,
                result_distinct,result_11, error_result_distinct,result_nchotomy, error_result_nchotomy],
 metis_tac [big_exp_determ, pair_CASES, PAIR_EQ, big_unclocked, add_clock]]);

val sub_from_counter = Q.store_thm ("sub_from_counter",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s' r'.
   (s = (count+extra, s0)) ∧
   (r1 = ((count'+extra,s'),r')) ∧
   (ck = T) ⇒
   evaluate T env (count,s0) e ((count',s'),r')) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count'+extra,s'),r')) ∧
   (s = (count+extra, s0)) ∧
   (ck = T) ⇒
   evaluate_list T env (count,s0) es ((count',s'),r')) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count'+extra,s'),r')) ∧
   (s = (count+extra, s0)) ∧
   (ck = T) ⇒
   evaluate_match T env (count,s0) v pes err_v ((count',s'),r'))`,
 ho_match_mp_tac evaluate_strongind >>
 rw [] >>
 rw [Once evaluate_cases] >>
 full_simp_tac (srw_ss()++ARITH_ss) []
 >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- (fs [] >>
     disj1_tac >>
     CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(can lhs))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qexists_tac `s2` >>
     qexists_tac `t2` >>
     qexists_tac `count' - extra` >>
     imp_res_tac clock_monotone >> fs[] >> rw[] >>
     `count' = count' - extra + extra` by DECIDE_TAC >>
     res_tac >> simp[]) >>
 metis_tac [pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]);

val clocked_min_counter = Q.store_thm ("clocked_min_counter",
`!count s0 env e count' s' r'.
evaluate T env (count,s0) e ((count',s'),r')
⇒
evaluate T env (count-count',s0) e ((0, s'), r')`,
 rw [] >>
 `count'' ≤ count'` by metis_tac [clock_monotone, PAIR_EQ, FST, SND, pair_CASES] >>
 `count'' = 0 + count'' ∧ count' = (count' - count'') + count'':num` by decide_tac >>
 metis_tac [sub_from_counter]);

val dec_evaluate_not_timeout = Q.store_thm ("dec_evaluate_not_timeout",
`!mn s env d s' r.
  evaluate_dec F mn env s d (s', r) ⇒ r ≠ Rerr (Rabort Rtimeout_error)`,
rw [evaluate_dec_cases] >>
PairCases_on `s''` >>
PairCases_on `s'''` >>
metis_tac [big_unclocked]);

val dec_unclocked = Q.store_thm ("dec_unclocked",
`!mn count s env d count' s' r env tdecls tdecls'.
  (evaluate_dec F mn env ((count, s),tdecls) d (((count',s'), tdecls'), r)
   ⇒
   (r ≠ Rerr (Rabort Rtimeout_error)) ∧
   (count = count')) ∧
  (evaluate_dec F mn env ((count, s),tdecls) d (((count,s'), tdecls'), r)
   =
   evaluate_dec F mn env ((count', s),tdecls) d (((count',s'), tdecls'), r))`,
 rw [evaluate_dec_cases] >>
 metis_tac [big_unclocked]);

val not_evaluate_dec_timeout = store_thm("not_evaluate_dec_timeout",
  ``∀mn env s d.
      (∀r. ¬evaluate_dec F mn env s d r) ⇒
      ∃r. evaluate_dec T mn env s d r ∧ (SND r = Rerr (Rabort Rtimeout_error))``,
  rpt gen_tac >> PairCases_on`s` >> 
  reverse(Cases_on`d`)>> simp[Once evaluate_dec_cases]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  rw[] >>
  rw[Once evaluate_dec_cases] >>
  fsrw_tac[DNF_ss][] >> rfs[] >> fs[] >>
  fs[] >>
  Cases_on`∃r. evaluate F env (s0,s1,s2) e r` >- (
    fs[] >> PairCases_on`r`>>fs[] >>
    Cases_on`r3`>>fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >> res_tac >>
    metis_tac[match_result_nchotomy] ) >>
  metis_tac[big_clocked_unclocked_equiv_timeout])

val dec_clocked_total = store_thm("dec_clocked_total",
  ``∀mn env s d. ∃res. evaluate_dec T mn env s d res``,
  rpt gen_tac >> PairCases_on`s` >>
  reverse(Cases_on`d`)>>simp[Once evaluate_dec_cases] >>
  srw_tac[DNF_ss][] >- metis_tac[] >>
  qspecl_then[`s0`,`s1,s2`,`env`,`e`]strip_assume_tac big_clocked_total >>
  Cases_on`r`>>metis_tac[match_result_nchotomy, pair_CASES])

val dec_clocked_min_counter = store_thm("dec_clocked_min_counter",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ck ⇒ evaluate_dec ck mn env ((FST(FST s)-FST(FST(FST res)),SND(FST s)),SND s) d (((0,SND(FST(FST res))),SND(FST res)),SND res)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  TRY (
    PairCases_on`s1` >>
    imp_res_tac clocked_min_counter >> rw[] >>
    srw_tac[DNF_ss][] >>
    TRY disj1_tac >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  PairCases_on`s`>>
  PairCases_on`s'`>>
  imp_res_tac clocked_min_counter >> rw[] )

val dec_clocked_unclocked_equiv = store_thm("dec_clocked_unclocked_equiv",
  ``∀mn env count1 s1 s2 d s3 r1 r2.
      evaluate_dec F mn env ((count1,s1),s2) d (((count1,s3),r1),r2) ⇔
      ∃count. evaluate_dec T mn env ((count,s1),s2) d (((0,s3),r1),r2) ∧
              r2 ≠ Rerr (Rabort Rtimeout_error)``,
  Cases_on`d`>>simp[Once evaluate_dec_cases]>>rw[]>>
  rw[Once evaluate_dec_cases]>>srw_tac[DNF_ss][EQ_IMP_THM]>>
  fs[big_clocked_unclocked_equiv]>>
  TRY (metis_tac[]) >>
  TRY disj1_tac >>
  first_assum(match_exists_tac o concl) >> simp[])

val dec_sub_from_counter = store_thm("dec_sub_from_counter",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ∀extra count count' s0 s1 r0 r1 r2.
         s = ((count + extra,s0),s1) ∧
         res = (((count' + extra,r0),r1),r2) ∧ ck ⇒
        evaluate_dec ck mn env ((count,s0),s1) d (((count',r0),r1),r2)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac sub_from_counter >> fs[] >>
  metis_tac[])

val dec_clock_monotone = store_thm("dec_clock_monotone",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ck ⇒ FST(FST(FST res)) ≤ FST(FST s)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  imp_res_tac clock_monotone >> fs[] >>
  TRY(PairCases_on`s1`)>>fs[]>>
  PairCases_on`s'`>>fs[]>>
  PairCases_on`s`>>fs[])

val dec_add_clock = store_thm("dec_add_clock",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ¬ck ⇒
          ∃count. evaluate_dec T mn env ((count,s0),s1) d (((0,r1),r2),r3)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac add_clock >> fs[] >>
  metis_tac[])

val dec_add_to_counter = store_thm("dec_add_to_counter",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 extra.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ck ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_dec T mn env ((count1+extra,s0),s1) d (((count2+extra,r1),r2),r3)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac add_to_counter >> fs[] >>
  metis_tac[])

val dec_unclocked_ignore = store_thm("dec_unclocked_ignore",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 count.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_dec F mn env ((count,s0),s1) d (((count,r1),r2),r3)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  rw[Once evaluate_dec_cases] >>
  imp_res_tac big_unclocked_ignore >> fs[] >>
  metis_tac[])

val decs_add_clock = store_thm("decs_add_clock",
  ``∀ck mn env s d res. evaluate_decs ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ¬ck ⇒
          ∃count. evaluate_decs T mn env ((count,s0),s1) d (((0,r1),r2),r3)``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_add_clock >> fs[] >-
  metis_tac[] >>
  PairCases_on`s'`>>fs[] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(equal``evaluate_decs`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  imp_res_tac dec_add_to_counter >> fs[] >>
  metis_tac[])

val decs_evaluate_not_timeout = Q.store_thm ("decs_evaluate_not_timeout",
`!ck mn env s ds r.
  evaluate_decs ck mn env s ds r ⇒
    !s' cenv' r'. ck = F ∧ r = (s', cenv', r') ⇒ r' ≠ Rerr (Rabort Rtimeout_error)`,
ho_match_mp_tac evaluate_decs_ind >>
rw [] >>
rw []
>- (CCONTR_TAC >>
    fs [] >>
    imp_res_tac dec_evaluate_not_timeout >>
    fs []) >>
cases_on `r` >>
rw [combine_dec_result_def]);

val decs_unclocked = Q.store_thm ("decs_unclocked",
`!mn count s env ds count' s' r env tdecls tdecls' cenv.
  (evaluate_decs F mn env ((count, s),tdecls) ds (((count',s'), tdecls'),cenv,r)
   ⇒
   (r ≠ Rerr (Rabort Rtimeout_error)) ∧
   (count = count')) ∧
  (evaluate_decs F mn env ((count, s),tdecls) ds (((count,s'), tdecls'),cenv,r)
   =
   evaluate_decs F mn env ((count', s),tdecls) ds (((count',s'), tdecls'),cenv,r))`,
 induct_on `ds` >>
 rpt gen_tac >>
 ONCE_REWRITE_TAC [evaluate_decs_cases] >>
 rw []
 >- metis_tac [dec_unclocked]
 >- metis_tac [dec_unclocked]
 >- (PairCases_on `s2` >>
     res_tac >>
     cases_on `r'` >>
     rw [combine_dec_result_def])
 >- metis_tac [pair_CASES, dec_unclocked]
 >- (eq_tac >>
     rw []
     >- metis_tac [dec_unclocked]
     >- (PairCases_on `s2` >>
         fs [] >>
         metis_tac [dec_unclocked])
     >- metis_tac [dec_unclocked]
     >- (PairCases_on `s2` >>
         fs [] >>
         metis_tac [dec_unclocked])));

val not_evaluate_decs_timeout = store_thm("not_evaluate_decs_timeout",
  ``∀mn env s ds.
    (∀r. ¬evaluate_decs F mn env s ds r) ⇒
    ∃r. evaluate_decs T mn env s ds r ∧ (SND(SND r) = Rerr (Rabort Rtimeout_error))``,
  Induct_on`ds` >- ( simp[Once evaluate_decs_cases] ) >>
  rpt gen_tac >>
  simp[Once evaluate_decs_cases] >>
  srw_tac[DNF_ss][] >>
  fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >>
  srw_tac[DNF_ss][Once evaluate_decs_cases] >>
  qspecl_then[`mn`,`env`,`s`,`h`]strip_assume_tac dec_clocked_total >>
  imp_res_tac dec_clocked_min_counter >> fs[] >>
  PairCases_on`res` >> fs[] >>
  Cases_on`res4=Rerr (Rabort Rtimeout_error)`>-metis_tac[]>>
  reverse(Cases_on`∃r. evaluate_dec F mn env s h r`) >> fs[] >- (
    imp_res_tac not_evaluate_dec_timeout >>
    Cases_on`r`>>fs[]>>metis_tac[] ) >>
  PairCases_on`s` >>
  PairCases_on`r` >>
  imp_res_tac dec_unclocked >>
  qspecl_then[`mn`,`env`,`s0`,`s1,s2`,`s3`,`h`,`res1,res2`,`res3`,`res4`]mp_tac (GSYM dec_clocked_unclocked_equiv) >>
  fs[] >> disch_then (mp_tac o fst o EQ_IMP_RULE) >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  reverse(Cases_on`res4`)>>fs[]>-metis_tac[]>>
  PairCases_on`a`>>fs[]>>
  res_tac >> disj2_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  pop_assum(assume_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars(["s3'","new_tds'","r'"])))) >>
  fs[GSYM FORALL_PROD] >>
  qmatch_assum_abbrev_tac`∀p. ¬evaluate_decs F mn envs ss ds p` >>
  `∀p. ¬evaluate_decs F mn envs ((res0,res1,res2),res3) ds p` by (
    fs[FORALL_PROD] >> metis_tac[decs_unclocked] ) >>
  last_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  PairCases_on`r`>>fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[combine_dec_result_def])

val decs_clocked_total = store_thm("decs_clocked_total",
  ``∀mn env s ds. ∃res. evaluate_decs T mn env s ds res``,
  Induct_on`ds`>>simp[Once evaluate_decs_cases] >>
  qx_gen_tac`d` >>
  srw_tac[DNF_ss][] >>
  qspecl_then[`mn`,`env`,`s`,`d`]strip_assume_tac dec_clocked_total >>
  PairCases_on`res` >>
  reverse(Cases_on`res4`)>-metis_tac[] >>
  PairCases_on`a`>>fs[]>>
  disj2_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  fs[EXISTS_PROD])

val decs_clock_monotone = store_thm("decs_clock_monotone",
  ``∀ck mn env s d res. evaluate_decs ck mn env s d res ⇒
      ck ⇒ FST(FST(FST res)) ≤ FST(FST s)``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  imp_res_tac dec_clock_monotone >> fsrw_tac[ARITH_ss][])

val decs_sub_from_counter = store_thm("decs_sub_from_counter",
  ``∀ck mn env s d res. evaluate_decs ck mn env s d res ⇒
      ∀extra count count' s0 s1 r0 r1 r2.
         s = ((count + extra,s0),s1) ∧
         res = (((count' + extra,r0),r1),r2) ∧ ck ⇒
        evaluate_decs ck mn env ((count,s0),s1) d (((count',r0),r1),r2)``,
  ho_match_mp_tac evaluate_decs_strongind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_sub_from_counter >> fs[] >>
  PairCases_on`s'`>>fs[]>>
  imp_res_tac dec_clock_monotone >>
  imp_res_tac decs_clock_monotone >>
  fs[] >> rw[] >>
  metis_tac [DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``])

val decs_clocked_min_counter = store_thm("decs_clocked_min_counter",
  ``∀ck mn env s ds res. evaluate_decs ck mn env s ds res ⇒
    ck ⇒ evaluate_decs ck mn env ((FST (FST s) - FST(FST(FST res)),SND (FST s)),SND s) ds
                (((0,SND(FST(FST res))),SND(FST res)),SND res)``,
  rw[] >>
  imp_res_tac decs_clock_monotone >>
  PairCases_on`s`>>PairCases_on`res`>>fs[]>>
  `res0 = 0 + res0 ∧ s0 = (s0 - res0) + res0` by decide_tac >>
  metis_tac[decs_sub_from_counter])

val decs_unclocked_ignore = store_thm("decs_unclocked_ignore",
  ``∀ck mn env s d res. evaluate_decs ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 count.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ SND r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_decs F mn env ((count,s0),s1) d (((count,r1),r2),r3)``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw[Once evaluate_decs_cases] >>
  imp_res_tac dec_unclocked_ignore >> fs[] >>
  PairCases_on`s'`>>fs[] >>
  Cases_on`r=Rerr (Rabort Rtimeout_error)`>-fs[combine_dec_result_def]>>fs[]>>
  metis_tac[])

val decs_add_to_counter = store_thm("decs_add_to_counter",
  ``∀ck mn env s d res. evaluate_decs ck mn env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 extra.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ck ∧ SND r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_decs T mn env ((count1+extra,s0),s1) d (((count2+extra,r1),r2),r3)``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  rw [Once evaluate_decs_cases] >>
  imp_res_tac dec_add_to_counter >> 
  fs [] >>
  rw [] >>
  PairCases_on `s'` >>
  fs [] >>
  `r ≠ Rerr (Rabort Rtimeout_error)` 
        by (Cases_on `r` >>
            fs [combine_dec_result_def]) >>
  fs [] >>
  metis_tac []);

val top_evaluate_not_timeout = Q.store_thm ("top_evaluate_not_timeout",
`!mn env s top s' cenv' r.
  evaluate_top F env s top (s', cenv', r) ⇒ r ≠ Rerr (Rabort Rtimeout_error)`,
rw [evaluate_top_cases] >>
metis_tac [dec_evaluate_not_timeout, decs_evaluate_not_timeout]);

val top_unclocked = Q.store_thm ("top_unclocked",
`!count s env top count' s' r env tdecls tdecls' mods mods' cenv.
  (evaluate_top F env ((count, s),tdecls,mods) top (((count',s'), tdecls',mods'),cenv,r)
   ⇒
   (r ≠ Rerr (Rabort Rtimeout_error)) ∧
   (count = count')) ∧
  (evaluate_top F env ((count, s),tdecls,mods) top (((count,s'), tdecls',mods'),cenv,r)
   =
   evaluate_top F env ((count', s),tdecls,mods) top (((count',s'), tdecls',mods'),cenv,r))`,
 rw [evaluate_top_cases] >>
 metis_tac [dec_unclocked, decs_unclocked]);

val not_evaluate_top_timeout = store_thm("not_evaluate_top_timeout",
  ``∀env stm top. (∀res. ¬evaluate_top F env stm top res) ⇒
    ∃r. evaluate_top T env stm top r ∧ SND(SND r) = Rerr (Rabort Rtimeout_error)``,
  Cases_on`top`>>simp[Once evaluate_top_cases]>> srw_tac[DNF_ss][] >>
  simp[Once evaluate_top_cases] >> srw_tac[DNF_ss][] >>
  PairCases_on`stm`>>fs[] >- (
    Cases_on`no_dup_types l`>>fs[] >>
    metis_tac[not_evaluate_decs_timeout,SND,result_nchotomy,pair_CASES]) >>
  metis_tac[not_evaluate_dec_timeout,SND,result_nchotomy,pair_CASES]);

val top_clocked_total = store_thm("top_clocked_total",
  ``∀env s t. ∃res. evaluate_top T env s t res``,
  rpt gen_tac >> PairCases_on`s` >>
  reverse(Cases_on`t`)>>simp[Once evaluate_top_cases] >>
  srw_tac[DNF_ss][] >- (
    qspecl_then[`NONE`,`env`,`((s0,s1,s2),s3)`,`d`]strip_assume_tac dec_clocked_total >>
    PairCases_on`res`>>Cases_on`res4`>>metis_tac[pair_CASES] ) >>
  qspecl_then[`SOME s`,`env`,`((s0,s1,s2),s3)`,`l`]strip_assume_tac decs_clocked_total >>
  PairCases_on`res`>>fs[]>>
  Cases_on`res5`>>metis_tac[])

val top_clocked_min_counter = store_thm("top_clocked_min_counter",
  ``∀ck env s top res. evaluate_top ck env s top res ⇒
      ck ⇒
        evaluate_top ck env (((FST(FST s)-FST(FST(FST res))),SND(FST s)),SND s) top
          (((0,SND(FST(FST res))),SND (FST res)),SND res)``,
  ho_match_mp_tac evaluate_top_ind >> rw[] >>
  rw[Once evaluate_top_cases] >>
  imp_res_tac dec_clocked_min_counter >> fs[] >>
  imp_res_tac decs_clocked_min_counter >> fs[FMEQ_SINGLE_SIMPLE_DISJ_ELIM]);

val top_add_clock = store_thm("top_add_clock",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3.
        stm = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ¬ck
        ⇒ ∃count. evaluate_top T env ((count,s0),s1) top (((0,r1),r2),r3)``,
  ho_match_mp_tac evaluate_top_ind >> rw[] >>
  rw[Once evaluate_top_cases] >>
  metis_tac[dec_add_clock,decs_add_clock]);

val top_unclocked_ignore = store_thm("top_unclocked_ignore",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 count.
        stm = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ SND r3 ≠ Rerr (Rabort Rtimeout_error)
        ⇒ evaluate_top F env ((count,s0),s1) top (((count,r1),r2),r3)``,
  ho_match_mp_tac evaluate_top_ind >> rw[] >>
  rw[Once evaluate_top_cases] >>
  imp_res_tac dec_unclocked_ignore >>
  imp_res_tac decs_unclocked_ignore >> fs[FMEQ_SINGLE_SIMPLE_DISJ_ELIM]);

val top_clocked_unclocked_equiv = store_thm("top_clocked_unclocked_equiv",
  ``∀env count1 s1 s2 t r1 r2 r3.
      evaluate_top F env ((count1,s1),s2) t (((count1,r1),r2),r3) ⇔
      ∃count. evaluate_top T env ((count,s1),s2) t (((0,r1),r2),r3) ∧
              SND r3 ≠ Rerr (Rabort Rtimeout_error)``,
  simp[FORALL_PROD] >> rw[EQ_IMP_THM] >>
  imp_res_tac top_unclocked >>
  imp_res_tac top_clocked_min_counter >>
  imp_res_tac top_add_clock >>
  imp_res_tac top_unclocked_ignore >> fs[] >>
  metis_tac[]);

val top_clock_monotone = store_thm("top_clock_monotone",
  ``∀ck mn env s d res. evaluate_top ck env s d res ⇒
      ck ⇒ FST(FST(FST res)) ≤ FST(FST s)``,
  rw [evaluate_top_cases] >>
  imp_res_tac dec_clock_monotone >> fs[] >>
  imp_res_tac decs_clock_monotone >> fs[]);

val top_sub_from_counter = store_thm("top_sub_from_counter",
  ``∀ck env s d res. evaluate_top ck env s d res ⇒
      ∀extra count count' s0 s1 r0 r1 r2.
         s = ((count + extra,s0),s1) ∧
         res = (((count' + extra,r0),r1),r2) ∧ ck ⇒
        evaluate_top ck env ((count,s0),s1) d (((count',r0),r1),r2)``,
  rw[evaluate_top_cases] >>
  imp_res_tac dec_sub_from_counter >> fs[] >>
  imp_res_tac decs_sub_from_counter >> fs[] >>
  metis_tac[]);

val top_add_to_counter = store_thm("top_add_to_counter",
  ``∀ck env s d res. evaluate_top ck env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 extra.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ck ∧ SND r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_top T env ((count1+extra,s0),s1) d (((count2+extra,r1),r2),r3)``,
  rw[evaluate_top_cases] >>
  imp_res_tac dec_add_to_counter >> fs[] >>
  imp_res_tac decs_add_to_counter >> fs[] >>
  metis_tac[]);

val prog_unclocked = Q.store_thm ("prog_unclocked",
`!mn count s env ds count' s' r env x y x' y' z.
  (evaluate_prog F env ((count, s),x,y) ds (((count',s'), x',y'),z,r)
   ⇒
   (r ≠ Rerr (Rabort Rtimeout_error)) ∧
   (count = count')) ∧
  (evaluate_prog F env ((count, s),x,y) ds (((count,s'), x',y'),z,r)
   =
   evaluate_prog F env ((count', s),x,y) ds (((count',s'), x',y'),z,r))`,
 induct_on `ds` >>
 rpt gen_tac >>
 ONCE_REWRITE_TAC [evaluate_prog_cases] >>
 rw []
 >- (PairCases_on `s2` >>
     res_tac >>
     cases_on `r'` >>
     rw [combine_mod_result_def] >>
     Cases_on`a`>>rw[])
 >- (
   PairCases_on`s2`>>
   metis_tac[top_unclocked] )
 >- metis_tac[top_unclocked]
 >- metis_tac[top_unclocked]
 >- (eq_tac >>
     rw [] >> TRY
     (PairCases_on `s2` >> fs [] >>
         metis_tac [top_unclocked])
     >> metis_tac [top_unclocked]))

val not_evaluate_prog_timeout = store_thm("not_evaluate_prog_timeout",
  ``∀env stm prog. (∀res. ¬evaluate_prog F env stm prog res) ⇒
      ∃r. evaluate_prog T env stm prog r ∧ SND (SND r) = Rerr (Rabort Rtimeout_error)``,
  Induct_on`prog` >- simp[Once evaluate_prog_cases] >>
  rpt gen_tac >>
  simp[Once evaluate_prog_cases] >>
  srw_tac[DNF_ss][] >>
  fs[METIS_PROVE[]``P ∨ Q ⇔ ¬P ⇒ Q``] >>
  srw_tac[DNF_ss][Once evaluate_prog_cases] >>
  qspecl_then[`env`,`stm`,`h`]strip_assume_tac top_clocked_total >>
  imp_res_tac top_clocked_min_counter >> fs[] >>
  PairCases_on`res` >> fs[] >>
  Cases_on`res7=Rerr (Rabort Rtimeout_error)`>-metis_tac[]>>
  reverse(Cases_on`∃r. evaluate_top F env stm h r`) >> fs[] >- (
    imp_res_tac not_evaluate_top_timeout >>
    PairCases_on`r`>>fs[]>>metis_tac[] ) >>
  PairCases_on`stm` >>
  PairCases_on`r` >>
  imp_res_tac top_unclocked >>
  qspecl_then[`env`,`stm0`,`stm1,stm2`,`stm3,stm4`,`h`,`res1,res2`,`res3,res4`,`(res5,res6),res7`]mp_tac (GSYM top_clocked_unclocked_equiv) >>
  fs[] >> disch_then (mp_tac o fst o EQ_IMP_RULE) >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  reverse(Cases_on`res7`)>>fs[]>-metis_tac[]>>
  PairCases_on`a`>>fs[]>>
  res_tac >> disj1_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  pop_assum(assume_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["s3","new_tds'"]))) >>
  fs[GSYM FORALL_PROD] >>
  qmatch_assum_abbrev_tac`∀p. ¬evaluate_prog F envs ss ds p` >>
  `∀p. ¬evaluate_prog F envs ((res0,res1,res2),res3,res4) ds p` by (
    fs[FORALL_PROD] >> metis_tac[prog_unclocked] ) >>
  last_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  PairCases_on`r`>>fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[combine_mod_result_def])

val not_evaluate_whole_prog_timeout = store_thm("not_evaluate_whole_prog_timeout",
  ``∀env stm prog.
      (∀res. ¬evaluate_whole_prog F env stm prog res) ⇒
      ∃r. evaluate_whole_prog T env stm prog r ∧
          SND (SND r) = Rerr (Rabort Rtimeout_error)``,
  rw[FORALL_PROD,EXISTS_PROD,evaluate_whole_prog_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[GSYM EXISTS_PROD,GSYM FORALL_PROD] >>
  metis_tac[not_evaluate_prog_timeout,SND,pair_CASES])

val prog_clock_monotone = store_thm("prog_clock_monotone",
  ``∀ck env s d res. evaluate_prog ck env s d res ⇒
      ck ⇒ FST(FST(FST res)) ≤ FST(FST s)``,
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  imp_res_tac top_clock_monotone >> fsrw_tac[ARITH_ss][])

val prog_sub_from_counter = store_thm("prog_sub_from_counter",
  ``∀ck env s d res. evaluate_prog ck env s d res ⇒
      ∀extra count count' s0 s1 r0 r1 r2.
         s = ((count + extra,s0),s1) ∧
         res = (((count' + extra,r0),r1),r2) ∧ ck ⇒
        evaluate_prog ck env ((count,s0),s1) d (((count',r0),r1),r2)``,
  ho_match_mp_tac evaluate_prog_strongind >> rw[] >>
  rw[Once evaluate_prog_cases] >>
  imp_res_tac top_sub_from_counter >> fs[] >>
  PairCases_on`s'`>>fs[]>>
  imp_res_tac top_clock_monotone >>
  imp_res_tac prog_clock_monotone >>
  fs[] >> rw[] >>
  metis_tac [DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]);

val prog_clocked_min_counter = store_thm("prog_clocked_min_counter",
  ``∀ck env s ds res. evaluate_prog ck env s ds res ⇒
    ck ⇒ evaluate_prog ck env ((FST (FST s) - FST(FST(FST res)),SND (FST s)),SND s) ds
                (((0,SND(FST(FST res))),SND(FST res)),SND res)``,
  rw[] >>
  imp_res_tac prog_clock_monotone >>
  PairCases_on`s`>>PairCases_on`res`>>fs[]>>
  `res0 = 0 + res0 ∧ s0 = (s0 - res0) + res0` by decide_tac >>
  metis_tac[prog_sub_from_counter]);

val prog_add_clock = store_thm("prog_add_clock",
  ``∀ck env s d res. evaluate_prog ck env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ ¬ck ⇒
          ∃count. evaluate_prog T env ((count,s0),s1) d (((0,r1),r2),r3)``,
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  rw[Once evaluate_prog_cases] >>
  imp_res_tac top_add_clock >> fs[] 
  >- (PairCases_on `s'` >>
      fs [] >>
      imp_res_tac top_add_to_counter >>
      fs [] >>
      rw [] >>
      metis_tac [])
  >- metis_tac[]);

val prog_unclocked_ignore = store_thm("prog_unclocked_ignore",
  ``∀ck env s d res. evaluate_prog ck env s d res ⇒
      ∀count1 s0 s1 count2 r1 r2 r3 count.
        s = ((count1,s0),s1) ∧ res = (((count2,r1),r2),r3) ∧ SND r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
          evaluate_prog F env ((count,s0),s1) d (((count,r1),r2),r3)``,
  ho_match_mp_tac evaluate_prog_ind >> rw[] >>
  rw[Once evaluate_prog_cases] >>
  imp_res_tac top_unclocked_ignore >> fs[] >>
  PairCases_on`s'`>>fs[] >>
  Cases_on`r=Rerr (Rabort Rtimeout_error)`>-fs[combine_mod_result_def]>>fs[]>>
  metis_tac[]);

val prog_clocked_unclocked_equiv = store_thm("prog_clocked_unclocked_equiv",
  ``∀env count1 s1 s2 s3 p r1 r2 r3 r4.
      evaluate_prog F env ((count1,s1),s2,s3) p (((count1,r1),r2,r4),r3) ⇔
      ∃count. evaluate_prog T env ((count,s1),s2,s3) p (((0,r1),r2,r4),r3) ∧
              SND r3 ≠ Rerr (Rabort Rtimeout_error)``,
 rw [] >>
 simp[FORALL_PROD] >> rw[EQ_IMP_THM] >>
 PairCases_on `r3` >>
 fs [] >>
 imp_res_tac prog_unclocked >>
 rw [] >>
 imp_res_tac prog_clocked_min_counter >>
 imp_res_tac prog_add_clock >>
 imp_res_tac prog_unclocked_ignore >> fs[] >>
 metis_tac[]);

val _ = export_theory ();
