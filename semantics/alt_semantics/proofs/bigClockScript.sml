(*
  Theorems about the clocked big-step semantics. Primarily that they
  are total, and that they have the proper relationship to the
  unclocked version.
*)

open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open evaluateTheory determTheory;
open semanticPrimitivesPropsTheory fpSemPropsTheory;
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
  ho_match_mp_tac evaluate_ind >> rw [] >>
  fs[do_app_cases, shift_fp_opts_def, do_fprw_def, compress_if_bool_def] >>
  rw [] >> fs [] >>
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
  rw [Once evaluate_cases, shift_fp_opts_def]>>
  fs [opClass_cases, compress_if_bool_def, isFpBool_def] >>
  rw [] >> fs[] >>
  TRY (disj1_tac >>
       qexists_tac `vs` >>
       qexists_tac `s2 with clock := count'` >>
       rw [] >>
       NO_TAC) >>
  TRY (disj1_tac >>
       qexists_tac `ffi'` >>
       qexists_tac ‘refs'’ >>
       qexists_tac `vs` >>
       TRY $ qexists_tac `vFp` >>
       qexists_tac `s2 with clock := count'` >>
       rw [] >>
       NO_TAC) >>
  TRY (disj2_tac >> disj1_tac >>
       qexists_tac `ffi'` >>
       qexists_tac ‘refs'’ >>
       qexists_tac `vs` >>
       TRY $ qexists_tac `vFp` >>
       qexists_tac `s2 with clock := count'` >>
       rw [] >>
       NO_TAC) >>
  TRY (ntac 2 disj2_tac >> disj1_tac >>
       qexists_tac `ffi'` >>
       qexists_tac ‘refs'’ >>
       qexists_tac `vs` >> qexists_tac ‘res’ >>
       TRY $ qexists_tac `rOpt` >>
       qexists_tac `s2 with clock := count'` >>
       rw [] >>
       NO_TAC) >>
  TRY (qexists_tac `s2 with clock := count'` >>
       TRY $ qexists_tac ‘v’ >>
       rw [] >>
       NO_TAC) >>
  TRY (disj1_tac >>
       qexists_tac `ffi'` >> qexists_tac ‘refs'’ >>
       qexists_tac ‘vs’ >>
       qexists_tac `s2 with clock := count'` >>
       rw[] >>
       NO_TAC) >>
  TRY (disj2_tac >> disj1_tac >>
       qexists_tac ‘vs’ >>
       qexists_tac `s2 with clock := count'` >>
       rw[] >>
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
  rw [] >> rw [Once evaluate_cases, shift_fp_opts_def] >>
  fs[opClass_cases] >> rfs[] >>
  TRY (metis_tac[with_clock_refs]) >>
  TRY (disj2_tac >> disj1_tac >>
       first_x_assum $ qspec_then ‘extra’ $ irule_at Any >> gs[] >> NO_TAC) >>
  TRY (ntac 2 disj2_tac >> disj1_tac >>
       first_x_assum $ qspec_then ‘extra’ $ irule_at Any >> gs[] >> NO_TAC) >>
  TRY (qexists_tac ‘s2 with clock := extra + s2.clock’ >> qexists_tac ‘v’ >>
       gs[state_component_equality] >> NO_TAC) >>
  TRY (qexists_tac ‘s2 with clock := extra + s2.clock’ >>
       gs[state_component_equality] >> NO_TAC) >>
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
  rw [Once evaluate_cases, shift_fp_opts_def] >>
  srw_tac[DNF_ss][] >> fs[opClass_cases] >>
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
  TRY (
    disj2_tac >> disj1_tac >>
    last_x_assum $ irule_at Any >> gs[] >> NO_TAC) >>
  TRY (
    ntac 2 disj2_tac >> disj1_tac >>
    last_x_assum $ irule_at Any >> gs[] >> NO_TAC) >>
  TRY (
    ntac 4 disj2_tac >> disj1_tac >>
    last_x_assum $ irule_at Any >> gs[] >> NO_TAC) >>
  TRY (
    srw_tac[DNF_ss][] >>
    rewrite_tac[ CONJ_ASSOC] >> once_rewrite_tac [CONJ_COMM] >>
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
  rw [Once evaluate_cases, shift_fp_opts_def] >>
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

Theorem big_clocked_unclocked_equiv_list:
  !s env e s' r1.
    evaluate_list F env s e (s', r1) =
    ?c. evaluate_list T env (s with clock := c) e (s' with clock := 0,r1) ∧
        (r1 ≠ Rerr (Rabort Rtimeout_error)) ∧
        (s.clock = s'.clock)
Proof
  metis_tac [with_clock_clock, with_same_clock, add_clock,
             big_unclocked_ignore, big_unclocked_unchanged, FST, SND,
             with_clock_with_clock]
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

Triviality list_size_REVERSE:
  ∀xs. list_size f (REVERSE xs) = list_size f xs
Proof
  Induct \\ fs [listTheory.list_size_def,listTheory.list_size_append]
QED

Triviality exp6_size_rev:
  !es. exp6_size (REVERSE es) = exp6_size es
Proof
  fs [exp_size_eq,list_size_REVERSE]
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
       by metis_tac [optionTheory.option_nchotomy, pair_CASES] >>
        fs[opClass_cases] >- metis_tac[] >>
        cases_on `s2.clock = 0` >>
        rw [] >-
          metis_tac [pair_CASES] >>
        `s2.clock-1 < s2.clock` by srw_tac [ARITH_ss] [] >>
        metis_tac [pair_CASES, clock_monotone, LESS_OR_EQ, LESS_TRANS, with_clock_clock]) >>
      cases_on ‘opClass o' Reals’ >- (
        cases_on ‘s2.fp_state.real_sem’ >- (
          `(do_app (s2.refs,s2.ffi) o' (REVERSE v) = NONE) ∨
           (?s3 e2. do_app (s2.refs,s2.ffi) o' (REVERSE v) = SOME (s3,e2))`
           by metis_tac [optionTheory.option_nchotomy, pair_CASES] >- (
             fs [opClass_cases] >> metis_tac [pair_CASES]) >>
          ‘getOpClass o' = Reals’ by (cases_on ‘o'’ >> gs[opClass_cases, getOpClass_def]) >>
          first_x_assum $ mp_then Any assume_tac (INST_TYPE [beta |-> alpha] realOp_determ) >>
          cases_on ‘s3’ >> gs[] >> res_tac >>
          first_x_assum $ qspec_then ‘s2.ffi’ assume_tac >> gs[] >> rveq >>
          qexists_tac ‘s2 with <| refs := s2.refs ; ffi := s2.ffi |>’ >>
          qexists_tac ‘e2’ >> gs[] >>
          ntac 7 disj2_tac >> disj1_tac >>
          last_x_assum $ irule_at Any >>
          qexists_tac ‘s2.refs’ >> qexists_tac ‘s2.ffi’ >>
          gs[]) >>
        qexists_tac ‘shift_fp_opts s2’ >> qexists_tac ‘Rerr (Rabort Rtype_error)’ >>
        gs[] >> ntac 7 disj2_tac >> disj1_tac >>
        last_x_assum $ irule_at Any >> gs[]) >>
      `(do_app (s2.refs,s2.ffi) o' (REVERSE v) = NONE) ∨
       (?s3 e2. do_app (s2.refs,s2.ffi) o' (REVERSE v) = SOME (s3,e2))`
        by metis_tac [optionTheory.option_nchotomy, pair_CASES] >- (
        fs [opClass_cases] >> metis_tac [pair_CASES]) >>
      cases_on ‘opClass o' Simple’ >> gs[] >- metis_tac [pair_CASES] >>
      cases_on ‘opClass o' Icing’ >> gs[] >- (
        PairCases_on ‘s3’ >> gs[] >>
        first_assum $ mp_then Any assume_tac (INST_TYPE [beta |-> alpha] fpOp_determ) >>
        ‘~ opClass o' FunApp’ by (Cases_on ‘o'’ >> gs[opClass_cases]) >>
        ‘getOpClass o' = Icing’ by (Cases_on ‘o'’ >> gs[getOpClass_def, opClass_cases]) >>
        res_tac >>
        first_x_assum $ qspec_then ‘s2.ffi’ assume_tac >> gs[] >>
        pop_assum $ kall_tac >>
        reverse $ cases_on ‘s2.fp_state.canOpt = FPScope Opt’ >> gs[] >- (
          qexists_tac ‘s2 with <| refs := s2.refs ; ffi := s2.ffi |>’ >>
          qexists_tac ‘compress_if_bool o' e2’ >> gs[] >>
          disj1_tac >>
          last_x_assum $ irule_at Any >>
          qexists_tac ‘e2’ >>
          qexists_tac ‘s2.refs’ >> qexists_tac ‘s2.ffi’ >> gs[]) >>
        qexists_tac ‘shift_fp_opts s2 with <| refs := s2.refs ; ffi := s2.ffi |>’ >>
        gs[] >>
        cases_on ‘do_fprw e2 (s2.fp_state.opts 0) s2.fp_state.rws’ >- (
          qexists_tac ‘compress_if_bool o' e2’ >>
          disj2_tac >> disj1_tac >>
          last_x_assum $ irule_at Any >>
          qexists_tac ‘e2’ >>
          qexists_tac ‘s2.refs’ >> qexists_tac ‘s2.ffi’ >> gs[]) >>
        qexists_tac ‘compress_if_bool o' x’ >>
        ntac 2 disj2_tac >> disj1_tac >>
        last_x_assum $ irule_at Any >>
        qexists_tac ‘e2’ >> qexists_tac ‘s2.refs’ >>
        qexists_tac ‘x’ >> qexists_tac ‘s2.ffi’ >>
        gs[]) >>
      ‘opClass o' EvalOp’ by (Cases_on ‘o'’ >> TRY (gs[opClass_cases] >> NO_TAC)) >>
      cases_on ‘o'’ >> gs[opClass_cases, do_app_def] >> every_case_tac >> gs[])
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
  >- ((* FpOptimise Strict *)
      `exp_size e' < exp_size (FpOptimise f e')`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, with_clock_clock])
  >- ((* FpOptimise not Strict*)
      `exp_size e' < exp_size (FpOptimise f e')`
             by srw_tac [ARITH_ss] [exp_size_def] >>
      metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, with_clock_clock])
QED

Theorem big_clocked_total:
  !s env e.
    ∃s' r. evaluate T env s e (s', r)
Proof
  metis_tac [big_clocked_total_lem, FST, SND, with_same_clock]
QED

Theorem big_clocked_list_total:
  ∀es env s. ∃r. evaluate_list T env s es r
Proof
  Induct >> rw[Once evaluate_cases, SF DNF_ss] >>
  qspecl_then [`s`,`env`,`h`] assume_tac big_clocked_total >> gvs[] >>
  Cases_on `r` >> gvs[SF SFY_ss] >>
  first_x_assum $ qspecl_then [`env`,`s'`] assume_tac >> gvs[] >>
  PairCases_on `r` >> Cases_on `r1` >>  gvs[SF SFY_ss]
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
  fs[do_app_cases, opClass_cases] >>
  rw [] >>
  fs [] >>
  every_case_tac >> fs[] >> rveq >> fs[] >>
  gs[do_fprw_def, compress_if_bool_def] >> every_case_tac >> gs[]
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
  >- (gs[] >>
      disj2_tac >> disj2_tac >> disj2_tac >>
      disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[] >>
      ntac 4 disj2_tac >>
      disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >> qexists_tac ‘vFp’ >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[shift_fp_opts_def] >>
      ntac 5 disj2_tac >>
      disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >> qexists_tac ‘vFp’ >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[shift_fp_opts_def] >>
      ntac 6 disj2_tac >>
      disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >> qexists_tac ‘res’ >>
      qexists_tac ‘rOpt’ >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[shift_fp_opts_def] >>
      ntac 7 disj2_tac >> disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[shift_fp_opts_def] >>
      ntac 7 disj2_tac >> disj1_tac >>
      imp_res_tac clock_monotone >>
      fs [] >>
      qexists_tac `vs` >>
      qexists_tac `s2 with clock := count''` >>
      rw [])
  >- (gs[shift_fp_opts_def] >>
      ntac 6 disj2_tac >> disj1_tac >>
      imp_res_tac clock_monotone >> fs [] >>
      qexists_tac `vs` >>
      rw []) >>
  TRY (
    qexists_tac ‘s2 with clock := count''’ >> TRY $ qexists_tac ‘v’ >> gs[] >> NO_TAC) >>
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

Theorem clocked_min_counter_list:
  ∀s env e s' r'.
    evaluate_list T env s e (s',r')
  ⇒ evaluate_list T env (s with clock := s.clock - s'.clock) e (s' with clock := 0, r')
Proof
  rw[] >> irule $ cj 2 sub_from_counter >> simp[] >>
  imp_res_tac clock_monotone >> gvs[]
QED

Theorem big_clocked_to_unclocked:
  evaluate T env s e (s',r) ∧
  r ≠ Rerr (Rabort Rtimeout_error) ⇒
  evaluate F env s e (s' with clock := s.clock, r)
Proof
  rw[] >> drule clocked_min_counter >> rw[] >>
  simp[big_clocked_unclocked_equiv] >> goal_assum drule
QED

Theorem big_clocked_to_unclocked_list:
  ∀env s e r.
  evaluate_list T env s e r ∧
  SND r ≠ Rerr (Rabort Rtimeout_error) ⇒
  evaluate_list F env s e (FST r with clock := s.clock, SND r)
Proof
  rw[] >> PairCases_on `r` >> gvs[] >>
  drule clocked_min_counter_list >> rw[] >>
  drule $ cj 2 big_unclocked_ignore >> simp[] >>
  disch_then $ qspec_then `s.clock` mp_tac >>
  qsuff_tac `s with clock := s.clock = s` >> rw[] >>
  simp[state_component_equality]
QED

Theorem evaluate_decs_clocked_to_unclocked_lemma[local]:
  (∀ck env (st:'ffi semanticPrimitives$state) d res.
    evaluate_dec ck env st d res ⇒ ck ∧
    SND res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ ∀c. evaluate_dec F env (st with clock := c) d
          (FST res with clock := c, SND res)) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds res.
    evaluate_decs ck env st ds res ⇒ ck ∧
    SND res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ ∀c. evaluate_decs F env (st with clock := c) ds
          (FST res with clock := c, SND res))
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  simp[Once evaluate_dec_cases, with_same_clock] >> gvs[]
  >- (
    drule $ cj 1 big_unclocked_ignore >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (
    disj1_tac >> drule $ cj 1 big_unclocked_ignore >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (
    disj1_tac >> drule $ cj 1 big_unclocked_ignore >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (
    drule $ cj 1 big_unclocked_ignore >> simp[]
    )
  >- (irule_at Any EQ_REFL >> gvs[])
  >- (
    disj1_tac >> last_x_assum $ irule_at Any >> simp[]
    )
  >- (
    disj2_tac >> irule_at Any EQ_REFL >>
    last_x_assum $ irule_at Any >> first_x_assum irule >>
    Cases_on `r` >> gvs[semanticPrimitivesTheory.combine_dec_result_def]
    )
QED

Theorem evaluate_decs_clocked_to_unclocked =
  evaluate_decs_clocked_to_unclocked_lemma |>
  CONJUNCTS |> map (Q.SPEC `T`) |> LIST_CONJ |>
  SIMP_RULE (srw_ss()) [FORALL_PROD, AND_IMP_INTRO];

Theorem evaluate_decs_add_to_clock_lemma[local]:
  (∀ck env (st:'ffi semanticPrimitives$state) d res.
    evaluate_dec ck env st d res ⇒ ck ∧ SND res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ ∀extra. evaluate_dec T env (st with clock := st.clock + extra) d
          (FST res with clock := (FST res).clock + extra, SND res)) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds res.
    evaluate_decs ck env st ds res ⇒ ck ∧ SND res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ ∀extra. evaluate_decs T env (st with clock := st.clock + extra) ds
          (FST res with clock := (FST res).clock + extra, SND res))
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  simp[Once evaluate_dec_cases] >> gvs[]
  >- (
    drule $ cj 1 add_to_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (
    disj1_tac >> drule $ cj 1 add_to_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (
    disj1_tac >> drule $ cj 1 add_to_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[]
    )
  >- (drule $ cj 1 add_to_counter >> simp[])
  >- (irule_at Any EQ_REFL >> simp[])
  >- (disj1_tac >> first_x_assum $ irule_at Any >> simp[])
  >- (
    disj2_tac >> irule_at Any EQ_REFL >>
    first_x_assum $ irule_at Any >> simp[] >>
    Cases_on `r` >> gvs[semanticPrimitivesTheory.combine_dec_result_def]
    )
QED

Theorem evaluate_decs_add_to_clock =
  evaluate_decs_add_to_clock_lemma |>
  CONJUNCTS |> map (Q.SPEC `T`) |> LIST_CONJ |>
  SIMP_RULE (srw_ss()) [FORALL_PROD, AND_IMP_INTRO];

Theorem evaluate_decs_clock_mono_lemma[local]:
  (∀ck env (st:'ffi semanticPrimitives$state) d res.
    evaluate_dec ck env st d res ⇒ ck ⇒ (FST res).clock ≤ st.clock) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds res.
    evaluate_decs ck env st ds res ⇒ ck ⇒ (FST res).clock ≤ st.clock)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >> gvs[] >>
  metis_tac[clock_monotone]
QED

Theorem evaluate_decs_clock_mono =
  evaluate_decs_clock_mono_lemma |>
  CONJUNCTS |> map (Q.SPEC `T`) |> LIST_CONJ |>
  SIMP_RULE (srw_ss()) [FORALL_PROD, AND_IMP_INTRO];

Theorem evaluate_decs_min_clock_lemma[local]:
  (∀ck env (st:'ffi semanticPrimitives$state) d res.
    evaluate_dec ck env st d res ⇒ ck ∧ SND res ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀c. c ≤ st.clock ∧ c ≤ (FST res).clock
  ⇒ evaluate_dec T env (st with clock := st.clock - c) d
          (FST res with clock := (FST res).clock - c, SND res)) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds res.
    evaluate_decs ck env st ds res ⇒ ck ∧ SND res ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀c. c ≤ st.clock ∧ c ≤ (FST res).clock
  ⇒ evaluate_decs T env (st with clock := st.clock - c) ds
          (FST res with clock := (FST res).clock - c, SND res))
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  simp[Once evaluate_dec_cases] >> gvs[]
  >- (
    drule $ cj 1 sub_from_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[] >> gvs[LESS_EQ_EXISTS]
    )
  >- (
    disj1_tac >> drule $ cj 1 sub_from_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[] >> gvs[LESS_EQ_EXISTS]
    )
  >- (
    disj1_tac >> drule $ cj 1 sub_from_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[] >> gvs[LESS_EQ_EXISTS]
    )
  >- (
    disj2_tac >> disj2_tac >> drule $ cj 1 sub_from_counter >> simp[] >>
    disch_then $ irule_at Any >> simp[] >> gvs[LESS_EQ_EXISTS]
    )
  >- (irule_at Any EQ_REFL >> simp[])
  >- (
    disj1_tac >> ntac 2 (last_assum $ irule_at Any) >> simp[] >>
    first_x_assum $ qspec_then `0` assume_tac >> gvs[] >>
    imp_res_tac evaluate_decs_clock_mono >> gvs[]
    )
  >- (
    disj2_tac >> irule_at Any EQ_REFL >>
    ntac 2 (first_assum $ irule_at Any >> simp[]) >>
    conj_asm1_tac >> gvs[]
    >- (Cases_on `r` >> gvs[semanticPrimitivesTheory.combine_dec_result_def]) >>
    first_x_assum $ qspec_then `0` assume_tac >> gvs[] >>
    imp_res_tac evaluate_decs_clock_mono >> gvs[]
    )
QED

Theorem evaluate_decs_min_clock:
  (∀ck env (st:'ffi semanticPrimitives$state) d st' res.
    evaluate_dec T env st d (st', res) ∧
    res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ evaluate_dec T env (st with clock := st.clock - st'.clock) d
      (st' with clock := 0, res)) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds st' res.
    evaluate_decs T env st ds (st', res) ∧
    res ≠ Rerr (Rabort Rtimeout_error)
  ⇒ evaluate_decs T env (st with clock := st.clock - st'.clock) ds
      (st' with clock := 0, res))
Proof
  rw[] >> imp_res_tac evaluate_decs_min_clock_lemma >> gvs[] >>
  pop_assum $ qspec_then `st'.clock` mp_tac >> simp[] >>
  disch_then irule >> metis_tac[evaluate_decs_clock_mono]
QED

Theorem evaluate_decs_unclocked_to_clocked_lemma[local]:
  (∀ck env (st:'ffi semanticPrimitives$state) d res.
    evaluate_dec ck env st d res ⇒ ¬ck
  ⇒ ∃c c'. evaluate_dec T env (st with clock := c) d
          (FST res with clock := c', SND res)) ∧
  (∀ck env (st:'ffi semanticPrimitives$state) ds res.
    evaluate_decs ck env st ds res ⇒ ¬ck
  ⇒ ∃c c'. evaluate_decs T env (st with clock := c) ds
          (FST res with clock := c', SND res))
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  simp[Once evaluate_dec_cases, with_same_clock] >> gvs[] >>
  gvs[big_clocked_unclocked_equiv]
  >- (goal_assum drule >> simp[])
  >- (irule_at Any OR_INTRO_THM1 >> goal_assum drule >> simp[])
  >- (irule_at Any OR_INTRO_THM1 >> goal_assum drule >> simp[])
  >- (irule_at Any EQ_REFL)
  >- (irule_at Any EQ_REFL)
  >- (
    irule_at Any OR_INTRO_THM2 >> irule_at Any OR_INTRO_THM2 >>
    goal_assum drule >> simp[]
    )
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- irule_at Any EQ_REFL
  >- (irule_at Any EQ_REFL >> simp[] >> pop_assum $ irule_at Any)
  >- (
    irule_at Any OR_INTRO_THM1 >>
    rename1 `evaluate_decs _ env (_ with clock := a) _ (_ with clock := b,_)` >>
    rename1 `evaluate_decs _ _ (_ with clock := c) _ (_ with clock := d,_)` >>
    last_x_assum assume_tac >>
    drule $ cj 2 evaluate_decs_min_clock >> simp[] >> strip_tac >>
    drule $ cj 2 evaluate_decs_add_to_clock >> simp[] >>
    disch_then $ qspec_then `c` assume_tac >>
    goal_assum drule >> goal_assum drule
    )
  >- (irule_at Any OR_INTRO_THM2 >> goal_assum drule)
  >- irule_at Any EQ_REFL
  >- (irule_at Any OR_INTRO_THM1 >> goal_assum drule)
  >- (
    irule_at Any OR_INTRO_THM2 >> irule_at Any EQ_REFL >>
    rename1 `evaluate_dec _ env (_ with clock := a) _ (_ with clock := b,_)` >>
    rename1 `evaluate_decs _ _ (_ with clock := c) _ (_ with clock := c',_)` >>
    drule $ cj 1 evaluate_decs_min_clock >> simp[] >> strip_tac >>
    drule $ cj 1 evaluate_decs_add_to_clock >> simp[] >>
    disch_then $ qspec_then `c` assume_tac >>
    goal_assum drule >> goal_assum drule
    )
QED

Theorem evaluate_decs_unclocked_to_clocked =
  evaluate_decs_unclocked_to_clocked_lemma |>
  CONJUNCTS |> map (Q.SPEC `F`) |> LIST_CONJ |>
  SIMP_RULE (srw_ss()) [FORALL_PROD, AND_IMP_INTRO];

Triviality wf_dec_lem:
  WF $ ($< : num -> num -> bool) LEX measure dec_size
Proof
  simp[WF_LEX]
QED

Triviality dec_ind = MATCH_MP WF_INDUCTION_THM wf_dec_lem;

Theorem evaluate_decs_total_lemma:
  ∀ds env ^s clk.
    (∀clk' d env ^s. clk' < clk ⇒
      ∃s' r. evaluate_dec T env (s with clock := clk') d (s', r)) ∧
    (∀d env ^s. dec_size d < dec1_size ds ⇒
      ∃s' r. evaluate_dec T env (s with clock := clk) d (s', r))
  ⇒ ∃s' r. evaluate_decs T env (s with clock := clk) ds (s',r)
Proof
  Induct >> rw[] >> simp[Once evaluate_dec_cases] >>
  gvs[SF DNF_ss, astTheory.dec_size_def] >>
  first_assum $ qspecl_then [`h`,`env`,`s`] mp_tac >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  Cases_on `r` >> gvs[SF SFY_ss] >> disj2_tac >> goal_assum drule >>
  simp[Once $ GSYM with_same_clock] >> last_x_assum irule >> rw[] >>
  imp_res_tac evaluate_decs_clock_mono >> gvs[] >>
  Cases_on `s'.clock = clk` >> gvs[]
QED

Theorem big_clocked_dec_total:
  ∀env st d.  ∃r. evaluate_dec T env st d r
Proof
  qsuff_tac
    `∀cd env st.
      ∃st' r. evaluate_dec T env (st with clock := FST cd) (SND cd) (st', r)`
  >- (
    rw[] >> first_x_assum $ qspecl_then [`(st.clock, d)`,`env`,`st`] assume_tac >>
    gvs[with_same_clock, SF SFY_ss]
    ) >>
  Induct using dec_ind >> rw[] >>
  PairCases_on `cd` >> rename1 `clk,d` >> gvs[FORALL_PROD, LEX_DEF_THM, SF DNF_ss] >>
  Cases_on `d` >> rw[Once evaluate_dec_cases, SF DNF_ss]
  >- ( (* Dlet *)
    Cases_on `ALL_DISTINCT (pat_bindings p []) ∧
              every_exp (one_con_check env.c) e` >> gvs[] >>
    qspecl_then [`st with clock := clk`,`env`,`e`] assume_tac big_clocked_total >>
    gvs[] >> Cases_on `r` >> gvs[SF SFY_ss] >>
    Cases_on `pmatch env.c s'.refs p a []` >> gvs[SF SFY_ss]
    )
  >- rw[DISJ_EQ_IMP]
  >- rw[DISJ_EQ_IMP]
  >- (
    gvs[astTheory.dec_size_def] >>
    drule_at Any evaluate_decs_total_lemma >>
    disch_then $ qspecl_then [`l`,`env`,`st`] mp_tac >> impl_tac >> rw[] >>
    Cases_on `r` >> gvs[SF SFY_ss]
    )
  >- (
    gvs[astTheory.dec_size_def] >>
    drule_at Any evaluate_decs_total_lemma >>
    disch_then $ qspecl_then [`l`,`env`,`st`] mp_tac >> impl_tac >> rw[] >>
    Cases_on `r` >> gvs[SF SFY_ss] >> disj1_tac >> goal_assum drule >>
    dxrule $ cj 2 evaluate_decs_clock_mono >> rw[] >> gvs[] >>
    simp[Once $ GSYM with_same_clock] >> irule evaluate_decs_total_lemma >>
    rw[] >> Cases_on `s'.clock = clk` >> gvs[]
    )
  >- (
    Cases_on `declare_env st.eval_state env` >> gvs[] >> PairCases_on `x` >> gvs[]
    )
QED

Theorem big_clocked_decs_total:
  ∀ds env st. ∃r. evaluate_decs T env st ds r
Proof
  Induct >> rw[] >> simp[Once evaluate_dec_cases, SF DNF_ss] >>
  qspecl_then [`env`,`st`,`h`] assume_tac big_clocked_dec_total >> gvs[] >>
  PairCases_on `r` >> Cases_on `r1` >> gvs[SF SFY_ss] >>
  disj2_tac >> goal_assum dxrule >> metis_tac[PAIR]
QED

Theorem big_dec_unclocked_no_timeout:
  (∀ck env ^s d r.
    evaluate_dec ck env s d r ⇒ ¬ck ⇒ SND r ≠ Rerr (Rabort Rtimeout_error)) ∧
  (∀ck env ^s ds r.
    evaluate_decs ck env s ds r ⇒ ¬ck ⇒ SND r ≠ Rerr (Rabort Rtimeout_error))
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[] >> gvs[] >>
  imp_res_tac big_unclocked >> gvs[] >>
  Cases_on `r` >> gvs[combine_dec_result_def]
QED

val _ = export_theory ();
