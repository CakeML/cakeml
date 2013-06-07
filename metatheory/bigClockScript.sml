open preamble;
open BigStepTheory SemanticPrimitivesTheory;

val _ = new_theory "bigClock";

val do_app_cases = Q.store_thm ("do_app_cases",
`!st env op v1 v2 st' env' v3.
  (do_app st env op v1 v2 = SOME (st',env',v3))
  =
  ((?op' n1 n2. 
    (op = Opn op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    ((((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧ 
     (st' = st) ∧ (env' = env) ∧ (v3 = Raise Div_error) ∨
     ~(((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (env' = env) ∧ (v3 = Lit (IntLit (opn_lookup op' n1 n2))))) ∨
  (?op' n1 n2.
    (op = Opb op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    (st = st') ∧ (env = env') ∧ (v3 = Lit (Bool (opb_lookup op' n1 n2)))) ∨
  ((op = Equality) ∧ ¬contains_closure v1 ∧ ~contains_closure v2 ∧ 
   (st = st') ∧ (env = env') ∧ (v3 = Lit (Bool (v1 = v2)))) ∨
  (∃env'' n e.
    (op = Opapp) ∧ (v1 = Closure env'' n e) ∧
    (st' = st) ∧ (env' = bind n v2 env'') ∧ (v3 = e)) ∨
  (?env'' funs n' n'' e.
    (op = Opapp) ∧ (v1 = Recclosure env'' funs n') ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (st = st') ∧ (env' = bind n'' v2 (build_rec_env funs env'' env'')) ∧ (v3 = e)) ∨
  (?lnum.
    (op = Opassign) ∧ (v1 = Loc lnum) ∧ (store_assign lnum v2 st = SOME st') ∧
    (env' = env) ∧ (v3 = Lit Unit)))`,
SIMP_TAC (srw_ss()) [do_app_def] >>
cases_on `op` >>
rw [] >|
[cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [],
 cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [],
 metis_tac [],
 cases_on `v1` >>
     rw [] >-
     metis_tac [] >>
     every_case_tac >>
     metis_tac [],
 cases_on `v1` >>
     rw [] >>
     every_case_tac >>
     metis_tac []]);


val big_unclocked_unchanged = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1)))`,
ho_match_mp_tac evaluate_ind >>
rw []);

val big_unclocked_ignore = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate F menv cenv (count2,st) env e ((count2, st'), r)) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate_list F menv cenv (count2,st) env es ((count2, st'), r)) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate_match F menv cenv (count2,st) env v pes ((count2, st'), r))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases]>>
TRY (PairCases_on `s'`) >>
fs [] >>
rw [] >>
metis_tac []);

val big_unclocked = Q.store_thm ("big_unclocked",
`!(menv : envM) (cenv : envC) count s env e count' s' r env.
  (evaluate F menv cenv (count, s) env e ((count',s'), r)
   ⇒
   (r ≠ Rerr Rtimeout_error) ∧
   (count = count')) ∧
  (evaluate F menv cenv (count, s) env e ((count,s'), r)
   =
   evaluate F menv cenv (count', s) env e ((count',s'), r))`,
rw [] >>
metis_tac [big_unclocked_ignore, big_unclocked_unchanged, FST, SND]);

val dec_count_add = Q.prove (
`!op count extra.
  (op ≠ Opapp ⇒ dec_count op count = count) ∧ 
  (dec_count Opapp (count + 1) = count) ∧
  (count ≠ 0 ⇒ dec_count Opapp (count + extra) = dec_count Opapp count + extra)`,
rw [dec_count_def] >>
decide_tac);

val add_to_counter = Q.store_thm ("add_to_counter",
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
   !s0 count count' s' r' extra.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate T menv cenv (count+extra,s0) env e ((count'+extra,s'),r')) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
   !s0 count count' s' r' extra.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate_list T menv cenv (count+extra,s0) env es ((count'+extra,s'),r')) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
   !s0 count count' s' r' extra.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate_match T menv cenv (count+extra,s0) env v pes ((count'+extra,s'),r'))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases] >|
[PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 metis_tac [],
 metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     disj1_tac >>
     qexists_tac `v1` >>
     qexists_tac `v2` >>
     qexists_tac `env'` >>
     qexists_tac `e''` >>
     qexists_tac `(s'0+extra, s'1)` >>
     qexists_tac `s3` >>
     qexists_tac `count'+extra` >>
     qexists_tac `s4` >>
     rw [] >>
     cases_on `op = Opapp` >>
     fs [] >>
     metis_tac [dec_count_add],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     metis_tac []]);

val tac = 
  TRY (PairCases_on `s'`) >>
  fs [] >>
  metis_tac [add_to_counter, arithmeticTheory.ADD_COMM,
             arithmeticTheory.ADD_0, result_distinct, error_result_distinct,
             result_11];

val add_clock = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
   !s0 count count' s' r'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (ck = F) ⇒
   ∃count1. evaluate T menv cenv (count1,s0) env e ((0,s'),r')) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = F) ⇒
   ∃count1. evaluate_list T menv cenv (count1,s0) env es ((0,s'),r')) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = F) ⇒
   ∃count1. evaluate_match T menv cenv (count1,s0) env v pes ((0,s'),r'))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases] >|
[metis_tac [],
 tac,
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 PairCases_on `s'` >>
     fs [] >>
     Q.ABBREV_TAC `inc = if op = Opapp then 1:num else 0` >>
     qexists_tac `count1+count1'+inc+count1''` >>
     rw [] >>
     disj1_tac >>
     qexists_tac `v1` >>
     qexists_tac `v2` >>
     qexists_tac `env'` >>
     qexists_tac `e''` >>
     qexists_tac `(count1+count1'+inc,s'1)` >>
     qexists_tac `s3` >>
     qexists_tac `count1+inc` >>
     qexists_tac `s4` >>
     rw [] >>
     UNABBREV_ALL_TAC >>
     fs [dec_count_add] >>
     rw [] >>
     fs [dec_count_add] >>
     metis_tac [add_to_counter, arithmeticTheory.ADD_COMM,
                arithmeticTheory.ADD_0, result_distinct, error_result_distinct, result_11],
 tac,
 tac,
 metis_tac [],
 tac,
 metis_tac [],
 metis_tac [],
 tac,
 metis_tac [],
 metis_tac [],
 tac,
 metis_tac [],
 tac,
 metis_tac [],
 metis_tac [],
 tac,
 metis_tac [],
 tac,
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac []]);

val clock_monotone = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
   !s0 count count' s' r'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (ck = T) ⇒
   (count' ≤ count)) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = T) ⇒
   (count' ≤ count)) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = T) ⇒
   (count' ≤ count))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases] >>
PairCases_on `s'` >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
cases_on `op` >>
full_simp_tac (srw_ss()++ARITH_ss) [dec_count_def]);


val big_clocked_unclocked_equiv = Q.store_thm ("big_clocked_unclocked_equiv",
`!(menv : envM) (cenv : envC) s env e s' r1 count1.
  evaluate F menv cenv (count1,s) env e ((count1, s'), r1) = 
  ?count. evaluate T menv cenv (count,s) env e ((0,s'),r1) ∧ 
          (r1 ≠ Rerr Rtimeout_error)`, 
metis_tac [add_clock, big_unclocked_ignore, big_unclocked]);

val wf_lem = Q.prove (
`WF (($< :(num->num->bool)) LEX measure exp_size)`,
rw [] >>
match_mp_tac WF_LEX >>
rw [prim_recTheory.WF_LESS]);

val ind = SIMP_RULE (srw_ss()) [wf_lem] (Q.ISPEC `(($< :(num->num->bool)) LEX measure exp_size)` WF_INDUCTION_THM)

val eval_list_total = Q.prove (
`∀(menv : envM) (cenv : envC) s env l i count'.
(∀p_1 p_2.
    p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Con i l) ⇒
    ∀menv' (cenv':envC) s' env'.
      ∃count1 s1 r1.
        evaluate T menv' cenv' (p_1,s') env' p_2 ((count1,s1),r1))
⇒
?s2 count2 r2. evaluate_list T menv cenv (count',s) env l ((count2,s2),r2)`,
induct_on `l` >>
rw [] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
`exp_size h < exp_size (Con i (h::l)) ∧
 exp_size (Con i l) < exp_size (Con i (h::l))`
         by srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
`?count1 s1 r1. evaluate T menv cenv (count',s) env h ((count1,s1),r1)`
          by metis_tac [] >>
`?count2 s2 r2. evaluate_list T menv cenv (count1, s1) env l ((count2,s2),r2)`
                by metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ, arithmeticTheory.LESS_TRANS] >>
metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES, AstTheory.error_nchotomy]);

(*
val big_clocked_total = Q.store_thm ("big_clocked_total",
`!count_e (menv : envM) (cenv : envC) s env.
  ∃count' s' r. evaluate T menv cenv (FST count_e,s) env (SND count_e) ((count',s'), r)`,

ho_match_mp_tac ind >>
rw [] >>
`?count e. count_e = (count,e)` by (PairCases_on `count_e` >> fs []) >>
rw [] >>
fs [FORALL_PROD, LEX_DEF_THM] >>
cases_on `e` >>
rw [Once evaluate_cases] >|
[(* Handle *)
     `exp_size e' < exp_size (Handle e' s' e0) ∧
      exp_size e0 < exp_size (Handle e' s' e0)`
            by srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
     `?count1 s1 r1. evaluate T menv cenv (count',s) env e' ((count1,s1),r1)`
            by metis_tac [] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES, AstTheory.error_nchotomy,
                clock_monotone, arithmeticTheory.LESS_OR_EQ],
 (* Con *)
     `?count2 s2 r2. evaluate_list T menv cenv (count',s) env l ((count2,s2),r2)`
               by metis_tac [eval_list_total] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES, AstTheory.error_nchotomy],
 (* Var *)
     cases_on `lookup_var_id i menv env` >>
         rw [],
 (* Uapp *)
     `exp_size e' < exp_size (Uapp u e')`
            by srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES],
 (* App *)
     `exp_size e' < exp_size (App o' e' e0) ∧
      exp_size e0 < exp_size (App o' e' e0)`
            by srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
     `?count1 s1 r1. evaluate T menv cenv (count',s) env e' ((count1,s1),r1)`
            by metis_tac [] >>
     `?count2 s2 r2. evaluate T menv cenv (count1,s1) env e0 ((count2,s2),r2)`
            by metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] >-
     metis_tac [] >>
     `(?err. r2 = Rerr err) ∨ (?v. r2 = Rval v)` by (cases_on `r2` >> metis_tac []) >>
     rw [] >-
     metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(do_app s2 env o' v v' = NONE) ∨ (?s3 env' e2. do_app s2 env o' v v' = SOME (s3,env',e2))`
                by metis_tac [optionTheory.option_nchotomy, pair_CASES] >-
     metis_tac [] >>
     all_tac,
 (* Log *)
     all_tac,
 (* If *)
     `exp_size e' < exp_size (If e' e0 e1) ∧
      exp_size e0 < exp_size (If e' e0 e1) ∧
      exp_size e1 < exp_size (If e' e0 e1)`
            by srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
      all_tac,
 (* match *)
     all_tac,
 (* Let *)
     all_tac,
 (* Letrec *)
     all_tac]


     *)
     (*
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES, AstTheory.error_nchotomy,
                clock_monotone, arithmeticTheory.LESS_OR_EQ],
                *)
val _ = export_theory ();
