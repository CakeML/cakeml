open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory;

val _ = new_theory "bigClock";

val do_app_cases = Q.store_thm ("do_app_cases",
`!st env op v1 v2 st' env' v3.
  (do_app env st op v1 v2 = SOME (env',st',v3))
  =
  ((?op' n1 n2. 
    (op = Opn op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    ((((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧ 
     (st' = st) ∧ (env' = env) ∧ (v3 = Raise (Con (SOME (Short "Div")) [])) ∨
     ~(((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (env' = env) ∧ (v3 = Lit (IntLit (opn_lookup op' n1 n2))))) ∨
  (?op' n1 n2.
    (op = Opb op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    (st = st') ∧ (env = env') ∧ (v3 = Lit (Bool (opb_lookup op' n1 n2)))) ∨
  ((op = Equality) ∧ (st = st') ∧ (env = env') ∧
      ((?b. (do_eq v1 v2 = Eq_val b) ∧ (v3 = Lit (Bool b))) ∨
       ((do_eq v1 v2 = Eq_closure) ∧ (v3 = Raise (Con (SOME (Short "Eq")) []))))) ∨
  (∃menv'' cenv'' env'' n e.
    (op = Opapp) ∧ (v1 = Closure (menv'',cenv'',env'') n e) ∧
    (st' = st) ∧ (env' = (menv'',cenv'',bind n v2 env'')) ∧ (v3 = e)) ∨
  (?menv'' cenv'' env'' funs n' n'' e.
    (op = Opapp) ∧ (v1 = Recclosure (menv'',cenv'',env'') funs n') ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (st = st') ∧ (env' = (menv'',cenv'', bind n'' v2 (build_rec_env funs (menv'',cenv'',env'') env''))) ∧ (v3 = e)) ∨
  (?lnum.
    (op = Opassign) ∧ (v1 = Loc lnum) ∧ (store_assign lnum v2 st = SOME st') ∧
    (env' = env) ∧ (v3 = Lit Unit)))`,
 SIMP_TAC (srw_ss()) [do_app_def] >>
 cases_on `op` >>
 rw [] 
 >- (cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [])
 >- (cases_on `do_eq v1 v2` >>
     rw [] >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     PairCases_on `p` >>
     rw [] >-
     metis_tac [] >>
     every_case_tac >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     every_case_tac >>
     metis_tac []));

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   ∀r2. evaluate ck env s e r2 ⇒
   (r1 = r2)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   ∀r2. evaluate_list ck env s es r2 ⇒
   (r1 = r2)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   ∀r2. evaluate_match ck env s v pes err_v r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
res_tac >>
fs [] >>
rw [] >> 
metis_tac []);

val do_con_check_build_conv = Q.store_thm ("do_con_check_build_conv",
`!tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v`,
rw [do_con_check_def, build_conv_def] >>
every_case_tac >>
fs []);

val big_unclocked_unchanged = Q.prove (
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1)))`,
ho_match_mp_tac evaluate_ind >>
rw []);

val big_unclocked_ignore = Q.prove (
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate F env (count2,st) e ((count2, st'), r)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate_list F env (count2,st) es ((count2, st'), r)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r)) ∧
       (r ≠ Rerr Rtimeout_error)
       ⇒
       evaluate_match F env (count2,st) v pes err_v ((count2, st'), r))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases]>>
TRY (PairCases_on `s'`) >>
fs [] >>
rw [] >>
metis_tac []);

val big_unclocked = Q.store_thm ("big_unclocked",
`!count s env e count' s' r env.
  (evaluate F env (count, s) e ((count',s'), r)
   ⇒
   (r ≠ Rerr Rtimeout_error) ∧
   (count = count')) ∧
  (evaluate F env (count, s) e ((count,s'), r)
   =
   evaluate F env (count', s) e ((count',s'), r))`,
rw [] >>
metis_tac [big_unclocked_ignore, big_unclocked_unchanged, FST, SND]);

val dec_count_add = Q.prove (
`!op count extra.
  (op ≠ Opapp ⇒ dec_count op count = count) ∧ 
  (dec_count Opapp (count + 1) = count) ∧
  (count ≠ 0 ⇒ dec_count Opapp (count + extra) = dec_count Opapp count + extra)`,
rw [dec_count_def] >>
decide_tac);

val dec_count_sub = Q.prove (
`!op count extra.
  (extra ≤ count ⇒ dec_count Opapp (count - extra) = dec_count Opapp count - extra)`,
rw [dec_count_def] >>
decide_tac);

val add_to_counter = Q.store_thm ("add_to_counter",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s' r' extra.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate T env (count+extra,s0) e ((count'+extra,s'),r')) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s' r' extra.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate_list T env (count+extra,s0) es ((count'+extra,s'),r')) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   !s0 count count' s' r' extra.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (r' ≠ Rerr Rtimeout_error) ∧
   (ck = T) ⇒
   evaluate_match T env (count+extra,s0) v pes err_v ((count'+extra,s'),r'))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases] >|
[PairCases_on `s'` >>
     fs [] >>
     metis_tac [],
 metis_tac [],
 metis_tac [],
 fs [] >>
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
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s' r'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (ck = F) ⇒
   ∃count1. evaluate T env (count1,s0) e ((0,s'),r')) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = F) ⇒
   ∃count1. evaluate_list T env (count1,s0) es ((0,s'),r')) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = F) ⇒
   ∃count1. evaluate_match T env (count1,s0) v pes err_v ((0,s'),r'))`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >>
 rw [Once evaluate_cases] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >- (
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
                arithmeticTheory.ADD_0, result_distinct, error_result_distinct, result_11]) >-
 tac >-
 tac >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 tac >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac [] >-
 metis_tac []);

val clock_monotone = Q.prove (
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s' r'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),r')) ∧
   (ck = T) ⇒
   (count' ≤ count)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s' r'.
   (r1 = ((count',s'),r')) ∧
   (s = (count, s0)) ∧
   (ck = T) ⇒
   (count' ≤ count)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
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
`!s env e s' r1 count1.
  evaluate F env (count1,s) e ((count1, s'), r1) = 
  ?count. evaluate T env (count,s) e ((0,s'),r1) ∧ 
          (r1 ≠ Rerr Rtimeout_error)`, 
metis_tac [add_clock, big_unclocked_ignore, big_unclocked]);

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
      ∃count1 s1 r1.
        evaluate T env' (p_1,s') p_2 ((count1,s1),r1))
⇒
?s2 count2 r2. evaluate_list T env (count',s) l ((count2,s2),r2)`,
induct_on `l` >>
rw [] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
`exp_size h < exp_size (Con i (h::l)) ∧
 exp_size (Con i l) < exp_size (Con i (h::l))`
         by srw_tac [ARITH_ss] [exp_size_def] >>
`?count1 s1 r1. evaluate T env (count',s) h ((count1,s1),r1)`
          by metis_tac [] >>
`?count2 s2 r2. evaluate_list T env (count1, s1) l ((count2,s2),r2)`
                by metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ, arithmeticTheory.LESS_TRANS] >>
metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]);

val eval_match_total = Q.prove (
`∀s env l i count' v err_v.
  (∀p_1 p_2.
    p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Mat e' l) ⇒
    ∀s env.
      ∃count'' s' r.
        evaluate T env (p_1,s) p_2 ((count'',s'),r))
⇒
?s2 count2 r2. evaluate_match T env (count',s) v l err_v ((count2,s2),r2)`,
induct_on `l` >>
rw [] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
`?p e. h = (p,e)` by metis_tac [pair_CASES] >>
rw [] >>
`exp_size e < exp_size (Mat e' ((p,e)::l)) ∧
 exp_size (Mat e' l) < exp_size (Mat e' ((p,e)::l))`
         by srw_tac [ARITH_ss] [exp_size_def] >>
PairCases_on `env` >>
`(pmatch env1 s p v env2 = Match_type_error) ∨ 
 (pmatch env1 s p v env2 = No_match) ∨ 
 (?env'. pmatch env1 s p v env2 = Match env')`
            by metis_tac [match_result_nchotomy] >>
rw [] >>
metis_tac [arithmeticTheory.LESS_TRANS]);

val eval_handle_total = Q.prove (
`∀env s l i count' v err_v.
  (∀p_1 p_2.
    p_1 < count' ∨ p_1 = count' ∧ exp_size p_2 < exp_size (Handle e' l) ⇒
    ∀s env.
      ∃count'' s' r.
        evaluate T env (p_1,s) p_2 ((count'',s'),r))
⇒
?count2 s2 r2. evaluate_match T env (count',s) v l err_v ((count2,s2),r2)`,
induct_on `l` >>
rw [] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
`?p e. h = (p,e)` by metis_tac [pair_CASES] >>
rw [] >>
`exp_size e < exp_size (Handle e' ((p,e)::l)) ∧
 exp_size (Handle e' l) < exp_size (Handle e' ((p,e)::l))`
         by srw_tac [ARITH_ss] [exp_size_def] >>
PairCases_on `env` >>
`(pmatch env1 s p v env2 = Match_type_error) ∨ 
 (pmatch env1 s p v env2 = No_match) ∨ 
 (?env'. pmatch env1 s p v env2 = Match env')`
            by metis_tac [match_result_nchotomy] >>
rw [] >>
metis_tac [arithmeticTheory.LESS_TRANS]);

val evaluate_raise_empty_ctor = Q.prove (
`!ck s env x cn.
  ?err. evaluate ck env s (Raise (Con cn [])) (s, Rerr err)`,
 ntac 5 (rw [Once evaluate_cases]) >>
 every_case_tac >>
 rw [] >>
 metis_tac [do_con_check_build_conv]);

val big_clocked_total_lem = Q.prove (
`!count_e env s.
  ∃count' s' r. evaluate T env (FST count_e,s) (SND count_e) ((count',s'), r)`,
 ho_match_mp_tac ind >>
 rw [] >>
 `?count e. count_e = (count,e)` by (PairCases_on `count_e` >> fs []) >>
 rw [] >>
 fs [FORALL_PROD, LEX_DEF_THM] >>
 cases_on `e` >>
 rw [Once evaluate_cases] 
 >- ((* Raise *)
     `exp_size e' < exp_size (Raise e')` by srw_tac [ARITH_ss] [exp_size_def] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES])
 >- ((* Handle *)
     `exp_size e' < exp_size (Handle e' l)` by srw_tac [ARITH_ss] [exp_size_def] >>
     PairCases_on `env` >>
     `?count1 s1 r1. evaluate T (env0,env1,env2) (count',s) e' ((count1,s1),r1)` by metis_tac [] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] 
     >- (cases_on `err` >>
         fs [] >-
         metis_tac [] >-
         (`?count2 s2 r2. evaluate_match T (env0,env1,env2) (count1,s1) v l v ((count2,s2),r2)`
                  by metis_tac [eval_handle_total, arithmeticTheory.LESS_TRANS, 
                                clock_monotone, arithmeticTheory.LESS_OR_EQ, pair_CASES] >>
          metis_tac []) >-
         metis_tac [])
     >- metis_tac []) 
 >- ((* Con *)
     `?count2 s2 r2. evaluate_list T env (count',s) l ((count2,s2),r2)`
               by metis_tac [pair_CASES, eval_list_total] >>
     metis_tac [do_con_check_build_conv, result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES])
 >- ((* Var *)
     cases_on `lookup_var_id i env` >>
         rw []) 
 >- ((* Uapp *)
     `exp_size e' < exp_size (Uapp u e')`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES])
 >- ((* App *)
     `exp_size e' < exp_size (App o' e' e0) ∧
      exp_size e0 < exp_size (App o' e' e0)`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     PairCases_on `env` >>
     `?count1 s1 r1. evaluate T (env0,env1,env2) (count',s) e' ((count1,s1),r1)`
            by metis_tac [] >>
     `?count2 s2 r2. evaluate T (env0,env1,env2) (count1,s1) e0 ((count2,s2),r2)`
            by metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] >-
     metis_tac [] >>
     `(?err. r2 = Rerr err) ∨ (?v. r2 = Rval v)` by (cases_on `r2` >> metis_tac []) >>
     rw [] >-
     metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(do_app (env0,env1,env2) s2 o' v v' = NONE) ∨ (?s3 env' e2. do_app (env0,env1,env2) s2 o' v v' = SOME (s3,env',e2))`
                by metis_tac [optionTheory.option_nchotomy, pair_CASES] >-
     metis_tac [] >>
     cases_on `o' = Opapp` >|
     [cases_on `count2 = 0` >>
          rw [] >-
          metis_tac [] >>
          `dec_count Opapp count2 < count2` by srw_tac [ARITH_ss] [dec_count_def] >>
          metis_tac [pair_CASES, clock_monotone, arithmeticTheory.LESS_OR_EQ, arithmeticTheory.LESS_TRANS],
      `(?l. e2 = Lit l) ∨ (e2 = Raise (Con (SOME (Short "Div")) [])) ∨ (e2 = Raise (Con (SOME (Short "Eq")) []))`
                  by fs [do_app_cases] >-
          prove_tac [evaluate_rules] >>
          metis_tac [evaluate_raise_empty_ctor]])
 >- ((* Log *)
     `exp_size e' < exp_size (Log l e' e0) ∧
      exp_size e0 < exp_size (Log l e' e0)`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     `?count1 s1 r1. evaluate T env (count',s) e' ((count1,s1),r1)`
            by metis_tac [pair_CASES] >>
     `?count2 s2 r2. evaluate T env (count1,s1) e0 ((count2,s2),r2)`
            by metis_tac [pair_CASES, clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] >-
     metis_tac [] >>
     `(do_log l v e0 = NONE) ∨ (?lit. do_log l v e0 = SOME (Lit lit)) ∨ (do_log l v e0 = SOME e0)`
                by (rw [do_log_def] >>
                    cases_on `v` >>
                    rw [] >>
                    cases_on `l'` >>
                    rw [] >>
                    cases_on `l` >>
                    rw []) >-
     metis_tac [] >-
     prove_tac [evaluate_rules] >>
     metis_tac [clock_monotone, arithmeticTheory.LESS_OR_EQ])
 >- ((* If *)
     `exp_size e' < exp_size (If e' e0 e1) ∧
      exp_size e0 < exp_size (If e' e0 e1) ∧
      exp_size e1 < exp_size (If e' e0 e1)`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     `?count1 s1 r1. evaluate T env (count',s) e' ((count1,s1),r1)`
            by metis_tac [pair_CASES] >>
     `?count2 s2 r2. evaluate T env (count1,s1) e0 ((count2,s2),r2)`
            by metis_tac [pair_CASES, clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `?count2 s2 r2. evaluate T env (count1,s1) e1 ((count2,s2),r2)`
            by metis_tac [pair_CASES, clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] >-
     metis_tac [] >>
     `(do_if v e0 e1 = NONE) ∨ (do_if v e0 e1 = SOME e0) ∨ (do_if v e0 e1 = SOME e1)`
                 by (rw [do_if_def]) >>
     metis_tac [])
 >- ((* match *)
     `exp_size e' < exp_size (Mat e' l)`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     `?count1 s1 r1. evaluate T env (count',s) e' ((count1,s1),r1)`
            by metis_tac [pair_CASES] >>
     `(?err. r1 = Rerr err) ∨ (?v. r1 = Rval v)` by (cases_on `r1` >> metis_tac []) >>
     rw [] >-
     metis_tac [] >>
     `?count2 s2 r2. evaluate_match T env (count1,s1) v l (Conv (SOME (Short "Bind", TypeExn)) []) ((count2,s2),r2)`
               by metis_tac [eval_match_total, arithmeticTheory.LESS_TRANS, 
                             pair_CASES, clock_monotone, arithmeticTheory.LESS_OR_EQ] >>
     metis_tac [])
 >- ((* Let *)
     `exp_size e' < exp_size (Let s' e' e0) ∧
      exp_size e0 < exp_size (Let s' e' e0)`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES,
                clock_monotone, arithmeticTheory.LESS_OR_EQ]) 
 >- ((* Letrec *)
     `exp_size e' < exp_size (Letrec l e')`
            by srw_tac [ARITH_ss] [exp_size_def] >>
     metis_tac [result_nchotomy, optionTheory.option_nchotomy, error_result_nchotomy, pair_CASES]));

val big_clocked_total = Q.store_thm ("big_clocked_total",
`!count s env e.
  ∃count' s' r. evaluate T env (count,s) e ((count',s'), r)`,
metis_tac [big_clocked_total_lem, FST, SND]);

val big_clocked_timeout_0 = Q.store_thm ("big_clocked_timeout_0",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr Rtimeout_error)) ∧
   (ck = T)
   ⇒
   (count' = 0)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr Rtimeout_error)) ∧
   (ck = T)
   ⇒
   (count' = 0)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   !s0 count count' s'.
   (s = (count, s0)) ∧
   (r1 = ((count',s'),Rerr Rtimeout_error)) ∧
   (ck = T)
   ⇒
   (count' = 0))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
PairCases_on `s'` >>
rw []);

val big_clocked_unclocked_equiv_timeout = Q.store_thm ("big_clocked_unclocked_equiv_timeout",
`!s env e count1.
  (!r. ¬evaluate F env (count1,s) e r) = 
  (∀count. ?s'. evaluate T env (count,s) e ((0,s'),Rerr Rtimeout_error))`,
rw [] >>
eq_tac >>
rw [] >|
[`?count1 s1 r1. evaluate T env (count',s) e ((count1,s1),r1)` 
             by metis_tac [big_clocked_total] >>
     metis_tac [big_unclocked_ignore, big_unclocked,big_clocked_timeout_0,
                result_distinct,result_11, error_result_distinct,result_nchotomy, error_result_nchotomy],
 metis_tac [big_exp_determ, pair_CASES, PAIR_EQ, big_unclocked, add_clock]]);

val dec_evaluate_not_timeout = Q.store_thm ("dec_evaluate_not_timeout",
`!mn s env d s' r.
  evaluate_dec mn env s d (s', r) ⇒ r ≠ Rerr Rtimeout_error`,
rw [evaluate_dec_cases] >>
metis_tac [big_unclocked]);

val decs_evaluate_not_timeout = Q.store_thm ("decs_evaluate_not_timeout",
`!mn env s ds r.
  evaluate_decs mn env s ds r ⇒
    !s' cenv' r'. r = (s', cenv', r') ⇒ r' ≠ Rerr Rtimeout_error`,
ho_match_mp_tac evaluate_decs_ind >>
rw [] >-
metis_tac [dec_evaluate_not_timeout] >>
cases_on `r` >>
rw [combine_dec_result_def]);

val top_evaluate_not_timeout = Q.store_thm ("top_evaluate_not_timeout",
`!mn env s top s' cenv' r.
  evaluate_top env s top (s', cenv', r) ⇒ r ≠ Rerr Rtimeout_error`,
rw [evaluate_top_cases] >>
metis_tac [dec_evaluate_not_timeout, decs_evaluate_not_timeout]);

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
 >- metis_tac [dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- metis_tac [dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- metis_tac [dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- metis_tac [dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]
 >- (PairCases_on `s'` >>
     fs [] >>
     disj1_tac >>
     qexists_tac `v1` >>
     qexists_tac `v2` >>
     qexists_tac `env'` >>
     qexists_tac `e''` >>
     qexists_tac `(s'0 - extra, s'1)` >>
     qexists_tac `s3` >>
     qexists_tac `count' - extra` >>
     qexists_tac `s4` >>
     cases_on `op ≠ Opapp` >-
     metis_tac [dec_count_sub, dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``] >>
     fs [] >>
     `s'0 ≤ count''+extra ∧ count' ≤ s'0 ∧ count'''+extra ≤ dec_count Opapp count'` by metis_tac [clock_monotone] >>
     `count'≤ s'0` by metis_tac [clock_monotone] >>
     fs [dec_count_def] >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [] >>
     NO_TAC) >>
 metis_tac [dec_count_sub, dec_count_add, pair_CASES, FST, clock_monotone, DECIDE ``y + z ≤ x ⇒ (x = (x - z) + z:num)``]);

val clocked_min_counter = Q.store_thm ("clocked_min_counter",
`!count s0 env e count' s' r'.
evaluate T env (count,s0) e ((count',s'),r')
⇒
evaluate T env (count-count',s0) e ((0, s'), r')`,
 rw [] >>
 `count'' ≤ count'` by metis_tac [clock_monotone, PAIR_EQ, FST, SND, pair_CASES] >>
 `count'' = 0 + count'' ∧ count' = (count' - count'') + count'':num` by decide_tac >>
 metis_tac [sub_from_counter]);

val _ = export_theory ();
