open preamble;
open MiniMLTheory MiniMLTerminationTheory evaluateEquationsTheory;

val _ = new_theory "untypedSafety";

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or
 * gives a result, and it can't do both. *)

val untyped_safety_exp_step = Q.prove (
`∀envC s env e c.
  (e_step (envC, s, env, e, c) = Estuck) =
  (c = []) ∧ ((?v. e = Val v) ∨ (?err. e = Exp (Raise err)))`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac);

val e_step_cenv_same = Q.store_thm("e_step_cenv_same",
`!envC s env e c envC' s' env' e' c'.
  (e_step (envC, s, env, e, c) = Estep (envC', s', env', e', c')) ⇒
  (envC = envC')`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac >>
fs []);

val e_step_rtc_cenv_same_lem = Q.prove (
`!s s'. e_step_reln^* s s' ⇒
  !envC store env e c envC' store' env' e' c'.
  (s = (envC, store, env, e, c)) ∧
  (s' = (envC', store', env', e', c')) ⇒
  (envC = envC')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [] >>
PairCases_on `s'` >>
fs [e_step_reln_def] >>
metis_tac [e_step_cenv_same]);

val e_step_rtc_cenv_same = Q.store_thm("e_step_rtc_cenv_same",
`!envC s env e c envC' s' env' e' c'.
  e_step_reln^* (envC, s, env, e, c) (envC', s', env', e', c')
  ⇒
  (envC = envC')`,
metis_tac [e_step_rtc_cenv_same_lem]);

val small_exp_safety1 = Q.prove (
`!cenv s env e r.
  ¬(e_diverges cenv s env e ∧ ?r. small_eval cenv s env e [] r)`,
rw [e_diverges_def, METIS_PROVE [] ``~x ∨ ~y = y ⇒ ~x``] >>
cases_on `r` >>
cases_on `r'` >>
(TRY (Cases_on `e'`)) >>
fs [small_eval_def, e_step_reln_def] >|
[`∀cenv'' s'' env'' e'' c''.
       e_step (cenv,q,env',Val a,[]) ≠ Estep (cenv'',s'',env'',e'',c'')`
            by rw [e_step_def, continue_def] >>
     metis_tac [],
 metis_tac [e_step_result_distinct],
 `∀cenv'' s'' env'' e''' c''.
    e_step (cenv,q,env',Exp (Raise e''),[]) ≠ Estep (cenv'',s'',env'',e''',c'')`
         by rw [e_step_def, continue_def] >>
     metis_tac []]);

val small_exp_safety2 = Q.prove (
`!cenv s env e.
  e_diverges cenv s env e ∨ ?r. small_eval cenv s env e [] r`,
rw [e_diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, e_step_reln_def] >>
cases_on `e_step (cenv',s',env',e',c')` >>
fs [untyped_safety_exp_step] >>
`cenv = cenv'` by metis_tac [e_step_rtc_cenv_same] >|
[PairCases_on `p` >>
     fs [],
 qexists_tac `(s', Rerr Rtype_error)` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `s', Rval v` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `(s', Rerr (Rraise err))` >>
     rw [small_eval_def] >>
     metis_tac []]);

val untyped_safety_exp = Q.store_thm ("untyped_safety_exp",
`!cenv s env e. (?r. small_eval cenv s env e [] r) = ¬e_diverges cenv s env e`,
metis_tac [small_exp_safety2, small_exp_safety1]);

val untyped_safety_step = Q.prove (
`∀envC s env ds st.
  (d_step (envC, s, env, ds, st) = Dstuck) = (ds = []) ∧ (st = NONE)`,
rw [d_step_def, e_step_def, continue_def, push_def, return_def] >>
cases_on `st` >>
rw [] >-
every_case_tac >>
PairCases_on `x` >> 
rw [] >>
cases_on `x5` >>
rw [] >>
every_case_tac);

val untyped_safety_thm = Q.prove (
`!cenv s env ds.
  diverges cenv s env ds ∨ ?r. d_small_eval cenv s env ds NONE r`,
rw [diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, d_step_reln_def] >>
cases_on `d_step (cenv',s',env',ds',c')` >>
fs [untyped_safety_step] >|
[PairCases_on `p` >> 
     fs [],
 qexists_tac `(d_state_to_store s' c', Rerr (Rraise e))` >>
     rw [d_small_eval_def] >>
     metis_tac [d_state_to_store_thm],
 qexists_tac `(d_state_to_store s' c', Rerr Rtype_error)` >>
     rw [d_small_eval_def] >>
     metis_tac [d_state_to_store_thm],
 qexists_tac `(d_state_to_store s' c', Rval (cenv',env'))` >>
     rw [d_small_eval_def] >>
     metis_tac [d_state_to_store_thm]]);

val untyped_safety_thm2 = Q.prove (
`!cenv s env ds r.
  ¬(diverges cenv s env ds ∧ ?r. d_small_eval cenv s env ds NONE r)`,
rw [diverges_def, METIS_PROVE [] ``~x ∨ ~y = y ⇒ ~x``] >>
cases_on `r` >>
cases_on `r'` >|
[all_tac, cases_on `e`] >>
fs [d_small_eval_def, d_step_reln_def] >|
[PairCases_on `a` >>
     fs [d_small_eval_def, d_step_reln_def] >>
     `∀cenv'' s'' env'' ds'' c''.
         d_step (a0,q,a1,[],NONE) ≠ Dstep (cenv'',s'',env'',ds'',c'')`
              by rw [d_step_def] >>
     metis_tac [],
 metis_tac [d_step_result_distinct],
 metis_tac [d_step_result_distinct]]);

val untyped_safety = Q.store_thm ("untyped_safety",
`!cenv s env ds. (?r. d_small_eval cenv s env ds NONE r) = ~diverges cenv s env ds`,
metis_tac [untyped_safety_thm2, untyped_safety_thm]);

val _ = export_theory ();
