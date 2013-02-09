open preamble;
open MiniMLTheory MiniMLTerminationTheory evaluateEquationsTheory determTheory;

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

val untyped_safety = Q.store_thm ("untyped_safety",
`!cenv s env ds. (?r. evaluate_decs cenv s env ds r) = ~diverges cenv s env ds`,
induct_on `ds` >>
rw [] >-
rw [Once evaluate_decs_cases, Once diverges_cases] >>
rw [Once evaluate_decs_cases, Once diverges_cases] >>
cases_on `h` >>
rw [evaluate_dec_cases, d_diverges_def] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
imp_res_tac small_exp_determ >>
fs [] >>
rw [] >>
pop_assum mp_tac >>
rw [GSYM untyped_safety_exp] >|
[metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 cheat,
 metis_tac [],
 cheat,
 metis_tac [],
 cheat]);

val _ = export_theory ();
