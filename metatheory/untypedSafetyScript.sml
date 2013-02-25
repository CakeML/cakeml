open preamble;
open MiniMLTheory MiniMLTerminationTheory evaluateEquationsTheory determTheory;

val _ = new_theory "untypedSafety";

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or
 * gives a result, and it can't do both. *)

val untyped_safety_exp_step = Q.prove (
`∀menv cenv s env e c.
  (e_step (menv,cenv, s, env, e, c) = Estuck) =
  (c = []) ∧ ((?v. e = Val v) ∨ (?err. e = Exp (Raise err)))`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac);

val e_step_cenv_same = Q.store_thm("e_step_cenv_same",
`!menv cenv s env e c menv' cenv' s' env' e' c'.
  (e_step (menv,cenv, s, env, e, c) = Estep (menv',cenv', s', env', e', c')) ⇒
  (cenv = cenv') ∧ (menv = menv')`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac >>
fs []);

val e_step_rtc_cenv_same_lem = Q.prove (
`!s s'. e_step_reln^* s s' ⇒
  !menv cenv store env e c menv' cenv' store' env' e' c'.
  (s = (menv,cenv, store, env, e, c)) ∧
  (s' = (menv',cenv', store', env', e', c')) ⇒
  (cenv = cenv') ∧ (menv = menv')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [] >>
PairCases_on `s'` >>
fs [e_step_reln_def] >>
metis_tac [e_step_cenv_same]);

val e_step_rtc_cenv_same = Q.store_thm("e_step_rtc_cenv_same",
`!menv cenv s env e c menv' cenv' s' env' e' c'.
  e_step_reln^* (menv,cenv, s, env, e, c) (menv',cenv', s', env', e', c')
  ⇒
  (cenv = cenv') ∧ (menv = menv')`,
metis_tac [e_step_rtc_cenv_same_lem]);

val small_exp_safety1 = Q.prove (
`!menv cenv s env e r.
  ¬(e_diverges menv cenv s env e ∧ ?r. small_eval menv cenv s env e [] r)`,
rw [e_diverges_def, METIS_PROVE [] ``~x ∨ ~y = y ⇒ ~x``] >>
cases_on `r` >>
cases_on `r'` >>
(TRY (Cases_on `e'`)) >>
fs [small_eval_def, e_step_reln_def] >|
[`∀menv'' cenv'' s'' env'' e'' c''.
       e_step (menv,cenv,q,env',Val a,[]) ≠ Estep (menv'',cenv'',s'',env'',e'',c'')`
            by rw [e_step_def, continue_def] >>
     metis_tac [],
 metis_tac [e_step_result_distinct],
 `∀menv'' cenv'' s'' env'' e''' c''.
    e_step (menv,cenv,q,env',Exp (Raise e''),[]) ≠ Estep (menv'',cenv'',s'',env'',e''',c'')`
         by rw [e_step_def, continue_def] >>
     metis_tac []]);

val small_exp_safety2 = Q.prove (
`!menv cenv s env e.
  e_diverges menv cenv s env e ∨ ?r. small_eval menv cenv s env e [] r`,
rw [e_diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, e_step_reln_def] >>
cases_on `e_step (menv',cenv',s',env',e',c')` >>
fs [untyped_safety_exp_step] >>
`(cenv = cenv') ∧ (menv = menv')` by metis_tac [e_step_rtc_cenv_same] >|
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
`!menv cenv s env e. (?r. small_eval menv cenv s env e [] r) = ¬e_diverges menv cenv s env e`,
metis_tac [small_exp_safety2, small_exp_safety1]);

val untyped_safety_dec = Q.store_thm ("untyped_safety_dec",
`!mn menv cenv s env d. (∃r. evaluate_dec mn menv cenv s env d r) = ~dec_diverges menv cenv s env d`,
rw [Once evaluate_dec_cases, dec_diverges_def] >>
cases_on `d` >>
rw [] >|
[eq_tac >>
     rw [GSYM untyped_safety_exp] >-
     metis_tac [] >-
     metis_tac [] >-
     metis_tac [] >-
     metis_tac [] >-
     metis_tac [] >>
     fs [GSYM untyped_safety_exp] >>
     PairCases_on `r` >>
     fs [] >>
     cases_on `r1` >>
     fs [] >|
     [cases_on `ALL_DISTINCT (pat_bindings p [])` >>
          fs [] >|
          [cases_on `pmatch o' cenv r0 p a emp` >>
               fs [] >|
               [qexists_tac `(r0, Rerr (Rraise Bind_error))` >>
                    rw [] >>
                    metis_tac [],
                qexists_tac `(r0, Rerr Rtype_error)` >>
                    rw [] >>
                    metis_tac [],
                fs [merge_def, emp_def] >-
                    metis_tac [] >>
                    `?r. evaluate_decs mn menv cenv r0 (l ++ env) ds r` by metis_tac [] >>
                    PairCases_on `r` >>
                    metis_tac [APPEND]],
           qexists_tac `(r0, Rerr Rtype_error)` >>
               rw [] >>
               metis_tac []],
      qexists_tac `(r0,Rerr e')` >>
          rw []],
 metis_tac [],
 metis_tac []]);

val untyped_safety_decs = Q.store_thm ("untyped_safety_decs",
`!mn menv cenv s env ds. (?r. evaluate_decs mn menv cenv s env ds r) = ~decs_diverges mn menv cenv s env ds`,
induct_on `ds` >>
rw [] >-
rw [Once evaluate_decs_cases, Once decs_diverges_cases] >>
rw [Once evaluate_decs_cases, Once decs_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
imp_res_tac dec_determ >>
fs [] >>
rw [] >>
pop_assum mp_tac >>
rw [] >>
metis_tac [untyped_safety_dec, pair_CASES, result_nchotomy]);

val untyped_safety_prog = Q.store_thm ("untyped_safety_prog",
`!menv cenv s env ds. (?r. evaluate_prog menv cenv s env ds r) = ~prog_diverges menv cenv s env ds`,
induct_on `ds` >>
rw [] >-
rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
imp_res_tac dec_determ >>
imp_res_tac decs_determ >>
fs [] >>
rw [] >>
pop_assum mp_tac >>
rw [] >>
metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]);

val _ = export_theory ();
