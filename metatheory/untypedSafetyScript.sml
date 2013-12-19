open preamble;
open libTheory astTheory bigStepTheory smallStepTheory semanticPrimitivesTheory
open determTheory bigSmallEquivTheory
open terminationTheory bigClockTheory;

val _ = new_theory "untypedSafety";

(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or
 * gives a result, and it can't do both. *)

val untyped_safety_exp_step = Q.prove (
`∀env s e c.
  (e_step (env,s,e,c) = Estuck) =
  ((?v. e = Val v) ∧ ((c = []) ∨ (?env. c = [(Craise (), env)])))`,
rw [e_step_def, continue_def, push_def, return_def] >>
every_case_tac >>
metis_tac [oneTheory.one]);

val small_exp_safety1 = Q.prove (
`!s env e r.
  ¬(e_diverges env s e ∧ ?r. small_eval env s e [] r)`,
rw [e_diverges_def, METIS_PROVE [] ``(~x ∨ ~y) = (y ⇒ ~x)``] >>
cases_on `r` >>
cases_on `r'` >>
(TRY (Cases_on `e'`)) >>
fs [small_eval_def, e_step_reln_def] >|
[`∀s'' env'' e'' c''.
       e_step (env',q,Val a,[]) ≠ Estep (env'',s'',e'',c'')`
            by rw [e_step_def, continue_def] >>
     metis_tac [],
 metis_tac [e_step_result_distinct],
 `∀s'' env''' e''' c''.
    e_step (env',q,Val v,[(Craise (),env'')]) ≠ Estep (env''',s'',e''',c'')`
         by rw [push_def, e_step_def, continue_def] >>
     metis_tac []]);

val small_exp_safety2 = Q.prove (
`!menv cenv s env e. e_diverges env s e ∨ ?r. small_eval env s e [] r`,
rw [e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``, e_step_reln_def] >>
cases_on `e_step (env',s',e',c')` >>
fs [untyped_safety_exp_step] >|
[PairCases_on `p` >>
     fs [],
 qexists_tac `(s', Rerr Rtype_error)` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `(s', Rval v)` >>
     rw [small_eval_def] >>
     metis_tac [],
 qexists_tac `(s', Rerr (Rraise v))` >>
     rw [small_eval_def] >>
     metis_tac []]);

val untyped_safety_exp = Q.store_thm ("untyped_safety_exp",
`!s env e. (?r. small_eval env s e [] r) = ¬e_diverges env s e`,
metis_tac [small_exp_safety2, small_exp_safety1]);

val untyped_safety_dec = Q.store_thm ("untyped_safety_dec",
`!mn s env d. (∃r. evaluate_dec mn env s d r) = ~dec_diverges env s d`,
rw [Once evaluate_dec_cases, dec_diverges_def] >>
cases_on `d` >>
rw [] >|
[eq_tac >>
     rw [GSYM untyped_safety_exp] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >>
     fs [GSYM untyped_safety_exp] >>
     PairCases_on `r` >>
     fs [] >>
     cases_on `r1` >>
     fs [] >>
     cases_on `ALL_DISTINCT (pat_bindings p [])` >>
     fs [] >|
     [cases_on `pmatch (all_env_to_cenv env) r0 p a emp` >>
          fs [] >|
          [qexists_tac `(r0, Rerr (Rraise (Conv (SOME (Short "Bind", TypeExn)) [])))` >>
               rw [] >>
               metis_tac [small_big_exp_equiv, big_unclocked],
           qexists_tac `(r0, Rerr Rtype_error)` >>
               rw [] >>
               metis_tac [small_big_exp_equiv, big_unclocked],
           fs [merge_def, emp_def] >-
               metis_tac [small_big_exp_equiv, big_unclocked] >>
               `?r. evaluate_decs mn menv cenv r0 (l ++ env) ds r` by metis_tac [] >>
               PairCases_on `r` >>
               metis_tac [APPEND, small_big_exp_equiv, big_unclocked]],
      qexists_tac `(r0,Rerr e')` >>
          rw [] >>
          metis_tac [small_big_exp_equiv, big_unclocked]],
 metis_tac [],
 metis_tac [],
 metis_tac []]);

val untyped_safety_decs = Q.store_thm ("untyped_safety_decs",
`!mn s env ds. (?r. evaluate_decs mn env s ds r) = ~decs_diverges mn env s ds`,
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

val untyped_safety_top = Q.store_thm ("untyped_safety_top",
`!s env top. (?r. evaluate_top env s top r) = ~top_diverges env s top`,
rw [evaluate_top_cases, top_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
rw [] >>
metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]);

val untyped_safety_prog = Q.store_thm ("untyped_safety_prog",
`!s env tops. (?r. evaluate_prog env s tops r) = ~prog_diverges env s tops`,
induct_on `tops` >>
rw [] >-
rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
imp_res_tac top_determ >>
fs [] >>
rw [] >>
pop_assum mp_tac >>
rw [] >>
metis_tac [top_nchotomy, untyped_safety_top, pair_CASES, result_nchotomy]);

val _ = export_theory ();
