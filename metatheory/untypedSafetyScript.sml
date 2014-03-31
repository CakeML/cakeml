(* Prove that the small step semantics never gets stuck if there is still work
 * to do (i.e., it must detect all type errors).  Thus, it either diverges or
 * gives a result, and it can't do both. *)

open preamble;
open libTheory astTheory bigStepTheory smallStepTheory semanticPrimitivesTheory
open determTheory bigSmallEquivTheory
open terminationTheory bigClockTheory;

val _ = new_theory "untypedSafety";

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
    e_step (env',q,Val a,[(Craise (),env'')]) ≠ Estep (env''',s'',e''',c'')`
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
`!mn s tdecls env d count. (∃r. evaluate_dec F mn env ((count,s),tdecls) d r) = ~dec_diverges env (s,tdecls) d`,
 rw [] >>
 rw [Once evaluate_dec_cases, dec_diverges_def] >>
 cases_on `d` >>
 rw []
 >- (eq_tac >>
     rw [GSYM untyped_safety_exp] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >-
     metis_tac [pair_CASES, small_big_exp_equiv, big_unclocked] >-
     metis_tac [small_big_exp_equiv, big_unclocked] >>
     `?s. (?err. r = (s,Rerr err)) ∨ (?v. r = (s,Rval v))` by metis_tac [pair_CASES, result_nchotomy] >>
     rw [] >>
     cases_on `ALL_DISTINCT (pat_bindings p [])` >>
     fs []
     >- (qexists_tac `(((count',s'),tdecls),Rerr err)` >>
         rw [] >>
         metis_tac [small_big_exp_equiv])
     >- (cases_on `pmatch (all_env_to_cenv env) s' p v emp` >>
         fs []
         >- (MAP_EVERY qexists_tac [`(((count',s'),tdecls), Rerr (Rraise (Conv (SOME ("Bind", TypeExn (Short "Bind"))) [])))`] >>
             rw [] >>
             metis_tac [small_big_exp_equiv, big_unclocked])
         >- (MAP_EVERY qexists_tac [`(((count',s'),tdecls), Rerr Rtype_error)`] >>
             rw [] >>
             metis_tac [small_big_exp_equiv, big_unclocked])
         >- (fs [merge_def, emp_def] >-
             metis_tac [small_big_exp_equiv, big_unclocked])))
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []);

val untyped_safety_decs = Q.store_thm ("untyped_safety_decs",
`!mn s tdecls env ds count. (?r. evaluate_decs F mn env ((count,s),tdecls) ds r) = ~decs_diverges mn env (s,tdecls) ds`,
 induct_on `ds` >>
 rw [] >-
 rw [Once evaluate_decs_cases, Once decs_diverges_cases] >>
 rw [Once evaluate_decs_cases, Once decs_diverges_cases] >>
 eq_tac
 >- (rw [] >>
     rw [] >>
     CCONTR_TAC >> 
     fs [] >>
     imp_res_tac dec_determ >>
     fs [] >>
     rw [] >>
     pop_assum mp_tac >>
     rw []
     >- metis_tac [untyped_safety_dec]
     >- metis_tac [dec_unclocked, result_distinct, dec_determ, PAIR_EQ, pair_CASES]
     >- metis_tac [untyped_safety_dec]
     >- metis_tac [PAIR_EQ, result_11, pair_CASES, dec_determ, dec_unclocked])
 >- (rw [] >>
     imp_res_tac (GSYM untyped_safety_dec) >>
     pop_assum (qspecl_then [`mn`, `count'`] strip_assume_tac) >>
     `?s. (?err. r = (s,Rerr err)) ∨ (?cenv env'. r = (s,Rval (cenv,env')))` by metis_tac [pair_CASES, result_nchotomy] >>
     rw []
     >- metis_tac []
     >- metis_tac [PAIR_EQ, result_11, pair_CASES, dec_determ, dec_unclocked]));

val untyped_safety_top = Q.store_thm ("untyped_safety_top",
`!s env top count tdecls mods. (?r. evaluate_top F env ((count,s),tdecls,mods) top r) = ~top_diverges env (s,tdecls,mods) top`,
rw [evaluate_top_cases, top_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >> 
fs [] >>
rw []
>- metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]
>- metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]
>- metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]
>- metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy] >>
cases_on `top` >>
fs [] >>
metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]);

val untyped_safety_prog = Q.store_thm ("untyped_safety_prog",
`!s env tops count tdecls mods. (?r. evaluate_prog F env ((count,s),tdecls,mods) tops r) = ~prog_diverges env (s,tdecls,mods) tops`,
 induct_on `tops` >>
 rw [] >-
 rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
 rw [Once evaluate_prog_cases, Once prog_diverges_cases] >>
 eq_tac
 >- (rw [] >>
     rw [] >>
     CCONTR_TAC >> 
     fs [] >>
     imp_res_tac top_determ >>
     fs [] >>
     rw [] >>
     pop_assum mp_tac >>
     rw []
     >- metis_tac [untyped_safety_top]
     >- metis_tac [top_unclocked, result_distinct, top_determ, PAIR_EQ, pair_CASES, result_11]
     >- metis_tac [untyped_safety_top]
     >- metis_tac [PAIR_EQ, result_distinct, result_11, pair_CASES, top_determ, top_unclocked])
 >- (rw [] >>
     imp_res_tac (GSYM untyped_safety_top) >>
     pop_assum (qspecl_then [`count'`] strip_assume_tac) >>
     `?s cenv. (?err. r = (s,cenv,Rerr err)) ∨ (?menv env'. r = (s,cenv,Rval (menv,env')))` by metis_tac [pair_CASES, result_nchotomy] >>
     rw []
     >- metis_tac []
     >- metis_tac [PAIR_EQ, result_11, pair_CASES, top_determ, top_unclocked]));

val _ = export_theory ();
