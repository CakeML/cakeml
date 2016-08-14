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
 cases_on `e` >>
 rw [] >|
 [cases_on `e'`,
  cases_on `c`] >>
 rw [] >>
 every_case_tac >>
 fs [application_def, oneTheory.one, push_def, return_def] >>
 every_case_tac);

val small_exp_safety1 = Q.prove (
`!s env e r.
  ¬(e_diverges env s e ∧ ?r. small_eval env s e [] r)`,
 rw [e_diverges_def, METIS_PROVE [] ``(~x ∨ ~y) = (y ⇒ ~x)``] >>
 cases_on `r` >>
 cases_on `r'` >>
 (TRY (Cases_on `e'`)) >>
 fs [small_eval_def, e_step_reln_def]
 >- (`∀s'' env'' e'' c''.
        e_step (env',q,Val a,[]) ≠ Estep (env'',s'',e'',c'')`
             by rw [e_step_def, continue_def] >>
     metis_tac [])
 >- (`∀s'' env''' e''' c''.
     e_step (env',q,Val a,[(Craise (),env'')]) ≠ Estep (env''',s'',e''',c'')`
          by rw [push_def, e_step_def, continue_def] >>
     metis_tac [])
 >- metis_tac [e_step_result_distinct]);

val small_exp_safety2 = Q.prove (
`!menv cenv s env e. e_diverges env s e ∨ ?r. small_eval env s e [] r`,
 rw [e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``, e_step_reln_def] >>
 cases_on `e_step (env',s',e',c')` >>
 fs [untyped_safety_exp_step]
 >- (PairCases_on `p` >>
     fs [])
 >- (qexists_tac `(s', Rerr (Rabort a))` >>
     rw [small_eval_def] >>
     metis_tac [])
 >- (qexists_tac `(s', Rval v)` >>
     rw [small_eval_def] >>
     metis_tac [])
 >- (qexists_tac `(s', Rerr (Rraise v))` >>
     rw [small_eval_def] >>
     metis_tac []));

val untyped_safety_exp = Q.store_thm ("untyped_safety_exp",
`!s env e. (?r. small_eval env s e [] r) = ¬e_diverges env s e`,
metis_tac [small_exp_safety2, small_exp_safety1]);

val to_small_st_surj = Q.prove(
  `∀s. ∃y. s = to_small_st y`,
  srw_tac[QUANT_INST_ss[record_default_qp,std_qp]][to_small_st_def]);

val untyped_safety_dec = Q.store_thm ("untyped_safety_dec",
  `!mn s env d. (∃r. evaluate_dec F mn env s d r) = ~dec_diverges env s d`,
  rw [] >>
  rw [Once evaluate_dec_cases, dec_diverges_def] >>
  cases_on `d` >>
  rw []
  >- (eq_tac >>
      rw [GSYM untyped_safety_exp] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >-
      metis_tac [to_small_st_def, small_big_exp_equiv, big_unclocked] >>
      `?s. (?err. r = (s,Rerr err)) ∨ (?v. r = (s,Rval v))` by metis_tac [pair_CASES, result_nchotomy] >>
      rw [] >>
      cases_on `ALL_DISTINCT (pat_bindings p [])` >>
      fs []
      >- (qexists_tac `(s with <| ffi := SND s'; refs := FST s' |>, Rerr err)` >>
          rw [] >>
          fs [GSYM small_big_exp_equiv, to_small_st_def])
      >- (cases_on `pmatch env.c (FST s') p v []` >>
          fs []
          >- (MAP_EVERY qexists_tac [`(s with <| ffi := SND s'; refs := FST s' |>, Rerr (Rraise Bindv))`] >>
              fs [GSYM small_big_exp_equiv, to_small_st_def] >>
              metis_tac [])
          >- (MAP_EVERY qexists_tac [`(s with <| ffi := SND s'; refs := FST s' |>, Rerr (Rabort Rtype_error))`] >>
              fs [GSYM small_big_exp_equiv, to_small_st_def] >>
              metis_tac [])
          >- (fs [] >>
              rw [GSYM small_big_exp_equiv, to_small_st_def] >>
              qexists_tac `(s with <| refs := FST s'; ffi := SND s' |>, Rval <|v := alist_to_env a; c := eEmpty|>)` >>
              rw [] >>
              metis_tac [])))
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []);

val untyped_safety_decs = Q.store_thm ("untyped_safety_decs",
`!mn s env ds. (?r. evaluate_decs F mn env s ds r) = ~decs_diverges mn env s ds`,
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
     >- metis_tac [untyped_safety_dec]
     >- metis_tac [dec_unclocked, result_distinct, dec_determ, PAIR_EQ, pair_CASES])
 >- (rw [] >>
     imp_res_tac (GSYM untyped_safety_dec) >>
     pop_assum (qspecl_then [`mn`] strip_assume_tac) >>
     `?s. (?err. r = (s,Rerr err)) ∨ (?env'. r = (s,Rval env'))` by metis_tac [pair_CASES, result_nchotomy] >>
     rw []
     >- metis_tac []
     >- metis_tac [PAIR_EQ, result_11, pair_CASES, dec_determ, dec_unclocked]));

val untyped_safety_top = Q.store_thm ("untyped_safety_top",
`!s env top. (?r. evaluate_top F env s top r) = ~top_diverges env s top`,
rw [evaluate_top_cases, top_diverges_cases] >>
eq_tac >>
rw [] >>
rw [] >>
CCONTR_TAC >>
fs [] >>
rw [] >>
metis_tac [top_nchotomy, untyped_safety_decs, untyped_safety_dec, pair_CASES, result_nchotomy]);

val untyped_safety_prog = Q.store_thm ("untyped_safety_prog",
`!s env tops. (?r. evaluate_prog F env s tops r) = ~prog_diverges env s tops`,
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
     rw [] >>
     metis_tac [untyped_safety_top])
 >- (rw [] >>
     imp_res_tac (GSYM untyped_safety_top) >>
     `?s. (?err. r = (s,Rerr err)) ∨ (?env'. r = (s,Rval env'))` by metis_tac [pair_CASES, result_nchotomy] >>
     rw []
     >- metis_tac []
     >- metis_tac [PAIR_EQ, result_11, pair_CASES, top_determ, top_unclocked]));

val _ = export_theory ();
