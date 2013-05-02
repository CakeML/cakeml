open preamble
open SemanticPrimitivesTheory AltBigStepTheory BigStepTheory TypeSystemTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSoundTheory;
open terminationTheory;

val _ = new_theory "bigBigEquiv"

val pmatch_pmatch' = Q.prove (
`(!(cenv : envC)  (s:store) p v env. (pmatch cenv s p v env ≠ Match_type_error) ⇒
   (pmatch cenv s p v env = pmatch' s p v env)) ∧
 (!(cenv : envC) (s:store) ps vs env. (pmatch_list cenv s ps vs env ≠ Match_type_error) ⇒
   (pmatch_list cenv s ps vs env = pmatch_list' s ps vs env))`,
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, pmatch'_def] >|
[Cases_on `lookup n cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     Cases_on `lookup n' cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs []]);

val eval'_to_eval = Q.prove (
`(!s env e r. evaluate' s env e r ⇒
   !menv (cenv : envC). (!s'. ¬evaluate menv cenv s env e (s', Rerr Rtype_error)) ⇒
   evaluate menv cenv s env e r) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv (cenv : envC). (!s'. ¬evaluate_list menv cenv s env es (s', Rerr Rtype_error)) ⇒
   evaluate_list menv cenv s env es r) ∧
 (!s env v p r. evaluate_match' s env v p r ⇒
   !menv (cenv : envC). (!s'. ¬evaluate_match menv cenv s env v p (s', Rerr Rtype_error)) ⇒
   evaluate_match menv cenv s env v p r)`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
fs [lookup_var_id_def] >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val type_no_error = Q.prove (
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_e tenvM tenvC tenv e t ⇒
  (!st'. ¬evaluate menv cenv st env e (st', Rerr Rtype_error))`,
rw [GSYM small_big_exp_equiv] >>
metis_tac [bind_tvar_def, untyped_safety_exp, small_exp_determ, exp_type_soundness, PAIR_EQ]);

val eval'_to_eval_thm = Q.store_thm ("eval'_to_eval_thm",
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs r.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_e tenvM tenvC tenv e t ⇒
  (evaluate' st env e r ⇒ evaluate menv cenv st env e r)`,
metis_tac [type_no_error, eval'_to_eval]);

val eval_dec'_to_eval_dec = Q.prove (
`!mn menv (cenv : envC) st env d r.
  evaluate_dec' mn menv cenv st env d r ⇒
  (!st'. ¬evaluate_dec mn menv cenv st env d (st', Rerr Rtype_error)) ⇒
  evaluate_dec mn menv cenv st env d r`,
rw [evaluate_dec_cases, evaluate_dec'_cases] >>
metis_tac [eval'_to_eval, pmatch_pmatch', match_result_distinct,
           result_distinct, match_result_11, result_11])

val eval_dec'_to_eval_dec_thm = Q.store_thm ("eval_dec'_to_eval_dec_thm",
`!mn menv (cenv : envC) st env d r tenvM tenvC tenvS tenv tenvC' tenv'.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  evaluate_dec' mn menv cenv st env d r ⇒
  evaluate_dec mn menv cenv st env d r`,
metis_tac [eval_dec'_to_eval_dec, dec_type_soundness, untyped_safety_dec, dec_determ, PAIR_EQ]);

val eval_decs'_to_eval_decs = Q.prove (
`!mn menv (cenv : envC) st env ds r.
  evaluate_decs' mn menv cenv st env ds r ⇒
  (!st'. ¬evaluate_decs mn menv cenv st env ds (st', Rerr Rtype_error)) ⇒
  evaluate_decs mn menv cenv st env ds r`,
ho_match_mp_tac evaluate_decs'_ind >>
rw [] >>
rw [Once evaluate_decs_cases] >>
pop_assum (MP_TAC o SIMP_RULE (srw_ss()) [Once evaluate_decs_cases]) >>
rw [combine_dec_result_def] >>
metis_tac [eval_dec'_to_eval_dec, result_case_def, result_nchotomy,
           result_distinct, result_11, pair_case_def, PAIR_EQ, pair_CASES]);

val eval_decs'_to_eval_decs_thm = Q.store_thm ("eval_decs'_to_eval_decs_thm",
`!mn menv (cenv : envC) st env ds r tenvM tenvC tenvS tenv tenvC' tenv'.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ∧
  evaluate_decs' mn menv cenv st env ds r ⇒
  evaluate_decs mn menv cenv st env ds r`,
metis_tac [eval_decs'_to_eval_decs, decs_type_soundness, untyped_safety_decs, decs_determ, PAIR_EQ]);

val eval_prog'_to_eval_prog = Q.prove (
`!menv (cenv : envC) st env prog r.
  evaluate_prog' menv cenv st env prog r ⇒
  (!st'. ¬evaluate_prog menv cenv st env prog (st', Rerr Rtype_error)) ⇒
  evaluate_prog menv cenv st env prog r`,
ho_match_mp_tac evaluate_prog'_ind >>
rw [] >>
rw [Once evaluate_prog_cases] >>
pop_assum (MP_TAC o SIMP_RULE (srw_ss()) [Once evaluate_prog_cases]) >>
rw [combine_mod_result_def] >>
metis_tac [eval_dec'_to_eval_dec, eval_decs'_to_eval_decs, result_case_def, result_nchotomy,
           result_distinct, result_11, pair_case_def, PAIR_EQ, pair_CASES]);

val eval_prog'_to_eval_prog_thm = Q.store_thm ("eval_prog'_to_eval_prog_thm",
`!menv (cenv : envC) st env prog r tenvM tenvC tenvS tenv tenvM' tenvC' tenv'.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  (num_tvs tenv = 0) ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_prog tenvM tenvC tenv prog tenvM' tenvC' tenv' ∧
  evaluate_prog' menv cenv st env prog r ⇒
  evaluate_prog menv cenv st env prog r`,
metis_tac [eval_prog'_to_eval_prog, prog_type_soundness, untyped_safety_prog, prog_determ, PAIR_EQ]);

val _ = export_theory ();
