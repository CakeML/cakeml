open preamble MiniMLTheory MiniMLTerminationTheory;
open typeSoundTheory bigSmallEquivTheory determTheory untypedSafetyTheory;

val _ = new_theory "bigBigEquiv"

val pmatch_pmatch' = Q.prove (
`(!envc p v env. (pmatch envc p v env ≠ Match_type_error) ⇒
   (pmatch envc p v env = pmatch' p v env)) ∧
 (!envc ps vs env. (pmatch_list envc ps vs env ≠ Match_type_error) ⇒
   (pmatch_list envc ps vs env = pmatch_list' ps vs env))`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [pmatch_def, pmatch'_def] >|
[Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup n envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     Cases_on `lookup n' envc` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `pmatch envc p v env` >>
     fs [] >>
     Cases_on `pmatch' p v env` >>
     fs []]);

val evaluate_to_evaluate' = Q.prove (
`(!envc env e r. evaluate envc env e r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate' env e r) ∧
 (!envc env es r. evaluate_list envc env es r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate_list' env es r) ∧
 (!envc env v p r. evaluate_match envc env v p r ⇒
   (r ≠ Rerr Rtype_error) ⇒ evaluate_match' env v p r)`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate'_cases] >>
fs [] >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val evaluate'_to_evaluate = Q.prove (
`(!env e r. evaluate' env e r ⇒
   !envc. ¬evaluate envc env e (Rerr Rtype_error) ⇒ evaluate envc env e r) ∧
 (!env es r. evaluate_list' env es r ⇒
   !envc. ¬evaluate_list envc env es (Rerr Rtype_error) ⇒
   evaluate_list envc env es r) ∧
 (!env v p r. evaluate_match' env v p r ⇒
   !envc. ¬evaluate_match envc env v p (Rerr Rtype_error) ⇒
   evaluate_match envc env v p r)`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val type_no_error = Q.prove (
`!tenvC tenv e t envC env r.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_e tenvC tenv e t
  ⇒
  ¬evaluate envC env e (Rerr Rtype_error)`,
rw [GSYM small_big_exp_equiv] >>
metis_tac [untyped_safety_exp, small_exp_determ, exp_type_soundness]);

val evaluate_evaluate'_thm = Q.store_thm ("evaluate_evaluate'_thm",
`!tenvC envC tenv e t cenv env r.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_e tenvC tenv e t
  ⇒
  (evaluate' env e r = evaluate envC env e r)`,
metis_tac [type_no_error, evaluate'_to_evaluate, evaluate_to_evaluate']);


val evaluate_decs_to_evaluate_decs' = Q.prove (
`!cenv env ds r.
  evaluate_decs cenv env ds r ⇒
  (r ≠ Rerr Rtype_error) ⇒
  evaluate_decs' cenv env ds r`,
ho_match_mp_tac evaluate_decs_ind >>
rw [] >>
fs [] >>
rw [Once evaluate_decs'_cases] >>
metis_tac [result_distinct, evaluate_to_evaluate', result_11]);

val evaluate_decs'_to_evaluate_decs = Q.prove (
`!cenv env ds r.
  evaluate_decs' cenv env ds r ⇒
  ¬evaluate_decs cenv env ds (Rerr Rtype_error) ⇒
  evaluate_decs cenv env ds r`,
ho_match_mp_tac evaluate_decs'_ind >>
rw [] >>
fs [] >>
rw [Once evaluate_decs_cases] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_decs_cases]) >>
fs [] >>
metis_tac [evaluate'_to_evaluate]);

val type_no_error_dec = Q.prove (
`!tenvC tenv ds t envC env r tenvC' tenvE'.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_ds tenvC tenv ds tenvC' tenvE'
  ⇒
  ¬evaluate_decs envC env ds (Rerr Rtype_error)`,
rw [GSYM small_big_equiv] >>
metis_tac [untyped_safety, small_determ, type_soundness]);

val evaluate_dec_evaluate_dec'_thm = Q.store_thm ("evaluate_dec_evaluate_dec'_thm",
`!tenvC envC tenv ds t cenv env r tenvC' tenvE'.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC env tenv ∧
  type_ds tenvC tenv ds tenvC' tenvE'
  ⇒
  (evaluate_decs' envC env ds r = evaluate_decs envC env ds r)`,
metis_tac [type_no_error_dec, evaluate_decs'_to_evaluate_decs,
           evaluate_decs_to_evaluate_decs']);

val _ = export_theory ()
