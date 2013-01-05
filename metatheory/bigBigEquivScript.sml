open preamble MiniMLTheory MiniMLTerminationTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSoundTheory;

val _ = new_theory "bigBigEquiv"

val pmatch_pmatch' = Q.prove (
`(!tvs envc s p v env. (pmatch tvs envc s p v env ≠ Match_type_error) ⇒
   (pmatch tvs envc s p v env = pmatch' tvs s p v env)) ∧
 (!tvs envc s ps vs env. (pmatch_list tvs envc s ps vs env ≠ Match_type_error) ⇒
   (pmatch_list tvs envc s ps vs env = pmatch_list' tvs s ps vs env))`,
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
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs []]);

val evaluate_to_evaluate' = Q.prove (
`(!envc s env e r. evaluate envc s env e r ⇒
   (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate' s env e r) ∧
 (!envc s env es r. evaluate_list envc s env es r ⇒
   (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate_list' s env es r) ∧
 (!envc s env v p r. evaluate_match envc s env v p r ⇒
   (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate_match' s env v p r)`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate'_cases] >>
fs [] >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val evaluate'_to_evaluate = Q.prove (
`(!s env e r. evaluate' s env e r ⇒
   !envc. (!s'. ¬evaluate envc s env e (s', Rerr Rtype_error)) ⇒ evaluate envc s env e r) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !envc. (!s'. ¬evaluate_list envc s env es (s', Rerr Rtype_error)) ⇒
   evaluate_list envc s env es r) ∧
 (!s env v p r. evaluate_match' s env v p r ⇒
   !envc. (!s'. ¬evaluate_match envc s env v p (s', Rerr Rtype_error)) ⇒
   evaluate_match envc s env v p r)`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
metis_tac [pmatch_pmatch', match_result_distinct]);

val type_no_error = Q.prove (
`!tenvC senv tenv e t envC s env r.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC senv env tenv ∧
  type_s tenvC senv s ∧
  type_e tenvC tenv e t
  ⇒
  (!s'. ¬evaluate envC s env e (s', Rerr Rtype_error))`,
rw [GSYM small_big_exp_equiv] >>
metis_tac [untyped_safety_exp, small_exp_determ, exp_type_soundness, PAIR_EQ]);

val evaluate_evaluate'_thm = Q.store_thm ("evaluate_evaluate'_thm",
`!tenvC envC tenv e t cenv env r.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC senv env tenv ∧
  type_s tenvC senv s ∧
  type_e tenvC tenv e t
  ⇒
  (evaluate' s env e r = evaluate envC s env e r)`,
metis_tac [type_no_error, evaluate'_to_evaluate, evaluate_to_evaluate']);

val evaluate_decs_to_evaluate_decs' = Q.prove (
`!cenv s env ds r.
  evaluate_decs cenv s env ds r ⇒
  (!s'. r ≠ (s', Rerr Rtype_error)) ⇒
  evaluate_decs' cenv s env ds r`,
ho_match_mp_tac evaluate_decs_ind >>
rw [] >>
fs [] >>
rw [Once evaluate_decs'_cases] >>
imp_res_tac evaluate_to_evaluate' >>
fs [] >>
metis_tac []);

val evaluate_decs'_to_evaluate_decs = Q.prove (
`!cenv s env ds r.
  evaluate_decs' cenv s env ds r ⇒
  (!s'. ¬evaluate_decs cenv s env ds (s', Rerr Rtype_error)) ⇒
  evaluate_decs cenv s env ds r`,
ho_match_mp_tac evaluate_decs'_ind >>
rw [] >>
fs [] >>
rw [Once evaluate_decs_cases] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_decs_cases]) >>
fs [] >>
metis_tac [evaluate'_to_evaluate]);

val type_no_error_dec = Q.prove (
`!tenvC senv tenv ds t envC env r tenvC' tenvE'.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC senv env tenv ∧
  type_s tenvC senv s ∧
  type_ds tenvC tenv ds tenvC' tenvE'
  ⇒
  (!s'. ¬evaluate_decs envC s env ds (s', Rerr Rtype_error))`,
rw [GSYM small_big_equiv] >>
metis_tac [untyped_safety, small_determ, type_soundness, PAIR_EQ]);

val evaluate_dec_evaluate_dec'_thm = Q.store_thm ("evaluate_dec_evaluate_dec'_thm",
`!tenvC envC tenv ds t cenv env r tenvC' tenvE' s senv.
  tenvC_ok tenvC ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_env tenvC senv env tenv ∧
  type_s tenvC senv s ∧
  type_ds tenvC tenv ds tenvC' tenvE'
  ⇒
  (evaluate_decs' envC s env ds r = evaluate_decs envC s env ds r)`,
metis_tac [type_no_error_dec, evaluate_decs'_to_evaluate_decs,
           evaluate_decs_to_evaluate_decs']);

val _ = export_theory ()
