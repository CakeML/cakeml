open preamble MiniMLTheory MiniMLTerminationTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSoundTheory;

val _ = new_theory "bigBigEquiv"

val pmatch_pmatch' = Q.prove (
`(!tvs (cenv : envC)  (s:'a store) p v env. (pmatch tvs cenv s p v env ≠ Match_type_error) ⇒
   (pmatch tvs cenv s p v env = pmatch' tvs s p v env)) ∧
 (!tvs (cenv : envC) (s:'a store) ps vs env. (pmatch_list tvs cenv s ps vs env ≠ Match_type_error) ⇒
   (pmatch_list tvs cenv s ps vs env = pmatch_list' tvs s ps vs env))`,
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

val evaluate'_to_evaluate = Q.prove (
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

val evaluate'_to_evaluate_thm = Q.store_thm ("evaluate'_to_evaluate_thm",
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs r.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_e tenvM tenvC tenv e t ⇒
  (evaluate' st env e r ⇒ evaluate menv cenv st env e r)`,
metis_tac [type_no_error, evaluate'_to_evaluate]);

(* TODO: establish dec', decs', and prog' imply dec, decs and prog *)

val _ = export_theory ()
