open preamble MiniMLTheory MiniMLTerminationTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSoundTheory;

val _ = new_theory "bigBigEquiv"

val no_mod_vars_def = tDefine "no_mod_vars" `
(no_mod_vars (Raise _) = T) ∧
(no_mod_vars (Handle e1 _ e2) = no_mod_vars e1 ∧ no_mod_vars e2) ∧
(no_mod_vars (Lit _) = T) ∧
(no_mod_vars (Con cn es) = EVERY no_mod_vars es) ∧
(no_mod_vars (Var (Short _) _) = T) ∧
(no_mod_vars (Var (Long _ _) _) = F) ∧
(no_mod_vars (Fun _ _ e) = no_mod_vars e) ∧
(no_mod_vars (Uapp _ e) = no_mod_vars e) ∧
(no_mod_vars (App _ e1 e2) = no_mod_vars e1 ∧ no_mod_vars e2) ∧
(no_mod_vars (Log _ e1 e2) = no_mod_vars e1 ∧ no_mod_vars e2) ∧
(no_mod_vars (If e1 e2 e3) = no_mod_vars e1 ∧ no_mod_vars e2 ∧ no_mod_vars e3) ∧
(no_mod_vars (Mat e pes) = no_mod_vars e ∧ EVERY no_mod_vars (MAP SND pes)) ∧
(no_mod_vars (Let _ _ _ e1 e2) = no_mod_vars e1 ∧ no_mod_vars e2) ∧
(no_mod_vars (Letrec _ funs e) = EVERY (\(a,b,c,d,e). no_mod_vars e) funs)`
(WF_REL_TAC `measure (exp_size (\x.0))` >>
rw [] >>
TRY (induct_on `pes`) >>
TRY (induct_on `funs`) >>
TRY (induct_on `es`) >>
rw [] >>
fs [] >>
res_tac >>
TRY (PairCases_on `h`) >>
fs [exp_size_def] >>
decide_tac);

val v_no_mod_vars_def = tDefine "v_no_mod_vars" `
(v_no_mod_vars (Litv _) = T) ∧
(v_no_mod_vars (Conv _ vs) = EVERY v_no_mod_vars vs) ∧
(v_no_mod_vars (Closure env _ _ e) = EVERY (\(a,b,c). v_no_mod_vars b) env ∧ no_mod_vars e) ∧
(v_no_mod_vars (Recclosure env funs _) = 
  EVERY (\(a,b,c). v_no_mod_vars b) env ∧ EVERY (\(a,b,c,d,e). no_mod_vars e) funs) ∧
(v_no_mod_vars (Loc _) = T)`
(WF_REL_TAC `measure (v_size (\x.0))` >>
 rw [] >>
 TRY (induct_on `env`) >>
 TRY (induct_on `vs`) >>
 rw [] >>
 fs [v_size_def] >>
 decide_tac);

val pmatch_pmatch' = Q.prove (
`(!tvs (menv : 'a envM) cenv (s:'a store) p v env. (pmatch tvs menv cenv s p v env ≠ Match_type_error) ⇒
   (pmatch tvs menv cenv s p v env = pmatch' tvs s p v env)) ∧
 (!tvs (menv : 'a envM) cenv (s:'a store) ps vs env. (pmatch_list tvs menv cenv s ps vs env ≠ Match_type_error) ⇒
   (pmatch_list tvs menv cenv s ps vs env = pmatch_list' tvs s ps vs env))`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [pmatch_def, pmatch'_def] >|
[Cases_on `lookup_con_id n menv cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup_con_id n menv cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 Cases_on `lookup_con_id n menv cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     Cases_on `lookup_con_id n' menv cenv` >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     rw [] >>
     metis_tac [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs []]);

(*
val evaluate_to_evaluate' = Q.prove (
`(!(menv : t envM) cenv s env e r. evaluate menv cenv s env e r ⇒
   EVERY (\(a,b,c). v_no_mod_vars b) env ∧ no_mod_vars e ∧ (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate' s env e r) ∧
 (!(menv : t envM) cenv s env es r. evaluate_list menv cenv s env es r ⇒
   EVERY (\(a,b,c). v_no_mod_vars b) env ∧ EVERY no_mod_vars es ∧ (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate_list' s env es r) ∧
 (!(menv : t envM) cenv s env v p r. evaluate_match menv cenv s env v p r ⇒
   EVERY (\(a,b,c). v_no_mod_vars b) env ∧ v_no_mod_vars v ∧ (!s'. r ≠ (s', Rerr Rtype_error)) ⇒ evaluate_match' s env v p r)`,
ho_match_mp_tac evaluate_ind >>
rw [no_mod_vars_def] >>
SIMP_TAC (srw_ss()) [Once evaluate'_cases] >>
fs [] >>
e(metis_tac [pmatch_pmatch', match_result_distinct]);

val evaluate'_to_evaluate = Q.prove (
`(!s env e r. evaluate' s env e r ⇒
   !menv cenv. (!s'. ¬evaluate menv cenv s env e (s', Rerr Rtype_error)) ⇒
   evaluate menv cenv s env e r) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv cenv. (!s'. ¬evaluate_list menv cenv s env es (s', Rerr Rtype_error)) ⇒
   evaluate_list menv cenv s env es r) ∧
 (!s env v p r. evaluate_match' s env v p r ⇒
   !menv cenv. (!s'. ¬evaluate_match menv cenv s env v p (s', Rerr Rtype_error)) ⇒
   evaluate_match menv cenv s env v p r)`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
e(metis_tac [pmatch_pmatch', match_result_distinct]);

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
           *)
val _ = export_theory ()
