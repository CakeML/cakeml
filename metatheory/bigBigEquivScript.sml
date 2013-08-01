open preamble
open SemanticPrimitivesTheory AltBigStepTheory BigStepTheory TypeSystemTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSysPropsTheory typeSoundTheory;
open terminationTheory bigClockTheory;

val _ = new_theory "bigBigEquiv"

val big_exp_determ' = Q.store_thm ("big_exp_determ'",
`(∀s env e r1.
   evaluate' s env e r1 ⇒
   ∀r2. evaluate' s env e r2 ⇒
   (r1 = r2)) ∧
 (∀s env es r1.
   evaluate_list' s env es r1 ⇒
   ∀r2. evaluate_list' s env es r2 ⇒
   (r1 = r2)) ∧
 (∀s env v pes err_v r1.
   evaluate_match' s env v pes err_v r1 ⇒
   ∀r2. evaluate_match' s env v pes err_v r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate'_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate'_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
res_tac >>
fs [] >>
rw [] >> 
metis_tac []);

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
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate F menv cenv (count,s) env e ((count,s'), Rerr Rtype_error)) ⇒
     evaluate F menv cenv (count,s) env e ((count,s1),r1)) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate_list F menv cenv (count,s) env es ((count,s'), Rerr Rtype_error)) ⇒
     evaluate_list F menv cenv (count,s) env es ((count,s1),r1)) ∧
 (!s env v p err_v r. evaluate_match' s env v p err_v r ⇒
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate_match F menv cenv (count,s) env v p err_v ((count,s'), Rerr Rtype_error)) ⇒
     evaluate_match F menv cenv (count,s) env v p err_v ((count,s1),r1))`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
TRY (qpat_assum `!s. ~evaluate F a0 b0 c0 d0 e0 f0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
TRY (qpat_assum `!s. ~evaluate_match F a0 b0 c0 d0 e0 f0 g0 h0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
TRY (qpat_assum `!s. ~evaluate_list F a0 b0 c0 d0 e0 f0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
fs [lookup_var_id_def] >>
metis_tac [pmatch_pmatch', match_result_distinct, big_unclocked]);

val type_no_error = Q.prove (
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_e tenvM tenvC tenv e t ⇒
  (!st' count. ¬evaluate F menv cenv (count,st) env e (st', Rerr Rtype_error))`,
rw [] >>
cases_on `st'` >>
metis_tac [exp_type_soundness, bind_tvar_def, big_unclocked,small_big_exp_equiv, untyped_safety_exp, small_exp_determ, PAIR_EQ]);

val eval'_to_eval_thm = Q.store_thm ("eval'_to_eval_thm",
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs s' r' count.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_e tenvM tenvC tenv e t ⇒
  (evaluate' st env e (s',r') ⇒ evaluate F menv cenv (count,st) env e ((count, s'), r'))`,
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
  tenvC_has_exns tenvC ∧
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
  (!st' cenv'. ¬evaluate_decs mn menv cenv st env ds (st', cenv', Rerr Rtype_error)) ⇒
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
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ∧
  evaluate_decs' mn menv cenv st env ds r ⇒
  evaluate_decs mn menv cenv st env ds r`,
rw [] >>
imp_res_tac eval_decs'_to_eval_decs >>
pop_assum match_mp_tac >>
rw [] >>
metis_tac [decs_type_soundness, untyped_safety_decs, decs_determ, PAIR_EQ]);

val eval_top'_to_eval_top = Q.prove (
`!menv (cenv : envC) st env top r.
  evaluate_top' menv cenv st env top r ⇒
  (!cenv' st'. ¬evaluate_top menv cenv st env top (st', cenv', Rerr Rtype_error)) ⇒
  evaluate_top menv cenv st env top r`,
rw [evaluate_top_cases, evaluate_top'_cases] >>
metis_tac [eval_dec'_to_eval_dec, eval_decs'_to_eval_decs, result_case_def, result_nchotomy,
           result_distinct, result_11, pair_case_def, PAIR_EQ, pair_CASES]);

           (*
val eval_top'_to_eval_top_thm = Q.store_thm ("eval_top'_to_eval_top_thm",
`!menv (cenv : envC) st env top r tenvM tenvC tenvS tenv tenvM' tenvC' tenv'.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
  (num_tvs tenv = 0) ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvM tenvC tenvS env tenv ∧ 
  type_s tenvM tenvC tenvS st ∧
  type_top tenvM tenvC tenv top tenvM' tenvC' tenv' ∧
  evaluate_top' menv cenv st env top r ⇒
  evaluate_top menv cenv st env top r`,
metis_tac [eval_top'_to_eval_top, top_type_soundness, untyped_safety_top, top_determ, PAIR_EQ]);
*)

val eval_prog'_to_eval_prog = Q.prove (
`!menv (cenv : envC) st env prog r.
  evaluate_prog' menv cenv st env prog r ⇒
  (!cenv' st'. ¬evaluate_prog menv cenv st env prog (st', cenv', Rerr Rtype_error)) ⇒
  evaluate_prog menv cenv st env prog r`,
ho_match_mp_tac evaluate_prog'_ind >>
rw [] >>
rw [Once evaluate_prog_cases] >>
pop_assum (MP_TAC o SIMP_RULE (srw_ss()) [Once evaluate_prog_cases]) >>
rw [combine_mod_result_def] >>
metis_tac [eval_top'_to_eval_top, result_case_def, result_nchotomy,
           result_distinct, result_11, pair_case_def, PAIR_EQ, pair_CASES]);

(*
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
*)

val var_pat_def = Define `
(var_pat (Pvar x) = T) ∧
(var_pat _ = F)`;

val check_ctors_p_def = Define `
(check_ctors_p (cenv:envC) NONE (Pvar x) = T) ∧
(check_ctors_p cenv NONE (Plit l) = T) ∧
(check_ctors_p cenv (SOME t) (Pcon (SOME cn) ps) =
  case lookup cn cenv of
     | NONE => F
     | SOME (len, tn) =>
         (t = tn) ∧
         (len = LENGTH ps) ∧
         EVERY var_pat ps) ∧
(check_ctors_p cenv NONE (Pref p) = var_pat p) ∧
(check_ctors_p cenv _ _ = F)`;

val get_pat_type_def = Define `
(get_pat_type (cenv:envC) (Pvar x) = NONE) ∧
(get_pat_type cenv (Plit x) = NONE) ∧
(get_pat_type cenv (Pref x) = NONE) ∧
(get_pat_type cenv (Pcon (SOME cn) ps) = 
  case lookup cn cenv of
     | NONE => NONE
     | SOME (len, tn) => SOME tn) ∧
(get_pat_type cenv (Pcon NONE ps) =
  NONE)`;

val get_pat_type_thm = Q.prove (
`!cenv p1 p2.
  check_ctors_p cenv (get_pat_type cenv p1) p2
  ⇒
  (get_pat_type cenv p1 = get_pat_type cenv p2)`,
cases_on `p1` >>
rw [get_pat_type_def, check_ctors_p_def] >>
cases_on `p2` >>
fs [get_pat_type_def, check_ctors_p_def] >>
cases_on `o'` >>
fs [get_pat_type_def, check_ctors_p_def] >>
cases_on `lookup x cenv` >>
fs [] >>
TRY (PairCases_on `x'`) >>
fs [check_ctors_p_def] >>
cases_on `o''` >>
fs [get_pat_type_def, check_ctors_p_def] >>
cases_on `lookup x' cenv` >>
fs [] >>
PairCases_on `x''` >>
fs []);

val check_ctors_def = tDefine "check_ctors" `
(check_ctors (cenv:envC) (Raise e) = check_ctors cenv e) ∧
(check_ctors cenv (Handle e1 pes) = 
  (check_ctors cenv e1 ∧
   EVERY (\(p,e). check_ctors_p cenv (SOME TypeExn) p ∧ check_ctors cenv e) pes)) ∧
(check_ctors cenv (Lit l) = T) ∧
(check_ctors cenv (Con (SOME cn) es) = 
  (do_con_check cenv (SOME cn) (LENGTH es) ∧
   EVERY (check_ctors cenv) es)) ∧
(check_ctors cenv (Con NONE es) = F) ∧
(check_ctors cenv (Var id) = T) ∧
(check_ctors cenv (Fun x e) = 
  check_ctors cenv e) ∧
(check_ctors cenv (Uapp uop e) = 
  check_ctors cenv e) ∧
(check_ctors cenv (App op e1 e2) = 
  (check_ctors cenv e1 ∧ check_ctors cenv e2)) ∧
(check_ctors cenv (Log lop e1 e2) = 
  (check_ctors cenv e1 ∧ check_ctors cenv e2)) ∧
(check_ctors cenv (If e1 e2 e3) =
  (check_ctors cenv e1 ∧ check_ctors cenv e2 ∧ check_ctors cenv e3)) ∧
(check_ctors cenv (Mat e []) = F) ∧
(check_ctors cenv (Mat e ((p,e')::pes)) = 
  let t = get_pat_type cenv p in
    check_ctors cenv e ∧
    check_ctors_p cenv t p ∧
    check_ctors cenv e' ∧
    EVERY (\(p,e). check_ctors_p cenv t p ∧ check_ctors cenv e) pes) ∧
(check_ctors cenv (Let x e1 e2) =
  (check_ctors cenv e1 ∧ check_ctors cenv e2)) ∧
(check_ctors cenv (Letrec funs e) = 
  (EVERY (\(f,x,e). check_ctors cenv e) funs ∧ check_ctors cenv e))`
(wf_rel_tac `measure (exp_size o SND)` >>
srw_tac [ARITH_ss] [] >|
[induct_on `pes`,
 induct_on `funs`,
 induct_on `pes`,
 induct_on `es`] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
res_tac >>
decide_tac);

val check_ctors_v_def = tDefine "check_ctors_v" `
(check_ctors_v cenv (Litv l) = T) ∧
(check_ctors_v cenv (Conv (SOME cn) vs) =
  (do_con_check cenv (SOME cn) (LENGTH vs) ∧
   EVERY (check_ctors_v cenv) vs)) ∧
(check_ctors_v cenv (Conv NONE vs) = F) ∧
(check_ctors_v cenv (Closure env x e) =
  (EVERY (\(x,v). check_ctors_v cenv v) env ∧
   check_ctors cenv e)) ∧
(check_ctors_v cenv (Recclosure env funs x) =
  (EVERY (\(x,v). check_ctors_v cenv v) env ∧
   EVERY (\(f,x,e). check_ctors cenv e) funs)) ∧
(check_ctors_v cenv (Loc l) = T)`
(wf_rel_tac `measure (v_size o SND)` >>
srw_tac [ARITH_ss] [] >|
[induct_on `env`,
 induct_on `vs`,
 induct_on `env`] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def, v_size_def] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def, v_size_def] >>
res_tac >>
decide_tac);

val check_var_pat = Q.prove (
`(!p. var_pat p ⇒ check_ctors_p cenv NONE p) ∧
 (!ps. EVERY var_pat ps ⇒ EVERY (check_ctors_p cenv NONE) ps)`,
Induct >>
rw [var_pat_def, check_ctors_p_def] >>
metis_tac []);

val eval_ctor_inv_def = Define `
eval_ctor_inv cenv s env =
  (EVERY (check_ctors_v cenv) s ∧
   EVERY (\(x,v). check_ctors_v cenv v) env)`;

val eval_ctor_inv_bind_env = Q.prove (
`!cenv s x v env.
  eval_ctor_inv cenv s (bind x v env) =
  (check_ctors_v cenv v ∧ eval_ctor_inv cenv s env)`,
rw [eval_ctor_inv_def, LibTheory.bind_def, eval_ctor_inv_def] >>
metis_tac []);

val eval_ctor_inv_lookup = Q.prove (
`!cenv s env n v.
  eval_ctor_inv cenv s env ∧
  (lookup n env = SOME v) ⇒
  check_ctors_v cenv v`,
rw [eval_ctor_inv_def, LibTheory.bind_def, eval_ctor_inv_def] >>
imp_res_tac lookup_in >>
fs [GSYM PEXISTS_THM, GSYM PFORALL_THM, LAMBDA_PROD, MEM_MAP, EVERY_MEM] >>
rw [] >>
metis_tac []);

val eval_ctor_inv_do_uapp = Q.prove (
`!s1 uop v1 s2 v2.
  (do_uapp s1 uop v1 = SOME (s2, v2)) ∧
  eval_ctor_inv cenv s1 env ∧
  check_ctors_v cenv v1
  ⇒
  check_ctors_v cenv v2 ∧
  eval_ctor_inv cenv s2 env`,
rw [do_uapp_def, eval_ctor_inv_def, check_ctors_v_def] >>
cases_on `uop` >>
cases_on `v1` >>
fs [check_ctors_v_def, LET_THM, store_alloc_def] >>
rw [check_ctors_v_def] >>
cases_on `store_lookup n s1` >>
fs [store_lookup_def, EVERY_MEM, LAMBDA_PROD, GSYM PFORALL_THM] >>
metis_tac [MEM_EL]);

val eval_ctor_build_rec_env = Q.prove (
`!cenv s funs1 funs2 cl_env add_to_env.
  eval_ctor_inv cenv s add_to_env ∧
  eval_ctor_inv cenv s cl_env ∧
  EVERY (λ(f,x,e). check_ctors cenv e) funs1
  ⇒
  eval_ctor_inv cenv s ( FOLDR (λ(f,x,e) env'. bind f (Recclosure cl_env funs1 f) env') add_to_env funs2)`,
induct_on `funs2` >>
rw [] >>
PairCases_on `h` >>
fs [eval_ctor_inv_bind_env, build_rec_env_def, check_ctors_v_def] >>
fs [eval_ctor_inv_def]);

val cenv_bind_div_eq_def = Define `
cenv_bind_div_eq (cenv : envC) =
  ((lookup (Short "Div") cenv = SOME (0, TypeExn)) ∧
   (lookup (Short "Bind") cenv = SOME (0, TypeExn)) ∧
   (lookup (Short "Eq") cenv = SOME (0, TypeExn)))`;

val eval_ctor_inv_do_app = Q.prove (
`!s1 env1 op v1 v2 s2 env2 e.
  (do_app s1 env1 op v1 v2 = SOME (s2,env2,e)) ∧
  eval_ctor_inv cenv s1 env1 ∧
  check_ctors_v cenv v1 ∧
  check_ctors_v cenv v2 ∧
  cenv_bind_div_eq cenv
  ⇒
  check_ctors cenv e ∧
  eval_ctor_inv cenv s2 env2`,
rw [do_app_cases] >>
rw [check_ctors_def] >>
fs [do_con_check_def, cenv_bind_div_eq_def, check_ctors_v_def, eval_ctor_inv_bind_env] >|
[fs [eval_ctor_inv_def],
 induct_on `funs` >>
     rw [Once find_recfun_def] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0 = n'` >>
     fs [] >>
     metis_tac [],
 rw [build_rec_env_def] >>
     match_mp_tac eval_ctor_build_rec_env >>
     fs [eval_ctor_inv_def],
 fs [store_assign_def, eval_ctor_inv_def] >>
     fs [EVERY_EL] >>
     rw [EL_LUPDATE]]);

val eval_ctor_inv_do_log = Q.prove (
`!op v e1 e2.
  (do_log op v e1 = SOME e2) ∧
  check_ctors_v cenv v ∧
  check_ctors cenv e1 
  ⇒
  check_ctors cenv e2`, 
rw [do_log_def] >>
cases_on `v` >>
fs [] >>
cases_on `l` >>
fs [] >>
cases_on `b` >>
fs [] >>
cases_on `op` >>
fs [] >>
rw [] >>
fs [check_ctors_def]);

val eval_ctor_inv_do_if = Q.prove (
`!v e1 e2 e3.
  (do_if v e1 e2 = SOME e3) ∧
  check_ctors_v cenv v ∧
  check_ctors cenv e1 ∧
  check_ctors cenv e2 
  ⇒
  check_ctors cenv e3`, 
rw [do_if_def] >>
metis_tac []);

val check_ctors_result_def = Define `
(check_ctors_result cenv (Rval v) = check_ctors_v cenv v) ∧
(check_ctors_result cenv _ = T)`;

val check_ctors_result2_def = Define `
(check_ctors_result2 cenv n (Rval vs) = ((LENGTH vs = n) ∧ EVERY (check_ctors_v cenv) vs)) ∧
(check_ctors_result2 cenv n _ = T)`;

val check_ctors_match_result_def = Define `
(check_ctors_match_result cenv s (Match env) = 
  eval_ctor_inv cenv s env) ∧
(check_ctors_match_result cenv s _ = T)`;

val get_val_type_def = Define `
(get_val_type (cenv:envC) (Conv (SOME cn) vs) = 
  case lookup cn cenv of
     | NONE => NONE
     | SOME (len, tn) => SOME tn) ∧
(get_val_type cenv _ = NONE)`;

val pmatch'_pmatch2_lem = Q.prove (
`!ps vs env.
  (LENGTH ps = LENGTH vs) ∧
  EVERY var_pat ps ∧
  EVERY (check_ctors_v cenv) vs ∧
  eval_ctor_inv cenv s env
  ⇒
  (pmatch_list' s ps vs env = pmatch_list cenv s ps vs env) ∧
  check_ctors_match_result cenv s (pmatch_list cenv s ps vs env)`,
Induct >>
rw [] >>
cases_on `vs` >>
fs [pmatch_def, pmatch'_def, check_ctors_match_result_def, var_pat_def] >>
cases_on `h` >>
fs [pmatch_def, pmatch'_def, check_ctors_match_result_def, var_pat_def] >>
metis_tac [eval_ctor_inv_bind_env]);

val pmatch'_pmatch2 = Q.prove (
`!(cenv : envC) (s:store) p v env (menv : envM) t. 
  eval_ctor_inv cenv s env ∧ 
  check_ctors_p cenv t p ∧ 
  check_ctors_v cenv v 
  ⇒
  check_ctors_match_result cenv s (pmatch cenv s p v env) ∧
  ((pmatch' s p v env = pmatch cenv s p v env) ∨
   (?t1 t2. 
      pmatch' s p v env = No_match ∧
      pmatch cenv s p v env = Match_type_error ∧
      (get_pat_type cenv p = SOME t1) ∧ 
      (get_val_type cenv v = SOME t2) ∧ 
      t1 ≠ t2))`,
cases_on `p` >>
cases_on `v` >>
cases_on `t` >>
fs [pmatch_def, pmatch'_def, check_ctors_p_def, check_ctors_v_def, eval_ctor_inv_bind_env,
    check_ctors_match_result_def, get_pat_type_def, get_val_type_def] >-
rw [check_ctors_match_result_def] >|
[NTAC 4 strip_tac >>
     cases_on `o'` >>
     cases_on `o''` >>
     fs [check_ctors_p_def, pmatch_def] >>
     Cases_on `lookup x' cenv` >>
     fs [] >|
     [Cases_on `x''` >>
          fs [check_ctors_v_def, get_pat_type_def, get_val_type_def],
      PairCases_on `x'''` >>
          fs [] >>
          Cases_on `lookup x'' cenv` >>
          fs [do_con_check_def, check_ctors_p_def, get_pat_type_def,
              get_val_type_def, check_ctors_v_def] >>
          PairCases_on `x'''` >>
          fs [] >>
          rw [check_ctors_match_result_def] >>
          fs [] >>
          metis_tac [pmatch'_pmatch2_lem]],
 NTAC 4 STRIP_TAC >>
     every_case_tac >>
     fs [store_lookup_def, EVERY_EL] >>
     fs [check_ctors_p_def, EVERY_EL, eval_ctor_inv_def, check_ctors_match_result_def] >>
     cases_on `p'` >>
     fs [var_pat_def, pmatch_def, pmatch'_def, check_ctors_match_result_def,
         eval_ctor_inv_bind_env] >>
     fs [eval_ctor_inv_def, EVERY_EL] >>
     metis_tac []]);

val pmatch'_wrong_type = Q.prove (
`!cenv p v t1 t2 p'.
  (get_pat_type cenv p = SOME t1) ∧
  (get_val_type cenv v = SOME t2) ∧
  t1 ≠ t2 ∧
  check_ctors_p cenv (get_pat_type cenv p) p'
  ⇒
  pmatch' s p' v env = No_match`,
cases_on `p` >>
cases_on `v` >>
rw [get_pat_type_def, get_val_type_def] >>
every_case_tac >>
fs [] >>
cases_on `o'` >>
cases_on `o''` >>
cases_on `p'` >>
fs [check_ctors_p_def, pmatch'_def, get_pat_type_def, get_val_type_def] >>
rw [] >>
cases_on `lookup x cenv` >>
fs [] >>
cases_on `lookup x' cenv` >>
fs [] >>
PairCases_on `x''` >>
fs [] >>
PairCases_on `x'''` >>
fs [check_ctors_p_def]);

val eval'_to_eval2_lem = Q.prove (
`!pes cenv p v t1 t2 s env count err_v.
  (get_pat_type cenv p = SOME t1) ∧
  (get_val_type cenv v = SOME t2) ∧
  t1 ≠ t2 ∧
  (∀e. MEM e pes ⇒
        (λ(p',e').
           check_ctors_p cenv (get_pat_type cenv p) p' ∧
           check_ctors cenv e') e)
  ⇒
  evaluate_match' s env v pes err_v (s, Rerr (Rraise err_v)) ∨
  evaluate_match' s env v pes err_v (s, Rerr Rtype_error)`,
induct_on `pes` >>
rw [] >>
ONCE_REWRITE_TAC [evaluate_cases, evaluate'_cases] >>
rw [] >>
`(λ(p',e'). check_ctors_p cenv (get_pat_type cenv p) p' ∧ check_ctors cenv e') h`
        by metis_tac [] >>
PairCases_on `h` >>
fs [] >>
cases_on `ALL_DISTINCT (pat_bindings h0 [])` >>
fs [] >>
`pmatch' s h0 v env = No_match` by metis_tac [pmatch'_wrong_type] >>
rw [] >>
`evaluate_match' s env v pes err_v (s,Rerr (Rraise err_v)) ∨
 evaluate_match' s env v pes err_v (s,Rerr Rtype_error)`
         by metis_tac [] >>
rw [] >>
metis_tac []);

val eval'_to_eval_simple_pat = Q.store_thm ("eval'_to_eval_simple_pat",
`(!s env e r. evaluate' s env e r ⇒
   !menv cenv count s1 r1. (r = (s1,r1)) ∧ r1 ≠ Rerr (Rraise (Conv (SOME (Short "Bind")) [])) ∧ check_ctors cenv e ∧
      eval_ctor_inv cenv s env ⇒
      eval_ctor_inv cenv s1 env ∧
      check_ctors_result cenv r1 ∧
      evaluate F menv cenv (count,s) env e ((count,s1),r1)) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv cenv count s1 r1. (r = (s1,r1)) ∧ r1 ≠ Rerr (Rraise (Conv (SOME (Short "Bind")) [])) ∧ EVERY (check_ctors cenv) es ∧
      eval_ctor_inv cenv s env ⇒
      eval_ctor_inv cenv s1 env ∧
      check_ctors_result2 cenv (LENGTH es) r1 ∧
      evaluate_list F menv cenv (count,s) env es ((count,s1),r1)) ∧
 (!s env v pes err_v r. evaluate_match' s env v pes err_v r ⇒
   !menv (cenv:envC) count s1 r1. (r = (s1,r1)) ∧ r1 ≠ Rerr (Rraise (Conv (SOME (Short "Bind")) [])) ∧
      check_ctors_v cenv v ∧
      EVERY (\(p,e). check_ctors_p cenv (get_pat_type cenv (FST (HD pes))) p ∧ check_ctors cenv e) pes ∧
      eval_ctor_inv cenv s env ⇒
      eval_ctor_inv cenv s1 env ∧
      check_ctors_result cenv r1 ∧
      evaluate_match F menv cenv (count,s) env v pes err_v ((count,s1),r1))`,
 ho_match_mp_tac evaluate'_strongind >>
 REPEAT CONJ_TAC >>
 REPEAT GEN_TAC >>
 REPEAT DISCH_TAC >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
 SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
 fs [] >>
 fs [lookup_var_id_def, EVERY_MEM, check_ctors_result_def, check_ctors_v_def, check_ctors_def] >>
 BasicProvers.VAR_EQ_TAC >>
 fs []
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- cheat
 >- (cases_on `cn` >>
     fs [check_ctors_def, do_con_check_def, check_ctors_result_def, check_ctors_v_def, check_ctors_result2_def] >>
     rw [check_ctors_result_def, check_ctors_v_def, do_con_check_def] >>
     every_case_tac >>
     fs [EVERY_MEM] >>
     metis_tac [])
 >- (cases_on `cn` >>
     fs [check_ctors_def, do_con_check_def, check_ctors_result_def, check_ctors_v_def, check_ctors_result2_def] >>
     rw [check_ctors_result_def, check_ctors_v_def, do_con_check_def] >>
     every_case_tac >>
     fs [EVERY_MEM] >>
     metis_tac [])
 >- metis_tac [eval_ctor_inv_lookup, check_ctors_result_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def, eval_ctor_inv_def]
 >- metis_tac [check_ctors_result_def, eval_ctor_inv_do_uapp]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- cheat
 (*
 `check_ctors cenv e'' ∧
  eval_ctor_inv cenv s'' env'`
        by prove_tac [eval_ctor_inv_do_app] >>
     rw [] >|
     [fs [eval_ctor_inv_def] >>
          metis_tac [],
      metis_tac []],
      *)
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, eval_ctor_inv_do_log]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- metis_tac [check_ctors_result_def, eval_ctor_inv_do_if]
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- (cases_on `pes` >>
     fs [check_ctors_def] >>
     `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [check_ctors_def, LET_THM, EVERY_MEM, LAMBDA_PROD, GSYM PFORALL_THM,
         GSYM PEXISTS_THM] >>
     metis_tac [])
 >- (cases_on `pes` >>
     fs [check_ctors_def] >>
     `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [check_ctors_def, LET_THM, EVERY_MEM, LAMBDA_PROD, GSYM PFORALL_THM,
         GSYM PEXISTS_THM] >>
     metis_tac [])
 >- metis_tac [check_ctors_result_def, check_ctors_v_def, eval_ctor_inv_bind_env]
 >- (`eval_ctor_inv cenv s (build_rec_env funs env env)` 
            by (rw [build_rec_env_def] >>
                match_mp_tac eval_ctor_build_rec_env >>
                fs [eval_ctor_inv_def, EVERY_MEM]) >>
     rw [] >>
     fs [eval_ctor_inv_def, EVERY_MEM] >>
     metis_tac [])
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]
 >- rw [check_ctors_result2_def]
 >- (rw [check_ctors_result2_def] >>
     metis_tac [check_ctors_result2_def, check_ctors_result_def])
 >- (rw [check_ctors_result2_def] >>
     metis_tac [check_ctors_result2_def, check_ctors_result_def])
 >- metis_tac [check_ctors_result2_def, check_ctors_result_def]
 >- metis_tac [check_ctors_result2_def, check_ctors_result_def]
 >- metis_tac [check_ctors_result2_def, check_ctors_result_def]
 >- metis_tac [check_ctors_result2_def, check_ctors_result_def]
 >- (`pmatch cenv s p v env = Match env' ∧ eval_ctor_inv cenv s env'` 
         by metis_tac [pmatch'_pmatch2, match_result_distinct, check_ctors_match_result_def] >>
     rw [] >>
     fs [eval_ctor_inv_def] >>
     metis_tac [])
 >- (`(pmatch cenv s p v env = No_match) ∨ 
      ((pmatch cenv s p v env = Match_type_error) ∧
       ?t1 t2. get_pat_type cenv p = SOME t1 ∧ get_val_type cenv v = SOME t2 ∧ t1 ≠ t2)`
                 by metis_tac [pmatch'_pmatch2, match_result_distinct] >|
     [`(pes = []) ∨ ?p' e' pes'. pes = (p',e')::pes'` 
            by (cases_on `pes` >>
                rw [] >>
                cases_on `h` >>
                metis_tac []) >>
          fs [] >>
          `get_pat_type cenv p' = get_pat_type cenv p` 
                    by (rw [] >>
                        fs [LAMBDA_PROD, GSYM PFORALL_THM] >>
                        metis_tac [get_pat_type_thm]) >>
          metis_tac [],
      `evaluate_match' s env v pes err_v (s,Rerr (Rraise err_v)) ∨
       evaluate_match' s env v pes err_v (s,Rerr Rtype_error)`
                 by metis_tac [eval'_to_eval2_lem] >>
          imp_res_tac big_exp_determ' >>
          fs [check_ctors_result_def] >>
          cheat])
 >- (`pmatch cenv s p v env = Match_type_error` by metis_tac [pmatch'_pmatch2, match_result_distinct] >>
     rw [check_ctors_result_def])
 >- metis_tac [check_ctors_result_def, check_ctors_v_def]);

val check_ctors_dec_def = Define `
(check_ctors_dec cenv (Dlet p e) = (check_ctors_p cenv (get_pat_type cenv p) p ∧ check_ctors cenv e)) ∧
(check_ctors_dec cenv (Dletrec funs) = EVERY (λ(f,x,e). check_ctors cenv e) funs) ∧
(check_ctors_dec cenv (Dtype _) = T) ∧
(check_ctors_dec cenv (Dexn _ _) = T)`;

val check_ctors_result3_def = Define `
(check_ctors_result3 cenv (Rval (cenv',env)) = 
  EVERY (λ(x,v). check_ctors_v cenv v) env) ∧
(check_ctors_result3 cenv _ = T)`;

val eval_dec'_to_eval_dec_simple_pat = Q.store_thm ("eval_dec'_to_eval_dec_simple_pat",
`!mn menv cenv s env d s' r.
   (r ≠ Rerr (Rraise (Conv (SOME (Short "Bind")) []))) ∧
   check_ctors_dec cenv d ∧ 
   eval_ctor_inv cenv s env ∧
   evaluate_dec' mn menv cenv s env d (s',r)
   ⇒
   evaluate_dec mn menv cenv s env d (s',r) ∧
   eval_ctor_inv cenv s' env ∧
   check_ctors_result3 cenv r`,
rw [evaluate_dec_cases, evaluate_dec'_cases] >>
fs [check_ctors_dec_def, check_ctors_result3_def] >|
[`evaluate F menv cenv (0,s) env e ((0,s'), Rval v) ∧
  eval_ctor_inv cenv s' env ∧
  check_ctors_result cenv (Rval v)`
        by metis_tac [eval'_to_eval_simple_pat, result_distinct] >>
     fs [check_ctors_result_def] >>
     `eval_ctor_inv cenv s' (emp:(string,v) env)`
                 by fs [eval_ctor_inv_def, LibTheory.emp_def] >>
     metis_tac [pmatch'_pmatch2, match_result_distinct],
 metis_tac [eval'_to_eval_simple_pat, result_distinct],
 `evaluate F menv cenv (0,s) env e ((0,s'), Rval v) ∧
  eval_ctor_inv cenv s' env ∧
  check_ctors_result cenv (Rval v)`
        by metis_tac [eval'_to_eval_simple_pat, result_distinct] >>
     fs [check_ctors_result_def] >>
     `eval_ctor_inv cenv s' (emp:(string,v) env)`
                 by fs [eval_ctor_inv_def, LibTheory.emp_def] >>
     metis_tac [check_ctors_match_result_def, pmatch'_pmatch2, match_result_distinct, eval_ctor_inv_def],
 `evaluate F menv cenv (0,s) env e ((0,s'), Rval v) ∧
  eval_ctor_inv cenv s' env ∧
  check_ctors_result cenv (Rval v)`
        by metis_tac [eval'_to_eval_simple_pat, result_distinct] >>
     fs [check_ctors_result_def] >>
     `eval_ctor_inv cenv s' (emp:(string,v) env)`
                 by fs [eval_ctor_inv_def, LibTheory.emp_def] >>
     metis_tac [check_ctors_match_result_def, pmatch'_pmatch2, match_result_distinct, eval_ctor_inv_def],
 metis_tac [eval'_to_eval_simple_pat, result_distinct],
 metis_tac [eval'_to_eval_simple_pat, result_distinct, error_result_distinct, result_11],
 metis_tac [eval'_to_eval_simple_pat, result_distinct, error_result_distinct, result_11],
 fs [LibTheory.emp_def, eval_ctor_inv_def] >>
     metis_tac [SIMP_RULE (srw_ss()) [eval_ctor_inv_def] eval_ctor_build_rec_env, EVERY_DEF,
                build_rec_env_def],
 fs [LibTheory.emp_def]]);

val check_ctors_p_weakening = Q.prove (
`(!p cenv1 cenv2. 
  disjoint_env cenv1 cenv2 ∧ check_ctors_p cenv1 (get_pat_type cenv1 p) p ⇒
  check_ctors_p (cenv2++cenv1) (get_pat_type (cenv2++cenv1) p) p)`,
cases_on `p` >>
rw [check_ctors_p_def, get_pat_type_def, lookup_append] >>
cases_on `o'` >>
fs [check_ctors_p_def, get_pat_type_def, lookup_append] >>
every_case_tac >>
fs [check_ctors_p_def] >>
rw [lookup_append] >>
imp_res_tac lookup_in2 >>
fs [disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
metis_tac []);

val check_ctors_e_weakening = Q.prove (
`!cenv2 e cenv1. 
  disjoint_env cenv1 cenv2 ∧ check_ctors cenv1 e ⇒ check_ctors (cenv2++cenv1) e`,
ho_match_mp_tac (fetch "-" "check_ctors_ind") >>
rw [check_ctors_def, EVERY_MEM, do_con_check_def, lookup_append] >|
[cheat,
 every_case_tac >>
     imp_res_tac lookup_in2 >>
     fs [disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [],
 metis_tac [],
 Q.UNABBREV_TAC `t` >>
     fs [LET_THM] >>
     metis_tac [check_ctors_p_weakening],
 metis_tac [],
 PairCases_on `e''` >>
     fs [] >>
     Q.UNABBREV_TAC `t` >>
     fs [LET_THM] >>
     res_tac >>
     fs [] >>
     `get_pat_type cenv1 p = get_pat_type cenv1 e''0` by metis_tac [get_pat_type_thm] >>
     fs [] >>
     cases_on `e''0` >>
     cases_on `p` >> 
     fs [check_ctors_p_def, get_pat_type_def] >>
     cases_on `o'` >>
     fs [check_ctors_p_def, get_pat_type_def] >>
     cases_on `lookup x cenv1` >>
     fs [] >>
     TRY (PairCases_on `x'`) >>
     fs [check_ctors_p_def] >>
     cases_on `o''` >>
     fs [get_pat_type_def] >>
     every_case_tac >>
     fs [lookup_append] >>
     every_case_tac >>
     cases_on `lookup x cenv2` >>
     fs [] >>
     imp_res_tac lookup_in2 >>
     fs [disjoint_env_def, DISJOINT_DEF, EXTENSION, check_ctors_p_def] >>
     rw [] >>
     fs [lookup_append] >>
     metis_tac [],
 PairCases_on `e'` >>
     fs [] >>
     res_tac >>
     fs []]);

val check_ctors_v_weakening = Q.prove (
`!cenv1 v cenv2. disjoint_env cenv1 cenv2 ⇒ check_ctors_v cenv1 v ⇒ check_ctors_v (cenv2++cenv1) v`,
ho_match_mp_tac (fetch "-" "check_ctors_v_ind") >>
rw [check_ctors_v_def, EVERY_MEM, do_con_check_def, lookup_append] >|
[every_case_tac >>
     imp_res_tac lookup_in2 >>
     fs [disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [],
 PairCases_on `e'` >>
     fs [] >>
     res_tac >>
     fs [],
 metis_tac [check_ctors_e_weakening],
 PairCases_on `e` >>
     fs [] >>
     res_tac >>
     fs [],
 PairCases_on `e` >>
     fs [] >>
     res_tac >>
     fs [] >>
     metis_tac [check_ctors_e_weakening]]);

val check_ctors_dec_weakening = Q.prove (
`!cenv1 d cenv2. disjoint_env cenv1 cenv2 ⇒ check_ctors_dec cenv1 d ⇒ check_ctors_dec (cenv2++cenv1) d`,
cases_on `d` >>
rw [check_ctors_dec_def] >-
metis_tac [check_ctors_p_weakening] >-
metis_tac [check_ctors_e_weakening] >>
fs [EVERY_MEM] >>
rw [] >>
PairCases_on `e` >>
fs [] >>
res_tac >>
fs [] >>
metis_tac [check_ctors_e_weakening]);

val evaluate_dec_ctor_disjoint = Q.prove (
`!mn menv cenv s env d s2 new_tds new_env.
  evaluate_dec' mn menv cenv s env d (s2,Rval (new_tds,new_env))
  ⇒
  disjoint_env cenv new_tds`,
rw [evaluate_dec'_cases] >>
imp_res_tac check_dup_ctors_disj >>
fs [LibTheory.emp_def, disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
rw [] >>
pop_assum (mp_tac o Q.SPEC `x`) >>
rw [] >-
metis_tac [] >>
`lookup x (build_ctor_tenv mn tds) = NONE`
          by metis_tac [lookup_in2, optionTheory.option_nchotomy, optionTheory.NOT_SOME_NONE] >>
metis_tac [lookup_notin, lookup_none]);

val check_ctors_result4_def = Define `
(check_ctors_result4 cenv (Rval env) = 
  EVERY (λ(x,v). check_ctors_v cenv v) env) ∧
(check_ctors_result4 cenv _ = T)`;

val dec_to_cenv_def = Define `
(dec_to_cenv mn (Dtype tds) = build_tdefs mn tds) ∧
(dec_to_cenv mn _ = [])`;

val check_ctors_decs_def = Define `
(check_ctors_decs mn cenv [] = T) ∧
(check_ctors_decs mn cenv (d::ds) = 
  (check_ctors_dec cenv d ∧
   check_ctors_decs mn (dec_to_cenv mn d ++ cenv) ds))`;

val eval_dec'_to_cenv = Q.prove (
`evaluate_dec' mn menv cenv s env h (s2,Rval (new_tds,new_env))
 ⇒
 dec_to_cenv mn h = new_tds`,
rw [evaluate_dec'_cases, dec_to_cenv_def, LibTheory.emp_def] >>
rw [dec_to_cenv_def]);

val eval_decs'_to_eval_decs_simple_pat = Q.store_thm ("eval_decs'_to_eval_decs_simple_pat",
`!mn menv cenv s env ds s' r cenv'.
   (r ≠ Rerr (Rraise (Conv (SOME (Short "Bind")) []))) ∧
   check_ctors_decs mn cenv ds ∧ 
   eval_ctor_inv cenv s env ∧
   evaluate_decs' mn menv cenv s env ds (s',cenv',r)
   ⇒
   evaluate_decs mn menv cenv s env ds (s',cenv',r) ∧
   eval_ctor_inv (cenv'++cenv) s' env ∧
   check_ctors_result4 (cenv'++cenv) r`,
induct_on `ds` >>
REPEAT GEN_TAC >>
rw [Once evaluate_decs_cases, Once evaluate_decs'_cases, LibTheory.emp_def,
    check_ctors_result4_def, check_ctors_decs_def] >>
rw [check_ctors_result4_def] >-
metis_tac [eval_dec'_to_eval_dec_simple_pat, result_distinct, error_result_distinct, result_11] >-
metis_tac [eval_dec'_to_eval_dec_simple_pat, result_distinct, error_result_distinct, result_11] >>
`evaluate_dec mn menv cenv s env h (s2,(Rval (new_tds,new_env))) ∧
 eval_ctor_inv cenv s2 env ∧ 
 check_ctors_result3 cenv (Rval (new_tds,new_env))`
       by metis_tac [eval_dec'_to_eval_dec_simple_pat, result_distinct, error_result_distinct, result_11] >>
fs [LibTheory.merge_def, check_ctors_result3_def] >>
`disjoint_env cenv new_tds` by metis_tac [evaluate_dec_ctor_disjoint] >>
`eval_ctor_inv (new_tds ++ cenv) s2 (new_env++env)` 
           by (rw [eval_ctor_inv_def] >>
               fs [EVERY_MEM, eval_ctor_inv_def] >>
               rw [] >-
               metis_tac [check_ctors_v_weakening] >>
               PairCases_on `e` >>
               rw [] >>
               `(λ(x,v). check_ctors_v cenv v) (e0,e1)` by metis_tac [] >>
               fs [] >>
               metis_tac [LAMBDA_PROD, check_ctors_v_weakening]) >>
`evaluate_decs mn menv (new_tds ++ cenv) s2 (new_env ++ env) ds (s',new_tds',r') ∧
 eval_ctor_inv (new_tds' ++ new_tds ++ cenv) s' (new_env ++ env) ∧
 check_ctors_result4 (new_tds' ++ new_tds ++ cenv) r'`
       by (cases_on `r'` >>
           fs [combine_dec_result_def] >>
           metis_tac [eval_dec'_to_cenv, APPEND_ASSOC, result_distinct, error_result_distinct, result_11]) >-
metis_tac [] >-
fs [eval_ctor_inv_def] >>
cases_on `r'` >>
fs [combine_dec_result_def, check_ctors_result4_def, LibTheory.merge_def, eval_ctor_inv_def]);

(*
val check_ctors_top_def = Define `
(check_ctors_top cenv (Tdec d) =
  check_ctors_dec cenv d) ∧
(check_ctors_top cenv (Tmod mn specs ds)  =
  EVERY (check_ctors_dec cenv) ds)`;

val check_ctors_result5_def = Define `
(check_ctors_result5 cenv (Rval (menv,env)) = 
  EVERY (λ(x,v). check_ctors_v cenv v) env) ∧
(check_ctors_result5 cenv _ = T)`;

val eval_top'_to_eval_top_simple_pat = Q.store_thm ("eval_top'_to_eval_top_simple_pat",
`!menv cenv s env top s' cenv' r.
   (r ≠ Rerr (Rraise Bind_error)) ∧
   check_ctors_top cenv top ∧ 
   eval_ctor_inv cenv s env ∧
   evaluate_top' menv cenv s env top (s',cenv',r)
   ⇒
   evaluate_top menv cenv s env top (s',cenv',r) ∧
   eval_ctor_inv (cenv'++cenv) s' env ∧
   check_ctors_result5 (cenv'++cenv) r`,

rw [evaluate_top_cases, evaluate_top'_cases] >>
fs [check_ctors_top_def, check_ctors_result5_def] >>

metis_tac [eval_decs'_to_eval_decs_simple_pat, eval_dec'_to_eval_dec_simple_pat, 
           eval_ctor_inv_def, result_distinct, error_result_distinct, result_11] >>

           *)

val _ = export_theory ();
