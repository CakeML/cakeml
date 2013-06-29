open preamble
open SemanticPrimitivesTheory AltBigStepTheory BigStepTheory TypeSystemTheory;
open bigSmallEquivTheory determTheory untypedSafetyTheory;
open typeSoundTheory;
open terminationTheory bigClockTheory;

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
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate F menv cenv (count,s) env e ((count,s'), Rerr Rtype_error)) ⇒
     evaluate F menv cenv (count,s) env e ((count,s1),r1)) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate_list F menv cenv (count,s) env es ((count,s'), Rerr Rtype_error)) ⇒
     evaluate_list F menv cenv (count,s) env es ((count,s1),r1)) ∧
 (!s env v p r. evaluate_match' s env v p r ⇒
   !menv (cenv : envC) count s1 r1. 
     (r = (s1,r1)) ∧
     (!s'. ¬evaluate_match F menv cenv (count,s) env v p ((count,s'), Rerr Rtype_error)) ⇒
     evaluate_match F menv cenv (count,s) env v p ((count,s1),r1))`,
ho_match_mp_tac evaluate'_ind >>
rw [] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
TRY (qpat_assum `!s. ~evaluate F a0 b0 c0 d0 e0 f0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
TRY (qpat_assum `!s. ~evaluate_match F a0 b0 c0 d0 e0 f0 g0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
TRY (qpat_assum `!s. ~evaluate_list F a0 b0 c0 d0 e0 f0` (assume_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases])) >>
fs [lookup_var_id_def] >>
metis_tac [pmatch_pmatch', match_result_distinct, big_unclocked]);

val type_no_error = Q.prove (
`∀tenvM tenvC tenvS tenv st e t menv cenv env tvs.
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧
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

val atomic_pat_def = Define `
(atomic_pat (Pvar x) = T) ∧
(atomic_pat (Plit x) = T)`;

val check_ctors_p_def = Define `
(check_ctors_p cenv t (Pvar x) = T) ∧
(check_ctors_p cenv t (Plit l) = T) ∧
(check_ctors_p cenv t (Pcon cn ps) =
  case lookup cn cenv of
     | NONE => F
     | SOME (len, tn) =>
         (t = SOME tn) ∧
         (len = LENGTH ps) ∧
         EVERY atomic_pat ps) ∧
(check_ctors_p cenv t (Pref p) = atomic_pat p)`;

val get_pat_type_def = Define `
(get_pat_type cenv (Pvar x) = NONE) ∧
(get_pat_type cenv (Plit x) = NONE) ∧
(get_pat_type cenv (Pref x) = NONE) ∧
(get_pat_type cenv (Pcon cn ps) = 
  case lookup cn cenv of
     | NONE => NONE
     | SOME (len, tn) => SOME tn)`;

val check_ctors_def = tDefine "check_ctors" `
(check_ctors (cenv:envC) (Raise e) = T) ∧
(check_ctors cenv (Handle e1 x e2) = 
  (check_ctors cenv e1 ∧ check_ctors cenv e2)) ∧
(check_ctors cenv (Lit l) = T) ∧
(check_ctors cenv (Con cn es) = 
  (do_con_check cenv cn (LENGTH es) ∧
   EVERY (check_ctors cenv) es)) ∧
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
 induct_on `es`] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
srw_tac [ARITH_ss] [AstTheory.exp_size_def] >>
res_tac >>
decide_tac);

val check_ctors_v_def = tDefine "check_ctors_v" `
(check_ctors_v cenv (Litv l) = T) ∧
(check_ctors_v cenv (Conv cn vs) =
  (do_con_check cenv cn (LENGTH vs) ∧
   EVERY (check_ctors_v cenv) vs)) ∧
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

(*
val eval_check_ctors_pres = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r.
   evaluate ck menv cenv s env e r ⇒
   !count s1 r1 v.
     (r = ((count,s1), Rval v)) ⇒
     check_ctors_v cenv v) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r.
   evaluate_list ck menv cenv s env es r ⇒
   !count s1 r1 v.
     (r = ((count,s1), Rval v)) ⇒
     EVERY (check_ctors_v cenv) v) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r.
   evaluate_match ck menv cenv s env v pes r ⇒
   !count s1 r1 v.
     (r = ((count,s1), Rval v)) ⇒
     check_ctors_v cenv v)`,

ho_match_mp_tac evaluate_ind >>
rw [check_ctors_v_def] >|
[fs [do_con_check_def] >>
     every_case_tac >>
     rw []
     *)

     (*
val pmatch'_pmatch2 = Q.prove (
`(!(cenv : envC) (s:store) p v env t. 
   EVERY (check_ctors_v cenv) s ∧ check_ctors_p cenv t p ∧ check_ctors_v cenv v ⇒
   (pmatch' s p v env = pmatch cenv s p v env)) ∧
 (!(cenv : envC) (s:store) ps vs env env' t. 
    EVERY (check_ctors_v cenv) s ∧ EVERY (check_ctors_p cenv t) ps ∧ EVERY (check_ctors_v cenv) vs ⇒
   (pmatch_list' s ps vs env = pmatch_list cenv s ps vs env))`,
cheat)
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, pmatch'_def, check_ctors_p_def, check_ctors_v_def] >|
[Cases_on `lookup n cenv` >>
     fs [do_con_check_def] >>
     Cases_on `x` >>
     fs [] >>
     metis_tac [],
 Cases_on `lookup n cenv` >>
     fs [do_con_check_def] >>
     Cases_on `x` >>
     fs [] >>
     metis_tac [],
 Cases_on `lookup n cenv` >>
     fs [do_con_check_def] >>
     Cases_on `x` >>
     fs [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     all_tac,
 every_case_tac >>
     fs [store_lookup_def, EVERY_EL] >>
     metis_tac [],
 every_case_tac >>
     fs []]);

val unfinished = all_tac;
val eval'_to_eval2 = Q.prove (
`(!s env e r. evaluate' s env e r ⇒
   !menv cenv count s1 r1. (r = (s1,r1)) ∧ check_ctors cenv e ⇒
   evaluate F menv cenv (count,s) env e ((count,s1),r1)) ∧
 (!s env es r. evaluate_list' s env es r ⇒
   !menv cenv count s1 r1. (r = (s1,r1)) ∧ EVERY (check_ctors cenv) es ⇒
   evaluate_list F menv cenv (count,s) env es ((count,s1),r1)) ∧
 (!s env v pes r. evaluate_match' s env v pes r ⇒
   !menv (cenv:envC) count s1 r1. (r = (s1,r1)) ∧
   EVERY (\(p,e). check_ctors_p cenv (get_pat_type cenv (FST (HD pes))) p ∧ check_ctors cenv e) pes ⇒
   evaluate_match F menv cenv (count,s) env v pes ((count,s1),r1))`,

ho_match_mp_tac evaluate'_ind >>
rw [check_ctors_def] >>
SIMP_TAC (srw_ss()) [Once evaluate_cases] >>
fs [] >>
fs [lookup_var_id_def, EVERY_MEM] >|
[metis_tac [],
 metis_tac [],
 metis_tac [],
(* `check_ctors cenv e''`
            by (fs [do_app_cases] >>
                rw [check_ctors_def])
                *)
 unfinished,
 metis_tac [],
 metis_tac [],
 `check_ctors cenv e'`
            by (fs [do_log_def] >>
                rw [] >>
                cases_on `v` >>
                fs [] >>
                cases_on `l` >>
                fs [] >>
                every_case_tac >>
                rw [check_ctors_def]) >>
     metis_tac [],
 metis_tac [],
 `check_ctors cenv e'`
            by (fs [do_if_def] >>
                rw [] >>
                every_case_tac >>
                rw [check_ctors_def]) >>
     metis_tac [],
 metis_tac [],
 induct_on `pes` >>
     rw [] >>
     fs [check_ctors_def] >>
     `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [check_ctors_def, LET_THM] >>
     disj1_tac >>
     qexists_tac `v` >>
     qexists_tac `(count',s')` >>
     rw [] >>
     pop_assum match_mp_tac >>
     rw [] >>
     rw [] >>
     `?p e. e'' = (p,e)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [EVERY_MEM] >>
     res_tac >>
     fs [],
 cases_on `pes` >>
     fs [check_ctors_def] >>
     `?p e. h = (p,e)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [check_ctors_def, LET_THM],
 metis_tac [],
 metis_tac [],
 metis_tac [],
 unfinished,
 unfinished,
 unfinished]


 *) 


val _ = export_theory ();
