open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open intLang2Theory;
open intLang3Theory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "toIntLang3Proof";

val exp_to_i3_correct = Q.prove (
`(∀b env s e res. 
   evaluate_i2 b env s e res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_i3 b env' (s,genv) e ((s',genv),r)) ∧
 (∀b env s es res.
   evaluate_list_i2 b env s es res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_list_i3 b env' (s,genv) es ((s',genv),r)) ∧
 (∀b env s v pes res. 
   evaluate_match_i2 b env s v pes res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_match_i3 b env' (s,genv) v pes ((s',genv),r))`,
 ho_match_mp_tac evaluate_i2_ind >>
 rw [] >>
 rw [Once evaluate_i3_cases] >>
 fs [all_env_i2_to_genv_def, all_env_i2_to_env_def]
 >- metis_tac []
 >- (* Uapp *)
    (fs [do_uapp_i2_def, do_uapp_i3_def] >>
     every_case_tac >>
     fs [LET_THM]
     >- (Q.LIST_EXISTS_TAC [`Loc_i2 n`,`s2`] >>
         rw [])
     >- (Q.LIST_EXISTS_TAC [`v`, `s2`, `genv`] >>
         rw [] >>
         cases_on `store_alloc v s2` >>
         fs []))
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []);

 (*
val eval_i3_genv_weakening = Q.prove (
`(∀b env s e res. 
   evaluate_i3 b env s e res ⇒ 
   !s' s'' genv env' r genv' genv''.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_i3 b env (s',genv++genv'') e ((s'',genv'++genv''),r)) ∧
 (∀b env s es res.
   evaluate_list_i3 b env s es res ⇒ 
   !s' s'' genv genv' genv'' env' r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_list_i3 b env (s',genv++genv'') es ((s'',genv'++genv''),r) )∧
 (∀b env s v pes err_v res. 
   evaluate_match_i3 b env s v pes res ⇒ 
   !s' s'' genv genv' genv'' env' r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_match_i3 b env (s',genv++genv'') v pes ((s'',genv'++genv''),r))`,
 ho_match_mp_tac evaluate_i3_ind >>
 rw [] >>
 srw_tac [ARITH_ss] [Once evaluate_i3_cases] >>
 >- cheat
 >- srw_tac [ARITH_ss] [EL_APPEND1]
 >- srw_tac [ARITH_ss] [EL_APPEND1]
 >- (CCONTR_TAC >>
     fs [arithmeticTheory.NOT_GREATER]
     >- decide_tac 
     >- cheat)
 >- metis_tac []
 >- (fs [do_uapp_i3_def] >>
     every_case_tac >>
     fs [LET_THM]
     >- (Q.LIST_EXISTS_TAC [`Loc_i2 n`,`s2`] >>
         rw [])
     >- (Q.LIST_EXISTS_TAC [`v`, `s2`] >>
         rw [] >>
         cases_on `store_alloc v s2` >>
         fs []))
 >- (rw [] >>
     Q.LIST_EXISTS_TAC [`v`, `s2`, `genv++genv''`] >>
     rw []
     >- metis_tac []


     *)



val eval_i3_extend_genv = Q.prove (
`!b env s genv n s' genv' v.
  evaluate_i3 b env (s,genv) (Extend_global_i2 n) (s',r)
  ⇔
  r = Rval (Litv_i2 Unit) ∧
  s' = (s,genv ++ GENLIST (\x. NONE) n)`,
 rw [Once evaluate_i3_cases] >>
 metis_tac []);

val eval_i3_var =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Var_local_i2 var) (s',r)``;

val eval_i3_con =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Con_i2 tag es) (s',r)``;

val eval_i3_mat =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Mat_i2 e pes) (s',r)``;

val eval_match_i3_nil = 
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_match_i3 b env s v [] (s',r)``;

val eval_match_i3_var = 
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, eval_match_i3_nil, eval_i3_var, pmatch_i2_def] ``evaluate_match_i3 b env s v [(Pvar_i2 var, Var_local_i2 var)] (s',r)``;

val (dec_result_to_i3_rules, dec_result_to_i3_ind, dec_result_to_i3_cases) = Hol_reln `
(∀v. dec_result_to_i3 NONE (Rval v)) ∧
(∀err. dec_result_to_i3 (SOME (Rraise err)) (Rerr (Rraise err))) ∧
(dec_result_to_i3 (SOME Rtype_error) (Rerr Rtype_error)) ∧
(dec_result_to_i3 (SOME Rtimeout_error) (Rerr Rtimeout_error))`;

(*
val decs_to_i3_correct = Q.prove (
`!ck genv s ds s' new_env r next.
  evaluate_decs_i2 ck genv s ds (s',new_env,r) ∧
  r ≠ SOME Rtype_error
  ⇒
  ?r_i3.
    dec_result_to_i3 r r_i3 ∧ 
    evaluate_i3 ck [] (s,genv ++ GENLIST (\x. NONE) (num_defs ds)) (decs_to_i3 next ds)
                ((s',genv ++ MAP SOME new_env ++ GENLIST (\x. NONE) (num_defs ds - LENGTH new_env)),r_i3)`,

 induct_on `ds` >>
 rw [decs_to_i3_def] 
 >- fs [Once evaluate_decs_i2_cases, Once evaluate_i3_cases, dec_result_to_i3_cases, num_defs_def] >>
 Cases_on `h` >>
 qpat_assum `evaluate_decs_i2 x0 x1 x2 x3 x4` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [num_defs_def, LET_THM] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [] >>
 fs [evaluate_dec_i2_cases] >>
 rw [] >>
 imp_res_tac exp_to_i3_correct >>
 fs [emp_def] >>
 pop_assum mp_tac >>
 rw [eval_i3_mat, opt_bind_def]
 >- (qexists_tac `Rerr e'` >>
     rw [dec_result_to_i3_cases]
     >- (cases_on `e'` >>
         fs [])
     >- cheat)
 >- (res_tac >>
     pop_assum (qspecl_then [`next + LENGTH new_env'`] strip_assume_tac) >>
     qexists_tac `r_i3` >>
     rw [] >>
     fs [dec_result_to_i3_cases] >>
     srw_tac [ARITH_ss] [GENLIST_APPEND] >>
     cheat)
 >- (res_tac >>
     fs [] >>
     pop_assum (qspecl_then [`next + LENGTH new_env'`] strip_assume_tac) >>
     rw [] >>
     fs [dec_result_to_i3_cases] >>
     srw_tac [ARITH_ss] [GENLIST_APPEND] >>
     disj2_tac
     metis_tac []

 res_tac
metis_tac []
*)

val prompt_num_defs_def = Define `
prompt_num_defs (Prompt_i2 ds) = num_defs ds`;

val eval_decs_num_defs = Q.prove (
`!ck genv s ds s' env.
  evaluate_decs_i2 ck genv s ds (s',env,NONE) ⇒ num_defs ds - LENGTH env = 0`,
 induct_on `ds` >>
 rw [num_defs_def] >>
 cases_on `h` >>
 rw [num_defs_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [] >>
 res_tac >>
 rw [] >>
 fs [evaluate_dec_i2_cases]);

val (result_to_i3_rules, result_to_i3_ind, result_to_i3_cases) = Hol_reln `
(∀v. result_to_i3 NONE (Rval v)) ∧
(∀err. result_to_i3 (SOME (Rraise err)) (Rval err)) ∧
(result_to_i3 (SOME Rtype_error) (Rerr Rtype_error)) ∧
(result_to_i3 (SOME Rtimeout_error) (Rerr Rtimeout_error))`;

(*
val prompt_to_i3_correct = Q.prove (
`!ck genv s p new_env s' r next next' e.
  evaluate_prompt_i2 ck genv s p (s',new_env,r) ∧
  r ≠ SOME Rtype_error ∧
  ((next',e) = prompt_to_i3 next p)
  ⇒
  ?r_i3.
    result_to_i3 r r_i3 ∧
    evaluate_i3 ck [] (s,genv) e ((s',genv++new_env),r_i3)`,
 rw [evaluate_prompt_i2_cases, prompt_to_i3_def] >>
 fs [LET_THM] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [eval_i3_extend_genv] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [eval_i3_con, eval_match_i3_var, pat_bindings_i2_def, bind_def, lookup_def, opt_bind_def, prompt_num_defs_def] >>
 imp_res_tac decs_to_i3_correct >>
 fs [result_to_i3_cases] 
 >- (`num_defs ds - LENGTH env = 0` by metis_tac [eval_decs_num_defs] >>
     full_simp_tac bool_ss [] >>
     fs [] >>
     metis_tac []) >>
 pop_assum mp_tac >>
 rw [] >>
 pop_assum (qspecl_then [`next`] mp_tac) >>
 rw []);
 *)

val _ = export_theory ();
