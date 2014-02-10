open preamble;
open optionTheory;
open libTheory astTheory semanticPrimitivesTheory bigStepTheory terminationTheory;
open bigClockTheory;
open intLang1Theory;
open evalPropsTheory;

val _ = new_theory "toIntLang1Proof";

val LUPDATE_MAP = Q.prove (
`!x n l f. MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)`,
 induct_on `l` >>
 rw [LUPDATE_def] >>
 cases_on `n` >>
 fs [LUPDATE_def]);

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (exp_to_i1_def, exp_to_i1_ind) =
  tprove_no_defn ((exp_to_i1_def, exp_to_i1_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
  srw_tac [ARITH_ss] [size_abbrevs, exp_size_def]);
val _ = register "exp_to_i1_ind" exp_to_i1_def exp_to_i1_ind;

val (do_eq_i1_def, do_eq_i1_ind) =
  tprove_no_defn ((do_eq_i1_def, do_eq_i1_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y) => v_i1_size x
                                        | INR (xs,ys) => v_i14_size xs)`);
val _ = register "do_eq_i1_ind" do_eq_i1_def do_eq_i1_ind;

val v_to_i1_def = tDefine "v_to_i1" `
(v_to_i1 mods tops (Litv lit) = 
  Litv_i1 lit) ∧
(v_to_i1 mods tops (Conv cn vs) = 
  Conv_i1 cn (vs_to_i1 mods tops vs)) ∧
(v_to_i1 mods tops (Closure (menv,cenv,env) x e) = 
  Closure_i1 (cenv, FILTER (λ(n,v). n ∉ FDOM tops) (env_to_i1 mods tops env)) x (exp_to_i1 mods (tops \\ x) e)) ∧
(v_to_i1 mods tops (Recclosure (menv,cenv,env) funs x) = 
  let new_tops = FOLDR (\(n,x,y) m. m \\ n) tops funs in
    Recclosure_i1 (cenv, FILTER (λ(n,v). n ∉ FDOM new_tops) (env_to_i1 mods new_tops env)) (funs_to_i1 mods new_tops funs) x) ∧
(v_to_i1 mods tops (Loc loc) = Loc_i1 loc) ∧
(vs_to_i1 mods tops [] = []) ∧
(vs_to_i1 mods tops (v::vs) = v_to_i1 mods tops v :: vs_to_i1 mods tops vs) ∧
(env_to_i1 mods tops [] = []) ∧
(env_to_i1 mods tops ((x,v)::env) = (x,v_to_i1 mods tops v) :: env_to_i1 mods tops env)`
(wf_rel_tac `inv_image (<) (\x. case x of INL (x,y,v) => v_size v
                                        | INR (INL (x,y,vs)) => vs_size vs
                                        | INR (INR (x,y,env)) => envE_size env)` >>
 srw_tac [ARITH_ss] [v_size_def]);

val result_to_i1_def = Define `
(result_to_i1 mods tops (Rval v) = Rval (v_to_i1 mods tops v)) ∧
(result_to_i1 mods tops (Rerr (Rraise v)) = Rerr (Rraise (v_to_i1 mods tops v))) ∧
(result_to_i1 mods tops (Rerr Rtimeout_error) = Rerr Rtimeout_error) ∧
(result_to_i1 mods tops (Rerr Rtype_error) = Rerr Rtype_error)`;

val results_to_i1_def = Define `
(results_to_i1 mods tops (Rval vs) = Rval (vs_to_i1 mods tops vs)) ∧
(results_to_i1 mods tops (Rerr (Rraise v)) = Rerr (Rraise (v_to_i1 mods tops v))) ∧
(results_to_i1 mods tops (Rerr Rtimeout_error) = Rerr Rtimeout_error) ∧
(results_to_i1 mods tops (Rerr Rtype_error) = Rerr Rtype_error)`;

val s_to_i1_def = Define `
s_to_i1 mods tops (c,s) = (c,MAP (v_to_i1 mods tops) s)`;

val global_env_inv_def = Define `
global_env_inv mods tops menv env genv ⇔
  EVERY (\(x,v). case FLOOKUP tops x of 
                     NONE => T
                   | SOME n => n < LENGTH genv ∧ v_to_i1 mods tops v = EL n genv)
        env ∧
  EVERY (\(mn,env). 
           case FLOOKUP mods mn of
            | NONE => F
            | SOME map =>
                EVERY (λ(x,v). case FLOOKUP map x of
                                | NONE => F
                                | SOME n => n < LENGTH genv ∧ v_to_i1 mods tops v = EL n genv)
                      env)
        menv`;

val env_all_to_i1_def = Define `
env_all_to_i1 mods tops (menv,cenv,env) (genv,cenv',lenv) ⇔
  global_env_inv mods tops menv env genv ∧
  cenv = cenv' ∧
  lenv = FILTER (\(n,v). n ∉ FDOM tops) (env_to_i1 mods tops env)`;

val do_con_check_i1 = Q.prove (
`!mods tops env cn es env_i1. 
  do_con_check (all_env_to_cenv env) cn (LENGTH es) ∧
  env_all_to_i1 mods tops env env_i1
  ⇒
  do_con_check (all_env_i1_to_cenv env_i1) cn (LENGTH (exps_to_i1 mods tops es))`,
 rw [do_con_check_def] >>
 every_case_tac >>
 fs [] >>
 PairCases_on `env` >>
 PairCases_on `env_i1` >>
 fs [env_all_to_i1_def, all_env_i1_to_cenv_def, all_env_to_cenv_def] >>
 rw [] >>
 fs [] >>
 rw [] >>
 ntac 2 (pop_assum (fn _ => all_tac)) >>
 induct_on `es` >>
 rw [exp_to_i1_def]);

val build_conv_i1 = Q.prove (
`!mods tops env cn vs v env_i1.
  (build_conv (all_env_to_cenv env) cn vs = SOME v) ∧
  env_all_to_i1 mods tops env env_i1
  ⇒
  (build_conv_i1 (all_env_i1_to_cenv env_i1) cn (vs_to_i1 mods tops vs) = SOME (v_to_i1 mods tops v))`,
 rw [build_conv_def, build_conv_i1_def] >>
 every_case_tac >>
 rw [v_to_i1_def] >>
 PairCases_on `env` >>
 PairCases_on `env_i1` >>
 fs [env_all_to_i1_def, all_env_i1_to_cenv_def, all_env_to_cenv_def] >>
 rw [v_to_i1_def] >>
 fs []);

val global_env_inv_lookup = Q.prove (
`!mods tops menv env genv x v n.
  global_env_inv mods tops menv env genv ∧
  lookup x env = SOME v ∧
  FLOOKUP tops x = SOME n
  ⇒
  LENGTH genv > n ∧ v_to_i1 mods tops v = EL n genv`,
 induct_on `env` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = x` >>
 fs [] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
 metis_tac []);

val global_env_inv_lookup_mod1 = Q.prove (
`!mods tops menv env genv mn n env'.
  global_env_inv mods tops menv env genv ∧
  lookup mn menv = SOME env'
  ⇒
  ?n. FLOOKUP mods mn = SOME n`,
 induct_on `menv` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = mn` >>
 fs [] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
 cases_on `FLOOKUP mods h0` >>
 fs [] >>
 metis_tac []);

val global_env_inv_lookup_mod2 = Q.prove (
`!mods tops menv env genv mn n env' x v map.
  global_env_inv mods tops menv env genv ∧
  lookup mn menv = SOME env' ∧
  lookup x env' = SOME v ∧
  FLOOKUP mods mn = SOME map
  ⇒
  ?n. FLOOKUP map x = SOME n`,
 induct_on `menv` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = mn` >>
 fs [] >>
 rw []
 >- (induct_on `env'` >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0' = x` >>
     fs [] >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
     cases_on `FLOOKUP mods h0` >>
     fs [] >>
     cases_on `FLOOKUP x h0'` >>
     fs [] >>
     metis_tac []) >>
 full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
 metis_tac []);

val global_env_inv_lookup_mod3 = Q.prove (
`!mods tops menv env genv mn n env' x v map n.
  global_env_inv mods tops menv env genv ∧
  lookup mn menv = SOME env' ∧
  lookup x env' = SOME v ∧
  FLOOKUP mods mn = SOME map ∧
  FLOOKUP map x = SOME n
  ⇒
  LENGTH genv > n ∧ v_to_i1 mods tops v = EL n genv`,
 induct_on `menv` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = mn` >>
 fs [] >>
 rw []
 >- (induct_on `env'` >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0' = x` >>
     fs [] >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
     cases_on `FLOOKUP mods h0` >>
     fs [] >>
     cases_on `FLOOKUP x h0'` >>
     rw [] >>
     fs [] >>
     srw_tac [ARITH_ss] [] >>
     metis_tac [])
 >- (full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
     metis_tac [])
 >- (induct_on `env'` >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0' = x` >>
     fs [] >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
     cases_on `FLOOKUP mods h0` >>
     fs [] >>
     cases_on `FLOOKUP x h0'` >>
     rw [] >>
     fs [] >>
     srw_tac [ARITH_ss] [] >>
     metis_tac [])
 >- (full_simp_tac (srw_ss()++ARITH_ss) [global_env_inv_def] >>
     metis_tac []));

val do_uapp_i1 = Q.prove (
`!mods tops s1 s2 uop v1 v2. 
  (do_uapp s1 uop v1 = SOME (s2, v2))
  ⇒
  (do_uapp_i1 (MAP (v_to_i1 mods tops) s1) uop (v_to_i1 mods tops v1) = SOME (MAP (v_to_i1 mods tops) s2, v_to_i1 mods tops v2))`,
 rw [do_uapp_def, do_uapp_i1_def] >>
 every_case_tac >>
 fs [store_alloc_def, LET_THM, v_to_i1_def] >>
 rw [v_to_i1_def] >>
 fs [EL_MAP, store_lookup_def]);

val length_vs_to_i1 = Q.prove (
`!vs mods tops. LENGTH (vs_to_i1 mods tops vs) = LENGTH vs`,
 induct_on `vs` >>
 rw [v_to_i1_def]);

val do_eq_i1 = Q.prove (
`(!v1 v2 mods tops r.
  do_eq v1 v2 = r
  ⇒ 
  do_eq_i1 (v_to_i1 mods tops v1) (v_to_i1 mods tops v2) = r) ∧
 (!vs1 vs2 mods tops r.
  do_eq_list vs1 vs2 = r
  ⇒ 
  do_eq_list_i1 (vs_to_i1 mods tops vs1) (vs_to_i1 mods tops vs2) = r)`,
 ho_match_mp_tac do_eq_ind >>
 rw [do_eq_i1_def, do_eq_def, v_to_i1_def] >>
 rw [] >>
 fs [length_vs_to_i1]
 >- (PairCases_on `v1` >> PairCases_on `v5` >> rw [do_eq_i1_def, v_to_i1_def])
 >- (PairCases_on `v8` >> PairCases_on `v11` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v14` >> PairCases_on `v17` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v20` >> PairCases_on `v23` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v56` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v59` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v76` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v79` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v36` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v36` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v36` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v39` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v39` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v39` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v136` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def]))
 >- (PairCases_on `v139` >> ntac 2 (rw [do_eq_i1_def, v_to_i1_def])) >>
 every_case_tac >>
 metis_tac []);

 (*
val do_app_i1 = Q.prove (
`!mods tops env s1 s2 op v1 v2 e env' env_i1. 
  (op ≠ Opapp) ∧
  (do_app env s1 op v1 v2 = SOME (env', s2, e)) ∧
  env_all_to_i1 mods tops env env_i1
  ⇒
   (env = env') ∧
   do_app_i1 env_i1 (MAP (v_to_i1 mods tops) s1) op (v_to_i1 mods tops v1) (v_to_i1 mods tops v2) = 
        SOME (env_i1, MAP (v_to_i1 mods tops) s2, (exp_to_i1 mods tops e))`,
 fs [do_app_cases, do_app_i1_def] >>
 rw [v_to_i1_def, exp_to_i1_def, env_all_to_i1_def, bind_def] >>
 rw [v_to_i1_def, exp_to_i1_def, env_all_to_i1_def, bind_def] >>
 every_case_tac >>
 fs [store_assign_def] >>
 rw [LUPDATE_MAP] >>
 metis_tac [do_eq_i1, eq_result_11, eq_result_distinct]);
 *)

val exp_to_i1_correct = Q.prove (
`(∀b env s e res. 
   evaluate b env s e res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !mods tops s' r env_i1 s_i1 e_i1 s'_i1 r_i1 locals.
     (res = (s',r)) ∧
     (env_all_to_i1 mods tops env env_i1) ∧
     (s_i1 = s_to_i1 mods tops s) ∧
     (e_i1 = exp_to_i1 mods tops e) ∧
     (s'_i1 = s_to_i1 mods tops s') ∧
     (r_i1 = result_to_i1 mods tops r)
     ⇒
     evaluate_i1 b env_i1 s_i1 e_i1 (s'_i1, r_i1)) ∧
 (∀b env s es res.
   evaluate_list b env s es res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !mods tops s' r env_i1 s_i1 es_i1 s'_i1 r_i1 locals.
     (res = (s',r)) ∧
     (env_all_to_i1 mods tops env env_i1) ∧
     (s_i1 = s_to_i1 mods tops s) ∧
     (es_i1 = exps_to_i1 mods tops es) ∧
     (s'_i1 = s_to_i1 mods tops s') ∧
     (r_i1 = results_to_i1 mods tops r)
     ⇒
     evaluate_list_i1 b env_i1 s_i1 es_i1 (s'_i1, r_i1)) ∧
 (∀b env s v pes err_v res. 
   evaluate_match b env s v pes err_v res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !mods tops s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 s'_i1 r_i1 locals.
     (res = (s',r)) ∧
     (env_all_to_i1 mods tops env env_i1) ∧
     (s_i1 = s_to_i1 mods tops s) ∧
     (v_i1 = v_to_i1 mods tops v) ∧
     (pes_i1 = pat_exp_to_i1 mods tops pes) ∧
     (err_v_i1 = v_to_i1 mods tops err_v) ∧
     (s'_i1 = s_to_i1 mods tops s') ∧
     (r_i1 = result_to_i1 mods tops r)
     ⇒
     evaluate_match_i1 b env_i1 s_i1 v_i1 pes_i1 err_v_i1 (s'_i1, r_i1))`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >>
 fs [result_to_i1_def] >>
 TRY (Cases_on `err`) >>
 fs [result_to_i1_def, results_to_i1_def] >>
 rw [Once evaluate_i1_cases,exp_to_i1_def, result_to_i1_def, v_to_i1_def]
 >- metis_tac []
 >- metis_tac [do_con_check_i1, build_conv_i1]
 >- metis_tac [do_con_check_i1]
 >- metis_tac [do_con_check_i1]
 >- (PairCases_on `env` >>
     PairCases_on `env_i1` >>
     cases_on `n` >>
     rw [exp_to_i1_def] >>
     fs [lookup_var_id_def] >>
     every_case_tac >>
     fs [env_all_to_i1_def, all_env_i1_to_env_def, all_env_i1_to_genv_def] >>
     rw []
     >- (pop_assum mp_tac >>
         pop_assum (fn _ => all_tac) >>
         induct_on `env3` >>
         rw [] >>
         PairCases_on `h` >>
         fs [v_to_i1_def] >>
         every_case_tac >>
         rw [] >>
         fs [FLOOKUP_DEF])
     >- metis_tac [global_env_inv_lookup]
     >- metis_tac [global_env_inv_lookup]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod1]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod1]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod2]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod2]
     >- metis_tac [global_env_inv_lookup_mod3]
     >- metis_tac [global_env_inv_lookup_mod3])
 >- (PairCases_on `env` >>
     PairCases_on `env_i1` >>
     fs [v_to_i1_def, env_all_to_i1_def, all_env_i1_to_cenv_def, all_env_i1_to_env_def] >>
     rw [])
 >- metis_tac [s_to_i1_def, do_uapp_i1]
 (*
 >- (Cases_on `op ≠ Opapp` >>
     fs [s_to_i1_def]
     >- metis_tac [do_app_i1] >>

     rw [] >>
     disj1_tac >>
     fs [do_app_cases, do_app_i1_def] >>
     rw [] 
     >- (qexists_tac `v_to_i1 mods tops (Closure (menv'',cenv'',env'') n e'')` >>
         qexists_tac `v_to_i1 mods tops v2` >>
         fs [v_to_i1_def] >>
         rw [] >>
         qexists_tac `s_to_i1 mods tops s'` >>
         qexists_tac `MAP (v_to_i1 mods tops) s3` >>
         qexists_tac `count'` >>
         rw []

 
         `env_all_to_i1 mods (tops \\ n) (menv'',cenv'',bind n v2 env'') 
                        (all_env_i1_to_genv env_i1,cenv'',bind n (v_to_i1 mods tops v2) (FILTER (λ(n,v). n ∉ FDOM tops) (env_to_i1 mods tops env'')))` by cheat

                        res_tac

metis_tac []

     >- cheat)
     *)
 >- cheat
 >- cheat
 >- cheat
 >- metis_tac []
 >- metis_tac []
 >- (fs [do_log_def] >>
     every_case_tac >>
     fs [v_to_i1_def, exp_to_i1_def] >>
     rw [do_if_i1_def]
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool T)` >>
         rw [] >>
         metis_tac [])
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool F)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac [])
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool T)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac [])
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool F)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac []))
 >- (cases_on `op` >> 
     rw [])
 >- (cases_on `op` >> 
     rw [])
 >- (fs [do_if_def, do_if_i1_def] >>
     every_case_tac >>
     rw [] >>
     disj1_tac
     >- (qexists_tac `Litv_i1 (Bool F)` >>
         fs [v_to_i1_def, exp_to_i1_def] >>
         metis_tac [])
     >- (qexists_tac `Litv_i1 (Bool T)` >>
         fs [v_to_i1_def, exp_to_i1_def] >>
         metis_tac []))
 >- (fs [v_to_i1_def] >>
     metis_tac []) 
 >- cheat
 >- (rw [markerTheory.Abbrev_def] >>
     cheat)
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- cheat
 >- cheat);

val _ = export_theory ();
