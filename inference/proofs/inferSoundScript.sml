open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory infer_tTheory;
open astPropsTheory;
open inferPropsTheory;
open typeSysPropsTheory;
open infer_eCompleteTheory;
open type_eDetermTheory;
open infer_eSoundTheory;

local open typeSoundInvariantsTheory in
val tenvT_ok_def = tenvT_ok_def;
val flat_tenvT_ok_def = flat_tenvT_ok_def;
end

val _ = new_theory "inferSound";

val letrec_lemma2 = Q.prove (
`!funs_ts l l' s s'.
 (!t1 t2. t_walkstar s t1 = t_walkstar s t2 ⇒  t_walkstar s' t1 = t_walkstar s' t2) ∧
 (LENGTH funs_ts = LENGTH l) ∧
 (LENGTH funs_ts = LENGTH l') ∧
 MAP (λn. t_walkstar s (Infer_Tuvar n)) l' = MAP (t_walkstar s) funs_ts
 ⇒
 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar s' (Infer_Tuvar n))) l')
  =
  MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s' t))) l funs_ts)`,
induct_on `funs_ts` >>
cases_on `l` >>
cases_on `l'` >>
rw [] >>
fs [] >|
[PairCases_on `h` >>
     rw [] >>
     metis_tac [],
 metis_tac []]);

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 rw [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

val generalise_none = Q.prove (
`(!t s' t' x.
   check_t 0 x t ∧
   generalise 0 0 FEMPTY t = (0, s', t')
   ⇒
   s' = FEMPTY ∧
   check_t 0 {} t) ∧
 (!ts s' ts' x.
   EVERY (check_t 0 x) ts ∧
   generalise_list 0 0 FEMPTY ts = (0, s', ts')
   ⇒
   s' = FEMPTY ∧
   EVERY (check_t 0 {}) ts)`,
 ho_match_mp_tac infer_t_induction >>
 rw [generalise_def, check_t_def, LET_THM, LAMBDA_PROD]
 >- (`?n s' t'. generalise_list 0 0 FEMPTY ts = (n,s',t')` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [])
 >- (`?n s' t'. generalise_list 0 0 FEMPTY ts = (n,s',t')` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac []) >>
 `?n' s'' t''. generalise 0 0 FEMPTY t = (n',s'',t'')` by metis_tac [pair_CASES] >>
 fs [] >>
 `?n s' t'. generalise_list 0 n' s'' ts = (n,s',t')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 metis_tac []);

val check_s_more5 = Q.prove (
`!s uvs tvs uvs'. check_s tvs uvs s ∧ uvs ⊆ uvs' ⇒ check_s tvs uvs' s`,
 rw [check_s_def] >>
 metis_tac [check_t_more5]);

val infer_d_sound = Q.prove (
`!mn decls tenvT menv cenv env d st1 st2 decls' tenvT' cenv' env' tenv.
  infer_d mn decls tenvT menv cenv env d st1 = (Success (decls',tenvT',cenv',env'), st2) ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  type_d T mn (convert_decls decls) tenvT (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) d (convert_decls decls') tenvT' cenv' (convert_env2 env')`,
 cases_on `d` >>
 rpt gen_tac >>
 strip_tac >>
 `?mdecls tdecls edecls. decls = (mdecls,tdecls,edecls)` by metis_tac [pair_CASES] >>
 fs [infer_d_def, success_eqns, type_d_cases] >>
 fs []
 >- (`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     fs [success_eqns] >>
     `?tvs s ts. generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env'')) = (tvs,s,ts)`
                 by (cases_on `generalise_list st''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP SND env''))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [METIS_PROVE [] ``!x. (x = 0:num ∨ is_value e) = (x<>0 ⇒ is_value e)``] >>
     rw [] >>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv' = bind_tvar tvs (bind_var_list2 (convert_env2 env) Empty)` >>
     fs [init_state_def] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     `init_infer_state.next_uvar = 0` 
                 by (fs [init_infer_state_def] >> rw []) >>
     `check_t 0 (count st'''.next_uvar) t1` by metis_tac [infer_e_check_t, COUNT_ZERO] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     fs [] >>
     rw [] >>
     fs [] >>
     imp_res_tac infer_p_check_t >>
     fs [every_shim] >>
     `t_wfs s` by metis_tac [t_unify_wfs, infer_p_wfs] >>
     `?last_sub ec1. sub_completion tvs st''''.next_uvar s ec1 last_sub ∧
                     t_wfs last_sub ∧
                     (ts = MAP (t_walkstar last_sub) (MAP SND env''))`
                          by metis_tac [arithmeticTheory.ADD_0, generalise_complete, infer_d_check_s_helper1] >>
     `num_tvs tenv' = tvs` 
                  by (Q.UNABBREV_TAC `tenv'` >>
                      fs [bind_tvar_def] >> 
                      full_case_tac >>
                      rw [num_tvs_def, num_tvs_bvl2]) >>
     imp_res_tac sub_completion_unify2 >>
     `?ec2. sub_completion (num_tvs tenv') st'''.next_uvar st'''.subst (ec2++((t1,t)::ec1)) last_sub` 
               by metis_tac [sub_completion_infer_p] >>
     rw [] >>
     `(init_infer_state:(num |-> infer_t) infer_st).subst = FEMPTY` by fs [init_infer_state_def] >>
     `tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)` by metis_tac [tenv_inv_convert_env2] >>
     `tenv_inv FEMPTY env tenv'` by metis_tac [tenv_inv_extend_tvar_empty_subst] >>
     `tenv_inv last_sub env tenv'` by metis_tac [tenv_inv_empty_to] >>
     `type_e (convert_menv menv) cenv tenv' e (convert_t (t_walkstar last_sub t1))`
             by metis_tac [infer_e_sound, COUNT_ZERO] >>
     `type_p (num_tvs tenv') cenv p (convert_t (t_walkstar last_sub t)) (convert_env last_sub env'')`
             by metis_tac [infer_p_sound] >>
     `t_walkstar last_sub t = t_walkstar last_sub t1`
             by (imp_res_tac infer_e_wfs >>
                 imp_res_tac infer_p_wfs >>
                 imp_res_tac t_unify_wfs >>
                 metis_tac [sub_completion_apply, t_unify_apply]) >>
     cases_on `¬(is_value e)` >>
     rw [] >|
     [qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env'')` >>
          `num_tvs tenv' = 0` by metis_tac [] >>
          rw [] >|
          [rw [empty_decls_def, convert_decls_def],
           rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
               REPEAT (pop_assum (fn _ => all_tac)) >> 
               induct_on `env''` >>
               rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
               (PairCases_on `h` >>
                    rw []) >>
               rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem],
           match_mp_tac infer_e_type_pe_determ >>
               MAP_EVERY qexists_tac [`env`, `st'''`, `st''''`, `t1`] >>
               rw [check_cenv_tenvC_ok]
               >- rw [num_tvs_bvl2, num_tvs_def]
               >- metis_tac [tenv_invC_convert_env2] >>
               fs [] >>
               imp_res_tac generalise_none >>
               fs [EVERY_MAP, LAMBDA_PROD] >>
               first_x_assum match_mp_tac >>
               fs [EVERY_MEM] >>
               qexists_tac `count st''''.next_uvar` >>
               rw [] >>
               PairCases_on `e'` >>
               rw [] >>
               res_tac >>
               fs [] >>
               match_mp_tac t_walkstar_check >>
               `check_t 0 (count st''''.next_uvar ∪ FDOM s) e'1 ∧ 
                check_t 0 (count st''''.next_uvar ∪ FDOM s) t`
                        by (rw [] >>
                            match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] (CONJUNCT1 check_t_more5)) >> 
                            rw [] >>
                            qexists_tac `count st''''.next_uvar` >>
                            simp []) >>
               `check_t 0 (count st''''.next_uvar ∪ FDOM s) t1` 
                        by (rw [] >>
                            match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] (CONJUNCT1 check_t_more5)) >> 
                            rw [] >>
                            qexists_tac `count st'''.next_uvar` >>
                            imp_res_tac infer_p_next_uvar_mono >>
                            simp [count_def, SUBSET_DEF]) >>
               rw [] >>
               match_mp_tac t_unify_check_s >>
               MAP_EVERY qexists_tac [`st''''.subst`, `t1`, `t`] >>
               rw []
               >- metis_tac [infer_p_wfs] >>
               match_mp_tac check_s_more5 >> 
               qexists_tac `count st''''.next_uvar` >>
               rw [SUBSET_DEF] >>
               match_mp_tac (CONJUNCT1 infer_p_check_s) >>
               MAP_EVERY qexists_tac [`cenv`, `p`, `st'''`] >>
               rw [] >>
               match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`menv`, `cenv`, `env`, `e`, `init_infer_state`, `t1`] >>
               rw [check_s_def],
           imp_res_tac infer_p_bindings >>
               fs [],
           metis_tac [],
           fs [bind_tvar_def]],
      qexists_tac `num_tvs tenv'` >>
          qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env'')` >>
          rw [] >|
          [rw [empty_decls_def, convert_decls_def],
           rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
               REPEAT (pop_assum (fn _ => all_tac)) >> 
               induct_on `env''` >>
               rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
               (PairCases_on `h` >>
                    rw []) >>
               rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem],
           imp_res_tac infer_p_bindings >>
               fs []]])
 >- (fs [success_eqns] >>
     `?tvs s ts. generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l)))) = (tvs,s,ts)`
                 by (cases_on `generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l))))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [] >>
     rw [] >>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv' = bind_tvar tvs (bind_var_list2 (convert_env2 env) Empty)` >>
     fs [init_state_def] >>
     rw [] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     `init_infer_state.next_uvar = 0` 
                 by (fs [init_infer_state_def] >> rw []) >>
     fs [] >>
     rw [] >>
     fs [] >>
     `EVERY (\t. check_t 0 (count st''''.next_uvar) t) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l)))`
                 by (rw [EVERY_MAP, check_t_def] >>
                     rw [EVERY_MEM, MEM_COUNT_LIST] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     decide_tac) >>
     `t_wfs st'''''.subst` by metis_tac [pure_add_constraints_wfs, infer_e_wfs, infer_st_rewrs] >>
     `?last_sub ec1. sub_completion tvs st''''.next_uvar st'''''.subst ec1 last_sub ∧
                     t_wfs last_sub ∧
                     (ts = MAP (t_walkstar last_sub) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`
                          by metis_tac [arithmeticTheory.ADD_0, generalise_complete, infer_d_check_s_helper2, LENGTH_COUNT_LIST] >>
     imp_res_tac sub_completion_add_constraints >>
     rw [] >>
     `(init_infer_state:(num |-> infer_t) infer_st).subst = FEMPTY` by fs [init_infer_state_def] >>
     `tenv_inv FEMPTY env (bind_var_list2 (convert_env2 env) Empty)` by metis_tac [tenv_inv_convert_env2] >>
     `tenv_inv FEMPTY env tenv'` by metis_tac [tenv_inv_extend_tvar_empty_subst] >>
     `tenv_inv last_sub env tenv'` by metis_tac [tenv_inv_empty_to] >>
     Q.ABBREV_TAC `tenv'' = 
                   bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l)))) 
                                 tenv'` >> 
     Q.ABBREV_TAC `env'' = MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l (MAP (λn.  Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l))) ++ env` >>
     `tenv_inv last_sub env'' tenv''` by metis_tac [tenv_inv_letrec_merge] >>
     fs [] >>
     `check_env (count (LENGTH l)) env''` 
                 by (Q.UNABBREV_TAC `env''` >>
                     rw [MAP2_MAP, check_env_merge, check_env_letrec] >>
                     metis_tac [check_env_more, COUNT_ZERO, DECIDE ``0<=x:num``]) >> 
     `num_tvs tenv'' = tvs`
                 by  (Q.UNABBREV_TAC `tenv''` >>
                      rw [num_tvs_bind_var_list] >>
                      Q.UNABBREV_TAC `tenv'` >>
                      fs [bind_tvar_rewrites, num_tvs_bvl2, num_tvs_def]) >>
     `type_funs (convert_menv menv) cenv tenv'' l (MAP2 (λ(x,y,z) t. (x,(convert_t o t_walkstar last_sub) t)) l funs_ts)`
             by (match_mp_tac (List.nth (CONJUNCTS infer_e_sound, 3)) >>
                 rw [] >>
                 qexists_tac `env''` >>
                 qexists_tac `init_infer_state with next_uvar := LENGTH l` >>
                 rw [] >>
                 metis_tac [num_tvs_bind_var_list]) >>
     `t_wfs (init_infer_state with next_uvar := LENGTH l).subst` by rw [] >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     qexists_tac `(MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l))))` >>
     qexists_tac `tvs` >>
     rw [] >|
     [rw [empty_decls_def, convert_decls_def],
      rw [LENGTH_MAP, LENGTH_COUNT_LIST, MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
          REPEAT (pop_assum (fn _ => all_tac)) >> 
          induct_on `l` >>
          rw [COUNT_LIST_def, tenv_add_tvs_def, convert_env_def, convert_env2_def] >-
          (PairCases_on `h` >> rw []) >>
          rw [MAP_MAP_o, MAP2_MAP, ZIP_MAP, LENGTH_COUNT_LIST, combinTheory.o_DEF, remove_pair_lem],
      `LENGTH l = LENGTH funs_ts` by fs [LENGTH_COUNT_LIST] >>
          fs [MAP_ZIP, LENGTH_COUNT_LIST, MAP_MAP_o, combinTheory.o_DEF] >>
          metis_tac [letrec_lemma2, LENGTH_COUNT_LIST, LENGTH_MAP, 
                     pure_add_constraints_wfs, sub_completion_apply]])
 >- (rw [convert_decls_def, convert_env2_def, EVERY_MAP, DISJOINT_DEF, EXTENSION] >>
     fs [EVERY_MAP, EVERY_MEM] >>
     Q.LIST_EXISTS_TAC [`set mdecls`, `set edecls`, `set tdecls`] >>
     rw [MEM_MAP] >>
     metis_tac [])
 >- rw [convert_decls_def, convert_env2_def, empty_decls_def]
 >- (rw [convert_decls_def, convert_env2_def]>>metis_tac[MAP_ID]));

val infer_ds_sound = Q.prove (
`!mn decls tenvT menv cenv env ds st1 decls' tenvT' cenv' env' st2 tenv.
  infer_ds mn decls tenvT menv cenv env ds st1 = (Success (decls',tenvT',cenv',env'), st2) ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env
  ⇒
  type_ds T mn (convert_decls decls) tenvT (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) ds (convert_decls decls') tenvT' cenv' (convert_env2 env')`,
 induct_on `ds` >>
 rpt gen_tac >>
 `?mdecls tdecls edecls. decls = (mdecls,tdecls,edecls)` by metis_tac [pair_CASES] >>
 rw [infer_ds_def, success_eqns]
 >- rw [empty_decls_def,convert_decls_def, convert_env2_def, Once type_ds_cases] >>
 `?decls'' cenv'' tenvT'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
 fs [success_eqns] >>
 `?decls''' tenvT''' cenv''' env'''. v'' = (decls''',tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
 fs [success_eqns] >>
 rw [Once type_ds_cases] >>
 fs [init_infer_state_def] >>
 imp_res_tac infer_d_check >>
 `check_cenv (merge_alist_mod_env ([],cenv'') cenv)` 
          by (PairCases_on `cenv` >>
              fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def]) >>
 `tenvT_ok (merge_mod_env (FEMPTY,tenvT'') tenvT)` 
        by (match_mp_tac tenvT_ok_merge >>
            fs [tenvT_ok_def, FEVERY_FEMPTY]) >>
 `check_env {} (env'' ++ env)` 
                 by fs [check_env_def, init_infer_state_def] >>
 imp_res_tac infer_d_sound >>
 res_tac >>
 fs [convert_env2_def, bvl2_append] >>
 metis_tac [convert_append_decls]);

val db_subst_infer_subst_swap2 = Q.prove (
`(!t s tvs uvar n.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
    (convert_t t))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  EVERY (\t. check_t tvs {} t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))) o
       convert_t)
      ts))`,
ho_match_mp_tac infer_t_induction >>
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST]);

val check_weakE_sound = Q.prove (
`!tenv1 tenv2 st st2.
  check_env {} tenv1 ∧
  check_env {} tenv2 ∧
  (check_weakE tenv1 tenv2 st = (Success (), st2))
  ⇒
  weakE (convert_env2 tenv1) (convert_env2 tenv2)`,
ho_match_mp_tac check_weakE_ind >>
rw [convert_env2_def, check_weakE_def, weakE_def, success_eqns, 
    SIMP_RULE (srw_ss()) [] check_env_bind] >>
 cases_on `ALOOKUP tenv1 n` >>
 fs [success_eqns] >>
 `?tvs_impl t_impl. x' = (tvs_impl,t_impl)` by (PairCases_on `x'` >> metis_tac []) >>
 rw [] >>
 fs [success_eqns] >>
 rw [] >>
 `ALOOKUP (MAP (λ(x,y). (x,(λ(tvs,t). (tvs, convert_t t)) y)) tenv1) n = SOME ((λ(tvs,t). (tvs, convert_t t)) (tvs_impl,t_impl))`
         by rw [ALOOKUP_MAP] >>
 fs [remove_pair_lem] >>
 `(λ(x,y). (x,FST y,convert_t (SND y))) = (λ(x,tvs:num,t). (x,tvs,convert_t t))`
                 by (rw [FUN_EQ_THM] >>
                     PairCases_on `y` >>
                     rw []) >>
 rw [] >>
 fs [init_state_def, init_infer_state_def] >>
 rw [] 
 >- (fs [] >>
     `t_wfs FEMPTY` by rw [t_wfs_def] >>
     imp_res_tac t_unify_wfs >>
     imp_res_tac t_unify_apply >>
     imp_res_tac check_env_lookup >>
     `?s'. ALL_DISTINCT (MAP FST s') ∧ (FEMPTY |++ s' = FUN_FMAP (\x. Infer_Tapp [] TC_unit) (count tvs_impl DIFF FDOM s))`
                   by metis_tac [fmap_to_list] >>
     `FINITE (count tvs_impl DIFF FDOM s)` by metis_tac [FINITE_COUNT, FINITE_DIFF] >>
     `t_wfs (s |++ s')`
               by (`t_vR s = t_vR (s |++ s')`
                            by (rw [t_vR_eqn, FUN_EQ_THM] >>
                                cases_on `FLOOKUP (s |++ s') x'` >>
                                fs [flookup_update_list_none, flookup_update_list_some] >>
                                cases_on `FLOOKUP s x'` >>
                                fs [flookup_update_list_none, flookup_update_list_some] >>
                                `FLOOKUP (FEMPTY |++ s') x' = SOME x''` by rw [flookup_update_list_some] >>
                                pop_assum mp_tac >>
                                rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                                rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
                                fs [FLOOKUP_DEF]) >>
                   fs [t_wfs_eqn]) >>
     `check_s tvs_spec (count tvs_impl) s`
                by (match_mp_tac t_unify_check_s >>
                    MAP_EVERY qexists_tac [`FEMPTY`, `t_spec`, 
                                           `(infer_deBruijn_subst (MAP (λn.  Infer_Tuvar n) (COUNT_LIST tvs_impl)) t_impl)`] >>
                    rw [check_s_def, check_t_infer_db_subst2] >>
                    metis_tac [check_t_more, check_t_more2, arithmeticTheory.ADD_0]) >>
     qexists_tac `MAP (\n. convert_t (t_walkstar (s |++ s') (Infer_Tuvar n))) (COUNT_LIST tvs_impl)` >>
     rw [LENGTH_COUNT_LIST, check_t_to_check_freevars, EVERY_MAP]
     >- (rw [EVERY_MEM] >>
         `FDOM (FEMPTY |++ s') = count tvs_impl DIFF FDOM s` by metis_tac [FDOM_FMAP] >>
         `check_t tvs_spec {} (t_walkstar (s |++ s') (Infer_Tuvar n'))`
                     by (rw [check_t_def] >>
                         match_mp_tac t_walkstar_check >>
                         rw [check_t_def, FDOM_FUPDATE_LIST] >|
                         [fs [check_s_def, fdom_fupdate_list2] >>
                              rw [] >>
                              rw [FUPDATE_LIST_APPLY_NOT_MEM] >>
                              `count tvs_impl ⊆ FDOM s ∪ set (MAP FST s')` by rw [SUBSET_DEF] >|
                              [metis_tac [check_t_more5],
                               metis_tac [check_t_more5],
                               `FLOOKUP (s |++ s') uv = SOME ((s |++ s') ' uv)`
                                           by (rw [FLOOKUP_DEF, FDOM_FUPDATE_LIST]) >>
                                   fs [flookup_update_list_some] >|
                                   [imp_res_tac ALOOKUP_MEM >>
                                        fs [MEM_MAP] >>
                                        rw [] >>
                                        PairCases_on `y` >>
                                        imp_res_tac (GSYM mem_to_flookup) >>
                                        fs [] >>
                                        ntac 3 (pop_assum mp_tac) >>
                                        rw [FLOOKUP_FUN_FMAP] >>
                                        rw [check_t_def],
                                    pop_assum mp_tac >>
                                        rw [FLOOKUP_DEF]]],
                          fs [EXTENSION, MEM_COUNT_LIST] >>
                              res_tac >>
                              fs [FDOM_FUPDATE_LIST]]) >>
         rw [check_t_to_check_freevars])
     >- (imp_res_tac t_walkstar_no_vars >>
         fs [] >>
         rw [SIMP_RULE (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] (GSYM db_subst_infer_subst_swap2)] >>
         match_mp_tac (METIS_PROVE [] ``x = y ⇒ f x = f y``) >>
         match_mp_tac (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] no_vars_extend_subst) >>
         rw []
         >- (rw [DISJOINT_DEF, EXTENSION] >>
             metis_tac [])
         >- (imp_res_tac check_t_t_vars  >>
             fs [EXTENSION, SUBSET_DEF])))
 >- metis_tac[]);

val check_flat_weakC_sound = Q.prove (
`!tenvC1 tenvC2.
  check_flat_weakC tenvC1 tenvC2
  ⇒
  flat_weakC tenvC1 tenvC2`,
induct_on `tenvC2` >>
fs [check_flat_weakC_def, flat_weakC_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [] >>
rw [] >>
cases_on `ALOOKUP tenvC1 cn` >>
fs []);

val check_flat_weakT_sound = Q.prove (
`!mn tenvT1 tenvT2.
  check_flat_weakT mn tenvT1 tenvT2
  ⇒
  flat_weakT mn tenvT1 tenvT2`,
 rw [check_flat_weakT_def, flat_weakT_def, success_eqns] >>
 cases_on `FLOOKUP tenvT2 tn` >>
 rw [] >>
 PairCases_on `x` >>
 rw [] >>
 cases_on `FLOOKUP tenvT1 tn` >>
 rw []
 >- (imp_res_tac FEVERY_FLOOKUP >>
     fs [] >>
     pop_assum mp_tac >>
     rw []) >>
 PairCases_on `x` >>
 rw [] >>
 imp_res_tac FEVERY_FLOOKUP >>
 REV_FULL_SIMP_TAC (srw_ss()) []);

val check_freevars_more = Q.prove (
`(!t x fvs1 fvs2.
  check_freevars x fvs1 t ⇒
  check_freevars x (fvs2++fvs1) t ∧
  check_freevars x (fvs1++fvs2) t) ∧
 (!ts x fvs1 fvs2.
  EVERY (check_freevars x fvs1) ts ⇒
  EVERY (check_freevars x (fvs2++fvs1)) ts ∧
  EVERY (check_freevars x (fvs1++fvs2)) ts)`,
Induct >>
rw [check_freevars_def] >>
metis_tac []);

val t_to_freevars_check = Q.prove (
`(!t st fvs st'.
   (t_to_freevars t (st:'a) = (Success fvs, st'))
   ⇒
   check_freevars 0 fvs t) ∧
 (!ts st fvs st'.
   (ts_to_freevars ts (st:'a) = (Success fvs, st'))
   ⇒
   EVERY (check_freevars 0 fvs) ts)`,
Induct >>
rw [t_to_freevars_def, success_eqns, check_freevars_def] >>
rw [] >>
metis_tac [check_freevars_more]);

val check_freevars_nub = Q.prove (
`(!t x fvs.
  check_freevars x fvs t ⇒
  check_freevars x (nub fvs) t) ∧
 (!ts x fvs.
  EVERY (check_freevars x fvs) ts ⇒
  EVERY (check_freevars x (nub fvs)) ts)`,
Induct >>
rw [check_freevars_def] >> metis_tac[]);

val check_specs_sound = Q.prove (
`!mn orig_tenvT mdecls tdecls edecls tenvT cenv env specs st decls' tenvT' cenv' env' st' init_decls.
  (check_specs mn orig_tenvT (mdecls,tdecls,edecls) tenvT cenv env specs st = (Success (decls',tenvT',cenv',env'), st'))
  ⇒
  ?decls'' tenvT'' cenv'' env''.
    type_specs mn orig_tenvT specs (convert_decls decls'') tenvT'' cenv'' (convert_env2 env'') ∧
    (decls' = append_decls decls'' (mdecls,tdecls,edecls)) ∧
    (tenvT' = FUNION tenvT'' tenvT) ∧
    (cenv' = cenv'' ++ cenv) ∧
    (env' = env'' ++ env)`,
 ho_match_mp_tac check_specs_ind >>
 rw [check_specs_def, success_eqns]
 >- (rw [Once type_specs_cases] >>
     qexists_tac `([],[],[])` >>
     fs [empty_decls_def, convert_decls_def, append_decls_def, convert_env2_def])
 >- (rw [Once type_specs_cases] >>
     res_tac >>
     `check_freevars 0 fvs t` by metis_tac [t_to_freevars_check] >>
     `check_freevars 0 (nub fvs) t` by metis_tac [check_freevars_nub] >>
     Q.LIST_EXISTS_TAC [`decls''`, `tenvT'''`, `cenv''`, `env''++[(x,LENGTH (nub fvs),infer_type_subst (ZIP (nub fvs, MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs))))) t)]`] >>
     rw [] >>
     qexists_tac `convert_env2 env''` >>
     rw [] >>
     qexists_tac `nub fvs` >>
     rw [] >>
     fs [LENGTH_MAP, convert_t_subst, convert_env2_def,
         LENGTH_COUNT_LIST,LENGTH_GENLIST] >>
     fs [MAP_MAP_o, combinTheory.o_DEF, convert_t_def] >>
     metis_tac [COUNT_LIST_GENLIST, combinTheory.I_DEF])
 >- (rw [Once type_specs_cases] >>
     rw [convert_decls_def] >>
     res_tac >>
     qexists_tac `append_decls decls'' ([],MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs,[])` >>
     rw [] >>
     PairCases_on `decls''` >>
     fs [append_decls_def, convert_decls_def] >>
     fs [PULL_EXISTS] >>
     qexists_tac `tenvT''''` >>
     rw [] >>
     qexists_tac `(set decls''0,set decls''1,set decls''2)` >>
     rw [union_decls_def, DISJOINT_DEF, EXTENSION, MEM_MAP] >>
     fs [EVERY_MEM, EVERY_MAP, FUNION_ASSOC])
 >- (rw [Once type_specs_cases, PULL_EXISTS] >>
     res_tac >>
     rw [FUNION_FUPDATE_2] >>
     qexists_tac `decls''` >>
     qexists_tac `tenvT'''` >>
     rw [FUNION_FUPDATE_1])
 >- (rw [Once type_specs_cases] >>
     rw [convert_decls_def] >>
     res_tac >>
     qexists_tac `append_decls decls'' ([],[],[mk_id mn cn])` >>
     rw [PULL_EXISTS] >>
     qexists_tac `tenvT'''` >>
     PairCases_on `decls''` >>
     rw [convert_decls_def, append_decls_def] >>
     qexists_tac `convert_decls (decls''0,decls''1,decls''2)` >>
     fs [convert_decls_def, union_decls_def, DISJOINT_DEF, EXTENSION, MEM_MAP] >>
     metis_tac [])
 >- (rw [Once type_specs_cases, convert_decls_def] >>
     res_tac >>
     rw [PULL_EXISTS] >>
     qexists_tac `append_decls decls'' ([],[mk_id mn tn],[])` >>
     PairCases_on `decls''` >>
     rw [append_decls_def] >>
     qexists_tac `tenvT'''` >>
     qexists_tac `convert_decls (decls''0,decls''1,decls''2)` >>
     fs [convert_decls_def, union_decls_def, DISJOINT_DEF, EXTENSION, MEM_MAP] >>
     rw [FUNION_FUPDATE_1, FUNION_FUPDATE_2]));

val infer_sound_invariant_def = Define `
infer_sound_invariant tenvT menv cenv env ⇔
  tenvT_ok tenvT ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env`;

val infer_top_sound = Q.store_thm ("infer_top_sound",
`!decls tenvT menv cenv env top st1 decls' tenvT' menv' cenv' env' st2.
  (infer_top decls tenvT menv cenv env top st1 = (Success (decls',tenvT',menv', cenv', env'), st2)) ∧
  infer_sound_invariant tenvT menv cenv env
  ⇒
  type_top T (convert_decls decls) tenvT (convert_menv menv) cenv 
           (bind_var_list2 (convert_env2 env) Empty) 
           top 
           (convert_decls decls') tenvT' (convert_menv menv') cenv' (convert_env2 env') ∧
  infer_sound_invariant (merge_mod_env tenvT' tenvT) (FUNION menv' menv) (merge_alist_mod_env cenv' cenv) (env'++env)`,
 cases_on `top` >>
 rpt gen_tac >>
 `?mdecls tdecls edecls. decls = (mdecls,tdecls,edecls)` by metis_tac [pair_CASES] >>
 fs [infer_top_def, success_eqns, type_top_cases, infer_sound_invariant_def] >>
 strip_tac >>
 `∃decls'' tenvT'' cenv'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
 fs [success_eqns]
 >- (`∃mdecls''' tdecls''' edecls''' tenvT''' cenv''' env'''. v'' = ((mdecls''',tdecls''',edecls'''),tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
     `flat_tenvT_ok (FEMPTY:flat_tenvT) ∧ check_flat_cenv [] ∧ check_env {} ([]:(tvarN, num # infer_t) alist)` 
                by rw [flat_tenvT_ok_def, check_flat_cenv_def, check_env_def,
                       check_cenv_def, FEVERY_FEMPTY] >>
     `flat_tenvT_ok tenvT'' ∧ check_flat_cenv cenv'' ∧ check_env ∅ env''` by metis_tac [infer_ds_check] >>
     rw []
     >- (fs [success_eqns] >>
         rw [convert_decls_def] >>
         imp_res_tac infer_ds_sound >>
         cases_on `o'` >>
         fs [success_eqns, check_signature_def, check_signature_cases]
         >- (fs [convert_menv_def] >>
             rw [] >>
             fs [convert_env2_def, convert_decls_def] >>
             metis_tac [convert_env2_def, INSERT_SING_UNION])
         >- (PairCases_on `v'` >>
             fs [success_eqns] >>
             rw [] >>
             `check_env {} env''' ∧ flat_tenvT_ok tenvT'''` by metis_tac [check_specs_check] >>
             imp_res_tac check_specs_sound >>
             fs [] >>
             rw [] >>
             Q.LIST_EXISTS_TAC [`tenvT''`, `cenv''`, `convert_env2 env''`,
                                `convert_env2 env'''`, `convert_decls decls''`, 
                                `set mdecls'''`, `tenvT'''`] >>
             rw []
             >- metis_tac [INSERT_SING_UNION]
             >- rw [convert_menv_def, convert_env2_def]
             >- rw [convert_env2_def]
             >- fs [convert_decls_def]
             >- metis_tac [check_weakE_sound, convert_env2_def]
             >- metis_tac [check_flat_weakC_sound]
             >- (PairCases_on `decls''` >>
                 PairCases_on `decls'''` >>
                 fs [convert_decls_def, weak_decls_def, check_weak_decls_def, append_decls_def,
                     list_subset_def, SUBSET_DEF, EVERY_MEM] >>
                 rw [] >>
                 metis_tac [])
             >- metis_tac [check_flat_weakT_sound]
             >- (PairCases_on `decls'''` >>
                 fs [convert_decls_def, append_decls_def])))
     >- (match_mp_tac tenvT_ok_merge >>
         fs [success_eqns, check_signature_def] >>
         rw [tenvT_ok_def, FEVERY_FUPDATE, FEVERY_FEMPTY] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw [] >>
         PairCases_on `v'` >>
         fs [success_eqns] >>
         rw [] >>
         metis_tac [check_specs_check])
     >- (fs [success_eqns, check_menv_def] >>
         rw [FEVERY_FUPDATE, FEVERY_FEMPTY] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw []
         >- (fs [check_env_def] >>
             match_mp_tac fevery_funion >>
             rw [FEVERY_FUPDATE, FEVERY_FEMPTY])
         >- (PairCases_on `v'` >>
             fs [success_eqns] >>
             rw [] >>
             match_mp_tac fevery_funion >>
             rw [FEVERY_FUPDATE, FEVERY_FEMPTY] >>
             `check_env {} env'''` by metis_tac [check_specs_check] >>
             fs [check_env_def, check_flat_cenv_def]))
     >- (fs [success_eqns, check_menv_def] >>
         rw [] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw []
         >- (fs [check_cenv_def] >>
             PairCases_on `cenv` >>
             fs [merge_alist_mod_env_def, check_cenv_def])
         >- (PairCases_on `v'` >>
             fs [success_eqns] >>
             rw [] >>
             `check_flat_cenv cenv'''` by metis_tac [check_specs_check] >>
             fs [check_env_def, check_flat_cenv_def] >>
             PairCases_on `cenv` >>
             fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def]))
     >- (fs [success_eqns, check_menv_def] >>
         rw [] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw [])) >>
 rw []
 >- rw [convert_menv_def]
 >- metis_tac [infer_d_sound]
 >- (match_mp_tac tenvT_ok_merge >>
     rw [tenvT_ok_def] >>
     imp_res_tac infer_d_check >>
     fs [FEVERY_FEMPTY])
 >- (imp_res_tac infer_d_check >>
     PairCases_on `cenv` >>
     fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def])
 >- (imp_res_tac infer_d_check >>
     fs [check_env_def]));

val infer_prog_sound = Q.store_thm ("infer_prog_sound",
`!decls tenvT menv cenv env prog st1 decls' tenvT' menv' cenv' env' st2.
  (infer_prog decls tenvT menv cenv env prog st1 = (Success (decls',tenvT',menv',cenv', env'), st2)) ∧
  infer_sound_invariant tenvT menv cenv env
  ⇒
  type_prog T (convert_decls decls) tenvT (convert_menv menv) cenv (bind_var_list2 (convert_env2 env) Empty) prog (convert_decls decls') tenvT' (convert_menv menv') cenv' (convert_env2 env') ∧
  infer_sound_invariant (merge_mod_env tenvT' tenvT) (FUNION menv' menv) (merge_alist_mod_env cenv' cenv) (env' ++ env)`,
 induct_on `prog` >>
 rw [infer_prog_def, success_eqns]
 >- rw [Once type_prog_cases, empty_decls_def, convert_decls_def, convert_menv_def, convert_env2_def]
 >- (PairCases_on `cenv` >>
     PairCases_on `tenvT` >>
     rw [merge_mod_env_def, merge_alist_mod_env_def])
 >- (rw [Once type_prog_cases] >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     imp_res_tac infer_top_sound >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT', menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     rw [] >>
     res_tac >>
     Q.LIST_EXISTS_TAC [`tenvT''`, `convert_menv menv''`, `cenv''`, `convert_env2 env''`, `tenvT'''`,`convert_menv menv'''`, `cenv'''`, `convert_env2 env'''`, `convert_decls decls''`, `convert_decls decls'''`] >>
     fs [append_decls_def, convert_decls_def, convert_menv_def, convert_env2_def] >>
     PairCases_on `decls'''` >>
     PairCases_on `decls''` >>
     PairCases_on `decls` >>
     fs [convert_decls_def, union_decls_def, append_decls_def, o_f_FUNION] >>
     metis_tac [bvl2_append])
 >- (`?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     imp_res_tac infer_top_sound >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     rw [] >>
     res_tac >>
     metis_tac [FUNION_ASSOC, APPEND_ASSOC, merge_mod_env_assoc, 
                evalPropsTheory.merge_alist_mod_env_assoc]));

val _ = export_theory ();
