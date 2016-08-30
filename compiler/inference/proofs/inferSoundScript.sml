open preamble;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory infer_tTheory;
open astPropsTheory;
open inferPropsTheory;
open typeSysPropsTheory;
open infer_eSoundTheory;
open envRelTheory;
open type_eDetermTheory;
open infer_eCompleteTheory

val _ = new_theory "inferSound";

val sym_sub_tac = SUBST_ALL_TAC o SYM

(*
val lookup_tenv_NONE = prove(``
  ∀ls n.
  (lookup_tenv_val x n ls = NONE ⇒
  ∀m. lookup_tenv_val x m ls = NONE)``,
  Induct>>fs[lookup_tenv_val_def]>>rw[]>>
  metis_tac[])

val lookup_tenv_SOME = prove(``
  ∀ls n tvs t.
  (lookup_tenv_val x n ls = SOME(tvs,t) ⇒
  ∀m. ∃tvs' t'. lookup_tenv_val x m ls = SOME(tvs',t'))``,
  Induct>>fs[lookup_tenv_val_def]>>rw[]>>
  metis_tac[])

val tenv_invC_extend_tvar_empty_subst = Q.store_thm ("tenv_invC_extend_tvar_empty_subst",
`!env tvs tenv.
  tenv_val_ok tenv ∧
  num_tvs tenv = 0 ∧
  tenv_invC FEMPTY env tenv ⇒ tenv_invC FEMPTY env (bind_tvar tvs tenv)`,
  rw[]>>
  fs [tenv_invC_def,lookup_tenv_val_def,bind_tvar_def,tenv_val_ok_def] >>
  Cases_on`tvs=0`>>fs[lookup_tenv_val_def]
  >-
    metis_tac[]
  >>
  rw[]>>
  imp_res_tac lookup_tenv_SOME>>
  pop_assum (qspec_then`0` assume_tac)>>fs[]>>
  imp_res_tac lookup_tenv_val_inc_tvs>>
  metis_tac[])
  *)

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

val deBruijn_subst_convert = prove(``
  (∀t.
  check_t n {} t ⇒
  deBruijn_subst 0 (MAP convert_t subst) (convert_t t) =
  convert_t (infer_deBruijn_subst subst t) ) ∧
  (∀ts.
  EVERY (check_t n {}) ts ⇒
  MAP ((deBruijn_subst 0 (MAP convert_t subst)) o convert_t) ts
  =
  MAP (convert_t o (infer_deBruijn_subst subst)) ts)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def]>>
  fs[convert_t_def,deBruijn_subst_def,infer_deBruijn_subst_def]
  >-
    (IF_CASES_TAC>>fs[EL_MAP,convert_t_def])
  >>
    fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f]);

val ienv_to_tenv_def = Define `
  ienv_to_tenv ienv =
    <| v := nsMap (\(tvs, t). (tvs, convert_t t)) ienv.inf_v;
       c := ienv.inf_c;
       t := ienv.inf_t |>`;

val infer_d_sound = Q.store_thm ("infer_d_sound",
`!mn decls tenv ienv d st1 st2 decls' ienv'.
  infer_d mn decls ienv d st1 = (Success (decls',ienv'), st2) ∧
  env_rel tenv ienv
  ⇒
  type_d T mn (convert_decls decls) tenv d (convert_decls decls') (ienv_to_tenv ienv')`,

 fs[env_rel_def]>>
 cases_on `d` >>
 rpt gen_tac >>
 strip_tac >>
 fs [infer_d_def, success_eqns, type_d_cases] >>
 fs []
 >- (

   fs [init_state_def]
   >> rw []
   >> rename1 `infer_e _ _ _ = (Success t1, st1)`
   >> rename1 `infer_p _ _ _ = (Success v, st1')`
   >> `?t bindings. v = (t,bindings)` by metis_tac [pair_CASES]
   >> fs [success_eqns]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def]
   >> `init_infer_state.next_uvar = 0` by (fs [init_infer_state_def] >> rw [])
   >> drule (CONJUNCT1 infer_e_wfs)
   >> rw []
   >> drule (CONJUNCT1 infer_p_wfs)
   >> disch_then drule
   >> rw []
   >> drule t_unify_wfs
   >> disch_then drule
   >> rw []
   >> drule (CONJUNCT1 infer_e_check_t)
   >> impl_tac
   >- fs [ienv_ok_def]
   >> rw []
   >> drule (CONJUNCT1 infer_e_check_s)
   >> simp []
   >> rename1 `generalise_list _ _ _ _ = (tvs, s2, ts)`
   >> disch_then (qspec_then `0` mp_tac)
   >> impl_tac
   >- simp [check_s_def, init_infer_state_def]
   >> rw []
   >> drule (CONJUNCT1 infer_p_check_t)
   >> rw []
   >> drule (CONJUNCT1 infer_p_check_s)
   >> disch_then (qspec_then `0` mp_tac)
   >> impl_tac
   >- fs [ienv_ok_def]
   >> rw []
   >> drule t_unify_check_s
   >> simp []
   >> disch_then drule
   >> simp []
   >> impl_tac
   >- metis_tac [infer_p_next_uvar_mono, check_t_more4]
   >> rw []
   >> `?ec1 last_sub.
          ts = MAP (t_walkstar last_sub) (MAP SND bindings) ∧
          t_wfs last_sub ∧
          sub_completion tvs st1'.next_uvar s ec1 last_sub`
     by (
       `tvs = tvs +0 ` by DECIDE_TAC>>pop_assum SUBST1_TAC>>
       match_mp_tac generalise_complete>>fs[]>>
       fs [LAMBDA_PROD, EVERY_MAP])
   >> drule sub_completion_unify2
   >> disch_then drule
   >> rw []
   >> drule (CONJUNCT1 sub_completion_infer_p)
   >> disch_then drule
   >> rw []
   >> `env_rel_sound FEMPTY ienv tenv (bind_tvar tvs Empty)`
     by (
      `t_wfs FEMPTY` by rw [t_wfs_def]
      >> metis_tac [env_rel_sound_extend_tvs])
   >> drule env_rel_e_sound_empty_to
   >> disch_then drule
   >> disch_then drule
   >> rw []
   >> drule (CONJUNCT1 infer_e_sound)
   >> simp []
   >> disch_then drule
   >> simp [num_tvs_def]
   >> disch_then drule
   >> drule (CONJUNCT1 infer_p_sound)
   >> simp []
   >> disch_then (qspecl_then [`tenv`, `tvs`, `(t1,t)::ec1`, `last_sub`] mp_tac)
   >> simp [num_tvs_def]
   >> impl_tac
   >- fs [typeSoundInvariantsTheory.tenv_ok_def, env_rel_sound_def]
   >> rw []
   >> `t_walkstar last_sub t = t_walkstar last_sub t1`
     by (
       imp_res_tac infer_e_wfs >>
       imp_res_tac infer_p_wfs >>
       imp_res_tac t_unify_wfs >>
       metis_tac [sub_completion_apply, t_unify_apply])
   >> Cases_on `is_value e`
   >> fs [success_eqns, empty_decls_def, empty_inf_decls_def]
   >> rw [convert_decls_def, ienv_to_tenv_def]

   >- (
     qexists_tac `tvs`
     >> qexists_tac `convert_t (t_walkstar last_sub t)`
     >> qexists_tac `convert_env last_sub bindings`
     >> rw []
     >- (
       simp [ZIP_MAP, tenv_add_tvs_def]
       >> simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, convert_env_def])
     >- (
       imp_res_tac infer_p_bindings
       >> fs [])
     >- cheat)
   >- (
     qexists_tac `convert_t (t_walkstar last_sub t)`
     >> qexists_tac `convert_env last_sub bindings`
     >> rw []
     >- (
       simp [ZIP_MAP, tenv_add_tvs_def]
       >> simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, convert_env_def])
     >- cheat
     >- (
       imp_res_tac infer_p_bindings
       >> fs [])
     >- fs [bind_tvar_def]))

   >> disch_then drule

     fs [METIS_PROVE [] ``!x. (x = 0:num ∨ is_value e) = (x<>0 ⇒ is_value e)``] >>
     rw [] >>rfs[]>>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv_v' = bind_tvar tvs (bind_var_list2 tenv_v Empty)` >>
     fs [init_state_def] >>
     `check_t 0 (count st'''.next_uvar) t1` by metis_tac [ienv_ok_def, infer_e_check_t, COUNT_ZERO] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     fs [] >>
     rw [] >>
     fs [] >>
     imp_res_tac infer_p_check_t >>
     fs [every_shim] >>
     `t_wfs s` by metis_tac [t_unify_wfs, infer_p_wfs] >>
     `?ec1 last_sub. (ts = MAP (t_walkstar last_sub) (MAP SND env)) ∧
                     t_wfs last_sub ∧
                     sub_completion tvs st''''.next_uvar s ec1 last_sub`
        by
        (`tvs = tvs +0 ` by DECIDE_TAC>>pop_assum SUBST1_TAC>>
        match_mp_tac generalise_complete>>fs[]>>
        cheat
        (*metis_tac[infer_d_check_s_helper1]*))>>
     `num_tvs tenv_v' = tvs`
                  by (Q.UNABBREV_TAC `tenv_v'` >>
                      fs [bind_tvar_def] >>
                      rw [num_tvs_def]) >>
     imp_res_tac sub_completion_unify2 >>
     `?ec2. sub_completion (num_tvs tenv_v') st'''.next_uvar st'''.subst (ec2++((t1,t)::ec1)) last_sub`
               by metis_tac [sub_completion_infer_p] >>
     rw [] >>
     `(init_infer_state:(num |-> infer_t) infer_st).subst = FEMPTY` by fs [init_infer_state_def] >>
     `tenv_inv FEMPTY ienv.inf_v (bind_var_list2 tenv_v Empty)` by metis_tac [tenv_alpha_def] >>
     `tenv_inv FEMPTY ienv.inf_v tenv_v'` by (fs[Abbr`tenv_v'`]>>metis_tac [tenv_inv_extend_tvar_empty_subst]) >>
     `tenv_inv last_sub ienv.inf_v tenv_v'` by metis_tac [tenv_inv_empty_to] >>
     `type_e (tenv with v := tenv_v') e (convert_t (t_walkstar last_sub t1))`
             by
        (match_mp_tac (hd (CONJUNCTS infer_e_sound))>>fs[Abbr`tenv_v'`]>>
        metis_tac[COUNT_ZERO,menv_alpha_convert])>>
     `type_p (num_tvs tenv_v') tenv p (convert_t (t_walkstar last_sub t)) (convert_env last_sub env)`
             by
        (match_mp_tac (hd (CONJUNCTS infer_p_sound))>>fs[Abbr`tenv_v'`]>>
        metis_tac[])>>
     `t_walkstar last_sub t = t_walkstar last_sub t1`
             by (imp_res_tac infer_e_wfs >>
                 imp_res_tac infer_p_wfs >>
                 imp_res_tac t_unify_wfs >>
                 metis_tac [sub_completion_apply, t_unify_apply]) >>
     cases_on `¬(is_value e)` >>
     rw []
     >-
     (qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env)` >>
          `num_tvs tenv_v' = 0` by metis_tac [] >>
          rw []
          >- rw [empty_decls_def, convert_decls_def,empty_inf_decls_def]
          >- (rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
              REPEAT (pop_assum (fn _ => all_tac)) >>
              induct_on `env` >>
              rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
                 (PairCases_on `h` >>
                      rw []) >>
              rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem])
           >- (match_mp_tac infer_e_type_pe_determ >>
               MAP_EVERY qexists_tac [`ienv`, `st'''`, `st''''`, `t1`] >>
               rw [check_cenv_tenvC_ok]
               >- rw [num_tvs_bvl2, num_tvs_def]
               >- metis_tac [tenv_alpha_def] >>
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
               map_every qexists_tac [`ienv`, `p`, `st'''`] >>
               rw [] >>
               match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`ienv`,`e`, `init_infer_state`, `t1`] >>
               rw [check_s_def])
           >- (imp_res_tac infer_p_bindings >> fs [])
           >- metis_tac []
           >- (`tenv = tenv with v:=tenv_v'` by
                  fs[bind_tvar_def,type_environment_component_equality]>>
               metis_tac[]))
      >>
      qexists_tac `num_tvs tenv_v'` >>
          qexists_tac `convert_t (t_walkstar last_sub t)` >>
          qexists_tac `(convert_env last_sub env)` >>
          CONJ_TAC >-
            rw[empty_decls_def,convert_decls_def,empty_inf_decls_def]>>
          fs[]>>
          CONJ_ASM1_TAC>-
           (rw [ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
               REPEAT (pop_assum (fn _ => all_tac)) >>
               induct_on `env` >>
               rw [convert_env2_def, tenv_add_tvs_def, convert_env_def] >-
               (PairCases_on `h` >>
                    rw []) >>
               rw [MAP_MAP_o, combinTheory.o_DEF, remove_pair_lem])>>
           CONJ_ASM1_TAC>-
             (imp_res_tac infer_p_bindings >>fs [])
           >>

           (*Proof of generalization*)
           rw[weakE_def] >>
           Cases_on`ALOOKUP (tenv_add_tvs tvs' bindings') x`>>fs[]>>
           Cases_on`x'`>>fs[]>>
           CASE_TAC>-
             (imp_res_tac ALOOKUP_FAILS>>
             imp_res_tac ALOOKUP_MEM>>
             imp_res_tac type_p_pat_bindings>>
             fs[tenv_add_tvs_def,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
             pop_assum sym_sub_tac>>
             fs[Once LIST_EQ_REWRITE,MEM_EL,PULL_EXISTS,EL_MAP]>>
             first_x_assum(qspec_then `n` mp_tac)>>simp[EL_MAP]>>
             metis_tac[FST,PAIR_EQ,PAIR])
           >>
           Cases_on`x'`>>fs[]>>
           Q.ISPECL_THEN [`tvs'`,`bindings'`,`tenv with v:=bind_tvar tvs'(bind_var_list2 tenv_v Empty)`,`t'`,`p`,`ienv`,`e`] mp_tac (GEN_ALL infer_pe_complete)>>
           impl_tac>-
             (fs[Abbr`tenv_v'`,check_cenv_tenvC_ok,sub_completion_def,pure_add_constraints_def]>> rw []
              >- (Cases_on`tvs'=0`>>fs[num_tvs_bvl2,num_tvs_def,bind_tvar_def])
              >- (match_mp_tac tenv_invC_extend_tvar_empty_subst>>
                  fs[tenv_invC_convert_env2,num_tvs_bvl2,num_tvs_def]>>
                  metis_tac[tenv_alpha_def])
              >- metis_tac [type_p_tenvV_indep])
          >>
          rw[]>>
          imp_res_tac ALOOKUP_MEM>>
          qpat_x_assum `A=tenv_add_tvs B C` sym_sub_tac >>
          fs[convert_env2_def,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF]>>
          fs[MEM_MAP,PULL_EXISTS]>>
          fs[simp_tenv_invC_def,tenv_add_tvs_def,MEM_MAP,EXISTS_PROD]>>
          fs[ALOOKUP_MAP]>>
          res_tac>>
          imp_res_tac generalise_subst>>
          fs[]>>
          `t_walkstar last_sub (SND x') = infer_subst s' (t_walkstar s (SND x'))` by
           (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
           fs[MEM_EL])>>
          fs[sub_completion_def]>>
          Q.ISPECL_THEN [`tvs'`,`s''`] mp_tac (GEN_ALL generalise_subst_exist)>>
          impl_tac>-
            (fs[init_infer_state_def]>>
            `t_wfs FEMPTY` by fs[t_wfs_def]>>
            imp_res_tac infer_e_wfs>>
            imp_res_tac infer_p_wfs>>
            imp_res_tac t_unify_wfs>>
            rfs[]>>
            CONJ_TAC>-
              metis_tac[pure_add_constraints_wfs]
            >>
            Cases_on`tvs'=0`>>fs[bind_tvar_def,num_tvs_bvl2,num_tvs_def])
          >>
          rw[]>>
          pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND env)`,`[]`,`FEMPTY`,`num_tvs tenv_v'`,`s'`,`MAP (t_walkstar last_sub) (MAP SND env)`] mp_tac)>>
         impl_keep_tac
         >-
           (fs[MAP_MAP_o,combinTheory.o_DEF]>>
           fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
           fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
           ntac 2 strip_tac>>
           CONJ_ASM2_TAC
           >-
             metis_tac[check_t_t_vars]
           >>
           last_x_assum (qspec_then `x` assume_tac)>>rfs[]>>
           fs[UNCURRY]>>
           match_mp_tac t_walkstar_check>> fs[]>>
           reverse CONJ_TAC>-
           (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
           HINT_EXISTS_TAC>>
           fs[])
           >>
           match_mp_tac (check_s_more3 |> MP_CANON)>>
           qexists_tac `count st''''.next_uvar`>>
           fs[]>>
           match_mp_tac t_unify_check_s>>
           CONV_TAC (STRIP_QUANT_CONV (move_conj_left is_eq)) >>
           first_assum (match_exists_tac o concl)>>
           fs[]>>(reverse(rw[]))
           >-
             (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
             qexists_tac`count st'''.next_uvar`>>
             fs[]>>
             imp_res_tac infer_e_next_uvar_mono>>
             imp_res_tac infer_p_next_uvar_mono>>
             fs[SUBSET_DEF]>>
             DECIDE_TAC)
           >-
             (match_mp_tac (infer_p_check_s|>CONJUNCT1)>>
             first_assum (match_exists_tac o concl)>>
             fs[]>>
             match_mp_tac (infer_e_check_s|>CONJUNCT1)>>
             first_assum (match_exists_tac o concl)>>
             fs[check_s_def])
           >>
           `t_wfs FEMPTY` by fs[t_wfs_def]>>
           imp_res_tac infer_p_wfs >>
           imp_res_tac infer_e_wfs>>fs[])
         >>
         rw[]>>
       Cases_on`x'`>>fs[]>>
       `r' = t'` by
         (imp_res_tac ALOOKUP_ALL_DISTINCT_MEM>>
         fs[])>>
       pop_assum SUBST_ALL_TAC>>
       qexists_tac`MAP convert_t subst'`>>fs[]>>
       `check_t (num_tvs tenv_v') {} (infer_subst s' (t_walkstar s t'))`
         by
         (qpat_x_assum `A = infer_subst B C` sym_sub_tac>>
        (check_t_less |> CONJUNCT1 |> Q.GENL[`s`,`uvars`,`n`]
      |> Q.SPECL[`num_tvs tenv_v'`,`count (st'''':(num|->infer_t) infer_st).next_uvar`,`last_sub`]
      |> mp_tac)>>simp[]>>
          disch_then (qspec_then `t'` mp_tac)>>
          impl_tac>-
          (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
          metis_tac[])>>
          rw[]>>
          `count st''''.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
          (simp[EXTENSION]>>fs[SUBSET_DEF]>>
          metis_tac[])>>
          fs[])
      >>
       CONJ_ASM1_TAC>-
         metis_tac[check_t_to_check_freevars]>>
       CONJ_TAC>-
         (fs[EVERY_MAP,EVERY_MEM]>>
         metis_tac[check_t_to_check_freevars])
       >>
       imp_res_tac deBruijn_subst_convert>>
       pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
       `r = convert_t (t_walkstar s'' t')` by
         (qpat_x_assum`unconvert_t r = A`(assume_tac o Q.AP_TERM `convert_t`)>>
         metis_tac[check_freevars_empty_convert_unconvert_id])>>
       fs[]>>AP_TERM_TAC>>
       Q.ISPECL_THEN [`s''`,`s'`,`subst'`,`tvs'`,`count st''''.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
       impl_tac>-
         (fs[SUBSET_DEF]>>
         rw[]>>
         fs[IN_FRANGE]>>
         metis_tac[pure_add_constraints_wfs])>>
       rw[]>>
       pop_assum kall_tac>>
       pop_assum(qspec_then `t_walkstar s t'` mp_tac)>>
       impl_tac>-
         (
         imp_res_tac infer_p_check_t>>
         fs[EXTENSION,SUBSET_DEF]>>
         fs[MEM_MAP,PULL_EXISTS]>>
         imp_res_tac ALOOKUP_MEM>>
         fs[FORALL_PROD,EXISTS_PROD]>>
         CONJ_TAC>-
           metis_tac[]>>
         reverse CONJ_TAC>-
           metis_tac[]
         >>
         fs[EVERY_MAP,MAP_MAP_o,EVERY_MEM,UNCURRY]>>
         match_mp_tac t_walkstar_check>>fs[]>>
         CONJ_TAC>-
           (`check_s 0 (count init_infer_state.next_uvar) init_infer_state.subst ∧ t_wfs init_infer_state.subst` by
             fs[init_infer_state_def,check_s_def,t_wfs_def]>>
           fs[init_infer_state_def]>>
           drule (CONJUNCT1 infer_e_check_s) >>
           rfs[]>>
           disch_then(qspec_then`0` assume_tac)>>rfs[]>>
           drule (infer_p_check_s|>CONJUNCT1)>>
           simp [] >>
           disch_then drule >>
           rw [] >>
           `check_s 0 (count st''''.next_uvar) s` by
             (match_mp_tac t_unify_check_s>>
             `t_wfs st''''.subst` by
               metis_tac[infer_e_wfs,infer_p_wfs]>>
              first_assum (match_exists_tac o concl)>>
              HINT_EXISTS_TAC>>fs[]>>
              qexists_tac`t`>>fs[]>>
              match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
              qexists_tac `count st'''.next_uvar`>>
              fs[EXTENSION,SUBSET_DEF] >>
              rw[]>>
              imp_res_tac infer_p_next_uvar_mono>>
              DECIDE_TAC)>>
           match_mp_tac check_s_more5>>
           HINT_EXISTS_TAC>>
           fs[SUBSET_DEF])
           >>
           first_x_assum(qspec_then`(q',t')` assume_tac)>>rfs[]>>
           imp_res_tac check_t_more5>>
           fs[SUBSET_DEF,EXTENSION])
       >>
       rw[]>>
       metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success])
 (*Letrec*)
 >- (fs [success_eqns] >>
     `?tvs s ts. generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l)))) = (tvs,s,ts)`
                 by (cases_on `generalise_list st'''.next_uvar 0 FEMPTY (MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar (st'''.next_uvar + n)) (COUNT_LIST (LENGTH l))))` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [] >>
     rw [] >>
     fs [success_eqns] >>
     Q.ABBREV_TAC `tenv_v' = bind_tvar tvs (bind_var_list2 tenv_v Empty)` >>
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
     `tenv_inv FEMPTY ienv.inf_v (bind_var_list2 tenv_v Empty)` by metis_tac [tenv_alpha_def] >>
     `tenv_inv FEMPTY ienv.inf_v tenv_v'` by metis_tac [tenv_inv_extend_tvar_empty_subst] >>
     `tenv_inv last_sub ienv.inf_v tenv_v'` by metis_tac [tenv_inv_empty_to] >>
     Q.ABBREV_TAC `tenv_v'' =
                   bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l))))
                                 tenv_v'` >>
     Q.ABBREV_TAC `env'' = MAP2 (λ(f,x,e) uvar. (f,0,uvar)) l (MAP (λn.  Infer_Tuvar (0 + n)) (COUNT_LIST (LENGTH l))) ++ ienv.inf_v` >>
     `tenv_inv last_sub env'' tenv_v''` by metis_tac [tenv_inv_letrec_merge] >>
     fs [] >>
     `check_env (count (LENGTH l)) env''`
                 by (Q.UNABBREV_TAC `env''` >>
                     rw [MAP2_MAP, check_env_merge, check_env_letrec] >>
                     metis_tac [check_env_more, COUNT_ZERO, DECIDE ``0<=x:num``]) >>
     `num_tvs tenv_v'' = tvs`
                 by  (Q.UNABBREV_TAC `tenv_v''` >>
                      rw [num_tvs_bind_var_list] >>
                      Q.UNABBREV_TAC `tenv_v'` >>
                      fs [bind_tvar_rewrites, num_tvs_bvl2, num_tvs_def]) >>
     `type_funs (tenv with v := tenv_v'') l (MAP2 (λ(x,y,z) t. (x,(convert_t o t_walkstar last_sub) t)) l funs_ts)`
             by (match_mp_tac (List.nth (CONJUNCTS infer_e_sound, 3)) >>
                 rw [] >>
                 qexists_tac`ienv with inf_v := env''` >>
                 qexists_tac `init_infer_state with next_uvar := LENGTH l` >>
                 rw [] >>
                 metis_tac [num_tvs_bind_var_list,menv_alpha_convert]) >>
     `t_wfs (init_infer_state with next_uvar := LENGTH l).subst` by rw [] >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     qexists_tac `(MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar last_sub (Infer_Tuvar (0 + n)))) (COUNT_LIST (LENGTH l))))` >>
     qexists_tac `tvs` >>
     rw []
     >-
       rw [empty_decls_def, convert_decls_def,empty_inf_decls_def]
     >-
      (rw [LENGTH_MAP, LENGTH_COUNT_LIST, MAP2_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
          REPEAT (pop_assum (fn _ => all_tac)) >>
          induct_on `l` >>
          rw [COUNT_LIST_def, tenv_add_tvs_def, convert_env_def, convert_env2_def] >-
          (PairCases_on `h` >> rw []) >>
          rw [MAP_MAP_o, MAP2_MAP, ZIP_MAP, LENGTH_COUNT_LIST, combinTheory.o_DEF, remove_pair_lem])
      >-
      (`LENGTH l = LENGTH funs_ts` by fs [LENGTH_COUNT_LIST] >>
          fs [MAP_ZIP, LENGTH_COUNT_LIST, MAP_MAP_o, combinTheory.o_DEF] >>
          metis_tac [letrec_lemma2, LENGTH_COUNT_LIST, LENGTH_MAP,
                     pure_add_constraints_wfs, sub_completion_apply])
      >>
      (*Proof of generalization*)
      ntac 4 (qpat_x_assum`∀ts s2. P ts s2`kall_tac) >>
          rw[weakE_def] >>
          Cases_on`ALOOKUP (tenv_add_tvs tvs' bindings') x`>>fs[]>>
          Cases_on`x'`>>fs[]>>
          CASE_TAC>-(
            imp_res_tac ALOOKUP_FAILS>>
            imp_res_tac ALOOKUP_MEM>>
            imp_res_tac type_funs_MAP_FST >>
            ntac 2 (pop_assum mp_tac) >>
            simp[Once LIST_EQ_REWRITE,EL_MAP,GSYM AND_IMP_INTRO] >>
            ntac 2 strip_tac >> fs[LENGTH_COUNT_LIST] >>
            disch_then kall_tac >>
            fs[tenv_add_tvs_def,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
            fs[MAP2_MAP,MEM_MAP,PULL_EXISTS,EXISTS_PROD,LENGTH_COUNT_LIST] >>
            fs[MEM_ZIP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
            fs[MEM_EL] >>
            metis_tac[FST,PAIR,PAIR_EQ])
           >>
           Cases_on`x'`>>fs[]>>rfs[]>>
           first_assum (mp_tac o MATCH_MP(GEN_ALL infer_funs_complete|>REWRITE_RULE[GSYM AND_IMP_INTRO]))>>
           fs[check_cenv_tenvC_ok,check_env_def,tenv_alpha_def]>>
           rpt (disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
           rw[]>>
           `st''''' = st'` by (
             simp[infer_st_component_equality] >>
             metis_tac[pure_add_constraints_functional] ) >>
           var_eq_tac >>
           imp_res_tac ALOOKUP_MEM>>
           fs[tenv_add_tvs_def,MAP2_MAP,MAP_MAP_o,LENGTH_COUNT_LIST]>>
           fs[MEM_MAP,EXISTS_PROD]>>
           fs[MEM_ZIP,LENGTH_COUNT_LIST]>>
           fs[EL_MAP,LENGTH_COUNT_LIST,COUNT_LIST_GENLIST,EL_GENLIST]>>
           rfs[EL_MAP]>>
           imp_res_tac generalise_subst>>
           fs[]>>
          `t_walkstar last_sub (Infer_Tuvar n) = infer_subst s (t_walkstar st'.subst (Infer_Tuvar n))` by
           (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
           metis_tac[])>>
         fs[sub_completion_def]>>
          Q.ISPECL_THEN [`tvs'`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>
          impl_tac>-
            (fs[]>>metis_tac[pure_add_constraints_wfs])
          >>
          rator_x_assum `generalise_list` mp_tac>>
          qpat_abbrev_tac `ts:infer_t list = MAP A B`>>
          qpat_abbrev_tac `ts':infer_t list = MAP A B`>>
          rw[]>>
          pop_assum (qspecl_then[`ts`,`[]`,`FEMPTY`,`num_tvs tenv_v''`,`s`,`ts'`] mp_tac)>>
         impl_keep_tac
         >-
           (
           fs[MAP_MAP_o,combinTheory.o_DEF]>>
           fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
           fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
           ntac 2 strip_tac>>
           CONJ_ASM2_TAC
           >-
             metis_tac[check_t_t_vars]
           >>
           fs[Abbr`ts`,MEM_MAP,MEM_GENLIST]>>
           match_mp_tac t_walkstar_check >>
           simp[] >>
           (*inferencer invariant*)
           simp[check_t_def] >>
           reverse conj_tac >- (
             imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >> fs[] >>
             DECIDE_TAC ) >>
           match_mp_tac (check_s_more3 |> MP_CANON)>>
           qexists_tac `count st'.next_uvar`>>
           simp[] )
         >>
         rw[]>>
       qexists_tac`MAP convert_t subst'`>>fs[]>>
       `check_t (num_tvs tenv_v'') {} (infer_subst s (t_walkstar st'.subst (Infer_Tuvar n)))`
         by
         (qpat_x_assum `A = infer_subst B C` sym_sub_tac>>
        (check_t_less |> CONJUNCT1 |> Q.GENL[`s`,`uvars`,`n`]
      |> Q.SPECL[`num_tvs tenv_v''`,`count (st':(num|->infer_t) infer_st).next_uvar`,`last_sub`]
      |> mp_tac)>>simp[]>>
          disch_then (qspec_then `Infer_Tuvar n` mp_tac)>>
          impl_tac>-
          (fs[check_t_def]>>
           imp_res_tac infer_e_next_uvar_mono>>
           fs[]>>
           DECIDE_TAC)>>
          rw[]>>
          `count st'.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
          (simp[EXTENSION]>>fs[SUBSET_DEF]>>
          metis_tac[])>>
          fs[])
      >>
       CONJ_ASM1_TAC>-
         metis_tac[check_t_to_check_freevars]>>
       CONJ_TAC>-
         (fs[EVERY_MAP,EVERY_MEM]>>
         metis_tac[check_t_to_check_freevars])
       >>
       imp_res_tac deBruijn_subst_convert>>
       pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
       `r = convert_t (t_walkstar s' (Infer_Tuvar n))` by
         (
         `r = EL n (MAP SND bindings')` by (
           qpat_x_assum`MEM X bindings'`mp_tac >>
           qpat_x_assum`X = EL n Y`mp_tac >>
           rator_x_assum`ALL_DISTINCT`mp_tac >>
           imp_res_tac type_funs_MAP_FST >>
           pop_assum kall_tac >> pop_assum mp_tac >>
           `n < LENGTH l` by metis_tac[] >> pop_assum mp_tac >>
           rpt (pop_assum kall_tac) >> rw[] >>
           fs[MEM_EL] >>
           fs[EL_ALL_DISTINCT_EL_EQ] >>
           first_x_assum(qspecl_then[`n`,`n'`]mp_tac) >>
           impl_keep_tac >- metis_tac[LENGTH_MAP] >>
           `EL n (MAP FST bindings') = EL n (MAP FST l)` by metis_tac[] >>
           pop_assum SUBST1_TAC >>
           simp[EL_MAP] >>
           metis_tac[FST,SND]) >>
         `r = convert_t (t_walkstar s' (EL n funs_ts))` by simp[EL_MAP] >>
         simp[]>>AP_TERM_TAC>>
         `t_compat st'.subst s'` by metis_tac[pure_add_constraints_success] >>
         fs[t_compat_def]>>
         `t_walkstar st'.subst (EL n funs_ts) =
          t_walkstar st'.subst (Infer_Tuvar n)` by
           (fs[MAP_ZIP]>>
           qpat_x_assum`MAP (t_walkstar E) B = MAP C D` mp_tac>>
           simp[LIST_EQ_REWRITE,EL_MAP])>>
          metis_tac[])>>
       fs[]>>AP_TERM_TAC>>
       Q.ISPECL_THEN [`s'`,`s`,`subst'`,`tvs'`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
       impl_tac>-
         (fs[SUBSET_DEF]>>
         rw[]>>
         fs[IN_FRANGE]>>
         metis_tac[pure_add_constraints_wfs])>>
       rw[]>>
       pop_assum kall_tac>>
       pop_assum(qspec_then `t_walkstar st'.subst (Infer_Tuvar n)` mp_tac)>>
       impl_tac>-
         (
         fs[EXTENSION,SUBSET_DEF,Abbr`ts`]>>
         fs[MEM_MAP,PULL_EXISTS]>>
         imp_res_tac ALOOKUP_MEM>>
         fs[FORALL_PROD,EXISTS_PROD,MEM_GENLIST]>>
         CONJ_TAC>-
           metis_tac[]>>
         reverse CONJ_TAC>-
           metis_tac[]
         >>
         fs[EVERY_MAP,EVERY_GENLIST])
       >>
       rw[]>>
       metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success])
 >- (rw [convert_decls_def, ienv_to_tenv_def, EVERY_MAP, DISJOINT_DEF, EXTENSION,empty_inf_decls_def] >>
     fs [EVERY_MAP, EVERY_MEM, env_rel_sound_def] >>
     rw [MEM_MAP] >>
     metis_tac [])
 >- (
   fs [convert_decls_def, ienv_to_tenv_def, empty_decls_def,empty_inf_decls_def, env_rel_sound_def]
   >> rw [])
 >- (
   fs [convert_decls_def, ienv_to_tenv_def,empty_inf_decls_def, env_rel_sound_def]
   >> rw []
   >> metis_tac[MAP_ID]));

val infer_ds_sound = Q.prove (
`!mn decls ienv ds st1 decls' tenvT' cenv' env' st2 tenv.
  infer_ds mn decls ienv ds st1 = (Success (decls',tenvT',cenv',env'), st2) ∧
  env_rel tenv ienv
  ⇒
  type_ds T mn (convert_decls decls) tenv ds (convert_decls decls') (tenvT',cenv',(convert_env2 env'))`,
 fs[env_rel_def]>>
 induct_on `ds` >>
 rpt gen_tac >>
 rw [infer_ds_def, success_eqns]
 >- rw [empty_decls_def,convert_decls_def, convert_env2_def, Once type_ds_cases,empty_inf_decls_def]
 >- rw [convert_env2_def]
 >>
 `?decls'' cenv'' tenvT'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
 fs [success_eqns] >>
 `?decls''' tenvT''' cenv''' env'''. v'' = (decls''',tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
 fs [success_eqns] >>
 rw [Once type_ds_cases] >>
 fs [init_infer_state_def] >>
 imp_res_tac infer_d_check >>
 ntac 6 (pop_assum kall_tac) >>
 `check_cenv (merge_alist_mod_env ([],cenv'') tenv.c)`
          by (Cases_on`tenv.c` >>
              fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def]) >>
 `tenv_tabbrev_ok (merge_mod_env (FEMPTY,tenvT'') tenv.t)`
        by (match_mp_tac tenv_tabbrev_ok_merge >>
            fs [tenv_tabbrev_ok_def, FEVERY_FEMPTY]) >>
 `check_env {} (env'' ++ ienv.inf_v)`
                 by fs [check_env_def, init_infer_state_def] >>
 first_x_assum(mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] (infer_d_sound|>REWRITE_RULE[env_rel_def]))) >>
 disch_then(qspecl_then[`tenv`]mp_tac) >> simp[] >> strip_tac >>
 qabbrev_tac`tenv' = tenv with
   <|t := (merge_mod_env (FEMPTY,tenvT'') tenv.t);
     c := (merge_alist_mod_env ([],cenv'') tenv.c)|>`>>
 fs[type_environment_component_equality,markerTheory.Abbrev_def]>>
 ntac 4 (pop_assum (mp_tac o SYM))>> ntac 4 strip_tac>>fs[]>>
 first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
 fs[extend_env_new_decs_def,EXISTS_PROD,tenv_bvl_def]>>
 disch_then(qspecl_then[`tenv' with v:= bind_var_list2 ((convert_env2 env'') ++ tenv_v) Empty`]mp_tac) >> simp[] >>
 impl_tac >- (
   conj_tac >- metis_tac[]>>
   conj_tac >- (
     simp[bvl2_append] >>
     match_mp_tac tenv_val_ok_bind_var_list2 >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     fs[check_env_def,convert_env2_def,EVERY_MAP] >>
     fs[EVERY_MEM,UNCURRY] >>
     metis_tac[check_t_to_check_freevars] ) >>
   match_mp_tac tenv_alpha_bind_var_list2>>
   rw[]>-
     metis_tac[tenv_alpha_convert]
   >>
   rfs[]>>
   fs[EXTENSION,MEM_MAP,PULL_EXISTS,EXISTS_PROD,convert_env2_def])>>
 strip_tac >>
 CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``type_d`` o fst o strip_comb))) >>
 first_assum(match_exists_tac o concl) >> simp[] >>
 fs[convert_append_decls,bvl2_append] >>
 pop_assum mp_tac>>
 qpat_abbrev_tac` A = tenv' with v := B`>>
 qpat_abbrev_tac `B = <|m:=C;c:=D;v:=E;t:=G|>`>>
 `A = B` by
   (unabbrev_all_tac>>fs[type_environment_component_equality])>>
 strip_tac>>rfs[]>>
 CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``type_ds`` o fst o strip_comb))) >>
 first_assum(match_exists_tac o concl) >> simp[] >>
 simp[convert_env2_def,append_new_dec_tenv_def]);

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

val weakE_anub = store_thm("weakE_anub",
  ``∀env1 env2. weakE env1 (anub env2 []) ⇒ weakE env1 env2``,
  rw[weakE_def] >>
  fs[Once ALOOKUP_anub])

val flat_weakC_anub = store_thm("flat_weakC_anub",
  ``flat_weakC x (anub y []) ⇒ flat_weakC x y``,
  rw[flat_weakC_def] >>
  fs[Once ALOOKUP_anub])

val check_weakE_sound = Q.prove (
  `!tenv1 tenv2a tenv2 acc st st2.
    check_env {} tenv1 ∧
    check_env {} tenv2 ∧
    anub tenv2 acc = tenv2a ∧
    (check_weakE tenv1 (anub tenv2 acc) st = (Success (), st2))
    ⇒
    weakE (convert_env2 tenv1) (convert_env2 (anub tenv2 acc))`,
  ho_match_mp_tac check_weakE_ind >>
  conj_tac >- (
    rw[anub_def,weakE_def,convert_env2_def] ) >>
  srw_tac[][] >>
  imp_res_tac(check_weakE_EVERY |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SIMP_RULE(srw_ss())[PULL_EXISTS]) >>
  REV_FULL_SIMP_TAC(srw_ss())[] >>
  Cases_on`ALOOKUP tenv1 n` >> fsrw_tac[][] >>
  `?tvs_impl t_impl. x = (tvs_impl,t_impl)` by metis_tac[PAIR] >> fsrw_tac[][] >>
  rator_x_assum`EVERY`(mp_tac o CONV_RULE(REWR_CONV(GSYM check_weakE_EVERY))) >>
  strip_tac >>
  imp_res_tac anub_tl_anub >>
  fs[] >>
  first_x_assum(qspecl_then[`a`,`b`,`st`]mp_tac) >> simp[] >>
  impl_keep_tac >- (
    fs[check_env_def,SUBSET_DEF,EVERY_MEM] ) >>
  rw [convert_env2_def, weakE_def] >>
  rw[] >>
  simp[Q.ISPEC`λ(tvs,t). (tvs, convert_t t)`ALOOKUP_MAP|>SIMP_RULE(srw_ss())[LAMBDA_PROD]] >>
  fs[LET_THM,IS_SOME_EXISTS] >>
  pop_assum kall_tac >>
  qmatch_assum_rename_tac`t_unify FEMPTY t_spec _ = SOME s` >>
  fs [] >>
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
                    simp [check_s_def, check_t_infer_db_subst2] >>
                    simp[COUNT_LIST_GENLIST,MAP_GENLIST,ETA_AX] >>
                    reverse conj_tac >-
                      metis_tac [check_t_more, check_t_more2, arithmeticTheory.ADD_COMM] >>
                    `ALOOKUP tenv2 n = SOME (tvs_spec,t_spec)` suffices_by
                      metis_tac[check_t_more, check_t_more2] >>
                    `ALOOKUP tenv2 n = ALOOKUP (anub tenv2 acc) n` by (
                      CONV_TAC(RAND_CONV(REWR_CONV ALOOKUP_anub)) >> rw[] >>
                      metis_tac[anub_notin_acc,MEM,MAP,FST] ) >>
                    rw[]) >>
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
                                        fs[] >>
                                        imp_res_tac (GSYM mem_to_flookup) >>
                                        fs[] >>
                                        ntac 2 (pop_assum mp_tac) >>
                                        rw [FLOOKUP_FUN_FMAP] >>
                                        rw [check_t_def],
                                    pop_assum mp_tac >>
                                        rw [FLOOKUP_DEF]]],
                          fs [EXTENSION, MEM_COUNT_LIST] >>
                              res_tac >>
                              fs [FDOM_FUPDATE_LIST]]) >>
         rw [check_t_to_check_freevars])
     >- (
       `check_t tvs_spec {} t_spec` by (
         first_x_assum match_mp_tac >>
        `ALOOKUP tenv2 n = SOME (tvs_spec,t_spec)` suffices_by
          metis_tac[check_t_more, check_t_more2] >>
        `ALOOKUP tenv2 n = ALOOKUP (anub tenv2 acc) n` by (
          CONV_TAC(RAND_CONV(REWR_CONV ALOOKUP_anub)) >> rw[] >>
          metis_tac[anub_notin_acc,MEM,MAP,FST] ) >>
        rw[] ) >>
       imp_res_tac t_walkstar_no_vars >>
       fs [] >>
       rw [SIMP_RULE (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] (GSYM db_subst_infer_subst_swap2)] >>
       AP_TERM_TAC >>
       simp[MAP_GENLIST,COUNT_LIST_GENLIST,ETA_AX] >>
       match_mp_tac (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] no_vars_extend_subst) >>
         rw []
         >- (rw [DISJOINT_DEF, EXTENSION] >>
             metis_tac [])
         >- (imp_res_tac check_t_t_vars  >>
             fs [EXTENSION, SUBSET_DEF])));

val check_flat_weakC_sound = Q.prove (
`!tenvC1 tenvC2 acc.
  check_flat_weakC tenvC1 (anub tenvC2 acc)
  ⇒
  flat_weakC tenvC1 (anub tenvC2 acc)`,
rpt gen_tac >>
Induct_on`anub tenvC2 acc` >>
rw[] >- (
  last_x_assum(strip_assume_tac o SYM) >>
  rw[flat_weakC_def] ) >>
qpat_x_assum`X = Y`(assume_tac o SYM) >>
imp_res_tac anub_tl_anub >> rw[] >>
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
`!mn orig_tenvT idecls tenvT cenv env specs st idecls' tenvT' cenv' env' st'.
  (check_specs mn orig_tenvT idecls tenvT cenv env specs st = (Success (idecls',tenvT',cenv',env'), st')) ⇒
  tenv_tabbrev_ok orig_tenvT
  ⇒
  ?decls'' tenvT'' cenv'' env''.
    type_specs mn orig_tenvT specs decls'' (tenvT'',cenv'',(convert_env2 env'')) ∧
    (convert_decls idecls' = union_decls decls'' (convert_decls idecls)) ∧
    (tenvT' = FUNION tenvT'' tenvT) ∧
    (cenv' = cenv'' ++ cenv) ∧
    (env' = env'' ++ env)`,
 ho_match_mp_tac check_specs_ind >>
 rw [check_specs_def, success_eqns]
 >- (rw [Once type_specs_cases] >>
     fs [empty_decls_def, convert_decls_def, append_decls_def, convert_env2_def,union_decls_def])
 >- (rw [Once type_specs_cases] >>
     res_tac >>
     `check_freevars 0 fvs t` by metis_tac [t_to_freevars_check] >>
     `check_freevars 0 (nub fvs) t` by metis_tac [check_freevars_nub] >>
     fs[PULL_EXISTS,EXISTS_PROD,append_new_dec_tenv_def]>>
     fs[convert_env2_def]>>
     Q.LIST_EXISTS_TAC [`decls''`, `tenvT''`,`nub fvs`]>>fs[]>>
     rw [] >>
     `check_freevars 0 (nub fvs) (type_name_subst orig_tenvT t)` by fs[check_freevars_type_name_subst]>>
     fs [LENGTH_MAP, convert_env2_def, convert_t_subst,
         LENGTH_COUNT_LIST,LENGTH_GENLIST] >>
     fs [MAP_MAP_o, combinTheory.o_DEF, convert_t_def] >>
     metis_tac [COUNT_LIST_GENLIST, combinTheory.I_DEF])
 >- (rw [Once type_specs_cases] >>
     rw [convert_decls_def] >>
     res_tac >>
     pop_assum mp_tac>>impl_tac>-
       (match_mp_tac tenv_tabbrev_ok_merge>>fs[tenv_tabbrev_ok_def,FEVERY_FEMPTY,flat_tenv_tabbrev_ok_def]>>
      fs[FEVERY_ALL_FLOOKUP,flookup_update_list_some]>>rw[]>>
      imp_res_tac ALOOKUP_MEM>>
      fs[MEM_MAP]>>PairCases_on`y`>>
      fs[check_freevars_def,EVERY_MAP,EVERY_MEM])>>
    strip_tac>>
    fs[PULL_EXISTS,EXISTS_PROD,append_new_dec_tenv_def]>>
    qexists_tac`tenvT'''`>>
    qexists_tac`decls''`>>
    fs[union_decls_def,convert_decls_def]>>
    rw[EXTENSION]>- metis_tac[]>>
    fs[FUNION_ASSOC])
 >- (rw [Once type_specs_cases, PULL_EXISTS] >>
     res_tac >>
     pop_assum mp_tac>>impl_tac>-
       (match_mp_tac tenv_tabbrev_ok_merge>>fs[tenv_tabbrev_ok_def,FEVERY_FEMPTY,flat_tenv_tabbrev_ok_def]>>
       fs[FEVERY_FUPDATE,FEVERY_FEMPTY,check_freevars_type_name_subst])>>
     strip_tac>>
     qexists_tac`decls''`>>fs[EXISTS_PROD,append_new_dec_tenv_def]>>
     qexists_tac`tenvT''`>>
     rw[FUNION_FUPDATE_2]>>
     rw[FUNION_FUPDATE_1])
 >- (rw [Once type_specs_cases] >>
     res_tac >>
     fs[PULL_EXISTS,EXISTS_PROD,append_new_dec_tenv_def]>>
     qexists_tac`tenvT''`>>
     qexists_tac`decls''`>>
     fs[union_decls_def,convert_decls_def,EXTENSION]>>
     metis_tac[])
 >- (rw [Once type_specs_cases, convert_decls_def] >>
     res_tac >>
     pop_assum mp_tac>>impl_tac>-
       (match_mp_tac tenv_tabbrev_ok_merge>>fs[tenv_tabbrev_ok_def,FEVERY_FEMPTY,flat_tenv_tabbrev_ok_def]>>
      fs[FEVERY_FUPDATE,FEVERY_FEMPTY,check_freevars_type_name_subst,check_freevars_def,EVERY_MAP,EVERY_MEM])>>
     rw [PULL_EXISTS,EXISTS_PROD,append_new_dec_tenv_def] >>
     qexists_tac`tenvT''`>>
     qexists_tac`decls''`>>
     fs[union_decls_def,convert_decls_def,Once INSERT_SING_UNION]>>
     fs[EXTENSION]>>
     CONJ_TAC>- metis_tac[]>>
     rw[FUNION_FUPDATE_2]>>
     rw[FUNION_FUPDATE_1]))

val infer_top_sound = Q.store_thm ("infer_top_sound",
`!idecls ienv tenv top st1 idecls' tenvT' menv' cenv' env' st2.
  (infer_top idecls ienv top st1 = (Success (idecls',tenvT',menv', cenv', env'), st2)) ∧
  env_rel tenv ienv
  ⇒
  type_top T (convert_decls idecls) tenv top (convert_decls idecls') (tenvT',(convert_menv menv'),cenv',(convert_env2 env')) ∧
  env_rel
  <|t:= (merge_mod_env tenvT' tenv.t);
    m := (convert_menv menv' ⊌ tenv.m);
    c:= (merge_alist_mod_env cenv' tenv.c);
    v:= (bind_var_list2 (convert_env2 env') tenv.v)|>
  <|inf_t:= (merge_mod_env tenvT' tenv.t);
    inf_m:= (FUNION menv' ienv.inf_m);
    inf_c:= (merge_alist_mod_env cenv' tenv.c);
    inf_v:=(env'++ienv.inf_v)|>`,
 fs[env_rel_def]>>
 cases_on `top` >>
 rpt gen_tac >>
 fs [infer_top_def, success_eqns, type_top_cases] >>
 strip_tac >>
 `∃decls'' tenvT'' cenv'' env''. v' = (decls'',tenvT'',cenv'',env'')` by metis_tac [pair_CASES] >>
 fs [success_eqns]
 >- (`∃decls''' tenvT''' cenv''' env'''. v'' = (decls''',tenvT''',cenv''',env''')` by metis_tac [pair_CASES] >>
     fs[success_eqns]>>
     `flat_tenv_tabbrev_ok (FEMPTY:flat_tenv_tabbrev) ∧ check_flat_cenv ([]:flat_tenv_ctor) ∧ check_env {} ([]:(tvarN, num # infer_t) alist)`
                by rw [flat_tenv_tabbrev_ok_def, check_flat_cenv_def, check_env_def,
                       check_cenv_def, FEVERY_FEMPTY] >>
     `flat_tenv_tabbrev_ok tenvT'' ∧ check_flat_cenv cenv'' ∧ check_env ∅ env''` by metis_tac [infer_ds_check] >>
     rw[]
     >- (fs [success_eqns] >>
         rw [convert_decls_def] >>
         first_x_assum(mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] infer_ds_sound)) >>
         disch_then(qspecl_then[`tenv`] mp_tac) >>
         impl_tac>-
           simp[env_rel_def]>>
         simp[] >> strip_tac >>
         cases_on `o'` >>
         fs [success_eqns, check_signature_def, check_signature_cases]
         >- (fs [convert_menv_def] >>
             rw [] >>
             fs [convert_env2_def, convert_decls_def,mod_lift_new_dec_tenv_def] >>
             CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``type_ds`` o fst o strip_comb))) >>
             first_assum(match_exists_tac o concl) >>
             simp[union_decls_def,mod_lift_new_dec_tenv_def] >>
             metis_tac [INSERT_SING_UNION])
         >- (PairCases_on `v'` >>
             fs [success_eqns] >>
             rw [] >>
             `check_env {} env''' ∧ flat_tenv_tabbrev_ok tenvT'''` by (
               first_x_assum(mp_tac o MATCH_MP(
                 check_specs_check
                 |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left is_eq)))
                 |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
               simp[])>>
             imp_res_tac check_specs_sound >>
             fs[convert_decls_def,EXISTS_PROD]>>
             CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``type_ds`` o fst o strip_comb))) >>
             first_assum(match_exists_tac o concl) >> simp[] >>
             fs[weak_new_dec_tenv_def]>>
             Q.LIST_EXISTS_TAC [`tenvT''''`,`cenv''''`,`convert_env2 env''''`,`decls''''`]>>
             fs[mod_lift_new_dec_tenv_def,convert_env2_def,union_decls_def,empty_inf_decls_def,Once INSERT_SING_UNION]>>
             (reverse(rw[]))
             >- (fs[weak_decls_def,check_weak_decls_def,list_subset_def,SUBSET_DEF,EVERY_MEM]>>
               metis_tac[])
             >- metis_tac [check_weakE_sound, convert_env2_def, weakE_anub, convert_env2_anub]
             >- metis_tac[check_flat_weakC_sound,flat_weakC_anub]
             >- metis_tac [check_flat_weakT_sound]
             >>
               fs[convert_menv_def]))
     >>
       simp[convert_env2_def,bind_var_list2_def]
     >-
       (*Extra case..*)
       (fs[typeSoundInvariantsTheory.tenv_mod_ok_def]>>
       match_mp_tac fevery_funion >> simp[] >>
       fs[convert_menv_def,FEVERY_FUPDATE,FEVERY_FEMPTY]>>
       match_mp_tac tenv_val_ok_bind_var_list2>>
       fs[tenv_val_ok_def,num_tvs_def,EVERY_MAP]>>
       qsuff_tac`check_menv (FEMPTY |+ (s,env'''))`
       >-
         (fs[check_menv_def,FEVERY_FUPDATE]>>
         fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
         metis_tac[check_t_to_check_freevars])
       >>
       imp_res_tac infer_top_invariant>>rfs[]>>
       first_x_assum match_mp_tac>>
       qexists_tac`Tmod s o' l`>>
       simp[infer_top_def,success_eqns,PULL_FORALL,EXISTS_PROD,success_eqns,PULL_FORALL,GSYM AND_IMP_INTRO]>>
       metis_tac[])
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
             first_x_assum(mp_tac o MATCH_MP(
               check_specs_check
               |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left is_eq)))
               |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
             fs [check_env_def, check_flat_cenv_def]))
     >- (fs[success_eqns]>>
       `check_menv (FEMPTY|+(s,env'''))` by
         (fs[check_menv_def,FEVERY_DEF]>>
         Cases_on`o'`>>fs[check_signature_def,success_eqns]
         >-
           metis_tac[check_env_def]
         >>
         PairCases_on`v'`>>fs[success_eqns]>>
         `check_env {} env'''` by
            imp_res_tac check_specs_check)>>
         fs[check_env_def]>>
       imp_res_tac menv_alpha_convert>>
       fs[menv_alpha_def]>>
       match_mp_tac fmap_rel_FUNION_rels>>fs[])
     >- (fs [success_eqns, check_menv_def] >>
         rw [] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw []
         >- (fs [check_cenv_def] >>
             Cases_on `tenv.c` >>
             fs [merge_alist_mod_env_def, check_cenv_def])
         >- (PairCases_on `v'` >>
             fs [success_eqns] >>
             rw [] >>
             first_x_assum(mp_tac o MATCH_MP(
               check_specs_check
               |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left is_eq)))
               |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
             fs [check_env_def, check_flat_cenv_def] >>
             Cases_on`tenv.c` >>
             fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def]))
     >- (match_mp_tac tenv_tabbrev_ok_merge >>
         fs [success_eqns, check_signature_def] >>
         rw [tenv_tabbrev_ok_def, FEVERY_FUPDATE, FEVERY_FEMPTY] >>
         cases_on `o'` >>
         fs [check_signature_def, success_eqns] >>
         rw [] >>
         PairCases_on `v'` >>
         fs [success_eqns] >>
         rw [] >>
         first_x_assum(mp_tac o MATCH_MP(
           check_specs_check
           |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left is_eq)))
           |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
         rw[]))>>
 rw [EXISTS_PROD,lift_new_dec_tenv_def,convert_menv_def]>>
 fs[tenv_bvl_def]>>rfs[]
 >- metis_tac [infer_d_sound,env_rel_def,tenv_bvl_def]
 >-  metis_tac[bind_var_list2_append]
 >- (imp_res_tac infer_d_check >>
     ntac 6 (pop_assum kall_tac) >>
     rw[bind_var_list2_append] >>
     match_mp_tac tenv_val_ok_bind_var_list2 >>
     rw[num_tvs_bvl2,num_tvs_def,convert_env2_def,EVERY_MAP] >>
     fs[EVERY_MEM,UNCURRY,check_env_def] >>
     metis_tac[check_t_to_check_freevars])
 >- (imp_res_tac infer_d_check >>
     Cases_on`tenv.c` >>
     fs [merge_alist_mod_env_def, check_cenv_def, check_flat_cenv_def])
 >- (match_mp_tac tenv_tabbrev_ok_merge >>
     rw [tenv_tabbrev_ok_def] >>
     imp_res_tac infer_d_check >>
     fs [FEVERY_FEMPTY])
 >- (imp_res_tac infer_d_check >>
     fs [check_env_def])
 >- (fs[GSYM bind_var_list2_append]>>
    match_mp_tac tenv_alpha_bind_var_list2>>
    rw[]>-
     metis_tac[tenv_alpha_convert,infer_d_check]>>
    fs[EXTENSION,MEM_MAP,PULL_EXISTS,EXISTS_PROD,convert_env2_def]));

val infer_prog_sound = Q.store_thm ("infer_prog_sound",
`!idecls ienv prog st1 tenv idecls' tenvT' menv' cenv' env' st2.
  (infer_prog idecls ienv prog st1 = (Success (idecls',tenvT',menv',cenv', env'), st2)) ∧
  env_rel tenv ienv
  ⇒
  type_prog T (convert_decls idecls) tenv prog (convert_decls idecls') (tenvT',(convert_menv menv'),cenv',(convert_env2 env')) ∧
  env_rel
  <|t:= (merge_mod_env tenvT' tenv.t);
    m:= (convert_menv menv' ⊌ tenv.m);
    c:= (merge_alist_mod_env cenv' tenv.c);
    v:=(bind_var_list2 (convert_env2 env') tenv.v)|>
  <|inf_t:= (merge_mod_env tenvT' tenv.t);
    inf_m:= (FUNION menv' ienv.inf_m);
    inf_c:= (merge_alist_mod_env cenv' tenv.c);
    inf_v:=(env'++ienv.inf_v)|>`,
 induct_on `prog` >>
 rw [infer_prog_def, success_eqns]
 >- rw [Once type_prog_cases, empty_decls_def, convert_decls_def, convert_menv_def, convert_env2_def,empty_inf_decls_def]
 >- (fs[env_rel_def,tenv_bvl_def]>>
     Cases_on`tenv.t` >>
     rw [merge_mod_env_def, merge_alist_mod_env_def,convert_env2_def,convert_menv_def]>>
     fs[bind_var_list2_def]>>
     metis_tac[])
 >- (fs[env_rel_def,tenv_bvl_def]>>
       Cases_on`tenv.t` >>
       rw [merge_mod_env_def, merge_alist_mod_env_def,convert_env2_def,convert_menv_def]>>
       fs[bind_var_list2_def]>>
       metis_tac[])
 >- (fs[env_rel_def,tenv_bvl_def]>>
       Cases_on`tenv.t` >>
       rw [merge_mod_env_def, merge_alist_mod_env_def,convert_env2_def,convert_menv_def]>>
       fs[bind_var_list2_def]>>
       metis_tac[])
 >- (rw [Once type_prog_cases] >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     imp_res_tac infer_top_sound >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT', menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     rw [] >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``type_top`` o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qabbrev_tac`tenv' = tenv with
     <|t := (merge_mod_env tenvT'' tenv.t);
     c := (merge_alist_mod_env cenv'' tenv.c);
     m := (convert_menv menv'' ⊌ tenv.m);
     v := bind_var_list2 (convert_env2 env'') tenv.v|>`>>
     fs[type_environment_component_equality,markerTheory.Abbrev_def]>>
     res_tac>> ntac 5 (pop_assum kall_tac)>>
     qmatch_assum_abbrev_tac`env_rel A B`>>
     first_x_assum(qspecl_then[`A`]mp_tac)>>unabbrev_all_tac>>fs[env_rel_def]>>
     strip_tac>>
     fs[convert_append_decls,extend_env_new_tops_def,bind_var_list2_append]>>
     qmatch_assum_abbrev_tac`type_prog T A B C D E `>>
     qexists_tac`E`>>
     qexists_tac`D`>>
     unabbrev_all_tac>>fs[append_new_top_tenv_def,convert_menv_def,convert_env2_def,o_f_FUNION])
  >- (`?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     imp_res_tac infer_top_sound >>
     `?decls' tenvT' menv' cenv' env'. v' = (decls',tenvT',menv',cenv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [success_eqns] >>
     rw [] >>
     qabbrev_tac`tenv' = tenv with
     <|t := (merge_mod_env tenvT'' tenv.t);
     c := (merge_alist_mod_env cenv'' tenv.c);
     m := (convert_menv menv'' ⊌ tenv.m);
     v := bind_var_list2 (convert_env2 env'') tenv.v|>`>>
     fs[type_environment_component_equality,markerTheory.Abbrev_def]>>
     res_tac>> ntac 4 (pop_assum kall_tac)>>
     qmatch_assum_abbrev_tac`env_rel A B`>>
     first_x_assum(qspecl_then[`A`]mp_tac)>>unabbrev_all_tac>>fs[env_rel_def]>>
     fs[convert_env2_def,convert_menv_def,o_f_FUNION,tenv_bvl_def] >>
     fs[GSYM bind_var_list2_append]>>
     metis_tac [FUNION_ASSOC, APPEND_ASSOC, merge_mod_env_assoc,
                semanticPrimitivesPropsTheory.merge_alist_mod_env_assoc]))

val _ = export_theory ();
