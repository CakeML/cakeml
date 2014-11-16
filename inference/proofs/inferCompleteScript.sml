open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib;
open infer_eSoundTheory;
open infer_eCompleteTheory;

val _ = new_theory "inferComplete";


(*
val tenv_invC_bind_tvar = store_thm("tenv_invC_bind_tvar",
  ``∀tvs s tenv tenvE.
      tenv_invC s tenv tenvE ⇒
      tenv_invC s tenv (bind_tvar tvs tenvE)``,
  rw[bind_tvar_def] >>
  fs[tenv_invC_def,lookup_tenv_def] >>
  rpt gen_tac >> strip_tac >>
  lookup_tenv_inc
  lookup_tenv_inc_tvs
  num_tvs_def
*)

val generalise_no_uvars = Q.prove (
`(!t m n s dbvars.
  check_t dbvars {} t
  ⇒ 
  ?s' t'. generalise m n s t = (0,s',t')) ∧
 (!ts m n s dbvars.
  EVERY (check_t dbvars {}) ts
  ⇒ 
  ?s' ts'. generalise_list m n s ts = (0,s',ts'))`,
 ho_match_mp_tac infer_tTheory.infer_t_induction >>
 rw [generalise_def, check_t_def]
 >- metis_tac [PAIR_EQ] >>
 rw [PULL_FORALL] >>
 res_tac >>
 pop_assum (qspecl_then [`s`, `n`, `m`] mp_tac) >>
 rw [] >>
 rw [] >>
 first_x_assum (qspecl_then [`s'`, `n`, `m`] mp_tac) >>
 rw [] >>
 rw []);

val infer_d_complete = Q.prove (
`!mn mdecls tdecls edecls tenvT menv cenv tenvE d mdecls' tdecls' edecls' tenvT' cenv' tenvE' tenv st.
  check_menv menv ∧
  check_env {} tenv ∧
  tenvC_ok cenv ∧
  tenv_invC FEMPTY tenv tenvE ∧
  num_tvs tenvE = 0 ∧
  type_d T mn (set mdecls,set tdecls,set edecls) tenvT (convert_menv menv) cenv tenvE d (set mdecls',set tdecls',set edecls') tenvT' cenv' tenvE'
  ⇒
  ?tenv' st' mdecls'' tdecls'' edecls''.
    set mdecls'' = set mdecls' ∧
    set tdecls'' = set tdecls' ∧
    set edecls'' = set edecls' ∧
    tenvE' = MAP (\(x,(n,t)). (x, (n, convert_t t))) tenv' ∧
    (* Need something relating tenv' with tenvE'. tenv_invC is not the right thing here. It's probably some mapping of unconvert *)
    infer_d mn (mdecls,tdecls,edecls) tenvT menv cenv tenv d st = 
      (Success ((mdecls'',tdecls'',edecls''), tenvT', cenv', tenv'), st')`,
 rw [type_d_cases] >>
 rw [infer_d_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def] >>
 fs [empty_decls_def]
 (* Let generalisation case *)
 >- (
   rw[PULL_EXISTS] >>
   (infer_e_complete |> CONJUNCT1 |> GEN_ALL
    |> REWRITE_RULE[GSYM AND_IMP_INTRO]
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars["st"]))) >>
   disch_then(qspecl_then[`init_infer_state`]mp_tac) >>
   `t_wfs init_infer_state.subst` by simp[init_infer_state_def,t_wfs_def] >>
   simp[init_infer_state_def] >>
   simp[GSYM init_infer_state_def] >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   disch_then(qspecl_then[`FEMPTY`,`[]`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     simp[sub_completion_def,pure_add_constraints_def] ) >>
   (* the tenv_invC hypothesis seems like it might be wrong? *)
   discharge_hyps >- cheat >>
   strip_tac >> simp[] >>
   (infer_p_complete |> CONJUNCT1
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   disch_then(qspecl_then[`s'`,`st'`]mp_tac) >>
   imp_res_tac (CONJUNCT1 infer_e_wfs) >>
   simp[] >>
   cheat)
 (* Non generalised let *)
 >- (
     (infer_e_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     rw [PULL_EXISTS] >>
     pop_assum (qspecl_then [`FEMPTY`, `menv`, `tenv`, `init_infer_state`, `[]`] mp_tac) >>
     rw [init_infer_state_def, t_wfs_def] >>
     `sub_completion 0 0 FEMPTY [] FEMPTY` by rw [sub_completion_def, pure_add_constraints_def] >>
     fs [] >>
     (infer_p_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     rw [] >>
     pop_assum (qspecl_then [`s'`, `st'`, `constraints'`] mp_tac) >>
     rw [] >>
     `t_wfs <|next_uvar := 0; subst := FEMPTY|>.subst` by rw [t_wfs_def] >>
     `t_wfs st'.subst` by metis_tac [infer_e_wfs] >>
     fs [] >>
     `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
     imp_res_tac infer_p_bindings >>
     pop_assum (qspecl_then [`[]`] assume_tac) >>
     fs [] >>
     (* because this is what sub completion does *)
     `check_t (num_tvs tenvE) {} (t_walkstar s' t') ∧ check_t (num_tvs tenvE) {} (t_walkstar s'' t'')` 
             by (conj_tac >>
                 match_mp_tac (GEN_ALL sub_completion_completes) >>
                 rw []
                 >- metis_tac [sub_completion_wfs]
                 >- (imp_res_tac (CONJUNCT1 infer_e_check_t) >>
                     fs [])
                 >- fs [sub_completion_def]
                 >- metis_tac [sub_completion_wfs]
                 >- (imp_res_tac (CONJUNCT1 infer_p_check_t) >>
                     fs [])
                 >- fs [sub_completion_def]) >>
     `t_walkstar s'' (t_walkstar s' t') = t_walkstar s'' (t_walkstar s'' t'')` by metis_tac [convert_bi_remove] >>
     `t_walkstar s'' t' = t_walkstar s'' t''` 
               by metis_tac [t_walkstar_SUBMAP, SUBMAP_REFL, t_compat_def] >> 
     imp_res_tac sub_completion_wfs >>
     `t_compat st''.subst s''` 
                  by metis_tac [pure_add_constraints_success, sub_completion_def, t_compat_def] >>
     `?si. t_unify st''.subst t' t'' = SOME si ∧ t_compat si s''` by metis_tac [t_compat_eqs_t_unify] >>
     qexists_tac `si` >>
     rw [] >>
     (* *)
     `EVERY (check_t 0 {}) (MAP (t_walkstar s'') (MAP SND tenv''))` 
                 by (rw [EVERY_MAP] >>
                     rw [EVERY_MEM] >>
                     match_mp_tac (CONJUNCT1 check_t_walkstar) >>
                     fs [t_compat_def] >>
                     imp_res_tac infer_p_check_t >>
                     fs [EVERY_MEM] >>
                     res_tac >>
                     PairCases_on `x` >>
                     fs [sub_completion_def]) >>
     fs [type_e_determ_def] >>
     cheat)                
     (*
     `∃s' t'. generalise_list 0 0 FEMPTY (MAP (t_walkstar si) (MAP SND tenv'')) = (0,s',t')` 
                by metis_tac [generalise_no_uvars] >>
     rw [tenv_add_tvs_def, ] >>
*)

 (* generalised letrec *)
 >- cheat
 (* Type definition *)
 >- (rw [PULL_EXISTS] >>
     PairCases_on `tenvT` >>
     fs [merge_mod_env_def, EVERY_MAP, EVERY_MEM, DISJOINT_DEF, EXTENSION] >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     CCONTR_TAC >>
     fs [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``] >>
     res_tac >> 
     fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD] >>
     metis_tac [])
 (* Exception definition *)
 >- metis_tac []);

val _ = export_theory ();
