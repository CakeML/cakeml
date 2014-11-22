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
open type_eDetermTheory

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
  generalise m n s t = (0,s,t)) ∧
 (!ts m n s dbvars.
  EVERY (check_t dbvars {}) ts
  ⇒ 
  generalise_list m n s ts = (0,s,ts))`,
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
 rw [] >>
 metis_tac [PAIR_EQ]);

val infer_d_complete = Q.prove (
`!mn mdecls tdecls edecls tenvT menv cenv d mdecls' tdecls' edecls' tenvT' cenv' tenv st.
  check_menv menv ∧
  check_env {} tenv ∧
  tenvC_ok cenv ∧
  type_d T mn (set mdecls,set tdecls,set edecls) tenvT (convert_menv menv) cenv (bind_var_list2 (convert_env2 tenv) Empty) d (set mdecls',set tdecls',set edecls') tenvT' cenv' (convert_env2 tenv')
  ⇒
  ?st' mdecls'' tdecls'' edecls''.
    set mdecls'' = set mdecls' ∧
    set tdecls'' = set tdecls' ∧
    set edecls'' = set edecls' ∧
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
     `num_tvs (bind_var_list2 (convert_env2 tenv) Empty) = 0`
               by rw [num_tvs_bvl2, num_tvs_def] >>
     `tenv_invC FEMPTY tenv (bind_var_list2 (convert_env2 tenv) Empty)`
               by metis_tac [tenv_invC_convert_env2] >>
     `∃t2 t' tenv' st st' s constrs s'.
       infer_e menv cenv tenv e init_infer_state = (Success t2,st) ∧
       infer_p cenv p st = (Success (t',tenv'),st') ∧
       t_unify st'.subst t2 t' = SOME s ∧
       sub_completion 0 st.next_uvar s constrs s' ∧
       t = convert_t (t_walkstar s' t') ∧
       t = convert_t (t_walkstar s' t2) ∧ t_wfs s ∧
       simp_tenv_invC s' 0 tenv' tenv''`
              by metis_tac [infer_pe_complete] >>
     rw [] >>
     imp_res_tac infer_p_bindings >>
     pop_assum (qspecl_then [`[]`] assume_tac) >>
     fs [] >>
     `tenv_inv FEMPTY tenv (bind_var_list2 (convert_env2 tenv) Empty)`
               by metis_tac [tenv_inv_convert_env2] >>
     imp_res_tac type_pe_determ_infer_e >>
     `EVERY (check_t 0 {}) (MAP (t_walkstar s) (MAP SND tenv'''))`
          by (fs [EVERY_MEM, MEM_MAP] >>
              rw [] >>
              res_tac >>
              PairCases_on `y'` >>
              fs []) >>
     imp_res_tac generalise_no_uvars >>
     pop_assum (qspecl_then [`FEMPTY`, `0`, `0`] mp_tac) >>
     rw [init_infer_state_def] >>
     simp[MAP_MAP_o,ZIP_MAP,combinTheory.o_DEF] >>
     rator_x_assum`convert_env2`mp_tac >>
     imp_res_tac type_p_pat_bindings >> rfs[] >>
     simp[convert_env2_def,tenv_add_tvs_def] >>
     pop_assum mp_tac >>
     simp[Once LIST_EQ_REWRITE,GSYM AND_IMP_INTRO,EL_MAP] >>
     ntac 2 strip_tac >>
     simp[Once LIST_EQ_REWRITE,GSYM AND_IMP_INTRO,EL_MAP,UNCURRY] >>
     ntac 2 strip_tac >>
     simp[Once LIST_EQ_REWRITE,EL_MAP] >>
     qx_gen_tac`n`>>strip_tac >>
     Cases_on`EL n tenv'` >>
     rpt(first_x_assum(qspec_then`n`mp_tac)) >> simp[] >>
     Cases_on`r`>>simp[] >> rw[] >>
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
     rw []
     >- (PairCases_on `x` >>
         fs [] >>
         CCONTR_TAC >>
         fs [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``] >>
         res_tac >> 
         fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD] >>
         metis_tac [])
     >- (Cases_on `tenv'` >>
         fs [convert_env2_def]))
 (* Exception definition *)
 >- (Cases_on `tenv'` >>
     fs [convert_env2_def])
 >- metis_tac []
 >- (Cases_on `tenv'` >>
     fs [convert_env2_def]));

val _ = export_theory ();
