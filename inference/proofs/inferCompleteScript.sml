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

(* this might be totally wrong

val generalise_uvars = prove(
  ``(∀t m n s u d. FINITE u ∧ check_t d u t ⇒ FST(generalise m n s t) ≤ n + CARD (u DIFF (FDOM s))) ∧
    (∀ts m n s u d. FINITE u ∧ EVERY (check_t d u) ts ⇒ FST(generalise_list m n s ts) ≤ CARD (u DIFF (FDOM s)))``,
  ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw[generalise_def,check_t_def] >> rw[] >>
  TRY BasicProvers.CASE_TAC >> simp[] >>
  fsrw_tac[boolSimps.ETA_ss][] >- metis_tac[FST] >- (
    fs[FLOOKUP_DEF] >>
    `FINITE (FDOM s)` by simp[] >>
    asm_simp_tac std_ss [GSYM(MP_CANON CARD_DIFF)] >>
    `∃z. u DIFF FDOM s = n INSERT z ∧ n ∉ z ∧ FINITE z` by (
      qexists_tac`u DIFF (n INSERT (FDOM s))` >>
      simp[EXTENSION] >> metis_tac[] ) >>
    first_x_assum (CHANGED_TAC o SUBST1_TAC) >>
    simp[] ) >>
  last_x_assum(qspecl_then[`m`,`n`,`s`]mp_tac) >> simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`m`,`num_gen+n`,`s'`]mp_tac) >> simp[] >> strip_tac >>
  res_tac >> simp[]

  fs[GSYM AND_IMP_INTRO] >>
  rpt(first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th))) >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th))

  res_tac
  metis_tac[FST,arithmeticTheory.ADD_ASSOC,arithmeticTheory.ADD_COMM]
*)


val infer_d_complete = Q.prove (
`!mn mdecls tdecls edecls tenvT menv cenv d mdecls' tdecls' edecls' tenvT' cenv' tenv st.
  check_menv menv ∧
  check_env {} tenv ∧
  tenvC_ok cenv ∧
  check_env ∅ tenv' ∧
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
   (infer_pe_complete
    |> (CONV_RULE(LAND_CONV(lift_conjunct_conv(can(match_term``type_p a b c d e ∧ type_e f g h i j``)))))
    |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> GEN_ALL
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   simp[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] >>
   disch_then(qspec_then`tenv`mp_tac) >>
   discharge_hyps >- (
     fs[convert_env2_def,tenv_add_tvs_def,tenv_invC_def,bind_tvar_rewrites] >>
     rpt gen_tac >> strip_tac >>
     qmatch_assum_abbrev_tac`lookup_tenv x tvs tenvx = SOME y` >>
     `tenv_ok tenvx ∧ num_tvs tenvx = 0` by (
       conj_tac >- (
         simp[Abbr`tenvx`] >>
         match_mp_tac tenv_ok_bind_var_list2 >>
         simp[typeSoundInvariantsTheory.tenv_ok_def,EVERY_MAP,UNCURRY] >>
         simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
         match_mp_tac check_t_to_check_freevars >>
         fs[check_env_def,EVERY_MEM,num_tvs_def] >>
         res_tac >> fs[]) >>
       simp[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] ) >>
     qspecl_then[`tvs`,`FST y`,`tenvx`,`x`]mp_tac lookup_tenv_inc_tvs >>
     simp[Abbr`y`] >>
     simp[GSYM bvl2_lookup,Abbr`tenvx`] >>
     disch_then(qspec_then`t'`mp_tac) >> simp[] >>
     Q.ISPECL_THEN[`λ(tvs:num,t). (tvs,convert_t t)`,`tenv`]mp_tac ALOOKUP_MAP >>
     simp[UNCURRY,Once LAMBDA_PROD] >> disch_then kall_tac >>
     simp[EXISTS_PROD] >> strip_tac >> simp[] >>
     simp[t_walkstar_FEMPTY] >>
     fs[check_env_def,EVERY_MEM] >>
     imp_res_tac ALOOKUP_MEM >>
     res_tac >> fs[] >>
     imp_res_tac check_t_to_check_freevars >>
     simp[] >>
     metis_tac[check_t_empty_unconvert_convert_id] ) >>
   simp[] >> strip_tac >> simp[] >>
   imp_res_tac infer_p_bindings >> fs[] >>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   fs[init_infer_state_def] >>
   qspecl_then[`0`,`s`,`MAP SND tenv'''`]mp_tac generalise_complete >> simp[] >>
   disch_then(qspec_then`st'.next_uvar`mp_tac) >>
   discharge_hyps >- (
     conj_tac >- (
       match_mp_tac t_unify_check_s >>
       CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       fs[GSYM init_infer_state_def] >>
       `t_wfs (init_infer_state.subst)` by rw[init_infer_state_def,t_wfs_def] >>
       `t_wfs st.subst` by imp_res_tac infer_e_wfs >>
       `t_wfs st'.subst` by imp_res_tac infer_p_wfs >>
       imp_res_tac infer_p_check_t >> simp[] >>
       imp_res_tac(CONJUNCT1 infer_e_check_t) >>
       conj_tac >- (
         match_mp_tac (MP_CANON(CONJUNCT1 check_t_more5)) >>
         rfs[init_infer_state_def] >>
         first_assum(match_exists_tac o concl) >>
         imp_res_tac infer_p_next_uvar_mono >>
         simp[SUBSET_DEF] ) >>
       match_mp_tac (CONJUNCT1 infer_p_check_s) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[GSYM check_cenv_tenvC_ok] >>
       match_mp_tac (CONJUNCT1 infer_e_check_s) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[GSYM check_cenv_tenvC_ok] >>
       simp[init_infer_state_def] >>
       simp[check_s_def] ) >>
     imp_res_tac infer_p_check_t >>
     fs[EVERY_MEM,EVERY_MAP,FORALL_PROD] >>
     metis_tac[] ) >>
   strip_tac >> simp[ZIP_MAP] >>
   simp[MAP_MAP_o,combinTheory.o_DEF] >>
   fs[convert_env2_def,tenv_add_tvs_def] >>
   qpat_assum`MAP X Y = MAP A B`mp_tac >>
   simp[Once LIST_EQ_REWRITE,EL_MAP,UNCURRY,GSYM AND_IMP_INTRO] >>
   strip_tac >> strip_tac >>
   simp[LIST_EQ_REWRITE,EL_MAP] >>
   imp_res_tac type_p_pat_bindings >>
   `MAP FST tenv'' = MAP FST tenv'''` by metis_tac[APPEND_NIL] >>
   conj_asm1_tac >- metis_tac[LENGTH_MAP] >>
   qx_gen_tac`n` >> strip_tac >>
   first_x_assum(qspec_then`n`mp_tac) >> simp[] >> strip_tac >>
   `∃x y c z f g h. (EL n tenv' = (x,y,c)) ∧ (EL n tenv'' = (z,f)) ∧ (EL n tenv''' = (g,h))` by metis_tac[pair_CASES] >>
   simp[] >> rpt BasicProvers.VAR_EQ_TAC >>
   rfs[] >> fs[] >> rpt BasicProvers.VAR_EQ_TAC >>
   conj_asm1_tac >- (
     qpat_assum`MAP X Y = Z`mp_tac >>
     simp[Once LIST_EQ_REWRITE,EL_MAP] >>
     disch_then(qspec_then`n`mp_tac) >> simp[] ) >>
   BasicProvers.VAR_EQ_TAC >>
   imp_res_tac generalise_subst_empty >>
   pop_assum mp_tac >>
   simp[MAP_MAP_o,Once LIST_EQ_REWRITE,EL_MAP] >>
   disch_then(qspec_then`n`mp_tac) >> simp[] >>
   disch_then kall_tac >>
   rator_x_assum`simp_tenv_invC`mp_tac >>
   simp[simp_tenv_invC_def] >>
   `ALL_DISTINCT (MAP FST tenv'')` by metis_tac[] >>
   imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
   ntac 2 (pop_assum mp_tac) >>
   simp[MEM_EL,PULL_EXISTS] >>
   disch_then(qspec_then`n`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"]))) >>
   simp[] >> strip_tac >>
   disch_then(qspec_then`n`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n'"]))) >>
   simp[] >> strip_tac >>
   simp[GSYM FORALL_AND_THM] >>
   disch_then(qspec_then`g`mp_tac) >> simp[] >>
   strip_tac >>
   `check_t y ∅ c'` by (
     rator_x_assum`check_env`mp_tac >>
     simp[check_env_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
     disch_then(qspec_then`n`mp_tac)>>simp[] ) >>
   imp_res_tac check_t_empty_unconvert_convert_id >>
   reverse conj_tac >- (
     pop_assum(SUBST1_TAC o SYM) >>
     first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
     (* need more assumptions from infer_pe_complete about constrs? )
     cheat ) >>
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
     `EVERY (λ(n,t). check_t 0 ∅ (t_walkstar s t)) tenv'''` by metis_tac [type_pe_determ_infer_e] >>
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
     fs[simp_tenv_invC_def] >>
     imp_res_tac type_p_pat_bindings >>
     `ALL_DISTINCT (MAP FST tenv'')` by metis_tac[] >>
     imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
     first_x_assum(qspecl_then[`SND (EL n tenv''')`,`FST (EL n tenv''')`]mp_tac) >>
     first_x_assum(qspecl_then[`SND (EL n tenv'')`,`FST (EL n tenv'')`]mp_tac) >> simp[] >>
     discharge_hyps >- metis_tac[MEM_EL] >> strip_tac >>
     discharge_hyps >- metis_tac[MEM_EL] >> strip_tac >>
     res_tac >> rfs[] >> rw[] >>
     (* not sure of strategy from this point *)
     fs[sub_completion_def] >>
     imp_res_tac pure_add_constraints_success >>
     fs[t_compat_def] >>
     first_x_assum(qspec_then`SND (EL n tenv''')`(assume_tac o SYM)) >> fs[] >>
     fs[EVERY_MEM] >>
     first_x_assum(qspec_then`EL n tenv'''`mp_tac) >>
     discharge_hyps >- metis_tac[MEM_EL] >> simp[UNCURRY] >> strip_tac >>
     imp_res_tac t_walkstar_no_vars >> fs[] >>
     qsuff_tac`unconvert_t (convert_t r') = r'`>-metis_tac[]>>
     match_mp_tac (GEN_ALL check_t_empty_unconvert_convert_id) >>
     fs [check_env_def, EVERY_EL] >>
     res_tac >>
     pop_assum mp_tac >>
     ASM_REWRITE_TAC [] >>
     rw [] >>
     metis_tac [])
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
