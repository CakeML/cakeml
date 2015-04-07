open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib BasicProvers;

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
`!mn mdecls tdecls edecls tenvT menv cenv d mdecls' tdecls' edecls' tenvT' cenv' tenv tenv' st itenv.
  check_menv menv ∧
  (*check_env ∅ tenv ∧ 
  don't know what to put here, should be the equivalent of check_env for the 
  type system but not really tenv_ok*)
  (*This should be implied by the above and generalization condition*)
  check_env ∅ itenv ∧
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  tenvC_ok cenv ∧
  type_d T mn (set mdecls,set tdecls,set edecls) tenvT (convert_menv menv) cenv (bind_var_list2 tenv Empty) d (mdecls',tdecls',edecls') tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty)
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv'.
    set mdecls'' = mdecls' ∧
    set tdecls'' = tdecls' ∧
    set edecls'' = edecls' ∧
    infer_d mn (mdecls,tdecls,edecls) tenvT menv cenv itenv d st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', cenv', itenv'), st') ∧
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    MAP FST itenv' = MAP FST tenv' ∧
    check_env {} itenv'`,
 rw [type_d_cases] >>
 rw [infer_d_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def] >>
 fs [empty_decls_def,check_env_def]
 (* Let generalisation case *)
 >- (
   rw[PULL_EXISTS] >>
   (infer_pe_complete
    |> (CONV_RULE(LAND_CONV(lift_conjunct_conv(can(match_term``type_p a b c d e ∧ type_e f g h i j``)))))
    |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> GEN_ALL
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   simp[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] >>
   disch_then(qspec_then`itenv`mp_tac) >>
   discharge_hyps >- (
     fs[tenv_alpha_def,tenv_invC_def,bind_tvar_rewrites] >>
     rpt gen_tac >> strip_tac >>
     qmatch_assum_abbrev_tac`lookup_tenv x tvs tenvx = SOME y` >>
     `tenv_ok tenvx ∧ num_tvs tenvx = 0` by (
       conj_tac >- (
         simp[Abbr`tenvx`] >>
         match_mp_tac tenv_ok_bind_var_list2 >>
         simp[typeSoundInvariantsTheory.tenv_ok_def,EVERY_MAP,UNCURRY] >>
         simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
         simp[num_tvs_def] >>
         cheat
         (*See first comment in thm statement
         match_mp_tac check_t_to_check_freevars >>
         fs[check_env_def,EVERY_MEM,num_tvs_def] >>
         res_tac >> fs[]*)) >>
       simp[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] ) >>
     qspecl_then[`tvs`,`FST y`,`tenvx`,`x`]mp_tac lookup_tenv_inc_tvs >>
     simp[Abbr`y`] >>
     disch_then(qspec_then`t'`mp_tac) >> simp[] >>
     disch_then(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
     strip_tac >> conj_tac >- metis_tac[] >> simp[] >>
     reverse IF_CASES_TAC >- metis_tac[] >> fs[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     `tvs = tvs + 0` by simp[] >> pop_assum SUBST1_TAC >>
     match_mp_tac(MP_CANON(CONJUNCT2 check_t_more2)) >>
     first_assum ACCEPT_TAC ) >>
   discharge_hyps_keep >- simp[check_env_def] >>
   strip_tac >> simp[] >>
   imp_res_tac infer_p_bindings >> fs[] >>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   fs[init_infer_state_def] >>
   qspecl_then[`0`,`s`,`MAP SND tenv'`]mp_tac generalise_complete >> simp[] >>
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
         rfs[check_env_def] >>
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
       simp[check_s_def] >>
       simp[check_env_def]) >>
     imp_res_tac infer_p_check_t >>
     fs[EVERY_MEM,EVERY_MAP,FORALL_PROD] >>
     metis_tac[] ) >>
   strip_tac >> simp[ZIP_MAP] >>
   simp[MAP_MAP_o,combinTheory.o_DEF] >>
   rfs[convert_env2_def,tenv_add_tvs_def] >>
   simp[MAP_MAP_o,EVERY_MAP,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
   imp_res_tac type_p_pat_bindings >> simp[] >>
   reverse conj_asm2_tac >- (
     fs[sub_completion_def] >>
     imp_res_tac infer_p_check_t >>
     fs[EVERY_MEM,FORALL_PROD] >>
     rw[] >> res_tac >>
     `count st'.next_uvar ∩ COMPL (FDOM last_sub) = {}` by (
       simp[EXTENSION] >> fs[SUBSET_DEF] >>
       metis_tac[] ) >>
     (check_t_less |> CONJUNCT1 |> Q.GENL[`s`,`uvars`,`n`]
      |> Q.SPECL[`a`,`count (st':(num|->infer_t) infer_st).next_uvar`,`last_sub`]
      |> mp_tac) >>
     simp[] ) >>
   simp[tenv_alpha_def] >>
   conj_tac >- (
     simp[tenv_inv_def] >>
     simp[LAMBDA_PROD,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup] >>
     rw[] >>
     fs[simp_tenv_invC_def] >>
     res_tac >> res_tac >> simp[] >> fs[] >>
     rpt BasicProvers.VAR_EQ_TAC >>
     reverse IF_CASES_TAC >- (
       imp_res_tac ALOOKUP_MEM >>
       fs[EVERY_MEM,FORALL_PROD] >>
       metis_tac[] ) >>
     `convert_t (t_walkstar s' p2) = t` by (
       metis_tac[check_freevars_empty_convert_unconvert_id] ) >>
     BasicProvers.VAR_EQ_TAC >>
     cheat ) >>
   simp[tenv_invC_def] >>
   simp[LAMBDA_PROD,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup] >>
   rw[] >>
   fs[simp_tenv_invC_def] >>
   res_tac >> simp[] >>
   reverse IF_CASES_TAC >- (
     imp_res_tac ALOOKUP_MEM >>
     fs[EVERY_MEM,FORALL_PROD] >>
     metis_tac[] ) >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   simp[num_tvs_bvl2,num_tvs_def] >>
   (*
   qpat_assum`MAP X Y = MAP A B`mp_tac >>
   simp[Once LIST_EQ_REWRITE,EL_MAP,UNCURRY,GSYM AND_IMP_INTRO] >>
   strip_tac >> strip_tac >>
   simp[LIST_EQ_REWRITE,EL_MAP] >>
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
     (* need more assumptions from infer_pe_complete about constrs? *)
     cheat ) >>
   *)
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
     >- (fs[tenv_generalize_def]))
 (* Exception definition *)
 >- fs[tenv_generalize_def]
 >- metis_tac []
 >- fs[tenv_generalize_def]);
*)

val tenv_alpha_bind_var_list2 = prove(``
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧
  set (MAP FST itenv) = set (MAP FST tenv) ∧  
  tenv_alpha itenv' (bind_var_list2 tenv' Empty)
  ⇒ 
  tenv_alpha (itenv++itenv') (bind_var_list2 (tenv++tenv') Empty)``,cheat)

(*  rw[tenv_alpha_def,tenv_invC_def,tenv_inv_def]>>
  fs[GSYM bvl2_lookup,ALOOKUP_APPEND]>>
  EVERY_CASE_TAC >> TRY(metis_tac[])>>
  fs[]>>
  res_tac>>fs[num_tvs_bvl2]>>
  Cases_on`x'`>>res_tac>>fs[]>>
  metis_tac[ALOOKUP_MEM,ALOOKUP_NONE,optionTheory.NOT_SOME_NONE])*)

val infer_ds_complete = prove(``
!ds mn mdecls tdecls edecls tenvT menv cenv d mdecls' tdecls' edecls' tenvT' cenv' tenv tenv' st itenv.
  check_menv menv ∧
  (*check_env ∅ tenv ∧ 
  don't know what to put here, should be the equivalent of check_env for the 
  type system but not really tenv_ok*)
  (*This should be implied by the above and generalization condition*)
  check_env ∅ itenv ∧  
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧ 
  (*check_env ∅ tenv' ∧ *)
  type_ds T mn (set mdecls,set tdecls,set edecls) tenvT (convert_menv menv) cenv (bind_var_list2 tenv Empty) ds (mdecls',tdecls',edecls') tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty)
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv'.
    set mdecls'' = mdecls' ∧
    set tdecls'' = tdecls' ∧
    set edecls'' = edecls' ∧
    infer_ds mn (mdecls,tdecls,edecls) tenvT menv cenv itenv ds st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', cenv', itenv'), st') ∧ 
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧ 
    MAP FST itenv' = MAP FST tenv' ∧  
    (*maybe implied as well*)
    check_env ∅ itenv'``,
  Induct>-
  (rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[tenv_alpha_def,bind_var_list2_def,tenv_invC_def,lookup_tenv_def,tenv_inv_def])
  >>
  rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[]>>
  fs[empty_decls_def] >>
    (infer_d_complete|>
      CONV_RULE(
        STRIP_QUANT_CONV(LAND_CONV(
          lift_conjunct_conv(same_const``type_d`` o fst o strip_comb))))
    |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    |> (fn th => first_assum(mp_tac o MATCH_MP th)))>>
  disch_then (Q.ISPECL_THEN [`st`,`itenv`] mp_tac)>>
  discharge_hyps>-
    fs[check_env_def]>>
  rw[]>>
  fs[PULL_EXISTS]>>
  fs[GSYM AND_IMP_INTRO]>>
  first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th))>>
  `tenvC_ok (merge_alist_mod_env ([],cenv'') cenv)` by
    (fs[tenvC_ok_merge]>>
    imp_res_tac type_d_ctMap_ok >>
    metis_tac[ctMap_ok_tenvC_ok,MAP_REVERSE,ALL_DISTINCT_REVERSE])>>
  `tenvT_ok (merge_mod_env (FEMPTY,tenvT'') tenvT)` by 
    (match_mp_tac tenvT_ok_merge>>
    fs[typeSoundInvariantsTheory.tenvT_ok_def]>>
    metis_tac[FEVERY_FEMPTY,type_d_tenvT_ok])>>
  fs[GSYM bind_var_list2_append]>>
  FULL_SIMP_TAC bool_ss [UNION_APPEND,union_decls_def] >>
  `tenv_alpha (itenv'++itenv) (bind_var_list2 (tenv''++tenv) Empty)` by 
     metis_tac[tenv_alpha_bind_var_list2]>>
  `check_env {} (itenv'++itenv)` by 
    fs[check_env_def]>>
  rpt
   (disch_then (fn th => first_x_assum (mp_tac o MATCH_MP th)))>>
  disch_then (qspec_then `st'` strip_assume_tac)>>
  fs[append_decls_def]>>
  fs[check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2])

val _ = export_theory ();
