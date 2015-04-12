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

val infer_d_complete = Q.prove (`
!mn (mdecls:'a list) tdecls edecls tenvT menv cenv d (mdecls':'a->bool) tdecls' edecls' tenvT' cenv' tenv tenv' st itenv tenvM.
  tenv_ok (bind_var_list2 tenv Empty) ∧
  tenvM_ok tenvM ∧
  check_env ∅ itenv ∧
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧
  check_menv menv ∧
  tenvC_ok cenv ∧
  type_d T mn (set mdecls,set tdecls,set edecls) tenvT tenvM cenv (bind_var_list2 tenv Empty) d (mdecls',tdecls',edecls') tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧
  menv_alpha menv tenvM
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
   disch_then(qspecl_then[`menv`,`itenv`]mp_tac) >>
   discharge_hyps >- (
     fs[tenv_alpha_def,tenv_invC_def,bind_tvar_rewrites] >>
     rpt gen_tac >> strip_tac >>
     qmatch_assum_abbrev_tac`lookup_tenv x tvs tenvx = SOME y` >>
     `num_tvs tenvx = 0` by 
       simp[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     qspecl_then[`tvs`,`FST y`,`tenvx`,`x`]mp_tac lookup_tenv_inc_tvs >>
     simp[Abbr`y`] >>
     disch_then(qspec_then`t'`mp_tac) >> simp[] >>
     disch_then(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
     strip_tac >>
     metis_tac[])
     (* conj_tac >- metis_tac[] >> simp[] >>
     reverse IF_CASES_TAC >- metis_tac[] >> fs[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     `tvs = tvs + 0` by simp[] >> pop_assum SUBST1_TAC >>
     match_mp_tac(MP_CANON(CONJUNCT2 check_t_more2)) >>
     first_assum ACCEPT_TAC *) >>
   discharge_hyps_keep >- simp[check_env_def] >>
   simp[]>>
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
     fs[tenv_alpha_def]>>
     `tenv_inv last_sub itenv (bind_tvar a (bind_var_list2 tenv Empty))` by metis_tac [tenv_inv_empty_to,tenv_inv_extend_tvar_empty_subst] >>
     `type_e tenvM cenv (bind_tvar a (bind_var_list2 tenv Empty)) e (convert_t (t_walkstar last_sub t'))` by 
       (match_mp_tac (infer_e_sound|>CONJUNCT1)>>
       first_assum (match_exists_tac o concl)>>
       fs[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def,t_wfs_def,check_cenv_tenvC_ok]>>
       fs[sub_completion_def]>>
       imp_res_tac infer_p_constraints>>
       imp_res_tac infer_p_next_uvar_mono>>
       `pure_add_constraints st'.subst [t',t''] s` by
         fs[pure_add_constraints_def]>>
       qexists_tac`ts++[t',t'']++ec1`>>
       CONJ_TAC>-
         metis_tac[pure_add_constraints_append]>>
       fs[SUBSET_DEF]>>simp[])>>
     `type_p a cenv p (convert_t (t_walkstar last_sub t'')) (convert_env last_sub tenv')` by 
       (match_mp_tac(infer_p_sound|>CONJUNCT1)>>
       first_assum (match_exists_tac o concl)>>
       imp_res_tac infer_e_wfs>>
       fs[t_wfs_def,check_cenv_tenvC_ok,sub_completion_def]>>
       `pure_add_constraints st'.subst [t',t''] s` by
         fs[pure_add_constraints_def]>>
       metis_tac[pure_add_constraints_append])>>
     `t_walkstar last_sub t' = t_walkstar last_sub t''`
             by (imp_res_tac infer_e_wfs >>
                 imp_res_tac infer_p_wfs >>
                 imp_res_tac t_unify_wfs >>
                 match_mp_tac sub_completion_apply>>
                 `t_wfs FEMPTY` by fs[t_wfs_def]>>
                 fs[]>>rfs[]>>
                 metis_tac[t_unify_apply])>>
     pop_assum SUBST_ALL_TAC>>
     res_tac>>
     fs[weakE_def,convert_env_def]>>
     first_x_assum (qspec_then `x` mp_tac)>>
     fs[ALOOKUP_MAP])>>
   (*TENVINVC*)
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
   imp_res_tac generalise_subst>>
   `t_walkstar last_sub t'''' = infer_subst b (t_walkstar s t'''')` by
     (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
     imp_res_tac ALOOKUP_MEM>>
     fs[MEM_EL]>>
     metis_tac[SND])>>
   fs[sub_completion_def]>>
   Q.ISPECL_THEN [`tvs`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>discharge_hyps
   >-
     (fs[]>>
     `t_wfs FEMPTY` by fs[t_wfs_def]>>
     imp_res_tac infer_e_wfs>>
     imp_res_tac infer_p_wfs>>
     imp_res_tac t_unify_wfs>>
     rfs[]>>
     metis_tac[pure_add_constraints_wfs])
   >>
     rw[]>>
     pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND tenv')`,`[]`,`FEMPTY`,`a`,`b`,`MAP (t_walkstar last_sub) (MAP SND tenv')`] mp_tac)>>
     discharge_hyps_keep
     >-
       (fs[]>>
       imp_res_tac (infer_e_check_t |>CONJUNCT1)>>
       fs[check_env_def]>>rfs[]>>
       first_assum (mp_tac o (MATCH_MP (infer_e_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       simp[t_wfs_def]>>
       disch_then (qspec_then`0` mp_tac)>>
       discharge_hyps>-
         fs[check_env_def,check_s_def,check_cenv_tenvC_ok]>>
       strip_tac>>fs[check_s_def]>>
       imp_res_tac (infer_p_check_t |> CONJUNCT1)>>
       first_assum (mp_tac o (MATCH_MP (infer_p_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       disch_then(qspec_then`0` mp_tac)>>
       discharge_hyps>-
         (fs[check_env_def,check_s_def,check_cenv_tenvC_ok]>>
         imp_res_tac infer_e_wfs>>
         fs[t_wfs_def])
       >>
       strip_tac>>
       fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
       fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
       ntac 2 strip_tac>>
       CONJ_ASM2_TAC>-
         metis_tac[check_t_t_vars]
       >>
       first_x_assum (qspec_then `y'` assume_tac)>>rfs[]>>
       fs[UNCURRY]>>
       match_mp_tac t_walkstar_check>> fs[]>>
       reverse CONJ_TAC>-
         (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
         HINT_EXISTS_TAC>>
         fs[])
       >>
       match_mp_tac (check_s_more3 |> MP_CANON)>>
       qexists_tac `count st'.next_uvar`>>
       fs[]>>
       match_mp_tac t_unify_check_s>>
       CONV_TAC (STRIP_QUANT_CONV (lift_conjunct_conv is_eq)) >>
       first_assum (match_exists_tac o concl)>>
       fs[]>>CONJ_TAC>-
         (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
         qexists_tac`count st.next_uvar`>>
         fs[]>>
         imp_res_tac infer_e_next_uvar_mono>>
         imp_res_tac infer_p_next_uvar_mono>>
         fs[SUBSET_DEF]>>
         DECIDE_TAC)
       >>
       `t_wfs FEMPTY` by fs[t_wfs_def]>>
       imp_res_tac infer_p_wfs >>
       imp_res_tac infer_e_wfs>>fs[])
    >> 
       rw[]>>
       qexists_tac`subst'`>>fs[]>>
       CONJ_ASM1_TAC>-
         fs[EVERY_MEM]
       >>
       Q.ISPECL_THEN [`s'`,`b`,`subst'`,`tvs`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
       discharge_hyps>-
         (fs[SUBSET_DEF]>>
         rw[]>>
         fs[IN_FRANGE]>>
         metis_tac[pure_add_constraints_wfs])>>
       rw[]>>
       pop_assum kall_tac>>
       pop_assum(qspec_then `t_walkstar s t''''` mp_tac)>>
       discharge_hyps>-
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
         `t'''' = SND (x,t'''')` by fs[]>>
         metis_tac[])
       >>
       rw[]>>
       metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success])
 (* Non generalised let *)
 >- (
     simp[PULL_EXISTS] >>
     (infer_pe_complete
      |> CONV_RULE(LAND_CONV(lift_conjunct_conv(same_const``type_e`` o fst o strip_comb)))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> GEN_ALL
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     simp[GSYM AND_IMP_INTRO]>>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th))>>
     disch_then(qspecl_then[`menv`,`itenv`] mp_tac)>>
     simp[AND_IMP_INTRO]>>
     discharge_hyps >- (
       fs[tenv_alpha_def,check_env_def] ) >>
     strip_tac >> simp[] >>
     imp_res_tac infer_p_bindings >>
     pop_assum (qspecl_then [`[]`] assume_tac) >>
     fs [] >>
     (type_pe_determ_infer_e
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``type_pe_determ`` o fst o strip_comb))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     simp[GSYM AND_IMP_INTRO] >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[check_env_def] >>
     discharge_hyps >- fs[tenv_alpha_def] >>
     strip_tac >>
     `EVERY (check_t 0 {}) (MAP (t_walkstar s) (MAP SND tenv'))` by (
       simp[EVERY_MAP,LAMBDA_PROD] ) >>
     imp_res_tac generalise_no_uvars >>
     pop_assum (qspecl_then [`FEMPTY`, `0`, `init_infer_state.next_uvar`] mp_tac) >>
     simp[MAP_MAP_o,ZIP_MAP,combinTheory.o_DEF] >>
     disch_then kall_tac >>
     simp[EVERY_MAP,LAMBDA_PROD,UNCURRY,FST_pair] >>
     reverse conj_tac >- (
       simp[tenv_add_tvs_def,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
       imp_res_tac type_p_pat_bindings >> fs[] ) >>
     simp[tenv_alpha_def] >>
     conj_tac >- (
       simp[tenv_inv_def,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup,tenv_add_tvs_def] >>
       rw[] >> fs[simp_tenv_invC_def] >>
       res_tac >> res_tac >> simp[] >>
       reverse IF_CASES_TAC >- (
         fs[EVERY_MEM,FORALL_PROD] >>
         imp_res_tac ALOOKUP_MEM >>
         metis_tac[] ) >>
       simp[LENGTH_NIL] >>
       simp[deBruijn_subst_nothing] >>
       fs[] >> rw[] >>
       fs[sub_completion_def]>>
       imp_res_tac pure_add_constraints_success>>
       qpat_assum `unconvert_t t = B` (assume_tac o Q.AP_TERM `convert_t`) >>
       imp_res_tac t_walkstar_SUBMAP>>
       first_x_assum(qspec_then `p2` SUBST_ALL_TAC)>>
       metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])>>
     simp[tenv_invC_def,GSYM bvl2_lookup,tenv_add_tvs_def,PULL_EXISTS,ALOOKUP_MAP] >>
     rw[] >>
     qexists_tac`0` >>
     fs[simp_tenv_invC_def] >>
     res_tac >> res_tac >> simp[] >>
     reverse IF_CASES_TAC >- (
       fs[EVERY_MEM,FORALL_PROD] >>
       imp_res_tac ALOOKUP_MEM >>
       metis_tac[] ) >>
     simp[LENGTH_NIL,infer_deBruijn_subst_id] >>
     fs[sub_completion_def]>>
     imp_res_tac pure_add_constraints_success>>
     qpat_assum `unconvert_t t = B` (assume_tac o Q.AP_TERM `convert_t`) >>
     imp_res_tac t_walkstar_SUBMAP>>
     first_x_assum(qspec_then `t''''` SUBST_ALL_TAC)>>
     metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])
 (* generalised letrec *)
 >- (
   simp[PULL_EXISTS] >>
   imp_res_tac type_funs_distinct >> fs[FST_triple] >>
   imp_res_tac type_funs_MAP_FST >>
   imp_res_tac type_funs_Tfn>>
   simp[init_infer_state_def,ETA_AX] >>
   qpat_abbrev_tac`itenv2 = x ++ itenv` >>
   qpat_abbrev_tac`st:(num|->infer_t)infer_st = X Y` >>
   `st.subst = FEMPTY` by simp[Abbr`st`] >>
   `t_wfs st.subst` by simp[t_wfs_def] >>
   `st.next_uvar = LENGTH funs` by ( simp[Abbr`st`] ) >>
   simp[LENGTH_COUNT_LIST] >>
   `EVERY (check_freevars tvs []) (MAP SND tenv'')` by
     (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
     rw[]>>
     `ALOOKUP tenv'' p_1 = SOME e` by 
       metis_tac[ALOOKUP_ALL_DISTINCT_MEM]>>
     res_tac>>
     fs[num_tvs_bind_var_list,bind_tvar_def]>>
     Cases_on`tvs=0`>>fs[num_tvs_bvl2,num_tvs_def])>>
   Q.ISPECL_THEN [`init_infer_state`,`[]:(infer_t,infer_t) alist`,`FEMPTY:num|->infer_t`,`MAP SND tenv''`,`tvs`] mp_tac extend_multi_props>>
   discharge_hyps>-
       fs[init_infer_state_def,t_wfs_def,pure_add_constraints_def,count_def]
   >>
   LET_ELIM_TAC>>
   first_assum(mp_tac o MATCH_MP(last(CONJUNCTS infer_e_complete))) >>
   disch_then(qspecl_then[`s'`,`menv`,`itenv2`,`st`,`new_constraints`]mp_tac) >>
   discharge_hyps>-
      (fs[]>>
      conj_tac >- (
       simp[Abbr`itenv2`,MAP2_MAP,LENGTH_COUNT_LIST,check_env_merge] >>
       reverse conj_tac >- (
         match_mp_tac (MP_CANON check_env_more) >>
         qexists_tac`0` >> simp[] >> simp[check_env_def] ) >>
       simp[check_env_def,EVERY_MAP] >>
       simp[EVERY_MEM,MEM_ZIP,FORALL_PROD,LENGTH_COUNT_LIST,EL_MAP,PULL_EXISTS] >>
       simp[EL_COUNT_LIST,check_t_def] ) >>
      fs[init_infer_state_def]>>
      `LENGTH tenv'' = LENGTH funs` by
        metis_tac[LENGTH_MAP]>>
      rw[]
      >-
        (fs[sub_completion_def]>>
        fs[num_tvs_bind_var_list,bind_tvar_def]>>
        IF_CASES_TAC>>fs[num_tvs_bvl2,num_tvs_def]>>
        fs[Abbr`targs`,EL_MAP,EVERY_EL]>>
        metis_tac[check_freevars_to_check_t])
      >>
        fs[Abbr`itenv2`,tenv_invC_def]>>
        simp[GSYM bvl2_to_bvl,lookup_bvl2,bind_tvar_rewrites, deBruijn_inc0,lookup_tenv_def] >>
        `LENGTH tys = LENGTH funs` by simp[Abbr`tys`,LENGTH_COUNT_LIST] >>
        simp[MAP2_MAP,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        simp[tenv_add_tvs_def,ALOOKUP_MAP] >>
        rpt gen_tac >>
        Cases_on`ALOOKUP tenv'' x` >> simp[] >- (
          CASE_TAC >> simp[] >>
          CASE_TAC >> simp[] >>
          strip_tac >>
          `t = r` by (
            imp_res_tac lookup_freevars >>
            metis_tac[nil_deBruijn_inc] ) >>
          conj_tac >- metis_tac[lookup_freevars] >>
          simp[ALOOKUP_APPEND] >>
          reverse CASE_TAC >- (
            imp_res_tac ALOOKUP_MEM >>
            `MEM x (MAP FST funs)` by (
              rfs[MEM_MAP,MEM_ZIP,MEM_EL] >>
              metis_tac[] ) >>
            imp_res_tac ALOOKUP_FAILS >>
            rfs[] >>
            fs[MEM_MAP,EXISTS_PROD] ) >>
          fs[tenv_alpha_def,tenv_invC_def,bvl2_lookup] >>
          first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
          strip_tac >> simp[] >>
          CASE_TAC >- metis_tac[] >>
          imp_res_tac ALOOKUP_MEM >>
          fs[EVERY_MEM,FORALL_PROD] >>
          metis_tac[] ) >>
        strip_tac >> rpt VAR_EQ_TAC >>
        first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
        simp[num_tvs_bind_var_list] >>
        simp[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] >>
        strip_tac >> conj_tac >- metis_tac[] >>
        simp[ALOOKUP_APPEND] >>
        CASE_TAC >- (
          imp_res_tac ALOOKUP_FAILS >>
          imp_res_tac ALOOKUP_MEM >>
          `MEM x (MAP FST funs)` by (
            simp[] >>
            simp[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
            metis_tac[] ) >>
          rfs[MEM_MAP,MEM_ZIP,EXISTS_PROD,MEM_EL] >>
          metis_tac[] ) >>
        Cases_on`x'`>>simp[] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP] >>
        simp[check_t_def] >>
        cheat)
   >>
   rw[]>>
   imp_res_tac infer_funs_length>>
   fs[sub_completion_def]>>
   `t_compat st'.subst s''` by
     metis_tac[pure_add_constraints_success,infer_e_wfs]>>
   imp_res_tac t_compat_pure_add_constraints_1>>
   pop_assum kall_tac>>
   qpat_abbrev_tac `ls:(infer_t#infer_t)list = ZIP (A,B)`>>
   first_x_assum(qspec_then`ls` mp_tac)>>discharge_hyps>-
     (fs[Abbr`ls`]>>
     fs[EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS]>>
     rw[]>>
     fs[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]>>
     `LENGTH tenv'' = LENGTH env'` by metis_tac[LENGTH_MAP]>>
     last_x_assum(qspec_then`n` assume_tac)>>
     rfs[init_infer_state_def]>>
     fs[t_compat_def,Abbr`targs`,EL_MAP]>>
     fs[EL_MAP,MAP_MAP_o]>>
     last_x_assum(qspec_then`n`mp_tac) >>
     simp[] >> strip_tac >>
     last_x_assum(qspec_then`n`mp_tac) >>
     simp[] >> strip_tac >>
     match_mp_tac EQ_TRANS >>
     qexists_tac`t_walkstar s'' (t_walkstar s' (Infer_Tuvar n))` >>
     conj_asm1_tac >- simp[] >>
     match_mp_tac EQ_TRANS >>
     qexists_tac`t_walkstar s' (Infer_Tuvar n)` >>
     conj_asm1_tac >- (
       match_mp_tac t_walkstar_no_vars >>
       metis_tac[check_t_empty_unconvert_convert_id] ) >>
     simp[] >>
     last_assum(qspec_then`n`mp_tac) >>
     discharge_hyps >- (
       imp_res_tac(last(CONJUNCTS infer_e_next_uvar_mono)) >>
       DECIDE_TAC ) >>
     simp[] >>
     `EVERY (check_t 0 (count st'.next_uvar)) env'` by (
       match_mp_tac (last(CONJUNCTS infer_e_check_t)) >>
       first_assum (match_exists_tac o concl) >> simp[] >>
       simp[Abbr`itenv2`,check_env_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
       reverse conj_tac >- (
         simp[EVERY_MEM] >>
         fs[FORALL_PROD] >>
         rw[] >>
         match_mp_tac(MP_CANON(CONJUNCT1 check_t_more5)) >>
         res_tac >> HINT_EXISTS_TAC >> simp[] ) >>
       simp[EVERY_MAP,UNCURRY] >>
       simp[EVERY_MEM,MEM_ZIP,Abbr`tys`,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
       simp[check_t_def] ) >>
     strip_tac >>
     match_mp_tac (GEN_ALL check_t_empty_unconvert_convert_id) >>
     qexists_tac`tvs` >>
     match_mp_tac(CONJUNCT1 check_t_walkstar) >>
     simp[] >>
     conj_tac >- ( fs[EVERY_MEM,MEM_EL,PULL_EXISTS] ) >>
     rw[] >> res_tac >> pop_assum mp_tac >>
     simp_tac(srw_ss())[num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] )>>
   rw[]>>
   qexists_tac`<|next_uvar:=st'.next_uvar;subst:=si|>`>>fs[]>>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   reverse (rw[])
   >- (
     (* the use of generalise_complete here should probably be moved out for use in the second subgoal too *)
     first_assum(mp_tac o MATCH_MP(
       pure_add_constraints_check_s
       |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``pure_add_constraints`` o fst o strip_comb))))
       |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
     simp[AND_IMP_INTRO] >>
     disch_then(qspecl_then[`0`,`st'.next_uvar`]mp_tac) >>
     discharge_hyps >- (
       `check_env (count st.next_uvar) itenv2` by (
         simp[Abbr`itenv2`,check_env_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
         reverse conj_tac >- (
           simp[EVERY_MEM] >>
           fs[FORALL_PROD] >>
           rw[] >>
           match_mp_tac(MP_CANON(CONJUNCT1 check_t_more5)) >>
           fs[EVERY_MEM,FORALL_PROD] >>
           res_tac >> HINT_EXISTS_TAC >> simp[] ) >>
         simp[EVERY_MAP,UNCURRY] >>
         simp[EVERY_MEM,MEM_ZIP,Abbr`tys`,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
         simp[check_t_def] ) >>
       reverse conj_tac >- (
         match_mp_tac(last(CONJUNCTS infer_e_wfs)) >>
         first_assum(match_exists_tac o concl) >>
         simp[] ) >>
       reverse conj_tac >- (
         match_mp_tac(last(CONJUNCTS infer_e_check_s)) >>
         first_assum(match_exists_tac o concl) >>
         simp[GSYM check_cenv_tenvC_ok,check_s_def] ) >>
       simp[Abbr`ls`,EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,EL_MAP,PULL_EXISTS,EL_COUNT_LIST] >>
       simp[check_t_def] >>
       imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
       rw[] >- DECIDE_TAC >>
       imp_res_tac(last(CONJUNCTS infer_e_check_t)) >>
       fs[EVERY_MEM,PULL_EXISTS,MEM_EL] >>
       res_tac >> imp_res_tac check_t_more2 >> fs[] ) >>
     strip_tac >>
     first_assum(mp_tac o MATCH_MP(
       generalise_complete
       |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(is_eq))))
       |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
     disch_then(qspec_then`st'.next_uvar`mp_tac) >>
     simp[AND_IMP_INTRO] >>
     discharge_hyps >- (
       simp[EVERY_MAP,check_t_def] >>
       simp[EVERY_MEM,MEM_COUNT_LIST] >>
       imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
       rw[] >- DECIDE_TAC >>
       metis_tac[pure_add_constraints_wfs,infer_e_wfs]) >>
     rw[] >>
     simp[MAP2_MAP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
     simp[EVERY_MAP] >>
     cheat)
   >-
     cheat
   >>
   simp[tenv_alpha_def]>>
   CONJ_TAC>-
     (fs[tenv_inv_def]>>
     (*Generalization needed here:
       then show that
       whatever we got from the inferencer type checks in the
       type system at the expression level
       ⇒ the type system's generalizes it
     *)
     cheat)
   >>
   fs[tenv_invC_def]>>
   (*Should be same as generalized lets*)
   cheat)
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
     >- (fs[tenv_alpha_empty]))
 (* Exception definition *)
 >- fs[tenv_alpha_empty]
 >- metis_tac []
 >- fs[tenv_alpha_empty]);

val infer_ds_complete = prove(``
!ds mn (mdecls:'a list) tdecls edecls tenvT menv cenv mdecls' tdecls' edecls' tenvT' cenv' tenv tenv' st itenv tenvM. 
  check_menv menv ∧
  tenvM_ok tenvM ∧ 
  tenv_ok (bind_var_list2 tenv Empty) ∧ 
  check_env ∅ itenv ∧  
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧ 
  type_ds T mn (set mdecls,set tdecls,set edecls) tenvT tenvM cenv (bind_var_list2 tenv Empty) ds (mdecls',tdecls',edecls') tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧ 
  menv_alpha menv tenvM
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
  disch_then (Q.ISPECL_THEN [`menv`,`st`,`itenv`] mp_tac)>>
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
  `tenv_ok (bind_var_list2 (tenv''++tenv) Empty)` by 
    (fs[bind_var_list2_append]>>
    match_mp_tac tenv_ok_bvl2>>
    fs[typeSoundInvariantsTheory.tenv_ok_def,tenv_ok_bind_var_list2]>>
    match_mp_tac (INST_TYPE [alpha|->``:'a->bool``,beta|->alpha] type_d_tenv_ok)>>
    first_assum (match_exists_tac o concl)>>
    first_assum (match_exists_tac o concl)>>
    fs[num_tvs_bvl2,num_tvs_def])>>
  rpt
   (disch_then (fn th => first_x_assum (mp_tac o MATCH_MP th)))>>
  disch_then (qspec_then `st'` strip_assume_tac)>>
  fs[append_decls_def]>>
  fs[check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2])

(*TODO move to miscLib*)
fun any_match_mp impth th = 
  let
    val h = impth |> concl |> strip_forall |>snd |> dest_imp |> fst |>strip_conj
    val c = first(can (C match_term (concl th))) h
    val th2 = impth
      |> CONV_RULE (STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv (equal c))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
  in
    MATCH_MP th2 th  end

val infer_top_complete = store_thm("infer_top_complete",``
!top mdecls tdecls edecls tenvT menv cenv mdecls' tdecls' edecls' tenvT' cenv' tenv tenv' menv' st itenv tenvM tenvM'.
  check_menv menv ∧
  tenvM_ok tenvM ∧ 
  tenv_ok (bind_var_list2 tenv Empty) ∧ 
  check_env ∅ itenv ∧  
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧ 
  (*check_env ∅ tenv' ∧ *)
  type_top T (set mdecls,set tdecls,set edecls) tenvT tenvM cenv (bind_var_list2 tenv Empty) top (mdecls',tdecls',edecls') tenvT' tenvM' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧ 
  menv_alpha menv tenvM 
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv' menv'.
    set mdecls'' = mdecls' ∧
    set tdecls'' = tdecls' ∧
    set edecls'' = edecls' ∧
    infer_top (mdecls,tdecls,edecls) tenvT menv cenv itenv top st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', menv', cenv', itenv'), st') ∧ 
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧ 
    MAP FST itenv' = MAP FST tenv' ∧  
    (*maybe implied as well*)
    check_env ∅ itenv'``, 
  rw [Once type_top_cases]>>
  fs[infer_top_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]
  >-
    (first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] infer_d_complete)))>>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    disch_then (qspecl_then [`st`] mp_tac)>>
    rw[check_env_def]>>fs[PULL_EXISTS]>>
    fs[menv_alpha_def])
  >>
    first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] infer_ds_complete)))>>
    PairCases_on`decls'` >>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    disch_then (qspecl_then [`st`] mp_tac)>>
    rw[check_env_def]>>fs[PULL_EXISTS] >>
    fs[check_signature_cases]
    >-
      (fs[check_signature_def,success_eqns,EXTENSION,tenv_alpha_empty]>>
      fs[menv_alpha_def]>>
      match_mp_tac fmap_rel_FUPDATE_same>>
      fs[])
    >>
      fs[check_signature_def,success_eqns]>>
      cheat)

val infer_prog_complete = store_thm("infer_prog_complete",``
!prog mdecls tdecls edecls tenvT menv cenv mdecls' tdecls' edecls' tenvT' cenv' tenv tenv' menv' st itenv tenvM tenvM'.
  check_menv menv ∧
  tenvM_ok tenvM ∧ 
  tenv_ok (bind_var_list2 tenv Empty) ∧ 
  check_env ∅ itenv ∧  
  tenvC_ok cenv ∧
  tenvT_ok tenvT ∧ 
  type_prog T (set mdecls,set tdecls,set edecls) tenvT tenvM cenv (bind_var_list2 tenv Empty) prog (mdecls',tdecls',edecls') tenvT' tenvM' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv Empty) ∧ 
  menv_alpha menv tenvM 
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv' menv'.
    set mdecls'' = mdecls' ∧
    set tdecls'' = tdecls' ∧
    set edecls'' = edecls' ∧
    infer_prog (mdecls,tdecls,edecls) tenvT menv cenv itenv prog st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', menv', cenv', itenv'), st') ∧ 
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧ 
    MAP FST itenv' = MAP FST tenv' ∧  
    (*maybe implied as well*)
    check_env ∅ itenv'``,
  Induct>-
  (rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[tenv_alpha_empty,menv_alpha_def])
  >>
  rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def]>>
  fs[]>>
  first_assum (mp_tac o (any_match_mp (infer_top_complete|>REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
  rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
  disch_then (qspecl_then [`st`] mp_tac)>>
  rw[]>>
  `check_cenv cenv` by fs[check_cenv_tenvC_ok]>>
  qpat_assum`check_env {} itenv` mp_tac>>strip_tac>>
  qabbrev_tac`decls = (mdecls,tdecls,edecls)`>>
  first_assum (mp_tac o (any_match_mp infer_top_invariant))>>
  rpt (disch_then (fn th => first_assum (mp_tac o (any_match_mp th))))>>
  strip_tac>>
  fs[PULL_EXISTS]>>
  fs[GSYM bind_var_list2_append]>>
  FULL_SIMP_TAC bool_ss [UNION_APPEND,union_decls_def] >>
  first_x_assum(qspecl_then
    [`mdecls''++mdecls`,`tdecls''++tdecls`,`edecls''++edecls`
    ,`merge_mod_env (p_1,p_2) tenvT`,`FUNION menv''' menv`
    ,`merge_alist_mod_env (p_1',p_2')cenv`
    ,`p_1''''''`,`p_1'''''''`,`p_2'''''`,`(p_1'',p_2'')`
    ,`(p_1''',p_2''')`,`tenv''++tenv`,`tenv'''`,`st'`,`itenv'++itenv`
    ,`FUNION menv' tenvM`,`menv''`]
    mp_tac)>>
  discharge_hyps>-
    (rw[]
    >-
      metis_tac[check_menv_def,fevery_funion]
    >-
      (fs[typeSoundInvariantsTheory.tenvM_ok_def]>>
      cheat)
      (*type sys invariant*)
    >-
      (*type sys invariant*)
      cheat
    >-
      fs[check_env_def]
    >-
      fs[tenvC_ok_merge,check_cenv_tenvC_ok]
    >-
      fs[tenvT_ok_merge]
    >-
      metis_tac[tenv_alpha_bind_var_list2]
    >>
      fs[menv_alpha_def,fmap_rel_FUNION_rels])
  >>
  rw[]>>
  fs[append_decls_def,Abbr`decls`]>>
  fs[check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2,menv_alpha_def,fmap_rel_FUNION_rels])

val _ = export_theory ();
