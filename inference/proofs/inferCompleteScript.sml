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
val sym_sub_tac = SUBST_ALL_TAC o SYM;

val generalise_subst_exist = prove(``
  (t_wfs s ∧ 
  (∀uv. uv ∈ FDOM s ⇒ check_t tvs {} (t_walkstar s (Infer_Tuvar uv))))
  ⇒
  (∀t subst n smap a b t'. 
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧ 
  t_vars t ⊆ FDOM s ∧
  check_t 0 (FDOM s) t ∧ 
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  generalise 0 n smap t = (a,b,t') ⇒
  ∃subst'. 
    LENGTH subst' = a ∧ 
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧ 
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x))) ∧ 
  (∀ts subst n smap a b ts'. 
  LENGTH subst = n ∧
  FRANGE smap ⊆ count n ∧ 
  (∀x. MEM x subst ⇒ check_t tvs {} x) ∧ 
  EVERY (λt. t_vars t ⊆ FDOM s) ts ∧ 
  EVERY (check_t 0 (FDOM s)) ts ∧ 
  (∀x. x ∈ FDOM smap ⇒ EL (smap ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  generalise_list 0 n smap ts = (a,b,ts') ⇒
  ∃subst'. 
    LENGTH subst' = a ∧ 
    (∀x. MEM x subst' ⇒ check_t tvs {} x) ∧ 
    (∀x. x ∈ FDOM b ⇒  EL (b ' x) (subst++subst') = t_walkstar s (Infer_Tuvar x)))``,
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]>>
  fs[check_t_def]
  >-
    (fs[generalise_def]>>
    qpat_assum`A=(a,b,t')` mp_tac>>LET_ELIM_TAC>>
    fs[]>>
    first_assum match_mp_tac>>
    ntac 2 HINT_EXISTS_TAC >>
    fs[EVERY_MEM,t_vars_eqn,SUBSET_DEF,MEM_MAP]>>
    metis_tac[])
  >-
    (imp_res_tac generalise_subst>>
    fs[generalise_def]>>
    FULL_CASE_TAC>>fs[]
    >-
      (qexists_tac`[t_walkstar s (Infer_Tuvar n)]`>>
      qpat_assum`A=b` sym_sub_tac>>
      rw[]
      >-
        (simp[FAPPLY_FUPDATE_THM]>>
        `x ≠ n` by 
          (CCONTR_TAC>>
          fs[flookup_thm])>>
        fs[]>>
        `smap ' x < LENGTH subst` by fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>
        simp[EL_APPEND1])
      >>
      fs[t_vars_eqn,EL_LENGTH_APPEND])
    >>
    qexists_tac`[]`>>fs[EXTENSION]>>
    metis_tac[])
  >-
    (fs[generalise_def]>>
    qexists_tac`[]`>>fs[])
  >>
    fs[generalise_def]>>
    qpat_assum`A=(a,b,t')` mp_tac>>LET_ELIM_TAC>>
    imp_res_tac generalise_subst>>
    first_x_assum(qspecl_then[`subst`,`smap`,`num_gen`,`s'`,`t'`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then[`subst++subst'`,`s'`,`num_gen'`,`s''`,`ts''`] mp_tac)>>
    discharge_hyps>-
      (fsrw_tac [ARITH_ss] []>>
      reverse CONJ_TAC>-
        metis_tac[]>>
      fs[IN_FRANGE,SUBSET_DEF,PULL_EXISTS]>>
      gen_tac>>Cases_on`k ∈ FDOM smap`>>fs[]>>
      fs[SUBMAP_DEF]>>
      res_tac>>
      DECIDE_TAC)>>
    rw[]>>
    qexists_tac`subst'++subst''`>>fs[]>>
    metis_tac[])

val infer_deBruijn_subst_infer_subst_walkstar = prove(``
  ∀b subst n m.
  FRANGE b ⊆ count (LENGTH subst) ∧
  t_wfs s 
  ⇒
  ((∀t.
  (∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x)) ∧ 
  check_t 0 m t ∧
  t_vars t ⊆ FDOM b
  ⇒ 
  infer_deBruijn_subst subst (infer_subst b t) = 
  t_walkstar s t) ∧ 
  (∀ts.
  EVERY (λt.(∀x. x ∈ t_vars t ⇒  EL (b ' x) subst = t_walkstar s (Infer_Tuvar x))) ts ∧ 
  EVERY (check_t 0 m) ts ∧ 
  EVERY (λt.t_vars t ⊆ FDOM b) ts 
  ⇒ 
  MAP ((infer_deBruijn_subst subst) o (infer_subst b)) ts = 
  MAP (t_walkstar s) ts))``,
  ntac 5 strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
  fs[infer_subst_def,t_walkstar_eqn1,check_t_def,infer_deBruijn_subst_def]
  >-
    (fs[LIST_EQ_REWRITE,EL_MAP,t_vars_eqn,PULL_EXISTS,SUBSET_DEF,MEM_MAP]>>
    rw[]>>
    first_assum (match_mp_tac o MP_CANON)>>
    fs[EVERY_MEM]>>
    metis_tac[])
  >>
  (fs[t_vars_eqn] >> imp_res_tac flookup_thm>>
  fs[PULL_FORALL]>>
  fs[infer_deBruijn_subst_def]>>
  reverse IF_CASES_TAC
  >- (fs[SUBSET_DEF,IN_FRANGE,PULL_EXISTS]>>metis_tac[])
  >> REFL_TAC))

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
     `type_e (convert_menv menv) cenv (bind_tvar a (bind_var_list2 tenv Empty)) e (convert_t (t_walkstar last_sub t'))` by 
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
     disch_then(
       (fn th => first_assum(qspec_then`itenv`mp_tac o MATCH_MP th)) o
       ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] o
       CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``type_p`` o fst o strip_comb))))) >>
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
       cheat ) >>
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
     cheat)
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
