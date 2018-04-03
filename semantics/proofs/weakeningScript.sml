open preamble;
open optionTheory rich_listTheory alistTheory;
open miscTheory;
open libTheory astTheory typeSystemTheory typeSysPropsTheory;
open namespacePropsTheory;
open semanticPrimitivesTheory;
open astPropsTheory;
open typeSoundInvariantsTheory;
open terminationTheory;

val _ = new_theory "weakening";

val weak_tenvE_def = Define `
weak_tenvE tenv tenv' =
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t.
    (tveLookup n inc tenv' = SOME (tvs,t)) ⇔
    (tveLookup n inc tenv = SOME (tvs,t)))`;

val weakS_def = Define `
weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS`;

val weak_tenvE_refl = Q.store_thm ("weak_tenvE_refl",
  `!tenvE. weak_tenvE tenvE tenvE`,
 rw [weak_tenvE_def]);

(*
val weak_tenvT_refl = Q.store_thm ("weak_tenvT_refl",
  `∀n x. weak_tenvT n x x`,
 rw []
 >> PairCases_on `x`
 >> rw [weak_tenvT_def]);
 *)

val weak_tenv_refl = Q.store_thm ("weak_tenv_refl",
  `!tenv. tenv_val_ok tenv.v ⇒ weak_tenv tenv tenv`,
 rw [weak_tenv_def]
 >> irule nsSub_refl
 >> rw [tscheme_inst2_def]
 >- (
   qexists_tac `\n (tvs,t). check_freevars tvs [] t`
   >> rw []
   >> fs [tenv_val_ok_def]
   >> PairCases_on `x`
   >> rw [(*weak_tenvT_def,*) tscheme_inst_def]
   >> qexists_tac `MAP Tvar_db (COUNT_LIST x0)`
   >> rw [LENGTH_COUNT_LIST, EVERY_MAP]
   >> rw [EVERY_MEM, MEM_COUNT_LIST, check_freevars_def]
   >> fs [tenv_val_ok_def]
   >> metis_tac [deBruijn_subst_id])
 >> qexists_tac `\n t. T`
 >> rw [(*weak_tenvT_refl*)]);

val weakS_refl = Q.store_thm ("weakS_refl",
  `!tenvS. weakS tenvS tenvS`,
 rw [weakS_def]);

val weakS_bind = Q.store_thm ("weakS_bind",
`!l t tenvS. FLOOKUP tenvS l = NONE ⇒ weakS (tenvS |+ (l,t)) tenvS`,
 rw [weakS_def, FLOOKUP_UPDATE, flookup_thm]);

val weak_tenvE_freevars = Q.prove (
`!tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t`,
rw [weak_tenvE_def] >>
metis_tac [check_freevars_add]);

val weak_tenvE_bind = Q.prove (
`!tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv)`,
rw [weak_tenvE_def, tveLookup_def] >>
every_case_tac >>
rw []);

val weak_tenvE_opt_bind = Q.prove (
`!tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv)`,
 rw [weak_tenvE_def, num_tvs_def, opt_bind_name_def, tveLookup_def] >>
 every_case_tac >>
 fs [tveLookup_def, num_tvs_def] >>
 every_case_tac >>
 fs []);

val weak_tenvE_bind_tvar = Q.prove (
`!tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)`,
rw [weak_tenvE_def, num_tvs_def, bind_tvar_def, tveLookup_def] >>
decide_tac);

val weak_tenvE_bind_tvar2 = Q.prove (
`!tenv tenv' n tvs t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0 ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)`,
 rw [weak_tenvE_def, num_tvs_def, bind_tvar_def]
 >> metis_tac [tveLookup_no_tvs]);

val weak_tenvE_bind_var_list = Q.prove (
`!bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)`,
induct_on `bindings` >>
rw [weak_tenvE_def, bind_var_list_def, num_tvs_def] >>
PairCases_on `h` >>
fs [bind_var_list_def, tveLookup_def] >>
every_case_tac >>
fs [weak_tenvE_def] >>
PROVE_TAC []);

val eLookupC_weak = Q.prove (
  `∀cn tenv tenv' tvs ts tn.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.c cn = SOME (tvs,ts,tn)
    ⇒
    nsLookup tenv'.c cn = SOME (tvs,ts,tn)`,
 rw [weak_tenv_def, namespaceTheory.nsSub_def]);

val eLookupV_weak = Q.prove (
  `∀n tenv tenv' tvs t.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.v n = SOME (tvs,t)
    ⇒
    ∃tvs' t'. nsLookup tenv'.v n = SOME (tvs',t') ∧ tscheme_inst (tvs,t) (tvs',t')`,
 rw [weak_tenv_def, namespaceTheory.nsSub_def, tscheme_inst2_def]
 >> metis_tac [pair_CASES]);

      (*
val weakE_lookup = Q.prove (
`!n env env' tvs t.
  weakE env' env ∧
  (ALOOKUP env n = SOME (tvs, t))
  ⇒
  ?tvs' t' subst.
    (ALOOKUP env' n = SOME (tvs', t')) ∧
    check_freevars tvs' [] t' ∧
    (LENGTH subst = tvs') ∧
    EVERY (check_freevars tvs []) subst ∧
    (deBruijn_subst 0 subst t' = t)`,
 rw [weakE_def] >>
 qpat_x_assum `!cn. P cn` (MP_TAC o Q.SPEC `n`) >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 metis_tac []);

val weak_tenvM_lookup_lem = Q.prove (
`!tvs.
  EVERY (λx. check_freevars tvs [] (Tvar_db x)) (COUNT_LIST tvs)`,
Induct >>
rw [COUNT_LIST_def, check_freevars_def, EVERY_MAP] >>
fs [check_freevars_def]);

val weak_tenvM_lookup = Q.prove (
`!mn tenvM tenvM' tenv tenv' tvs t.
  weakM tenvM' tenvM ∧
  FLOOKUP tenvM mn = SOME tenv
  ⇒
  ?tenv'.
    FLOOKUP tenvM' mn = SOME tenv' ∧
    weakE tenv' tenv`,
 rw [weakM_def]);

 *)

val weak_def = Define `
weak tenv' tenv ⇔
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv`;

val type_p_weakening = Q.store_thm ("type_p_weakening",
`(!tvs tenv p t bindings. type_p tvs tenv p t bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_p tvs' tenv' p t bindings) ∧
 (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_ps tvs' tenv' ps ts bindings)`,
 ho_match_mp_tac type_p_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [type_p_cases] >>
 rw [] >>
 fs [EVERY_MEM] >>
 metis_tac [weak_def, check_freevars_add, EVERY_MEM, eLookupC_weak]);

val type_e_weakening_lem = Q.prove (
`(!tenv tenvE e t. type_e tenv tenvE e t ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)`,
 ho_match_mp_tac type_e_ind >>
 rw [weak_def] >>
 rw [Once type_e_cases]
 >- metis_tac [weak_tenvE_freevars]
 >- (fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     res_tac >>
     fs [] >>
     qexists_tac `bindings` >>
     rw []
     >- metis_tac [weak_def, type_p_weakening, weak_tenvE_def] >>
     first_x_assum match_mp_tac >>
     rw [weak_def, weak_tenvE_bind_var_list])
 >- (fs [EVERY_MEM] >>
     metis_tac [eLookupC_weak, weak_tenvE_freevars])
 >- (
   fs [lookup_var_def]
   >> Cases_on `lookup_varE n tenvE`
   >> fs []
   >- (
     drule weak_tenvE_freevars
     >> fs [weak_tenvE_def]
     >> CASE_TAC
     >> rfs [lookup_varE_def]
     >- (
       drule eLookupV_weak
       >> disch_then drule
       >> rw [tscheme_inst_def]
       >> rw []
       >> qexists_tac `MAP (deBruijn_subst 0 targs) subst`
       >> rw [EVERY_MAP]
       >- metis_tac [deBruijn_subst2, deBruijn_inc0]
       >> rw [EVERY_MEM]
       >> match_mp_tac deBruijn_subst_check_freevars2
       >> rw []
       >> metis_tac [EVERY_MEM])
     >- (
       Cases_on `n`
       >> fs []
       >> metis_tac [NOT_SOME_NONE, pair_CASES]))
   >- (
     rw []
     >> fs [weak_tenvE_def]
     >> Cases_on `n`
     >> rfs [lookup_varE_def]
     >> metis_tac [check_freevars_add, EVERY_MEM]))
 >- metis_tac [weak_tenvE_freevars, weak_tenvE_bind]
 >- (
   first_x_assum match_mp_tac >>
   rw [] >>
   metis_tac [weak_tenvE_bind, weak_tenvE_freevars])
 >- metis_tac [weak_tenvE_freevars]
 >- (fs [RES_FORALL] >>
     qexists_tac `t` >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     res_tac >>
     fs [] >>
     qexists_tac `bindings` >>
     rw []
     >- metis_tac [weak_def, type_p_weakening, weak_tenvE_def] >>
     first_x_assum match_mp_tac >>
     rw [weak_tenvE_bind_var_list])
 >- (
   qexists_tac `t` >>
   rw [] >>
   first_x_assum match_mp_tac >>
   rw [] >>
   metis_tac [weak_tenvE_opt_bind, weak_tenvE_bind_tvar])
 (* COMPLETENESS >- metis_tac [weak_tenvE_opt_bind, weak_tenvE_bind_tvar], *)
 >- (
   qexists_tac `bindings` >>
   rw [] >>
   first_x_assum match_mp_tac >>
   rw [] >>
   metis_tac [weak_tenvE_bind_var_list, weak_tenvE_bind_tvar])
 >- metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar, weak_tenvE_freevars]
 >- (
   first_x_assum match_mp_tac  >>
   rw [] >>
   metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar, weak_tenvE_freevars]));

val type_e_weakening = Q.store_thm ("type_e_weakening",
`(!tenv tenvE e t tenv' tenvE'.
   type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts tenv' tenvE'.
   type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings tenv' tenvE'.
   type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)`,
metis_tac [type_e_weakening_lem]);

val gt_0 = Q.prove (
`!x:num.x ≥ 0`,
decide_tac);

val weakCT_def = Define `
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl`;

val weak_ctMap_lookup = Q.prove (
`∀ctMap ctMap' tvs ts stamp.
  weakCT ctMap' ctMap ∧
  FLOOKUP ctMap stamp = SOME (tvs,ts)
  ⇒
  FLOOKUP ctMap' stamp = SOME (tvs,ts)`,
rw [weakCT_def] >>
metis_tac [FLOOKUP_SUBMAP]);

val weakCT_refl = Q.store_thm ("weakCT_refl",
`!ctMap. weakCT ctMap ctMap`,
rw [weakCT_def] >>
metis_tac [SUBMAP_REFL]);

val weakCT_trans = Q.store_thm ("weakCT_trans",
`weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3`,
 rw [weakCT_def]
 >> metis_tac [SUBMAP_TRANS]);

val disjoint_env_weakCT = Q.store_thm ("disjoint_env_weakCT",
`!ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap`,
rw [weakCT_def] >>
metis_tac [SUBMAP_FUNION, DISJOINT_SYM, SUBMAP_REFL]);

val weakCT2 = Q.store_thm ("weakCT2",
`!ctMap ctMap'. weakCT (FUNION ctMap' ctMap) ctMap'`,
  rw [weakCT_def] >>
  metis_tac [SUBMAP_FUNION, DISJOINT_SYM, SUBMAP_REFL]);

val type_tenv_ctor_weakening = Q.store_thm ("type_tenv_ctor_weakening",
`!ctMap tenvC envC ctMap'.
  weakCT ctMap' ctMap ∧
  nsAll2 (type_ctor ctMap) envC tenvC
  ⇒
  nsAll2 (type_ctor ctMap') envC tenvC`,
 rw [weakCT_def, weakS_def]
 >> irule nsAll2_mono
 >>  qexists_tac `type_ctor ctMap`
 >> rw []
 >> rename1 `type_ctor ctMap cn x1 x2`
 >> `?n t1 stamp tvs ts t2. x1 = (n,stamp) ∧ x2 = (tvs,ts,t2)` by metis_tac [pair_CASES]
 >> fs [type_ctor_def]
 >> rw []
 >> metis_tac [FLOOKUP_SUBMAP]);

val type_tenv_val_weakening_lemma = Q.prove (
`!ctMap tenvS tenvV envV ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  nsAll2 (λi v (tvs,t).
          ∀tvs' ctMap' tenvS'.
            (tvs = 0 ∨ tvs = tvs') ∧
            weakCT ctMap' ctMap ∧
            weakS tenvS' tenvS
            ⇒
            type_v tvs' ctMap' tenvS' v t)
         envV tenvV
  ⇒
  nsAll2 (λi v (tvs,t). type_v tvs ctMap' tenvS' v t) envV tenvV`,
 rw [type_all_env_def, weakCT_def, weakS_def]
 >> irule nsAll2_mono
 >> qexists_tac `(λi v (tvs,t).
           ∀tvs' ctMap' tenvS'.
             (tvs = 0 ∨ tvs = tvs') ∧ ctMap ⊑ ctMap' ∧
             tenvS ⊑ tenvS' ⇒
             type_v tvs' ctMap' tenvS' v t) `
 >> rw []
 >> pairarg_tac
 >> fs []);

val remove_lambda_prod = Q.prove (
`(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

val type_v_weakening = Q.store_thm ("type_v_weakening",
`(!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'.
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t)`,
 ho_match_mp_tac type_v_ind >>
 rw [] >>
 rw [Once type_v_cases]
 >- (
   qexists_tac `tvs'`
   >> qexists_tac `ts`
   >> rw []
   >> fs [EVERY_MEM, EVERY2_EVERY]
   >> rfs [MEM_ZIP]
   >> rw []
   >> fs [PULL_EXISTS]
   >> metis_tac [weak_ctMap_lookup, check_freevars_add, gt_0])
 >- (
   qexists_tac `tvs'`
   >> qexists_tac `ts`
   >> rw []
   >> fs [EVERY_MEM, EVERY2_EVERY]
   >> rfs [MEM_ZIP]
   >> rw []
   >> fs [PULL_EXISTS]
   >> metis_tac [weak_ctMap_lookup, check_freevars_add, gt_0])
 >- (
   fs [EVERY_MEM, EVERY2_EVERY]
   >>rfs [MEM_ZIP]
   >> rw []
   >> fs [PULL_EXISTS])
 >- (
   fs [EVERY_MEM, EVERY2_EVERY]
   >>rfs [MEM_ZIP]
   >> rw []
   >> fs [PULL_EXISTS])
 >- (fs [] >>
     qexists_tac `tenv` >>
     qexists_tac `tenvE` >>
     rw []
     >- metis_tac [type_tenv_ctor_weakening]
     >- metis_tac [type_tenv_val_weakening_lemma]
     >- metis_tac [check_freevars_add, gt_0]
     >> irule (CONJUNCT1 type_e_weakening)
     >> simp [weak_def]
     >> qexists_tac `tenv`
     >> fs [weak_tenv_refl, tenv_ok_def]
     >> simp [Once CONJ_SYM]
     >> first_assum (match_exists_tac o concl)
     >> simp []
     >> irule weak_tenvE_bind
     >> irule (SIMP_RULE (srw_ss()) [] weak_tenvE_bind_tvar2)
     >> simp [tenv_val_exp_ok_def, weak_tenvE_def])
 >- (fs [] >>
     qexists_tac `tenv` >>
     qexists_tac `tenvE` >>
     rw [] >>
     metis_tac [type_tenv_ctor_weakening, type_tenv_val_weakening_lemma])
 >- (fs [] >>
     qexists_tac `tenv` >>
     qexists_tac `tenvE` >>
     qexists_tac `bindings` >>
     rw []
     >- metis_tac [type_tenv_ctor_weakening]
     >- metis_tac [type_tenv_val_weakening_lemma]
     >> match_mp_tac (CONJUNCT2 (CONJUNCT2 type_e_weakening)) >>
     first_assum(match_exists_tac o concl) >> simp[weak_def] >>
     fs [weak_tenv_refl, tenv_ok_def]
     >> irule weak_tenvE_bind_var_list
     >> irule (SIMP_RULE (srw_ss()) [] weak_tenvE_bind_tvar2)
     >> simp [tenv_val_exp_ok_def, weak_tenvE_def])
 >- (fs [] >>
     qexists_tac `tenv` >>
     qexists_tac `tenvE` >>
     qexists_tac `bindings` >>
     rw [] >>
     metis_tac [type_tenv_ctor_weakening, type_tenv_val_weakening_lemma])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (fs [weakS_def] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- fs [EVERY_MEM]
 >- fs [EVERY_MEM]);

val type_all_env_weakening = Q.store_thm ("type_all_env_weakening",
`!ctMap tenvS tenv env ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  type_all_env ctMap tenvS env tenv
  ⇒
  type_all_env ctMap' tenvS' env tenv`,
 rw [type_all_env_def]
 >- metis_tac [type_tenv_ctor_weakening]
 >> irule type_tenv_val_weakening_lemma
 >> qexists_tac `ctMap`
 >> qexists_tac `tenvS`
 >> simp []
 >> irule nsAll2_mono
 >> simp [Once CONJ_SYM]
 >> first_assum (match_exists_tac o concl)
 >> rw []
 >> pairarg_tac
 >> rw []
 >> fs []
 >> metis_tac [type_v_weakening]);

val type_sv_weakening = Q.store_thm ("type_sv_weakening",
`!ctMap tenvS st sv ctMap' tenvS'.
  type_sv ctMap tenvS sv st ∧
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS
  ⇒
  type_sv ctMap' tenvS' sv st`,
 rpt gen_tac >>
 Cases_on `sv` >>
 Cases_on `st` >>
 rw [type_sv_def]
 >- metis_tac [type_v_weakening]
 >> fs [EVERY_MEM]
 >> metis_tac [type_v_weakening]);

val type_s_weakening = Q.store_thm ("type_s_weakening",
`!ctMap tenvS st ctMap'.
  type_s ctMap tenvS st ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' tenvS st`,
 rw [type_s_def] >>
 metis_tac [type_sv_weakening, weakS_refl]);

 (*
val weakCT_only_other_mods_def = Define `
weakCT_only_other_mods mn ctMap' ctMap =
  !cn tn.
    ((cn,tn) ∈ FDOM ctMap' ∧ (cn,tn) ∉ FDOM ctMap)
    ⇒
    (?mn' x. mn ≠ SOME mn' ∧ (tn = TypeId (Long mn' x) ∨ tn = TypeExn (Long mn' x)))`;

val weakCT_only_other_mods_merge = Q.prove (
`!mn ctMap1 ctMap2 ctMap3.
  weakCT_only_other_mods mn ctMap2 ctMap3
  ⇒
  weakCT_only_other_mods mn (FUNION ctMap1 ctMap2) (FUNION ctMap1 ctMap3)`,
rw [weakCT_only_other_mods_def] >>
metis_tac []);

val weak_decls_only_mods_union = Q.store_thm ("weak_decls_only_mods_union",
`!decls1 decls2 decls3.
  weak_decls_only_mods decls2 decls3
  ⇒
  weak_decls_only_mods (union_decls decls1 decls2) (union_decls decls1 decls3)`,
 rw [] >>
 fs [weak_decls_only_mods_def, union_decls_def] >>
 metis_tac []);

val weak_decls_only_mods_union2 = Q.store_thm ("weak_decls_only_mods_union2",
`!decls1 decls2 decls3 decls1'.
  weak_decls_only_mods decls1 decls1' ∧
  weak_decls_only_mods decls2 decls3
  ⇒
  weak_decls_only_mods (union_decls decls1 decls2) (union_decls decls1' decls3)`,
 rw [] >>
 fs [weak_decls_only_mods_def, union_decls_def] >>
 metis_tac []);

val weak_decls_refl = Q.store_thm ("weak_decls_refl",
`!decls. weak_decls decls decls`,
 rw [weak_decls_def]);

val weak_decls_trans = Q.store_thm ("weak_decls_trans",
`!decls1 decls2 decls3.
  weak_decls decls1 decls2 ∧
  weak_decls decls2 decls3
  ⇒
  weak_decls decls1 decls3`,
 rw [] >>
 fs [weak_decls_def, SUBSET_DEF]);

val weak_decls_other_mods_def = Define `
weak_decls_other_mods mn d' d ⇔
  (!tid. tid ∈ d'.defined_types ∧ tid ∉ d.defined_types ⇒ ¬?tn. tid = mk_id mn tn) ∧
  (!cid. cid ∈ d'.defined_exns ∧ cid ∉ d.defined_exns ⇒ ¬?cn. cid = mk_id mn cn)`;

val weak_decls_other_mods_refl = Q.store_thm ("weak_decls_other_mods_refl",
`!mn decls. weak_decls_other_mods mn decls decls`,
 rw [] >>
 rw [weak_decls_other_mods_def]);
 *)

val weak_tenv_extend_dec_tenv = Q.store_thm ("weak_tenv_extend_dec_tenv",
  `!tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3)`,
 rw []
 >> drule weak_tenv_refl
 >> fs [weak_tenv_def, extend_dec_tenv_def]
 >> rw []
 >> irule nsSub_nsAppend2
 >> simp []);

val type_d_weakening = Q.store_thm ("type_d_weakening",
`(!check tenv d decls tenv'.
  type_d check tenv d decls tenv' ⇒
  !tenv''.
  check = F ∧
  tenv_ok tenv'' ∧
  weak tenv'' tenv
  ⇒
  type_d check tenv'' d decls tenv') ∧
 (!check tenv d decls tenv'.
  type_ds check tenv d decls tenv' ⇒
  !tenv''.
  check = F ∧
  tenv_ok tenv'' ∧
  weak tenv'' tenv
  ⇒
  type_ds check tenv'' d decls tenv')`,
 ho_match_mp_tac type_d_ind >>
 rw [] >>
 simp [Once type_d_cases] >>
 rw []
 >- metis_tac[type_p_weakening,LESS_EQ_REFL,GREATER_EQ,type_e_weakening,weak_def,weak_tenvE_refl]
 >- metis_tac[type_p_weakening,LESS_EQ_REFL,GREATER_EQ,type_e_weakening,weak_def,weak_tenvE_refl]
 >- metis_tac[LESS_EQ_REFL,GREATER_EQ,type_e_weakening,weak_def,weak_tenvE_refl]
 >- (
  qexists_tac `type_identities` >>
  fs [weak_def, DISJOINT_DEF(*, weak_decls_other_mods_def*), EXTENSION] (*
  >> rw [MEM_MAP]
  >> CCONTR_TAC
  >> fs []
  >> rw []
  >> pairarg_tac
  >> fs []
  >> first_x_assum drule
  >> rw []
  >> fs [weak_decls_def, SUBSET_DEF, MEM_MAP, FORALL_PROD]
  >> metis_tac []*))
 >- fs [weak_def]
 >- fs [weak_def]
 >- fs [weak_def]
 >- fs [weak_def]
 >- (
   fs [weak_def, DISJOINT_DEF, (*weak_decls_other_mods_def,*) EXTENSION]
   >> metis_tac [])
 >- (
  qexists_tac `tenv'`
  >> qexists_tac `tenv''`
  >> qexists_tac `decls`
  >> qexists_tac `decls'`
  >> rw []
  >> first_x_assum irule
  >> simp []
  >- metis_tac [extend_dec_tenv_ok, type_d_tenv_ok] >>
  fs [weak_def]
  >> rw []
  >- rw [extend_dec_tenv_def]
  >> irule weak_tenv_extend_dec_tenv
  >> simp [] >>
  res_tac >>
  drule (CONJUNCT1 type_d_tenv_ok_helper) >>
  rw [tenv_ok_def]));

   (*
val weak_decls_union = Q.store_thm ("weak_decls_union",
`!decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls3 decls1) (union_decls decls3 decls2)`,
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []);

val weak_decls_union = Q.store_thm ("weak_decls_union",
`!decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls3 decls1) (union_decls decls3 decls2)`,
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []);

val weak_decls_union2 = Q.store_thm ("weak_decls_union2",
`!decls1 decls2 decls3.
  decls1.defined_mods = {}
  ⇒
  weak_decls (union_decls decls1 decls2) decls2`,
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF]);

val weak_decls_union3 = Q.store_thm ("weak_decls_union3",
`!decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls1 decls3) (union_decls decls2 decls3)`,
 rw [] >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF] >>
 metis_tac []);

val weak_decls_other_mods_union = Q.store_thm ("weak_decls_other_mods_union",
`!mn decls1 decls2 decls3.
  weak_decls_other_mods mn decls1 decls2
  ⇒
  weak_decls_other_mods mn (union_decls decls3 decls1) (union_decls decls3 decls2)`,
 rw [] >>
 fs [weak_decls_other_mods_def, union_decls_def] >>
 metis_tac []);

val weak_decls_other_mods_only_mods_NIL = Q.store_thm ("weak_decls_other_mods_only_mods_NIL",
`weak_decls_only_mods tdecs_no_sig tdecs1 ∧
 weak_decls tdecs_no_sig tdecs1
 ⇒
 weak_decls_other_mods [] tdecs_no_sig tdecs1`,
 fs [weak_decls_only_mods_def, weak_decls_other_mods_def, weak_decls_def, namespaceTheory.mk_id_def]
 >> metis_tac []);

val weak_decls_other_mods_only_mods_SOME = Q.store_thm ("weak_decls_other_mods_only_mods_SOME",
`decls_ok tdecs_no_sig ∧
 mn ≠ [] ∧
 mn ∉ tdecs1.defined_mods ∧
 weak_decls tdecs_no_sig tdecs1
 ⇒
 weak_decls_other_mods mn tdecs_no_sig tdecs1`,
 fs [weak_decls_only_mods_def, weak_decls_other_mods_def, weak_decls_def,
     namespaceTheory.mk_id_def, decls_ok_def, decls_to_mods_def, SUBSET_DEF]
 >> fsrw_tac[boolSimps.DNF_ss][decls_to_mods_def,GSPECIFICATION]
 >> rw []
 >> rw [METIS_PROVE [] ``¬x ∨ y ⇔ x ⇒ y``]
 >> res_tac
 >> fs [id_to_mods_mk_id]
 >> metis_tac []);

val type_ds_weak_decls_only_mods = Q.store_thm ("type_ds_weak_decls_only_mods",
 `!mn tdecs_no_sig tenv ds decls tenv' decls'.
  type_ds F mn tdecs_no_sig tenv ds decls tenv' ∧
  mn ≠ []
  ⇒
  weak_decls_only_mods decls decls'`,
 rw [weak_decls_only_mods_def]
 >> drule type_ds_mod
 >> srw_tac [DNF_ss] [decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
 >> res_tac
 >> fs [namespaceTheory.id_to_mods_def]);

 *)

  (*
val consistent_decls_weakening = Q.store_thm ("consistent_decls_weakening",
`!decls1 decls2 decls3.
  consistent_decls decls1 decls3 ∧
  weak_decls decls2 decls3
  ⇒
  consistent_decls decls1 decls2`,
 rw [] >>
 fs [consistent_decls_def, RES_FORALL, weak_decls_def] >>
 rw [] >>
 every_case_tac >>
 fs [SUBSET_DEF] >>
 res_tac >>
 fs []);

val consistent_ctMap_weakening = Q.store_thm ("consistent_ctMap_weakening",
`!ctMap tdecls tdecls'.
  consistent_ctMap tdecls ctMap ∧
  weak_decls tdecls' tdecls
  ⇒
  consistent_ctMap tdecls' ctMap`,
 rw [] >>
 fs [weak_decls_def, consistent_ctMap_def, RES_FORALL] >>
 rw [] >>
 PairCases_on `x` >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs [SUBSET_DEF]);
 *)

val _ = export_theory ();
