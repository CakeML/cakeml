open preamble;
open optionTheory rich_listTheory alistTheory;
open miscTheory;
open libTheory astTheory typeSystemTheory typeSysPropsTheory;
open semanticPrimitivesTheory;
open libPropsTheory astPropsTheory;
open typeSoundInvariantsTheory;
open terminationTheory;

val _ = new_theory "weakening";

val _ = Parse.bring_to_front_overload "lookup" {Name="lookup",Thy="lib"} 

val weak_tenvE_def = Define `
weak_tenvE tenv tenv' = 
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t. 
    (lookup_tenv n inc tenv' = SOME (tvs,t)) ⇒
    (lookup_tenv n inc tenv = SOME (tvs,t)))`;

val weakS_def = Define `
weakS tenvS tenvS' =
  !l v. (lib$lookup l tenvS' = SOME v) ⇒ (lib$lookup l tenvS = SOME v)`;

val weak_tenvE_refl = Q.prove (
`!tenv. weak_tenvE tenv tenv`,
rw [weak_tenvE_def]);

val flat_weakC_refl = Q.store_thm ("flat_weakC_refl",
`!tenvC. flat_weakC tenvC tenvC`,
rw [flat_weakC_def] >>
every_case_tac);

val weakC_refl = Q.store_thm ("weakC_refl",
`!tenvC. weakC tenvC tenvC`,
rw [weakC_def, flat_weakC_refl]);

val weakE_refl = Q.store_thm ("weakE_refl",
`!tenv. tenv_ok (bind_var_list2 tenv Empty) ⇒ weakE tenv tenv`,
rw [weakE_def] >>
every_case_tac >>
qexists_tac `MAP Tvar_db (COUNT_LIST q)` >>
rw [LENGTH_COUNT_LIST, EVERY_MAP] >>
rw [EVERY_MEM, MEM_COUNT_LIST, check_freevars_def] >>
metis_tac [lookup_freevars, deBruijn_subst_id]);

val weakM_refl = Q.store_thm ("weakM_refl",
`!tenvM. tenvM_ok tenvM ⇒ weakM tenvM tenvM`,
rw [weakM_def] >>
metis_tac [weakE_refl, tenvM_ok_lookup]);

val weakS_refl = Q.store_thm ("weakS_refl",
`!tenvS. weakS tenvS tenvS`,
rw [weakS_def]);

val weakM_bind = Q.store_thm ("weakM_bind",
`!tenvM tenvM' mn tenv.
  weakM tenvM' tenvM ∧
  ~MEM mn (MAP FST tenvM) ⇒
  weakM (bind mn tenv tenvM') tenvM`,
rw [weakM_def, bind_def] >>
every_case_tac >>
metis_tac [NOT_SOME_NONE, lookup_notin]);

val weakM_bind2 = Q.store_thm ("weakM_bind2",
`!mn tenv tenvM tenvM'.
  tenv_ok (bind_var_list2 tenv Empty) ∧
  weakM tenvM' tenvM ∧
  mn ∉ set (MAP FST tenvM) 
  ⇒
  weakM (bind mn tenv tenvM') (bind mn tenv tenvM)`,
rw [weakM_def] >>
fs [lookup_def, bind_def] >>
cases_on `mn = mn'` >>
fs [] >>
metis_tac [weakE_refl, tenvM_ok_lookup]);

val weakM_bind3 = Q.store_thm ("weakM_bind3",
`!mn tenv' tenv tenvM.
  tenvM_ok tenvM ∧
  weakE tenv' tenv
  ⇒
  weakM (bind mn tenv' tenvM) (bind mn tenv tenvM)`,
rw [weakM_def] >>
fs [lookup_def, bind_def] >>
cases_on `mn = mn'` >>
fs [] >>
metis_tac [weakE_refl, tenvM_ok_lookup]);

val weakM_bind' = Q.store_thm ("weakM_bind'",
`!mn tenv' tenvM' tenv tenvM.
  weakE tenv' tenv ∧
  weakM tenvM' tenvM
  ⇒
  weakM (bind mn tenv' tenvM') (bind mn tenv tenvM)`,
rw [weakM_def, bind_def, lookup_def] >>
full_case_tac >>
fs []);

val weakS_bind = Q.store_thm ("weakS_bind",
`!l t tenvS.
  (lookup l tenvS = NONE) ⇒
  weakS (bind l t tenvS) tenvS`,
rw [weakS_def, bind_def, lookup_def] >>
every_case_tac >>
rw [] >>
fs []);

val flat_weakC_merge = Q.prove (
`!tenvC1 tenvC2 tenvC3.
  flat_weakC tenvC1 tenvC2
  ⇒
  flat_weakC (merge tenvC3 tenvC1) (merge tenvC3 tenvC2)`,
rw [merge_def, lookup_append, flat_weakC_def] >>
pop_assum (mp_tac o Q.SPEC `cn`) >>
rw [] >>
every_case_tac);

val weakC_merge = Q.store_thm ("weakC_merge",
`!tenvC1 tenvC2 tenvC3.
  weakC tenvC1 tenvC2
  ⇒
  weakC (merge_tenvC tenvC3 tenvC1) (merge_tenvC tenvC3 tenvC2)`,
 rw [weakC_def] >>
 PairCases_on `tenvC1` >>
 PairCases_on `tenvC2` >>
 PairCases_on `tenvC3` >>
 fs [merge_tenvC_def]
 >- metis_tac [flat_weakC_merge]
 >- (fs [merge_def, lookup_append] >>
     every_case_tac >>
     fs [] >>
     rw [flat_weakC_refl]));

val weakC_merge_one_mod = Q.store_thm ("weakC_merge_one_mod",
`!tenvC1 tenvC2 flat_tenvC mn.
  mn ∉ set (MAP FST (FST tenvC1)) ∧
  weakC tenvC1 tenvC2
  ⇒
  weakC (merge_tenvC ([(mn, flat_tenvC)],emp) tenvC1) tenvC2`,
 rw [weakC_def] >>
 PairCases_on `tenvC1` >>
 fs [merge_tenvC_def, merge_def, emp_def] >>
 every_case_tac >>
 rw [] >>
 res_tac >>
 imp_res_tac lookup_in2);

val weakC_merge_one_mod2 = Q.store_thm ("weakC_merge_one_mod2",
`!tenvC1 tenvC2 flat_tenvC1 flat_tenvC2 mn.
  flat_weakC flat_tenvC1 flat_tenvC2 ∧
  weakC tenvC1 tenvC2
  ⇒
  weakC (merge_tenvC ([(mn, flat_tenvC1)],emp) tenvC1) (merge_tenvC ([(mn, flat_tenvC2)],emp) tenvC2)`,
 rw [weakC_def, emp_def] >>
 PairCases_on `tenvC1` >>
 PairCases_on `tenvC2` >>
 fs [merge_tenvC_def, merge_def] >>
 every_case_tac >>
 fs [] >>
 rw []);

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
  weak_tenvE (bind_tenv n tvs t tenv') (bind_tenv n tvs t tenv)`,
rw [weak_tenvE_def, num_tvs_def, bind_tenv_def, lookup_tenv_def] >>
every_case_tac >>
rw []);

val weak_tenvE_opt_bind = Q.prove (
`!tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_tenv n tvs t tenv') (opt_bind_tenv n tvs t tenv)`,
rw [weak_tenvE_def, num_tvs_def, opt_bind_tenv_def, lookup_tenv_def] >>
every_case_tac >>
fs [lookup_tenv_def, num_tvs_def] >>
every_case_tac >>
fs []);

val weak_tenvE_bind_tvar = Q.prove (
`!tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)`,
rw [weak_tenvE_def, num_tvs_def, bind_tvar_def, lookup_tenv_def] >>
decide_tac);

val weak_tenvE_bind_tvar2 = Q.prove (
`!tenv tenv' n tvs t.
  tenv_ok tenv ∧
  (num_tvs tenv = 0) ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)`,
rw [weak_tenvE_def, num_tvs_def, bind_tvar_def, lookup_tenv_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
metis_tac [lookup_tenv_inc_tvs]);

val weak_tenvE_bind_var_list = Q.prove (
`!tenv'' tenv tenv' n tvs t .
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_var_list tvs tenv'' tenv') (bind_var_list tvs tenv'' tenv)`,
induct_on `tenv''` >>
rw [weak_tenvE_def, bind_var_list_def, num_tvs_def] >>
PairCases_on `h` >>
fs [bind_var_list_def, num_tvs_def, bind_tenv_def, lookup_tenv_def,
    weak_tenvE_def, num_tvs_bind_var_list] >>
every_case_tac >>
fs [] >>
PROVE_TAC []);

val weak_tenvC_lookup = Q.prove (
`∀cn tenvC tenvC' tvs ts tn.
  weakC tenvC' tenvC ∧
  (lookup_con_id cn tenvC = SOME (tvs,ts,tn))
  ⇒
  (lookup_con_id cn tenvC' = SOME (tvs,ts,tn))`,
 rw [weakC_def] >>
 PairCases_on `tenvC` >>
 PairCases_on `tenvC'` >>
 fs [lookup_con_id_def] >>
 every_case_tac >>
 fs [flat_weakC_def]
 >- (LAST_X_ASSUM (mp_tac o Q.SPEC `a`) >>
     rw [] >>
     every_case_tac >>
     fs [])
 >- (FIRST_X_ASSUM (mp_tac o Q.SPEC `s`) >>
     rw [])
 >- (FIRST_X_ASSUM (mp_tac o Q.SPEC `s`) >>
     rw [] >>
     FIRST_X_ASSUM (mp_tac o Q.SPEC `a`) >>
     rw [] >>
     every_case_tac >>
     fs []));

val weakE_lookup = Q.prove (
`!n env env' tvs t.
  weakE env' env ∧
  (lookup n env = SOME (tvs, t))
  ⇒
  ?tvs' t' subst. 
    (lookup n env' = SOME (tvs', t')) ∧
    check_freevars tvs' [] t' ∧
    (LENGTH subst = tvs') ∧
    EVERY (check_freevars tvs []) subst ∧
    (deBruijn_subst 0 subst t' = t)`,
rw [weakE_def] >>
qpat_assum `!cn. P cn` (MP_TAC o Q.SPEC `n`) >>
rw [] >>
cases_on `lookup n env'` >>
fs [] >>
cases_on `x` >>
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
  (lookup mn tenvM = SOME tenv)
  ⇒
  ?tenv'.
    (lookup mn tenvM' = SOME tenv') ∧
    weakE tenv' tenv`,
induct_on `tenvM` >>
fs [weakM_def] >>
rw [] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = mn` >>
fs [] >>
rw [] >>
cases_on `lookup h0 tenvM'` >>
fs [EVERY_MEM, tenvM_ok_def]);

val type_p_weakening = Q.store_thm ("type_p_weakening",
`(!tvs tenvC p t tenv. type_p tvs tenvC p t tenv ⇒
    !tenvC' tvs'. tvs' ≥ tvs ∧ weakC tenvC' tenvC ⇒ type_p tvs' tenvC' p t tenv) ∧
 (!tvs tenvC ps ts tenv. type_ps tvs tenvC ps ts tenv ⇒
    !tenvC' tvs'. tvs' ≥ tvs ∧ weakC tenvC' tenvC ⇒ type_ps tvs' tenvC' ps ts tenv)`,
ho_match_mp_tac type_p_ind >>
rw [] >>
ONCE_REWRITE_TAC [type_p_cases] >>
rw [] >>
fs [EVERY_MEM] >>
metis_tac [check_freevars_add, EVERY_MEM, weak_tenvC_lookup]);

val type_e_weakening_lem = Q.prove (
`(!tenvM tenvC tenv e t. type_e tenvM tenvC tenv e t ⇒
    ∀tenvM' tenvC' tenv'. 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_e tenvM' tenvC' tenv' e t) ∧
 (!tenvM tenvC tenv es ts. type_es tenvM tenvC tenv es ts ⇒
    ∀tenvM' tenvC' tenv'. 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_es tenvM' tenvC' tenv' es ts) ∧
 (!tenvM tenvC tenv funs tenv''. type_funs tenvM tenvC tenv funs tenv'' ⇒
    ∀tenvM' tenvC' tenv'. 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_funs tenvM' tenvC' tenv' funs tenv'')`,
ho_match_mp_tac type_e_ind >>
rw [] >>
rw [Once type_e_cases] >|
[metis_tac [weak_tenvE_freevars],
 fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_p_weakening, weak_tenvE_def, weak_tenvE_bind_var_list],
 fs [EVERY_MEM] >>
     metis_tac [weak_tenvC_lookup, weak_tenvE_freevars],
 `(?vn. n = Short vn) ∨ (?mn vn. n = Long mn vn)` by (cases_on `n` >> rw []) >>
     rw [] >>
     fs [t_lookup_var_id_def] >|
     [fs [weak_tenvE_def] >>
          metis_tac [check_freevars_add, EVERY_MEM],
      cases_on `lookup mn tenvM` >>
          fs [] >>
          imp_res_tac weak_tenvM_lookup >>
          fs [] >>
          rw [] >>
          fs [] >>
          rw [] >>
          imp_res_tac weakE_lookup >>
          fs [] >>
          rw [] >>
          qexists_tac `MAP (deBruijn_subst 0 targs) subst'` >>
          rw [EVERY_MAP] >-
          metis_tac [deBruijn_subst2, deBruijn_inc0] >>
          `EVERY (check_freevars (num_tvs tenv') []) targs` 
                    by metis_tac [EVERY_MEM, weak_tenvE_freevars] >>
          rw [EVERY_MEM] >>
          match_mp_tac deBruijn_subst_check_freevars2 >>
          rw [] >>
          metis_tac [EVERY_MEM]],
 metis_tac [weak_tenvE_freevars, weak_tenvE_bind],
 metis_tac [weak_tenvE_bind, weak_tenvE_freevars],
 metis_tac [],
 fs [RES_FORALL] >>
     qexists_tac `t` >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_p_weakening, weak_tenvE_def, weak_tenvE_bind_var_list],
 metis_tac [weak_tenvE_opt_bind, weak_tenvE_bind_tvar],
 (* COMPLETENESS metis_tac [weak_tenvE_opt_bind, weak_tenvE_bind_tvar], *)
 metis_tac [weak_tenvE_bind_var_list, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar, weak_tenvE_freevars],
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar, weak_tenvE_freevars]]);

val type_e_weakening = Q.store_thm ("type_e_weakening",
`(!tenvM tenvC tenv e t tenvM' tenvC' tenv'. 
    type_e tenvM tenvC tenv e t ∧
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
    type_e tenvM' tenvC' tenv' e t) ∧
 (!tenvM tenvC tenv es ts tenvM' tenvC' tenv'.
    type_es tenvM tenvC tenv es ts ∧
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
    type_es tenvM' tenvC' tenv' es ts) ∧
 (!tenvM tenvC tenv funs tenv'' tenvM' tenvC' tenv'. 
    type_funs tenvM tenvC tenv funs tenv'' ∧
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
    type_funs tenvM' tenvC' tenv' funs tenv'')`,
metis_tac [type_e_weakening_lem]);

val gt_0 = Q.prove (
`!x:num.x ≥ 0`,
decide_tac);

val weakCT_def = Define `
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl`;

val weak_ctMap_lookup = Q.prove (
`∀cn ctMap ctMap' tvs ts tn.
  weakCT ctMap' ctMap ∧
  (FLOOKUP ctMap (cn,tn) = SOME (tvs,ts))
  ⇒
  (FLOOKUP ctMap' (cn,tn) = SOME (tvs,ts))`,
rw [weakCT_def] >>
metis_tac [FLOOKUP_SUBMAP]);

val weakCT_refl = Q.store_thm ("weakCT_refl",
`!ctMap. weakCT ctMap ctMap`,
rw [weakCT_def] >>
metis_tac [SUBMAP_REFL]);

val disjoint_env_weakCT = Q.store_thm ("disjoint_env_weakCT",
`!ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap`,
rw [weakCT_def] >>
metis_tac [SUBMAP_FUNION, DISJOINT_SYM, SUBMAP_REFL]);

val consistent_con_env_weakening = Q.prove (
`!ctMap (tenvC:tenvC) (envC:envC) ctMap'.
  consistent_con_env ctMap envC tenvC ∧
  ctMap_ok ctMap' ∧
  weakCT ctMap' ctMap
  ⇒
  consistent_con_env ctMap' envC tenvC`,
 rw [consistent_con_env_def] >>
 fs [weakCT_def] >>
 res_tac >>
 metis_tac [FLOOKUP_SUBMAP]);

val type_v_weakening = Q.store_thm ("type_v_weakening",
`(!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'. 
      ctMap_ok ctMap' ∧
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t) ∧
 (!tvs ctMap tenvS vs ts. type_vs tvs ctMap tenvS vs ts ⇒
    !tvs' ctMap' tenvS'. 
      ctMap_ok ctMap' ∧
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_vs tvs' ctMap' tenvS' vs ts) ∧
 (!ctMap tenvS env tenv. type_env ctMap tenvS env tenv ⇒
    !ctMap' tenvS'. 
      ctMap_ok ctMap' ∧
      weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_env ctMap' tenvS' env tenv) ∧
 (!tenvS ctMap envM tenvM. consistent_mod_env tenvS ctMap envM tenvM ⇒
    !ctMap' tenvS'. 
      ctMap_ok ctMap' ∧
      weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      consistent_mod_env tenvS' ctMap' envM tenvM)`,
 ho_match_mp_tac type_v_strongind >>
 rw [] >>
 rw [Once type_v_cases]
 >- (fs [EVERY_MEM] >>
     metis_tac [weak_ctMap_lookup, check_freevars_add, gt_0])
 >- (fs [EVERY_MEM] >>
     metis_tac [weak_ctMap_lookup, check_freevars_add, gt_0])
 >- (fs [] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >-
     metis_tac [check_freevars_add, gt_0] >>
     match_mp_tac (hd (CONJUNCTS type_e_weakening)) >>
     metis_tac [weak_tenvE_refl, weakM_refl, weakC_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >>
     match_mp_tac (hd (CONJUNCTS type_e_weakening)) >>
     metis_tac [weak_tenvE_refl, weakC_refl,weakM_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `tenv'` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >>
     match_mp_tac (hd (tl (tl (CONJUNCTS type_e_weakening)))) >>
     metis_tac [weak_tenvE_refl,weakM_refl, weakC_refl,
                weak_tenvE_bind_var_list, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `tenv'` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >>
     match_mp_tac (hd (tl (tl (CONJUNCTS type_e_weakening)))) >>
     metis_tac [weak_tenvE_refl,weakM_refl, weakC_refl,
                weak_tenvE_bind_var_list, weak_tenvE_bind_tvar2, type_v_freevars]) 
 >- (fs [weakS_def] >>
     metis_tac [])
 >- (fs [weakS_def] >>
     metis_tac [])
 >- (fs [weakS_def] >>
     metis_tac [])
 >- (fs [weakS_def] >>
     metis_tac [])
 >- (fs [weakS_def] >>
     metis_tac [])
 >- (fs [weakS_def] >>
     metis_tac [])
 >- fs [EVERY_MEM]
 >- fs [EVERY_MEM]
 >- rw [bind_def, emp_def, bind_tvar_def, bind_tenv_def]);

val type_ctxt_weakening = Q.store_thm ("type_ctxt_weakening",
`∀tvs tenvM ctMap tenvS tenv c t1 t2 tenvM' ctMap' tenvS' tenv' tenvC tenvC'.
    type_ctxt tvs tenvM ctMap tenvC tenvS tenv c t1 t2 ∧
    ctMap_ok ctMap' ∧ tenvM_ok tenvM' ∧ tenv_ok tenv ∧ (num_tvs tenv = 0) ∧ 
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ∧ weak_tenvE tenv' tenv ⇒
    type_ctxt tvs tenvM' ctMap' tenvC' tenvS' tenv' c t1 t2`,
 rw [type_ctxt_cases]
 >- (fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ 0``])
 >- metis_tac [type_v_weakening, type_e_weakening]
 >- metis_tac [type_e_weakening, weak_tenvE_refl]
 >- metis_tac [type_e_weakening]
 >- (fs [RES_FORALL] >>
     rw [] 
     >- (PairCases_on `x` >>
         rw [] >>
         res_tac >>
         fs [] >>
         metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ x``]) >>
     fs [Once type_v_cases] >>
     imp_res_tac type_funs_Tfn >>
     fs [] >>
     cases_on `tn` >>
     fs [tid_exn_to_tc_def] >>
     cases_on `tvs'` >>
     fs [] >>
     metis_tac [ZIP, LENGTH, weak_ctMap_lookup, type_v_weakening])
 >- metis_tac [check_freevars_add, gt_0, type_e_weakening, weak_tenvE_opt_bind]
 >- (qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     qexists_tac `t` >>
     qexists_tac `tn` >>
     qexists_tac `tvs'` >>
     rw [] >>
     metis_tac [gt_0, check_freevars_add, EVERY_MEM, type_e_weakening,
                weak_tenvE_bind_tvar, type_v_weakening, weak_tenvC_lookup])
 >- (qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     rw [] >>
     metis_tac [gt_0, check_freevars_add, EVERY_MEM, type_e_weakening,
                weak_tenvE_bind_tvar, type_v_weakening, weak_tenvC_lookup]));

val type_ctxts_weakening = Q.store_thm ("type_ctxts_weakening",
`∀tvs ctMap tenvS cs t1 t2. type_ctxts tvs ctMap tenvS cs t1 t2 ⇒
  !ctMap' tenvS'.
    ctMap_ok ctMap' ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
    type_ctxts tvs ctMap' tenvS' cs t1 t2`,
 ho_match_mp_tac type_ctxts_ind >>
 rw [] >>
 rw [Once type_ctxts_cases]
 >- (qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `t1'` >>
     rw [] >-
     metis_tac [type_v_weakening] >-
     metis_tac [consistent_con_env_weakening] >-
     metis_tac [type_v_weakening] >>
     match_mp_tac type_ctxt_weakening >>
     metis_tac [weak_tenvE_refl,weakM_refl,weakC_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars, type_v_weakening])
 >- (qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `t1'` >>
     rw [] >-
     metis_tac [type_v_weakening] >-
     metis_tac [consistent_con_env_weakening] >-
     metis_tac [type_v_weakening] >>
     match_mp_tac type_ctxt_weakening >>
     metis_tac [weak_tenvE_refl,weakM_refl, weakC_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars, type_v_weakening]));

val type_s_weakening = Q.store_thm ("type_s_weakening",
`!ctMap tenvS st ctMap'. 
  ctMap_ok ctMap' ∧
  type_s ctMap tenvS st ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' tenvS st`,
 rw [type_s_def] >>
 every_case_tac >>
 rw [] >>
 res_tac >>
 fs [EVERY_MEM] >>
 metis_tac [type_v_weakening, weakS_refl]);

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
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 PairCases_on `decls3` >>
 fs [weak_decls_only_mods_def, union_decls_def] >>
 metis_tac []);

val weak_decls_refl = Q.store_thm ("weak_decls_refl",
`!decls. weak_decls decls decls`,
 rw [] >>
 PairCases_on `decls` >>
 rw [weak_decls_def]);

val weak_decls_trans = Q.store_thm ("weak_decls_trans",
`!decls1 decls2 decls3. 
  weak_decls decls1 decls2 ∧
  weak_decls decls2 decls3
  ⇒
  weak_decls decls1 decls3`,
 rw [] >>
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 PairCases_on `decls3` >>
 fs [weak_decls_def, SUBSET_DEF]);

val weak_decls_other_mods_def = Define `
weak_decls_other_mods mn (mdecls',tdecls',edecls') (mdecls,tdecls,edecls) ⇔
  (!tid. tid ∈ tdecls' ∧ tid ∉ tdecls ⇒ ¬?tn. tid = mk_id mn tn) ∧ 
  (!cid. cid ∈ edecls' ∧ cid ∉ edecls ⇒ ¬?cn. cid = mk_id mn cn)`;

val weak_decls_other_mods_refl = Q.store_thm ("weak_decls_other_mods_refl",
`!mn decls. weak_decls_other_mods mn decls decls`,
 rw [] >>
 PairCases_on `decls` >>
 rw [weak_decls_other_mods_def]);

val type_d_weakening = Q.store_thm ("type_d_weakening",
`!mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv' decls'' tenvM'' tenvC''.
  type_d mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv' ∧
  weakM tenvM'' tenvM ∧ 
  weakC tenvC'' tenvC ∧
  weak_decls decls'' decls ∧ 
  weak_decls_other_mods mn decls'' decls ∧
  tenvC_ok tenvC''
  ⇒
  type_d mn decls'' tenvT tenvM'' tenvC'' tenv d decls' tenvT' tenvC' tenv'`,
 rw [type_d_cases]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- (`?mdecls'' tdecls'' edecls''. decls'' = (mdecls'',tdecls'',edecls'')` by metis_tac [pair_CASES] >>
     rw []
     >- (fs [DISJOINT_DEF, weak_decls_other_mods_def, EXTENSION] >>
         rw [] >>
         CCONTR_TAC >>
         fs [] >>
         res_tac >>
         fs [MEM_MAP] >>
         PairCases_on `y` >>
         fs [FORALL_PROD] >>
         rw [] >>
         metis_tac []))
 >- (`?mdecls'' tdecls'' edecls''. decls'' = (mdecls'',tdecls'',edecls'')` by metis_tac [pair_CASES] >>
     rw []
     >- (fs [weak_decls_other_mods_def] >>
         rw [] >>
         metis_tac [])));

val consistent_con_env_weakening = Q.store_thm ("consistent_con_env_weakening",
`!ctMap envC tenvC ctMap'.
  consistent_con_env ctMap envC tenvC ∧
  ctMap_ok ctMap' ∧
  weakCT ctMap' ctMap
  ⇒
  consistent_con_env ctMap' envC tenvC`,
 rw [weakCT_def, consistent_con_env_def] >>
 PairCases_on `envC` >>
 fs [lookup_con_id_def] >>
 every_case_tac >>
 fs []
 >- (FIRST_X_ASSUM (mp_tac o Q.SPECL [`Short a`, `n`, `t`]) >>
     rw [] >>
     metis_tac [FLOOKUP_SUBMAP])
 >- (FIRST_X_ASSUM (mp_tac o Q.SPECL [`Long s a`, `n`, `t`]) >>
     rw [] >>
     metis_tac [FLOOKUP_SUBMAP]));

val weak_decls_union = Q.store_thm ("weak_decls_union",
`!decls1 decls2 decls3.
  weak_decls decls1 decls2
  ⇒
  weak_decls (union_decls decls3 decls1) (union_decls decls3 decls2)`,
 rw [] >>
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 PairCases_on `decls3` >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF]);

val weak_decls_union2 = Q.store_thm ("weak_decls_union2",
`!decls1 decls2 decls3.
  FST decls1 = {}
  ⇒
  weak_decls (union_decls decls1 decls2) decls2`,
 rw [] >>
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 fs [weak_decls_def, union_decls_def, SUBSET_DEF]);

val weak_decls_other_mods_union = Q.store_thm ("weak_decls_other_mods_union",
`!mn decls1 decls2 decls3.
  weak_decls_other_mods mn decls1 decls2
  ⇒
  weak_decls_other_mods mn (union_decls decls3 decls1) (union_decls decls3 decls2)`,
 rw [] >>
 PairCases_on `decls1` >>
 PairCases_on `decls2` >>
 PairCases_on `decls3` >>
 fs [weak_decls_other_mods_def, union_decls_def] >>
 metis_tac []);

val type_ds_weakening = Q.store_thm ("type_ds_weakening",
`!mn decls tenvT tenvM tenvC tenv ds decls' tenvT' tenvC' tenv'.
  type_ds mn decls tenvT tenvM tenvC tenv ds decls' tenvT' tenvC' tenv' ⇒
  !decls'' tenvM'' tenvC''. 
  weak_decls decls'' decls ∧ 
  weak_decls_other_mods mn decls'' decls ∧
  tenvT_ok tenvT ∧
  tenvC_ok tenvC'' ∧ 
  weakM tenvM'' tenvM ∧
  weakC tenvC'' tenvC
  ⇒
  type_ds mn decls'' tenvT tenvM'' tenvC'' tenv ds decls' tenvT' tenvC' tenv'`,
 ho_match_mp_tac type_ds_ind >>
 rw [] >>
 rw [Once type_ds_cases] >>
 `type_d mn decls''' tenvT tenvM'' tenvC'' tenv d decls' tenvT' cenv' tenv'` by metis_tac [type_d_weakening] >>
 imp_res_tac type_d_ctMap_ok >>
 `tenvC_ok (merge_tenvC (emp,cenv') tenvC'')` 
        by (rw [tenvC_ok_merge, emp_def] >>
            metis_tac [ctMap_ok_tenvC_ok, MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
 `weak_decls (union_decls decls' decls''') (union_decls decls' decls)`
            by (metis_tac [weak_decls_union]) >>
 `weak_decls_other_mods mn (union_decls decls' decls''') (union_decls decls' decls)`
            by (metis_tac [weak_decls_other_mods_union]) >>
 fs [tenvT_ok_merge] >>
 imp_res_tac type_d_tenvT_ok >>
 fs [tenvT_ok_def, emp_def] >>
 metis_tac [weakC_merge, emp_def, merge_def]);

val consistent_decls_weakening = Q.store_thm ("consistent_decls_weakening",
`!decls1 decls2 decls3. 
  consistent_decls decls1 decls3 ∧
  weak_decls decls2 decls3
  ⇒
  consistent_decls decls1 decls2`,
 rw [] >>
 PairCases_on `decls2` >>
 PairCases_on `decls3` >>
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
 PairCases_on `tdecls` >>
 PairCases_on `tdecls'` >>
 fs [weak_decls_def, consistent_ctMap_def, RES_FORALL] >>
 rw [] >>
 PairCases_on `x` >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs [SUBSET_DEF]);

val type_ds_ctMap_disjoint = Q.store_thm ("type_ds_ctMap_disjoint",
`∀mn (tdecs1:decls) tenvT tenvM tenvC tenv ds tdecs1' tenvT' tenvC' tenv'.
  type_ds mn tdecs1 tenvT tenvM tenvC tenv ds tdecs1' tenvT' tenvC' tenv' 
  ⇒
  !(ctMap:ctMap). consistent_ctMap tdecs1 ctMap
  ⇒
  DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM ctMap) ∧
  DISJOINT (IMAGE SND (FDOM (flat_to_ctMap tenvC'))) (IMAGE SND (FDOM ctMap))`,
 ho_match_mp_tac type_ds_ind >>
 rw []
 >- rw [flat_to_ctMap_def, emp_def, flat_to_ctMap_list_def, FDOM_FUPDATE_LIST]
 >- rw [flat_to_ctMap_def, emp_def, flat_to_ctMap_list_def, FDOM_FUPDATE_LIST] >>
 rw [flat_to_ctMap_def, merge_def, flat_to_ctMap_list_append, FDOM_FUPDATE_LIST,
     DISJOINT_DEF, EXTENSION, REVERSE_APPEND] >>
 imp_res_tac type_d_ctMap_disjoint >>
 fs [DISJOINT_DEF, EXTENSION, flat_to_ctMap_def, FDOM_FUPDATE_LIST] >>
 metis_tac [weak_decls_union2, consistent_ctMap_weakening, type_d_mod]);

val _ = export_theory ();
