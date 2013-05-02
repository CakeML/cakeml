open preamble;
open optionTheory rich_listTheory;
open LibTheory AstTheory TypeSystemTheory typeSysPropsTheory;
open SemanticPrimitivesTheory;
open TypeSoundInvariantsTheory;
open terminationTheory metaTerminationTheory;

val _ = new_theory "weakening";

val weakC_mods_def = Define `
weakC_mods tenvC1 tenvC2 =
  { mn | 
    ?cn x. 
      (lookup (mk_id mn cn) tenvC1 = SOME x) ∧ (lookup (mk_id mn cn) tenvC2 = NONE) }`;

val weakC_mods_merge = Q.prove (
`!tenvC1 tenvC2 tenvC3. 
  ALL_DISTINCT (MAP FST (merge tenvC1 tenvC2)) ⇒
  (weakC_mods (merge tenvC1 tenvC2) (merge tenvC1 tenvC3) =
   weakC_mods tenvC2 tenvC3)`,
rw [weakC_mods_def, merge_def, lookup_append, EXTENSION] >>
eq_tac >>
rw [] >-
metis_tac [option_case_def, NOT_SOME_NONE, SOME_11, option_nchotomy] >>
qexists_tac `cn` >>
qexists_tac `x'` >>
rw [] >>
cases_on `lookup (mk_id x cn) tenvC1` >>
rw [] >>
fs [ALL_DISTINCT_APPEND] >>
imp_res_tac lookup_in2 >>
metis_tac []);

val tenvC_one_mod_def = Define `
tenvC_one_mod tenvC mn =
  !mn' cn x. 
    (lookup (mk_id mn' cn) tenvC = SOME x)  
    ⇒
    (mn = mn')`;

val build_ctor_tenv_one_mod = Q.prove (
`!mn tdecs.
  tenvC_one_mod (build_ctor_tenv mn tdecs) mn`,
rw [tenvC_one_mod_def, lookup_def, build_ctor_tenv_def] >>
induct_on `tdecs` >>
rw [] >>
fs [lookup_append] >>
PairCases_on `h` >>
fs [] >>
cases_on `lookup (mk_id mn' cn) (MAP (λ(cn,ts). (mk_id mn cn,h0,ts,mk_id mn h1)) h2)` >>
fs [] >>
rw [] >>
pop_assum mp_tac >>
pop_assum (fn _ => all_tac) >>
induct_on `h2` >>
rw [lookup_def] >>
PairCases_on `h` >>
fs [] >>
cases_on `mk_id mn h0' = mk_id mn' cn` >>
fs [] >>
Cases_on `mn` >>
Cases_on `mn'` >>
fs [mk_id_def]);

val tenvC_one_mod_merge = Q.prove (
`!tenvC1 tenvC2 mn.
  tenvC_one_mod tenvC1 mn ∧
  tenvC_one_mod tenvC2 mn
  ⇒
  tenvC_one_mod (merge tenvC1 tenvC2) mn`,
rw [tenvC_one_mod_def, merge_def, lookup_append] >>
every_case_tac >>
fs [] >>
metis_tac []);

val weak_tenvE_def = Define `
weak_tenvE tenv tenv' = 
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t. 
    (lookup_tenv n inc tenv' = SOME (tvs,t)) ⇒
    (lookup_tenv n inc tenv = SOME (tvs,t)))`;

val weakM_def = Define `
weakM tenvM tenvM' =
  !mn tenv'.
    (lookup mn tenvM' = SOME tenv')
    ⇒
    (?tenv. (lookup mn tenvM = SOME tenv) ∧
            weakE tenv tenv')`;

val weakS_def = Define `
weakS tenvS tenvS' =
  !l v. (lookup l tenvS' = SOME v) ⇒ (lookup l tenvS = SOME v)`;

val weak_tenvE_refl = Q.prove (
`!tenv. weak_tenvE tenv tenv`,
rw [weak_tenvE_def]);

val weakC_refl = Q.store_thm ("weakC_refl",
`!tenvC. weakC tenvC tenvC`,
rw [weakC_def] >>
full_case_tac >>
rw [] >>
PairCases_on `x` >>
rw []);

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
full_case_tac >>
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

val weakS_bind = Q.store_thm ("weakS_bind",
`!l t tenvS.
  (lookup l tenvS = NONE) ⇒
  weakS (bind l t tenvS) tenvS`,
rw [weakS_def, bind_def, lookup_def] >>
full_case_tac >>
rw [] >>
fs []);

val disjoint_env_weakC = Q.store_thm ("disjoint_env_weakC",
`!tenvC tenvC'.
  disjoint_env tenvC' tenvC ⇒
  weakC (merge tenvC' tenvC) tenvC`,
rw [weakC_def] >>
cases_on `lookup cn tenvC` >>
rw [] >>
cases_on `lookup cn (merge tenvC' tenvC)` >>
rw [] >-
metis_tac [NOT_SOME_NONE, lookup_disjoint, disjoint_env_def, DISJOINT_SYM] >>
PairCases_on `x` >>
fs [lookup_append, merge_def] >>
PairCases_on `x'` >>
rw [] >>
cases_on `lookup cn tenvC'` >>
fs [] >>
rw [] >>
fs [disjoint_env_def, DISJOINT_DEF] >>
imp_res_tac lookup_in2 >>
fs [EXTENSION] >>
metis_tac []);

val weakC_merge = Q.store_thm ("weakC_merge",
`!tenvC1 tenvC2 tenvC3.
  weakC tenvC1 tenvC2
  ⇒
  weakC (merge tenvC3 tenvC1) (merge tenvC3 tenvC2)`,
rw [weakC_def, merge_def, lookup_append] >>
pop_assum (mp_tac o Q.SPEC `cn`) >>
rw [] >>
every_case_tac);

val weakC_merge2 = Q.store_thm ("weakC_merge2",
`!tenvC1 tenvC2 tenvC3.
  disjoint_env tenvC1 tenvC3 ∧
  weakC tenvC1 tenvC2
  ⇒
  weakC (merge tenvC1 tenvC3) (merge tenvC2 tenvC3)`,
rw [weakC_def, merge_def, lookup_append] >>
pop_assum (mp_tac o Q.SPEC `cn`) >>
rw [] >>
every_case_tac >>
imp_res_tac lookup_in2 >>
fs [disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
metis_tac []);

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
full_case_tac >>
rw []);

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
metis_tac [lookup_tenv_inc]);

val weak_tenvE_bind_var_list = Q.prove (
`!tenv'' tenv tenv' n tvs t .
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_var_list tvs tenv'' tenv') (bind_var_list tvs tenv'' tenv)`,
induct_on `tenv''` >>
rw [weak_tenvE_def, bind_var_list_def, num_tvs_def] >>
PairCases_on `h` >>
fs [bind_var_list_def, num_tvs_def, bind_tenv_def, lookup_tenv_def,
    weak_tenvE_def, num_tvs_bind_var_list] >>
full_case_tac >>
fs [] >>
PROVE_TAC []);

val weak_tenvC_lookup = Q.prove (
`∀cn tenvC tenvC' tvs ts tn.
  weakC tenvC' tenvC ∧
  (lookup cn tenvC = SOME (tvs,ts,tn))
  ⇒
  (lookup cn tenvC' = SOME (tvs,ts,tn))`,
rw [weakC_def] >>
qpat_assum `!cn. P cn` (MP_TAC o Q.SPEC `cn`) >>
rw [] >>
cases_on `lookup cn tenvC'` >>
fs [] >>
PairCases_on `x` >>
fs []);

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

val type_e_weakening = Q.store_thm ("type_e_weakening",
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
 metis_tac [weak_tenvE_bind], 
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
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind_var_list, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar, weak_tenvE_freevars]]);

val gt_0 = Q.prove (
`!x:num.x ≥ 0`,
decide_tac);

val type_v_freevars = Q.store_thm ("type_v_freevars",
`(!tvs tenvM tenvC tenvS v t. type_v tvs tenvM tenvC tenvS v t ⇒
   tenvM_ok tenvM ⇒
   check_freevars tvs [] t) ∧
 (!tvs tenvM tenvC tenvS vs ts. type_vs tvs tenvM tenvC tenvS vs ts ⇒
   tenvM_ok tenvM ⇒
   EVERY (check_freevars tvs []) ts) ∧
 (!tenvM tenvC tenvS env tenv. type_env tenvM tenvC tenvS env tenv ⇒
   tenvM_ok tenvM ⇒
   tenv_ok tenv ∧ (num_tvs tenv = 0))`,
ho_match_mp_tac type_v_strongind >>
rw [check_freevars_def, tenv_ok_def, bind_tenv_def, num_tvs_def, bind_tvar_def,
    Tfn_def, Tbool_def, Tint_def, Tunit_def, Tref_def] >-
metis_tac [] >>
res_tac >|
[metis_tac [num_tvs_def, type_e_freevars, bind_tenv_def, bind_tvar_def,
            tenv_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM],
 metis_tac [num_tvs_def, type_e_freevars, bind_tenv_def, bind_tvar_def,
            tenv_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM],
 metis_tac [type_funs_Tfn, num_tvs_bind_var_list],
 metis_tac [type_funs_Tfn, num_tvs_bind_var_list, num_tvs_def,
            arithmeticTheory.ADD, arithmeticTheory.ADD_COMM],
 metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ]]);

val type_v_weakening = Q.store_thm ("type_v_weakening",
`(!tvs tenvM tenvC tenvS v t. type_v tvs tenvM tenvC tenvS v t ⇒
    !tvs' tenvM' tenvC' tenvS'. 
      tenvM_ok tenvM' ∧ ((tvs = 0) ∨ (tvs = tvs')) ∧ weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ⇒
      type_v tvs' tenvM' tenvC' tenvS' v t) ∧
 (!tvs tenvM tenvC tenvS vs ts. type_vs tvs tenvM tenvC tenvS vs ts ⇒
    !tvs' tenvM' tenvC' tenvS'. 
      tenvM_ok tenvM' ∧ ((tvs = 0) ∨ (tvs = tvs')) ∧ weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ⇒
      type_vs tvs' tenvM' tenvC' tenvS' vs ts) ∧
 (!tenvM tenvC tenvS env tenv. type_env tenvM tenvC tenvS env tenv ⇒
    !tenvM' tenvC' tenvS'. 
      tenvM_ok tenvM' ∧ weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ⇒
      type_env tenvM' tenvC' tenvS' env tenv)`,
ho_match_mp_tac type_v_strongind >>
rw [] >>
rw [Once type_v_cases] >|
[fs [EVERY_MEM] >>
     metis_tac [weak_tenvC_lookup, check_freevars_add, gt_0],
 fs [EVERY_MEM] >>
     metis_tac [weak_tenvC_lookup, check_freevars_add, gt_0],
 metis_tac [type_e_weakening, check_freevars_add, weak_tenvE_refl, 
            weak_tenvE_bind, weak_tenvE_bind_tvar2, gt_0, type_v_freevars],
 metis_tac [type_e_weakening, check_freevars_add, weak_tenvE_refl, 
            weak_tenvE_bind, weak_tenvE_bind_tvar2, gt_0, type_v_freevars],
 metis_tac [type_e_weakening, check_freevars_add, weak_tenvE_refl, 
            weak_tenvE_bind_var_list, weak_tenvE_bind_tvar2, gt_0, type_v_freevars],
 metis_tac [type_e_weakening, check_freevars_add, weak_tenvE_refl, 
            weak_tenvE_bind_var_list, weak_tenvE_bind_tvar2, gt_0, type_v_freevars],
 fs [weakS_def] >>
     metis_tac [],
 fs [weakS_def] >>
     metis_tac [],
 rw [bind_def, emp_def, bind_tvar_def, bind_tenv_def]]);

 (*
val type_ctxt_weakening = Q.store_thm ("type_ctxt_weakening",
`∀tvs tenvM tenvC tenvS tenv c t1 t2. type_ctxt tvs tenvM tenvC tenvS tenv c t1 t2 ⇒
  !tenvM' tenvC' tenvS' tenv' tvs'.
    tenvM_ok tenvM' ∧ tenv_ok tenv ∧ (num_tvs tenv = 0) ∧ ((tvs = 0) ∨ (tvs = tvs')) ∧ 
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ∧ weak_tenvE tenv' tenv ⇒
    type_ctxt tvs' tenvM' tenvC' tenvS' tenv' c t1 t2`,
rw [type_ctxt_cases] >|
[metis_tac [type_e_weakening, weak_tenvE_bind],
 metis_tac [type_e_weakening, weak_tenvE_bind],
 metis_tac [check_freevars_add, gt_0],
 metis_tac [check_freevars_add, gt_0, type_e_weakening, weak_tenvE_bind],
 metis_tac [type_e_weakening, weak_tenvE_refl],
 metis_tac [check_freevars_add, gt_0, type_v_weakening, weak_tenvE_bind],
 metis_tac [type_v_weakening],
 metis_tac [type_e_weakening],
 metis_tac [type_e_weakening],
 metis_tac [type_e_weakening],
 metis_tac [type_e_weakening],
 fs [RES_FORALL] >>
     rw [] >-
     metis_tac [check_freevars_add, gt_0] >>
     PairCases_on `x` >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, gt_0],
 fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ x``],
 metis_tac [check_freevars_add, gt_0, type_e_weakening, weak_tenvE_bind],
 metis_tac [type_e_weakening, weak_tenvE_bind],
 qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     qexists_tac `t` >>
     qexists_tac `tvs'` >>
     rw [] >>
     metis_tac [gt_0, check_freevars_add, EVERY_MEM, type_e_weakening,
                weak_tenvE_bind_tvar2, type_v_weakening, weak_tenvC_lookup],
 qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     qexists_tac `t` >>
     qexists_tac `tvs'` >>
     rw [] >>
     metis_tac [gt_0, check_freevars_add, EVERY_MEM, type_e_weakening,
                weak_tenvE_bind_tvar, type_v_weakening, weak_tenvC_lookup]]);
                *)

val type_ctxt_weakening = Q.store_thm ("type_ctxt_weakening",
`∀tvs tenvM tenvC tenvS tenv c t1 t2. type_ctxt tvs tenvM tenvC tenvS tenv c t1 t2 ⇒
  !tenvM' tenvC' tenvS' tenv'.
    tenvM_ok tenvM' ∧ tenv_ok tenv ∧ (num_tvs tenv = 0) ∧ 
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ∧ weak_tenvE tenv' tenv ⇒
    type_ctxt tvs tenvM' tenvC' tenvS' tenv' c t1 t2`,
rw [type_ctxt_cases] >|
[metis_tac [type_e_weakening, weak_tenvE_bind],
 metis_tac [type_e_weakening, weak_tenvE_refl],
 metis_tac [type_v_weakening],
 metis_tac [type_e_weakening],
 metis_tac [type_e_weakening],
 fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ x``],
 metis_tac [check_freevars_add, gt_0, type_e_weakening, weak_tenvE_bind],
 qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     qexists_tac `t` >>
     qexists_tac `tvs'` >>
     rw [] >>
     metis_tac [gt_0, check_freevars_add, EVERY_MEM, type_e_weakening,
                weak_tenvE_bind_tvar, type_v_weakening, weak_tenvC_lookup]]);

val type_ctxts_weakening = Q.store_thm ("type_ctxts_weakening",
`∀tvs tenvM tenvC tenvS cs t1 t2. type_ctxts tvs tenvM tenvC tenvS cs t1 t2 ⇒
  !tenvM' tenvC' tenvS'.
    tenvM_ok tenvM' ∧ weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakS tenvS' tenvS ⇒
    type_ctxts tvs tenvM' tenvC' tenvS' cs t1 t2`,
ho_match_mp_tac type_ctxts_ind >>
rw [] >>
rw [Once type_ctxts_cases] >>
metis_tac [type_v_weakening, type_ctxt_weakening, type_v_freevars, weak_tenvE_refl, check_freevars_add, gt_0]);

val consistent_mod_env_weakening = Q.store_thm ("consistent_mod_env_weakening",
`!tenvS tenvC menv tenvM tenvS' tenvC'.
  tenvM_ok tenvM ∧ consistent_mod_env tenvS tenvC menv tenvM ∧
  weakS tenvS' tenvS ∧ weakC tenvC' tenvC 
  ⇒
  consistent_mod_env tenvS' tenvC' menv tenvM`,
ho_match_mp_tac consistent_mod_env_ind >>
rw [consistent_mod_env_def, tenvM_ok_def] >>
metis_tac [type_v_weakening, weakM_refl, tenvM_ok_def]);

val type_s_weakening = Q.store_thm ("type_s_weakening",
`!tenvM tenvC tenvS st tenvM' tenvC'. 
  tenvM_ok tenvM' ∧
  type_s tenvM tenvC tenvS st ∧
  weakM tenvM' tenvM ∧ weakC tenvC' tenvC
  ⇒
  type_s tenvM' tenvC' tenvS st`,
rw [type_s_def] >>
metis_tac [type_v_weakening, weakS_refl]);

val weak_other_mods_def = Define `
weak_other_mods mn tenvC' tenvC =
  !cn.
    lookup (mk_id mn cn) tenvC' = lookup (mk_id mn cn) tenvC`;

val weak_other_mods_merge = Q.prove (
`!mn tenvC1 tenvC2 tenvC3.
  weak_other_mods mn tenvC2 tenvC3
  ⇒
  weak_other_mods mn (merge tenvC1 tenvC2) (merge tenvC1 tenvC3)`,
rw [weak_other_mods_def, merge_def, lookup_append] >>
eq_tac >>
rw [] >>
metis_tac []);

val check_dup_ctors_weakening = Q.store_thm ("check_dup_ctors_weakening",
`!mn tenvC tdecs tenvC'.
  check_dup_ctors mn tenvC tdecs ∧
  weakC tenvC' tenvC ∧
  weak_other_mods mn tenvC' tenvC
  ⇒
  check_dup_ctors mn tenvC' tdecs`,
rw [check_dup_ctors_def, RES_FORALL] >>
PairCases_on `x` >>
rw [] >>
PairCases_on `x` >>
rw [] >>
res_tac >>
fs [] >>
res_tac >>
fs [] >>
metis_tac [weak_other_mods_def]);

val check_ctor_tenv_weakening_lem = Q.prove (
`!tenvC id x y z.
 ALL_DISTINCT (MAP FST tenvC) ⇒
 ((lookup id tenvC = SOME (x,y,z))
  =
  MEM (id,x,y,z) tenvC)`,
Induct_on `tenvC` >>
rw [] >>
PairCases_on `h` >>
fs [] >>
every_case_tac >>
rw [] >>
fs [MEM_MAP] >>
eq_tac >>
rw [] >>
metis_tac [FST]);

val check_ctor_tenv_weakening = Q.store_thm ("check_ctor_tenv_weakening",
`!mn tenvC tdecs tenvC'.
  tenvC_ok tenvC' ∧
  tenvC_ok tenvC ∧
  check_ctor_tenv mn tenvC tdecs ∧
  weak_other_mods mn tenvC' tenvC ∧
  weakC tenvC' tenvC
  ⇒
  check_ctor_tenv mn tenvC' tdecs`,
rw [check_ctor_tenv_def] >-
metis_tac [check_dup_ctors_weakening] >>
fs [EVERY_MEM] >>
rw [] >>
res_tac >>
PairCases_on `e` >>
fs [] >>
rw [] >>
PairCases_on `p` >>
rw [] >>
fs [weak_other_mods_def] >>
cases_on `?cn. p0 = mk_id mn cn` >>
rw [] >|
[res_tac >>
     fs [] >>
     rw [] >>
     `ALL_DISTINCT (MAP FST tenvC')` by fs [tenvC_ok_def] >>
     fs [GSYM check_ctor_tenv_weakening_lem] >>
     `ALL_DISTINCT (MAP FST tenvC)` by fs [tenvC_ok_def] >>
     `MEM (mk_id mn cn,p1,p2,p3) tenvC` by metis_tac [check_ctor_tenv_weakening_lem] >>
     res_tac >>
     fs [],
 fs [tenvC_ok_def, EVERY_MEM] >>
     res_tac >>
     fs [] >>
     cases_on `p0` >>
     cases_on `p3` >>
     fs [same_module_def] >>
     cases_on `mn` >>
     fs [mk_id_def]]);

val type_d_weakening = Q.store_thm ("type_d_weakening",
`!mn tenvM tenvC tenv d tenvC' tenv' tenvM'' tenvC''.
  weak_other_mods mn tenvC'' tenvC ∧
  tenvC_ok tenvC'' ∧
  tenvC_ok tenvC ∧
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  weakM tenvM'' tenvM ∧ weakC tenvC'' tenvC
  ⇒
  type_d mn tenvM'' tenvC'' tenv d tenvC' tenv'`,
rw [type_d_cases] >|
[metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, 
            DECIDE ``!x:num. x ≥ x``],
 metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, 
            DECIDE ``!x:num. x ≥ x``],
 metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, 
            DECIDE ``!x:num. x ≥ x``],
 metis_tac [check_ctor_tenv_weakening]]);

val type_ds_weakening = Q.store_thm ("type_ds_weakening",
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !tenvM'' tenvC''. 
  weak_other_mods mn tenvC'' tenvC ∧ tenvC_ok tenvC'' ∧ weakM tenvM'' tenvM ∧
  weakC tenvC'' tenvC ∧ tenvC_ok tenvC
  ⇒
  type_ds mn tenvM'' tenvC'' tenv ds tenvC' tenv'`,
ho_match_mp_tac type_ds_ind >>
rw [] >>
rw [Once type_ds_cases] >>
`weak_other_mods mn (merge cenv' tenvC'') (merge cenv' tenvC)`
         by metis_tac [weak_other_mods_merge] >>
`tenvC_ok (merge cenv' tenvC'') ∧ tenvC_ok (merge cenv' tenvC)` 
       by (`type_d mn tenvM'' tenvC'' tenv d cenv' tenv'` by metis_tac [type_d_weakening] >>
           `tenvC_ok cenv' ∧ disjoint_env cenv' tenvC'' ∧ disjoint_env cenv' tenvC` by metis_tac [type_d_tenvC_ok] >>
           rw [tenvC_ok_merge] >>
           metis_tac []) >>
metis_tac [type_d_weakening, weakC_merge]);

val weakC_not_NONE = Q.prove (
`!tenvC1 tenvC2 l.
  weakC tenvC1 tenvC2 ∧
  weakC_mods tenvC1 tenvC2 ⊆ set (MAP SOME l)
  ⇒
  weak_other_mods NONE tenvC1 tenvC2`,
rw [MEM_MAP, weakC_def, weak_other_mods_def, weakC_mods_def, SUBSET_DEF] >>
pop_assum (mp_tac o Q.SPEC `NONE`) >>
pop_assum (mp_tac o Q.SPEC `mk_id NONE cn`) >>
rw [] >>
every_case_tac >>
metis_tac [NOT_SOME_NONE, SOME_11, option_case_def, option_nchotomy, mk_id_def]);

val weakC_not_SOME = Q.prove (
`!tenvC1 tenvC2 mn l.
  mn ∉ set l ∧
  weakC tenvC1 tenvC2 ∧
  weakC_mods tenvC1 tenvC2 ⊆ set (MAP SOME l)
  ⇒
  weak_other_mods (SOME mn) tenvC1 tenvC2`,
rw [MEM_MAP, weakC_def, weak_other_mods_def, weakC_mods_def, SUBSET_DEF] >>
pop_assum (mp_tac o Q.SPEC `(SOME mn)`) >>
pop_assum (mp_tac o Q.SPEC `mk_id (SOME mn) cn`) >>
rw [] >>
every_case_tac >>
metis_tac [NOT_SOME_NONE, SOME_11, option_case_def, option_nchotomy, mk_id_def]);

val type_prog_ignore_sig_weakening = Q.store_thm ("type_prog_ignore_sig_weakening",
`!tenvM tenvC tenv prog tenvM' tenvC' tenv'.
  type_prog_ignore_sig tenvM tenvC tenv prog tenvM' tenvC' tenv' ⇒
  !tenvM'' tenvC''. 
    weakM tenvM'' tenvM ∧ 
    weakC tenvC'' tenvC ∧
    weakC_mods tenvC'' tenvC ⊆ set (MAP SOME (MAP FST tenvM)) ∧
    (num_tvs tenv = 0) ∧
    (MAP FST tenvM = MAP FST tenvM'') ∧
    (tenvC_ok tenvC'') ∧
    (tenvC_ok tenvC)
    ⇒
    type_prog_ignore_sig tenvM'' tenvC'' tenv prog tenvM' tenvC' tenv'`,
ho_match_mp_tac type_prog_ignore_sig_ind >>
rw [num_tvs_bvl2] >>
rw [Once type_prog_ignore_sig_cases] >|
[`weak_other_mods NONE tenvC'' tenvC` by metis_tac [weakC_not_NONE] >>
     `type_d NONE tenvM'' tenvC'' tenv d cenv' tenv'` by metis_tac [type_d_weakening] >>
     `tenvC_ok cenv' ∧ disjoint_env cenv' tenvC ∧ disjoint_env cenv' tenvC''`
               by metis_tac [type_d_tenvC_ok] >>
     `tenvC_ok (merge cenv' tenvC) ∧ tenvC_ok (merge cenv' tenvC'')` 
                by rw [tenvC_ok_merge] >>
     metis_tac [tenvC_ok_def, weakC_merge, weakC_mods_merge],
 MAP_EVERY qexists_tac [`cenv'`, `tenvM'`, `tenv'`, `tenvC'`] >>
     rw [] >>
     `weak_other_mods (SOME mn) tenvC'' tenvC` by metis_tac [weakC_not_SOME] >|
     [metis_tac [],
      metis_tac [type_ds_weakening],
      `tenv_ok (bind_var_list2 tenv' Empty)` by metis_tac [type_ds_tenv_ok] >>
          `type_ds (SOME mn) tenvM'' tenvC'' tenv ds1 cenv' tenv'` 
                        by metis_tac [type_ds_weakening] >>
          `tenvC_ok cenv' ∧ disjoint_env cenv' tenvC ∧ disjoint_env cenv' tenvC''`
                    by metis_tac [type_ds_tenvC_ok] >>
          `tenvC_ok (merge cenv' tenvC'') ∧ tenvC_ok (merge cenv' tenvC)` 
                    by rw [tenvC_ok_merge] >>
          `weakC_mods tenvC'' tenvC ⊆ set (MAP SOME (MAP FST (bind mn tenv' tenvM)))`
                  by fs [bind_def, lookup_def, SUBSET_DEF] >>
          qpat_assum `!x. P x` match_mp_tac >>
          rw [] >>
          metis_tac [tenvC_ok_def, bind_def, MAP,weakC_merge, weakM_bind2, weakC_mods_merge, FST]]]);

val type_d_mod = Q.prove (
`∀mn tenvM tenvC tenv d tenvC' tenv'.
  type_d mn tenvM tenvC tenv d tenvC' tenv'
  ⇒
  tenvC_one_mod tenvC' mn`,
rw [type_d_cases, emp_def] >|
[rw [tenvC_one_mod_def],
 rw [tenvC_one_mod_def],
 rw [tenvC_one_mod_def],
 metis_tac [build_ctor_tenv_one_mod]]);

val type_ds_mod = Q.prove (
`∀mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv'
  ⇒
  tenvC_one_mod tenvC' mn`,
ho_match_mp_tac type_ds_ind >>
rw [emp_def] >-
rw [tenvC_one_mod_def] >>
metis_tac [tenvC_one_mod_merge, type_d_mod]);

val weakC_disjoint = Q.prove (
`!tenvC1 tenvC2 tenvC3.
  weakC tenvC1 tenvC2 ∧
  disjoint_env tenvC1 tenvC3
  ⇒
  disjoint_env tenvC2 tenvC3`,
rw [weakC_def, disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
pop_assum (mp_tac o Q.SPEC `x`) >>
pop_assum (mp_tac o Q.SPEC `x`) >>
rw [] >>
rw [] >>
`lookup x tenvC1 = NONE` by metis_tac [lookup_in2, option_nchotomy] >>
fs [] >>
cases_on `lookup x tenvC2` >>
fs [lookup_notin] >>
PairCases_on `x'` >>
fs []);

val type_prog_type_prog_ignore_sig = Q.store_thm ("type_prog_type_prog_ignore_sig",
`!tenvM tenvC tenv prog tenvM' tenvC' tenv'.
  type_prog tenvM tenvC tenv prog tenvM' tenvC' tenv' ⇒
  tenvC_ok tenvC ∧
  (num_tvs tenv = 0) ∧
  tenvM_ok tenvM ⇒
  ?tenvM'' tenvC'' tenv''. type_prog_ignore_sig tenvM tenvC tenv prog tenvM'' tenvC'' tenv''`,
ho_match_mp_tac type_prog_ind >>
rw [num_tvs_bvl2] >>
rw [Once type_prog_ignore_sig_cases] >>
`tenvC_ok cenv' ∧ disjoint_env cenv' tenvC`
         by metis_tac [type_ds_tenvC_ok, type_d_tenvC_ok] >>
`tenvC_ok (merge cenv' tenvC)` by rw [tenvC_ok_merge] >|
[metis_tac [],
 fs [check_signature_cases] >>
     `tenv_ok (bind_var_list2 emp Empty)` by rw [emp_def, bind_var_list2_def, tenv_ok_def] >>
     `tenv_ok (bind_var_list2 tenv'' Empty)` by metis_tac [type_ds_tenv_ok, type_specs_tenv_ok] >>
     `tenvM_ok (bind mn tenv'' tenvM)` 
                by (fs [tenvM_ok_def, bind_def] >>
                    metis_tac []) >-
     metis_tac [] >>
     fs [] >>
     rw [] >>
     rw [] >>
     `MAP FST (bind mn tenv'' tenvM) = MAP FST (bind mn tenv' tenvM)` by rw [bind_def] >>
     `disjoint_env cenv' tenvC` by metis_tac [type_ds_tenvC_ok] >>
     `tenvC_ok (emp:tenvC)` by rw [emp_def, tenvC_ok_def] >>
     `tenvC_ok cenv''` by metis_tac [type_specs_tenvC_ok] >>
     `disjoint_env cenv'' tenvC` by metis_tac [weakC_disjoint] >>
     `tenvC_ok (merge cenv'' tenvC)` 
             by rw [tenvC_ok_merge] >>
     fs [] >>
     MAP_EVERY qexists_tac [`tenv'''`, `cenv'`, `tenvM''`, `tenv'`, `tenvC''`] >>
     rw [] >>
     imp_res_tac type_ds_mod >>
     `weakC_mods (merge cenv' tenvC) (merge cenv'' tenvC) ⊆ {SOME mn}`
                 by (rw [weakC_mods_def] >>
                     fs [SUBSET_DEF, tenvC_one_mod_def, merge_def, lookup_append] >>
                     rw [] >>
                     cases_on `lookup (mk_id x cn) cenv'` >>
                     cases_on `lookup (mk_id x cn) cenv''` >>
                     metis_tac [NOT_SOME_NONE, option_case_def]) >> 
     `weakC_mods (merge cenv' tenvC) (merge cenv'' tenvC) ⊆ set (MAP SOME (MAP FST (bind mn tenv'' tenvM)))`
                  by fs [bind_def, SUBSET_DEF] >>
     metis_tac [type_prog_ignore_sig_weakening, weakM_bind3, weakC_merge2]]);

val _ = export_theory ();
