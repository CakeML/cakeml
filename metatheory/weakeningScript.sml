open preamble;
open optionTheory rich_listTheory;
open libTheory astTheory typeSystemTheory typeSysPropsTheory;
open semanticPrimitivesTheory;
open typeSoundInvariantsTheory;
open terminationTheory;

val _ = new_theory "weakening";

(*
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
cases_on `lookup (mk_id mn' cn) (MAP (λ(cn,ts). (mk_id mn cn,h0,ts,TypeId (mk_id mn h1))) h2)` >>
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

*)

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
every_case_tac);

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

val weakS_bind = Q.store_thm ("weakS_bind",
`!l t tenvS.
  (lookup l tenvS = NONE) ⇒
  weakS (bind l t tenvS) tenvS`,
rw [weakS_def, bind_def, lookup_def] >>
every_case_tac >>
rw [] >>
fs []);

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
every_case_tac >>
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
every_case_tac >>
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
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind, weak_tenvE_bind_tvar],
 metis_tac [weak_tenvE_bind_var_list, weak_tenvE_bind_tvar],
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

val type_v_freevars = Q.store_thm ("type_v_freevars",
`(!tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒
   check_freevars tvs [] t) ∧
 (!tvs tenvC tenvS vs ts. type_vs tvs tenvC tenvS vs ts ⇒
   EVERY (check_freevars tvs []) ts) ∧
 (!tenvC tenvS env tenv. type_env tenvC tenvS env tenv ⇒
   tenv_ok tenv ∧ (num_tvs tenv = 0)) ∧
 (!tenvS tenvC envM tenvM. consistent_mod_env tenvS tenvC envM tenvM ⇒
   T)`,
 ho_match_mp_tac type_v_strongind >>
 rw [check_freevars_def, tenv_ok_def, bind_tenv_def, num_tvs_def, bind_tvar_def,
     Tfn_def, Tbool_def, Tint_def, Tunit_def, Tref_def] >-
 metis_tac [] >>
 res_tac
 >- metis_tac [num_tvs_def, type_e_freevars, bind_tenv_def, bind_tvar_def,
               tenv_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]
 >- metis_tac [num_tvs_def, type_e_freevars, bind_tenv_def, bind_tvar_def,
               tenv_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]
 >- metis_tac [num_tvs_def, type_e_freevars, bind_tenv_def, bind_tvar_def,
               tenv_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]
 >- metis_tac [type_funs_Tfn, num_tvs_bind_var_list]
 >- (imp_res_tac type_funs_Tfn >>
     rw [] >>
     fs [Tfn_def] >>
     rw [] >>
     metis_tac [type_funs_Tfn, num_tvs_bind_var_list, num_tvs_def,
                arithmeticTheory.ADD, arithmeticTheory.ADD_COMM])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
               arithmeticTheory.GREATER_EQ]);

val weakCT_def = Define `
weakCT cenv_impl cenv_spec ⇔
  ∀cn tn.
    case lookup (cn,tn) cenv_spec of
        NONE => T
      | SOME (tvs_spec,ts_spec) =>
          case lookup (cn,tn) cenv_impl of
            NONE => F
          | SOME (tvs_impl,ts_impl) =>
              tvs_spec = tvs_impl ∧
              ts_spec = ts_impl`;

val weak_tenvCT_lookup = Q.prove (
`∀cn tenvCT tenvCT' tvs ts tn.
  weakCT tenvCT' tenvCT ∧
  (lookup (cn,tn) tenvCT = SOME (tvs,ts))
  ⇒
  (lookup (cn,tn) tenvCT' = SOME (tvs,ts))`,
rw [weakCT_def] >>
FIRST_X_ASSUM (MP_TAC o Q.SPECL [`cn`, `tn`]) >>
rw [] >>
cases_on `lookup (cn,tn) tenvCT'` >>
fs [] >>
PairCases_on `x` >>
fs []);

val weakCT_refl = Q.store_thm ("weakCT_refl",
`!tenvCT. weakCT tenvCT tenvCT`,
rw [weakCT_def] >>
every_case_tac);

val disjoint_env_weakCT = Q.store_thm ("disjoint_env_weakCT",
`!tenvC tenvC'.
  disjoint_env tenvC' tenvC ⇒
  weakCT (merge tenvC' tenvC) tenvC`,
rw [weakCT_def] >>
cases_on `lookup (cn,tn) tenvC` >>
rw [] >>
cases_on `lookup (cn,tn) (merge tenvC' tenvC)` >>
rw [] >-
metis_tac [NOT_SOME_NONE, lookup_disjoint, disjoint_env_def, DISJOINT_SYM] >>
PairCases_on `x` >>
fs [lookup_append, merge_def] >>
PairCases_on `x'` >>
rw [] >>
cases_on `lookup (cn,tn) tenvC'` >>
fs [] >>
rw [] >>
fs [disjoint_env_def, DISJOINT_DEF] >>
imp_res_tac lookup_in2 >>
fs [EXTENSION] >>
metis_tac []);

val consistent_con_env_weakening = Q.prove (
`!tenvCT (tenvC:tenvC) (envC:envC) tenvCT'.
  consistent_con_env tenvCT envC tenvC ∧
  tenvCT_ok tenvCT' ∧
  weakCT tenvCT' tenvCT
  ⇒
  consistent_con_env tenvCT' envC tenvC`,
 rw [consistent_con_env_def] >>
 fs [weakCT_def] >>
 FIRST_X_ASSUM (assume_tac o Q.SPECL [`cn`,`t`]) >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 imp_res_tac lookup_notin >>
 fs [] >>
 metis_tac []);

val type_v_weakening = Q.store_thm ("type_v_weakening",
`(!tvs tenvCT tenvS v t. type_v tvs tenvCT tenvS v t ⇒
    !tvs' tenvCT' tenvS'. 
      tenvCT_ok tenvCT' ∧
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ⇒
      type_v tvs' tenvCT' tenvS' v t) ∧
 (!tvs tenvCT tenvS vs ts. type_vs tvs tenvCT tenvS vs ts ⇒
    !tvs' tenvCT' tenvS'. 
      tenvCT_ok tenvCT' ∧
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ⇒
      type_vs tvs' tenvCT' tenvS' vs ts) ∧
 (!tenvCT tenvS env tenv. type_env tenvCT tenvS env tenv ⇒
    !tenvCT' tenvS'. 
      tenvCT_ok tenvCT' ∧
      weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ⇒
      type_env tenvCT' tenvS' env tenv) ∧
 (!tenvS tenvCT envM tenvM. consistent_mod_env tenvS tenvCT envM tenvM ⇒
    !tenvCT' tenvS'. 
      tenvCT_ok tenvCT' ∧
      weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ⇒
      consistent_mod_env tenvS' tenvCT' envM tenvM)`,
 ho_match_mp_tac type_v_strongind >>
 rw [] >>
 rw [Once type_v_cases]
 >- (fs [EVERY_MEM] >>
     metis_tac [weak_tenvCT_lookup, check_freevars_add, gt_0])
 >- (fs [EVERY_MEM] >>
     metis_tac [weak_tenvCT_lookup, check_freevars_add, gt_0])
 >- (fs [Tfn_def] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >-
     metis_tac [check_freevars_add, gt_0] >>
     match_mp_tac (hd (CONJUNCTS type_e_weakening)) >>
     metis_tac [weak_tenvE_refl, weakM_refl, weakC_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [Tfn_def] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >>
     match_mp_tac (hd (CONJUNCTS type_e_weakening)) >>
     metis_tac [weak_tenvE_refl, weakC_refl,weakM_refl,
                weak_tenvE_bind, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [Tfn_def] >>
     qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `tenv'` >>
     rw [] >-
     metis_tac [consistent_con_env_weakening] >>
     match_mp_tac (hd (tl (tl (CONJUNCTS type_e_weakening)))) >>
     metis_tac [weak_tenvE_refl,weakM_refl, weakC_refl,
                weak_tenvE_bind_var_list, weak_tenvE_bind_tvar2, type_v_freevars])
 >- (fs [Tfn_def] >>
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
 >- rw [bind_def, emp_def, bind_tvar_def, bind_tenv_def]);

val type_ctxt_weakening = Q.store_thm ("type_ctxt_weakening",
`∀tvs tenvM tenvCT tenvS tenv c t1 t2 tenvM' tenvCT' tenvS' tenv' tenvC tenvC'.
    type_ctxt tvs tenvM tenvCT tenvC tenvS tenv c t1 t2 ∧
    tenvCT_ok tenvCT' ∧ tenvM_ok tenvM' ∧ tenv_ok tenv ∧ (num_tvs tenv = 0) ∧ 
    weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ∧ weak_tenvE tenv' tenv ⇒
    type_ctxt tvs tenvM' tenvCT' tenvC' tenvS' tenv' c t1 t2`,
 rw [type_ctxt_cases]
 >- (fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ 0``])
 >- metis_tac [type_e_weakening, weak_tenvE_refl]
 >- metis_tac [type_v_weakening]
 >- metis_tac [type_e_weakening]
 >- metis_tac [type_e_weakening]
 >- (fs [RES_FORALL] >>
     rw [] 
     >- (PairCases_on `x` >>
         rw [] >>
         res_tac >>
         fs [] >>
         metis_tac [type_e_weakening, weak_tenvE_bind_var_list, type_p_weakening, DECIDE ``!x:num. x ≥ x``]) >>
     fs [Once type_v_cases, Texn_def, Tfn_def, Tref_def] >>
     imp_res_tac type_funs_Tfn >>
     fs [Tfn_def, tid_exn_to_tc_11] >>
     cases_on `tn` >>
     fs [tid_exn_to_tc_def] >>
     cases_on `tvs'` >>
     fs [] >>
     metis_tac [ZIP, LENGTH, weak_tenvCT_lookup, type_v_weakening])
 >- metis_tac [check_freevars_add, gt_0, type_e_weakening, weak_tenvE_bind]
 >- (fs [tid_exn_to_tc_11] >>
     qexists_tac `ts1` >>
     qexists_tac `ts2` >>
     qexists_tac `t` >>
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
`∀tvs tenvCT tenvS cs t1 t2. type_ctxts tvs tenvCT tenvS cs t1 t2 ⇒
  !tenvCT' tenvS'.
    tenvCT_ok tenvCT' ∧ weakCT tenvCT' tenvCT ∧ weakS tenvS' tenvS ⇒
    type_ctxts tvs tenvCT' tenvS' cs t1 t2`,
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
`!tenvCT tenvS st tenvCT'. 
  tenvCT_ok tenvCT' ∧
  type_s tenvCT tenvS st ∧
  weakCT tenvCT' tenvCT
  ⇒
  type_s tenvCT' tenvS st`,
rw [type_s_def] >>
metis_tac [type_v_weakening, weakS_refl]);

val weakC_only_other_mods_def = Define `
weakC_only_other_mods mn tenvC' tenvC =
  !cn id tvs ts tn.
    ((id = Short cn) ∨ (?x. (mn = SOME x) ∧ tn = TypeId (Long x cn)))
    ⇒
    (MEM (id, tvs, ts, tn) tenvC' ⇒ MEM (id, tvs, ts, tn) tenvC)`;

val weakC_only_other_mods_merge = Q.prove (
`!mn tenvC1 tenvC2 tenvC3.
  weakC_only_other_mods mn tenvC2 tenvC3
  ⇒
  weakC_only_other_mods mn (merge tenvC1 tenvC2) (merge tenvC1 tenvC3)`,
rw [weakC_only_other_mods_def, merge_def, lookup_append] >>
rw []);

(*
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


*)

val check_ctor_tenv_weakening = Q.store_thm ("check_ctor_tenv_weakening",
`!mn tenvC tdecs tenvC'.
  tenvC_ok tenvC' ∧
  check_ctor_tenv mn tenvC tdecs ∧
  weakC_only_other_mods mn tenvC' tenvC ∧
  weakC tenvC' tenvC
  ⇒
  check_ctor_tenv mn tenvC' tdecs`,
 rw [check_ctor_tenv_def, tenvC_ok_def] >>
 fs [EVERY_MEM] >>
 rw [] >>
 res_tac >>
 PairCases_on `e` >>
 fs [] >>
 rw [] >>
 PairCases_on `p` >>
 rw [] >>
 fs [weakC_only_other_mods_def] >>
 cases_on `?cn. p0 = Short cn` >>
 fs [] >>
 rw []
 >- (res_tac >>
     fs [] >>
     rw [] >>
     `MEM (Short cn, p1, p2, p3) tenvC` by metis_tac [] >>
     res_tac >>
     fs [])
 >- (res_tac >>
     fs [] >>
     cases_on `p0` >>
     fs [] >>
     cases_on `p3` >>
     fs [same_module_def] >>
     cases_on `i` >>
     fs [same_module_def] >>
     cases_on `mn` >>
     fs [mk_id_def] >>
     rw [] >>
     CCONTR_TAC  >>
     fs [] >>
     `MEM (Long s a,p1,p2,TypeId (Long s a')) tenvC` by metis_tac [] >>
     res_tac >>
     fs []));

val type_d_weakening = Q.store_thm ("type_d_weakening",
`!mn tenvM tenvC tenv d tenvC' tenv' tenvM'' tenvC''.
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  weakM tenvM'' tenvM ∧ weakC tenvC'' tenvC ∧
  tenvC_ok tenvC'' ∧
  weakC_only_other_mods mn tenvC'' tenvC
  ⇒
  type_d mn tenvM'' tenvC'' tenv d tenvC' tenv'`,
 rw [type_d_cases]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- metis_tac [type_p_weakening, type_e_weakening, weak_tenvE_refl, DECIDE ``!x:num. x ≥ x``]
 >- metis_tac [check_ctor_tenv_weakening]
 >- (fs [weakC_def] >>
     FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `Short cn`) >>
     every_case_tac >>
     fs [weakC_only_other_mods_def] >>
     imp_res_tac lookup_notin >>
     fs [MEM_MAP] >>
     pop_assum (ASSUME_TAC o Q.SPEC `(Short cn, q, q', r')`) >>
     fs [] >>
     `(Short cn, q, q', r') ∉ set tenvC''` by metis_tac [] >>
     induct_on `tenvC''` >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     every_case_tac >>
     fs [tenvC_ok_def] >>
     metis_tac []));

     (*
val type_ds_weakening = Q.store_thm ("type_ds_weakening",
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !tenvM'' tenvC''. 
  weakC_only_other_mods mn tenvC'' tenvC ∧ tenvC_ok tenvC'' ∧ weakM tenvM'' tenvM ∧
  weakC tenvC'' tenvC ∧ tenvC_ok tenvC
  ⇒
  type_ds mn tenvM'' tenvC'' tenv ds tenvC' tenv'`,
 ho_match_mp_tac type_ds_ind >>
 rw [] >>
 rw [Once type_ds_cases] >>
 `weakC_only_other_mods mn (merge cenv' tenvC'') (merge cenv' tenvC)`
          by metis_tac [weakC_only_other_mods_merge] >>
 `tenvC_ok (merge cenv' tenvC'') ∧ tenvC_ok (merge cenv' tenvC)` 
        by (`type_d mn tenvM'' tenvC'' tenv d cenv' tenv'` by metis_tac [type_d_weakening] >>
            imp_res_tac type_d_tenvCT_ok >>
            rw [tenvC_ok_merge] >>
            fs [tenvCT_ok_def, tenvC_ok_def, EVERY_MEM] >>
            rw [] >>
            PairCases_on `e` >>
            res_tac >>
            fs []
            metis_tac []) >>
 metis_tac [type_d_weakening, weakC_merge]);
 
val weakC_not_NONE = Q.store_thm ("weakC_not_NONE",
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

val weakC_not_SOME = Q.store_thm ("weakC_not_SOME",
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

val type_d_mod = Q.store_thm ("type_d_mod",
`∀mn tenvM tenvC tenv d tenvC' tenv'.
  type_d mn tenvM tenvC tenv d tenvC' tenv'
  ⇒
  tenvC_one_mod tenvC' mn`,
rw [type_d_cases, emp_def] >|
[rw [tenvC_one_mod_def],
 rw [tenvC_one_mod_def],
 rw [tenvC_one_mod_def],
 metis_tac [build_ctor_tenv_one_mod],
 rw [tenvC_one_mod_def] >>
     fs [bind_def, mk_id_def] >>
     every_case_tac >>
     fs [bind_def, mk_id_def]]);

val type_ds_mod = Q.store_thm ("type_ds_mod",
`∀mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv'
  ⇒
  tenvC_one_mod tenvC' mn`,
ho_match_mp_tac type_ds_ind >>
rw [emp_def] >-
rw [tenvC_one_mod_def] >>
metis_tac [tenvC_one_mod_merge, type_d_mod]);

val weakC_disjoint = Q.store_thm ("weakC_disjoint",
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

*)

val _ = export_theory ();
