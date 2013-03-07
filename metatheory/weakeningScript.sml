open preamble;
open rich_listTheory;
open MiniMLTheory MiniMLTerminationTheory typeSystemTheory;

val _ = new_theory "weakening";

val weak_tenvE_def = Define `
weak_tenvE tenv tenv' = 
  num_tvs tenv ≥ num_tvs tenv' ∧
  ∀n inc tvs t. 
    (lookup_tenv n inc tenv' = SOME (tvs,t)) ⇒
    (lookup_tenv n inc tenv = SOME (tvs,t))`;

val weakM_def = Define `
weakM tenvM tenvM' =
  EVERY (\(mn',tenv'). 
            case lookup mn' tenvM of
              | NONE => F
              | SOME tenv => weakE tenv tenv')
        tenvM'`;

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

val weak_tenvE_bind_var_list = Q.prove (
`!tenv'' tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_var_list 0 tenv'' tenv') (bind_var_list 0 tenv'' tenv)`,
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
ho_match_mp_tac lookup_ind >>
rw [weakC_def, lookup_def] >>
fs [] >>
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
    (LENGTH subst = tvs') ∧
    EVERY (check_freevars tvs []) subst ∧
    (deBruijn_subst 0 subst t' = t)`,
ho_match_mp_tac lookup_ind >>
rw [weakE_def] >>
fs [] >>
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
`!n tenvM tenvM' tenv tenv' tvs t.
  weakM tenvM' tenvM ∧
  weak_tenvE tenv' tenv ∧
  check_freevars tvs [] t ∧
  (t_lookup_var_id n tenvM tenv = SOME (tvs,t))
  ⇒
  ?tvs' t' subst.
    (t_lookup_var_id n tenvM' tenv' = SOME (tvs',t')) ∧
    (LENGTH subst = tvs') ∧
    EVERY (check_freevars tvs []) subst ∧
    (deBruijn_subst 0 subst t' = t)`,
rw [t_lookup_var_id_def] >>
cases_on `n` >>
fs [weak_tenvE_def] >|
[qexists_tac `t` >>
     qexists_tac `MAP Tvar_db (COUNT_LIST tvs)` >>
     rw [EVERY_MAP, LENGTH_COUNT_LIST] >>
     metis_tac [weak_tenvM_lookup_lem, deBruijn_subst_id],
 induct_on `tenvM` >>
     fs [weakM_def] >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0 = s` >>
     fs [] >>
     rw [] >>
     cases_on `lookup h0 tenvM'` >>
     fs [] >>
     metis_tac [weakE_lookup]]);

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
      tenvM_ok tenvM ∧ tenv_ok tenv ∧ 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_e tenvM' tenvC' tenv' e t) ∧
 (!tenvM tenvC tenv es ts. type_es tenvM tenvC tenv es ts ⇒
    ∀tenvM' tenvC' tenv'. 
      tenvM_ok tenvM ∧ tenv_ok tenv ∧ 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_es tenvM' tenvC' tenv' es ts) ∧
 (!tenvM tenvC tenv funs tenv''. type_funs tenvM tenvC tenv funs tenv'' ⇒
    ∀tenvM' tenvC' tenv'. 
      tenvM_ok tenvM ∧ tenv_ok tenv ∧ 
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      weakM tenvM' tenvM ∧ weakC tenvC' tenvC ∧ weak_tenvE tenv' tenv ⇒
      type_funs tenvM' tenvC' tenv' funs tenv'')`,

ho_match_mp_tac type_e_ind >>
rw [] >>
rw [Once type_e_cases] >|

[metis_tac [weak_tenvE_freevars],
 `tenv_ok (bind_tenv var 0 Tint tenv)` 
          by rw [tenv_ok_def, bind_tenv_def, check_freevars_def, Tint_def] >>
     metis_tac [weak_tenvE_bind], 
 fs [EVERY_MEM] >>
     metis_tac [weak_tenvC_lookup, weak_tenvE_freevars],
 metis_tac [weak_tenvM_lookup, type_e_freevars_t_lookup_var_id]
 
 cheat,
 metis_tac [weak_tenvE_bind, weak_tenvE_freevars],
 metis_tac [],
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
 metis_tac [weak_tenvE_bind_var_list, weak_tenvE_bind_tvar]


val _ = export_theory ();
