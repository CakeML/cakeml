(* Theorems about type_e, type_es, and type_funs *)
open preamble MiniMLTheory MiniMLTerminationTheory;

val _ = new_theory "typeSystem";

val mem_lem = Q.prove (
`!x y l. MEM (x,y) l ⇒ ∃z. (x = FST z) ∧ z ∈ set l`,
induct_on `l` >>
rw [] >>
metis_tac [FST]);

val lookup_zip_map = Q.prove (
`!x env keys vals res f res'.
  (LENGTH keys = LENGTH vals) ∧ (env = ZIP (keys,vals)) ∧ (lookup x env = res) ⇒
  (lookup x (ZIP (keys,MAP f vals)) = OPTION_MAP f res)`,
recInduct lookup_ind >>
rw [lookup_def] >>
cases_on `keys` >>
cases_on `vals` >>
fs []);

val option_map_eqns = Q.prove (
`(!f. option_map f NONE = NONE) ∧
 (!f x. option_map f (SOME x) = SOME (f x))`,
rw [option_map_def]);

(* TODO: Move these four definitions to miniML.lem? *)
(* Check that the dynamic and static constructor environments are consistent *)
val consistent_con_env_def = Define `
  (consistent_con_env [] [] = T) ∧
  (consistent_con_env ((cn, (n, ns))::envC) ((cn', (tvs, ts, tn))::tenvC) =
    (cn = cn') ∧
    (LENGTH ts = n) ∧
    cn IN ns ∧
    consistent_con_env envC tenvC) ∧
  (consistent_con_env _ _ = F)`;

(* Check that two constructors of the same type have the same set of all
 * constructors for that type *)
val consistent_con_env2_def = Define `
  consistent_con_env2 envC tenvC =
    (∀n1 n2 tvs1 tvs2 ts1 ts2 tn ns1 ns2 l1 l2.
       (lookup n1 tenvC = SOME (tvs1,ts1,tn)) ∧
       (lookup n2 tenvC = SOME (tvs2,ts2,tn)) ∧
       (lookup n1 envC = SOME (l1,ns1)) ∧
       (lookup n2 envC = SOME (l2,ns2))
       ⇒
       (ns1 = ns2))`;

val tenv_ok_def = Define `
(tenv_ok Empty = T) ∧
(tenv_ok (Bind_tvar n tenv) = tenv_ok tenv) ∧
(tenv_ok (Bind_name x tvs t tenv) = 
  check_freevars (tvs + num_tvs tenv) [] t ∧ tenv_ok tenv)`;

val tenvC_ok_def = Define `
tenvC_ok tenvC = EVERY (\(cn,tvs,ts,tn). EVERY (check_freevars 0 tvs) ts) tenvC`;

val get_first_tenv_def = Define `
  (get_first_tenv ds NONE =
     case ds of
        (Dtype tds::ds) => tds
      | _ => []) ∧
  (get_first_tenv _ _ = [])`;

val disjoint_env_def = Define `
  disjoint_env e1 e2 =
    DISJOINT (set (MAP FST e1)) (set (MAP FST e2))`;

val tenvC_ok_lookup = Q.store_thm ("tenvC_ok_lookup",
`!tenvC cn tvs ts tn.
  tenvC_ok tenvC ∧ (lookup cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
induct_on `tenvC` >>
rw [] >>
PairCases_on `h` >>
fs [tenvC_ok_def] >>
every_case_tac >>
rw [] >>
fs [] >>
metis_tac []);

(* Constructors in their type environment are also in their execution
 * environment *)
val consistent_con_env_thm = Q.store_thm ("consistent_con_env_thm",
`∀envC tenvC.
  consistent_con_env envC tenvC 
  ⇒
  ((lookup cn tenvC = SOME (tvs, ts, tn)) ⇒ 
     (∃ns. (lookup cn envC = SOME (LENGTH ts, ns)) ∧ cn IN ns))
  ∧
  ((lookup cn tenvC = NONE) ⇒ (lookup cn envC = NONE))`,
recInduct (fetch "-" "consistent_con_env_ind") >>
rw [lookup_def, consistent_con_env_def] >>
rw []);

val type_es_length = Q.store_thm ("type_es_length",
`∀tenvC tenv es ts.
  type_es tenvC tenv es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
rw [Once type_e_cases] >>
rw [] >>
metis_tac []);

val type_ps_length = Q.store_thm ("type_ps_length",
`∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)`,
induct_on `ps` >>
rw [Once type_p_cases] >>
rw [] >>
metis_tac []);

val lookup_in = Q.store_thm ("lookup_in",
`!x e v. (lookup x e = SOME v) ⇒ MEM v (MAP SND e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val lookup_in2 = Q.store_thm ("lookup_in2",
`!x e v. (lookup x e = SOME v) ⇒ MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val lookup_disjoint = Q.store_thm ("lookup_disjoint",
`!x v e e'. (lookup x e = SOME v) ∧ disjoint_env e e' ⇒
  (lookup x (merge e' e) = SOME v)`,
induct_on `e'` >>
rw [disjoint_env_def, merge_def, lookup_def] >>
cases_on `h` >>
fs [merge_def, lookup_def] >>
fs [Once DISJOINT_SYM, DISJOINT_INSERT] >>
`q ≠ x` by metis_tac [lookup_in2] >>
fs [disjoint_env_def] >>
metis_tac [DISJOINT_SYM]);


val lookup_notin = Q.store_thm ("lookup_notin",
`!x e. (lookup x e = NONE) = ~MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val bind_var_list_append = Q.store_thm ("bind_var_list_append",
`!n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3)`,
induct_on `te1` >>
rw [bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def]);

val check_freevars_subst_single = Q.store_thm ("check_freevars_subst_single",
`!dbmax tvs t tvs' ts.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars dbmax tvs t ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  check_freevars dbmax tvs' (type_subst (ZIP (tvs,ts)) t)`,
recInduct check_freevars_ind >>
rw [check_freevars_def, type_subst_def, EVERY_MAP] >|
[every_case_tac >>
     fs [check_freevars_def, lookup_notin] >|
     [imp_res_tac MAP_ZIP >>
          fs [],
      imp_res_tac lookup_in >>
          imp_res_tac MAP_ZIP >>
          fs [EVERY_MEM]],
 fs [EVERY_MEM]]);

val type_uop_cases = Q.store_thm ("type_uop_cases",
`∀uop t1 t2.
  type_uop uop t1 t2 =
  ((uop = Opref) ∧ (t2 = Tref t1)) ∨
  ((uop = Opderef) ∧ (t1 = Tref t2))`,
rw [type_uop_def, Tint_def, Tbool_def, Tunit_def, Tref_def] >>
cases_on `uop` >>
rw [] >>
cases_on `t1` >>
rw [] >>
cases_on `l` >>
rw [] >>
cases_on `t'` >>
rw [] >>
cases_on `t` >>
rw [] >>
metis_tac []);

val type_op_cases = Q.store_thm ("type_op_cases",
`!op t1 t2 t3.
  type_op op t1 t2 t3 =
  ((∃op'. op = Opn op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tint)) ∨
  ((∃op'. op = Opb op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tbool)) ∨
  ((op = Opapp) ∧ (t1 = Tfn t2 t3)) ∨
  ((op = Equality) ∧ (t1 = t2) ∧ (t3 = Tbool)) ∨
  ((op = Opassign) ∧ (t1 = Tref t2) ∧ (t3 = Tunit))`,
rw [type_op_def, Tfn_def, Tint_def, Tbool_def, Tunit_def, Tref_def] >>
cases_on `op` >>
rw [] >>
cases_on `t1` >>
rw [] >>
cases_on `l` >>
rw [] >|
[cases_on `t` >>
     rw [] >>
     cases_on `t2` >>
     rw [] >>
     every_case_tac,
 cases_on `t` >>
     rw [] >>
     cases_on `t2` >>
     rw [] >>
     every_case_tac,
 cases_on `t'` >>
     rw [] >>
     cases_on `t''` >>
     rw [] >>
     cases_on `t` >>
     rw [] >>
     metis_tac [],
 cases_on `t'` >>
     rw [] >>
     cases_on `t` >>
     rw []]);

val check_freevars_subst_list = Q.store_thm ("check_freevars_subst_list",
`!dbmax tvs tvs' ts ts'.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars dbmax tvs) ts' ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  EVERY (check_freevars dbmax tvs') (MAP (type_subst (ZIP (tvs,ts))) ts')`,
induct_on `ts'` >>
rw [] >>
metis_tac [check_freevars_subst_single]);

val deBruijn_subst_check_freevars = Q.store_thm ("deBruijn_subst_check_freevars",
`!tvs tvs' t ts n.
  check_freevars tvs tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
fs [EVERY_MEM] >>
fs [MEM_EL] >-
metis_tac [] >>
decide_tac);

val check_freevars_add = Q.store_thm ("check_freevars_add",
`(!tvs tvs' t. check_freevars tvs tvs' t ⇒ 
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def] >-
metis_tac [MEM_EL, EVERY_MEM] >>
decide_tac);

val check_freevars_subst_inc = Q.store_thm ("check_freevars_subst_inc",
`∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  (tvs = LENGTH targs + tvs') ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2
     (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t))`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_inc_def, deBruijn_subst_def, EVERY_MAP] >>
fs [EVERY_MEM] >>
cases_on `n < LENGTH targs` >>
rw [deBruijn_subst_def, check_freevars_def] >>
fs [MEM_EL] >-
metis_tac [] >-
metis_tac [] >>
decide_tac);

val type_e_freevars_lem2 = Q.prove (
`!tenvE targs n t inc.
  EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
  (lookup_tenv n inc tenvE = SOME (LENGTH targs,t)) ∧
  tenv_ok tenvE
  ⇒ 
  check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)`,
induct_on `tenvE` >>
rw [check_freevars_def, num_tvs_def, lookup_tenv_def, tenv_ok_def] >>
metis_tac [deBruijn_subst_check_freevars, arithmeticTheory.ADD_ASSOC,
           check_freevars_subst_inc]);

val num_tvs_bind_var_list = Q.store_thm ("num_tvs_bind_var_list",
`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE`,
induct_on `env` >>
rw [num_tvs_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def, bind_tenv_def, num_tvs_def]);

val tenv_ok_bind_var_list = Q.store_thm ("tenv_ok_bind_var_list",
`!funs tenvC env tenvE tvs env'.
  type_funs tenvC (bind_var_list 0 env' tenvE) funs env ∧
  tenv_ok tenvE
  ⇒
  tenv_ok (bind_var_list 0 env tenvE)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [check_freevars_def, bind_tenv_def, bind_var_list_def, tenv_ok_def] >>
fs [check_freevars_def, num_tvs_bind_var_list] >>
metis_tac []);

val type_freevars_lem4 = Q.prove (
`!funs tenvC env tenvE tvs env'.
  type_funs tenvC (bind_var_list 0 env' (bind_tvar tvs tenvE)) funs env ∧
  tenv_ok tenvE
  ⇒
  tenv_ok (bind_var_list tvs env tenvE)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [check_freevars_def, bind_tenv_def, bind_var_list_def, tenv_ok_def] >>
cases_on `tvs = 0` >>
fs [check_freevars_def, num_tvs_bind_var_list, bind_tvar_def, num_tvs_def] >>
metis_tac []);

val type_freevars_lem5 = Q.prove (
`!tenvE env.
  tenv_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_ok (bind_var_list 0 env tenvE)`,
induct_on `env` >>
rw [tenv_ok_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_tenv_def, tenv_ok_def, bind_var_list_def] >>
fs [num_tvs_bind_var_list]);

val type_p_freevars = Q.store_thm ("type_p_freevars",
`(!tvs tenvC p t env'. 
   type_p tvs tenvC p t env' ⇒ 
   check_freevars tvs [] t ∧
   EVERY (check_freevars tvs []) (MAP SND env')) ∧
 (!tvs tenvC ps ts env'. 
   type_ps tvs tenvC ps ts env' ⇒ 
   EVERY (check_freevars tvs []) ts ∧
   EVERY (check_freevars tvs []) (MAP SND env'))`,
ho_match_mp_tac type_p_ind >>
rw [check_freevars_def, bind_tenv_def, Tbool_def, Tint_def, Tunit_def, Tref_def,
    tenv_ok_def, bind_tvar_def, bind_var_list_def] >>
metis_tac []);

val type_e_freevars = Q.store_thm ("type_e_freevars",
`(!tenvC tenvE e t. 
   type_e tenvC tenvE e t ⇒ 
   tenv_ok tenvE ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenvC tenvE es ts. 
   type_es tenvC tenvE es ts ⇒
   tenv_ok tenvE ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenvC tenvE funs env. 
   type_funs tenvC tenvE funs env ⇒
   tenv_ok tenvE ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env))`,
ho_match_mp_tac type_e_strongind >>
rw [check_freevars_def, bind_tenv_def, num_tvs_def, type_uop_cases, type_op_cases,
    tenv_ok_def, bind_tvar_def, bind_var_list_def, Tbool_def, Tint_def, Tfn_def,
    Tunit_def, Tref_def] >>
fs [check_freevars_def] >|
[metis_tac [deBruijn_subst_check_freevars],
 metis_tac [type_e_freevars_lem2, arithmeticTheory.ADD],
 cases_on `pes` >>
     fs [RES_FORALL, num_tvs_bind_var_list] >>
     qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `(FST h, SND h)`) >>
     fs [] >>
     metis_tac [type_p_freevars, type_freevars_lem5],
 metis_tac [tenv_ok_bind_var_list, num_tvs_bind_var_list],
 metis_tac [type_freevars_lem4, num_tvs_bind_var_list, bind_tvar_def]]);

(* Recursive functions have function type *)
val type_funs_Tfn = Q.store_thm ("type_funs_Tfn",
`∀tenvC tenv funs tenv' tvs t n.
  type_funs tenvC tenv funs tenv' ∧
  (lookup n tenv' = SOME t)
  ⇒
  ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenv) [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs tenvC tenv funspat tenv'`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
rw [] >>
fs [lookup_def, emp_def, bind_def] >>
cases_on `fn = n` >>
fs [deBruijn_subst_def, check_freevars_def] >>
metis_tac [type_e_freevars, bind_tenv_def, num_tvs_def]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.store_thm ("type_funs_lookup",
`∀fn env tenvC funs env' n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenvC tenv funs env'
  ⇒
  (∃t. lookup fn env' = SOME t)`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [lookup_def, bind_def] >>
rw [] >>
metis_tac []);

(* Functions in the type environment can be found *)
val type_funs_find_recfun = Q.store_thm ("type_funs_find_recfun",
`∀fn env tenvC funs tenv' e tenv t.
  (lookup fn tenv' = SOME t) ∧
  type_funs tenvC tenv funs tenv'
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [lookup_def, bind_def, emp_def] >>
rw [Once find_recfun_def] >>
metis_tac []);

val type_recfun_lookup = Q.store_thm ("type_recfun_lookup",
`∀fn funs n e tenvC tenv tenv' tvs t1 t2 topt.
  (find_recfun fn funs = SOME (n,topt,e)) ∧
  type_funs tenvC tenv funs tenv' ∧
  (lookup fn tenv' = SOME (Tfn t1 t2))
  ⇒
  type_e tenvC (bind_tenv n 0 t1 tenv) e t2 ∧
  (?t3. topt = SOME t1) ∧
  check_freevars (num_tvs tenv) [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [Once find_recfun_def] >>
qpat_assum `type_funs tenvC tenv (h::funs) tenv'`
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
rw [] >>
fs [] >>
cases_on `fn' = fn` >>
fs [Tfn_def, lookup_def, bind_def, deBruijn_subst_def] >>
rw [check_freevars_def] >>
metis_tac [bind_tenv_def, num_tvs_def, type_e_freevars, type_funs_Tfn,
           EVERY_DEF, Tfn_def, check_freevars_def]);

(* No duplicate function definitions in a single let rec *)
val type_funs_distinct = Q.store_thm ("type_funs_distinct",
`∀tenvC tenv funs tenv'.
  type_funs tenvC tenv funs tenv'
  ⇒
  ALL_DISTINCT (MAP (λ(x,a,y,b,z). x) funs)`,
induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [MEM_MAP] >|
[PairCases_on `y` >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     metis_tac [type_funs_lookup, optionTheory.NOT_SOME_NONE],
 metis_tac []]);

val build_rec_env_help_lem = Q.prove (
`∀funs env funs' tvs.
FOLDR (λ(f,topt1,x,topt2,e) env'. bind f (Recclosure env funs' f, add_tvs tvs topt1) env') env funs =
merge (MAP (λ(fn,n,e). (fn, (Recclosure env funs' fn, add_tvs tvs n))) funs) env`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
`∀funs funs' env tvs.
  build_rec_env tvs funs env =
  merge (MAP (λ(fn,n,e). (fn, (Recclosure env funs fn, add_tvs tvs n))) funs) env`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val deBruijn_subst_tenvE_def = Define `
(deBruijn_subst_tenvE targs Empty = Empty) ∧
(deBruijn_subst_tenvE targs (Bind_tvar tvs env) = 
  Bind_tvar tvs (deBruijn_subst_tenvE targs env)) ∧
(deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
  Bind_name x tvs (deBruijn_subst (tvs + num_tvs env) 
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs)
                                  t)
       (deBruijn_subst_tenvE targs env))`;

val db_merge_def = Define `
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))`;

val num_tvs_db_merge = Q.prove (
`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
induct_on `e1` >>
rw [num_tvs_def, db_merge_def] >>
decide_tac);

val num_tvs_deBruijn_subst_tenvE = Q.prove (
`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE`,
induct_on `tenvE` >>
rw [deBruijn_subst_tenvE_def, num_tvs_def]);

val bind_tvar_rewrites = Q.store_thm ("bind_tvar_rewrites",
`(!tvs e1 e2. 
   db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
 (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
 (!n inc tvs e. lookup_tenv n inc (bind_tvar tvs e) = lookup_tenv n (inc+tvs) e) ∧
 (!tvs e. tenv_ok (bind_tvar tvs e) = tenv_ok e) ∧
 (!targs tvs e.
   deBruijn_subst_tenvE targs (bind_tvar tvs e) =
   bind_tvar tvs (deBruijn_subst_tenvE targs e))`,
rw [bind_tvar_def, deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def,
    lookup_tenv_def, tenv_ok_def]);

val lookup_tenv_db_merge = Q.prove (
`!n inc e1 e2.
  lookup_tenv n inc (db_merge e1 e2) =
  case lookup_tenv n inc e1 of
    | SOME t => SOME t
    | NONE =>
        lookup_tenv n (inc + num_tvs e1) e2`,
induct_on `e1` >>
rw [lookup_tenv_def, db_merge_def, num_tvs_def] >>
every_case_tac >>
srw_tac [ARITH_ss] []);

val tenv_ok_db_merge = Q.prove (
`!e1 e2. tenv_ok (db_merge e1 e2) ⇒ tenv_ok e2`,
induct_on `e1` >>
rw [tenv_ok_def, db_merge_def]);

val check_freevars_deBruijn_inc = Q.prove (
`!tvs tvs' t. check_freevars tvs tvs' t ⇒ 
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM] >>
rw [check_freevars_def] >>
decide_tac);

val check_freevars_lem = Q.prove (
`!l tvs' t.
  check_freevars l tvs' t ⇒
  !targs n1 tvs.
    (l = n1 + (LENGTH targs)) ∧
    EVERY (check_freevars tvs tvs') targs
     ⇒
     check_freevars (n1 + tvs) tvs'
       (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t)`,
ho_match_mp_tac check_freevars_ind >>
rw [deBruijn_inc_def, deBruijn_subst_def, check_freevars_def] >|
[fs [EVERY_MAP, EVERY_MEM] >>
     metis_tac [],
 rw [check_freevars_def] >|
     [fs [EVERY_MEM, MEM_EL] >>
          `n - n1 < LENGTH targs` by decide_tac >>
          rw [EL_MAP] >>
          metis_tac [check_freevars_deBruijn_inc, MEM_EL, 
                     arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC],
      decide_tac,
      decide_tac,
      decide_tac]]);

val type_subst_deBruijn_subst_single = Q.prove (
`!s t tvs tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars 0 tvs t ∧
  (s = (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (ZIP (tvs,ts)) t) =
   type_subst (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)) t)`,
recInduct type_subst_ind >>
rw [deBruijn_subst_def, deBruijn_inc_def, type_subst_def, check_freevars_def] >|
[every_case_tac >>
     fs [deBruijn_subst_def, deBruijn_inc_def] >|
     [imp_res_tac MAP_ZIP >>
          fs [lookup_notin],
      metis_tac [lookup_zip_map, optionTheory.OPTION_MAP_DEF, optionTheory.NOT_SOME_NONE],
      `lookup tv (ZIP (tvs, MAP (λt. deBruijn_subst inc ts' t) ts)) =
       OPTION_MAP (λt. deBruijn_subst inc ts' t) (SOME x)`
                     by metis_tac [lookup_zip_map] >>
          fs []],
 rw [rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     fs [EVERY_MEM] >>
     metis_tac []]);

val type_subst_deBruijn_subst_list = Q.store_thm ("type_subst_deBruijn_subst_list",
`!t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (ZIP (tvs,ts))) ts'') =
   MAP (type_subst (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) ts'')`,
induct_on `ts''` >>
rw [] >>
metis_tac [type_subst_deBruijn_subst_single]);

val type_subst_deBruijn_inc_single = Q.prove (
`!s t ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  (s = (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)) t)`,
recInduct type_subst_ind >>
rw [deBruijn_inc_def, type_subst_def, check_freevars_def] >|
[every_case_tac >>
     rw [deBruijn_inc_def] >|
     [imp_res_tac MAP_ZIP >>
          fs [lookup_notin],
      metis_tac [lookup_zip_map, optionTheory.OPTION_MAP_DEF, optionTheory.NOT_SOME_NONE],
      `lookup tv (ZIP (tvs, MAP (λt. deBruijn_inc sk inc t) ts)) =
       OPTION_MAP (λt. deBruijn_inc sk inc t) (SOME x)`
                     by metis_tac [lookup_zip_map] >>
          fs []],
 rw [rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     fs [EVERY_MEM] >>
     metis_tac []]);

val type_subst_deBruijn_inc_list = Q.store_thm ("type_subst_deBruijn_inc_list",
`!ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (ZIP (tvs,ts))) ts') =
   MAP (type_subst (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) ts')`,
induct_on `ts'` >>
rw [] >>
metis_tac [type_subst_deBruijn_inc_single]);

val lookup_tenv_subst_none = Q.prove (
`!n inc e.
 (lookup_tenv n inc e = NONE) ⇒ 
 (lookup_tenv n inc (deBruijn_subst_tenvE targs e) = NONE)`,
induct_on `e` >>
rw [deBruijn_subst_tenvE_def, lookup_tenv_def]);

val deBruijn_inc_deBruijn_inc = Q.prove (
`!sk i2 t i1. 
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t`,
ho_match_mp_tac deBruijn_inc_ind >>
rw [deBruijn_inc_def] >>
rw [] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
fs []);

(*
val deBruijn_subst_inc_lem = Q.prove (
`(!t ts idx.
   (deBruijn_subst 0 ts (deBruijn_inc (LENGTH ts) idx t) =
    deBruijn_subst idx ts (deBruijn_inc 0 idx t))) ∧
 (!ts' ts idx.
   (MAP (\t. deBruijn_subst 0 ts (deBruijn_inc (LENGTH ts) idx t)) ts' =
    MAP (\t. deBruijn_subst idx ts (deBruijn_inc 0 idx t)) ts'))`,
ho_match_mp_tac t_induction >>
rw [deBruijn_subst_def, deBruijn_inc_def] >>
full_simp_tac (srw_ss() ++ ARITH_ss) [MAP_MAP_o, combinTheory.o_DEF]);
*)

val lookup_tenv_inc_some = Q.prove (
`!n inc e tvs t inc2.
   (lookup_tenv n inc e = SOME (tvs, t)) 
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (lookup_tenv n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t'))`,
induct_on `e` >>
rw [deBruijn_inc_def, lookup_tenv_def] >>
rw [] >>
metis_tac [deBruijn_inc_deBruijn_inc]);

val nil_deBruijn_inc = Q.store_thm ("nil_deBruijn_inc",
`∀skip tvs t. 
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒ 
  (deBruijn_inc skip tvs t = t)`,
ho_match_mp_tac deBruijn_inc_ind >>
rw [deBruijn_inc_def, check_freevars_def] >-
decide_tac >-
(induct_on `ts` >>
     rw [] >>
     metis_tac []) >-
(induct_on `ts` >>
     rw [] >>
     metis_tac []) >>
metis_tac []);

val nil_deBruijn_subst = Q.store_thm ("nil_deBruijn_subst",
`∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)`,
ho_match_mp_tac deBruijn_subst_ind >>
rw [deBruijn_subst_def, check_freevars_def] >>
induct_on `ts'` >>
rw []);

val type_e_subst_lem1 = Q.prove (
`!e n inc t.
  (num_tvs e = 0) ∧
  tenv_ok e ∧
  (lookup_tenv n inc e = SOME (tvs, deBruijn_inc tvs inc t))
  ⇒
  check_freevars tvs [] t`,
induct_on `e` >>
rw [lookup_tenv_def, num_tvs_def, tenv_ok_def] >|
[metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM],
 `check_freevars n [] t0` 
          by metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM] >>
     fs [nil_deBruijn_inc] >>
     rw [] >>
     metis_tac [nil_deBruijn_inc],
 metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]]);

val type_e_subst_lem2 = Q.prove (
`(!t sk targs targs' tvs'.
  check_freevars (LENGTH targs) [] t ⇒
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
 (!ts sk targs targs' tvs'.
  EVERY (check_freevars (LENGTH targs) []) ts ⇒
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts)))`,
ho_match_mp_tac t_induction >>
rw [deBruijn_subst_def, deBruijn_inc_def] >>
fs [EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [deBruijn_subst_def, check_freevars_def] >>
metis_tac []);

val type_e_subst_lem3 = Q.store_thm ("type_e_subst_lem3",
`∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs n.
  (tvs = n + LENGTH targs) ∧
  EVERY (check_freevars tvs' tvs2) targs
  ⇒
  check_freevars (n + tvs') tvs2
     (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_inc_def, deBruijn_subst_def, EVERY_MAP] >>
fs [EVERY_MEM] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [check_freevars_def, EL_MAP, MEM_EL] >>
`n - n' < LENGTH targs` by decide_tac >>
metis_tac [check_freevars_deBruijn_inc]);

val type_e_subst_lem4 = Q.prove (
`!sk i2 t i1. 
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t`,
ho_match_mp_tac deBruijn_inc_ind >>
rw [deBruijn_inc_def] >>
rw [] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
rw []);

val type_e_subst_lem5 = Q.prove (
`(!t n inc n' targs.
   deBruijn_inc n inc 
         (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
   deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs) 
         (deBruijn_inc n inc t)) ∧
 (!ts n inc n' targs.
   MAP (deBruijn_inc n inc)
         (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
   MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
         (MAP (deBruijn_inc n inc) ts))`,
ho_match_mp_tac t_induction >>
rw [deBruijn_subst_def, deBruijn_inc_def] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [EL_MAP] >>
metis_tac [type_e_subst_lem4]);

val type_e_subst_lem6 = Q.prove (
`!e n inc t tvs.
  tenv_ok e ∧
  (lookup_tenv n inc e = SOME (tvs, t))
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t`,
induct_on `e` >>
rw [lookup_tenv_def, num_tvs_def, tenv_ok_def] >|
[metis_tac [arithmeticTheory.ADD_ASSOC],
 imp_res_tac check_freevars_deBruijn_inc >>
     metis_tac [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM],
 metis_tac []]);

val lookup_tenv_deBruijn_subst_tenvE = Q.prove (
`∀n e targs tvs t inc.
  (lookup_tenv n inc e = SOME (tvs,t)) 
  ⇒
  (lookup_tenv n inc (deBruijn_subst_tenvE targs e) = 
     SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t))`,
induct_on `e` >>
rw [lookup_tenv_def,deBruijn_subst_tenvE_def, deBruijn_inc_def, num_tvs_def] >>
metis_tac [arithmeticTheory.ADD_ASSOC, type_e_subst_lem5]);

val subst_inc_cancel = Q.prove (
`(!t ts inc. 
  deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t)
  =
  deBruijn_inc 0 inc t) ∧
 (!ts' ts inc. 
  MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts')
  =
  MAP (deBruijn_inc 0 inc) ts')`,
ho_match_mp_tac t_induction >>
rw [deBruijn_subst_def, deBruijn_inc_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
metis_tac []);

val type_e_subst_lem7 = Q.prove (
`(!t sk targs targs' tvs' tvs''.
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) 
     (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
 (!ts sk targs targs' tvs' tvs''.
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
       (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts))))`,
ho_match_mp_tac t_induction >>
rw [deBruijn_subst_def, deBruijn_inc_def] >>
fs [EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [EL_MAP, deBruijn_subst_def, check_freevars_def] >>
metis_tac [subst_inc_cancel, LENGTH_MAP]);

val type_p_subst = Q.store_thm ("type_p_subst",
`(!n tenvC p t tenv. type_p n tenvC p t tenv ⇒
    !targs' inc tvs targs.
    tenvC_ok tenvC ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenvC 
           (deBruijn_subst_p inc targs' p) 
           (deBruijn_subst inc targs' t)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) tenv)) ∧
 (!n tenvC ps ts tenv. type_ps n tenvC ps ts tenv ⇒
    !targs' inc targs tvs.
    tenvC_ok tenvC ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_ps (inc +  tvs) tenvC 
           (MAP (deBruijn_subst_p inc targs') ps) 
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) tenv))`,
ho_match_mp_tac type_p_strongind >>
rw [] >>
ONCE_REWRITE_TAC [type_p_cases] >>
rw [deBruijn_subst_p_def, deBruijn_subst_def, option_map_eqns, Tint_def,
    Tbool_def, Tunit_def, Tref_def] >|
[metis_tac [check_freevars_lem],
 rw [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [check_freevars_lem, EVERY_MEM],
 metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup],
 metis_tac []]); 

val pat_bindings_subst_p = Q.prove (
`(!p b sk ts. pat_bindings (deBruijn_subst_p sk ts p) b = pat_bindings p b) ∧
 (!ps b sk ts. pats_bindings (MAP (deBruijn_subst_p sk ts) ps) b = pats_bindings ps b)`,
ho_match_mp_tac pat_induction >>
rw [pat_bindings_def, deBruijn_subst_p_def] >>
metis_tac []);

val deBruijn_subst_E_bind_var_list = Q.store_thm ("deBruijn_subst_E_bind_var_list",
`!tenv1 tenv2 tvs. 
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) 
  =
  bind_var_list tvs 
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1) 
          (deBruijn_subst_tenvE targs tenv2)`,
induct_on `tenv1` >>
rw [bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def, deBruijn_subst_tenvE_def, bind_tenv_def, num_tvs_bind_var_list]);

val db_merge_bind_var_list = Q.store_thm ("db_merge_bind_var_list",
`!tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3)`,
induct_on `tenv1` >>
rw [bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def, db_merge_def, bind_tenv_def]);

val is_value_deBruijn_subst = Q.prove (
`!e. is_value e ⇒ is_value (deBruijn_subst_e x y e)`,
ho_match_mp_tac is_value_ind >>
rw [is_value_def, deBruijn_subst_e_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []);

val deBruijn_inc0 = Q.store_thm ("deBruijn_inc0",
`(!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)`,
ho_match_mp_tac t_induction >>
rw [deBruijn_inc_def] >>
metis_tac []);

val type_e_subst = Q.store_thm ("type_e_subst",
`(!tenvC tenvE e t. type_e tenvC tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
      type_e tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) 
                   (deBruijn_subst_e (num_tvs tenvE1) targs' e)
                   (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
 (!tenvC tenvE es ts. type_es tenvC tenvE es ts ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
    type_es tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                  (MAP (deBruijn_subst_e (num_tvs tenvE1) targs') es) 
                  (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
 (!tenvC tenvE funs env. type_funs tenvC tenvE funs env ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
      type_funs tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) 
                      (MAP (\(f,topt1,x,topt2,e').
                              (f, option_map (deBruijn_subst (num_tvs tenvE1) targs') topt1,
                               x, option_map (deBruijn_subst (num_tvs tenvE1) targs') topt2,
                               deBruijn_subst_e (num_tvs tenvE1) targs' e'))
                           funs) 
                      (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env))`,
ho_match_mp_tac type_e_strongind >>
rw [] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [deBruijn_subst_e_def, deBruijn_subst_def, deBruijn_subst_tenvE_def, 
    bind_tvar_rewrites, bind_tenv_def, num_tvs_def, option_map_eqns,
    num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE] >>
fs [deBruijn_subst_e_def, deBruijn_subst_def, deBruijn_subst_tenvE_def, 
    bind_tvar_rewrites, bind_tenv_def, num_tvs_def, option_map_eqns,
    num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_ok_def,
    Tbool_def, Tint_def, Tunit_def, Tref_def, Tfn_def] >>
`tenv_ok tenvE2` by metis_tac [tenv_ok_db_merge, bind_tvar_def, tenv_ok_def] >|
[metis_tac [check_freevars_lem],
 qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs' ⇒
        type_e tenvC
          (db_merge (deBruijn_subst_tenvE targs' tenvE1')
             (bind_tvar tvs' tenvE2))
          (deBruijn_subst_e (num_tvs tenvE1')
             (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e')
          (deBruijn_subst (num_tvs tenvE1')
             (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t)`
        (MP_TAC o Q.SPECL [`Bind_name var 0 Tint tenvE1`,
                           `targs`,
                           `tvs`]) >>
     rw [db_merge_def, Tint_def] >>
     fs [EVERY_MAP, EVERY_MEM, deBruijn_subst_tenvE_def, num_tvs_def,
         check_freevars_def, db_merge_def, deBruijn_subst_def],
 fs [EVERY_MAP, EVERY_MEM] >>
     rw [] >>
     metis_tac [check_freevars_lem, EVERY_MEM],
 metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup],
 imp_res_tac type_e_subst_lem6 >>
     fs [lookup_tenv_db_merge] >>
     cases_on `lookup_tenv n 0 tenvE1` >>
     fs [lookup_tenv_def, bind_tvar_rewrites, num_tvs_deBruijn_subst_tenvE] >>
     rw [] >|
     [imp_res_tac lookup_tenv_subst_none >>
          rw [] >>
          imp_res_tac lookup_tenv_inc_some >>
          rw [] >>
          pop_assum (ASSUME_TAC o Q.SPEC `num_tvs tenvE1 + tvs'`) >>
          fs [] >>
          rw [] >>
          imp_res_tac type_e_subst_lem1 >>
          fs [nil_deBruijn_inc] >-
          metis_tac [type_e_subst_lem2] >>
          fs [EVERY_MAP, EVERY_MEM] >>
          rw [] >>
          metis_tac [type_e_subst_lem3, EVERY_MEM],
      imp_res_tac lookup_tenv_deBruijn_subst_tenvE >>
          pop_assum (ASSUME_TAC o Q.SPEC `targs'`) >>
          fs [] >>
          rw [] >>
          fs [nil_deBruijn_subst, num_tvs_db_merge, bind_tvar_rewrites] >>
          fs [EVERY_MAP, EVERY_MEM] >>
          rw [] >>
          metis_tac [type_e_subst_lem3, EVERY_MEM, type_e_subst_lem7]],
 qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'` 
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     fs [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3],
 fs [type_uop_cases] >>
     rw [deBruijn_subst_def, Tref_def] >>
     fs [deBruijn_subst_def, Tref_def],
 fs [type_op_cases] >>
     rw [] >>
     fs [Tfn_def, Tint_def, Tunit_def, Tbool_def, Tref_def, deBruijn_subst_def] >>
     metis_tac [],
 fs [RES_FORALL] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     rw [] >>
     PairCases_on `x` >>
     fs [MEM_MAP] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     qpat_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(y0,y1)`) >>
     rw [] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      tenv'` >>
     rw [pat_bindings_subst_p] >-
     metis_tac [type_p_subst] >>
     pop_assum (MATCH_MP_TAC o 
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                      db_merge_bind_var_list] o
                Q.SPECL [`bind_var_list 0 tenv' tenvE1`, `targs`, `tvs`]) >>
     rw [] >>
     match_mp_tac type_freevars_lem5 >>
     rw [num_tvs_db_merge, bind_tvar_rewrites] >>
     metis_tac [type_p_freevars],
 disj1_tac >>
     rw [is_value_deBruijn_subst] >|
     [qpat_assum `∀tenvE1' targs' tvs''.
                     EVERY (check_freevars tvs'' []) targs' ∧
                     (bind_tvar tvs
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       (deBruijn_subst_e (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e)
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t)`
                (MP_TAC o Q.SPECL [`bind_tvar tvs tenvE1`, `targs`, `tvs'`]) >>
          rw [bind_tvar_rewrites] >>
          fs [MAP_MAP_o, combinTheory.o_DEF, deBruijn_inc_deBruijn_inc] >>
          metis_tac [],
      qpat_assum `∀tenvE1' targs' tvs''.
                     check_freevars (tvs + (num_tvs tenvE1 + LENGTH targs)) [] t ∧
                     EVERY (check_freevars tvs'' []) targs' ∧
                     (Bind_name n tvs t
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       (deBruijn_subst_e (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e')
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t')`
                 (MP_TAC o 
                  Q.SPECL [`Bind_name n tvs t tenvE1`, `targs`, `tvs'`]) >>
          rw [bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, 
              num_tvs_def] >>
          imp_res_tac type_e_freevars >>
          fs [tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge] >>
          fs [MAP_MAP_o, combinTheory.o_DEF, deBruijn_inc_deBruijn_inc] >>
          metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]],
 disj2_tac >>
     rw [] >>
     fs [deBruijn_inc0] >-
     metis_tac [] >>
     qpat_assum `∀tenvE1' targs' tvs'.
                     check_freevars (skip' + LENGTH targs) [] t ∧
                     EVERY (check_freevars tvs' []) targs' ∧
                     (Bind_name n 0 t
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs' tenvE2))
                       (deBruijn_subst_e (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e')
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t')`
                 (MP_TAC o 
                  Q.SPECL [`Bind_name n 0 t tenvE1`, `targs`, `tvs`]) >>
     rw [bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, 
         num_tvs_def] >>
     imp_res_tac type_e_freevars >>
     fs [tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge] >>
     metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM],
 qexists_tac `MAP (\(x,t). (x, deBruijn_subst skip' ts' t)) env` >>
     rw [] >|
     [qpat_assum `∀tenvE1' targs' tvs''.
                     tenv_ok
                       (bind_var_list 0 env
                          (bind_tvar tvs
                             (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)))) ∧
                     EVERY (check_freevars tvs'' []) targs' ∧
                     (bind_var_list 0 env
                        (bind_tvar tvs
                           (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2))) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_funs tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       (MAP
                          (λ(f,topt1,x,topt2,e').
                             (f,
                              option_map
                                (deBruijn_subst (num_tvs tenvE1')
                                   (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs'))
                                topt1,x,
                              option_map
                                (deBruijn_subst (num_tvs tenvE1')
                                   (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs'))
                                topt2,
                              deBruijn_subst_e (num_tvs tenvE1')
                                (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e'))
                          funs)
                       (MAP
                          (λ(x,t).
                             (x,
                              deBruijn_subst (num_tvs tenvE1')
                                (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t))
                          env)`
                 (MP_TAC o 
                  Q.SPECL [`bind_var_list 0 env (bind_tvar tvs tenvE1)`, `targs`, `tvs'`]) >>
          rw [bind_tvar_rewrites, db_merge_bind_var_list, num_tvs_bind_var_list, 
              deBruijn_subst_E_bind_var_list] >>
          `ts' = MAP (deBruijn_inc 0 skip') targs`
                      by metis_tac [MAP_MAP_o, combinTheory.o_DEF,deBruijn_inc_deBruijn_inc] >>
          fs [] >>
          rw [] >>
          pop_assum match_mp_tac >>
          match_mp_tac tenv_ok_bind_var_list >>
          rw [bind_tvar_rewrites] >>
          metis_tac [],
      qpat_assum `∀tenvE1' targs' tvs''.
                     tenv_ok
                       (bind_var_list tvs env
                          (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2))) ∧
                     EVERY (check_freevars tvs'' []) targs' ∧
                     (bind_var_list tvs env
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       (deBruijn_subst_e (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e)
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t)`
                 (MP_TAC o 
                  Q.SPECL [`bind_var_list tvs env tenvE1`, `targs`, `tvs'`]) >>
          rw [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list, db_merge_bind_var_list] >>
          `ts' = MAP (deBruijn_inc 0 skip') targs`
                      by metis_tac [MAP_MAP_o, combinTheory.o_DEF,deBruijn_inc_deBruijn_inc] >>
          fs [] >>
          rw [] >>
          pop_assum match_mp_tac >>
          match_mp_tac type_freevars_lem4 >>
          metis_tac []],
 fs [check_freevars_def] >>
     qpat_assum `∀tenvE1' targs' tvs'.
               check_freevars (num_tvs tenvE1 + LENGTH targs) [] t1 ∧
               EVERY (check_freevars tvs' []) targs' ∧
               (Bind_name n 0 t1
                  (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
               type_e tenvC
                 (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                    (bind_tvar tvs' tenvE2))
                 (deBruijn_subst_e (num_tvs tenvE1')
                    (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') e)
                 (deBruijn_subst (num_tvs tenvE1')
                    (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t)`
                 (MP_TAC o 
                  Q.SPECL [`Bind_name n 0 t1 tenvE1`, `targs`, `tvs`]) >>
     rw [deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def] >|
     [metis_tac [check_freevars_lem],
      metis_tac [check_freevars_lem],
      fs [lookup_notin, MAP_MAP_o, combinTheory.o_DEF, LIST_TO_SET_MAP] >>
          CCONTR_TAC >>
          fs [] >>
          PairCases_on `x'` >>
          fs [] >>
          rw [] >>
          fs [] >>
          metis_tac [mem_lem]]]);

val tenvC_pat_weakening = Q.store_thm ("tenvC_pat_weakening",
`(!tvs tenvC p t tenv. type_p tvs tenvC p t tenv ⇒
    !tenvC'. disjoint_env tenvC tenvC' ⇒
             type_p tvs (merge tenvC' tenvC) p t tenv) ∧
 (!tvs tenvC ps ts tenv. type_ps tvs tenvC ps ts tenv ⇒
    !tenvC'. disjoint_env tenvC tenvC' ⇒
             type_ps tvs (merge tenvC' tenvC) ps ts tenv)`,
ho_match_mp_tac type_p_ind >>
rw [] >>
rw [Once type_p_cases] >>
metis_tac [lookup_disjoint]);

val tenvC_weakening = Q.store_thm ("tenvC_weakening",
`(!tenvC tenv e t. type_e tenvC tenv e t ⇒
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_e (merge tenvC' tenvC) tenv e t) ∧
 (!tenvC tenv es ts. type_es tenvC tenv es ts ⇒
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_es (merge tenvC' tenvC) tenv es ts) ∧
 (!tenvC tenv funs tenv'. type_funs tenvC tenv funs tenv' ⇒
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_funs (merge tenvC' tenvC) tenv funs tenv')`,
ho_match_mp_tac type_e_ind >>
rw [] >>
rw [Once type_e_cases] >>
fs [RES_FORALL, FORALL_PROD] >>
metis_tac [lookup_disjoint, tenvC_pat_weakening]);

val check_ctor_tenv_dups_helper1 = Q.prove (
`∀tenvC l y z.
  (!x. MEM x l ⇒ (λ(n,ts). lookup n tenvC = NONE) x)
  ⇒
  DISJOINT (set (MAP (λx. FST ((λ(cn,ts). (cn,y,ts,z)) x)) l))
           (set (MAP FST tenvC))`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
fs [] >>
`(λ(n,ts). lookup n tenvC = NONE) (q,r)` by metis_tac [] >>
fs [] >>
metis_tac [lookup_notin]);

val check_ctor_tenv_dups_helper2 = Q.prove (
`!tds tenvC.
  (∀((tvs,tn,condefs)::set tds) ((n,ts)::set condefs). lookup n tenvC = NONE) ⇒
    disjoint_env tenvC (build_ctor_tenv tds)`,
induct_on `tds` >>
rw [build_ctor_tenv_def, disjoint_env_def] >|
[fs [RES_FORALL] >>
     cases_on `h` >>
     fs [] >>
     cases_on `r` >>
     fs [] >>
     `(λ(tvs,tn,condefs).
         ∀x. MEM x condefs ⇒ (λ(n,ts). lookup n tenvC = NONE) x) (q,q',r')`
                by metis_tac [] >>
     fs [MAP_MAP_o, combinTheory.o_DEF] >>
     metis_tac [check_ctor_tenv_dups_helper1],
 fs [RES_FORALL] >>
     `disjoint_env tenvC (build_ctor_tenv tds)` by metis_tac [] >>
     fs [disjoint_env_def, build_ctor_tenv_def] >>
     metis_tac [DISJOINT_SYM]]);

val check_ctor_tenv_dups = Q.store_thm ("check_ctor_tenv_dups",
`!tenvC tds.
  check_ctor_tenv tenvC tds ⇒ disjoint_env tenvC (build_ctor_tenv tds)`,
rw [check_ctor_tenv_def, check_dup_ctors_def] >>
metis_tac [check_ctor_tenv_dups_helper2, RES_FORALL]);

val disjoint_env_rev = Q.store_thm ("disjoint_env_rev",
`!tenvC tenvC'. disjoint_env tenvC tenvC' ⇒ disjoint_env tenvC (REVERSE tenvC')`,
induct_on `tenvC'` >>
rw [disjoint_env_def] >>
fs [Once DISJOINT_SYM] >>
metis_tac [disjoint_env_def, DISJOINT_SYM]);

val consistent_con_append = Q.prove (
`!envC tenvC.
  consistent_con_env envC tenvC ⇒
    ∀envC' tenvC'.
      consistent_con_env envC' tenvC'
      ⇒
      consistent_con_env (envC++envC') (tenvC++tenvC')`,
ho_match_mp_tac (fetch "-" "consistent_con_env_ind") >>
rw [consistent_con_env_def] >>
rw []);

val consistent_con_env_rev = Q.prove (
`!envC tenvC.
  consistent_con_env envC tenvC ⇒
  consistent_con_env (REVERSE envC) (REVERSE tenvC)`,
ho_match_mp_tac (fetch "-" "consistent_con_env_ind") >>
rw [consistent_con_env_def] >>
`consistent_con_env [(cn,LENGTH ts,ns)] [(cn,tvs,ts,tn)]`
              by rw [consistent_con_env_def] >>
metis_tac [consistent_con_append]);

val extend_consistent_con = Q.store_thm ("extend_consistent_con",
`!envC tenvC tds.
  consistent_con_env envC tenvC
  ⇒
  consistent_con_env (build_tdefs tds ++ envC)
                     (REVERSE (build_ctor_tenv tds) ++ tenvC)`,
induct_on `tds` >>
rw [build_tdefs_def, build_ctor_tenv_def] >>
cases_on `h` >>
cases_on `r` >>
fs [] >>
`!x. (!cn ts. MEM (cn,ts) r' ⇒ MEM (cn,ts) x) ⇒
  consistent_con_env
  (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) x})) r')
  (MAP (λ(cn,ts). (cn,q,ts,q')) r')`
            by (Induct_on `r'` >>
                rw [consistent_con_env_def] >>
                cases_on `h` >>
                cases_on `r` >>
                fs [] >>
                rw [consistent_con_env_def, GSPECIFICATION] >|
                [qexists_tac `(q'',[])` >>
                     rw [],
                 qexists_tac `(q'',h::t)` >>
                     rw []]) >>
fs [build_ctor_tenv_def, build_tdefs_def] >>
metis_tac [consistent_con_append, APPEND_ASSOC, consistent_con_env_rev,
           REVERSE_APPEND]);

val check_dup_ctors_disj = Q.store_thm ("check_dup_ctors_disj",
`!tenvC tds.
  check_dup_ctors tds tenvC ⇒ disjoint_env tenvC (build_ctor_tenv tds)`,
rw [check_dup_ctors_def] >>
metis_tac [check_ctor_tenv_dups_helper2]);

val consistent_con_env_destruct_help = Q.prove (
`!l x y q q' l'.
  consistent_con_env
    (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) l'})) l ++ x)
    (MAP (\(cn,ts). (cn,q,ts,q')) l ++ y)
  ⇒
  consistent_con_env x y`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
fs [consistent_con_env_def] >>
metis_tac []);

val lookup_append = Q.store_thm ("lookup_append",
`!x e1 e2.
  lookup x (e1++e2) =
     case lookup x e1 of
        | NONE => lookup x e2
        | SOME v => SOME v`,
induct_on `e1` >>
rw [lookup_def] >>
every_case_tac >>
PairCases_on `h` >>
fs [lookup_def] >>
rw [] >>
fs []);

val lookup_append_none = Q.store_thm ("lookup_append_none",
`!x e1 e2. 
  (lookup x (e1++e2) = NONE) = (lookup x e1 = NONE) ∧ (lookup x e2 = NONE)`,
rw [lookup_append] >>
eq_tac >>
rw [] >>
cases_on `lookup x e1` >>
rw [] >>
fs []);

val lookup_reverse_none = Q.store_thm ("lookup_reverse_none",
`!x tenvC.
  (lookup x (REVERSE tenvC) = NONE) = (lookup x tenvC = NONE)`,
induct_on `tenvC` >>
rw [] >>
cases_on `h` >>
rw [lookup_def,lookup_append_none]);

val lookup_none_lem = Q.prove (
`!x h0 h1 h2 h3.
  (lookup x (MAP (λ(cn,ts). (cn,h0,ts,h1)) h2) = NONE)
  = 
  (lookup x (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) h3})) h2) = NONE)`,
induct_on `h2` >>
rw [lookup_def] >>
PairCases_on `h` >>
rw [lookup_def]);
  

val lookup_none = Q.store_thm ("lookup_none",
`!tds tenvC envC x.
  !x. (lookup x (build_ctor_tenv tds) = NONE) =
      (lookup x (build_tdefs tds) = NONE)`,
Induct >>
rw [] >-
fs [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
rw [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
PairCases_on `h` >>
rw [lookup_append_none, REVERSE_APPEND, lookup_reverse_none] >>
eq_tac >>
rw [] >|
[metis_tac [lookup_none_lem],
 metis_tac [build_ctor_tenv_def, build_tdefs_def, lookup_reverse_none],
 metis_tac [lookup_none_lem],
 metis_tac [build_ctor_tenv_def, build_tdefs_def, lookup_reverse_none]]);

val build_ctor_tenv_empty = Q.store_thm ("build_ctor_tenv_empty",
`build_ctor_tenv [] = []`,
rw [build_ctor_tenv_def]);

val build_ctor_tenv_cons = Q.prove (
`∀tvs tn ctors tds.
  build_ctor_tenv ((tvs,tn,ctors)::tds) =
    MAP (λ(cn,ts). (cn,tvs,ts,tn)) ctors ++ build_ctor_tenv tds`,
rw [build_ctor_tenv_def]);

val lemma = Q.prove (
`!f a b c. (\(x,y,z). f x y z) (a,b,c) = f a b c`,
rw []);

val every_conj_tup3 = Q.prove (
`!P Q l.
  EVERY (\(x,y,z). P x y z ∧ Q x y z) l =
  EVERY (\(x,y,z). P x y z) l ∧
  EVERY (\(x,y,z). Q x y z) l`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
cases_on `r` >>
rw [] >>
metis_tac []);

val check_ctor_tenv_different_types = Q.store_thm ("check_ctor_tenv_different_types",
`!tenvC tds.
  EVERY
    (λ(tvs,tn,ctors).
       EVERY (λx. case x of (v,v2,v4,tn') => tn ≠ tn') tenvC) tds ∧
  (lookup n1 tenvC = SOME (tvs1,ts1,tn1)) ∧
  (lookup n2 (REVERSE (build_ctor_tenv tds)) = SOME (tvs2,ts2,tn2))
  ⇒
  (tn1 ≠ tn2)`,
induct_on `tenvC` >>
rw [build_ctor_tenv_empty,lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [] >|
[induct_on `tds` >>
     fs [lookup_def,build_ctor_tenv_empty]  >>
     rw [] >>
     cases_on `h` >>
     cases_on `r'` >>
     fs [build_ctor_tenv_cons, lookup_append, REVERSE_APPEND] >>
     every_case_tac >>
     fs [] >>
     induct_on `r''` >>
     fs [lookup_def] >>
     rw [] >>
     cases_on `h` >>
     fs [lookup_def] >>
     every_case_tac >>
     fs [] >>
     fs [lookup_append] >>
     every_case_tac >>
     fs [lookup_def],
 fs [every_conj_tup3] >>
     metis_tac []]);

val build_tdefs_cons = Q.prove (
`!tvs tn ctors tds.
  build_tdefs ((tvs,tn,ctors)::tds) =
    build_tdefs tds ++
    REVERSE (MAP (\(conN,ts). (conN, LENGTH ts, {cn | (cn,ts) | MEM (cn,ts) ctors}))
        ctors)`,
rw [build_tdefs_def]);

val check_dup_ctors_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_dup_ctors ((tvs,ts,ctors)::tds) tenvC
  ⇒
  check_dup_ctors tds tenvC`,
induct_on `tds` >>
rw [check_dup_ctors_def, LET_THM, RES_FORALL] >-
metis_tac [] >-
metis_tac [] >>
cases_on `h` >>
fs [] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
rw [] >>
cases_on `h` >>
fs []);

val check_ctor_tenv_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_ctor_tenv tenvC ((tvs,ts,ctors)::tds) ⇒
  check_ctor_tenv tenvC tds`,
rw [check_ctor_tenv_def] >>
metis_tac [check_dup_ctors_cons]);

val lookup_type = Q.prove (
`!x ctors tn tvs ts tn' tvs'.
  (lookup x (MAP (λ(cn,ts). (cn,tvs,ts,tn)) ctors) = SOME (tvs',ts,tn'))
  ⇒
  (tn = tn')`,
induct_on `ctors` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [] >>
metis_tac []);

val lookup_same_ctor_type_help = Q.prove (
`!tds.
  (lookup n2 (REVERSE (build_ctor_tenv tds)) = SOME (tvs2,ts2,tn))
  ⇒
  MEM tn (MAP (λx. case x of (v,tn,v3) => tn) tds)`,
Induct >>
rw [lookup_def,build_ctor_tenv_empty] >>
cases_on `h` >>
cases_on `r` >>
fs [build_ctor_tenv_cons, REVERSE_APPEND] >>
induct_on `r'` >>
rw [] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
fs [lookup_append] >>
every_case_tac >>
fs [lookup_def]);

val lookup_same_ctor_type_help2 = Q.prove (
`!ctors n1 ns1 r'.
  (lookup n1
    (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) r'})) ctors) =
   SOME (l1,ns1))
  ⇒
  (ns1 = {cn | (cn,ts) | MEM (cn,ts) r'})`,
Induct >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [] >>
metis_tac []);

val lookup_same_ctor_type = Q.store_thm ("lookup_same_ctor_type",
`!tds.
  check_ctor_tenv tenvC tds ∧
  (lookup n1 (REVERSE (build_ctor_tenv tds)) = SOME (tvs1,ts1,tn)) ∧
  (lookup n2 (REVERSE (build_ctor_tenv tds)) = SOME (tvs2,ts2,tn)) ∧
  (lookup n1 (build_tdefs tds) = SOME (l1,ns1)) ∧
  (lookup n2 (build_tdefs tds) = SOME (l2,ns2))
  ⇒
  (ns1 = ns2)`,
Induct >>
rw [] >-
fs [build_tdefs_def, lookup_def] >>
PairCases_on `h` >>
fs [build_ctor_tenv_cons,build_tdefs_cons, lookup_append,
    REVERSE_APPEND] >>
`check_ctor_tenv tenvC tds` by metis_tac [check_ctor_tenv_cons] >>
every_case_tac >>
fs [lookup_reverse_none, lookup_none] >>
rw [] >|
[metis_tac [lookup_same_ctor_type_help2, rich_listTheory.MAP_REVERSE],
 metis_tac [lookup_same_ctor_type_help2, rich_listTheory.MAP_REVERSE],
 metis_tac [lookup_same_ctor_type_help2, rich_listTheory.MAP_REVERSE],
 metis_tac [lookup_same_ctor_type_help2, rich_listTheory.MAP_REVERSE],
 `h1 = tn` by metis_tac [lookup_type, rich_listTheory.MAP_REVERSE] >>
     rw [] >>
     fs [check_ctor_tenv_def] >>
     metis_tac [lookup_same_ctor_type_help],
 metis_tac [lookup_none, optionTheory.NOT_SOME_NONE, lookup_reverse_none],
 `h1 = tn` by metis_tac [lookup_type, rich_listTheory.MAP_REVERSE] >>
     rw [] >>
     fs [check_ctor_tenv_def] >>
     metis_tac [lookup_same_ctor_type_help],
 metis_tac [lookup_none, optionTheory.NOT_SOME_NONE, lookup_reverse_none]]);

val extend_consistent_con2 = Q.store_thm ("extend_consistent_con2",
`!envC tenvC tds.
  check_ctor_tenv tenvC tds ∧
  consistent_con_env2 envC tenvC ⇒
  consistent_con_env2 (build_tdefs tds ++ envC) (REVERSE (build_ctor_tenv tds) ++ tenvC)`,
rw [consistent_con_env2_def, lookup_append] >>
every_case_tac >>
fs [lookup_none, lookup_reverse_none] >-
metis_tac [] >>
imp_res_tac check_dup_ctors_disj >|
[metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none, 
            check_ctor_tenv_different_types, check_ctor_tenv_def],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none, 
            check_ctor_tenv_different_types, check_ctor_tenv_def],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_none, lookup_reverse_none],
 metis_tac [lookup_same_ctor_type]]);

val type_e_tvs_weaken_help = Q.prove (
`!(x:num) y z. x + y ≥ x`,
rw [] >>
decide_tac);

val type_p_tvs_weaken = Q.prove (
`(!tvs tenvC p t tenv. type_p tvs tenvC p t tenv ⇒
    !tvs'. type_p (tvs + tvs') tenvC p t tenv) ∧
 (!tvs tenvC ps ts tenv. type_ps tvs tenvC ps ts tenv ⇒
    !tvs'. type_ps (tvs + tvs') tenvC ps ts tenv)`,
ho_match_mp_tac type_p_ind >>
rw [] >>
ONCE_REWRITE_TAC [type_p_cases] >>
rw [] >>
metis_tac [type_e_tvs_weaken_help, check_freevars_add, EVERY_MEM]);

val type_e_tvs_weaken = Q.store_thm ("type_e_tvs_weaken",
`(!tenvC tenvE e t. type_e tenvC tenvE e t ⇒
    !tenvE1 tenvE2 tvs.
      tenv_ok tenvE2 ∧
      (num_tvs tenvE2 = 0) ∧
      (tenvE = db_merge tenvE1 (bind_tvar 0 tenvE2))
      ⇒
      type_e tenvC (db_merge tenvE1 (bind_tvar tvs tenvE2)) e t) ∧
 (!tenvC tenvE es ts. type_es tenvC tenvE es ts ⇒
    !tenvE1 tenvE2 tvs.
      tenv_ok tenvE2 ∧
      (num_tvs tenvE2 = 0) ∧
      (tenvE = db_merge tenvE1 (bind_tvar 0 tenvE2))
      ⇒
    type_es tenvC (db_merge tenvE1 (bind_tvar tvs tenvE2)) es ts) ∧
 (!tenvC tenvE funs env. type_funs tenvC tenvE funs env ⇒
    !tenvE1 tenvE2 tvs.
      tenv_ok tenvE2 ∧
      (num_tvs tenvE2 = 0) ∧
      (tenvE = db_merge tenvE1 (bind_tvar 0 tenvE2))
      ⇒
      type_funs tenvC (db_merge tenvE1 (bind_tvar tvs tenvE2)) funs env)`,
ho_match_mp_tac type_e_strongind >>
rw [] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [] >>
fs [num_tvs_db_merge, bind_tvar_rewrites] >|
[metis_tac [type_e_tvs_weaken_help, check_freevars_add],
 metis_tac [db_merge_def, bind_tenv_def],
 metis_tac [type_e_tvs_weaken_help, check_freevars_add, EVERY_MEM],
 qexists_tac `t` >>
     rw [] >-
     metis_tac [type_e_tvs_weaken_help, check_freevars_add, EVERY_MEM] >>
     fs [lookup_tenv_db_merge] >>
     every_case_tac >>
     fs [bind_tvar_rewrites] >>
     induct_on `tenvE2` >>
     rw [lookup_tenv_def, num_tvs_def] >>
     fs [tenv_ok_def] >>
     rw [nil_deBruijn_inc],
 metis_tac [type_e_tvs_weaken_help, check_freevars_add, EVERY_MEM, db_merge_def,
            bind_tenv_def],
 metis_tac [db_merge_def, bind_tenv_def],
 metis_tac [db_merge_def, bind_tenv_def],
 fs [RES_FORALL] >>
     rw [] >>
     qexists_tac `t` >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     rw [] >>
     RES_TAC >>
     fs [] >>
     metis_tac [type_p_tvs_weaken, db_merge_bind_var_list],
 metis_tac [db_merge_def, bind_tenv_def, bind_tvar_def],
 metis_tac [db_merge_def, bind_tenv_def],
 metis_tac [db_merge_def, bind_tenv_def, bind_tvar_def, db_merge_bind_var_list],
 fs [Tfn_def] >>
     metis_tac [type_e_tvs_weaken_help, check_freevars_add, EVERY_MEM,
                db_merge_def, bind_tenv_def]]);

val _ = export_theory ();

