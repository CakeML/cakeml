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
  (lookup cn tenvC = SOME (tvs, ts, tn)) ⇒ 
     (∃ns. (lookup cn envC = SOME (LENGTH ts, ns)) ∧ cn IN ns) 
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

val check_freevars_subst_list = Q.prove (
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

val type_freevars_lem3 = Q.prove (
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
rw [check_freevars_def, bind_tenv_def,
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
rw [check_freevars_def, bind_tenv_def, num_tvs_def, type_uop_def, type_op_def,
    tenv_ok_def, bind_tvar_def, bind_var_list_def] >|
[metis_tac [deBruijn_subst_check_freevars],
 metis_tac [type_e_freevars_lem2, arithmeticTheory.ADD],
 cases_on `uop` >>
     fs [check_freevars_def] >>
     cases_on `t` >>
     fs [check_freevars_def],
 cases_on `op` >>
     fs [check_freevars_def] >>
     cases_on `t` >>
     fs [check_freevars_def] >>
     cases_on `t'` >>
     fs [check_freevars_def],
 cases_on `pes` >>
     fs [RES_FORALL, num_tvs_bind_var_list] >>
     qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `(FST h, SND h)`) >>
     fs [] >>
     metis_tac [type_p_freevars, type_freevars_lem5],
 metis_tac [type_freevars_lem3, num_tvs_bind_var_list],
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
fs [lookup_def, bind_def, deBruijn_subst_def] >>
rw [check_freevars_def] >>
metis_tac [bind_tenv_def, num_tvs_def, type_e_freevars, type_funs_Tfn,
           check_freevars_def]);

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
FOLDR (λx. case x of (f,topt1,x,topt2,e) => λenv'. bind f (Recclosure env funs' f, add_tvs tvs topt1) env') env funs =
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

val type_op_cases = Q.store_thm ("type_op_cases",
`!op t1 t2 t3.
  type_op op t1 t2 t3 =
  ((∃op'. op = Opn op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tint)) ∨
  ((∃op'. op = Opb op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tbool)) ∨
  ((op = Opapp) ∧ (t1 = Tfn t2 t3)) ∨
  ((op = Equality) ∧ (t1 = t2) ∧ (t3 = Tbool)) ∨
  ((op = Opassign) ∧ (t1 = Tref t2) ∧ (t3 = Tunit))`,
rw [type_op_def] >>
cases_on `op` >>
rw [] >>
cases_on `t1` >>
rw [] >>
every_case_tac >>
fs [] >>
metis_tac []);

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

val type_subst_deBruijn_subst_list = Q.prove (
`!t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (ZIP (tvs,ts))) ts'') =
   MAP (type_subst (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) ts'')`,
induct_on `ts''` >>
rw [] >>
metis_tac [type_subst_deBruijn_subst_single]);

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

(*
val deBruijn_subst_order = Q.prove (
`!sk ts' t.
  deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) ts')) ts) (deBruijn_subst (LENGTH ts + sk) ts' t)
  =
  deBruijn_subst sk (MAP (deBruijn_inc 0 sk) ts') (deBruijn_subst 0 ts t)`,

ho_match_mp_tac deBruijn_subst_ind >>
rw [deBruijn_subst_def] >>
rw [] >>
full_simp_tac (srw_ss() ++ ARITH_ss) [EL_MAP]

decide_tac
*)

(*
∃tenv'.
  type_env tenvC senv env tenv' ∧
  type_e tenvC
    (bind_tenv x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenv'))
    (deBruijn_subst_e 0 targs e) (deBruijn_subst 0 targs t2)
------------------------------------
  0.  tenvC_ok tenvC
  1.  EVERY (check_freevars tvs []) targs
  2.  check_freevars (LENGTH targs) [] t2
  3.  type_env tenvC senv env tenv
  4.  check_freevars (LENGTH targs) [] t1
  5.  type_e tenvC (bind_tenv x 0 t1 (bind_tvar (LENGTH targs) tenv)) e
        t2
        *)

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
rw [deBruijn_subst_p_def, deBruijn_subst_def, option_map_eqns] >|
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

val deBruijn_subst_E_bind_var_list = Q.prove (
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

val db_merge_bind_var_list = Q.prove (
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
    num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_ok_def] >>
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
     rw [db_merge_def] >>
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
 metis_tac [type_e_subst_lem3],
 qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'` 
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     fs [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def],
 cases_on `uop` >>
     fs [type_uop_def] >>
     rw [] >>
     fs [] >>
     rw [deBruijn_subst_def] >>
     cases_on `t` >>
     fs [] >>
     rw [] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) (Tref t')` >>
     fs [deBruijn_subst_def],
 cases_on `op` >>
     fs [type_op_def] >|
     [cases_on `t` >>
          fs [] >>
          cases_on `t'` >>
          fs [] >>
          qexists_tac `Tint` >>
          qexists_tac `Tint` >>
          fs [deBruijn_subst_def] >>
          rw [] >>
          metis_tac [],
      cases_on `t` >>
          fs [] >>
          cases_on `t'` >>
          fs [] >>
          qexists_tac `Tint` >>
          qexists_tac `Tint` >>
          fs [deBruijn_subst_def] >>
          rw [] >>
          metis_tac [],
      fs [deBruijn_subst_def] >>
          qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t'` >>
          rw [],
      cases_on `t` >>
          fs [] >>
          qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) (Tfn t''' t0)` >>
          fs [deBruijn_subst_def],
      cases_on `t` >>
          fs [] >>
          qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) (Tref t')` >>
          qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t'` >>
          rw [deBruijn_subst_def]],
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
          match_mp_tac type_freevars_lem3 >>
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
     metis_tac [check_freevars_lem],
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
     rw [deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def] >>
     pop_assum match_mp_tac >>
     fs [check_freevars_def],
 fs [lookup_notin, MAP_MAP_o, combinTheory.o_DEF, LIST_TO_SET_MAP] >>
     CCONTR_TAC >>
     fs [] >>
     PairCases_on `x'` >>
     fs [] >>
     rw [] >>
     fs [] >>
     metis_tac [mem_lem]]);

val _ = export_theory ();

