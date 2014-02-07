(* Theorems about the type system. *)

open preamble rich_listTheory optionTheory;
open miscTheory alistTheory;
open libTheory astTheory typeSystemTheory typeSoundInvariantsTheory terminationTheory;
open libPropsTheory;

val _ = new_theory "typeSysProps";

val check_dup_ctors_def = semanticPrimitivesTheory.check_dup_ctors_def;
val build_tdefs_def = semanticPrimitivesTheory.build_tdefs_def;
val find_recfun_def = semanticPrimitivesTheory.find_recfun_def;
val same_tid_def = semanticPrimitivesTheory.same_tid_def;
val lookup_con_id_def = semanticPrimitivesTheory.lookup_con_id_def;
val merge_envC_def = semanticPrimitivesTheory.merge_envC_def;

(* ---------- check_freevars ---------- *)

val check_freevars_add = Q.store_thm ("check_freevars_add",
`(!tvs tvs' t. check_freevars tvs tvs' t ⇒ 
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def] >-
metis_tac [MEM_EL, EVERY_MEM] >>
decide_tac);

(* ---------- type_subst ---------- *)

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

(* ---------- deBruijn_inc ---------- *)

val deBruijn_inc0 = Q.store_thm ("deBruijn_inc0",
`(!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)`,
ho_match_mp_tac t_induction >>
rw [deBruijn_inc_def] >>
metis_tac []);

val deBruijn_inc_deBruijn_inc = Q.store_thm ("deBruijn_inc_deBruijn_inc",
`!sk i2 t i1. 
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t`,
ho_match_mp_tac deBruijn_inc_ind >>
rw [deBruijn_inc_def] >>
rw [] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
fs []);

val deBuijn_inc_lem1 = Q.prove (
`!sk i2 t i1. 
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t`,
ho_match_mp_tac deBruijn_inc_ind >>
rw [deBruijn_inc_def] >>
rw [] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
rw []);

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

val check_freevars_deBruijn_inc = Q.prove (
`!tvs tvs' t. check_freevars tvs tvs' t ⇒ 
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM] >>
rw [check_freevars_def] >>
decide_tac);

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

(* ---------- deBruijn_subst ---------- *)

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

val deBruijn_subst_check_freevars2 = Q.store_thm ("deBruijn_subst_check_freevars2",
`!tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
fs [EVERY_MEM] >>
fs [MEM_EL] >>
rw [] >>
metis_tac []);

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

val nil_deBruijn_subst = Q.store_thm ("nil_deBruijn_subst",
`∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)`,
ho_match_mp_tac deBruijn_subst_ind >>
rw [deBruijn_subst_def, check_freevars_def] >>
induct_on `ts'` >>
rw []);

val deBruijn_subst2 = Q.store_thm ("deBruijn_subst2",
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
metis_tac [deBuijn_inc_lem1]);

val subst_inc_cancel = Q.store_thm ("subst_inc_cancel",
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

val deBruijn_subst_id = Q.store_thm ("deBruijn_subst_id",
`(!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts))`,
Induct >>
rw [deBruijn_subst_def, LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST,
    check_freevars_def] >>
metis_tac []);

(* ---------- tenvC stuff ----------*)
(* merge_tenvC, lookup_con_id, flat_tenvC_ok, tenvC_ok *)

val flat_tenvC_ok_merge = Q.prove (
`!tenvC1 tenvC2.
  flat_tenvC_ok (merge tenvC1 tenvC2) = 
  (flat_tenvC_ok tenvC1 ∧ flat_tenvC_ok tenvC2)`, 
rw [flat_tenvC_ok_def, merge_def, ALL_DISTINCT_APPEND] >>
eq_tac >>
rw [DISJOINT_DEF, EXTENSION] >>
metis_tac []);

val tenvC_ok_merge = Q.store_thm ("tenvC_ok_merge",
`!tenvC1 tenvC2.
  tenvC_ok (merge_tenvC tenvC1 tenvC2) = 
  (tenvC_ok tenvC1 ∧ tenvC_ok tenvC2)`, 
 rw [] >>
 PairCases_on `tenvC1` >>
 PairCases_on `tenvC2` >>
 rw [tenvC_ok_def, merge_tenvC_def, ALL_DISTINCT_APPEND] >>
 eq_tac >>
 rw [merge_def, EVERY_MEM] >>
 res_tac >>
 metis_tac [flat_tenvC_ok_merge, merge_def]);
val flat_tenvC_ok_lookup = Q.prove (
`!tenvC cn tvs ts tn.
  flat_tenvC_ok tenvC ∧ (lookup cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
induct_on `tenvC` >>
rw [] >>
PairCases_on `h` >>
fs [flat_tenvC_ok_def] >>
every_case_tac >>
rw [] >>
fs [] >>
metis_tac []);

val lookup_con_id_merge_emp = Q.store_thm ("lookup_con_id_merge_emp",
`(!cn envC1 envC2.
  lookup_con_id cn (merge_envC (emp,envC1) envC2) =
    case lookup_con_id cn (emp,envC1) of
       | NONE => lookup_con_id cn envC2
       | SOME v => SOME v) ∧
 (!cn envC1 envC2.
  lookup_con_id cn (merge_tenvC (emp,envC1) envC2) =
    case lookup_con_id cn (emp,envC1) of
       | NONE => lookup_con_id cn envC2
       | SOME v => SOME v)`,
 rw [] >>
 PairCases_on `envC2` >>
 cases_on `cn` >>
 fs [lookup_con_id_def, merge_envC_def, merge_tenvC_def, merge_def, lookup_append] >>
 every_case_tac >>
 fs [emp_def]);

val tenvC_ok_lookup = Q.store_thm ("tenvC_ok_lookup",
`!tenvC cn tvs ts tn.
  tenvC_ok tenvC ∧ (lookup_con_id cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 cases_on `cn` >>
 rw [] >>
 PairCases_on `tenvC` >>
 fs [lookup_con_id_def, tenvC_ok_def]
 >- metis_tac [flat_tenvC_ok_lookup] >> 
 every_case_tac >>
 fs [] >>
 imp_res_tac lookup_in >>
 fs [MEM_MAP, EVERY_MEM] >>
 rw [] >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 PairCases_on `y'` >>
 fs [] >>
 rw [] >>
 res_tac >>
 fs [] >>
 imp_res_tac flat_tenvC_ok_lookup >>
 fs [EVERY_MEM]);

(* ---------- tenv stuff ---------- *)
(* bind_tvar, bind_var_list, bind_var_list2, lookup_tenv, bind_tenv,
 * t_lookup_var_id, num_tvs, deBruijn_subst_tenvE, db_merge, tenv_ok *)

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

val bind_var_list_append = Q.store_thm ("bind_var_list_append",
`!n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3)`,
induct_on `te1` >>
rw [bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def]);

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

val num_tvs_bvl2 = Q.store_thm ("num_tvs_bvl2",
`!tenv1 tenv2. num_tvs (bind_var_list2 tenv1 tenv2) = num_tvs tenv2`,
ho_match_mp_tac bind_var_list2_ind >>
rw [num_tvs_def, bind_var_list2_def, bind_tenv_def]);

val num_tvs_bind_var_list = Q.store_thm ("num_tvs_bind_var_list",
`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE`,
induct_on `env` >>
rw [num_tvs_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def, bind_tenv_def, num_tvs_def]);

val tenv_ok_bind_var_list = Q.store_thm ("tenv_ok_bind_var_list",
`!tenvE env.
  tenv_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_ok (bind_var_list 0 env tenvE)`,
induct_on `env` >>
rw [tenv_ok_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_tenv_def, tenv_ok_def, bind_var_list_def] >>
fs [num_tvs_bind_var_list]);

val lookup_freevars = Q.store_thm ("lookup_freevars",
`!n tenv tvs t.
  tenv_ok (bind_var_list2 tenv Empty) ∧
  (lookup n tenv = SOME (tvs, t))
  ⇒
  check_freevars tvs [] t`,
induct_on `tenv` >>
rw [lookup_def] >>
PairCases_on `h` >>
fs [lookup_def, bind_var_list2_def, tenv_ok_def, bind_tenv_def] >>
every_case_tac >>
fs [] >>
metis_tac [num_tvs_bvl2, arithmeticTheory.ADD_0, num_tvs_def]);

val type_e_freevars_lem3 = Q.prove (
`!tenv tenv' targs n t inc.
  EVERY (check_freevars (num_tvs tenv') []) targs ∧
  (lookup n tenv = SOME (LENGTH targs,t)) ∧
  tenv_ok (bind_var_list2 tenv Empty)
  ⇒ 
  check_freevars (num_tvs tenv') [] (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
rw [lookup_def, tenv_ok_def, bind_var_list2_def] >>
PairCases_on `h` >>
rw [] >>
fs [lookup_def, tenv_ok_def, bind_var_list2_def, bind_tenv_def] >>
cases_on `h0 = n` >>
fs [] >>
rw [] >>
metis_tac [deBruijn_subst_check_freevars2, arithmeticTheory.ADD_0, num_tvs_bvl2, num_tvs_def]);

val lookup_tenv_db_merge = Q.store_thm ("lookup_tenv_db_merge",
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

val lookup_tenv_deBruijn_subst_tenvE = Q.store_thm ("lookup_tenv_deBruijn_subst_tenvE",
`∀n e targs tvs t inc.
  (lookup_tenv n inc e = SOME (tvs,t)) 
  ⇒
  (lookup_tenv n inc (deBruijn_subst_tenvE targs e) = 
     SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t))`,
induct_on `e` >>
rw [lookup_tenv_def,deBruijn_subst_tenvE_def, deBruijn_inc_def, num_tvs_def] >>
metis_tac [arithmeticTheory.ADD_ASSOC, type_e_subst_lem5]);

val num_tvs_db_merge = Q.store_thm ("num_tvs_db_merge",
`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
induct_on `e1` >>
rw [num_tvs_def, db_merge_def] >>
decide_tac);

val num_tvs_deBruijn_subst_tenvE = Q.store_thm ("num_tvs_deBruijn_subst_tenvE",
`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE`,
induct_on `tenvE` >>
rw [deBruijn_subst_tenvE_def, num_tvs_def]);

val lookup_tenv_subst_none = Q.prove (
`!n inc e.
 (lookup_tenv n inc e = NONE) ⇒ 
 (lookup_tenv n inc (deBruijn_subst_tenvE targs e) = NONE)`,
induct_on `e` >>
rw [deBruijn_subst_tenvE_def, lookup_tenv_def]);

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

val tenv_ok_db_merge = Q.prove (
`!e1 e2. tenv_ok (db_merge e1 e2) ⇒ tenv_ok e2`,
induct_on `e1` >>
rw [tenv_ok_def, db_merge_def]);

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

val lookup_tenv_freevars = Q.prove (
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

val lookup_tenv_inc = Q.store_thm ("lookup_tenv_inc",
`!tvs l tenv n t.
  tenv_ok tenv ∧
  (num_tvs tenv = 0)
  ⇒
  ((lookup_tenv n 0 tenv = SOME (l,t))
   =
   (lookup_tenv n tvs tenv = SOME (l,t)))`,
induct_on `tenv` >>
rw [lookup_tenv_def, num_tvs_def, tenv_ok_def] >>
eq_tac >>
rw [] >>
fs [] >>
metis_tac [nil_deBruijn_inc, deBruijn_inc0]);

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

val tenv_ok_bvl2 = Q.store_thm ("tenv_ok_bvl2",
`!tenv tenv'. 
  tenv_ok (bind_var_list2 tenv Empty) ∧ tenv_ok tenv'
  ⇒
  tenv_ok (bind_var_list2 tenv tenv')`,
ho_match_mp_tac bind_var_list2_ind >>
rw [bind_var_list2_def, tenv_ok_def, bind_tenv_def, num_tvs_bvl2, num_tvs_def] >>
`tvs + num_tvs tenv' ≥ tvs` by decide_tac >>
metis_tac [check_freevars_add]);

val bvl2_lookup = Q.store_thm ("bvl2_lookup",
`!n tenv. lookup n tenv = lookup_tenv n 0 (bind_var_list2 tenv Empty)`,
ho_match_mp_tac lookup_ind >>
rw [lookup_def, bind_var_list2_def, lookup_tenv_def] >>
cases_on `n''` >>
rw [bind_var_list2_def, lookup_tenv_def, bind_tenv_def, deBruijn_inc0]);

val bvl2_append = Q.store_thm ("bvl2_append",
`!tenv1 tenv3 tenv2.
  (bind_var_list2 (tenv1 ++ tenv2) tenv3 = 
   bind_var_list2 tenv1 (bind_var_list2 tenv2 tenv3))`,
ho_match_mp_tac bind_var_list2_ind >>
rw [bind_var_list2_def]);

val bvl2_to_bvl = Q.store_thm ("bvl2_to_bvl",
`!tvs tenv tenv'. bind_var_list2 (tenv_add_tvs tvs tenv) tenv' = bind_var_list tvs tenv tenv'`,
ho_match_mp_tac bind_var_list_ind >>
rw [bind_var_list_def, bind_var_list2_def, tenv_add_tvs_def]);

(* ---------- tenvM stuff ---------- *)

val tenvM_ok_lookup = Q.store_thm ("tenvM_ok_lookup",
`!n tenvM tenvC tenv.
  tenvM_ok tenvM ∧
  (lookup n tenvM = SOME tenv) ⇒
  tenv_ok (bind_var_list2 tenv Empty)`,
induct_on `tenvM` >>
rw [lookup_def, tenvM_ok_def] >>
PairCases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac [tenvM_ok_def]);

val type_e_freevars_lem4 = Q.prove (
`!tenvM tenv targs n t.
  EVERY (check_freevars (num_tvs tenv) []) targs ∧
  (t_lookup_var_id n tenvM tenv = SOME (LENGTH targs,t)) ∧
  tenvM_ok tenvM ∧
  tenv_ok tenv
  ⇒ 
  check_freevars (num_tvs tenv) [] (deBruijn_subst 0 targs t)`,
rw [t_lookup_var_id_def] >>
every_case_tac >>
fs [] >>
imp_res_tac tenvM_ok_lookup >>
metis_tac [type_e_freevars_lem3,type_e_freevars_lem2,arithmeticTheory.ADD]);

val freevars_t_lookup_var_id = Q.store_thm ("freevars_t_lookup_var_id",
`!tenvM tenv tvs n t.
  (t_lookup_var_id n tenvM tenv = SOME (tvs,t)) ∧
  tenvM_ok tenvM ∧
  tenv_ok tenv
  ⇒ 
  check_freevars (num_tvs tenv + tvs) [] t`,
rw [t_lookup_var_id_def] >>
every_case_tac >>
fs [] >|
[imp_res_tac lookup_tenv_freevars >>
     full_simp_tac (srw_ss()++ARITH_ss) [],
 imp_res_tac tenvM_ok_lookup >>
     imp_res_tac lookup_freevars >>
     `num_tvs tenv + tvs ≥ tvs` by decide_tac >>
     metis_tac [check_freevars_add]]);

(* ---------- type_uop ---------- *)

val type_uop_cases = Q.store_thm ("type_uop_cases",
`∀uop t1 t2.
  type_uop uop t1 t2 =
  (((uop = Opref) ∧ (t2 = Tref t1)) ∨
   ((uop = Opderef) ∧ (t1 = Tref t2)))`,
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

(* ---------- type_op ---------- *)

val type_op_cases = Q.store_thm ("type_op_cases",
`!op t1 t2 t3.
  type_op op t1 t2 t3 =
  (((∃op'. op = Opn op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tint)) ∨
   ((∃op'. op = Opb op') ∧ (t1 = Tint) ∧ (t2 = Tint) ∧ (t3 = Tbool)) ∨
   ((op = Opapp) ∧ (t1 = Tfn t2 t3)) ∨
   ((op = Equality) ∧ (t1 = t2) ∧ (t3 = Tbool)) ∨
   ((op = Opassign) ∧ (t1 = Tref t2) ∧ (t3 = Tunit)))`,
rw [type_op_def, Tfn_def, Tint_def, Tbool_def, Tunit_def, Tref_def] >>
cases_on `op` >>
rw [] >>
cases_on `t1` >>
rw [] >|
[cases_on `t2` >>
     fs [],
 cases_on `t2` >>
     fs [],
 cases_on `t2` >>
     rw [] >>
     cases_on `t'` >>
     rw [] >>
     every_case_tac,
 cases_on `t2` >>
     fs [],
 cases_on `t2` >>
     fs [],
 cases_on `t2` >>
     rw [] >>
     cases_on `t'` >>
     rw [] >>
     every_case_tac,
 cases_on `t` >>
     rw []  >>
     every_case_tac >>
     metis_tac [],
 cases_on `t` >>
     rw []  >>
     every_case_tac >>
     metis_tac []]);

(* ---------- type_p ---------- *)

val type_ps_length = Q.store_thm ("type_ps_length",
`∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)`,
induct_on `ps` >>
rw [Once type_p_cases] >>
rw [] >>
metis_tac []);

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

val type_p_subst = Q.store_thm ("type_p_subst",
`(!n tenvC p t tenv. type_p n tenvC p t tenv ⇒
    !targs' inc tvs targs.
    tenvC_ok tenvC ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenvC 
           p
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
           ps
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) tenv))`,
ho_match_mp_tac type_p_strongind >>
rw [] >>
ONCE_REWRITE_TAC [type_p_cases] >>
rw [deBruijn_subst_def, OPTION_MAP_DEF, Tint_def,
    Tbool_def, Tunit_def, Tref_def] >|
[metis_tac [check_freevars_lem],
 rw [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [check_freevars_lem, EVERY_MEM],
 metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup],
 metis_tac [],
 metis_tac []]); 

val type_p_bvl = Q.store_thm ("type_p_bvl",
`(!tvs tenvC p t tenv. type_p tvs tenvC p t tenv ⇒
  !tenv'. tenv_ok tenv' ⇒ tenv_ok (bind_var_list tvs tenv tenv')) ∧
 (!tvs tenvC ps ts tenv. type_ps tvs tenvC ps ts tenv ⇒
  !tenv'. tenv_ok tenv' ⇒ tenv_ok (bind_var_list tvs tenv tenv'))`,
ho_match_mp_tac type_p_ind >>
rw [bind_var_list_def, tenv_ok_def, bind_tenv_def, num_tvs_def,
    bind_var_list_append] >>
`tvs + num_tvs tenv' ≥ tvs` by decide_tac >>
metis_tac [check_freevars_add]);

(* ---------- type_e, type_es, type_funs ---------- *)

val type_es_length = Q.store_thm ("type_es_length",
`∀tenvM tenvC tenv es ts.
  type_es tenvM tenvC tenv es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
rw [Once type_e_cases] >>
rw [] >>
metis_tac []);

val tenv_ok_bind_var_list_tvs = Q.store_thm ("tenv_ok_bind_var_list_tvs",
`!funs tenvM tenvC env tenvE tvs env'.
  type_funs tenvM tenvC (bind_var_list 0 env' (bind_tvar tvs tenvE)) funs env ∧
  tenv_ok tenvE
  ⇒
  tenv_ok (bind_var_list tvs env tenvE)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [check_freevars_def, bind_tenv_def, bind_var_list_def, tenv_ok_def] >>
cases_on `tvs = 0` >>
fs [check_freevars_def, num_tvs_bind_var_list, bind_tvar_def, num_tvs_def] >>
metis_tac []);

val tenv_ok_bind_var_list_funs = Q.store_thm ("tenv_ok_bind_var_list_funs",
`!funs tenvM tenvC env tenvE tvs env'.
  type_funs tenvM tenvC (bind_var_list 0 env' tenvE) funs env ∧
  tenv_ok tenvE
  ⇒
  tenv_ok (bind_var_list 0 env tenvE)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [check_freevars_def, bind_tenv_def, bind_var_list_def, tenv_ok_def] >>
fs [check_freevars_def, num_tvs_bind_var_list] >>
metis_tac []);

val type_e_freevars = Q.store_thm ("type_e_freevars",
`(!tenvM tenvC tenvE e t. 
   type_e tenvM tenvC tenvE e t ⇒ 
   tenvM_ok tenvM ∧
   tenv_ok tenvE ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenvM tenvC tenvE es ts. 
   type_es tenvM tenvC tenvE es ts ⇒
   tenvM_ok tenvM ∧
   tenv_ok tenvE ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenvM tenvC tenvE funs env. 
   type_funs tenvM tenvC tenvE funs env ⇒
   tenvM_ok tenvM ∧
   tenv_ok tenvE ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env))`,
ho_match_mp_tac type_e_strongind >>
rw [check_freevars_def, bind_tenv_def, num_tvs_def, type_uop_cases, type_op_cases,
    tenv_ok_def, bind_tvar_def, bind_var_list_def, Tbool_def, Tint_def, Tfn_def,
    Tunit_def, Tref_def] >>
fs [check_freevars_def] >|
[metis_tac [deBruijn_subst_check_freevars],
 metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD],
 metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD],
 cases_on `pes` >>
     fs [RES_FORALL, num_tvs_bind_var_list] >>
     qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `(FST h, SND h)`) >>
     fs [] >>
     metis_tac [type_p_freevars, tenv_ok_bind_var_list],
 metis_tac [tenv_ok_bind_var_list_funs, num_tvs_bind_var_list],
 metis_tac [tenv_ok_bind_var_list_tvs, num_tvs_bind_var_list, bind_tvar_def]]);

val type_e_subst = Q.store_thm ("type_e_subst",
`(!tenvM tenvC tenvE e t. type_e tenvM tenvC tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvM_ok tenvM ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
      type_e tenvM tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) 
                   e
                   (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
 (!tenvM tenvC tenvE es ts. type_es tenvM tenvC tenvE es ts ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvM_ok tenvM ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
    type_es tenvM tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                  es
                  (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
 (!tenvM tenvC tenvE funs env. type_funs tenvM tenvC tenvE funs env ⇒
    !tenvE1 targs tvs targs'.
      (num_tvs tenvE2 = 0) ∧
      tenvM_ok tenvM ∧
      tenvC_ok tenvC ∧
      tenv_ok tenvE ∧
      (EVERY (check_freevars tvs []) targs) ∧
      (tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) ∧
      (targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
      ⇒
      type_funs tenvM tenvC (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) 
                      funs 
                      (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env))`,
ho_match_mp_tac type_e_strongind >>
rw [] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [deBruijn_subst_def, deBruijn_subst_tenvE_def, 
    bind_tvar_rewrites, bind_tenv_def, num_tvs_def, OPTION_MAP_DEF,
    num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE] >>
fs [deBruijn_subst_def, deBruijn_subst_tenvE_def, 
    bind_tvar_rewrites, bind_tenv_def, num_tvs_def, OPTION_MAP_DEF,
    num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_ok_def,
    Tbool_def, Tint_def, Tunit_def, Tref_def, Tfn_def] >>
`tenv_ok tenvE2` by metis_tac [tenv_ok_db_merge, bind_tvar_def, tenv_ok_def] >|
[metis_tac [check_freevars_lem],
 fs [Texn_def, deBruijn_subst_def],
 fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     fs [MEM_MAP] >>
     qpat_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
     rw [] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      tenv'` >>
     rw [] >-
         (mp_tac (Q.SPECL [`num_tvs tenvE1 + LENGTH (targs:t list)`, 
                           `tenvC:tenvC`,
                           `x0`,
                           `Texn`,
                           `tenv'`] (hd (CONJUNCTS type_p_subst))) >>
          rw [] >>
          metis_tac [deBruijn_subst_def, MAP, Texn_def]) >>
     pop_assum (MATCH_MP_TAC o 
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                      db_merge_bind_var_list] o
                Q.SPECL [`bind_var_list 0 tenv' tenvE1`, `targs`, `tvs`]) >>
     rw [] >>
     match_mp_tac tenv_ok_bind_var_list >>
     rw [num_tvs_db_merge, bind_tvar_rewrites] >>
     metis_tac [type_p_freevars],
 fs [EVERY_MAP, EVERY_MEM] >>
     rw [] >>
     metis_tac [check_freevars_lem, EVERY_MEM],
 metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup],
 metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup],
 cases_on `n` >>
     fs [t_lookup_var_id_def] >|
     [imp_res_tac lookup_tenv_freevars >>
          fs [lookup_tenv_db_merge] >>
          cases_on `lookup_tenv a 0 tenvE1` >>
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
               fs [nil_deBruijn_inc] >>
               qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)` >>
               rw [] >-
               metis_tac [deBruijn_subst2] >>
               fs [EVERY_MAP, EVERY_MEM, MEM_MAP] >>
               rw [] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM],
           imp_res_tac lookup_tenv_deBruijn_subst_tenvE >>
               fs [] >>
               rw [] >>
               fs [nil_deBruijn_subst, num_tvs_db_merge, bind_tvar_rewrites] >>
               fs [EVERY_MAP, EVERY_MEM] >>
               rw [] >>
               qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)`  >>
               rw [] >>
               fs [MEM_MAP] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM, type_e_subst_lem7]],
      cases_on `lookup s tenvM` >>
          fs [] >>
          rw [] >>
          qexists_tac `MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs` >>
          rw [] >|
          [match_mp_tac (hd (CONJUNCTS deBruijn_subst2)) >>
               rw [] >>
               metis_tac [tenvM_ok_lookup, lookup_freevars, arithmeticTheory.ADD, arithmeticTheory.ADD_0],
           fs [EVERY_MAP, EVERY_MEM] >>
               rw [] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM]]],
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
     qpat_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
     rw [] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      tenv'` >>
     rw [] >-
     metis_tac [type_p_subst] >>
     pop_assum (MATCH_MP_TAC o 
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                      db_merge_bind_var_list] o
                Q.SPECL [`bind_var_list 0 tenv' tenvE1`, `targs`, `tvs`]) >>
     rw [] >>
     match_mp_tac tenv_ok_bind_var_list >>
     rw [num_tvs_db_merge, bind_tvar_rewrites] >>
     metis_tac [type_p_freevars],
 disj1_tac >>
     rw [] >>
     qexists_tac `deBruijn_subst (tvs + num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs) t` >>
     qexists_tac `tvs` >>
     rw [] >|
     [qpat_assum `∀tenvE1' targs' tvs''.
                     EVERY (check_freevars tvs'' []) targs' ∧
                     (bind_tvar tvs
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvM tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       e
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
                     type_e tenvM tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       e'
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
     qexists_tac `deBruijn_subst (num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     fs [deBruijn_inc0] >>
     rw [] >>
     qpat_assum `∀tenvE1' targs' tvs'.
                     check_freevars (skip' + LENGTH targs) [] t ∧
                     EVERY (check_freevars tvs' []) targs' ∧
                     (Bind_name n 0 t
                        (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                      db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
                     type_e tenvM tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs' tenvE2))
                       e'
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t')`
                 (MP_TAC o 
                  Q.SPECL [`Bind_name n 0 t tenvE1`, `targs`, `tvs`]) >>
     rw [bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, 
         num_tvs_def] >>
     imp_res_tac type_e_freevars >>
     fs [tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge] >>
     metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM],
 qexists_tac `MAP (λ(x,t').
                 (x,
                  deBruijn_subst (tvs + num_tvs tenvE1)
                    (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs)
                    t')) env` >>
     qexists_tac `tvs` >>
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
                     type_funs tenvM tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       funs
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
          pop_assum match_mp_tac >>
          match_mp_tac tenv_ok_bind_var_list_funs >>
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
                     type_e tenvM tenvC
                       (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                          (bind_tvar tvs'' tenvE2))
                       e
                       (deBruijn_subst (num_tvs tenvE1')
                          (MAP (deBruijn_inc 0 (num_tvs tenvE1')) targs') t)`
                 (MP_TAC o 
                  Q.SPECL [`bind_var_list tvs env tenvE1`, `targs`, `tvs'`]) >>
          rw [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list, db_merge_bind_var_list] >>
          pop_assum match_mp_tac >>
          match_mp_tac tenv_ok_bind_var_list_tvs >>
          metis_tac []],
 fs [check_freevars_def] >>
     qpat_assum `∀tenvE1' targs' tvs'.
               check_freevars (num_tvs tenvE1 + LENGTH targs) [] t1 ∧
               EVERY (check_freevars tvs' []) targs' ∧
               (Bind_name n 0 t1
                  (db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2)) =
                db_merge tenvE1' (bind_tvar (LENGTH targs') tenvE2)) ⇒
               type_e tenvM tenvC
                 (db_merge (deBruijn_subst_tenvE targs' tenvE1')
                    (bind_tvar tvs' tenvE2))
                 e
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
          metis_tac [mem_exists_set]]]);

(* Recursive functions have function type *)
val type_funs_Tfn = Q.store_thm ("type_funs_Tfn",
`∀tenvM tenvC tenv funs tenv' tvs t n.
  type_funs tenvM tenvC tenv funs tenv' ∧
  (lookup n tenv' = SOME t)
  ⇒
  ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenv) [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs tenvM tenvC tenv funspat tenv'`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
rw [] >>
fs [lookup_def, emp_def, bind_def] >>
cases_on `fn = n` >>
fs [deBruijn_subst_def, check_freevars_def] >>
metis_tac [type_e_freevars, bind_tenv_def, num_tvs_def]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.store_thm ("type_funs_lookup",
`∀fn env tenvM tenvC funs env' n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenvM tenvC tenv funs env'
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
`∀fn env tenvM tenvC funs tenv' e tenv t.
  (lookup fn tenv' = SOME t) ∧
  type_funs tenvM tenvC tenv funs tenv'
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
`∀fn funs n e tenvM tenvC tenv tenv' tvs t1 t2.
  (find_recfun fn funs = SOME (n,e)) ∧
  type_funs tenvM tenvC tenv funs tenv' ∧
  (lookup fn tenv' = SOME (Tfn t1 t2))
  ⇒
  type_e tenvM tenvC (bind_tenv n 0 t1 tenv) e t2 ∧
  check_freevars (num_tvs tenv) [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [Once find_recfun_def] >>
qpat_assum `type_funs tenvM tenvC tenv (h::funs) tenv'`
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
`∀tenvM tenvC tenv funs tenv'.
  type_funs tenvM tenvC tenv funs tenv'
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs)`,
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

val type_funs_tenv_ok = Q.store_thm ("type_funs_tenv_ok",
`!funs tenvM tenvC env tenvE tvs env'.
  (num_tvs tenvE = 0) ∧
  type_funs tenvM tenvC (bind_var_list 0 env' (bind_tvar tvs tenvE)) funs env
  ⇒
  tenv_ok (bind_var_list tvs env Empty)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [check_freevars_def, bind_tenv_def, bind_var_list_def, tenv_ok_def] >>
cases_on `tvs = 0` >>
fs [check_freevars_def, num_tvs_bind_var_list, bind_tvar_def, num_tvs_def] >>
metis_tac [arithmeticTheory.ADD_0]);

(* ---------- tid_exn_to_tc ---------- *)

val tid_exn_to_tc_11 = Q.store_thm ("tid_exn_to_tc_11",
`!x y. (tid_exn_to_tc x = tid_exn_to_tc y) = same_tid x y`,
cases_on `x` >>
cases_on `y` >>
rw [tid_exn_to_tc_def, same_tid_def]);

(* ---------- ctMap stuff ---------- *)
(* flat_tenvC_ok, ctMap_ok, flat_to_ctMap_list, to_ctMap_list, flat_to_ctMap,
 * to_ctMap, ctMap_to_mods, tenvC_to_types *)

val ctMap_ok_merge_imp = Q.store_thm ("ctMap_ok_merge_imp",
`!tenvC1 tenvC2.
  (ctMap_ok tenvC1 ∧ ctMap_ok tenvC2) ⇒
  ctMap_ok (FUNION tenvC1 tenvC2)`,
 rw [ctMap_ok_def] >>
 metis_tac [fevery_funion]);

val ctMap_ok_lookup = Q.store_thm ("ctMap_ok_lookup",
`!ctMap cn tvs ts tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap (cn,tn) = SOME (tvs,ts))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 rw [ctMap_ok_def, FEVERY_ALL_FLOOKUP] >>
 res_tac >>
 fs []);

val tenvC_ok_ctMap = Q.store_thm ("tenvC_ok_ctMap",
`!tenvC. tenvC_ok tenvC ⇒ ctMap_ok (to_ctMap tenvC)`,
 rw [to_ctMap_list_def, flat_to_ctMap_list_def, to_ctMap_def, EVERY_MEM, tenvC_ok_def, 
     flookup_fupdate_list, ctMap_ok_def, FEVERY_ALL_FLOOKUP] >>
 rw [] >>
 `?cn tn tvs ts. k = (cn,tn) ∧ v = (tvs,ts)` 
              by metis_tac [pair_CASES] >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 fs [REVERSE_APPEND, ALOOKUP_APPEND] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 PairCases_on `tenvC` >>
 fs [tenvC_ok_def] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_REVERSE, MEM_FLAT, MEM_MAP]
 >- (fs [EVERY_MEM, flat_tenvC_ok_def] >>
     rw [] >>
     PairCases_on `y` >>
     fs [MEM_MAP] >>
     rw [] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     res_tac >>
     fs [])
 >- (PairCases_on `y` >>
     fs [EVERY_MEM, flat_tenvC_ok_def] >>
     res_tac >>
     fs [])); 

val flat_to_ctMap_lookup_none = Q.prove (
`!cn flat_tenvC.
  (lookup cn flat_tenvC = NONE)
  ⇒
  !t. (FLOOKUP (flat_to_ctMap flat_tenvC) (cn,t) = NONE)`,
 rw [flat_to_ctMap_def, flookup_fupdate_list] >>
 every_case_tac >>
 rw [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_REVERSE, flat_to_ctMap_list_def, MEM_MAP, lookup_notin] >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 metis_tac [FST]);

val flat_to_ctMap_lookup_not_none = Q.prove (
`!cn flat_tenvC tvs ts t.
  lookup cn flat_tenvC = SOME (tvs,ts,t)
  ⇒
  FLOOKUP (flat_to_ctMap flat_tenvC) (cn,t) ≠ NONE`,
 rw [flat_to_ctMap_def, flookup_fupdate_list] >>
 every_case_tac >>
 rw [] >>
 fs [ALOOKUP_NONE, MEM_MAP, flat_to_ctMap_list_def] >>
 induct_on `flat_tenvC` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 rw []
 >- (qexists_tac `((cn,h3), (h1, h2))` >>
     rw [] >>
     qexists_tac `(cn,h1,h2,h3)` >>
     rw [])
 >- metis_tac []);

val to_ctMap_lookup = Q.prove (
`!cn tenvC tvs ts t x.
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list tenvC)) ∧
  lookup cn tenvC = SOME (tvs,ts,t) ∧
  FLOOKUP (flat_to_ctMap tenvC) (cn,t) = SOME x
  ⇒
  x = (tvs,ts)`,
 rw [flat_to_ctMap_def, flat_to_ctMap_list_def, flookup_fupdate_list] >>
 every_case_tac >>
 imp_res_tac alookup_distinct_reverse >>
 fs [] >>
 rw [] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum mp_tac >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 induct_on `tenvC` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 fs [] >>
 rw []);

val tenvC_to_types_def = Define `
tenvC_to_types tenvC =
  set (MAP (\(cn,tvs,ts,tn). (cn,tn)) (SND tenvC)) ∪
  BIGUNION (set (MAP (\(mn, tenvC). set (MAP (\(cn,tvs,ts,tn). (cn,tn)) tenvC)) (FST tenvC)))`;

val to_ctMap_to_types_thm = Q.store_thm ("to_ctMap_to_types_thm",
`!tenvC. tenvC_to_types tenvC = FDOM (to_ctMap tenvC)`,
 rw [tenvC_to_types_def] >>
 PairCases_on `tenvC` >>
 rw [flat_to_ctMap_list_def, EXTENSION, to_ctMap_list_def, to_ctMap_def] >>
 eq_tac >>
 rw [FDOM_FUPDATE_LIST, MEM_MAP, MEM_FLAT]
 >- (fs [MEM_FLAT, MEM_MAP] >>
     rw [] >>
     PairCases_on `y` >>
     rw [EXISTS_PROD] >>
     metis_tac [])
 >- (PairCases_on `y` >>
     fs [MEM_MAP] >>
     PairCases_on `y` >>
     fs [] >>
     qexists_tac `((y0',y3), (y1',y2))` >>
     rw [] >>
     disj2_tac >>
     qexists_tac `MAP (\(a,b,c,d).((a, d), b, c)) y1` >>
     rw [MEM_MAP]
     >- (qexists_tac `(y0,y1)` >>
         rw [])
     >- (qexists_tac `(y0',y1',y2,y3)` >>
         rw []))
 >- (disj1_tac >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     qexists_tac `(y'0,y'1,y'2,y'3)` >>
     rw [])
 >- (disj2_tac >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     PairCases_on `y'` >>
     fs [] >>
     qexists_tac `set (MAP FST (flat_to_ctMap_list y'1))` >>
     rw [flat_to_ctMap_list_def, MEM_MAP]
     >- (qexists_tac `((y'0', y'3), (y'1',y'2))` >>
         rw [] >>
         qexists_tac `(y'0',y'1',y'2,y'3)` >>
         rw [])
     >- (qexists_tac `(y'0,y'1)` >>
         rw [EXTENSION, MEM_MAP] >>
         eq_tac >>
         rw []
         >- (qexists_tac `y'` >>
             fs [] >>
             PairCases_on `y'` >>
             fs [])
         >- (PairCases_on `y` >>
             fs [] >>
             qexists_tac `((y0,y3), (y1,y2))` >>
             rw [] >>
             qexists_tac `(y0,y1,y2,y3)` >>
             rw []))));

val flat_to_ctMap_list_append = Q.store_thm ("flat_to_ctMap_list_append",
`!tenvC1 tenvC2. flat_to_ctMap_list (tenvC1 ++ tenvC2) = flat_to_ctMap_list tenvC1 ++ flat_to_ctMap_list tenvC2`,
rw [flat_to_ctMap_list_def]);

(* ---------- type_v, type_vs, type_env, consistent_mod_env ---------- *)


(* ---------- constructor checking stuff ---------- *)
(* check_new_type, check_ctor_tenv, build_ctor_tenv, check_new_exn,
 * check_exn_tenv *)

val lookup_ctor_none_lem = Q.prove (
`!x h0 h1 h2 h3.
  (lookup x (MAP (λ(cn,ts). (cn,h0,ts,TypeId (mk_id mn h1))) h2) = NONE)
  = 
  (lookup x (MAP (λ(conN,ts). (conN,LENGTH ts,TypeId (mk_id mn h3))) h2) = NONE)`,
induct_on `h2` >>
rw [lookup_def] >>
PairCases_on `h` >>
rw [lookup_def]);

val lookup_ctor_none = Q.store_thm ("lookup_ctor_none",
`!tds tenvC envC x.
  !x. (lookup x (build_ctor_tenv mn tds) = NONE) =
      (lookup x (build_tdefs mn tds) = NONE)`,
 Induct >>
 rw [] >-
 fs [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
 rw [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
 PairCases_on `h` >>
 rw [lookup_append_none] >>
 eq_tac >>
 rw []
 >- metis_tac [lookup_ctor_none_lem]
 >- metis_tac [build_ctor_tenv_def, build_tdefs_def, lookup_reverse_none]
 >- metis_tac [lookup_ctor_none_lem]
 >- metis_tac [build_ctor_tenv_def, build_tdefs_def, lookup_reverse_none]);

val build_tdefs_cons = Q.prove (
`!tvs tn ctors tds.
  build_tdefs mn ((tvs,tn,ctors)::tds) =
    (MAP (\(conN,ts). (conN, LENGTH ts, TypeId (mk_id mn tn)))
        ctors) ++ build_tdefs mn tds`,
rw [build_tdefs_def]);

val build_ctor_tenv_cons = Q.prove (
`∀tvs tn ctors tds.
  build_ctor_tenv mn ((tvs,tn,ctors)::tds) =
    (MAP (λ(cn,ts). (cn,tvs,ts,TypeId (mk_id mn tn))) ctors ++ build_ctor_tenv mn tds)`,
rw [build_ctor_tenv_def]);

val build_ctor_tenv_empty = Q.store_thm ("build_ctor_tenv_empty",
`build_ctor_tenv mn [] = []`,
rw [build_ctor_tenv_def]);

val check_ctor_foldr_flat_map = Q.prove (
`!c. (FOLDR
         (λ(tvs,tn,condefs) x2.
            FOLDR (λ(n,ts) x2. n::x2) x2 condefs) [] c)
    =
    FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) c)`,
induct_on `c` >>
rw [LET_THM] >>
PairCases_on `h` >>
fs [LET_THM] >>
pop_assum (fn _ => all_tac) >>
induct_on `h2` >>
rw [] >>
PairCases_on `h` >>
rw []);

val check_dup_ctors_thm = Q.store_thm ("check_dup_ctors_thm",
`!tds.
  check_dup_ctors tds =
    ALL_DISTINCT (FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) tds))`,
metis_tac [check_dup_ctors_def,check_ctor_foldr_flat_map]);

val check_ctor_tenvC_ok = Q.store_thm ("check_ctor_tenvC_ok",
`!mn tenvC c. check_ctor_tenv mn tenvC c ⇒ flat_tenvC_ok (build_ctor_tenv mn c)`,
 rw [build_ctor_tenv_def, tenvC_ok_def, flat_tenvC_ok_def] >>
 fs [check_ctor_tenv_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
 rw [] >>
 PairCases_on `y` >>
 fs [MEM_MAP] >>
 rw [] >>
 PairCases_on `y` >>
 rw [] >>
 res_tac >>
 fs [] >>
 res_tac >>
 fs []);

val check_dup_ctors_cons = Q.store_thm ("check_dup_ctors_cons",
`!tvs ts ctors tds.
  check_dup_ctors ((tvs,ts,ctors)::tds)
  ⇒
  check_dup_ctors tds`,
induct_on `tds` >>
rw [check_dup_ctors_def, LET_THM, RES_FORALL] >>
PairCases_on `h` >>
fs [] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
rw [] >>
PairCases_on `h` >>
fs []);

val check_ctor_tenv_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_ctor_tenv mn tenvC ((tvs,ts,ctors)::tds) ⇒
  check_ctor_tenv mn tenvC tds`,
 rw [] >>
 fs [check_ctor_tenv_def] >>
 metis_tac [check_dup_ctors_cons]);

val check_ctor_tenv_dups = Q.store_thm ("check_ctor_tenv_dups",
`!mn tenvC tdecs. check_ctor_tenv mn tenvC tdecs ⇒ check_dup_ctors tdecs`,
 induct_on `tdecs` >>
 rw [check_dup_ctors_def, LET_THM] >>
 PairCases_on `h` >>
 imp_res_tac check_ctor_tenv_cons >>
 res_tac >>
 rw [] >>
 fs [check_ctor_tenv_def, check_dup_ctors_def, LET_THM]);

val check_ctor_ctMap_ok = Q.store_thm ("check_ctor_ctMap_ok",
`!mn tenvC c. check_ctor_tenv mn tenvC c ⇒ ctMap_ok (flat_to_ctMap (build_ctor_tenv mn c))`,
 rw [] >>
 imp_res_tac check_ctor_tenvC_ok >>
 fs [flat_tenvC_ok_def, ctMap_ok_def, EVERY_MEM, flat_to_ctMap_def, MEM_MAP] >>
 rw [FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 fs [flat_to_ctMap_list_def, MEM_MAP] >>
 res_tac >>
 PairCases_on `y` >>
 fs []);

val ctor_env_to_tdefs = Q.prove (
`!mn tds cn n t tvs ts.
  (lookup cn (build_ctor_tenv mn tds) = SOME (tvs,ts,t))
  ⇒
  (lookup cn (build_tdefs mn tds) = SOME (LENGTH ts,t))`,
 induct_on `tds` >>
 rw [build_ctor_tenv_empty] >>
 PairCases_on `h` >>
 fs [build_ctor_tenv_cons, build_tdefs_cons] >>
 fs [lookup_append] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 induct_on `h2` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 rw []);

val check_new_type_thm = Q.store_thm ("check_new_type_thm",
`!id tenvC. check_new_type id tenvC ⇔ TypeId id ∉ IMAGE SND (tenvC_to_types tenvC)`,
 rw [] >>
 PairCases_on `tenvC` >>
 fs [check_new_type_def, tenvC_to_types_def] >>
 eq_tac
 >- (rw [EVERY_MEM, MEM_MAP] >>
     CCONTR_TAC >>
     fs [] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     fs [MEM_MAP] >>
     rw [] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [])
 >- (rw [EVERY_MEM] >>
     PairCases_on `p` >>
     fs [] >>
     rw [] >>
     TRY (PairCases_on `p`) >>
     rw [] >>
     CCONTR_TAC >>
     fs [MEM_MAP] >>
     rw [] >>
     fs [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``] >>
     res_tac >>
     fs [MEM_MAP, FORALL_PROD] >>
     fs [MEM_MAP, FORALL_PROD, EXISTS_PROD]
     >- metis_tac [] >>
     FIRST_X_ASSUM (mp_tac o Q.SPEC `p0'`) >>
     rw [] >>
     disj1_tac >>
     qexists_tac `set (MAP (λ(cn,tvs,ts,tn). (cn,tn)) p1)` >>
     rw [MEM_MAP]
     >- metis_tac [] >>
     qexists_tac `(p0',p1',p2,TypeId id)` >>
     rw []));

val check_new_exn_thm = Q.store_thm ("check_new_exn_thm",
`!mn cn tenvC. check_new_exn mn cn tenvC ⇔ (cn,TypeExn mn) ∉ tenvC_to_types tenvC`,
 rw [] >>
 PairCases_on `tenvC` >>
 fs [check_new_exn_def, tenvC_to_types_def] >>
 eq_tac
 >- (rw [EVERY_MEM, MEM_MAP] >>
     CCONTR_TAC >>
     fs [] >>
     PairCases_on `y` >>
     fs [MEM_MAP] >>
     rw [] >>
     res_tac >>
     fs [] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [])
 >- (rw [EVERY_MEM] >>
     PairCases_on `p` >>
     fs [] >>
     CCONTR_TAC >>
     fs [MEM_MAP] >>
     rw [] >>
     fs [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``] >>
     res_tac >>
     fs [] >>
     fs [MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     metis_tac []));

val check_ctor_disjoint_env = Q.store_thm ("check_ctor_disjoint_env",
`!mn tenvC tds.
  check_ctor_tenv mn tenvC tds
  ⇒
  DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn tds))) (FDOM (to_ctMap tenvC))`,
 rw [check_ctor_tenv_def, DISJOINT_DEF, EVERY_MEM,
     check_new_type_thm, EXTENSION, MEM_MAP, to_ctMap_to_types_thm] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 fs [FDOM_FUPDATE_LIST, flat_to_ctMap_list_def, flat_to_ctMap_def, build_ctor_tenv_def, MEM_MAP, MEM_FLAT] >>
 rw [] >>
 PairCases_on `y'` >>
 fs [MEM_MAP] >>
 rw [] >>
 res_tac >>
 fs [] >>
 PairCases_on `y''` >>
 fs [MEM_MAP] >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 pop_assum (fn _ => all_tac) >>
 FIRST_X_ASSUM (mp_tac o Q.SPEC `(y'0,TypeId (mk_id mn y''1))`) >>
 rw [EXISTS_PROD]);

val check_exn_tenv_disjoint = Q.store_thm ("check_exn_tenv_disjoint",
`!tvs tenvC cn ts.
  check_exn_tenv tvs tenvC cn ts
  ⇒
  DISJOINT (FDOM (flat_to_ctMap (bind cn ([]:tvarN list,ts,TypeExn tvs) emp))) (FDOM (to_ctMap tenvC))`,
 rw [FDOM_FUPDATE_LIST, bind_def, DISJOINT_DEF,EXTENSION, MEM_MAP, flat_to_ctMap_def] >>
 fs [flat_to_ctMap_list_def, check_exn_tenv_def, check_new_exn_thm, to_ctMap_to_types_thm] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 fs [MEM_MAP] >>
 rw [] >>
 PairCases_on `y'` >>
 fs [emp_def]);

val check_dup_ctors_distinct = Q.prove (
`!tds mn.
  check_dup_ctors tds ⇒ ALL_DISTINCT (MAP FST (flat_to_ctMap_list (build_ctor_tenv mn tds)))`,
 induct_on `tds` >>
 rw [check_dup_ctors_thm, build_ctor_tenv_def, flat_to_ctMap_list_def,
     ALL_DISTINCT_APPEND] >>
 fs [flat_to_ctMap_list_def, build_ctor_tenv_def, check_dup_ctors_thm, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
 rw [] >>
 PairCases_on `h` >>
 fs [MAP_FLAT, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF]
 >- (induct_on `h2` >>
    rw [] >>
    PairCases_on `h` >>
    fs [MEM_FLAT, MEM_MAP] >>
    rw [] >>
    PairCases_on `x` >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    rw [] >>
    LAST_X_ASSUM (mp_tac o Q.SPEC `(h0',x1)`) >>
    rw [])
 >- (rw [] >>
     PairCases_on `y` >>
     fs [] >>
     res_tac >>
     fs [MEM_FLAT, MEM_MAP] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     rw [] >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     rw [] >>
     FIRST_X_ASSUM (mp_tac o Q.SPEC `MAP FST (y'2:(β, γ) alist)`) >>
     rw [MEM_MAP]
     >- (qexists_tac `(y'0,y'1,y'2)` >>
         rw [FST_pair])
     >- metis_tac [FST]));

(* ---------- consistent_con_env ---------- *)

val extend_consistent_con = Q.store_thm ("extend_consistent_con",
`!envC tenvC tds.
  check_ctor_tenv mn tenvC tds ∧
  consistent_con_env (to_ctMap tenvC) envC tenvC
  ⇒
  consistent_con_env (FUNION (flat_to_ctMap (build_ctor_tenv mn tds)) (to_ctMap tenvC))
                     (merge_envC (emp,build_tdefs mn tds) envC)
                     (merge_tenvC (emp, build_ctor_tenv mn tds) tenvC)`,
 rw [consistent_con_env_def, lookup_append, tenvC_ok_merge, lookup_con_id_merge_emp]
 >- (rw [tenvC_ok_def, emp_def] >>
     metis_tac [check_ctor_tenvC_ok])
 >- metis_tac [check_ctor_ctMap_ok, ctMap_ok_merge_imp]
 >- (fs [lookup_con_id_def, emp_def] >>
     every_case_tac >>
     fs [id_to_n_def] >>
     imp_res_tac ctor_env_to_tdefs >>
     fs [GSYM lookup_ctor_none] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     fs [lookup_ctor_none, FLOOKUP_FUNION] >>
     every_case_tac >>
     fs []
     >- metis_tac [NOT_SOME_NONE, flat_to_ctMap_lookup_none, lookup_ctor_none]
     >- (PairCases_on `x` >>
         imp_res_tac ctor_env_to_tdefs  >>
         fs [] >>
         rw [] >>
         imp_res_tac check_ctor_tenv_dups >>
         imp_res_tac flat_to_ctMap_lookup_not_none >>
         metis_tac [pair_CASES, to_ctMap_lookup, check_dup_ctors_distinct,
                    option_nchotomy])
     >- (PairCases_on `x` >>
         imp_res_tac ctor_env_to_tdefs  >>
          fs [] >>
         rw [] >>
         imp_res_tac check_ctor_tenv_dups >>
         metis_tac [pair_CASES, to_ctMap_lookup, check_dup_ctors_distinct])
     >- (res_tac >>
         fs [lookup_append] >>
         rw [] >>
         imp_res_tac check_ctor_disjoint_env >>
         fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
         metis_tac []))
 >- (fs [lookup_con_id_def, emp_def] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     metis_tac [NOT_SOME_NONE, pair_CASES,ctor_env_to_tdefs]));

val extend_consistent_con_exn = Q.store_thm ("extend_consistent_con_exn",
`∀mn tenvC cn ts cenv.
  check_exn_tenv mn tenvC cn ts ∧
  consistent_con_env (to_ctMap tenvC) cenv tenvC
  ⇒
  consistent_con_env (FUNION (flat_to_ctMap (bind cn ([],ts,TypeExn mn) [])) (to_ctMap tenvC))
                     (merge_envC (emp, bind cn (LENGTH ts,TypeExn mn) []) cenv)
                     (merge_tenvC (emp, bind cn ([],ts,TypeExn mn) []) tenvC)`,
 rw [check_exn_tenv_def, consistent_con_env_def, bind_def, FEVERY_ALL_FLOOKUP,
     flat_to_ctMap_def, ctMap_ok_def, tenvC_ok_merge, tenvC_ok_def,
     flat_tenvC_ok_def, lookup_con_id_merge_emp, emp_def] >>
 fs [flookup_fupdate_list, FLOOKUP_FUNION, emp_def, lookup_con_id_def] >>
 every_case_tac >>
 fs [flat_to_ctMap_list_def, id_to_n_def] >>
 rw [merge_def, lookup_append] >>
 res_tac >>
 fs [check_new_exn_thm, to_ctMap_to_types_thm, MEM_MAP, FORALL_PROD]  >>
 PairCases_on `tenvC` >>
 fs [lookup_con_id_def] >>
 every_case_tac >>
 fs [FLOOKUP_DEF]);

(* ---------- type_d ---------- *)

val type_d_tenv_ok = Q.store_thm ("type_d_tenv_ok",
`!tvs tenvM tenvC tenv d tenvC' tenv' tenvM'' tenvC''.
  type_d tvs tenvM tenvC tenv d tenvC' tenv' ∧
  (num_tvs tenv = 0)
  ⇒
  tenv_ok (bind_var_list2 tenv' Empty)`,
rw [type_d_cases] >>
`tenv_ok Empty` by rw [tenv_ok_def] >>
imp_res_tac type_p_bvl >>
rw [bvl2_to_bvl] >|
[metis_tac [type_funs_tenv_ok],
 rw [bind_var_list2_def, emp_def, tenv_ok_def],
 rw [bind_var_list2_def, emp_def, tenv_ok_def]]);

val type_d_ctMap_ok = Q.store_thm ("type_d_ctMap_ok",
`!tvs tenvM tenvC tenv d tenvC' tenv' tenvM'' tenvC''.
  type_d tvs tenvM tenvC tenv d tenvC' tenv'
  ⇒
  ctMap_ok (flat_to_ctMap tenvC') ∧
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list tenvC')) ∧
  DISJOINT (FDOM (to_ctMap tenvC)) (FDOM (flat_to_ctMap tenvC'))`,
 rw [type_d_cases, flat_to_ctMap_def, flat_to_ctMap_list_def] >>
 imp_res_tac type_p_bvl >>
 rw [bvl2_to_bvl] >>
 imp_res_tac check_ctor_ctMap_ok >>
 fs [ctMap_ok_def, FDOM_FUPDATE_LIST, emp_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
 rw [] >>
 every_case_tac >>
 fs [flat_to_ctMap_def, flat_to_ctMap_list_def, flookup_fupdate_list] >>
 rw []
 >- (imp_res_tac check_ctor_tenv_dups >>
     imp_res_tac check_dup_ctors_distinct >>
     fs [flat_to_ctMap_list_def])
 >- (imp_res_tac check_ctor_disjoint_env >>
     fs [FDOM_FUPDATE_LIST, flat_to_ctMap_def, flat_to_ctMap_list_def] >>
     metis_tac [DISJOINT_SYM])
 >- (fs [bind_def, check_exn_tenv_def] >>
     rw [])
 >- fs [bind_def]
 >- (imp_res_tac check_exn_tenv_disjoint >>
     fs [FDOM_FUPDATE_LIST, flat_to_ctMap_def, flat_to_ctMap_list_def] >>
     metis_tac [emp_def,DISJOINT_SYM]));

(* ---------- type_ds ---------- *)

val type_ds_tenv_ok = Q.store_thm ("type_ds_tenv_ok",
`!tvs tenvM tenvC tenv ds tenvC' tenv'.
  type_ds tvs tenvM tenvC tenv ds tenvC' tenv' ⇒
  (num_tvs tenv = 0) ⇒
  tenv_ok (bind_var_list2 tenv' Empty)`,
ho_match_mp_tac type_ds_ind >>
rw [] >|
[rw [bind_var_list2_def, tenv_ok_def, emp_def],
 imp_res_tac type_d_tenv_ok >>
     fs [bvl2_append, merge_def, num_tvs_bvl2] >>
     metis_tac [tenv_ok_bvl2]]);

val type_ds_ctMap_ok = Q.store_thm ("type_ds_ctMap_ok",
`!tvs tenvM tenvC tenv ds tenvC' tenv'.
  type_ds tvs tenvM tenvC tenv ds tenvC' tenv' ⇒
  ctMap_ok (flat_to_ctMap tenvC') ∧
  DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM (to_ctMap tenvC)) ∧
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list tenvC'))`,
 ho_match_mp_tac type_ds_ind >>
 rw []
 >- rw [ctMap_ok_def, emp_def, flat_to_ctMap_def, flat_to_ctMap_list_def,
        FEVERY_ALL_FLOOKUP, flookup_fupdate_list]
 >- rw [flat_to_ctMap_def, flat_to_ctMap_list_def, FDOM_FUPDATE_LIST, emp_def]
 >- rw [flat_to_ctMap_list_def, emp_def]
 >- (imp_res_tac type_d_ctMap_ok >>
     fs [merge_def, flat_to_ctMap_def] >>
     fs [ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     fs [flat_to_ctMap_list_def, ALOOKUP_APPEND, REVERSE_APPEND] >>
     every_case_tac >>
     fs [])
 >- (imp_res_tac type_d_ctMap_ok >>
     fs [merge_def, flat_to_ctMap_def] >>
     fs [num_tvs_bvl2, merge_def, DISJOINT_DEF, EXTENSION] >>
     rw [] >>
     PairCases_on `tenvC` >>
     fs [flat_to_ctMap_def, merge_tenvC_def, merge_def, emp_def, to_ctMap_def,
         REVERSE_APPEND, flat_to_ctMap_list_def, FDOM_FUPDATE_LIST, to_ctMap_list_def] >>
     metis_tac [])
 >- (rw [merge_def, flat_to_ctMap_list_append, ALL_DISTINCT_APPEND] >>
     imp_res_tac type_d_ctMap_ok >>
     PairCases_on `tenvC` >>
     fs [merge_tenvC_def, DISJOINT_DEF, EXTENSION, flat_to_ctMap_def,
         to_ctMap_def, MEM_MAP, MEM_REVERSE, FDOM_FUPDATE_LIST,
         to_ctMap_list_def, MEM_FLAT, flat_to_ctMap_list_append, merge_def] >>
     metis_tac []));

(* ---------- type_specs ---------- *)

val type_specs_tenv_ok = Q.store_thm ("type_specs_tenv_ok",
`!tvs tenvC tenv specs tenvC' tenv'.
  type_specs tvs tenvC tenv specs tenvC' tenv' ⇒
  tenv_ok (bind_var_list2 tenv Empty) ⇒
  tenv_ok (bind_var_list2 tenv' Empty)`,
ho_match_mp_tac type_specs_ind >>
rw [bind_var_list2_def, emp_def, tenv_ok_def] >>
qpat_assum `A ⇒ B` match_mp_tac >>
rw [bind_def, bind_var_list2_def, bind_tenv_def, tenv_ok_def, num_tvs_bvl2,
    num_tvs_def] >>
match_mp_tac check_freevars_subst_single >>
rw [rich_listTheory.LENGTH_COUNT_LIST, EVERY_MAP] >>
rw [EVERY_MEM] >>
fs [rich_listTheory.MEM_COUNT_LIST, check_freevars_def] >>
metis_tac [check_freevars_add, DECIDE ``!x:num. x ≥ 0``]);

val _ = export_theory ();
