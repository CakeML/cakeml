(* Theorems about the type system. *)

open preamble rich_listTheory optionTheory;
open miscTheory alistTheory finite_mapTheory;
open libTheory astTheory typeSystemTheory typeSoundInvariantsTheory terminationTheory;
open astPropsTheory;

val _ = new_theory "typeSysProps";

val check_dup_ctors_def = semanticPrimitivesTheory.check_dup_ctors_def;
val build_tdefs_def = semanticPrimitivesTheory.build_tdefs_def;
val find_recfun_def = semanticPrimitivesTheory.find_recfun_def;
val same_tid_def = semanticPrimitivesTheory.same_tid_def;
val lookup_var_id_def = semanticPrimitivesTheory.lookup_var_id_def;
val build_tdefs_cons = evalPropsTheory.build_tdefs_cons;
val check_dup_ctors_cons = evalPropsTheory.check_dup_ctors_cons;
val merge_alist_mod_env_def = semanticPrimitivesTheory.merge_alist_mod_env_def;
val lookup_alist_mod_env_def = semanticPrimitivesTheory.lookup_alist_mod_env_def;

val type_env_cases = List.nth (CONJUNCTS type_v_cases, 2);
val consistent_mod_cases = List.nth (CONJUNCTS type_v_cases, 3);

(* miscellany TODO: reorganise *)

val type_env_list_rel = store_thm("type_env_list_rel",
  ``!ctMap tenvS env tenv.
   type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇔ LIST_REL (λ(x,v1) (y,n,v2). x = y ∧ type_v n ctMap tenvS v1 v2) env tenv``,
  induct_on `env` >>
  rw [] >>
  cases_on `tenv` >>
  rw [bind_var_list2_def] >>
  ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS type_v_cases)))] >>
  rw [bind_var_list2_def] >>
  PairCases_on `h` >>
  fs [bind_var_list2_def, bind_tenv_def] >>
  PairCases_on `h'` >>
  fs [bind_var_list2_def, bind_tenv_def] >>
  metis_tac []);

val type_env_list_rel_append = store_thm("type_env_list_rel_append",
  ``!ctMap tenvS env tenv rest rst.
   type_env ctMap tenvS (env ++ rest) (bind_var_list2 tenv rst) ∧ LENGTH env = LENGTH tenv
     ⇒ LIST_REL (λ(x,v1) (y,n,v2). x = y ∧ type_v n ctMap tenvS v1 v2) env tenv``,
  induct_on `env` >>
  rw [LENGTH_NIL_SYM] >>
  cases_on `tenv` >> fs[] >>
  PairCases_on`h'` >>
  fs [bind_var_list2_def] >>
  PairCases_on`h`>>simp[] >>
  miscLib.rator_x_assum`type_env`mp_tac >>
  simp[Once type_v_cases] >>
  rw[bind_tenv_def] >>
  metis_tac[])

val bind_var_list2_append = store_thm("bind_var_list2_append",
  ``∀l1 l2 g. bind_var_list2 (l1 ++ l2) g = bind_var_list2 l1 (bind_var_list2 l2 g)``,
  Induct >> simp[bind_var_list2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[bind_var_list2_def])

val type_env_length = store_thm("type_env_length",
  ``∀d a b c e f g h.
    type_env a b (c ++ d) (bind_var_list2 e f) ∧
    type_env g h d f ⇒
    LENGTH c = LENGTH e``,
  Induct >> simp[] >- (
    rw[] >>
    pop_assum mp_tac >>
    simp[Once type_v_cases] >>
    rw[] >>
    imp_res_tac type_env_list_rel >>
    fs[LIST_REL_EL_EQN] ) >>
  rw[] >>
  pop_assum mp_tac >>
  simp[Once type_v_cases] >>
  rw[] >>
  qsuff_tac`LENGTH (c ++ [n,v]) = LENGTH (e++[n,tvs,t])` >- simp[] >>
  first_x_assum match_mp_tac >>
  simp[bind_var_list2_append,bind_var_list2_def] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC])

val merge_mod_env_assoc = Q.store_thm ("merge_mod_env_assoc",
`∀env1 env2 env3.
  merge_mod_env env1 (merge_mod_env env2 env3) =
  merge_mod_env (merge_mod_env env1 env2) env3`,
rw [] >>
PairCases_on `env1` >>
PairCases_on `env2` >>
PairCases_on `env3` >>
rw [merge_mod_env_def, FUNION_ASSOC]);


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
  check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t)`,
 recInduct check_freevars_ind >>
 rw [check_freevars_def, type_subst_def, EVERY_MAP]
 >- (every_case_tac >>
     fs [check_freevars_def, ALOOKUP_FAILS]
     >- (imp_res_tac MEM_ZIP >>
         fs [MEM_EL] >>
         metis_tac [])
     >- (imp_res_tac ALOOKUP_MEM >>
         imp_res_tac MEM_ZIP >>
         fs [MEM_EL, EVERY_MEM] >>
         rw [] >>
         metis_tac []))
 >- fs [EVERY_MEM]);

val check_freevars_subst_list = Q.store_thm ("check_freevars_subst_list",
`!dbmax tvs tvs' ts ts'.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars dbmax tvs) ts' ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  EVERY (check_freevars dbmax tvs') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts')`,
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
  (s = alist_to_fmap (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t)`,
 recInduct type_subst_ind >>
 rw [deBruijn_inc_def, type_subst_def, check_freevars_def]
 >- (every_case_tac >>
     fs [deBruijn_inc_def, ALOOKUP_NONE]
     >- (imp_res_tac MEM_ZIP >>
         fs [MEM_MAP, MEM_ZIP, MEM_EL] >>
         metis_tac [FST, pair_CASES])
     >- (imp_res_tac ALOOKUP_MEM >>
         ntac 2 (pop_assum mp_tac) >>
         simp [MEM_MAP, MEM_ZIP, MEM_EL, EL_MAP] >>
         metis_tac [FST])
     >- (pop_assum mp_tac >>
         simp [ALOOKUP_ZIP_MAP_SND]))
 >- (rw [rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     fs [EVERY_MEM] >>
     metis_tac []));

val type_subst_deBruijn_inc_list = Q.store_thm ("type_subst_deBruijn_inc_list",
`!ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts')`,
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
  (s = alist_to_fmap (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) =
   type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t)`,
 recInduct type_subst_ind >>
 rw [deBruijn_subst_def, deBruijn_inc_def, type_subst_def, check_freevars_def]
 >- (every_case_tac >>
     fs [deBruijn_subst_def, deBruijn_inc_def] >>
     ntac 2 (pop_assum mp_tac) >>
     simp [ALOOKUP_ZIP_MAP_SND])
 >- (rw [rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     fs [EVERY_MEM] >>
     metis_tac []));

val type_subst_deBruijn_subst_list = Q.store_thm ("type_subst_deBruijn_subst_list",
`!t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')`,
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

val type_subst_lem1 = 
(GEN_ALL o
 SIMP_RULE (srw_ss()++ARITH_ss) [] o
 Q.SPECL [`[]`, `t`, `0`, `targs`, `tvs`] o
 SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM])
check_freevars_subst_inc

val type_subst_lem3 = Q.prove (
`!skip targs t tvs.
  (skip = 0) ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t 
  ⇒
  check_freevars tvs [] (deBruijn_subst skip targs t)`,
ho_match_mp_tac deBruijn_subst_ind >>
rw [check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
fs [EVERY_MEM, MEM_EL] >>
metis_tac []);

(* ---------- tenvT stuff ---------- *)
(* type_name_subst, check_type_names, tenvT_ok, merge_tenvT *)

val flat_tenvT_ok_lookup = Q.prove (
`!tenvT tn tvs t.
  flat_tenvT_ok tenvT ∧ 
  FLOOKUP tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t`,
 rw [flat_tenvT_ok_def] >>
 imp_res_tac FEVERY_FLOOKUP >>
 fs []);

val tenvT_ok_lookup = Q.store_thm ("tenvT_ok_lookup",
`!tenvT tn tvs t.
  tenvT_ok tenvT ∧ 
  (lookup_mod_env tn tenvT = SOME (tvs,t))
  ⇒
  check_freevars 0 tvs t`,
 Cases_on `tenvT` >>
 rw [lookup_mod_env_def, tenvT_ok_def] >>
 every_case_tac >>
 imp_res_tac flat_tenvT_ok_lookup >>
 fs [] >>
 imp_res_tac FEVERY_FLOOKUP >>
 fs []);

val check_freevars_type_name_subst = Q.store_thm ("check_freevars_type_name_subst",
`!dbmax tvs t tenvT.
  tenvT_ok tenvT ∧
  check_type_names tenvT t ∧
  check_freevars dbmax tvs t
  ⇒
  check_freevars dbmax tvs (type_name_subst tenvT t)`,
 recInduct check_freevars_ind >>
 rw [type_name_subst_def, LET_THM] >>
 every_case_tac >>
 fs [check_type_names_def, check_freevars_def, EVERY_MAP] >>
 fs [EVERY_MEM] >>
 match_mp_tac check_freevars_subst_single >>
 rw [EVERY_MAP] >>
 rw [EVERY_MEM] >>
 imp_res_tac tenvT_ok_lookup >>
 metis_tac [check_freevars_add, numeralTheory.numeral_distrib]);

val flat_tenvT_ok_merge = Q.prove (
`!tenvT1 tenvT2.
  flat_tenvT_ok tenvT1 ∧ flat_tenvT_ok tenvT2
  ⇒
  flat_tenvT_ok (FUNION tenvT1 tenvT2)`,
 rw [flat_tenvT_ok_def, ALL_DISTINCT_APPEND] >>
 rw [DISJOINT_DEF, EXTENSION, fevery_funion]);

val tenvT_ok_merge = Q.store_thm ("tenvT_ok_merge",
`!tenvT1 tenvT2.
  tenvT_ok tenvT1 ∧ tenvT_ok tenvT2
  ⇒
  tenvT_ok (merge_mod_env tenvT1 tenvT2)`,
 rw [] >>
 PairCases_on `tenvT1` >>
 PairCases_on `tenvT2` >>
 rw [tenvT_ok_def, merge_mod_env_def, ALL_DISTINCT_APPEND] >>
 fs [tenvT_ok_def]
 >- (match_mp_tac fevery_funion >>
     fs []) >>
 metis_tac [flat_tenvT_ok_merge]);

(* ---------- tenvC stuff ----------*)
(* lookup_tenvC, flat_tenvC_ok, tenvC_ok *)

val flat_tenvC_ok_merge = Q.prove (
`!tenvC1 tenvC2.
  flat_tenvC_ok (tenvC1 ++ tenvC2) = 
  (flat_tenvC_ok tenvC1 ∧ flat_tenvC_ok tenvC2)`, 
rw [flat_tenvC_ok_def, ALL_DISTINCT_APPEND] >>
eq_tac >>
rw [DISJOINT_DEF, EXTENSION] >>
metis_tac []);

val tenvC_ok_merge = Q.store_thm ("tenvC_ok_merge",
`!tenvC1 tenvC2.
  tenvC_ok (merge_alist_mod_env tenvC1 tenvC2) = 
  (tenvC_ok tenvC1 ∧ tenvC_ok tenvC2)`, 
 rw [] >>
 PairCases_on `tenvC1` >>
 PairCases_on `tenvC2` >>
 rw [tenvC_ok_def, merge_alist_mod_env_def, ALL_DISTINCT_APPEND] >>
 eq_tac >>
 rw [EVERY_MEM] >>
 res_tac >>
 metis_tac [flat_tenvC_ok_merge]);

val flat_tenvC_ok_lookup = Q.prove (
`!tenvC cn tvs ts tn.
  flat_tenvC_ok tenvC ∧ (ALOOKUP tenvC cn = SOME (tvs,ts,tn))
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

val lookup_tenvC_merge_emp = Q.store_thm ("lookup_tenvC_merge_emp",
`(!cn envC1 envC2.
  lookup_alist_mod_env cn (merge_alist_mod_env ([],envC1) envC2) =
    case lookup_alist_mod_env cn ([],envC1) of
       | NONE => lookup_alist_mod_env cn envC2
       | SOME v => SOME v) ∧
 (!cn envC1 envC2.
  lookup_alist_mod_env cn (merge_alist_mod_env ([],envC1) envC2) =
    case lookup_alist_mod_env cn ([],envC1) of
       | NONE => lookup_alist_mod_env cn envC2
       | SOME v => SOME v)`,
 rw [] >>
 PairCases_on `envC2` >>
 cases_on `cn` >>
 fs [lookup_alist_mod_env_def, merge_alist_mod_env_def] >>
 every_case_tac >>
 fs [ALOOKUP_APPEND]);

val tenvC_ok_lookup = Q.store_thm ("tenvC_ok_lookup",
`!tenvC cn tvs ts tn.
  tenvC_ok tenvC ∧ (lookup_alist_mod_env cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 cases_on `cn` >>
 rw [] >>
 PairCases_on `tenvC` >>
 fs [lookup_alist_mod_env_def, tenvC_ok_def]
 >- metis_tac [flat_tenvC_ok_lookup] >> 
 every_case_tac >>
 fs [] >>
 imp_res_tac flat_tenvC_ok_lookup >>
 imp_res_tac ALOOKUP_MEM >>
 fs [EVERY_MEM] >>
 rw [] >>
 res_tac >>
 fs []);

val merge_tenvC_empty_assoc = Q.store_thm ("merge_tenvC_empty_assoc",
`!tenvC1 tenvC2 tenvC3.
  merge_alist_mod_env ([],tenvC1) (merge_alist_mod_env ([],tenvC2) tenvC3)
  =
  merge_alist_mod_env ([],tenvC1++tenvC2) tenvC3`,
 rw [] >>
 PairCases_on `tenvC3` >>
 rw [merge_alist_mod_env_def]);

val merge_tenvC_empty = Q.store_thm ("merge_tenvC_empty",
`(!tenvC. merge_alist_mod_env ([],[]) tenvC = tenvC)`,
 rw [] >>
 TRY (PairCases_on `envC`) >>
 TRY (PairCases_on `tenvC`) >>
 rw [merge_alist_mod_env_def]);

val lookup_tenvC_mod_cons = Q.store_thm ("lookup_tenvC_mod_cons",
`!mn cn mn' flat_envC1 envC1 flat_envC2.
  lookup_alist_mod_env (Long mn cn) ((mn',flat_envC1)::envC1,flat_envC2) =
  if mn = mn' then
    ALOOKUP flat_envC1 cn
  else
    lookup_alist_mod_env (Long mn cn) (envC1,flat_envC2)`,
rw [lookup_alist_mod_env_def]);

val merge_tenvC_assoc = Q.store_thm ("merge_tenvC_assoc",
`∀tenvC1 tenvC2 tenvC3.
  merge_alist_mod_env tenvC1 (merge_alist_mod_env tenvC2 tenvC3) =
  merge_alist_mod_env (merge_alist_mod_env tenvC1 tenvC2) tenvC3`,
rw [] >>
PairCases_on `tenvC1` >>
PairCases_on `tenvC2` >>
PairCases_on `tenvC3` >>
rw [merge_alist_mod_env_def])

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
  (ALOOKUP tenv n = SOME (tvs, t))
  ⇒
  check_freevars tvs [] t`,
induct_on `tenv` >>
rw [] >>
PairCases_on `h` >>
fs [bind_var_list2_def, tenv_ok_def, bind_tenv_def] >>
every_case_tac >>
fs [] >>
metis_tac [num_tvs_bvl2, arithmeticTheory.ADD_0, num_tvs_def]);

val type_e_freevars_lem3 = Q.prove (
`!tenv tenv' targs n t inc.
  EVERY (check_freevars (num_tvs tenv') []) targs ∧
  (ALOOKUP tenv n = SOME (LENGTH targs,t)) ∧
  tenv_ok (bind_var_list2 tenv Empty)
  ⇒ 
  check_freevars (num_tvs tenv') [] (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
rw [tenv_ok_def, bind_var_list2_def] >>
PairCases_on `h` >>
rw [] >>
fs [tenv_ok_def, bind_var_list2_def, bind_tenv_def] >>
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

val lookup_tenv_inc = Q.store_thm ("lookup_tenv_inc",
`!x inc tenv tvs t inc2.
  (lookup_tenv x inc tenv = SOME (tvs,t))
  ⇒
  (lookup_tenv x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t))`,
induct_on `tenv` >>
rw [lookup_tenv_def] >>
rw [deBruijn_inc_deBruijn_inc] >>
metis_tac [arithmeticTheory.ADD_ASSOC]);

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

val lookup_tenv_inc_tvs = Q.store_thm ("lookup_tenv_inc_tvs",
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
`!n tenv. ALOOKUP tenv n = lookup_tenv n 0 (bind_var_list2 tenv Empty)`,
 induct_on `tenv` >>
 rw [bind_var_list2_def, lookup_tenv_def] >>
 PairCases_on `h` >>
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

val type_lookup_lem4 = Q.prove (
`!tvs l tenv n t.
  tenv_ok tenv ∧
  (num_tvs tenv = 0) ∧
  (lookup_tenv n 0 tenv = SOME (l,t))
  ⇒
  (lookup_tenv n tvs tenv = SOME (l,t))`,
induct_on `tenv` >>
rw [lookup_tenv_def, num_tvs_def, tenv_ok_def] >-
metis_tac [] >>
fs [] >>
metis_tac [nil_deBruijn_inc]);

(* ---------- tenvM stuff ---------- *)

val tenvM_ok_lookup = Q.store_thm ("tenvM_ok_lookup",
`!n tenvM tenvC tenv.
  tenvM_ok tenvM ∧
  (FLOOKUP tenvM n = SOME tenv) ⇒
  tenv_ok (bind_var_list2 tenv Empty)`,
 induct_on `tenvM` >>
 rw [tenvM_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_UPDATE] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 metis_tac []);

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

val tenvM_ok_pres = Q.store_thm ("tenvM_ok_pres",
`∀tenvM mn tenv. 
  tenvM_ok tenvM ∧
  tenv_ok (bind_var_list2 tenv Empty)
  ⇒
  tenvM_ok (tenvM |+ (mn,tenv))`,
 induct_on `tenvM` >>
 rw [tenvM_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_UPDATE] >>
 cases_on `mn = k` >>
 fs [] >>
 metis_tac []);

(* ---------- type_op ---------- *)

val type_op_cases = Q.store_thm ("type_op_cases",
`!op ts t3.
  type_op op ts t3 ⇔
  (((∃op'. op = Opn op') ∧ ts = [Tint; Tint] ∧ (t3 = Tint)) ∨
   ((∃op'. op = Opb op') ∧ ts = [Tint; Tint] ∧ (t3 = Tbool)) ∨
   ((op = Opapp) ∧ ?t2. ts = [Tfn t2 t3;t2]) ∨
   ((op = Equality) ∧ ?t1. ts = [t1; t1] ∧ (t3 = Tbool)) ∨
   ((op = Opassign) ∧ ?t2. ts = [Tref t2; t2] ∧ (t3 = Tunit)) ∨
   ((op = Opref) ∧ ?t1. ts = [t1] ∧ t3 = Tref t1) ∨ 
   ((op = Opderef) ∧ ts = [Tref t3]) ∨
   ((op = Aw8alloc) ∧ ts = [Tint; Tword8] ∧ t3 = Tword8array) ∨
   ((op = Aw8sub) ∧ ts = [Tword8array; Tint] ∧ t3 = Tword8) ∨
   ((op = Aw8length) ∧ ts = [Tword8array] ∧ t3 = Tint) ∨
   ((op = Aw8update) ∧ ts = [Tword8array; Tint; Tword8] ∧ t3 = Tunit) ∨
   ((op = Explode) ∧ ts = [Tstring] ∧ t3 = Tapp [Tchar] (TC_name (Short "list"))) ∨
   ((op = Implode) ∧ ts = [Tapp [Tchar] (TC_name (Short "list"))] ∧ t3 = Tstring) ∨
   ((op = VfromList) ∧ ?t2. ts = [Tapp [t2] (TC_name (Short "list"))] ∧ t3 = Tapp [t2] TC_vector) ∨
   ((op = Vsub) ∧ ts = [Tapp [t3] TC_vector; Tint]) ∨
   ((op = Vlength) ∧ ?t1. ts = [Tapp [t1] TC_vector] ∧ t3 = Tint) ∨
   ((op = Aalloc) ∧ ?t1. ts = [Tint; t1] ∧ t3 = Tapp [t1] TC_array) ∨
   ((op = Asub) ∧ ts = [Tapp [t3] TC_array; Tint]) ∨
   ((op = Alength) ∧ ?t1. ts = [Tapp [t1] TC_array] ∧ t3 = Tint) ∨
   ((op = Aupdate) ∧ ?t1. ts = [Tapp [t1] TC_array; Tint; t1] ∧ t3 = Tunit))`,
 rw [type_op_def] >>
 every_case_tac >>
 fs [Tchar_def] >>
 metis_tac []);

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
rw [check_freevars_def, bind_tenv_def,
    tenv_ok_def, bind_tvar_def, bind_var_list_def, Tchar_def] >>
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
rw [deBruijn_subst_def, OPTION_MAP_DEF, Tchar_def] >|
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

val type_es_list_rel = Q.store_thm ("type_es_list_rel",
`!es ts tenvM tenvC tenv. type_es tenvM tenvC tenv es ts = LIST_REL (type_e tenvM tenvC tenv) es ts`,
 induct_on `es` >>
 rw [] >>
 rw [Once type_e_cases]);

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
 rw [check_freevars_def, bind_tenv_def, num_tvs_def, type_op_cases,
     tenv_ok_def, bind_tvar_def, bind_var_list_def, opt_bind_tenv_def] >>
 fs [check_freevars_def,Tchar_def]
 >- metis_tac [deBruijn_subst_check_freevars]
 >- metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD]
 >- metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD]
 >- (cases_on `pes` >>
     fs [RES_FORALL, num_tvs_bind_var_list] >>
     qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `(FST h, SND h)`) >>
     fs [] >>
     metis_tac [type_p_freevars, tenv_ok_bind_var_list])
 >- (every_case_tac >>
     fs [num_tvs_def, tenv_ok_def])
     (* COMPLETENESS
 >- (every_case_tac >>
     fs [num_tvs_def, tenv_ok_def])
 >- (every_case_tac >>
     fs [num_tvs_def, tenv_ok_def])
     *)
 >- metis_tac [tenv_ok_bind_var_list_funs, num_tvs_bind_var_list]
 (* COMPLETENESS
 >- metis_tac [tenv_ok_bind_var_list_tvs, num_tvs_bind_var_list, bind_tvar_def]
 *));

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
 rw [deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_tenv_def, 
     bind_tvar_rewrites, bind_tenv_def, num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE] >>
 fs [deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_tenv_def, 
     bind_tvar_rewrites, bind_tenv_def, num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_ok_def, Tchar_def] >>
 `tenv_ok tenvE2` by metis_tac [tenv_ok_db_merge, bind_tvar_def, tenv_ok_def]
 >- metis_tac [check_freevars_lem]
 >- (fs [RES_FORALL] >>
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
          metis_tac [deBruijn_subst_def, MAP]) >>
     pop_assum (MATCH_MP_TAC o 
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                      db_merge_bind_var_list] o
                Q.SPECL [`bind_var_list 0 tenv' tenvE1`, `targs`, `tvs`]) >>
     rw [] >>
     match_mp_tac tenv_ok_bind_var_list >>
     rw [num_tvs_db_merge, bind_tvar_rewrites] >>
     metis_tac [type_p_freevars])
 >- (fs [EVERY_MAP, EVERY_MEM] >>
     rw [] >>
     metis_tac [check_freevars_lem, EVERY_MEM])
 >- metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup]
 >- metis_tac [type_subst_deBruijn_subst_list, tenvC_ok_lookup]
 >- (cases_on `n` >>
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
      cases_on `FLOOKUP tenvM s` >>
          fs [] >>
          rw [] >>
          qexists_tac `MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs` >>
          rw [] >|
          [match_mp_tac (hd (CONJUNCTS deBruijn_subst2)) >>
               rw [] >>
               metis_tac [tenvM_ok_lookup, lookup_freevars, arithmeticTheory.ADD, arithmeticTheory.ADD_0],
           fs [EVERY_MAP, EVERY_MEM] >>
               rw [] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM]]])
 >- (qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'` 
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     fs [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3])
 >- (qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'` 
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     fs [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3])
 >- (fs [type_op_cases] >>
     rw [] >>
     fs [deBruijn_subst_def,Tchar_def] >>
     metis_tac [])
 >- (fs [RES_FORALL] >>
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
     metis_tac [type_p_freevars])
     (* COMPLETENESS
 >- (disj1_tac >>
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
      every_case_tac >>
          fs [tenv_ok_def] >>
          FIRST_X_ASSUM
                 (MP_TAC o 
                  Q.SPECL [`Bind_name x tvs t tenvE1`, `targs`, `tvs'`]) >>
          rw [bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, 
              num_tvs_def] >>
          imp_res_tac type_e_freevars >>
          fs [tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge]])
          *)
 >- ((* COMPLETENESS disj2_tac >> *)
     rw [] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     fs [deBruijn_inc0] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     FIRST_X_ASSUM
                 (MP_TAC o 
                  Q.SPECL [`Bind_name x 0 t tenvE1`, `targs`, `tvs`]) >>
     rw [bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, 
         num_tvs_def] >>
     imp_res_tac type_e_freevars >>
     fs [tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge])
     (* COMPLETENESS
 >- (qexists_tac `MAP (λ(x,t').
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
          metis_tac []])
          *)
 >- (qexists_tac `MAP (λ(x,t').
                 (x,
                  deBruijn_subst (num_tvs tenvE1)
                    (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                    t')) env` >>
    rw []
    >- (LAST_X_ASSUM (MP_TAC o Q.SPECL [`bind_var_list 0 env tenvE1`, `targs`, `tvs`]) >>
        rw [bind_tvar_rewrites, db_merge_bind_var_list, num_tvs_bind_var_list, 
            deBruijn_subst_E_bind_var_list] >>
        pop_assum match_mp_tac >>
        match_mp_tac tenv_ok_bind_var_list_funs >>
        rw [bind_tvar_rewrites] >>
        metis_tac [])
    >- (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`bind_var_list 0 env tenvE1`, `targs`, `tvs`]) >>
        rw [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list, db_merge_bind_var_list] >>
        pop_assum match_mp_tac >>
        match_mp_tac tenv_ok_bind_var_list_funs >>
        rw [] >>
        metis_tac []))
 >- (fs [check_freevars_def] >>
     metis_tac [check_freevars_lem])
 >- (fs [check_freevars_def] >>
     LAST_X_ASSUM (MP_TAC o Q.SPECL [`Bind_name n 0 t1 tenvE1`, `targs`, `tvs`]) >>
     rw [deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def])
 >- (fs [ALOOKUP_FAILS, MAP_MAP_o, combinTheory.o_DEF, LIST_TO_SET_MAP] >>
     CCONTR_TAC >>
     fs [] >>
     PairCases_on `x` >>
     fs [] >>
     rw [] >>
     fs [] >>
     metis_tac [mem_exists_set]));

(* Recursive functions have function type *)
val type_funs_Tfn = Q.store_thm ("type_funs_Tfn",
`∀tenvM tenvC tenv funs tenv' tvs t n.
  type_funs tenvM tenvC tenv funs tenv' ∧
  (ALOOKUP tenv' n = SOME t)
  ⇒
  ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenv) [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs tenvM tenvC tenv funspat tenv'`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
rw [] >>
fs [] >>
cases_on `fn = n` >>
fs [deBruijn_subst_def, check_freevars_def] >>
metis_tac [type_e_freevars, bind_tenv_def, num_tvs_def]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.store_thm ("type_funs_lookup",
`∀fn env tenvM tenvC funs env' n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenvM tenvC tenv funs env'
  ⇒
  (∃t. ALOOKUP env' fn = SOME t)`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [] >>
rw [] >>
metis_tac []);

val type_funs_MAP_FST = store_thm("type_funs_MAP_FST",
``!funs tenvM tenvC tenv env.
  type_funs tenvM tenvC tenv funs env ⇒ 
  MAP FST funs = MAP FST env``,
  Induct>>rw[]>>
  pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
  fs[]>>metis_tac[])

(* Functions in the type environment can be found *)
val type_funs_find_recfun = Q.store_thm ("type_funs_find_recfun",
`∀fn env tenvM tenvC funs tenv' e tenv t.
  (ALOOKUP tenv' fn = SOME t) ∧
  type_funs tenvM tenvC tenv funs tenv'
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [] >>
rw [Once find_recfun_def] >>
metis_tac []);

val type_recfun_lookup = Q.store_thm ("type_recfun_lookup",
`∀fn funs n e tenvM tenvC tenv tenv' tvs t1 t2.
  (find_recfun fn funs = SOME (n,e)) ∧
  type_funs tenvM tenvC tenv funs tenv' ∧
  (ALOOKUP tenv' fn = SOME (Tfn t1 t2))
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
fs [deBruijn_subst_def] >>
rw [check_freevars_def] >>
metis_tac [bind_tenv_def, num_tvs_def, type_e_freevars, type_funs_Tfn,
           EVERY_DEF, check_freevars_def]);

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

val type_e_subst_lem = Q.prove (
`(∀tenvM tenvC tenv e t targs tvs targs'.
  type_e tenvM tenvC (bind_tenv x 0 t1 (bind_tvar (LENGTH targs) tenv)) e t ∧
  (num_tvs tenv = 0) ∧ 
  tenvM_ok tenvM ∧ 
  tenvC_ok tenvC ∧ 
  tenv_ok (bind_tvar (LENGTH targs) tenv) ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t1
  ⇒
  type_e tenvM tenvC (bind_tenv x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenv)) e (deBruijn_subst 0 targs t))`,
rw [bind_tenv_def] >>
match_mp_tac ((SIMP_RULE (srw_ss()) [bind_tenv_def, num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def, deBruijn_inc0] o
               Q.SPECL [`tenvM`, `tenvC`, `e`, `t`, `bind_tenv x 0 t1 Empty`] o
               SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o
               hd o
               CONJUNCTS)
              type_e_subst) >>
rw [tenv_ok_def, bind_tvar_def, num_tvs_def] >>
metis_tac []);

val type_funs_subst_lem = 
(Q.GEN `tenvE2` o
 SIMP_RULE (srw_ss()) [bind_tenv_def, num_tvs_def, deBruijn_subst_tenvE_def,
                       db_merge_def, deBruijn_inc0, num_tvs_bind_var_list,
                       db_merge_bind_var_list,
                       deBruijn_subst_E_bind_var_list] o
 Q.SPECL [`tenvM`, `tenvC`, `e`, `t`, `bind_var_list 0 tenv' Empty`] o
 SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o
 hd o
 tl o
 tl o
 CONJUNCTS)
type_e_subst;

(* ---------- tid_exn_to_tc ---------- *)

val tid_exn_to_tc_11 = Q.store_thm ("tid_exn_to_tc_11",
`!x y. (tid_exn_to_tc x = tid_exn_to_tc y) = same_tid x y`,
cases_on `x` >>
cases_on `y` >>
rw [tid_exn_to_tc_def, same_tid_def]);

(* ---------- ctMap stuff ---------- *)
(* flat_tenvC_ok, ctMap_ok, flat_to_ctMap_list, to_ctMap_list, flat_to_ctMap,
 * to_ctMap, ctMap_to_mods, tenvC_to_types, consistent_ctMap *)

val empty_to_ctMap = Q.store_thm ("empty_to_ctMap",
`(!ctMap. FUNION (flat_to_ctMap []) ctMap = ctMap) ∧
 (!ctMap. DISJOINT (FDOM (flat_to_ctMap [])) (FDOM ctMap))`,
 rw [flat_to_ctMap_def, flat_to_ctMap_list_def, fmap_eq_flookup,
     FLOOKUP_FUNION, flookup_fupdate_list, DISJOINT_DEF, EXTENSION,
     FDOM_FUPDATE_LIST]);

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

val flat_tenvC_ok_ctMap = Q.store_thm ("flat_tenvC_ok_ctMap",
`!tenvC. flat_tenvC_ok tenvC ⇒ ctMap_ok (flat_to_ctMap tenvC)`,
 rw [flat_to_ctMap_def, flat_to_ctMap_list_def, EVERY_MEM, flat_tenvC_ok_def, 
     flookup_fupdate_list, ctMap_ok_def, FEVERY_ALL_FLOOKUP] >>
 `?cn tn tvs ts. k = (cn,tn) ∧ v = (tvs,ts)` 
              by metis_tac [pair_CASES] >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP] >>
 PairCases_on `y` >>
 fs [EVERY_MEM, flat_tenvC_ok_def] >>
 res_tac >>
 fs []); 

val flat_to_ctMap_lookup_none = Q.prove (
`!cn flat_tenvC.
  (ALOOKUP flat_tenvC cn = NONE)
  ⇒
  !t. (FLOOKUP (flat_to_ctMap flat_tenvC) (cn,t) = NONE)`,
 rw [flat_to_ctMap_def, flookup_fupdate_list] >>
 every_case_tac >>
 rw [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_REVERSE, flat_to_ctMap_list_def, MEM_MAP, ALOOKUP_FAILS] >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 metis_tac [FST]);

val flat_to_ctMap_lookup_not_none = Q.prove (
`!cn flat_tenvC tvs ts t.
  ALOOKUP flat_tenvC cn = SOME (tvs,ts,t)
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
  ALOOKUP tenvC cn = SOME (tvs,ts,t) ∧
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

val flat_to_ctMap_list_append = Q.store_thm ("flat_to_ctMap_list_append",
`!tenvC1 tenvC2. flat_to_ctMap_list (tenvC1 ++ tenvC2) = flat_to_ctMap_list tenvC1 ++ flat_to_ctMap_list tenvC2`,
rw [flat_to_ctMap_list_def]);

val ctMap_ok_tenvC_ok = Q.store_thm ("ctMap_ok_tenvC_ok",
`!tenvC. 
  ALL_DISTINCT (MAP FST (REVERSE (flat_to_ctMap_list tenvC))) ∧ ctMap_ok (flat_to_ctMap tenvC) ⇒ tenvC_ok ([],tenvC)`,
 rw [flat_to_ctMap_list_def, flat_to_ctMap_def, ctMap_ok_def, tenvC_ok_def, flat_tenvC_ok_def] >>
 imp_res_tac FEVERY_FUPDATE_LIST >>
 fs [EVERY_MEM, EVERY_MAP] >>
 rw [] >>
 PairCases_on `e` >>
 fs [MEM_MAP] >>
 rw [] >>
 res_tac >>
 fs []);

val flat_to_ctMap_append = Q.store_thm ("flat_to_ctMap_append",
`!tenvC1 tenvC2.
  flat_to_ctMap (tenvC1++tenvC2) = FUNION (flat_to_ctMap tenvC1) (flat_to_ctMap tenvC2)`,
rw [REVERSE_APPEND, flat_to_ctMap_def, flat_to_ctMap_list_def, fmap_eq_flookup,
    flookup_fupdate_list, FLOOKUP_FUNION] >>
every_case_tac >>
fs [ALOOKUP_APPEND] >>
every_case_tac >>
fs []);

val consistent_ctMap_extend = Q.store_thm ("consistent_ctMap_extend",
`!mn tdefs mdecls tdecls edecls ctMap.
  consistent_ctMap (mdecls, tdecls, edecls) ctMap
  ⇒
  consistent_ctMap (mdecls,set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs) ∪ tdecls, edecls) 
                   (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs) ⊌ ctMap)`,
 rw [consistent_ctMap_def, RES_FORALL] >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 fs [flat_to_ctMap_def, build_ctor_tenv_def, flat_to_ctMap_list_def] >>
 fs [FDOM_FUPDATE_LIST, MEM_MAP, MEM_FLAT] >>
 rw []
 >- (PairCases_on `y''` >>
     fs [] >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     PairCases_on `y` >>
     fs [] >>
     rw [EXISTS_PROD] >>
     metis_tac [])
 >- (res_tac >>
     fs [] >>
     every_case_tac >>
     fs []));

val consistent_ctMap_extend_exn = Q.store_thm ("consistent_ctMap_extend_exn",
`!mn cn ts mdecls tdecls edecls ctMap.
  consistent_ctMap (mdecls, tdecls, edecls) ctMap
  ⇒
  consistent_ctMap (mdecls,tdecls, {mk_id mn cn} ∪ edecls) 
                   (flat_to_ctMap [(cn,([],ts,TypeExn (mk_id mn cn)))] ⊌ ctMap)`,
 rw [consistent_ctMap_def, RES_FORALL] >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 fs [flat_to_ctMap_def, flat_to_ctMap_list_def] >>
 fs [FDOM_FUPDATE_LIST, MEM_MAP, MEM_FLAT] >>
 rw [] >>
 res_tac >>
 fs [] >>
 every_case_tac >>
 fs []);

(* ---------- consistent_decls ---------- *)

val consistent_decls_disjoint = Q.store_thm ("consistent_decls_disjoint",
`!mdecls tdecls edecls tdefs ctMap mn.
  DISJOINT (set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs)) tdecls ∧
  consistent_ctMap (mdecls,tdecls,edecls) ctMap
  ⇒
  DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs))) (FDOM ctMap)` ,
 rw [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``, consistent_ctMap_def, RES_FORALL, DISJOINT_DEF, EXTENSION] >>
 res_tac >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 fs [] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs [] >>
 rw [build_ctor_tenv_def, flat_to_ctMap_def,flat_to_ctMap_list_def, FDOM_FUPDATE_LIST,
     MEM_MAP, MEM_FLAT, FORALL_PROD] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 fs [MEM_MAP] >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 fs [FORALL_PROD] >>
 metis_tac []);

val consistent_decls_disjoint_exn = Q.store_thm ("consistent_decls_disjoint_exn",
`!mdecls tdecls edecls cn ctMap mn ts.
  mk_id mn cn ∉ edecls ∧
  consistent_ctMap (mdecls,tdecls,edecls) ctMap
  ⇒
  DISJOINT (FDOM (flat_to_ctMap [(cn,([]:tvarN list,ts,TypeExn (mk_id mn cn)))])) (FDOM ctMap)` ,
 rw [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``, consistent_ctMap_def, RES_FORALL, DISJOINT_DEF, EXTENSION] >>
 res_tac >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 fs [] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs [] >>
 rw [flat_to_ctMap_def,flat_to_ctMap_list_def, FDOM_FUPDATE_LIST, MEM_MAP] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 fs []);

val consistent_decls_add_mod = Q.store_thm ("consistent_decls_add_mod",
`!decls mdecls tdecls edecls mn.
  consistent_decls decls (mdecls,tdecls,edecls)
  ⇒
  consistent_decls decls ({mn} ∪ mdecls,tdecls,edecls)`,
 rw [consistent_decls_def, RES_FORALL] >>
 every_case_tac >>
 fs [] >>
 res_tac >>
 fs []);

(* ---------- type_v, type_vs, type_env, consistent_mod_env ---------- *)

val type_vs_list_rel = Q.store_thm ("type_vs_list_rel",
`!vs ts tvs tenvC tenvS. type_vs tvs tenvC tenvS vs ts = LIST_REL (type_v tvs tenvC tenvS) vs ts`,
 induct_on `vs` >>
 rw [] >>
 rw [Once type_v_cases]);

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
 rw [check_freevars_def, tenv_ok_def, bind_tenv_def, num_tvs_def, bind_tvar_def, Tchar_def] >-
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
     fs [] >>
     rw [] >>
     metis_tac [type_funs_Tfn, num_tvs_bind_var_list, num_tvs_def,
                arithmeticTheory.ADD, arithmeticTheory.ADD_COMM])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
               arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
               arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
               arithmeticTheory.GREATER_EQ]);

val type_vs_length = Q.store_thm ("type_vs_length",
`∀tvs tenvC tenvS vs ts.
  type_vs tvs tenvC tenvS vs ts ⇒ (LENGTH vs = LENGTH ts)`,
induct_on `vs` >>
rw [Once type_v_cases] >>
rw [] >>
metis_tac []);

(* Typing lists of values from the end *)
val type_vs_end = Q.store_thm ("type_vs_end",
`∀tvs tenvC vs ts v t tenvS.
  type_vs tvs tenvC tenvS (vs++[v]) (ts++[t]) =
  (type_v tvs tenvC tenvS v t ∧
   type_vs tvs tenvC tenvS vs ts)`,
induct_on `vs` >>
rw [] >>
cases_on `ts` >>
fs [] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 metis_tac [type_v_rules],
 imp_res_tac type_vs_length >>
     fs [],
 imp_res_tac type_vs_length >>
     fs [],
 imp_res_tac type_vs_length >>
     fs [],
 imp_res_tac type_vs_length >>
     fs [],
 imp_res_tac type_vs_length >>
     fs [],
 imp_res_tac type_vs_length >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [type_v_rules],
 rw [Once type_v_cases] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs []]);

(* Everything in the type environment is also in the execution environment *)
val type_lookup_lem = Q.prove (
`∀tenvC env tenvS tenv v n t' idx.
  type_env tenvC tenvS env tenv ∧
  (lookup_tenv n idx tenv = SOME t')
  ⇒
  (∃v'. ALOOKUP env n = SOME v')`,
induct_on `tenv` >>
rw [Once type_v_cases] >>
fs [lookup_tenv_def, bind_tenv_def] >-
metis_tac [] >>
every_case_tac >>
fs [] >>
metis_tac []);

val type_lookup = Q.store_thm ("type_lookup",
`∀tenvC env tenvS tenv v n t' idx tvs.
  type_env tenvC tenvS env tenv ∧
  (lookup_tenv n idx (bind_tvar tvs tenv) = SOME t')
  ⇒
  (∃v'. ALOOKUP env n = SOME v')`,
induct_on `tvs` >>
rw [bind_tvar_def] >-
metis_tac [type_lookup_lem] >>
fs [bind_tvar_def, lookup_tenv_def] >>
rw [] >>
every_case_tac >>
fs [lookup_tenv_def] >>
`!x y. x + SUC y = (x + 1) + y` by decide_tac >>
metis_tac []);

val type_lookup_id = Q.store_thm ("type_lookup_id",
`∀tenvS tenvC menv tenvM (cenv : envC) tenv.
  type_env tenvC tenvS env tenv ∧
  consistent_mod_env tenvS tenvC menv tenvM 
  ⇒
  ((t_lookup_var_id n tenvM (bind_tvar tvs tenv) = SOME (tvs', t)) ⇒ 
     (∃v. (lookup_var_id n (menv,cenv,env) = SOME v)))`,
 induct_on `menv` >>
 rw [t_lookup_var_id_def, lookup_var_id_def] >>
 cases_on `n` >>
 fs [] >>
 rw [lookup_var_id_def, t_lookup_var_id_def] >>
 imp_res_tac type_lookup >>
 rw [] >>
 qpat_assum `consistent_mod_env tenvS x0 x1 x2` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 fs [] >>
 rw [] >>
 fs [t_lookup_var_id_def, lookup_var_id_def, FLOOKUP_UPDATE]
 >- (match_mp_tac type_lookup >>
     every_case_tac >>
     fs [lookup_tenv_def, bind_tvar_def, bvl2_lookup] >>
     metis_tac [SAME_KEY_UPDATES_DIFFER])
 >- metis_tac []);

val type_subst = Q.store_thm ("type_subst",
`(!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    ∀targs tvs'.
      (tvs = LENGTH targs) ∧
      ctMap_ok ctMap ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars (LENGTH targs) [] t
      ⇒
      type_v tvs' ctMap tenvS v
             (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs' t))) ∧
 (!tvs ctMap tenvS vs ts. type_vs tvs ctMap tenvS vs ts ⇒
   ∀targs tvs'.
     (tvs = LENGTH targs) ∧
     ctMap_ok ctMap ∧
     EVERY (check_freevars tvs' []) targs ∧
     EVERY (check_freevars (LENGTH targs) []) ts
     ⇒
     type_vs tvs' ctMap tenvS vs
             (MAP (deBruijn_subst 0 targs) (MAP (deBruijn_inc (LENGTH targs) tvs') ts))) ∧
 (!ctMap tenvS env tenv. type_env ctMap tenvS env tenv ⇒ 
    type_env ctMap tenvS env tenv) ∧
 (!ctMap tenvS envM tenvM. consistent_mod_env ctMap tenvS envM tenvM ⇒ 
    consistent_mod_env ctMap tenvS envM tenvM)`,
 ho_match_mp_tac type_v_strongind >>
 rw [] >>
 rw [Once type_v_cases] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 fs [check_freevars_def, Tchar_def] >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 rw [nil_deBruijn_inc, deBruijn_subst_check_freevars, type_subst_lem3,
     nil_deBruijn_subst]
 >- (rw [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [type_subst_lem1, EVERY_MEM])
 >- (`EVERY (check_freevars 0 tvs') ts` by metis_tac [ctMap_ok_lookup, EVERY_MEM] >>
     `EVERY (check_freevars (LENGTH targs) tvs') ts`
           by (`LENGTH targs ≥ 0` by decide_tac >>
               metis_tac [EVERY_MEM, check_freevars_add]) >>
     fs [GSYM FUNION_alist_to_fmap] >>
     `type_vs tvs'' ctMap tenvS vs
              (MAP (deBruijn_subst 0 targs)
                 (MAP (deBruijn_inc (LENGTH targs) tvs'')
                    (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)))`
            by metis_tac [check_freevars_subst_list] >>
     pop_assum mp_tac >>
     rw [type_subst_deBruijn_subst_list, type_subst_deBruijn_inc_list])
 >- metis_tac []
 >- (qexists_tac `menv` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >>
     match_mp_tac type_e_subst_lem >>
     rw [tenv_ok_def, bind_tvar_def] >>
     metis_tac [type_v_freevars, ctMap_ok_lookup, consistent_con_env_def])
 >- (qexists_tac `menv` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     qexists_tac `MAP (λ(x,t). (x,deBruijn_subst 0 targs t)) tenv'` >>
     rw [] >|
     [match_mp_tac type_funs_subst_lem >>
          rw [] >-
          metis_tac [type_v_freevars] >-
          metis_tac [consistent_con_env_def] >>
          match_mp_tac tenv_ok_bind_var_list_funs >>
          metis_tac [tenv_ok_bind_var_list_funs, type_v_freevars, bind_tvar_rewrites],
      qpat_assum `type_funs w0 w x y z` (fn x => ALL_TAC) >>
          induct_on `tenv'` >>
          fs [] >>
          rw [] >>
          PairCases_on `h` >>
          fs [] >>
          rw [] >>
          metis_tac []])
 >- (fs [EVERY_MEM] >>
     rw [] >>
     res_tac >>
     fs [] >>
     imp_res_tac nil_deBruijn_inc >>
     fs [] >>
     imp_res_tac nil_deBruijn_subst >>
     fs [])
 >- (fs [bind_tenv_def] >>
     metis_tac [type_v_rules])
 >- (fs [bind_tenv_def] >>
     rw [Once type_v_cases, bind_tenv_def])
 >- (fs [bind_tenv_def] >>
     metis_tac [type_v_rules])
 >- (fs [bind_tenv_def] >>
     metis_tac [type_v_rules]));

(* They value of a binding in the execution environment has the type given by
 * the type environment. *)
val type_lookup_lem2 = Q.prove (
`∀ctMap env tenv tvs tenvS v x t targs tparams idx.
  ctMap_ok ctMap ∧
  type_env ctMap tenvS env tenv ∧
  EVERY (check_freevars tvs []) targs ∧
  (lookup_tenv x 0 (bind_tvar tvs tenv) = SOME (LENGTH targs, t)) ∧
  (ALOOKUP env x = SOME v)
  ⇒
  type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
rw [] >>
fs [lookup_tenv_def, bind_tvar_def] >>
qpat_assum `type_env ctMap tenvS env tenv_pat`
        (MP_TAC o SIMP_RULE (srw_ss ())
                         [Once type_env_cases]) >>
rw [] >>
fs [bind_tenv_def] >>
rw [] >>
cases_on `n'≠x` >>
rw [] >-
metis_tac [lookup_tenv_def] >>
`(n = LENGTH targs) ∧ (t = deBruijn_inc n tvs t')`
          by (cases_on `tvs` >>
              fs [lookup_tenv_def] >>
              metis_tac []) >>
rw [] >>
metis_tac [type_v_freevars, type_subst, bind_tvar_def]);

val consistent_mod_env_lookup = Q.prove (
`!tenvS ctMap menv tenvM tenv env n.
  consistent_mod_env tenvS ctMap menv tenvM ∧
  ALOOKUP menv n = SOME env ∧
  FLOOKUP tenvM n = SOME tenv
  ⇒
  type_env ctMap tenvS env (bind_var_list2 tenv Empty)`,
 induct_on `menv` >>
 rw [] >>
 qpat_assum `consistent_mod_env x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once consistent_mod_cases]) >>
 fs [] >>
 rw [] >>
 fs [FLOOKUP_UPDATE] >>
 every_case_tac >>
 fs [] >>
 metis_tac []);

val type_lookup_type_v = Q.store_thm ("type_lookup_type_v",
`∀tenvM ctMap menv env tenv tvs tenvS v x t targs tparams idx.
  tenvM_ok tenvM ∧
  ctMap_ok ctMap ∧
  type_env ctMap tenvS env tenv ∧
  consistent_mod_env tenvS ctMap menv tenvM ∧
  EVERY (check_freevars tvs []) targs ∧
  (t_lookup_var_id x tenvM (bind_tvar tvs tenv) = SOME (LENGTH targs, t)) ∧
  (lookup_var_id x (menv,cenv,env) = SOME v)
  ⇒
  type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
 cases_on `x` >>
 rw [] >>
 fs [lookup_var_id_def, t_lookup_var_id_def] >-
 metis_tac [type_lookup_lem2] >>
 every_case_tac >>
 fs [] >>
 match_mp_tac type_lookup_lem2 >>
 rw [bind_tvar_rewrites] >>
 imp_res_tac consistent_mod_env_lookup >>
 qexists_tac `x` >>
 qexists_tac `bind_var_list2 x' Empty` >>
 qexists_tac `a` >>
 rw [] >>
 metis_tac [tenvM_ok_lookup, type_lookup_lem4, num_tvs_bvl2, num_tvs_def, bvl2_lookup]);

val type_env_merge_bvl2 = Q.store_thm ("type_env_merge_bvl2",
`!tenvM tenvC tenvS env1 tenv1 env2 tenv2.
  type_env tenvC tenvS env2 (bind_var_list2 tenv2 Empty) ∧
  type_env tenvC tenvS env1 (bind_var_list2 tenv1 Empty) ⇒
  type_env tenvC tenvS (env1 ++ env2) (bind_var_list2 (tenv1 ++ tenv2) Empty)`,
 induct_on `env1` >>
 cases_on `tenv1` >>
 rw [] >>
 rw [Once type_v_cases] >>
 rw [] >>
 PairCases_on `h` >>
 fs [bind_var_list2_def, bind_tenv_def] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 fs [bind_tenv_def] >>
 metis_tac []);

(* ---------- constructor checking stuff ---------- *)
(* check_new_type, check_ctor_tenv, build_ctor_tenv, check_new_exn,
 * check_exn_tenv *)

val lookup_ctor_none_lem = Q.prove (
`!x h0 h1 h2 h3.
  ALOOKUP (MAP (λ(cn,ts). (cn,h0,MAP f ts,TypeId (mk_id mn h1))) h2) x = NONE
  ⇔ 
  ALOOKUP (MAP (λ(conN,ts). (conN,LENGTH ts,TypeId (mk_id mn h3))) h2) x = NONE`,
 induct_on `h2` >>
 rw [] >>
 PairCases_on `h` >>
 rw []);

val lookup_ctor_none = Q.store_thm ("lookup_ctor_none",
`!tds tenvC envC.
  !x. ALOOKUP (build_ctor_tenv mn tenvT tds) x = NONE ⇔
      ALOOKUP (build_tdefs mn tds) x = NONE`,
 rw [build_ctor_tenv_def, build_tdefs_def, flookup_fupdate_list] >>
 eq_tac >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 induct_on `tds` >>
 rw [ALOOKUP_APPEND, REVERSE_APPEND] >>
 every_case_tac >>
 fs [] >>
 PairCases_on `h` >>
 fs [] >>
 metis_tac [lookup_ctor_none_lem, NOT_SOME_NONE, MAP_REVERSE]);

val build_ctor_tenv_cons = Q.prove (
`∀tvs tn ctors tds.
  build_ctor_tenv mn tenvT ((tvs,tn,ctors)::tds) =
    build_ctor_tenv mn tenvT tds ++ REVERSE (MAP (λ(cn,ts). (cn,tvs,MAP (type_name_subst tenvT) ts,TypeId (mk_id mn tn))) ctors)`,
rw [build_ctor_tenv_def]);

val build_ctor_tenv_empty = Q.store_thm ("build_ctor_tenv_empty",
`build_ctor_tenv mn tenvT [] = []`,
rw [build_ctor_tenv_def]);

val check_ctor_tenvC_ok = Q.store_thm ("check_ctor_tenvC_ok",
`!mn c tenvT. 
 check_ctor_tenv mn tenvT c ∧
 tenvT_ok tenvT
 ⇒ 
 flat_tenvC_ok (build_ctor_tenv mn tenvT c)`,
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
 fs [MEM_MAP] >>
 rw [] >>
 res_tac >>
 fs [] >>
 match_mp_tac check_freevars_type_name_subst >>
 rw []);

val check_ctor_tenv_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_ctor_tenv mn tenvT ((tvs,ts,ctors)::tds) ⇒
  check_ctor_tenv mn tenvT tds`,
 rw [] >>
 fs [check_ctor_tenv_def] >>
 metis_tac [check_dup_ctors_cons]);

val check_ctor_tenv_dups = Q.store_thm ("check_ctor_tenv_dups",
`!mn tdecs. check_ctor_tenv mn tenvT tdecs ⇒ check_dup_ctors tdecs`,
 induct_on `tdecs` >>
 rw [check_dup_ctors_def, LET_THM] >>
 PairCases_on `h` >>
 imp_res_tac check_ctor_tenv_cons >>
 res_tac >>
 rw [] >>
 fs [check_ctor_tenv_def, check_dup_ctors_def, LET_THM]);

val check_ctor_ctMap_ok = Q.store_thm ("check_ctor_ctMap_ok",
`!mn tenvT c. 
 check_ctor_tenv mn tenvT c ∧
 tenvT_ok tenvT
 ⇒ 
 ctMap_ok (flat_to_ctMap (build_ctor_tenv mn tenvT c))`,
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
  ALOOKUP (build_ctor_tenv mn tenvT tds) cn = SOME (tvs,ts,t)
  ⇒
  ALOOKUP (build_tdefs mn tds) cn = SOME (LENGTH ts,t)`,
 induct_on `tds` >>
 rw [build_ctor_tenv_empty] >>
 PairCases_on `h` >>
 fs [build_ctor_tenv_cons, build_tdefs_cons] >>
 fs [ALOOKUP_APPEND, FLOOKUP_FUNION] >>
 cases_on `ALOOKUP (build_tdefs mn tds) cn` >>
 rw []
 >- (cases_on `ALOOKUP (build_ctor_tenv mn tenvT tds) cn` >>
     fs []
     >- (fs [GSYM MAP_REVERSE, flookup_fupdate_list] >>
         rpt (pop_assum mp_tac) >>
         Q.SPEC_TAC (`REVERSE h2`, `h2`) >>
         induct_on `h2` >>
         rw [] >>
         PairCases_on `h` >>
         fs [] >>
         rw [] >>
         fs [])
     >- metis_tac [NOT_SOME_NONE])
 >- (fs [flookup_fupdate_list] >>
     Cases_on `ALOOKUP (build_ctor_tenv mn tenvT tds) cn` >>
     fs []
     >- metis_tac [lookup_ctor_none, NOT_SOME_NONE]
     >- (rw [] >>
         res_tac >>
         fs [])));

val check_dup_ctors_distinct = Q.prove (
`!tds mn.
  check_dup_ctors tds ⇒ ALL_DISTINCT (MAP FST (flat_to_ctMap_list (build_ctor_tenv mn tenvT tds)))`,
 induct_on `tds` >>
 rw [check_dup_ctors_thm, build_ctor_tenv_def, flat_to_ctMap_list_def,REVERSE_APPEND, ALL_DISTINCT_APPEND] >>
 fs [flat_to_ctMap_list_def, build_ctor_tenv_def, check_dup_ctors_thm, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
 rw [] >>
 PairCases_on `h` >>
 fs [MAP_FLAT, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, REVERSE_APPEND, GSYM MAP_REVERSE]
 >- (`?l. h2 = REVERSE l` by (qexists_tac `REVERSE h2` >> rw []) >>
     rw [] >>
     fs [MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     induct_on `l` >>
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
 >- (fs [MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     fs [MEM_FLAT, MEM_MAP] >>
     rw [] >>
     PairCases_on `y` >>
     fs [] >>
     PairCases_on `y'` >>
     fs [MEM_MAP] >>
     rw [FORALL_PROD] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     fs [] >>
     rw [] >>
     `y1 = h1` by (fs [mk_id_def] >> every_case_tac >> fs []) >>
     rw [] >>
     FIRST_X_ASSUM (mp_tac o Q.SPEC `p_1`) >>
     rw [MEM_MAP]
     >- (qexists_tac `(p_1,p_2')` >>
         rw [FST_pair])
     >- (rw [EXISTS_PROD, LAMBDA_PROD] >>
         qexists_tac `MAP FST y2` >>
         rw []
         >- metis_tac [FST_pair] >>
         rw [MEM_MAP] >>
         metis_tac [FST])));

(* ---------- consistent_con_env ---------- *)

val extend_consistent_con = Q.store_thm ("extend_consistent_con",
`!ctMap cenv tenvC mn tdefs.
  DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs))) (FDOM ctMap) ∧
  tenvT_ok tenvT ∧
  check_ctor_tenv mn tenvT tdefs ∧
  consistent_con_env ctMap cenv tenvC
  ⇒
  consistent_con_env (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs) ⊌ ctMap)
                     (merge_alist_mod_env ([],build_tdefs mn tdefs) cenv)
                     (merge_alist_mod_env ([],build_ctor_tenv mn tenvT tdefs) tenvC)`,
 rw [consistent_con_env_def, ALOOKUP_APPEND, tenvC_ok_merge, lookup_tenvC_merge_emp]
 >- (rw [tenvC_ok_def] >>
     metis_tac [check_ctor_tenvC_ok])
 >- metis_tac [check_ctor_ctMap_ok, ctMap_ok_merge_imp]
 >- (fs [lookup_alist_mod_env_def] >>
     PairCases_on `cenv` >>
     fs [lookup_mod_env_def, FLOOKUP_FUNION, merge_mod_env_def] >>
     rpt (FIRST_X_ASSUM (qspecl_then [`cn`] mp_tac)) >>
     Cases_on `cn` >>
     fs []
     >- (Cases_on `ALOOKUP (build_tdefs mn tdefs) a` >>
         fs []
         >- (`ALOOKUP (build_ctor_tenv mn tenvT tdefs) a = NONE` by metis_tac [lookup_ctor_none] >>
             rw [] >>
             every_case_tac >>
             fs [id_to_n_def, flookup_thm, DISJOINT_DEF, EXTENSION] >>
             metis_tac [])
         >- (rw [] >>
             `ALOOKUP (build_ctor_tenv mn tenvT tdefs) a ≠ NONE`
                      by metis_tac [NOT_SOME_NONE, lookup_ctor_none] >>
             Cases_on `ALOOKUP (build_ctor_tenv mn tenvT tdefs) a` >>
             rw [] >>
             PairCases_on `x` >>
             imp_res_tac ctor_env_to_tdefs >>
             simp [] >>
             imp_res_tac flat_to_ctMap_lookup_not_none >>
             fs [id_to_n_def] >>
             rw [] >>
             Cases_on `FLOOKUP (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs)) (a,t)` >>
             rw [] >>
             imp_res_tac check_ctor_tenv_dups >>
             metis_tac [check_dup_ctors_distinct, to_ctMap_lookup]))
     >- (Cases_on `ALOOKUP cenv0 s` >>
         fs [] >>
         rw [id_to_n_def] >>
         MAP_EVERY qexists_tac [`tvs`, `ts`] >>
         rw [] >>
         every_case_tac >>
         fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
         metis_tac []))
 >- (fs [lookup_alist_mod_env_def] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     PairCases_on `cenv` >>
     fs [lookup_mod_env_def, ALOOKUP_APPEND, merge_mod_env_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [NOT_SOME_NONE, pair_CASES,ctor_env_to_tdefs]));

val extend_consistent_con_exn = Q.store_thm ("extend_consistent_con_exn",
`∀mn tenvC cn ts cenv ctMap.
  (cn,TypeExn (mk_id mn cn)) ∉ FDOM ctMap ∧
  check_exn_tenv mn cn ts ∧
  tenvT_ok tenvT ∧
  EVERY (check_type_names tenvT) ts ∧
  consistent_con_env ctMap cenv tenvC
  ⇒
  consistent_con_env (FUNION (flat_to_ctMap [(cn,([],MAP (type_name_subst tenvT) ts,TypeExn (mk_id mn cn)))]) ctMap)
                     (merge_alist_mod_env ([], [(cn,(LENGTH ts,TypeExn (mk_id mn cn)))]) cenv)
                     (merge_alist_mod_env ([], [(cn,([],MAP (type_name_subst tenvT) ts,TypeExn (mk_id mn cn)))]) tenvC)`,
 rw [check_exn_tenv_def, consistent_con_env_def, FEVERY_ALL_FLOOKUP,
     flat_to_ctMap_def, ctMap_ok_def, tenvC_ok_merge, tenvC_ok_def,
     flat_tenvC_ok_def, lookup_tenvC_merge_emp] >>
 fs [flookup_fupdate_list, FLOOKUP_FUNION, lookup_alist_mod_env_def] >>
 rpt (FIRST_X_ASSUM (qspecl_then [`cn'`] mp_tac)) >>
 rw [] >>
 every_case_tac >>
 fs [flat_to_ctMap_list_def, id_to_n_def] >>
 rw [ALOOKUP_APPEND] >>
 res_tac >>
 fs [MEM_MAP, FORALL_PROD] >>
 PairCases_on `tenvC` >>
 PairCases_on `cenv` >>
 fs [lookup_mod_env_def, FLOOKUP_FUNION, merge_mod_env_def] >>
 fs [lookup_alist_mod_env_def] >>
 every_case_tac >>
 fs []>>
 fs[FLOOKUP_DEF,EVERY_MEM,MEM_MAP]>>
 metis_tac[check_freevars_type_name_subst,check_freevars_def]);

val consistent_con_env_lookup = Q.store_thm ("consistent_con_env_lookup",
`!ctMap envC tenvC cn tvs ts tn.
  consistent_con_env ctMap envC tenvC ∧
  lookup_alist_mod_env cn tenvC = SOME (tvs,ts,tn)
  ⇒
  FLOOKUP ctMap (id_to_n cn,tn) = SOME (tvs, ts)`,
 rw [consistent_con_env_def] >>
 cases_on `lookup_alist_mod_env cn envC` >>
 fs [] >>
 res_tac >>
 fs [] >>
 PairCases_on `x` >>
 res_tac >>
 fs [] >>
 rw []);

val consistent_con_env_to_mod = Q.store_thm ("consistent_con_env_to_mod",
`!ctMap envC flat_envC tenvC flat_tenvC mn.
  MAP FST flat_envC = MAP FST flat_tenvC ∧
  consistent_con_env ctMap envC tenvC ∧
  consistent_con_env ctMap (merge_alist_mod_env ([],flat_envC) envC) (merge_alist_mod_env ([],flat_tenvC) tenvC)
  ⇒
  consistent_con_env ctMap (merge_alist_mod_env ([(mn,flat_envC)],[]) envC) (merge_alist_mod_env ([(mn,flat_tenvC)],[]) tenvC)`,
 rw [consistent_con_env_def] >>
 PairCases_on `tenvC` >>
 PairCases_on `envC` >>
 fs [merge_alist_mod_env_def]
 >- fs [tenvC_ok_def, flat_tenvC_ok_def]
 >- (`(?mn' cn'. cn = Long mn' cn') ∨ (?cn'. cn = Short cn')` by (Cases_on `cn` >> metis_tac []) >>
     fs [lookup_tenvC_mod_cons] >>
     rw []
     >- (FIRST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`, `n`, `t`]) >>
         fs [lookup_alist_mod_env_def] >>
         rw [] >>
         fs [ALOOKUP_APPEND, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         every_case_tac >>
         fs [] >>
         rw [] >>
         fs [id_to_n_def] >>
         imp_res_tac ALOOKUP_MEM >>
         fs [MEM_MAP, ALOOKUP_FAILS] >>
         fs [flookup_thm] >>
         metis_tac [MEM_MAP, FST, pair_CASES])
     >- (fs [] >>
         FIRST_X_ASSUM (mp_tac o Q.SPECL [`Long mn' cn'`, `n`, `t`]) >>
         fs [lookup_alist_mod_env_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         rw [])
     >- (LAST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`, `n`, `t`]) >>
         fs [lookup_alist_mod_env_def,
             FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         rw []))
 >- (`(?mn' cn'. cn = Long mn' cn') ∨ (?cn'. cn = Short cn')` by (Cases_on `cn` >> metis_tac []) >>
     fs [lookup_tenvC_mod_cons, lookup_alist_mod_env_def, ALOOKUP_APPEND] >>
     rw [] >>
     fs [ALOOKUP_FAILS]
     >- metis_tac [MEM_MAP, FST, pair_CASES]
     >- (rpt (LAST_X_ASSUM (mp_tac o Q.SPECL [`Long mn' cn'`])) >>
         fs [lookup_alist_mod_env_def] >>
         rw [] >>
         fs [ALOOKUP_FAILS])
     >- (rpt (LAST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`])) >>
         fs [lookup_alist_mod_env_def] >>
         rw [] >>
         fs [ALOOKUP_FAILS])));

(* ---------- type_ctxt, type_ctxts ---------- *)

val type_ctxts_freevars = Q.store_thm ("type_ctxts_freevars",
`!tvs ctMap tenvS cs t1 t2.
  type_ctxts tvs ctMap tenvS cs t1 t2 ⇒
  ctMap_ok ctMap ⇒
  check_freevars tvs [] t1 ∧ check_freevars tvs [] t2`,
 ho_match_mp_tac type_ctxts_ind >>
 rw [type_ctxt_cases, check_freevars_def, GSYM FUNION_alist_to_fmap] >>
 rw [check_freevars_def] 
 >- (cases_on `pes` >>
     fs [RES_FORALL] >>
     qpat_assum `!x. (x = h) ∨ MEM x t ⇒ P x` (ASSUME_TAC o Q.SPEC `h`) >>
     fs [] >>
     PairCases_on `h` >>
     fs [] >>
     fs [Once context_invariant_cases] >>
     metis_tac [type_p_freevars])
 >- (imp_res_tac ctMap_ok_lookup >>
     fs [] >>
     match_mp_tac check_freevars_subst_single >>
     rw [] >>
     imp_res_tac consistent_con_env_lookup >>
     res_tac >>
     fs [] >>
     metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- (cases_on `pes` >>
     fs [RES_FORALL] >>
     qpat_assum `!x. (x = h) ∨ MEM x t ⇒ P x` (ASSUME_TAC o Q.SPEC `h`) >>
     fs [] >>
     PairCases_on `h` >>
     fs [] >>
     fs [Once context_invariant_cases] >>
     metis_tac [type_p_freevars])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- (imp_res_tac ctMap_ok_lookup >>
     fs [] >>
     match_mp_tac check_freevars_subst_single >>
     rw [] >>
     imp_res_tac consistent_con_env_lookup >>
     res_tac >>
     fs [] >>
     metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]);

(* ---------- type_d ---------- *)

val type_d_tenv_ok = Q.store_thm ("type_d_tenv_ok",
`!tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' tenvM'' tenvC''.
  type_d tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' ∧
  (num_tvs tenv = 0)
  ⇒
  tenv_ok (bind_var_list2 tenv' Empty)`,
 rw [type_d_cases] >>
 `tenv_ok Empty` by rw [tenv_ok_def] >>
 imp_res_tac type_p_bvl >>
 rw [bvl2_to_bvl]
 >- metis_tac [type_funs_tenv_ok] >>
 rw [bind_var_list2_def, tenv_ok_def]);

(*weakened*)
val type_d_tenvT_ok = Q.store_thm ("type_d_tenvT_ok",
`!tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' tenvM'' tenvC''.
  type_d tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' ∧
  tenvT_ok tenvT
  ⇒
  flat_tenvT_ok tenvT'`,
 rw [type_d_cases, flat_tenvT_ok_def] >>
 fs [FEVERY_ALL_FLOOKUP, check_ctor_tenv_def] >>
 fs [FLOOKUP_UPDATE, flookup_fupdate_list] >>
 rw [] >>
 fs [EVERY_MEM] >>
 every_case_tac >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP] >>
 imp_res_tac check_freevars_type_name_subst >>
 PairCases_on `y` >>
 fs [] >>
 rw [] >>
 res_tac >> 
 fs [] >>
 fs [check_freevars_def, EVERY_MAP] >>
 fs [EVERY_MEM]);

val type_d_ctMap_ok = Q.store_thm ("type_d_ctMap_ok",
`!tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' tenvM'' tenvC''.
  tenvT_ok tenvT ∧
  type_d tvs tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv'
  ⇒
  ctMap_ok (flat_to_ctMap tenvC') ∧
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list tenvC'))`,
 rw [type_d_cases, flat_to_ctMap_def, flat_to_ctMap_list_def] >>
 imp_res_tac type_p_bvl >>
 rw [bvl2_to_bvl] >>
 imp_res_tac check_ctor_ctMap_ok >>
 TRY (rw [ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >> NO_TAC)
 >- (fs [flat_to_ctMap_def, flat_to_ctMap_list_def] >>
     FIRST_X_ASSUM match_mp_tac >>
     match_mp_tac tenvT_ok_merge >>
     rw [tenvT_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list, flat_tenvT_ok_def] >>
     every_case_tac >>
     fs [] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [check_ctor_tenv_def, EVERY_MEM, MEM_MAP] >>
     PairCases_on `y` >>
     fs [] >>
     rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (imp_res_tac check_ctor_tenv_dups >>
     imp_res_tac check_dup_ctors_distinct >>
     fs [flat_to_ctMap_list_def])
 >- (fs [check_exn_tenv_def, ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
     rw [] >>
     rw [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     metis_tac [check_freevars_type_name_subst]));

val ctMap_ok_pres = Q.store_thm ("ctMap_ok_pres",
`!mn tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' ctMap.
  type_d mn tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv' ∧
  tenvT_ok tenvT ∧
  ctMap_ok ctMap
  ⇒
  ctMap_ok (FUNION (flat_to_ctMap tenvC') ctMap)`,
 rw [] >>
 imp_res_tac type_d_ctMap_ok >>
 rw [] >>
 rw [] >>
 imp_res_tac ctMap_ok_merge_imp >>
 rw []);

val type_d_mod = Q.store_thm ("type_d_mod",
`!mn tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv'.
  type_d mn tdecs tenvT tenvM tenvC tenv d tdecs' tenvT' tenvC' tenv'
  ⇒
  FST tdecs' = {} ∧
  decls_to_mods tdecs' ⊆ { mn }`,
 rw [type_d_cases, decls_to_mods_def, SUBSET_DEF,
     flat_to_ctMap_list_def, FDOM_FUPDATE_LIST] >>
 fs [build_ctor_tenv_def, MEM_FLAT, MEM_MAP] >>
 rw [empty_decls_def] >>
 every_case_tac >>
 fs [EXISTS_PROD, empty_decls_def, decls_to_mods_def, mk_id_def, MEM_MAP] >>
 every_case_tac >>
 fs [GSPECIFICATION]);

val type_d_ctMap_disjoint = Q.store_thm ("type_d_ctMap_disjoint",
`type_d mn tdecs1 tenvT tenvM tenvC tenv d tdecs1' tenvT' tenvC' tenv' ∧
 consistent_ctMap tdecs1 ctMap
 ⇒
 DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM ctMap) ∧
 DISJOINT (IMAGE SND (FDOM (flat_to_ctMap tenvC'))) (IMAGE SND (FDOM ctMap))`,
 rw [type_d_cases, DISJOINT_DEF, EXTENSION, flat_to_ctMap_def, FDOM_FUPDATE_LIST, 
     flat_to_ctMap_list_def] >>
 rw [MEM_MAP] >>
 fs [FORALL_PROD, consistent_ctMap_def, RES_FORALL] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 res_tac >>
 every_case_tac >>
 fs [build_ctor_tenv_def, MEM_MAP, MEM_FLAT] >>
 rw [] >>
 PairCases_on `y` >>
 fs [MEM_MAP] >>
 PairCases_on `y` >>
 fs [MEM_MAP, FORALL_PROD] >>
 rw [] >>
 metis_tac []);

(* ---------- type_ds ---------- *)

val type_ds_tenv_ok = Q.store_thm ("type_ds_tenv_ok",
`!tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'.
  type_ds tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv' ⇒
  (num_tvs tenv = 0) ⇒
  tenv_ok (bind_var_list2 tenv' Empty)`,
 ho_match_mp_tac type_ds_ind >>
 rw []
 >- (rw [bind_var_list2_def, tenv_ok_def])
 >- (imp_res_tac type_d_tenv_ok >>
     fs [bvl2_append, num_tvs_bvl2] >>
     metis_tac [tenv_ok_bvl2]));

val type_ds_mod = Q.store_thm ("type_ds_mod",
`!mn tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'.
  type_ds mn tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'
  ⇒
  FST tdecs' = {} ∧
  decls_to_mods tdecs' ⊆ {mn}`,
 induct_on `ds` >>
 rw [Once type_ds_cases]
 >- rw [decls_to_mods_def, empty_decls_def, SUBSET_DEF, FDOM_FUPDATE_LIST, MEM_MAP]
 >- rw [decls_to_mods_def, empty_decls_def, SUBSET_DEF, FDOM_FUPDATE_LIST, MEM_MAP] >>
 imp_res_tac type_d_mod >>
 res_tac >>
 fs [] >>
 PairCases_on `decls''` >>
 PairCases_on `decls'` >>
 fs [union_decls_def, decls_to_mods_def] >>
 rpt (pop_assum mp_tac) >>
 ONCE_REWRITE_TAC [SUBSET_DEF] >>
 REWRITE_TAC [GSPECIFICATION] >>
 rw_tac (bool_ss) [] >>
 metis_tac []);

val type_ds_ctMap_ok = Q.store_thm ("type_ds_ctMap_ok",
`!tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'.
  type_ds tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv' 
  ⇒
  tenvT_ok tenvT 
  ⇒
  ctMap_ok (flat_to_ctMap tenvC')`,
 ho_match_mp_tac type_ds_strongind >>
 rw [] 
 >- rw [ctMap_ok_def, flat_to_ctMap_def, flat_to_ctMap_list_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]
 >- (imp_res_tac type_d_ctMap_ok >>
     imp_res_tac type_d_tenvT_ok >>
     fs [flat_to_ctMap_def] >>
     fs [ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
     `tenvT_ok (merge_mod_env (FEMPTY,tenvT') tenvT)`
            by (match_mp_tac tenvT_ok_merge >>
                rw [tenvT_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]) >>
     fs [tenvT_ok_def] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     fs [flat_to_ctMap_list_def, ALOOKUP_APPEND, REVERSE_APPEND] >>
     every_case_tac >>
     fs [] >>
     rw []));

val type_ds_tenvC_ok = Q.store_thm ("type_ds_tenvC_ok",
`!tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'.
  type_ds tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv' ⇒
  tenvT_ok tenvT ⇒
  flat_tenvC_ok tenvC'`,
 ho_match_mp_tac type_ds_strongind >>
 rw [] 
 >- rw [flat_tenvC_ok_def]
 >- (imp_res_tac type_d_ctMap_ok >>
     imp_res_tac type_d_tenvT_ok >>
     `tenvC_ok ([],cenv')` by metis_tac [ctMap_ok_tenvC_ok, MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     fs [flat_tenvC_ok_def, tenvC_ok_def, tenvT_ok_merge] >>
     fs [tenvT_ok_def] >>
     FIRST_X_ASSUM match_mp_tac >>
     match_mp_tac tenvT_ok_merge >>
     rw [tenvT_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]));

val type_ds_tenvT_ok = Q.store_thm ("type_ds_tenvT_ok",
`!tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv'.
  type_ds tvs tdecs tenvT tenvM tenvC tenv ds tdecs' tenvT' tenvC' tenv' ⇒
  tenvT_ok tenvT
  ⇒
  flat_tenvT_ok tenvT'`,
 ho_match_mp_tac type_ds_strongind >>
 rw []  >>
 imp_res_tac type_d_tenvT_ok >>
 rw [flat_tenvT_ok_def] >>
 fs [flat_tenvT_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list, FLOOKUP_FUNION] >>
 rw [] >>
 every_case_tac >>
 fs []
 >- metis_tac [] >>
 `tenvT_ok (FEMPTY:tvarN |-> flat_tenvT,tenvT')`
        by (fs[tenvT_ok_def,flat_tenvT_ok_def] >>
            fs[FEVERY_FEMPTY,FEVERY_ALL_FLOOKUP] >>
            metis_tac []) >>
  fs[flat_tenvT_ok_def]>>
  Q.ISPECL_THEN[`FEMPTY:(tvarN |-> flat_tenvT),tenvT'`,`tenvT`] assume_tac tenvT_ok_merge >>
  metis_tac[]);

(* ---------- type_specs ---------- *)

val type_specs_tenv_ok = Q.store_thm ("type_specs_tenv_ok",
`!tvs tenvT specs decls' tenvT' tenvC' tenv'.
  type_specs tvs tenvT specs decls' tenvT' tenvC' tenv' 
  ⇒
  tenv_ok (bind_var_list2 tenv' Empty) ∧
  (tenvT_ok tenvT ⇒ flat_tenvT_ok tenvT')`,
 ho_match_mp_tac type_specs_ind >>
 rw [bind_var_list2_def, tenv_ok_def]
 >- rw [flat_tenvT_ok_def, FEVERY_ALL_FLOOKUP]
 >- (rw [bind_var_list2_def, bind_tenv_def, tenv_ok_def, num_tvs_bvl2, num_tvs_def] >>
     induct_on `tenv'` >>
     rw []
     >- (rw [bind_var_list2_def, bind_tenv_def, tenv_ok_def, num_tvs_bvl2, num_tvs_def] >>
         match_mp_tac check_freevars_subst_single >>
         rw [LENGTH_GENLIST, EVERY_MAP] >>
         rw [EVERY_MEM] >>
         fs [MEM_GENLIST, check_freevars_def] >>
         metis_tac [check_freevars_add, DECIDE ``!x:num. x ≥ 0``])
     >- (PairCases_on `h` >>
         fs [bind_var_list2_def, bind_tenv_def, tenv_ok_def, num_tvs_bvl2, num_tvs_def]))
 >- (`flat_tenvT_ok tenvT'` 
            by (first_x_assum match_mp_tac >>
                match_mp_tac tenvT_ok_merge >>
                rw [tenvT_ok_def, FEVERY_FEMPTY, flat_tenvT_ok_def,
                    FEVERY_ALL_FLOOKUP, flookup_fupdate_list, FLOOKUP_UPDATE] >>
                every_case_tac >>
                imp_res_tac ALOOKUP_MEM >>
                fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
                rw [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
     fs [FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, flookup_fupdate_list,FLOOKUP_UPDATE, flat_tenvT_ok_def] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     TRY (first_x_assum match_mp_tac >>
          qexists_tac `k` >>
          simp [] >>
          NO_TAC) >>
     imp_res_tac ALOOKUP_MEM >>
     fs [check_ctor_tenv_def, EVERY_MEM, MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (fs [flat_tenvT_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw []
     >- (match_mp_tac check_freevars_type_name_subst >>
         rw []) >>
     fs [PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     qexists_tac `k` >>
     simp [] >>
     match_mp_tac tenvT_ok_merge >>
     rw [tenvT_ok_def, FEVERY_FEMPTY, flat_tenvT_ok_def, FEVERY_FUPDATE] >>
     match_mp_tac check_freevars_type_name_subst >>
     rw [])
 >- (fs [flat_tenvT_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     fs [check_freevars_def, EVERY_MAP, EVERY_MEM] >>
     fs [PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     qexists_tac `k` >>
     simp [] >>
     match_mp_tac tenvT_ok_merge >>
     rw [tenvT_ok_def, FEVERY_FEMPTY, flat_tenvT_ok_def, FEVERY_FUPDATE] >>
     fs [check_freevars_def, EVERY_MAP, EVERY_MEM]));

val type_specs_no_mod = Q.store_thm ("type_specs_no_mod",
`!mn tenvT specs decls' flat_tenvT tenvC tenv.
  type_specs mn tenvT specs decls' flat_tenvT tenvC tenv ⇒
  FST decls' = {}`,
 ho_match_mp_tac type_specs_strongind >>
 rw [empty_decls_def] >>
 imp_res_tac type_d_mod >>
 PairCases_on `decls'` >>
 fs [union_decls_def]);

(* closed *)

val _ = Parse.overload_on("tmenv_dom",``λmenv:tenvM. {Long m x | (m,x) | ∃e.  FLOOKUP menv m = SOME e ∧ MEM x (MAP FST e)}``);

open boolSimps evalPropsTheory

val tenv_names_def = Define`
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)`
val _ = export_rewrites["tenv_names_def"]

val lookup_tenv_names = store_thm("lookup_tenv_names",
  ``∀tenv n inc x. lookup_tenv n inc tenv = SOME x ⇒ n ∈ tenv_names tenv``,
  Induct >> simp[lookup_tenv_def] >> metis_tac[])

val tenv_names_bind_var_list = store_thm("tenv_names_bind_var_list",
  ``∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2``,
  ho_match_mp_tac bind_var_list_ind >>
  simp[bind_var_list_def,bind_tenv_def,EXTENSION] >>
  metis_tac[])

val tenv_names_bind_var_list2 = store_thm("tenv_names_bind_var_list2",
  ``∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv``,
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >> simp[bind_var_list2_def,bind_tenv_def] >>
  simp[EXTENSION] >> metis_tac[])

val type_p_closed = prove(
  ``(∀tvs tcenv p t tenv.
       type_p tvs tcenv p t tenv ⇒
       pat_bindings p [] = MAP FST tenv) ∧
    (∀tvs cenv ps ts tenv.
      type_ps tvs cenv ps ts tenv ⇒
      pats_bindings ps [] = MAP FST tenv)``,
  ho_match_mp_tac type_p_ind >>
  simp[astTheory.pat_bindings_def] >>
  rw[] >> fs[SUBSET_DEF] >>
  rw [Once evalPropsTheory.pat_bindings_accum]);

val type_funs_dom = Q.prove (
  `!tenvM tenvC tenv funs tenv'.
    type_funs tenvM tenvC tenv funs tenv'
    ⇒
    IMAGE FST (set funs) = IMAGE FST (set tenv')`,
   Induct_on `funs` >>
   rw [Once type_e_cases] >>
   rw [] >>
   metis_tac []);

val type_e_closed = prove(
  ``(∀tmenv tcenv tenv e t.
      type_e tmenv tcenv tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)) ∧
    (∀tmenv tcenv tenv es ts.
      type_es tmenv tcenv tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)) ∧
    (∀tmenv tcenv tenv funs ts.
      type_funs tmenv tcenv tenv funs ts ⇒
      FV_defs funs ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_e_strongind >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP] >>
    rw[] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac) >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[t_lookup_var_id_def] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[MEM_FLAT,MEM_MAP,EXISTS_PROD] >-
      metis_tac[lookup_tenv_names] >>
    BasicProvers.CASE_TAC >> fs[] >> 
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD] >>
    rw [] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac [] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP] >>
    rw[] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac) >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >> metis_tac[]) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def,bind_tenv_def] >>
    every_case_tac >>
    fs [opt_bind_tenv_def] >>
    metis_tac[] ) >>
    (* COMPLETENESS
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def,bind_tenv_def] >>
    every_case_tac >>
    fs [opt_bind_tenv_def] >>
    metis_tac[] ) >> *)
  strip_tac >- (
    simp[tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac type_funs_dom >>
    fs [SUBSET_DEF] >>
    rw [] >>
    res_tac >>
    fs [MEM_MAP] >>
    `tenv_names (bind_tvar tvs tenv) = tenv_names tenv` 
               by (rw [bind_tvar_def] >>
                   every_case_tac >>
                   fs [tenv_names_def]) >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [EXTENSION] >>
    metis_tac []) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  simp[] >>
  rw [SUBSET_DEF,bind_tenv_def] >>
  res_tac >>
  fsrw_tac[DNF_ss][MEM_MAP,FV_defs_MAP,UNCURRY] >>
  rw [] >>
  metis_tac []);

val type_d_closed = prove(
  ``∀mno decls tenvT tmenv tcenv tenv d w x y z.
      type_d mno decls tenvT tmenv tcenv tenv d w x y z ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_d_ind >>
  strip_tac >- (
    simp[bind_tvar_def] >>
    rpt gen_tac >>
    Cases_on`tvs=0`>>simp[]>>strip_tac>>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[]) >>
  strip_tac >- (
    rw [] >>
    imp_res_tac (CONJUNCT2 type_e_closed) >>
    fs[tenv_names_bind_var_list,LET_THM] >>
    `tenv_names (bind_tvar tvs tenv) = tenv_names tenv`
              by (rw [bind_tvar_def] >>
                  every_case_tac >>
                  rw [tenv_names_def]) >>
    fs[SUBSET_DEF] >> 
    rw [] >>
    fs [MEM_MAP] >>
    res_tac >>
    rw [] >>
    imp_res_tac type_funs_dom >>
    fs [EXTENSION] >>
    metis_tac[]) >>
  simp[]);

val type_d_new_dec_vs = Q.prove (
  `!mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv'.
    type_d mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv'
    ⇒
    set (new_dec_vs d) = set (MAP FST tenv')`,
   rw [type_d_cases, new_dec_vs_def] >>
   rw [new_dec_vs_def] >>
   imp_res_tac type_p_closed >>
   rw [tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
   fs [LET_THM, LIST_TO_SET_MAP, FST_pair, IMAGE_COMPOSE] >>
   metis_tac [type_funs_dom]);

val type_ds_closed = prove(
  ``∀mn decls tenvT tmenv cenv tenv ds w x y z. type_ds mn decls tenvT tmenv cenv tenv ds w x y z ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_ds_ind >>
  rw [FV_decs_def] >>
  imp_res_tac type_d_closed >>
  fs [tenv_names_bind_var_list2] >>
  rw [SUBSET_DEF] >>
  `x ∈ IMAGE Short (set (MAP FST tenv')) ∪ IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv`
           by fs [SUBSET_DEF] >>
  fs [] >>
  rw [] >>
  fs[MEM_MAP] >>
  metis_tac [type_d_new_dec_vs,MEM_MAP]);

val type_top_closed = store_thm("type_top_closed",
  ``∀decls tenvT tmenv tcenv tenv top decls' tT' tm' tc' te'.
      type_top decls tenvT tmenv tcenv tenv top decls' tT' tm' tc' te'
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    metis_tac [type_d_closed]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac type_ds_closed >>
  fs[])

val type_env_dom = Q.prove (
  `!ctMap tenvS env tenv.
    type_env ctMap tenvS env tenv ⇒
    IMAGE Short (set (MAP FST env)) = IMAGE Short (tenv_names tenv)`,
   induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   fs [tenv_names_def] >>
   fs [bind_tenv_def, tenv_names_def] >>
   rw [] >>
   rw [] >>
   metis_tac []);

val weakM_dom = Q.prove (
  `!tenvM1 tenvM2.
    weakM tenvM1 tenvM2
    ⇒
    tmenv_dom tenvM2 ⊆ tmenv_dom tenvM1`,
   rw [weakM_def, SUBSET_DEF] >>
   res_tac >>
   rw [] >>
   fs [weakE_def] >>
   qpat_assum `!x. P x` (mp_tac o Q.SPEC `x'`) >>
   every_case_tac >>
   fs [ALOOKUP_FAILS] >>
   rw [] >>
   imp_res_tac ALOOKUP_MEM >>
   fs [MEM_MAP] >>
   metis_tac [FST, pair_CASES]);

val type_env_dom2 = Q.prove (
  `!ctMap tenvS env tenv.
    type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇒
    (set (MAP FST env) = set (MAP FST tenv))`,
   induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   fs [bind_var_list2_def, tenv_names_def] >>
   fs [bind_tenv_def, tenv_names_def] >>
   rw [] >>
   rw [] >>
   cases_on `tenv` >>
   TRY (PairCases_on `h`) >>
   fs [bind_var_list2_def, bind_tenv_def] >>
   metis_tac []);

val consistent_mod_env_dom = Q.prove (
  `!tenvS tenvC envM tenvM.
    consistent_mod_env tenvS tenvC envM tenvM
    ⇒
    (tmenv_dom tenvM = {Long m x | ∃e. ALOOKUP envM m = SOME e ∧ MEM x (MAP FST e)})`,
   induct_on `envM` >>
   rw []
   >- (Cases_on `tenvM` >>
       fs [Once type_v_cases]) >>
   pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
   rw [] >>
   res_tac >>
   rw [] >>
   imp_res_tac type_env_dom2 >>
   fs [EXTENSION, FLOOKUP_UPDATE] >>
   rw [] >>
   eq_tac >>
   rw [] >>
   every_case_tac >>
   rw [] >>
   fs [MEM_MAP] >>
   rw [] >>
   res_tac >>
   fs [] >>
   metis_tac []);

val type_sound_inv_closed = Q.store_thm ("type_sound_inv_closed",
  `∀top rs new_tenvM new_tenvC new_tenv new_decls new_tenvT decls' store.
    type_top rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top new_decls new_tenvT new_tenvM new_tenvC new_tenv ∧
    type_sound_invariants NONE (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,decls',rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE,store)
    ⇒
    FV_top top ⊆ all_env_dom (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)`,
  rw [] >>
  imp_res_tac type_top_closed >>
  `(?err. r = Rerr err) ∨ (?menv env. r = Rval (menv,env))`
          by (cases_on `r` >>
              rw [] >>
              PairCases_on `a` >>
              fs [])  >>
  fs [all_env_dom_def, type_sound_invariants_def, update_type_sound_inv_def] >>
  rw [] >>
  imp_res_tac weakM_dom >>
  imp_res_tac type_env_dom >>
  imp_res_tac (GSYM consistent_mod_env_dom) >>
  fs [] >>
  fs [SUBSET_DEF] >>
  metis_tac []);

val _ = export_theory ();
