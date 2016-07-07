(* Theorems about the type system. *)

open preamble
open libTheory astTheory typeSystemTheory typeSoundInvariantsTheory terminationTheory;
open astPropsTheory;
local open evalPropsTheory in end

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
  srw_tac[][] >>
  cases_on `tenv` >>
  srw_tac[][bind_var_list2_def] >>
  ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS type_v_cases)))] >>
  srw_tac[][bind_var_list2_def] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[bind_var_list2_def] >>
  PairCases_on `h'` >>
  full_simp_tac(srw_ss())[bind_var_list2_def] >>
  metis_tac []);

val type_env_list_rel_append = store_thm("type_env_list_rel_append",
  ``!ctMap tenvS env tenv rest rst.
   type_env ctMap tenvS (env ++ rest) (bind_var_list2 tenv rst) ∧ LENGTH env = LENGTH tenv
     ⇒ LIST_REL (λ(x,v1) (y,n,v2). x = y ∧ type_v n ctMap tenvS v1 v2) env tenv``,
  induct_on `env` >>
  srw_tac[][LENGTH_NIL_SYM] >>
  cases_on `tenv` >> full_simp_tac(srw_ss())[] >>
  PairCases_on`h'` >>
  full_simp_tac(srw_ss())[bind_var_list2_def] >>
  PairCases_on`h`>>simp[] >>
  rator_x_assum`type_env`mp_tac >>
  simp[Once type_v_cases] >>
  srw_tac[][] >>
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
    srw_tac[][] >>
    pop_assum mp_tac >>
    simp[Once type_v_cases] >>
    srw_tac[][] >>
    imp_res_tac type_env_list_rel >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] ) >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  simp[Once type_v_cases] >>
  srw_tac[][] >>
  qsuff_tac`LENGTH (c ++ [n,v]) = LENGTH (e++[n,tvs,t])` >- simp[] >>
  first_x_assum match_mp_tac >>
  simp[bind_var_list2_append,bind_var_list2_def] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC])

val merge_mod_env_assoc = Q.store_thm ("merge_mod_env_assoc",
`∀env1 env2 env3.
  merge_mod_env env1 (merge_mod_env env2 env3) =
  merge_mod_env (merge_mod_env env1 env2) env3`,
srw_tac[][] >>
PairCases_on `env1` >>
PairCases_on `env2` >>
PairCases_on `env3` >>
srw_tac[][merge_mod_env_def, FUNION_ASSOC]);


(* ---------- check_freevars ---------- *)

val check_freevars_add = Q.store_thm ("check_freevars_add",
`(!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)`,
ho_match_mp_tac check_freevars_ind >>
srw_tac[][check_freevars_def] >-
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
 srw_tac[][check_freevars_def, type_subst_def, EVERY_MAP]
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[check_freevars_def, ALOOKUP_FAILS]
     >- (imp_res_tac MEM_ZIP >>
         full_simp_tac(srw_ss())[MEM_EL] >>
         metis_tac [])
     >- (imp_res_tac ALOOKUP_MEM >>
         imp_res_tac MEM_ZIP >>
         full_simp_tac(srw_ss())[MEM_EL, EVERY_MEM] >>
         srw_tac[][] >>
         metis_tac []))
 >- full_simp_tac(srw_ss())[EVERY_MEM]);

val check_freevars_subst_list = Q.store_thm ("check_freevars_subst_list",
`!dbmax tvs tvs' ts ts'.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars dbmax tvs) ts' ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  EVERY (check_freevars dbmax tvs') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts')`,
induct_on `ts'` >>
srw_tac[][] >>
metis_tac [check_freevars_subst_single]);

(* ---------- deBruijn_inc ---------- *)

val deBruijn_inc0 = Q.store_thm ("deBruijn_inc0",
`(!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)`,
ho_match_mp_tac t_induction >>
srw_tac[][deBruijn_inc_def] >>
metis_tac []);

val deBruijn_inc_deBruijn_inc = Q.store_thm ("deBruijn_inc_deBruijn_inc",
`!sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t`,
ho_match_mp_tac deBruijn_inc_ind >>
srw_tac[][deBruijn_inc_def] >>
srw_tac[][] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
full_simp_tac(srw_ss())[]);

val deBuijn_inc_lem1 = Q.prove (
`!sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t`,
ho_match_mp_tac deBruijn_inc_ind >>
srw_tac[][deBruijn_inc_def] >>
srw_tac[][] >-
decide_tac >-
decide_tac >>
induct_on `ts` >>
srw_tac[][]);

val type_subst_deBruijn_inc_single = Q.prove (
`!s t ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  (s = alist_to_fmap (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t)`,
 recInduct type_subst_ind >>
 srw_tac[][deBruijn_inc_def, type_subst_def, check_freevars_def]
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[deBruijn_inc_def, ALOOKUP_NONE]
     >- (imp_res_tac MEM_ZIP >>
         full_simp_tac(srw_ss())[MEM_MAP, MEM_ZIP, MEM_EL] >>
         metis_tac [FST, pair_CASES])
     >- (imp_res_tac ALOOKUP_MEM >>
         ntac 2 (pop_assum mp_tac) >>
         simp [MEM_MAP, MEM_ZIP, MEM_EL, EL_MAP] >>
         metis_tac [FST])
     >- (pop_assum mp_tac >>
         simp [ALOOKUP_ZIP_MAP_SND]))
 >- (srw_tac[][rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     metis_tac []));

val type_subst_deBruijn_inc_list = Q.store_thm ("type_subst_deBruijn_inc_list",
`!ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts')`,
 induct_on `ts'` >>
 srw_tac[][] >>
 metis_tac [type_subst_deBruijn_inc_single]);

val check_freevars_deBruijn_inc = Q.prove (
`!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)`,
ho_match_mp_tac check_freevars_ind >>
srw_tac[][check_freevars_def, deBruijn_inc_def] >>
full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
srw_tac[][check_freevars_def] >>
decide_tac);

val nil_deBruijn_inc = Q.store_thm ("nil_deBruijn_inc",
`∀skip tvs t.
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒
  (deBruijn_inc skip tvs t = t)`,
ho_match_mp_tac deBruijn_inc_ind >>
srw_tac[][deBruijn_inc_def, check_freevars_def] >-
decide_tac >-
(induct_on `ts` >>
     srw_tac[][] >>
     metis_tac []) >-
(induct_on `ts` >>
     srw_tac[][] >>
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
srw_tac[][check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM] >>
full_simp_tac(srw_ss())[MEM_EL] >-
metis_tac [] >>
decide_tac);

val deBruijn_subst_check_freevars2 = Q.store_thm ("deBruijn_subst_check_freevars2",
`!tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
ho_match_mp_tac check_freevars_ind >>
srw_tac[][check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM] >>
full_simp_tac(srw_ss())[MEM_EL] >>
srw_tac[][] >>
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
srw_tac[][check_freevars_def, deBruijn_inc_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM] >>
cases_on `n < LENGTH targs` >>
srw_tac[][deBruijn_subst_def, check_freevars_def] >>
full_simp_tac(srw_ss())[MEM_EL] >-
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
 srw_tac[][deBruijn_subst_def, deBruijn_inc_def, type_subst_def, check_freevars_def]
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[deBruijn_subst_def, deBruijn_inc_def] >>
     ntac 2 (pop_assum mp_tac) >>
     simp [ALOOKUP_ZIP_MAP_SND])
 >- (srw_tac[][rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     metis_tac []));

val type_subst_deBruijn_subst_list = Q.store_thm ("type_subst_deBruijn_subst_list",
`!t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')`,
induct_on `ts''` >>
srw_tac[][] >>
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
srw_tac[][deBruijn_inc_def, deBruijn_subst_def, check_freevars_def] >|
[full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
     metis_tac [],
 srw_tac[][check_freevars_def] >|
     [full_simp_tac(srw_ss())[EVERY_MEM, MEM_EL] >>
          `n - n1 < LENGTH targs` by decide_tac >>
          srw_tac[][EL_MAP] >>
          metis_tac [check_freevars_deBruijn_inc, MEM_EL,
                     arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC],
      decide_tac,
      decide_tac,
      decide_tac]]);

val nil_deBruijn_subst = Q.store_thm ("nil_deBruijn_subst",
`∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)`,
ho_match_mp_tac deBruijn_subst_ind >>
srw_tac[][deBruijn_subst_def, check_freevars_def] >>
induct_on `ts'` >>
srw_tac[][]);

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
srw_tac[][deBruijn_subst_def, deBruijn_inc_def] >>
full_simp_tac(srw_ss())[EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
srw_tac[][] >>
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
srw_tac[][check_freevars_def, deBruijn_inc_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM] >>
srw_tac[][] >>
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
srw_tac[][deBruijn_subst_def, deBruijn_inc_def] >>
srw_tac[][] >>
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
srw_tac[][deBruijn_subst_def, deBruijn_inc_def] >>
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
srw_tac[][deBruijn_subst_def, deBruijn_inc_def] >>
full_simp_tac(srw_ss())[EL_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
srw_tac[][] >>
full_simp_tac (srw_ss()++ARITH_ss) [EL_MAP, deBruijn_subst_def, check_freevars_def] >>
metis_tac [subst_inc_cancel, LENGTH_MAP]);

val deBruijn_subst_id = Q.store_thm ("deBruijn_subst_id",
`(!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts))`,
Induct >>
srw_tac[][deBruijn_subst_def, LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST,
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
srw_tac[][check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM, MEM_EL] >>
metis_tac []);

(* ---------- tenvT stuff ---------- *)
(* type_name_subst, check_type_names, tenv_tabbrev_ok, merge_tenvT *)

val flat_tenv_tabbrev_ok_lookup = Q.prove (
`!tenvT tn tvs t.
  flat_tenv_tabbrev_ok tenvT ∧
  FLOOKUP tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t`,
 srw_tac[][flat_tenv_tabbrev_ok_def] >>
 imp_res_tac FEVERY_FLOOKUP >>
 full_simp_tac(srw_ss())[]);

val tenv_tabbrev_ok_lookup = Q.store_thm ("tenv_tabbrev_ok_lookup",
`!tenvT tn tvs t.
  tenv_tabbrev_ok tenvT ∧
  (lookup_mod_env tn tenvT = SOME (tvs,t))
  ⇒
  check_freevars 0 tvs t`,
 Cases_on `tenvT` >>
 srw_tac[][lookup_mod_env_def, tenv_tabbrev_ok_def] >>
 every_case_tac >>
 imp_res_tac flat_tenv_tabbrev_ok_lookup >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac FEVERY_FLOOKUP >>
 full_simp_tac(srw_ss())[]);

val check_freevars_type_name_subst = Q.store_thm ("check_freevars_type_name_subst",
`!dbmax tvs t tenvT.
  tenv_tabbrev_ok tenvT ∧
  check_type_names tenvT t ∧
  check_freevars dbmax tvs t
  ⇒
  check_freevars dbmax tvs (type_name_subst tenvT t)`,
 recInduct check_freevars_ind >>
 srw_tac[][type_name_subst_def, LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[check_type_names_def, check_freevars_def, EVERY_MAP] >>
 full_simp_tac(srw_ss())[EVERY_MEM] >>
 match_mp_tac check_freevars_subst_single >>
 srw_tac[][EVERY_MAP] >>
 srw_tac[][EVERY_MEM] >>
 imp_res_tac tenv_tabbrev_ok_lookup >>
 metis_tac [check_freevars_add, numeralTheory.numeral_distrib]);

val flat_tenv_tabbrev_ok_merge = Q.prove (
`!tenvT1 tenvT2.
  flat_tenv_tabbrev_ok tenvT1 ∧ flat_tenv_tabbrev_ok tenvT2
  ⇒
  flat_tenv_tabbrev_ok (FUNION tenvT1 tenvT2)`,
 srw_tac[][flat_tenv_tabbrev_ok_def, ALL_DISTINCT_APPEND] >>
 srw_tac[][DISJOINT_DEF, EXTENSION, fevery_funion]);

val tenv_tabbrev_ok_merge = Q.store_thm ("tenv_tabbrev_ok_merge",
`!tenvT1 tenvT2.
  tenv_tabbrev_ok tenvT1 ∧ tenv_tabbrev_ok tenvT2
  ⇒
  tenv_tabbrev_ok (merge_mod_env tenvT1 tenvT2)`,
 srw_tac[][] >>
 PairCases_on `tenvT1` >>
 PairCases_on `tenvT2` >>
 srw_tac[][tenv_tabbrev_ok_def, merge_mod_env_def, ALL_DISTINCT_APPEND] >>
 full_simp_tac(srw_ss())[tenv_tabbrev_ok_def]
 >- (match_mp_tac fevery_funion >>
     full_simp_tac(srw_ss())[]) >>
 metis_tac [flat_tenv_tabbrev_ok_merge]);

(* ---------- tenvC stuff ----------*)
(* lookup_tenvC, flat_tenv_ctor_ok, tenv_ctor_ok *)

val flat_tenv_ctor_ok_merge = Q.prove (
`!tenvC1 tenvC2.
  flat_tenv_ctor_ok (tenvC1 ++ tenvC2) =
  (flat_tenv_ctor_ok tenvC1 ∧ flat_tenv_ctor_ok tenvC2)`,
srw_tac[][flat_tenv_ctor_ok_def, ALL_DISTINCT_APPEND] >>
eq_tac >>
srw_tac[][DISJOINT_DEF, EXTENSION] >>
metis_tac []);

val tenv_ctor_ok_merge = Q.store_thm ("tenv_ctor_ok_merge",
`!tenvC1 tenvC2.
  tenv_ctor_ok (merge_alist_mod_env tenvC1 tenvC2) =
  (tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2)`,
 srw_tac[][] >>
 PairCases_on `tenvC1` >>
 PairCases_on `tenvC2` >>
 srw_tac[][tenv_ctor_ok_def, merge_alist_mod_env_def, ALL_DISTINCT_APPEND] >>
 eq_tac >>
 srw_tac[][EVERY_MEM] >>
 res_tac >>
 metis_tac [flat_tenv_ctor_ok_merge]);

val flat_tenv_ctor_ok_lookup = Q.prove (
`!tenvC cn tvs ts tn.
  flat_tenv_ctor_ok tenvC ∧ (ALOOKUP tenvC cn = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
induct_on `tenvC` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[flat_tenv_ctor_ok_def] >>
every_case_tac >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
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
 srw_tac[][] >>
 PairCases_on `envC2` >>
 cases_on `cn` >>
 full_simp_tac(srw_ss())[lookup_alist_mod_env_def, merge_alist_mod_env_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[ALOOKUP_APPEND]);

val tenv_ctor_ok_lookup = Q.store_thm ("tenv_ctor_ok_lookup",
`!tenvC cn tvs ts tn.
  tenv_ctor_ok tenvC ∧ (lookup_alist_mod_env cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 cases_on `cn` >>
 srw_tac[][] >>
 PairCases_on `tenvC` >>
 full_simp_tac(srw_ss())[lookup_alist_mod_env_def, tenv_ctor_ok_def]
 >- metis_tac [flat_tenv_ctor_ok_lookup] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac flat_tenv_ctor_ok_lookup >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss())[EVERY_MEM] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[]);

val merge_tenvC_empty_assoc = Q.store_thm ("merge_tenvC_empty_assoc",
`!tenvC1 tenvC2 tenvC3.
  merge_alist_mod_env ([],tenvC1) (merge_alist_mod_env ([],tenvC2) tenvC3)
  =
  merge_alist_mod_env ([],tenvC1++tenvC2) tenvC3`,
 srw_tac[][] >>
 PairCases_on `tenvC3` >>
 srw_tac[][merge_alist_mod_env_def]);

val merge_tenvC_empty = Q.store_thm ("merge_tenvC_empty",
`(!tenvC. merge_alist_mod_env ([],[]) tenvC = tenvC)`,
 srw_tac[][] >>
 TRY (PairCases_on `envC`) >>
 TRY (PairCases_on `tenvC`) >>
 srw_tac[][merge_alist_mod_env_def]);

val lookup_tenvC_mod_cons = Q.store_thm ("lookup_tenvC_mod_cons",
`!mn cn mn' flat_envC1 envC1 flat_envC2.
  lookup_alist_mod_env (Long mn cn) ((mn',flat_envC1)::envC1,flat_envC2) =
  if mn = mn' then
    ALOOKUP flat_envC1 cn
  else
    lookup_alist_mod_env (Long mn cn) (envC1,flat_envC2)`,
srw_tac[][lookup_alist_mod_env_def]);

val merge_tenvC_assoc = Q.store_thm ("merge_tenvC_assoc",
`∀tenvC1 tenvC2 tenvC3.
  merge_alist_mod_env tenvC1 (merge_alist_mod_env tenvC2 tenvC3) =
  merge_alist_mod_env (merge_alist_mod_env tenvC1 tenvC2) tenvC3`,
srw_tac[][] >>
PairCases_on `tenvC1` >>
PairCases_on `tenvC2` >>
PairCases_on `tenvC3` >>
srw_tac[][merge_alist_mod_env_def])

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
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def]);

val bind_tvar_rewrites = Q.store_thm ("bind_tvar_rewrites",
`(!tvs e1 e2.
   db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
 (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
 (!n inc tvs e. lookup_tenv_val n inc (bind_tvar tvs e) = lookup_tenv_val n (inc+tvs) e) ∧
 (!tvs e. tenv_val_ok (bind_tvar tvs e) = tenv_val_ok e) ∧
 (!targs tvs e.
   deBruijn_subst_tenvE targs (bind_tvar tvs e) =
   bind_tvar tvs (deBruijn_subst_tenvE targs e))`,
srw_tac[][bind_tvar_def, deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def,
    lookup_tenv_val_def, tenv_val_ok_def]);

val num_tvs_bvl2 = Q.store_thm ("num_tvs_bvl2",
`!tenv1 tenv2. num_tvs (bind_var_list2 tenv1 tenv2) = num_tvs tenv2`,
ho_match_mp_tac bind_var_list2_ind >>
srw_tac[][num_tvs_def, bind_var_list2_def]);

val num_tvs_bind_var_list = Q.store_thm ("num_tvs_bind_var_list",
`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE`,
induct_on `env` >>
srw_tac[][num_tvs_def, bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, num_tvs_def]);

val tenv_val_ok_bind_var_list = Q.store_thm ("tenv_val_ok_bind_var_list",
`!tenvE env.
  tenv_val_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_ok (bind_var_list 0 env tenvE)`,
induct_on `env` >>
srw_tac[][tenv_val_ok_def, bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][tenv_val_ok_def, bind_var_list_def] >>
full_simp_tac(srw_ss())[num_tvs_bind_var_list]);

val tenv_val_ok_bind_var_list2 = Q.store_thm ("tenv_val_ok_bind_var_list2",
`!tenvE env.
  tenv_val_ok tenvE ∧ EVERY (λ(x,n,t). check_freevars (n + num_tvs tenvE) [] t) env
  ⇒
  tenv_val_ok (bind_var_list2 env tenvE)`,
induct_on `env` >>
srw_tac[][tenv_val_ok_def, bind_var_list2_def] >>
PairCases_on `h` >>
srw_tac[][tenv_val_ok_def, bind_var_list2_def] >>
full_simp_tac(srw_ss())[num_tvs_bvl2]);

val lookup_freevars = Q.store_thm ("lookup_freevars",
`!n tenv tvs t.
  tenv_val_ok (bind_var_list2 tenv Empty) ∧
  (ALOOKUP tenv n = SOME (tvs, t))
  ⇒
  check_freevars tvs [] t`,
induct_on `tenv` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[bind_var_list2_def, tenv_val_ok_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
metis_tac [num_tvs_bvl2, arithmeticTheory.ADD_0, num_tvs_def]);

val type_e_freevars_lem3 = Q.prove (
`!tenv tenv' targs n t inc.
  EVERY (check_freevars (num_tvs tenv') []) targs ∧
  (ALOOKUP tenv n = SOME (LENGTH targs,t)) ∧
  tenv_val_ok (bind_var_list2 tenv Empty)
  ⇒
  check_freevars (num_tvs tenv') [] (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
srw_tac[][tenv_val_ok_def, bind_var_list2_def] >>
PairCases_on `h` >>
srw_tac[][] >>
full_simp_tac(srw_ss())[tenv_val_ok_def, bind_var_list2_def] >>
cases_on `h0 = n` >>
full_simp_tac(srw_ss())[] >>
srw_tac[][] >>
metis_tac [deBruijn_subst_check_freevars2, arithmeticTheory.ADD_0, num_tvs_bvl2, num_tvs_def]);

val lookup_tenv_db_merge = Q.store_thm ("lookup_tenv_db_merge",
`!n inc e1 e2.
  lookup_tenv_val n inc (db_merge e1 e2) =
  case lookup_tenv_val n inc e1 of
    | SOME t => SOME t
    | NONE =>
        lookup_tenv_val n (inc + num_tvs e1) e2`,
induct_on `e1` >>
srw_tac[][lookup_tenv_val_def, db_merge_def, num_tvs_def] >>
every_case_tac >>
srw_tac [ARITH_ss] []);

val lookup_tenv_val_deBruijn_subst_tenvE = Q.store_thm ("lookup_tenv_val_deBruijn_subst_tenvE",
`∀n e targs tvs t inc.
  (lookup_tenv_val n inc e = SOME (tvs,t))
  ⇒
  (lookup_tenv_val n inc (deBruijn_subst_tenvE targs e) =
     SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t))`,
induct_on `e` >>
srw_tac[][lookup_tenv_val_def,deBruijn_subst_tenvE_def, deBruijn_inc_def, num_tvs_def] >>
metis_tac [arithmeticTheory.ADD_ASSOC, type_e_subst_lem5]);

val num_tvs_db_merge = Q.store_thm ("num_tvs_db_merge",
`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
induct_on `e1` >>
srw_tac[][num_tvs_def, db_merge_def] >>
decide_tac);

val num_tvs_deBruijn_subst_tenvE = Q.store_thm ("num_tvs_deBruijn_subst_tenvE",
`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE`,
induct_on `tenvE` >>
srw_tac[][deBruijn_subst_tenvE_def, num_tvs_def]);

val lookup_tenv_val_subst_none = Q.prove (
`!n inc e.
 (lookup_tenv_val n inc e = NONE) ⇒
 (lookup_tenv_val n inc (deBruijn_subst_tenvE targs e) = NONE)`,
induct_on `e` >>
srw_tac[][deBruijn_subst_tenvE_def, lookup_tenv_val_def]);

val lookup_tenv_val_inc_some = Q.prove (
`!n inc e tvs t inc2.
   (lookup_tenv_val n inc e = SOME (tvs, t))
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (lookup_tenv_val n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t'))`,
induct_on `e` >>
srw_tac[][deBruijn_inc_def, lookup_tenv_val_def] >>
srw_tac[][] >>
metis_tac [deBruijn_inc_deBruijn_inc]);

val lookup_tenv_val_inc = Q.store_thm ("lookup_tenv_val_inc",
`!x inc tenv tvs t inc2.
  (lookup_tenv_val x inc tenv = SOME (tvs,t))
  ⇒
  (lookup_tenv_val x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t))`,
induct_on `tenv` >>
srw_tac[][lookup_tenv_val_def] >>
srw_tac[][deBruijn_inc_deBruijn_inc] >>
metis_tac [arithmeticTheory.ADD_ASSOC]);

val type_e_freevars_lem2 = Q.prove (
`!tenvE targs n t inc.
  EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
  (lookup_tenv_val n inc tenvE = SOME (LENGTH targs,t)) ∧
  tenv_val_ok tenvE
  ⇒
  check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)`,
induct_on `tenvE` >>
srw_tac[][check_freevars_def, num_tvs_def, lookup_tenv_val_def, tenv_val_ok_def] >>
metis_tac [deBruijn_subst_check_freevars, arithmeticTheory.ADD_ASSOC,
           check_freevars_subst_inc]);

val tenv_val_ok_db_merge = Q.prove (
`!e1 e2. tenv_val_ok (db_merge e1 e2) ⇒ tenv_val_ok e2`,
induct_on `e1` >>
srw_tac[][tenv_val_ok_def, db_merge_def]);

val type_e_subst_lem1 = Q.prove (
`!e n inc t.
  (num_tvs e = 0) ∧
  tenv_val_ok e ∧
  (lookup_tenv_val n inc e = SOME (tvs, deBruijn_inc tvs inc t))
  ⇒
  check_freevars tvs [] t`,
induct_on `e` >>
srw_tac[][lookup_tenv_val_def, num_tvs_def, tenv_val_ok_def] >|
[metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM],
 `check_freevars n [] t0`
          by metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM] >>
     full_simp_tac(srw_ss())[nil_deBruijn_inc] >>
     srw_tac[][] >>
     metis_tac [nil_deBruijn_inc],
 metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]]);

val lookup_tenv_val_freevars = Q.prove (
`!e n inc t tvs.
  tenv_val_ok e ∧
  (lookup_tenv_val n inc e = SOME (tvs, t))
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t`,
induct_on `e` >>
srw_tac[][lookup_tenv_val_def, num_tvs_def, tenv_val_ok_def] >|
[metis_tac [arithmeticTheory.ADD_ASSOC],
 imp_res_tac check_freevars_deBruijn_inc >>
     metis_tac [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM],
 metis_tac []]);

val lookup_tenv_val_inc_tvs = Q.store_thm ("lookup_tenv_val_inc_tvs",
`!tvs l tenv n t.
  tenv_val_ok tenv ∧
  (num_tvs tenv = 0)
  ⇒
  ((lookup_tenv_val n 0 tenv = SOME (l,t))
   =
   (lookup_tenv_val n tvs tenv = SOME (l,t)))`,
induct_on `tenv` >>
srw_tac[][lookup_tenv_val_def, num_tvs_def, tenv_val_ok_def] >>
eq_tac >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
metis_tac [nil_deBruijn_inc, deBruijn_inc0]);

val deBruijn_subst_E_bind_var_list = Q.store_thm ("deBruijn_subst_E_bind_var_list",
`!tenv1 tenv2 tvs.
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
  =
  bind_var_list tvs
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
          (deBruijn_subst_tenvE targs tenv2)`,
induct_on `tenv1` >>
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, deBruijn_subst_tenvE_def, num_tvs_bind_var_list]);

val db_merge_bind_var_list = Q.store_thm ("db_merge_bind_var_list",
`!tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3)`,
induct_on `tenv1` >>
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, db_merge_def]);

val tenv_val_ok_bvl2 = Q.store_thm ("tenv_val_ok_bvl2",
`!tenv tenv'.
  tenv_val_ok (bind_var_list2 tenv Empty) ∧ tenv_val_ok tenv'
  ⇒
  tenv_val_ok (bind_var_list2 tenv tenv')`,
ho_match_mp_tac bind_var_list2_ind >>
srw_tac[][bind_var_list2_def, tenv_val_ok_def, num_tvs_bvl2, num_tvs_def] >>
`tvs + num_tvs tenv' ≥ tvs` by decide_tac >>
metis_tac [check_freevars_add]);

val bvl2_lookup = Q.store_thm ("bvl2_lookup",
`!n tenv. ALOOKUP tenv n = lookup_tenv_val n 0 (bind_var_list2 tenv Empty)`,
 induct_on `tenv` >>
 srw_tac[][bind_var_list2_def, lookup_tenv_val_def] >>
 PairCases_on `h` >>
 srw_tac[][bind_var_list2_def, lookup_tenv_val_def, deBruijn_inc0]);

val lookup_bvl2 = store_thm("lookup_bvl2",
 ``∀n tenv tenv2. lookup_tenv_val n m (bind_var_list2 tenv tenv2) =
                  case ALOOKUP tenv n of
                  | SOME (x,y) => SOME (x,deBruijn_inc x m y)
                  | NONE => lookup_tenv_val n m tenv2``,
  induct_on`tenv` >>
  srw_tac[][bind_var_list2_def, lookup_tenv_val_def] >>
  PairCases_on`h` >>
  srw_tac[][bind_var_list2_def, lookup_tenv_val_def])

val bvl2_append = Q.store_thm ("bvl2_append",
`!tenv1 tenv3 tenv2.
  (bind_var_list2 (tenv1 ++ tenv2) tenv3 =
   bind_var_list2 tenv1 (bind_var_list2 tenv2 tenv3))`,
ho_match_mp_tac bind_var_list2_ind >>
srw_tac[][bind_var_list2_def]);

val bvl2_to_bvl = Q.store_thm ("bvl2_to_bvl",
`!tvs tenv tenv'. bind_var_list2 (tenv_add_tvs tvs tenv) tenv' = bind_var_list tvs tenv tenv'`,
ho_match_mp_tac bind_var_list_ind >>
srw_tac[][bind_var_list_def, bind_var_list2_def, tenv_add_tvs_def]);

val type_lookup_lem4 = Q.prove (
`!tvs l tenv n t.
  tenv_val_ok tenv ∧
  (num_tvs tenv = 0) ∧
  (lookup_tenv_val n 0 tenv = SOME (l,t))
  ⇒
  (lookup_tenv_val n tvs tenv = SOME (l,t))`,
induct_on `tenv` >>
srw_tac[][lookup_tenv_val_def, num_tvs_def, tenv_val_ok_def] >-
metis_tac [] >>
full_simp_tac(srw_ss())[] >>
metis_tac [nil_deBruijn_inc]);

(* ---------- tenv_mod stuff ---------- *)

val tenv_mod_ok_lookup = Q.store_thm ("tenv_mod_ok_lookup",
`!n tenvM tenvC tenv.
  tenv_mod_ok tenvM ∧
  (FLOOKUP tenvM n = SOME tenv) ⇒
  tenv_val_ok (bind_var_list2 tenv Empty)`,
 induct_on `tenvM` >>
 srw_tac[][tenv_mod_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_UPDATE] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 metis_tac []);

val type_e_freevars_lem4 = Q.prove (
`!tenv targs n t.
  EVERY (check_freevars (num_tvs tenv.v) []) targs ∧
  t_lookup_var_id n tenv = SOME (LENGTH targs,t) ∧
  tenv_mod_ok tenv.m ∧
  tenv_val_ok tenv.v
  ⇒
  check_freevars (num_tvs tenv.v) [] (deBruijn_subst 0 targs t)`,
srw_tac[][t_lookup_var_id_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
imp_res_tac tenv_mod_ok_lookup >>
metis_tac [type_e_freevars_lem3,type_e_freevars_lem2,arithmeticTheory.ADD]);

val freevars_t_lookup_var_id = Q.store_thm ("freevars_t_lookup_var_id",
`!tenv tvs n t.
  t_lookup_var_id n tenv = SOME (tvs,t) ∧
  tenv_mod_ok tenv.m ∧
  tenv_val_ok tenv.v
  ⇒
  check_freevars (num_tvs tenv.v + tvs) [] t`,
srw_tac[][t_lookup_var_id_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >|
[imp_res_tac lookup_tenv_val_freevars >>
     full_simp_tac (srw_ss()++ARITH_ss) [],
 imp_res_tac tenv_mod_ok_lookup >>
     imp_res_tac lookup_freevars >>
     `num_tvs tenv.v + tvs ≥ tvs` by decide_tac >>
     metis_tac [check_freevars_add]]);

val tenv_mod_ok_pres = Q.store_thm ("tenv_mod_ok_pres",
`∀tenvM mn tenv.
  tenv_mod_ok tenvM ∧
  tenv_val_ok (bind_var_list2 tenv Empty)
  ⇒
  tenv_mod_ok (tenvM |+ (mn,tenv))`,
 induct_on `tenvM` >>
 srw_tac[][tenv_mod_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_UPDATE] >>
 cases_on `mn = k` >>
 full_simp_tac(srw_ss())[] >>
 metis_tac []);

(* ---------- type_op ---------- *)

val type_op_cases = Q.store_thm ("type_op_cases",
`!op ts t3.
  type_op op ts t3 ⇔
  (((∃op'. op = Opn op') ∧ ts = [Tint; Tint] ∧ (t3 = Tint)) ∨
   ((∃op'. op = Opb op') ∧ ts = [Tint; Tint] ∧ (t3 = Tapp [] (TC_name (Short "bool")))) ∨
   (∃wz. (∃op'. op = Opw wz op') ∧ ts = [Tword wz; Tword wz] ∧ (t3 = Tword wz)) ∨
   (∃wz. (∃sh n. op = Shift wz sh n) ∧ ts = [Tword wz] ∧ (t3 = Tword wz)) ∨
   ((op = Opapp) ∧ ?t2. ts = [Tfn t2 t3;t2]) ∨
   ((op = Equality) ∧ ?t1. ts = [t1; t1] ∧ (t3 = Tapp [] (TC_name (Short "bool")))) ∨
   ((op = Opassign) ∧ ?t2. ts = [Tref t2; t2] ∧ (t3 = Tapp [] TC_tup)) ∨
   ((op = Opref) ∧ ?t1. ts = [t1] ∧ t3 = Tref t1) ∨
   ((op = Opderef) ∧ ts = [Tref t3]) ∨
   ((op = Aw8alloc) ∧ ts = [Tint; Tword8] ∧ t3 = Tword8array) ∨
   ((op = Aw8sub) ∧ ts = [Tword8array; Tint] ∧ t3 = Tword8) ∨
   ((op = Aw8length) ∧ ts = [Tword8array] ∧ t3 = Tint) ∨
   ((op = Aw8update) ∧ ts = [Tword8array; Tint; Tword8] ∧ t3 = Tapp [] TC_tup) ∨
   (∃wz. (op = WordFromInt wz) ∧ ts = [Tint] ∧ t3 = Tword wz) ∨
   (∃wz. (op = WordToInt wz) ∧ ts = [Tword wz] ∧ t3 = Tint) ∨
   ((op = Ord) ∧ ts = [Tchar] ∧ t3 = Tint) ∨
   ((op = Chr) ∧ ts = [Tint] ∧ t3 = Tchar) ∨
   ((∃op'. op = Chopb op') ∧ ts = [Tchar; Tchar] ∧ (t3 = Tapp [] (TC_name (Short "bool")))) ∨
   ((op = Explode) ∧ ts = [Tstring] ∧ t3 = Tapp [Tchar] (TC_name (Short "list"))) ∨
   ((op = Implode) ∧ ts = [Tapp [Tchar] (TC_name (Short "list"))] ∧ t3 = Tstring) ∨
   ((op = Strlen) ∧ ts = [Tstring] ∧ t3 = Tint) ∨
   ((op = VfromList) ∧ ?t2. ts = [Tapp [t2] (TC_name (Short "list"))] ∧ t3 = Tapp [t2] TC_vector) ∨
   ((op = Vsub) ∧ ts = [Tapp [t3] TC_vector; Tint]) ∨
   ((op = Vlength) ∧ ?t1. ts = [Tapp [t1] TC_vector] ∧ t3 = Tint) ∨
   ((op = Aalloc) ∧ ?t1. ts = [Tint; t1] ∧ t3 = Tapp [t1] TC_array) ∨
   ((op = Asub) ∧ ts = [Tapp [t3] TC_array; Tint]) ∨
   ((op = Alength) ∧ ?t1. ts = [Tapp [t1] TC_array] ∧ t3 = Tint) ∨
   ((op = Aupdate) ∧ ?t1. ts = [Tapp [t1] TC_array; Tint; t1] ∧ t3 = Tapp [] TC_tup) ∨
   ((?n. op = FFI n) ∧ ts = [Tword8array] ∧ t3 = Tapp [] TC_tup))`,
 srw_tac[][type_op_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[Tchar_def,Tword_def,Tword8_def,Tword64_def,TC_word_def] >>
 metis_tac []);

(* ---------- type_p ---------- *)

val type_ps_length = Q.store_thm ("type_ps_length",
`∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)`,
induct_on `ps` >>
srw_tac[][Once type_p_cases] >>
srw_tac[][] >>
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
srw_tac[][check_freevars_def, bind_tvar_def, bind_var_list_def, Tchar_def, Tword64_def, Tword_def] >>
metis_tac []);

val type_p_subst = Q.store_thm ("type_p_subst",
`(!n tenv p t new_bindings. type_p n tenv p t new_bindings ⇒
    !targs' inc tvs targs.
    tenv_tabbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenv
           p
           (deBruijn_subst inc targs' t)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings)) ∧
 (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings ⇒
    !targs' inc targs tvs.
    tenv_tabbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_ps (inc +  tvs) tenv
           ps
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings))`,
 ho_match_mp_tac type_p_strongind >>
 srw_tac[][] >>
 ONCE_REWRITE_TAC [type_p_cases] >>
 simp [deBruijn_subst_def, OPTION_MAP_DEF, Tchar_def, Tword_def, Tword64_def]
 >- metis_tac [check_freevars_lem]
 >- (rw [] >>
     srw_tac[][EVERY_MAP] >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     srw_tac[][]
     >- metis_tac [check_freevars_lem, EVERY_MEM]
     >- metis_tac [type_subst_deBruijn_subst_list, tenv_ctor_ok_lookup])
 >- metis_tac []
 >- (conj_asm1_tac
     >- (match_mp_tac nil_deBruijn_subst >>
         match_mp_tac check_freevars_type_name_subst >>
         `! n:num . n ≥ 0` by decide_tac >>
         rw []
         >- metis_tac [check_freevars_add]) >>
     metis_tac [])
 >- metis_tac []);

val type_p_bvl = Q.store_thm ("type_p_bvl",
`(!tvs tenvC p t tenv. type_p tvs tenvC p t tenv ⇒
  !tenv'. tenv_val_ok tenv' ⇒ tenv_val_ok (bind_var_list tvs tenv tenv')) ∧
 (!tvs tenvC ps ts tenv. type_ps tvs tenvC ps ts tenv ⇒
  !tenv'. tenv_val_ok tenv' ⇒ tenv_val_ok (bind_var_list tvs tenv tenv'))`,
ho_match_mp_tac type_p_ind >>
srw_tac[][bind_var_list_def, tenv_val_ok_def, num_tvs_def, bind_var_list_append] >>
`tvs + num_tvs tenv' ≥ tvs` by decide_tac >>
metis_tac [check_freevars_add]);

val type_p_tenvV_indep = Q.store_thm ("type_p_tenvV_indep",
`(!p tvs tenv t ntenv tenvV.
  type_p tvs tenv p t ntenv = type_p tvs (tenv with v := tenvV) p t ntenv) ∧
 (!ps tvs tenv t ntenv tenvV.
  type_ps tvs tenv ps t ntenv = type_ps tvs (tenv with v := tenvV) ps t ntenv)`,
 Induct >>
 rw [] >>
 ONCE_REWRITE_TAC [type_p_cases] >>
 simp [] >>
 metis_tac []);

(* ---------- type_e, type_es, type_funs ---------- *)

val type_es_list_rel = Q.store_thm ("type_es_list_rel",
`!es ts tenv. type_es tenv es ts = LIST_REL (type_e tenv) es ts`,
 induct_on `es` >>
 srw_tac[][] >>
 srw_tac[][Once type_e_cases]);

val type_es_length = Q.store_thm ("type_es_length",
`∀tenv es ts.
  type_es tenv es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
srw_tac[][Once type_e_cases] >>
srw_tac[][] >>
metis_tac []);

val tenv_ok_bind_var_list_tvs = Q.store_thm ("tenv_ok_bind_var_list_tvs",
`!funs tenv env tvs env'.
  type_funs (tenv with v := bind_var_list 0 env' (bind_tvar tvs tenv.v)) funs env ∧
  tenv_val_ok tenv.v
  ⇒
  tenv_val_ok (bind_var_list tvs env tenv.v)`,
induct_on `funs` >>
srw_tac[][] >>
qpat_assum `type_funs x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
srw_tac[][check_freevars_def, bind_var_list_def, tenv_val_ok_def] >>
cases_on `tvs = 0` >>
full_simp_tac(srw_ss())[check_freevars_def, num_tvs_bind_var_list, bind_tvar_def, num_tvs_def] >>
metis_tac []);

val tenv_ok_bind_var_list_funs = Q.store_thm ("tenv_ok_bind_var_list_funs",
`!funs env tenv tvs env' tenv_val.
  type_funs (tenv with v := bind_var_list 0 env' tenv_val) funs env ∧
  tenv_val_ok tenv_val
  ⇒
  tenv_val_ok (bind_var_list 0 env tenv_val)`,
induct_on `funs` >>
srw_tac[][] >>
qpat_assum `type_funs x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
srw_tac[][check_freevars_def, bind_var_list_def, tenv_val_ok_def] >>
full_simp_tac(srw_ss())[check_freevars_def, num_tvs_bind_var_list] >>
metis_tac []);

val type_e_freevars = Q.store_thm ("type_e_freevars",
`(!tenv e t.
   type_e tenv e t ⇒
   tenv_mod_ok tenv.m ∧
   tenv_val_ok tenv.v ⇒
   check_freevars (num_tvs tenv.v) [] t) ∧
 (!tenv es ts.
   type_es tenv es ts ⇒
   tenv_mod_ok tenv.m ∧
   tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenv.v) []) ts) ∧
 (!tenv funs env.
   type_funs tenv funs env ⇒
   tenv_mod_ok tenv.m ∧
   tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenv.v) []) (MAP SND env))`,
 ho_match_mp_tac type_e_strongind >>
 srw_tac[][check_freevars_def, num_tvs_def, type_op_cases,
     tenv_val_ok_def, bind_tvar_def, bind_var_list_def, opt_bind_name_def] >>
 full_simp_tac(srw_ss())[check_freevars_def,Tchar_def,Tword_def]
 >- rw[Tword64_def,Tword_def,check_freevars_def]
 >- metis_tac [deBruijn_subst_check_freevars]
 >- metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD]
 >- metis_tac [type_e_freevars_lem4, arithmeticTheory.ADD]
 >- (cases_on `pes` >>
     full_simp_tac(srw_ss())[RES_FORALL, num_tvs_bind_var_list] >>
     qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `(FST h, SND h)`) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [type_p_freevars, tenv_val_ok_bind_var_list])
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[num_tvs_def, tenv_val_ok_def])
     (* COMPLETENESS
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[num_tvs_def, tenv_ok_def])
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[num_tvs_def, tenv_ok_def])
     *)
 >- metis_tac [tenv_ok_bind_var_list_funs, num_tvs_bind_var_list]
 (* COMPLETENESS
 >- metis_tac [tenv_ok_bind_var_list_tvs, num_tvs_bind_var_list, bind_tvar_def]
 *));

val type_e_subst = Q.store_thm ("type_e_subst",
`(!tenv e t. type_e tenv e t ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_tabbrev_ok tenv.t ∧
      tenv_mod_ok tenv.m ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      EVERY (check_freevars tvs []) targs ∧
      tenv.v = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_e (tenv with v := db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                   e
                   (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
 (!tenv es ts. type_es tenv es ts ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_tabbrev_ok tenv.t ∧
      tenv_mod_ok tenv.m ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      EVERY (check_freevars tvs []) targs ∧
      tenv.v = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_es (tenv with v := db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                  es
                  (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
 (!tenv funs env. type_funs tenv funs env ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_tabbrev_ok tenv.t ∧
      tenv_mod_ok tenv.m ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      EVERY (check_freevars tvs []) targs ∧
      tenv.v = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_funs (tenv with v := db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                      funs
                      (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env))`,
 ho_match_mp_tac type_e_strongind >>
 srw_tac[][] >>
 ONCE_REWRITE_TAC [type_e_cases] >>
 srw_tac[][deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_name_def,
     bind_tvar_rewrites, num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE] >>
 full_simp_tac(srw_ss())[deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_name_def,
     bind_tvar_rewrites, num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_val_ok_def, Tchar_def] >>
 `tenv_val_ok tenvE2` by metis_tac [tenv_val_ok_db_merge, bind_tvar_def, tenv_val_ok_def]
 >- simp[Tword_def,deBruijn_subst_def]
 >- simp[Tword_def,deBruijn_subst_def,Tword64_def]
 >- metis_tac [check_freevars_lem]
 >- (full_simp_tac(srw_ss())[RES_FORALL] >>
     srw_tac[][] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     qpat_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
     srw_tac[][] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      bindings` >>
     srw_tac[][]
     >- (
       REWRITE_TAC [GSYM type_p_tenvV_indep] >>
       first_assum (mp_tac o MATCH_MP (hd (CONJUNCTS type_p_subst))) >>
       srw_tac[][deBruijn_subst_def])
     >- (pop_assum (qspecl_then [`bind_var_list 0 tenv' tenvE1`, `targs`, `tvs`]
                    (MATCH_MP_TAC o
                     SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                            db_merge_bind_var_list]))  >>
         srw_tac[][] >>
         match_mp_tac tenv_val_ok_bind_var_list >>
         srw_tac[][num_tvs_db_merge, bind_tvar_rewrites] >>
         metis_tac [type_p_freevars]))
 >- (full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
     srw_tac[][] >>
     metis_tac [check_freevars_lem, EVERY_MEM])
 >- metis_tac [type_subst_deBruijn_subst_list, tenv_ctor_ok_lookup]
 >- metis_tac [type_subst_deBruijn_subst_list, tenv_ctor_ok_lookup]
 >- (cases_on `n` >>
     full_simp_tac(srw_ss())[t_lookup_var_id_def] >|
     [imp_res_tac lookup_tenv_val_freevars >>
          full_simp_tac(srw_ss())[lookup_tenv_db_merge] >>
          cases_on `lookup_tenv_val a 0 tenvE1` >>
          full_simp_tac(srw_ss())[lookup_tenv_val_def, bind_tvar_rewrites, num_tvs_deBruijn_subst_tenvE] >>
          srw_tac[][] >|
          [imp_res_tac lookup_tenv_val_subst_none >>
               srw_tac[][] >>
               imp_res_tac lookup_tenv_val_inc_some >>
               srw_tac[][] >>
               pop_assum (ASSUME_TAC o Q.SPEC `num_tvs tenvE1 + tvs'`) >>
               full_simp_tac(srw_ss())[] >>
               srw_tac[][] >>
               imp_res_tac type_e_subst_lem1 >>
               full_simp_tac(srw_ss())[nil_deBruijn_inc] >>
               qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)` >>
               srw_tac[][] >-
               metis_tac [deBruijn_subst2] >>
               full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM, MEM_MAP] >>
               srw_tac[][] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM],
           imp_res_tac lookup_tenv_val_deBruijn_subst_tenvE >>
               full_simp_tac(srw_ss())[] >>
               srw_tac[][] >>
               full_simp_tac(srw_ss())[nil_deBruijn_subst, num_tvs_db_merge, bind_tvar_rewrites] >>
               full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
               srw_tac[][] >>
               qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)`  >>
               srw_tac[][] >>
               full_simp_tac(srw_ss())[MEM_MAP] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM, type_e_subst_lem7]],
      cases_on `FLOOKUP tenv.m s` >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          qexists_tac `MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs` >>
          srw_tac[][] >|
          [match_mp_tac (hd (CONJUNCTS deBruijn_subst2)) >>
               srw_tac[][] >>
               metis_tac [tenv_mod_ok_lookup, lookup_freevars, arithmeticTheory.ADD, arithmeticTheory.ADD_0],
           full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
               srw_tac[][] >>
               metis_tac [type_e_subst_lem3, EVERY_MEM]]])
 >- (qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'`
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     full_simp_tac(srw_ss())[num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3])
 >- (qpat_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'`
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     full_simp_tac(srw_ss())[num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3])
 >- (full_simp_tac(srw_ss())[type_op_cases] >>
     srw_tac[][] >>
     TRY(cases_on`wz`\\CHANGED_TAC(fs[Tword_def,Tword8_def,Tword64_def])) >>
     full_simp_tac(srw_ss())[deBruijn_subst_def,Tchar_def,Tword_def] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[RES_FORALL] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     srw_tac[][] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     qpat_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
     srw_tac[][] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      bindings` >>
     srw_tac[][] >- (
       REWRITE_TAC [GSYM type_p_tenvV_indep] >>
       metis_tac [type_p_subst]) >>
     pop_assum (MATCH_MP_TAC o
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list,
                                      db_merge_bind_var_list] o
                Q.SPECL [`bind_var_list 0 bindings tenvE1`, `targs`, `tvs`]) >>
     srw_tac[][] >>
     match_mp_tac tenv_val_ok_bind_var_list >>
     srw_tac[][num_tvs_db_merge, bind_tvar_rewrites] >>
     metis_tac [type_p_freevars])
     (* COMPLETENESS
 >- (disj1_tac >>
     srw_tac[][] >>
     qexists_tac `deBruijn_subst (tvs + num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs) t` >>
     qexists_tac `tvs` >>
     srw_tac[][] >|
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
          srw_tac[][bind_tvar_rewrites] >>
          full_simp_tac(srw_ss())[MAP_MAP_o, combinTheory.o_DEF, deBruijn_inc_deBruijn_inc] >>
          metis_tac [],
      every_case_tac >>
          full_simp_tac(srw_ss())[tenv_ok_def] >>
          FIRST_X_ASSUM
                 (MP_TAC o
                  Q.SPECL [`Bind_name x tvs t tenvE1`, `targs`, `tvs'`]) >>
          srw_tac[][bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def,
              num_tvs_def] >>
          imp_res_tac type_e_freevars >>
          full_simp_tac(srw_ss())[tenv_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge]])
          *)
 >- ((* COMPLETENESS disj2_tac >> *)
     srw_tac[][] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     full_simp_tac(srw_ss())[deBruijn_inc0] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     first_x_assum (qspecl_then [`Bind_name x 0 t tenvE1`, `targs`, `tvs`] mp_tac) >>
     srw_tac[][bind_tvar_rewrites, db_merge_def, deBruijn_subst_tenvE_def, num_tvs_def] >>
     imp_res_tac type_e_freevars >>
     full_simp_tac(srw_ss())[tenv_val_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge] >>
     first_x_assum match_mp_tac >>
     srw_tac[][] >>
     rev_full_simp_tac(srw_ss())[tenv_val_ok_def, num_tvs_def, bind_tvar_rewrites, num_tvs_db_merge])
     (* COMPLETENESS
 >- (qexists_tac `MAP (λ(x,t').
                 (x,
                  deBruijn_subst (tvs + num_tvs tenvE1)
                    (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs)
                    t')) env` >>
     qexists_tac `tvs` >>
     srw_tac[][] >|
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
          srw_tac[][bind_tvar_rewrites, db_merge_bind_var_list, num_tvs_bind_var_list,
              deBruijn_subst_E_bind_var_list] >>
          pop_assum match_mp_tac >>
          match_mp_tac tenv_ok_bind_var_list_funs >>
          srw_tac[][bind_tvar_rewrites] >>
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
          srw_tac[][num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list, db_merge_bind_var_list] >>
          pop_assum match_mp_tac >>
          match_mp_tac tenv_ok_bind_var_list_tvs >>
          metis_tac []])
          *)
 >- (qexists_tac `MAP (λ(x,t').
                 (x,
                  deBruijn_subst (num_tvs tenvE1)
                    (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                    t')) env` >>
    srw_tac[][]
    >- (LAST_X_ASSUM (MP_TAC o Q.SPECL [`bind_var_list 0 env tenvE1`, `targs`, `tvs`]) >>
        srw_tac[][bind_tvar_rewrites, db_merge_bind_var_list, num_tvs_bind_var_list,
            deBruijn_subst_E_bind_var_list] >>
        pop_assum match_mp_tac >>
        metis_tac [tenv_ok_bind_var_list_funs])
    >- (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`bind_var_list 0 env tenvE1`, `targs`, `tvs`]) >>
        srw_tac[][num_tvs_bind_var_list, deBruijn_subst_E_bind_var_list, db_merge_bind_var_list] >>
        pop_assum match_mp_tac >>
        metis_tac [tenv_ok_bind_var_list_funs]))
 >- (match_mp_tac nil_deBruijn_subst >>
     match_mp_tac check_freevars_type_name_subst >>
     `! n:num . n ≥ 0` by decide_tac >>
     metis_tac [check_freevars_add])
 >- (* This goal follows immediately from the previous one, how to just use it? *)
    (* For now we just copy-paste the goal and its proof.                       *)
    (`deBruijn_subst (num_tvs tenvE1)
                     (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                     (type_name_subst tenv.t t) = type_name_subst tenv.t t`
     by (match_mp_tac nil_deBruijn_subst >>
         match_mp_tac check_freevars_type_name_subst >>
         `! n:num . n ≥ 0` by decide_tac >>
         metis_tac [check_freevars_add]) >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[check_freevars_def] >>
     metis_tac [check_freevars_lem])
 >- (full_simp_tac(srw_ss())[check_freevars_def] >>
     LAST_X_ASSUM (MP_TAC o Q.SPECL [`Bind_name n 0 t1 tenvE1`, `targs`, `tvs`]) >>
     srw_tac[][deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def])
 >- (full_simp_tac(srw_ss())[ALOOKUP_FAILS, MAP_MAP_o, combinTheory.o_DEF, LIST_TO_SET_MAP] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [mem_exists_set]));

(* Recursive functions have function type *)
val type_funs_Tfn = Q.store_thm ("type_funs_Tfn",
`∀tenv funs tenv' tvs t n.
  type_funs tenv funs tenv' ∧
  (ALOOKUP tenv' n = SOME t)
  ⇒
  ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenv.v) [] (Tfn t1 t2)`,
induct_on `funs` >>
srw_tac[][] >>
qpat_assum `type_funs tenv funspat tenv'`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
cases_on `fn = n` >>
full_simp_tac(srw_ss())[deBruijn_subst_def, check_freevars_def] >>
metis_tac [type_e_freevars, num_tvs_def]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.store_thm ("type_funs_lookup",
`∀fn env funs env' n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenv funs env'
  ⇒
  (∃t. ALOOKUP env' fn = SOME t)`,
Induct_on `funs` >>
srw_tac[][] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
full_simp_tac(srw_ss())[] >>
srw_tac[][] >>
metis_tac []);

val type_funs_MAP_FST = store_thm("type_funs_MAP_FST",
``!funs tenv env.
  type_funs tenv funs env ⇒
  MAP FST funs = MAP FST env``,
  Induct>>srw_tac[][]>>
  pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
  full_simp_tac(srw_ss())[]>>metis_tac[])

(* Functions in the type environment can be found *)
val type_funs_find_recfun = Q.store_thm ("type_funs_find_recfun",
`∀fn env funs tenv' e tenv t.
  (ALOOKUP tenv' fn = SOME t) ∧
  type_funs tenv funs tenv'
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))`,
Induct_on `funs` >>
srw_tac[][] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
full_simp_tac(srw_ss())[] >>
srw_tac[][Once find_recfun_def] >>
metis_tac []);

val type_recfun_lookup = Q.store_thm ("type_recfun_lookup",
`∀fn funs n e tenv tenv' tvs t1 t2.
  (find_recfun fn funs = SOME (n,e)) ∧
  type_funs tenv funs tenv' ∧
  (ALOOKUP tenv' fn = SOME (Tfn t1 t2))
  ⇒
  type_e (tenv with v := Bind_name n 0 t1 tenv.v) e t2 ∧
  check_freevars (num_tvs tenv.v) [] (Tfn t1 t2)`,
induct_on `funs` >>
srw_tac[][Once find_recfun_def] >>
qpat_assum `type_funs tenv (h::funs) tenv'`
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
cases_on `fn' = fn` >>
full_simp_tac(srw_ss())[deBruijn_subst_def] >>
srw_tac[][check_freevars_def] >>
metis_tac [num_tvs_def, type_e_freevars, type_funs_Tfn, EVERY_DEF, check_freevars_def]);

(* No duplicate function definitions in a single let rec *)
val type_funs_distinct = Q.store_thm ("type_funs_distinct",
`∀tenv funs tenv'.
  type_funs tenv funs tenv'
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs)`,
induct_on `funs` >>
srw_tac[][] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
srw_tac[][MEM_MAP] >|
[PairCases_on `y` >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [type_funs_lookup, optionTheory.NOT_SOME_NONE],
 metis_tac []]);

val type_funs_tenv_ok = Q.store_thm ("type_funs_tenv_ok",
`!funs env tenv tvs env'.
  (num_tvs tenv.v = 0) ∧
  type_funs (tenv with v := bind_var_list 0 env' (bind_tvar tvs tenv.v)) funs env
  ⇒
  tenv_val_ok (bind_var_list tvs env Empty)`,
induct_on `funs` >>
srw_tac[][] >>
qpat_assum `type_funs x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
srw_tac[][check_freevars_def, bind_var_list_def, tenv_val_ok_def] >>
cases_on `tvs = 0` >>
full_simp_tac(srw_ss())[check_freevars_def, num_tvs_bind_var_list, bind_tvar_def, num_tvs_def] >>
metis_tac [arithmeticTheory.ADD_0]);

val type_e_subst_lem = Q.prove (
`∀tenv e t targs tvs targs'.
  type_e (tenv with v := Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenv.v)) e t ∧
  num_tvs tenv.v = 0 ∧
  tenv_tabbrev_ok tenv.t ∧
  tenv_mod_ok tenv.m ∧
  tenv_ctor_ok tenv.c ∧
  tenv_val_ok (bind_tvar (LENGTH targs) tenv.v) ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t1
  ⇒
  type_e (tenv with v := Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenv.v)) e (deBruijn_subst 0 targs t)`,
 srw_tac[][] >>
 first_assum (fn t => mp_tac (MATCH_MP ((GEN_ALL o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] o hd o CONJUNCTS) type_e_subst) t)) >>
 srw_tac[][] >>
 pop_assum (qspecl_then [`tenv.v`, `Bind_name x 0 t1 Empty`] mp_tac) >>
 srw_tac[][num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def, deBruijn_inc0, tenv_val_ok_def, bind_tvar_def, num_tvs_def] >>
 metis_tac []);

(* ---------- tid_exn_to_tc ---------- *)

val tid_exn_to_tc_11 = Q.store_thm ("tid_exn_to_tc_11",
`!x y. (tid_exn_to_tc x = tid_exn_to_tc y) = same_tid x y`,
cases_on `x` >>
cases_on `y` >>
srw_tac[][tid_exn_to_tc_def, same_tid_def]);

(* ---------- ctMap stuff ---------- *)
(* flat_tenvC_ok, ctMap_ok, flat_to_ctMap_list, to_ctMap_list, flat_to_ctMap,
 * to_ctMap, ctMap_to_mods, tenvC_to_types, consistent_ctMap *)

val empty_to_ctMap = Q.store_thm ("empty_to_ctMap",
`(!ctMap. FUNION (flat_to_ctMap []) ctMap = ctMap) ∧
 (!ctMap. DISJOINT (FDOM (flat_to_ctMap [])) (FDOM ctMap))`,
 srw_tac[][flat_to_ctMap_def, flat_to_ctMap_list_def, fmap_eq_flookup,
     FLOOKUP_FUNION, flookup_fupdate_list, DISJOINT_DEF, EXTENSION,
     FDOM_FUPDATE_LIST]);

val ctMap_ok_merge_imp = Q.store_thm ("ctMap_ok_merge_imp",
`!tenvC1 tenvC2.
  (ctMap_ok tenvC1 ∧ ctMap_ok tenvC2) ⇒
  ctMap_ok (FUNION tenvC1 tenvC2)`,
 srw_tac[][ctMap_ok_def] >>
 metis_tac [fevery_funion]);

val ctMap_ok_lookup = Q.store_thm ("ctMap_ok_lookup",
`!ctMap cn tvs ts tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap (cn,tn) = SOME (tvs,ts))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
 srw_tac[][ctMap_ok_def, FEVERY_ALL_FLOOKUP] >>
 res_tac >>
 full_simp_tac(srw_ss())[]);

val flat_tenvC_ok_ctMap = Q.store_thm ("flat_tenvC_ok_ctMap",
`!tenvC. flat_tenv_ctor_ok tenvC ⇒ ctMap_ok (flat_to_ctMap tenvC)`,
 srw_tac[][flat_to_ctMap_def, flat_to_ctMap_list_def, EVERY_MEM, flat_tenv_ctor_ok_def,
     flookup_fupdate_list, ctMap_ok_def, FEVERY_ALL_FLOOKUP] >>
 `?cn tn tvs ts. k = (cn,tn) ∧ v = (tvs,ts)`
              by metis_tac [pair_CASES] >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[EVERY_MEM, flat_tenv_ctor_ok_def] >>
 res_tac >>
 full_simp_tac(srw_ss())[]);

val flat_to_ctMap_lookup_none = Q.prove (
`!cn flat_tenvC.
  (ALOOKUP flat_tenvC cn = NONE)
  ⇒
  !t. (FLOOKUP (flat_to_ctMap flat_tenvC) (cn,t) = NONE)`,
 srw_tac[][flat_to_ctMap_def, flookup_fupdate_list] >>
 every_case_tac >>
 srw_tac[][] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss())[MEM_REVERSE, flat_to_ctMap_list_def, MEM_MAP, ALOOKUP_FAILS] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 metis_tac [FST]);

val flat_to_ctMap_lookup_not_none = Q.prove (
`!cn flat_tenvC tvs ts t.
  ALOOKUP flat_tenvC cn = SOME (tvs,ts,t)
  ⇒
  FLOOKUP (flat_to_ctMap flat_tenvC) (cn,t) ≠ NONE`,
 srw_tac[][flat_to_ctMap_def, flookup_fupdate_list] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[ALOOKUP_NONE, MEM_MAP, flat_to_ctMap_list_def] >>
 induct_on `flat_tenvC` >>
 srw_tac[][] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[] >>
 every_case_tac >>
 srw_tac[][]
 >- (qexists_tac `((cn,h3), (h1, h2))` >>
     srw_tac[][] >>
     qexists_tac `(cn,h1,h2,h3)` >>
     srw_tac[][])
 >- metis_tac []);

val to_ctMap_lookup = Q.prove (
`!cn tenvC tvs ts t x.
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list tenvC)) ∧
  ALOOKUP tenvC cn = SOME (tvs,ts,t) ∧
  FLOOKUP (flat_to_ctMap tenvC) (cn,t) = SOME x
  ⇒
  x = (tvs,ts)`,
 srw_tac[][flat_to_ctMap_def, flat_to_ctMap_list_def, flookup_fupdate_list] >>
 every_case_tac >>
 imp_res_tac alookup_distinct_reverse >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum mp_tac >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 induct_on `tenvC` >>
 srw_tac[][] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][]);

val flat_to_ctMap_list_append = Q.store_thm ("flat_to_ctMap_list_append",
`!tenvC1 tenvC2. flat_to_ctMap_list (tenvC1 ++ tenvC2) = flat_to_ctMap_list tenvC1 ++ flat_to_ctMap_list tenvC2`,
srw_tac[][flat_to_ctMap_list_def]);

val ctMap_ok_tenvC_ok = Q.store_thm ("ctMap_ok_tenvC_ok",
`!tenvC.
  ALL_DISTINCT (MAP FST (REVERSE (flat_to_ctMap_list tenvC))) ∧ ctMap_ok (flat_to_ctMap tenvC) ⇒ tenv_ctor_ok ([],tenvC)`,
 srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, ctMap_ok_def, tenv_ctor_ok_def, flat_tenv_ctor_ok_def] >>
 imp_res_tac FEVERY_FUPDATE_LIST >>
 full_simp_tac(srw_ss())[EVERY_MEM, EVERY_MAP] >>
 srw_tac[][] >>
 PairCases_on `e` >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[]);

val flat_to_ctMap_append = Q.store_thm ("flat_to_ctMap_append",
`!tenvC1 tenvC2.
  flat_to_ctMap (tenvC1++tenvC2) = FUNION (flat_to_ctMap tenvC1) (flat_to_ctMap tenvC2)`,
srw_tac[][REVERSE_APPEND, flat_to_ctMap_def, flat_to_ctMap_list_def, fmap_eq_flookup,
    flookup_fupdate_list, FLOOKUP_FUNION] >>
every_case_tac >>
full_simp_tac(srw_ss())[ALOOKUP_APPEND] >>
every_case_tac >>
full_simp_tac(srw_ss())[]);

val consistent_ctMap_extend = Q.store_thm ("consistent_ctMap_extend",
`!mn tdefs d ctMap.
  consistent_ctMap d ctMap
  ⇒
  consistent_ctMap (d with defined_types := set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs) ∪ d.defined_types)
                   (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs) ⊌ ctMap)`,
 srw_tac[][consistent_ctMap_def, RES_FORALL] >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[flat_to_ctMap_def, build_ctor_tenv_def, flat_to_ctMap_list_def] >>
 full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, MEM_MAP, MEM_FLAT] >>
 srw_tac[][]
 >- (PairCases_on `y''` >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `y'` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     PairCases_on `y` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][EXISTS_PROD] >>
     metis_tac [])
 >- (res_tac >>
     full_simp_tac(srw_ss())[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[]));

val consistent_ctMap_extend_exn = Q.store_thm ("consistent_ctMap_extend_exn",
`!mn cn ts d ctMap.
  consistent_ctMap d ctMap
  ⇒
  consistent_ctMap (d with defined_exns := {mk_id mn cn} ∪ d.defined_exns)
                   (flat_to_ctMap [(cn,([],ts,TypeExn (mk_id mn cn)))] ⊌ ctMap)`,
 srw_tac[][consistent_ctMap_def, RES_FORALL] >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[flat_to_ctMap_def, flat_to_ctMap_list_def] >>
 full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, MEM_MAP, MEM_FLAT] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]);

(* ---------- consistent_decls ---------- *)

val consistent_decls_disjoint = Q.store_thm ("consistent_decls_disjoint",
`!d tdefs ctMap mn.
  DISJOINT (set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs)) d.defined_types ∧
  consistent_ctMap d ctMap
  ⇒
  DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn tenvT tdefs))) (FDOM ctMap)` ,
 srw_tac[][METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``, consistent_ctMap_def, RES_FORALL, DISJOINT_DEF, EXTENSION] >>
 res_tac >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][build_ctor_tenv_def, flat_to_ctMap_def,flat_to_ctMap_list_def, FDOM_FUPDATE_LIST,
     MEM_MAP, MEM_FLAT, FORALL_PROD] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[FORALL_PROD] >>
 metis_tac []);

val consistent_decls_disjoint_exn = Q.store_thm ("consistent_decls_disjoint_exn",
`!d cn ctMap mn ts.
  mk_id mn cn ∉ d.defined_exns ∧
  consistent_ctMap d ctMap
  ⇒
  DISJOINT (FDOM (flat_to_ctMap [(cn,([]:tvarN list,ts,TypeExn (mk_id mn cn)))])) (FDOM ctMap)` ,
 srw_tac[][METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``, consistent_ctMap_def, RES_FORALL, DISJOINT_DEF, EXTENSION] >>
 res_tac >>
 `?cn tid. x = (cn,tid)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][flat_to_ctMap_def,flat_to_ctMap_list_def, FDOM_FUPDATE_LIST, MEM_MAP] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[]);

val consistent_decls_add_mod = Q.store_thm ("consistent_decls_add_mod",
`!decls d mn.
  consistent_decls decls d
  ⇒
  consistent_decls decls (d with defined_mods := {mn} ∪ d.defined_mods)`,
 srw_tac[][consistent_decls_def, RES_FORALL] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[]);

(* ---------- type_v, type_vs, type_env, consistent_mod_env ---------- *)

val type_vs_list_rel = Q.store_thm ("type_vs_list_rel",
`!vs ts tvs tenvC tenvS. type_vs tvs tenvC tenvS vs ts = LIST_REL (type_v tvs tenvC tenvS) vs ts`,
 induct_on `vs` >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases]);

val type_v_freevars = Q.store_thm ("type_v_freevars",
`(!tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒
   check_freevars tvs [] t) ∧
 (!tvs tenvC tenvS vs ts. type_vs tvs tenvC tenvS vs ts ⇒
   EVERY (check_freevars tvs []) ts) ∧
 (!tenvC tenvS env tenv. type_env tenvC tenvS env tenv ⇒
   tenv_val_ok tenv ∧ (num_tvs tenv = 0)) ∧
 (!tenvS tenvC envM tenvM. consistent_mod_env tenvS tenvC envM tenvM ⇒
   T)`,
 ho_match_mp_tac type_v_strongind >>
 srw_tac[][check_freevars_def, tenv_val_ok_def, num_tvs_def, bind_tvar_def, Tchar_def]
 >- rw[Tword_def,check_freevars_def]
 >- rw[Tword64_def,Tword_def,check_freevars_def]
 >- metis_tac [] >>
 res_tac
 >- metis_tac [num_tvs_def, type_e_freevars, bind_tvar_def,
               tenv_val_ok_def, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM]
 >- (
   imp_res_tac type_e_freevars >>
   full_simp_tac(srw_ss())[tenv_val_ok_def]  >>
   rev_full_simp_tac(srw_ss())[num_tvs_def])
 >- (
   imp_res_tac type_e_freevars >>
   full_simp_tac(srw_ss())[tenv_val_ok_def]  >>
   rev_full_simp_tac(srw_ss())[num_tvs_def])
 >- (imp_res_tac type_funs_Tfn >>
     full_simp_tac(srw_ss())[num_tvs_bind_var_list] >>
     metis_tac [])
 >- (imp_res_tac type_funs_Tfn >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
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
srw_tac[][Once type_v_cases] >>
srw_tac[][] >>
metis_tac []);

(* Typing lists of values from the end *)
val type_vs_end = Q.store_thm ("type_vs_end",
`∀tvs tenvC vs ts v t tenvS.
  type_vs tvs tenvC tenvS (vs++[v]) (ts++[t]) =
  (type_v tvs tenvC tenvS v t ∧
   type_vs tvs tenvC tenvS vs ts)`,
induct_on `vs` >>
srw_tac[][] >>
cases_on `ts` >>
full_simp_tac(srw_ss())[] >>
EQ_TAC >>
srw_tac[][] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[],
 metis_tac [type_v_rules],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [type_v_rules],
 srw_tac[][Once type_v_cases] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[]]);

(* Everything in the type environment is also in the execution environment *)
val type_lookup_lem = Q.prove (
`∀tenvC env tenvS tenv v n t' idx.
  type_env tenvC tenvS env tenv ∧
  lookup_tenv_val n idx tenv = SOME t'
  ⇒
  (∃v'. ALOOKUP env n = SOME v')`,
induct_on `tenv` >>
srw_tac[][Once type_v_cases] >>
full_simp_tac(srw_ss())[lookup_tenv_val_def] >-
metis_tac [] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
metis_tac []);

val type_lookup = Q.store_thm ("type_lookup",
`∀tenvC env tenvS tenv v n t' idx tvs.
  type_env tenvC tenvS env tenv ∧
  lookup_tenv_val n idx (bind_tvar tvs tenv) = SOME t'
  ⇒
  (∃v'. ALOOKUP env n = SOME v')`,
induct_on `tvs` >>
srw_tac[][bind_tvar_def] >-
metis_tac [type_lookup_lem] >>
full_simp_tac(srw_ss())[bind_tvar_def, lookup_tenv_val_def] >>
srw_tac[][] >>
every_case_tac >>
full_simp_tac(srw_ss())[lookup_tenv_val_def] >>
`!x y. x + SUC y = (x + 1) + y` by decide_tac >>
metis_tac []);

val type_lookup_id = Q.store_thm ("type_lookup_id",
`∀tenvS tenvC tenv.
  type_env tenvC tenvS env.v tenv.v ∧
  consistent_mod_env tenvS tenvC env.m tenv.m
  ⇒
  ((t_lookup_var_id n (tenv with v := bind_tvar tvs tenv.v) = SOME (tvs', t)) ⇒
     (∃v. (lookup_var_id n env = SOME v)))`,
 induct_on `env.m` >>
 srw_tac[][t_lookup_var_id_def, lookup_var_id_def] >>
 qpat_assum`X = env.m`(assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
 cases_on `n` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][lookup_var_id_def, t_lookup_var_id_def] >>
 imp_res_tac type_lookup >>
 srw_tac[][] >>
 qpat_assum `consistent_mod_env tenvS x0 x1 x2` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[t_lookup_var_id_def, lookup_var_id_def, FLOOKUP_UPDATE] >- (
   match_mp_tac type_lookup >>
   every_case_tac >>
   full_simp_tac(srw_ss())[lookup_tenv_val_def, bind_tvar_def, bvl2_lookup] >>
   metis_tac [SAME_KEY_UPDATES_DIFFER]) >>
 first_x_assum(qspec_then`env with m := v`mp_tac) >> simp[] >>
 disch_then (match_mp_tac o MP_CANON) >>
 qexists_tac `tenvS` >>
 qexists_tac `tenvC` >>
 qexists_tac `tenv with m := tenvM` >>
 simp []);

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
 srw_tac[][] >>
 srw_tac[][Once type_v_cases] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][deBruijn_inc_def, deBruijn_subst_def] >>
 srw_tac[][deBruijn_inc_def, deBruijn_subst_def] >>
 full_simp_tac(srw_ss())[check_freevars_def, Tchar_def] >>
 srw_tac[][deBruijn_inc_def, deBruijn_subst_def] >>
 srw_tac[][nil_deBruijn_inc, deBruijn_subst_check_freevars, type_subst_lem3,
     nil_deBruijn_subst]
 >- rw[Tword_def,deBruijn_subst_def]
 >- rw[Tword_def,Tword64_def,deBruijn_subst_def]
 >- (srw_tac[][EVERY_MAP] >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     srw_tac[][] >>
     metis_tac [type_subst_lem1, EVERY_MEM])
 >- (`EVERY (check_freevars 0 tvs') ts` by metis_tac [ctMap_ok_lookup, EVERY_MEM] >>
     `EVERY (check_freevars (LENGTH targs) tvs') ts`
           by (`LENGTH targs ≥ 0` by decide_tac >>
               metis_tac [EVERY_MEM, check_freevars_add]) >>
     full_simp_tac(srw_ss())[GSYM FUNION_alist_to_fmap] >>
     `type_vs tvs'' ctMap tenvS vs
              (MAP (deBruijn_subst 0 targs)
                 (MAP (deBruijn_inc (LENGTH targs) tvs'')
                    (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)))`
            by metis_tac [check_freevars_subst_list] >>
     pop_assum mp_tac >>
     srw_tac[][type_subst_deBruijn_subst_list, type_subst_deBruijn_inc_list])
 >- metis_tac []
 >- (qexists_tac `tenv` >>
     srw_tac[][] >>
     match_mp_tac type_e_subst_lem >>
     srw_tac[][tenv_val_ok_def, bind_tvar_def] >>
     metis_tac [type_v_freevars, ctMap_ok_lookup, consistent_con_env_def])
 >- (qexists_tac `tenv` >>
     qexists_tac `MAP (λ(x,t). (x,deBruijn_subst 0 targs t)) tenv'` >>
     srw_tac[][]
     >- (first_assum (assume_tac o MATCH_MP (GEN_ALL (hd (tl (tl (CONJUNCTS type_e_subst)))))) >>
         pop_assum (qspecl_then [`tenv.v`, `bind_var_list 0 tenv' Empty`] mp_tac) >>
         simp [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def, deBruijn_inc0,
               num_tvs_bind_var_list, db_merge_bind_var_list,
               deBruijn_subst_E_bind_var_list] >>
         disch_then match_mp_tac >>
         srw_tac[][] >-
         metis_tac [type_v_freevars] >-
         metis_tac [consistent_con_env_def] >>
         match_mp_tac tenv_ok_bind_var_list_funs >>
         metis_tac [tenv_ok_bind_var_list_funs, type_v_freevars, bind_tvar_rewrites])
     >- (qpat_assum `type_funs x y z` (fn x => ALL_TAC) >>
         induct_on `tenv'` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         PairCases_on `h` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         metis_tac []))
 >- (full_simp_tac(srw_ss())[EVERY_MEM] >>
     srw_tac[][] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac nil_deBruijn_inc >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac nil_deBruijn_subst >>
     full_simp_tac(srw_ss())[])
 >- (full_simp_tac(srw_ss())[] >>
     metis_tac [type_v_rules])
 >- (full_simp_tac(srw_ss())[] >>
     metis_tac [type_v_rules]));

(* They value of a binding in the execution environment has the type given by
 * the type environment. *)
val type_lookup_lem2 = Q.prove (
`∀ctMap env tenv tvs tenvS v x t targs tparams idx.
  ctMap_ok ctMap ∧
  type_env ctMap tenvS env tenv ∧
  EVERY (check_freevars tvs []) targs ∧
  (lookup_tenv_val x 0 (bind_tvar tvs tenv) = SOME (LENGTH targs, t)) ∧
  (ALOOKUP env x = SOME v)
  ⇒
  type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
srw_tac[][] >>
full_simp_tac(srw_ss())[lookup_tenv_val_def, bind_tvar_def] >>
qpat_assum `type_env ctMap tenvS env tenv_pat` (MP_TAC o SIMP_RULE (srw_ss ()) [Once type_env_cases]) >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
srw_tac[][] >>
full_case_tac >>
srw_tac[][]
>- (
  full_case_tac >>
  full_simp_tac(srw_ss())[lookup_tenv_val_def] >>
  metis_tac [type_v_freevars, type_subst, bind_tvar_def])
>- metis_tac [lookup_tenv_val_def]);

val consistent_mod_env_lookup = Q.prove (
`!tenvS ctMap menv tenvM tenv env n.
  consistent_mod_env tenvS ctMap menv tenvM ∧
  ALOOKUP menv n = SOME env ∧
  FLOOKUP tenvM n = SOME tenv
  ⇒
  type_env ctMap tenvS env (bind_var_list2 tenv Empty)`,
 induct_on `menv` >>
 srw_tac[][] >>
 qpat_assum `consistent_mod_env x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once consistent_mod_cases]) >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[FLOOKUP_UPDATE] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 metis_tac []);

val type_lookup_type_v = Q.store_thm ("type_lookup_type_v",
`∀tenvM ctMap env tenv tvs tenvS v x t targs tparams idx.
  tenv_mod_ok tenv.m ∧
  ctMap_ok ctMap ∧
  type_env ctMap tenvS env.v tenv.v ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  EVERY (check_freevars tvs []) targs ∧
  (t_lookup_var_id x (tenv with v := bind_tvar tvs tenv.v) = SOME (LENGTH targs, t)) ∧
  (lookup_var_id x env = SOME v)
  ⇒
  type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
 cases_on `x` >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[lookup_var_id_def, t_lookup_var_id_def] >-
 metis_tac [type_lookup_lem2] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 match_mp_tac type_lookup_lem2 >>
 srw_tac[][bind_tvar_rewrites] >>
 imp_res_tac consistent_mod_env_lookup >>
 qexists_tac `x` >>
 qexists_tac `bind_var_list2 x' Empty` >>
 qexists_tac `a` >>
 srw_tac[][] >>
 match_mp_tac type_lookup_lem4 >>
 metis_tac [tenv_mod_ok_lookup, num_tvs_bvl2, num_tvs_def, bvl2_lookup]);

val type_env_merge_bvl2 = Q.store_thm ("type_env_merge_bvl2",
`!tenvM tenvC tenvS env1 tenv1 env2 tenv2.
  type_env tenvC tenvS env2 (bind_var_list2 tenv2 Empty) ∧
  type_env tenvC tenvS env1 (bind_var_list2 tenv1 Empty) ⇒
  type_env tenvC tenvS (env1 ++ env2) (bind_var_list2 (tenv1 ++ tenv2) Empty)`,
 induct_on `env1` >>
 cases_on `tenv1` >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases] >>
 srw_tac[][] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[bind_var_list2_def] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 full_simp_tac(srw_ss())[] >>
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
 srw_tac[][] >>
 PairCases_on `h` >>
 srw_tac[][]);

val lookup_ctor_none = Q.store_thm ("lookup_ctor_none",
`!tds tenvC envC.
  !x. ALOOKUP (build_ctor_tenv mn tenvT tds) x = NONE ⇔
      ALOOKUP (build_tdefs mn tds) x = NONE`,
 srw_tac[][build_ctor_tenv_def, build_tdefs_def, flookup_fupdate_list] >>
 eq_tac >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 induct_on `tds` >>
 srw_tac[][ALOOKUP_APPEND, REVERSE_APPEND] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [lookup_ctor_none_lem, NOT_SOME_NONE, MAP_REVERSE]);

val build_ctor_tenv_cons = Q.prove (
`∀tvs tn ctors tds.
  build_ctor_tenv mn tenvT ((tvs,tn,ctors)::tds) =
    build_ctor_tenv mn tenvT tds ++ REVERSE (MAP (λ(cn,ts). (cn,tvs,MAP (type_name_subst tenvT) ts,TypeId (mk_id mn tn))) ctors)`,
srw_tac[][build_ctor_tenv_def]);

val build_ctor_tenv_empty = Q.store_thm ("build_ctor_tenv_empty",
`build_ctor_tenv mn tenvT [] = []`,
srw_tac[][build_ctor_tenv_def]);

val check_ctor_tenvC_ok = Q.store_thm ("check_ctor_tenvC_ok",
`!mn c tenvT.
 check_ctor_tenv mn tenvT c ∧
 tenv_tabbrev_ok tenvT
 ⇒
 flat_tenv_ctor_ok (build_ctor_tenv mn tenvT c)`,
 srw_tac[][build_ctor_tenv_def, tenv_ctor_ok_def, flat_tenv_ctor_ok_def] >>
 full_simp_tac(srw_ss())[check_ctor_tenv_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
 srw_tac[][] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 srw_tac[][] >>
 PairCases_on `y` >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 match_mp_tac check_freevars_type_name_subst >>
 srw_tac[][]);

val check_ctor_tenv_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_ctor_tenv mn tenvT ((tvs,ts,ctors)::tds) ⇒
  check_ctor_tenv mn tenvT tds`,
 srw_tac[][] >>
 full_simp_tac(srw_ss())[check_ctor_tenv_def] >>
 metis_tac [check_dup_ctors_cons]);

val check_ctor_tenv_dups = Q.store_thm ("check_ctor_tenv_dups",
`!mn tdecs. check_ctor_tenv mn tenvT tdecs ⇒ check_dup_ctors tdecs`,
 induct_on `tdecs` >>
 srw_tac[][check_dup_ctors_def, LET_THM] >>
 PairCases_on `h` >>
 imp_res_tac check_ctor_tenv_cons >>
 res_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[check_ctor_tenv_def, check_dup_ctors_def, LET_THM]);

val check_ctor_ctMap_ok = Q.store_thm ("check_ctor_ctMap_ok",
`!mn tenvT c.
 check_ctor_tenv mn tenvT c ∧
 tenv_tabbrev_ok tenvT
 ⇒
 ctMap_ok (flat_to_ctMap (build_ctor_tenv mn tenvT c))`,
 srw_tac[][] >>
 imp_res_tac check_ctor_tenvC_ok >>
 full_simp_tac(srw_ss())[flat_tenv_ctor_ok_def, ctMap_ok_def, EVERY_MEM, flat_to_ctMap_def, MEM_MAP] >>
 srw_tac[][FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[flat_to_ctMap_list_def, MEM_MAP] >>
 res_tac >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[]);

val ctor_env_to_tdefs = Q.prove (
`!mn tds cn n t tvs ts.
  ALOOKUP (build_ctor_tenv mn tenvT tds) cn = SOME (tvs,ts,t)
  ⇒
  ALOOKUP (build_tdefs mn tds) cn = SOME (LENGTH ts,t)`,
 induct_on `tds` >>
 srw_tac[][build_ctor_tenv_empty] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[build_ctor_tenv_cons, build_tdefs_cons] >>
 full_simp_tac(srw_ss())[ALOOKUP_APPEND, FLOOKUP_FUNION] >>
 cases_on `ALOOKUP (build_tdefs mn tds) cn` >>
 srw_tac[][]
 >- (cases_on `ALOOKUP (build_ctor_tenv mn tenvT tds) cn` >>
     full_simp_tac(srw_ss())[]
     >- (full_simp_tac(srw_ss())[GSYM MAP_REVERSE, flookup_fupdate_list] >>
         rpt (pop_assum mp_tac) >>
         Q.SPEC_TAC (`REVERSE h2`, `h2`) >>
         induct_on `h2` >>
         srw_tac[][] >>
         PairCases_on `h` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[])
     >- metis_tac [NOT_SOME_NONE])
 >- (full_simp_tac(srw_ss())[flookup_fupdate_list] >>
     Cases_on `ALOOKUP (build_ctor_tenv mn tenvT tds) cn` >>
     full_simp_tac(srw_ss())[]
     >- metis_tac [lookup_ctor_none, NOT_SOME_NONE]
     >- (srw_tac[][] >>
         res_tac >>
         full_simp_tac(srw_ss())[])));

val check_dup_ctors_distinct = Q.prove (
`!tds mn.
  check_dup_ctors tds ⇒ ALL_DISTINCT (MAP FST (flat_to_ctMap_list (build_ctor_tenv mn tenvT tds)))`,
 induct_on `tds` >>
 srw_tac[][check_dup_ctors_thm, build_ctor_tenv_def, flat_to_ctMap_list_def,REVERSE_APPEND, ALL_DISTINCT_APPEND] >>
 full_simp_tac(srw_ss())[flat_to_ctMap_list_def, build_ctor_tenv_def, check_dup_ctors_thm, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
 srw_tac[][] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[MAP_FLAT, MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, REVERSE_APPEND, GSYM MAP_REVERSE]
 >- (`?l. h2 = REVERSE l` by (qexists_tac `REVERSE h2` >> srw_tac[][]) >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     induct_on `l` >>
     srw_tac[][] >>
     PairCases_on `h` >>
     full_simp_tac(srw_ss())[MEM_FLAT, MEM_MAP] >>
     srw_tac[][] >>
     PairCases_on `x` >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     LAST_X_ASSUM (mp_tac o Q.SPEC `(h0',x1)`) >>
     srw_tac[][])
 >- (full_simp_tac(srw_ss())[MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     full_simp_tac(srw_ss())[MEM_FLAT, MEM_MAP] >>
     srw_tac[][] >>
     PairCases_on `y` >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `y'` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     srw_tac[][FORALL_PROD] >>
     PairCases_on `y` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     FIRST_X_ASSUM (mp_tac o Q.SPEC `p_1`) >>
     srw_tac[][MEM_MAP]
     >- (qexists_tac `(p_1,p_2')` >>
         srw_tac[][FST_pair])
     >- (srw_tac[][EXISTS_PROD, LAMBDA_PROD] >>
         qexists_tac `MAP FST y2` >>
         srw_tac[][]
         >- metis_tac [FST_pair] >>
         srw_tac[][MEM_MAP] >>
         metis_tac [FST])));

(* ---------- consistent_con_env ---------- *)

val extend_consistent_con = Q.store_thm ("extend_consistent_con",
`!ctMap cenv tenv mn tdefs.
  DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn tenv.t tdefs))) (FDOM ctMap) ∧
  tenv_tabbrev_ok tenv.t ∧
  check_ctor_tenv mn tenv.t tdefs ∧
  consistent_con_env ctMap cenv tenv.c
  ⇒
  consistent_con_env (flat_to_ctMap (build_ctor_tenv mn tenv.t tdefs) ⊌ ctMap)
                     (merge_alist_mod_env ([],build_tdefs mn tdefs) cenv)
                     (merge_alist_mod_env ([],build_ctor_tenv mn tenv.t tdefs) tenv.c)`,
 srw_tac[][consistent_con_env_def, ALOOKUP_APPEND, tenv_ctor_ok_merge, lookup_tenvC_merge_emp]
 >- (srw_tac[][tenv_ctor_ok_def] >>
     metis_tac [check_ctor_tenvC_ok])
 >- metis_tac [check_ctor_ctMap_ok, ctMap_ok_merge_imp]
 >- (full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
     PairCases_on `cenv` >>
     full_simp_tac(srw_ss())[lookup_mod_env_def, FLOOKUP_FUNION, merge_mod_env_def] >>
     rpt (FIRST_X_ASSUM (qspecl_then [`cn`] mp_tac)) >>
     Cases_on `cn` >>
     full_simp_tac(srw_ss())[]
     >- (Cases_on `ALOOKUP (build_tdefs mn tdefs) a` >>
         full_simp_tac(srw_ss())[]
         >- (`ALOOKUP (build_ctor_tenv mn tenv.t tdefs) a = NONE` by metis_tac [lookup_ctor_none] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[id_to_n_def, flookup_thm, DISJOINT_DEF, EXTENSION] >>
             metis_tac [])
         >- (srw_tac[][] >>
             `ALOOKUP (build_ctor_tenv mn tenv.t tdefs) a ≠ NONE`
                      by metis_tac [NOT_SOME_NONE, lookup_ctor_none] >>
             Cases_on `ALOOKUP (build_ctor_tenv mn tenv.t tdefs) a` >>
             srw_tac[][] >>
             PairCases_on `x` >>
             imp_res_tac ctor_env_to_tdefs >>
             simp [] >>
             imp_res_tac flat_to_ctMap_lookup_not_none >>
             full_simp_tac(srw_ss())[id_to_n_def] >>
             srw_tac[][] >>
             Cases_on `FLOOKUP (flat_to_ctMap (build_ctor_tenv mn tenv.t tdefs)) (a,t)` >>
             srw_tac[][] >>
             imp_res_tac check_ctor_tenv_dups >>
             metis_tac [check_dup_ctors_distinct, to_ctMap_lookup]))
     >- (Cases_on `ALOOKUP cenv0 s` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][id_to_n_def] >>
         MAP_EVERY qexists_tac [`tvs`, `ts`] >>
         srw_tac[][] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
         metis_tac []))
 >- (full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     PairCases_on `cenv` >>
     full_simp_tac(srw_ss())[lookup_mod_env_def, ALOOKUP_APPEND, merge_mod_env_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [NOT_SOME_NONE, pair_CASES,ctor_env_to_tdefs]));

val extend_consistent_con_exn = Q.store_thm ("extend_consistent_con_exn",
`∀mn tenv cn ts cenv ctMap.
  (cn,TypeExn (mk_id mn cn)) ∉ FDOM ctMap ∧
  check_exn_tenv mn cn ts ∧
  tenv_tabbrev_ok tenv.t ∧
  EVERY (check_type_names tenv.t) ts ∧
  consistent_con_env ctMap cenv tenv.c
  ⇒
  consistent_con_env (FUNION (flat_to_ctMap [(cn,([],MAP (type_name_subst tenv.t) ts,TypeExn (mk_id mn cn)))]) ctMap)
                     (merge_alist_mod_env ([], [(cn,(LENGTH ts,TypeExn (mk_id mn cn)))]) cenv)
                     (merge_alist_mod_env ([], [(cn,([],MAP (type_name_subst tenv.t) ts,TypeExn (mk_id mn cn)))]) tenv.c)`,
 srw_tac[][check_exn_tenv_def, consistent_con_env_def, FEVERY_ALL_FLOOKUP,
     flat_to_ctMap_def, ctMap_ok_def, tenv_ctor_ok_merge, tenv_ctor_ok_def,
     flat_tenv_ctor_ok_def, lookup_tenvC_merge_emp] >>
 full_simp_tac(srw_ss())[flookup_fupdate_list, FLOOKUP_FUNION, lookup_alist_mod_env_def] >>
 rpt (FIRST_X_ASSUM (qspecl_then [`cn'`] mp_tac)) >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[flat_to_ctMap_list_def, id_to_n_def] >>
 srw_tac[][ALOOKUP_APPEND] >>
 res_tac >>
 full_simp_tac(srw_ss())[MEM_MAP, FORALL_PROD] >>
 full_simp_tac(srw_ss())[lookup_mod_env_def, FLOOKUP_FUNION, merge_mod_env_def] >>
 full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]>>
 full_simp_tac(srw_ss())[FLOOKUP_DEF,EVERY_MEM,MEM_MAP]>>
 metis_tac[check_freevars_type_name_subst,check_freevars_def]);

val consistent_con_env_lookup = Q.store_thm ("consistent_con_env_lookup",
`!ctMap envC tenvC cn tvs ts tn.
  consistent_con_env ctMap envC tenvC ∧
  lookup_alist_mod_env cn tenvC = SOME (tvs,ts,tn)
  ⇒
  FLOOKUP ctMap (id_to_n cn,tn) = SOME (tvs, ts)`,
 srw_tac[][consistent_con_env_def] >>
 cases_on `lookup_alist_mod_env cn envC` >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 PairCases_on `x` >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][]);

val consistent_con_env_to_mod = Q.store_thm ("consistent_con_env_to_mod",
`!ctMap envC flat_envC tenvC flat_tenvC mn.
  MAP FST flat_envC = MAP FST flat_tenvC ∧
  consistent_con_env ctMap envC tenvC ∧
  consistent_con_env ctMap (merge_alist_mod_env ([],flat_envC) envC) (merge_alist_mod_env ([],flat_tenvC) tenvC)
  ⇒
  consistent_con_env ctMap (merge_alist_mod_env ([(mn,flat_envC)],[]) envC) (merge_alist_mod_env ([(mn,flat_tenvC)],[]) tenvC)`,
 srw_tac[][consistent_con_env_def] >>
 PairCases_on `tenvC` >>
 PairCases_on `envC` >>
 full_simp_tac(srw_ss())[merge_alist_mod_env_def]
 >- full_simp_tac(srw_ss())[tenv_ctor_ok_def, flat_tenv_ctor_ok_def]
 >- (`(?mn' cn'. cn = Long mn' cn') ∨ (?cn'. cn = Short cn')` by (Cases_on `cn` >> metis_tac []) >>
     full_simp_tac(srw_ss())[lookup_tenvC_mod_cons] >>
     srw_tac[][]
     >- (FIRST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`, `n`, `t`]) >>
         full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[ALOOKUP_APPEND, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[id_to_n_def] >>
         imp_res_tac ALOOKUP_MEM >>
         full_simp_tac(srw_ss())[MEM_MAP, ALOOKUP_FAILS] >>
         full_simp_tac(srw_ss())[flookup_thm] >>
         metis_tac [MEM_MAP, FST, pair_CASES])
     >- (full_simp_tac(srw_ss())[] >>
         FIRST_X_ASSUM (mp_tac o Q.SPECL [`Long mn' cn'`, `n`, `t`]) >>
         full_simp_tac(srw_ss())[lookup_alist_mod_env_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         srw_tac[][])
     >- (LAST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`, `n`, `t`]) >>
         full_simp_tac(srw_ss())[lookup_alist_mod_env_def,
             FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
         srw_tac[][]))
 >- (`(?mn' cn'. cn = Long mn' cn') ∨ (?cn'. cn = Short cn')` by (Cases_on `cn` >> metis_tac []) >>
     full_simp_tac(srw_ss())[lookup_tenvC_mod_cons, lookup_alist_mod_env_def, ALOOKUP_APPEND] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[ALOOKUP_FAILS]
     >- metis_tac [MEM_MAP, FST, pair_CASES]
     >- (rpt (LAST_X_ASSUM (mp_tac o Q.SPECL [`Long mn' cn'`])) >>
         full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[ALOOKUP_FAILS])
     >- (rpt (LAST_X_ASSUM (mp_tac o Q.SPECL [`Short cn'`])) >>
         full_simp_tac(srw_ss())[lookup_alist_mod_env_def] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[ALOOKUP_FAILS])));

(* ---------- type_ctxt, type_ctxts ---------- *)

val type_ctxts_freevars = Q.store_thm ("type_ctxts_freevars",
`!tvs ctMap tenvS cs t1 t2.
  type_ctxts tvs ctMap tenvS cs t1 t2 ⇒
  ctMap_ok ctMap ⇒
  check_freevars tvs [] t1 ∧ check_freevars tvs [] t2`,
 ho_match_mp_tac type_ctxts_ind >>
 srw_tac[][type_ctxt_cases, check_freevars_def, GSYM FUNION_alist_to_fmap] >>
 srw_tac[][check_freevars_def]
 >- (cases_on `pes` >>
     full_simp_tac(srw_ss())[RES_FORALL] >>
     qpat_assum `!x. (x = h) ∨ MEM x t ⇒ P x` (ASSUME_TAC o Q.SPEC `h`) >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `h` >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[Once context_invariant_cases] >>
     metis_tac [type_p_freevars])
 >- (imp_res_tac ctMap_ok_lookup >>
     full_simp_tac(srw_ss())[] >>
     match_mp_tac check_freevars_subst_single >>
     srw_tac[][] >>
     imp_res_tac consistent_con_env_lookup >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- (cases_on `pes` >>
     full_simp_tac(srw_ss())[RES_FORALL] >>
     qpat_assum `!x. (x = h) ∨ MEM x t ⇒ P x` (ASSUME_TAC o Q.SPEC `h`) >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `h` >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[Once context_invariant_cases] >>
     metis_tac [type_p_freevars])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- (imp_res_tac ctMap_ok_lookup >>
     full_simp_tac(srw_ss())[] >>
     match_mp_tac check_freevars_subst_single >>
     srw_tac[][] >>
     imp_res_tac consistent_con_env_lookup >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ])
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]);

(* ---------- type_d ---------- *)

val type_d_check_uniq = Q.store_thm ("type_d_check_uniq",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_d uniq tvs tdecs tenv d tdecs' new_tenv
  ⇒
  type_d F tvs tdecs tenv d tdecs' new_tenv`,
 srw_tac[][type_d_cases] >>
 metis_tac []);


val type_d_tenv_ok = Q.store_thm ("type_d_tenv_ok",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_d uniq tvs tdecs tenv d tdecs' new_tenv ∧
  num_tvs tenv.v = 0
  ⇒
  tenv_val_ok (bind_var_list2 (SND (SND new_tenv)) Empty)`,
 srw_tac[][type_d_cases] >>
 `tenv_val_ok Empty` by srw_tac[][tenv_val_ok_def] >>
 imp_res_tac type_p_bvl >>
 srw_tac[][bvl2_to_bvl]
 >- metis_tac [type_funs_tenv_ok] >>
 srw_tac[][bind_var_list2_def, tenv_val_ok_def]);


(*weakened*)
val type_d_tenvT_ok = Q.store_thm ("type_d_tenvT_ok",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_d uniq tvs tdecs tenv d tdecs' new_tenv ∧
  tenv_tabbrev_ok tenv.t
  ⇒
  flat_tenv_tabbrev_ok (FST new_tenv)`,
 srw_tac[][type_d_cases, flat_tenv_tabbrev_ok_def] >>
 full_simp_tac(srw_ss())[FEVERY_ALL_FLOOKUP, check_ctor_tenv_def] >>
 full_simp_tac(srw_ss())[FLOOKUP_UPDATE, flookup_fupdate_list] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[EVERY_MEM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac ALOOKUP_MEM >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 imp_res_tac check_freevars_type_name_subst >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[check_freevars_def, EVERY_MAP] >>
 full_simp_tac(srw_ss())[EVERY_MEM]);

val type_d_ctMap_ok = Q.store_thm ("type_d_ctMap_ok",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  tenv_tabbrev_ok tenv.t ∧
  type_d uniq tvs tdecs tenv d tdecs' new_tenv
  ⇒
  ctMap_ok (flat_to_ctMap (FST (SND new_tenv))) ∧
  ALL_DISTINCT (MAP FST (flat_to_ctMap_list (FST (SND new_tenv))))`,
 srw_tac[][type_d_cases, flat_to_ctMap_def, flat_to_ctMap_list_def] >>
 imp_res_tac type_p_bvl >>
 srw_tac[][bvl2_to_bvl] >>
 imp_res_tac check_ctor_ctMap_ok >>
 TRY (srw_tac[][ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >> NO_TAC)
 >- (full_simp_tac(srw_ss())[flat_to_ctMap_def, flat_to_ctMap_list_def] >>
     FIRST_X_ASSUM match_mp_tac >>
     match_mp_tac tenv_tabbrev_ok_merge >>
     srw_tac[][tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list, flat_tenv_tabbrev_ok_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss())[check_ctor_tenv_def, EVERY_MEM, MEM_MAP] >>
     PairCases_on `y` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (imp_res_tac check_ctor_tenv_dups >>
     imp_res_tac check_dup_ctors_distinct >>
     full_simp_tac(srw_ss())[flat_to_ctMap_list_def])
 >- (full_simp_tac(srw_ss())[check_exn_tenv_def, ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
     srw_tac[][] >>
     srw_tac[][EVERY_MAP] >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     metis_tac [check_freevars_type_name_subst]));

val ctMap_ok_pres = Q.store_thm ("ctMap_ok_pres",
`!uniq mn tdecs tenv d tdecs' new_tenv ctMap.
  type_d uniq mn tdecs tenv d tdecs' new_tenv ∧
  tenv_tabbrev_ok tenv.t ∧
  ctMap_ok ctMap
  ⇒
  ctMap_ok (FUNION (flat_to_ctMap (FST (SND new_tenv))) ctMap)`,
 srw_tac[][] >>
 imp_res_tac type_d_ctMap_ok >>
 srw_tac[][] >>
 srw_tac[][] >>
 imp_res_tac ctMap_ok_merge_imp >>
 srw_tac[][]);

 (*

val type_d_new_tenv_ok = Q.store_thm ("type_d_new_tenv_ok",
`!x tvs decls tenv d decls' new_tenv.
  type_d x tvs decls tenv d decls' new_tenv ∧
  tenv_ok tenv ∧
  num_tvs tenv.v = 0
  ⇒
  new_dec_tenv_ok new_tenv`,

 srw_tac[][type_d_cases] >>
 simp [new_dec_tenv_ok_def, flat_tenv_tabbrev_ok_def, FEVERY_FEMPTY,
       flat_tenv_ctor_ok_def, tenv_add_tvs_def, EVERY_MAP]
 >- (
   imp_res_tac type_p_freevars >>
   full_simp_tac(srw_ss())[EVERY_MAP] >>
   full_simp_tac(srw_ss())[EVERY_MEM] >>
   srw_tac[][] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[] >>
   rename1 `MEM b bindings` >>
   PairCases_on `b` >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   res_tac >>
   full_simp_tac(srw_ss())[])
 >- (
   imp_res_tac type_p_freevars >>
   full_simp_tac(srw_ss())[EVERY_MAP] >>
   full_simp_tac(srw_ss())[EVERY_MEM] >>
   srw_tac[][] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[] >>
   rename1 `MEM b bindings` >>
   PairCases_on `b` >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   res_tac >>
   full_simp_tac(srw_ss())[])
 >- (
   imp_res_tac type_e_freevars >>
   rev_full_simp_tac(srw_ss())[tenv_ok_def] >>
   imp_res_tac tenv_ok_bind_var_list_funs >>
   rev_full_simp_tac(srw_ss())[bind_tvar_rewrites] >>
   full_simp_tac(srw_ss())[EVERY_MAP] >>
   full_simp_tac(srw_ss())[EVERY_MEM] >>
   srw_tac[][] >>
   every_case_tac >>
   rev_full_simp_tac(srw_ss())[] >>
   rename1 `MEM b bindings` >>
   PairCases_on `b` >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   res_tac >>
   full_simp_tac(srw_ss())[num_tvs_bind_var_list, bind_tvar_rewrites] >>
   rev_full_simp_tac(srw_ss())[])

   *)

val type_d_mod = Q.store_thm ("type_d_mod",
`!uniq mn tdecs tenv d tdecs' new_tenv.
  type_d uniq mn tdecs tenv d tdecs' new_tenv
  ⇒
  tdecs'.defined_mods = {} ∧
  decls_to_mods tdecs' ⊆ { mn }`,
 srw_tac[][type_d_cases, decls_to_mods_def, SUBSET_DEF, flat_to_ctMap_list_def, FDOM_FUPDATE_LIST] >>
 full_simp_tac(srw_ss())[build_ctor_tenv_def, MEM_FLAT, MEM_MAP] >>
 srw_tac[][empty_decls_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[EXISTS_PROD, empty_decls_def, decls_to_mods_def, mk_id_def, MEM_MAP] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[GSPECIFICATION] >>
 TRY (PairCases_on `y`) >>
 full_simp_tac(srw_ss())[]);

val type_d_ctMap_disjoint = Q.store_thm ("type_d_ctMap_disjoint",
`type_d uniq mn tdecs1 tenv d tdecs1' new_tenv ∧
 consistent_ctMap tdecs1 ctMap
 ⇒
 DISJOINT (FDOM (flat_to_ctMap (FST (SND new_tenv)))) (FDOM ctMap) ∧
 DISJOINT (IMAGE SND (FDOM (flat_to_ctMap (FST (SND new_tenv))))) (IMAGE SND (FDOM ctMap))`,
 srw_tac[][type_d_cases, DISJOINT_DEF, EXTENSION, flat_to_ctMap_def, FDOM_FUPDATE_LIST,
     flat_to_ctMap_list_def] >>
 srw_tac[][MEM_MAP] >>
 full_simp_tac(srw_ss())[FORALL_PROD, consistent_ctMap_def, RES_FORALL] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 res_tac >>
 every_case_tac >>
 full_simp_tac(srw_ss())[build_ctor_tenv_def, MEM_MAP, MEM_FLAT] >>
 srw_tac[][] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 PairCases_on `y` >>
 full_simp_tac(srw_ss())[MEM_MAP, FORALL_PROD] >>
 srw_tac[][] >>
 metis_tac []);

(* ---------- type_ds ---------- *)

val type_ds_check_uniq = Q.store_thm ("type_ds_check_uniq",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_ds uniq tvs tdecs tenv d tdecs' new_tenv
  ⇒
  type_ds F tvs tdecs tenv d tdecs' new_tenv`,
 ho_match_mp_tac type_ds_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_ds_cases] >>
 metis_tac [type_d_check_uniq]);

val type_ds_tenv_ok = Q.store_thm ("type_ds_tenv_ok",
`!x tvs tdecs tenv ds tdecs' new_tenv.
  type_ds x tvs tdecs tenv ds tdecs' new_tenv ⇒
  num_tvs tenv.v = 0 ⇒
  tenv_val_ok (bind_var_list2 (SND (SND new_tenv)) Empty)`,
 ho_match_mp_tac type_ds_ind >>
 srw_tac[][]
 >- (srw_tac[][bind_var_list2_def, tenv_val_ok_def])
 >- (imp_res_tac type_d_tenv_ok >>
     PairCases_on `new_tenv1` >>
     PairCases_on `new_tenv` >>
     full_simp_tac(srw_ss())[bvl2_append, num_tvs_bvl2, extend_env_new_decs_def, append_new_dec_tenv_def] >>
     metis_tac [tenv_val_ok_bvl2]));

val type_ds_mod = Q.store_thm ("type_ds_mod",
`!uniq mn tdecs tenv ds tdecs' new_tenv.
  type_ds uniq mn tdecs tenv ds tdecs' new_tenv
  ⇒
  tdecs'.defined_mods = {} ∧
  decls_to_mods tdecs' ⊆ {mn}`,
 induct_on `ds` >>
 srw_tac[][Once type_ds_cases]
 >- srw_tac[][decls_to_mods_def, empty_decls_def, SUBSET_DEF, FDOM_FUPDATE_LIST, MEM_MAP]
 >- srw_tac[][decls_to_mods_def, empty_decls_def, SUBSET_DEF, FDOM_FUPDATE_LIST, MEM_MAP] >>
 imp_res_tac type_d_mod >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[union_decls_def, decls_to_mods_def] >>
 rpt (pop_assum mp_tac) >>
 ONCE_REWRITE_TAC [SUBSET_DEF] >>
 REWRITE_TAC [GSPECIFICATION] >>
 rw_tac (bool_ss) [] >>
 metis_tac []);

val type_ds_ctMap_ok = Q.store_thm ("type_ds_ctMap_ok",
`!uniq tvs tdecs tenv ds tdecs' new_tenv.
  type_ds uniq tvs tdecs tenv ds tdecs' new_tenv
  ⇒
  tenv_tabbrev_ok tenv.t
  ⇒
  ctMap_ok (flat_to_ctMap (FST (SND new_tenv)))`,
 ho_match_mp_tac type_ds_strongind >>
 srw_tac[][]
 >- srw_tac[][ctMap_ok_def, flat_to_ctMap_def, flat_to_ctMap_list_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]
 >- (imp_res_tac type_d_ctMap_ok >>
     imp_res_tac type_d_tenvT_ok >>
     full_simp_tac(srw_ss())[flat_to_ctMap_def] >>
     full_simp_tac(srw_ss())[ctMap_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
     `tenv_tabbrev_ok (merge_mod_env (FEMPTY,FST new_tenv1) tenv.t)`
            by (match_mp_tac tenv_tabbrev_ok_merge >>
                srw_tac[][tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]) >>
     full_simp_tac(srw_ss())[tenv_tabbrev_ok_def] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[flat_to_ctMap_list_def, REVERSE_APPEND] >>
    PairCases_on `new_tenv1` >>
     PairCases_on `new_tenv` >>
     full_simp_tac(srw_ss())[append_new_dec_tenv_def,extend_env_new_decs_def, ALOOKUP_APPEND] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][]));

val type_ds_tenvC_ok = Q.store_thm ("type_ds_tenvC_ok",
`!x tvs tdecs tenv ds tdecs' new_tenv.
  type_ds x tvs tdecs tenv ds tdecs' new_tenv ⇒
  tenv_tabbrev_ok tenv.t ⇒
  flat_tenv_ctor_ok (FST (SND new_tenv))`,
 ho_match_mp_tac type_ds_strongind >>
 srw_tac[][]
 >- srw_tac[][flat_tenv_ctor_ok_def]
 >- (imp_res_tac type_d_ctMap_ok >>
     imp_res_tac type_d_tenvT_ok >>
     `tenv_ctor_ok ([],FST (SND new_tenv1))` by metis_tac [ctMap_ok_tenvC_ok, MAP_REVERSE, ALL_DISTINCT_REVERSE] >>
     full_simp_tac(srw_ss())[flat_tenv_ctor_ok_def, tenv_ctor_ok_def, tenv_tabbrev_ok_merge] >>
     full_simp_tac(srw_ss())[tenv_tabbrev_ok_def] >>
     PairCases_on `new_tenv1` >>
     PairCases_on `new_tenv` >>
     full_simp_tac(srw_ss())[append_new_dec_tenv_def] >>
     first_x_assum match_mp_tac >>
     simp [extend_env_new_decs_def] >>
     match_mp_tac tenv_tabbrev_ok_merge >>
     srw_tac[][tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list]));

val type_ds_tenvT_ok = Q.store_thm ("type_ds_tenvT_ok",
`!x tvs tdecs tenv ds tdecs' new_tenv.
  type_ds x tvs tdecs tenv ds tdecs' new_tenv ⇒
  tenv_tabbrev_ok tenv.t
  ⇒
  flat_tenv_tabbrev_ok (FST new_tenv)`,
 ho_match_mp_tac type_ds_strongind >>
 srw_tac[][]  >>
 imp_res_tac type_d_tenvT_ok >>
 srw_tac[][flat_tenv_tabbrev_ok_def] >>
 full_simp_tac(srw_ss())[flat_tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
 srw_tac[][] >>
 PairCases_on `new_tenv` >>
 PairCases_on `new_tenv1` >>
 full_simp_tac(srw_ss())[append_new_dec_tenv_def, FLOOKUP_FUNION, extend_env_new_decs_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 `tenv_tabbrev_ok (FEMPTY:tvarN |-> flat_tenv_tabbrev, new_tenv10)`
      by (full_simp_tac(srw_ss())[tenv_tabbrev_ok_def,flat_tenv_tabbrev_ok_def] >>
          full_simp_tac(srw_ss())[FEVERY_FEMPTY,FEVERY_ALL_FLOOKUP] >>
          metis_tac []) >>
  full_simp_tac(srw_ss())[flat_tenv_tabbrev_ok_def]>>
  metis_tac[tenv_tabbrev_ok_merge]);

(* ---------- type_specs ---------- *)

val type_specs_tenv_ok = Q.store_thm ("type_specs_tenv_ok",
`!tvs tenvT specs decls' new_tenv.
  type_specs tvs tenvT specs decls' new_tenv ⇒
  tenv_tabbrev_ok tenvT ⇒
    (tenv_val_ok (bind_var_list2 (SND (SND new_tenv)) Empty) ∧
     flat_tenv_tabbrev_ok (FST new_tenv))`,
 ho_match_mp_tac type_specs_ind >>
 srw_tac[][bind_var_list2_def, tenv_val_ok_def]
 >- srw_tac[][flat_tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP]
 >> PairCases_on`new_tenv`>>full_simp_tac(srw_ss())[append_new_dec_tenv_def]
 >- (srw_tac[][bind_var_list2_def, tenv_val_ok_def, num_tvs_bvl2, num_tvs_def] >>
     induct_on `new_tenv2` >>
     srw_tac[][]
     >- (srw_tac[][bind_var_list2_def, tenv_val_ok_def, num_tvs_bvl2, num_tvs_def] >>
         match_mp_tac check_freevars_subst_single >>
         srw_tac[][LENGTH_GENLIST, EVERY_MAP] >>
         srw_tac[][EVERY_MEM] >>
         full_simp_tac(srw_ss())[MEM_GENLIST, check_freevars_def] >>
         match_mp_tac check_freevars_type_name_subst >>
         metis_tac [check_freevars_add, DECIDE ``!x:num. x ≥ 0``])
     >- (PairCases_on `h` >>
         full_simp_tac(srw_ss())[bind_var_list2_def, tenv_val_ok_def, num_tvs_bvl2, num_tvs_def])) >>
 TRY (
   qpat_assum`_ ⇒ _`mp_tac >>
   impl_tac >- (
     match_mp_tac tenv_tabbrev_ok_merge >>
     srw_tac[][tenv_tabbrev_ok_def, FEVERY_FEMPTY, flat_tenv_tabbrev_ok_def,
         FEVERY_ALL_FLOOKUP, flookup_fupdate_list, FLOOKUP_UPDATE] >>
     every_case_tac >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss())[MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     srw_tac[][check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
   strip_tac)
 >- (full_simp_tac(srw_ss())[FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, flookup_fupdate_list,FLOOKUP_UPDATE, flat_tenv_tabbrev_ok_def] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     TRY (first_x_assum match_mp_tac >>
          qexists_tac `k` >>
          simp [] >>
          NO_TAC) >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss())[check_ctor_tenv_def, EVERY_MEM, MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     srw_tac[][check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
 TRY (
   qpat_assum`_ ⇒ _`mp_tac >>
   impl_tac >- (
     match_mp_tac tenv_tabbrev_ok_merge >>
     srw_tac[][tenv_tabbrev_ok_def, FEVERY_FEMPTY, flat_tenv_tabbrev_ok_def,
         FEVERY_ALL_FLOOKUP, flookup_fupdate_list, FLOOKUP_UPDATE] >>
     match_mp_tac check_freevars_type_name_subst >>
     srw_tac[][]) >>
   strip_tac)
 >- (full_simp_tac(srw_ss())[flat_tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][]
     >- (match_mp_tac check_freevars_type_name_subst >>
         srw_tac[][]) >>
     full_simp_tac(srw_ss())[PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     qexists_tac `k` >>
     simp [])
 >- (full_simp_tac(srw_ss())[flat_tenv_tabbrev_ok_def, FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[check_freevars_def, EVERY_MAP, EVERY_MEM] >>
     full_simp_tac(srw_ss())[PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     qexists_tac `k` >>
     simp []));

val type_specs_no_mod = Q.store_thm ("type_specs_no_mod",
`!mn tenvT specs decls' new_tenv.
  type_specs mn tenvT specs decls' new_tenv ⇒
  decls'.defined_mods = {}`,
 ho_match_mp_tac type_specs_strongind >>
 srw_tac[][empty_decls_def] >>
 imp_res_tac type_d_mod >>
 full_simp_tac(srw_ss())[union_decls_def]);

(* ---------------- type_top, type_prog uniqueness flag ---------- *)

val type_top_tenv_ok = store_thm("type_top_tenv_ok",
  ``∀ch decls tenv top decls' env.
    type_top ch decls tenv top decls' env ⇒
    ∀tenvT' menv' cenv' tenv'.
    env = (tenvT',menv',cenv',tenv') ⇒
      num_tvs tenv.v = 0 ⇒
      tenv_tabbrev_ok tenv.t ⇒
      tenv_val_ok (bind_var_list2 tenv' Empty) ∧
      FEVERY (λ(mn,tenv). tenv_val_ok (bind_var_list2 tenv Empty)) menv'``,
  ho_match_mp_tac type_top_ind >>
  srw_tac[][FEVERY_FEMPTY,FEVERY_FUPDATE,bind_var_list2_def,
     typeSoundInvariantsTheory.tenv_val_ok_def] >>
  imp_res_tac type_d_tenv_ok >>
  TRY(qpat_assum`lift_new_dec_tenv A = B` (assume_tac o SYM)>>
  PairCases_on`new_tenv`)>>
  full_simp_tac(srw_ss())[check_signature_cases,lift_new_dec_tenv_def,FEVERY_FEMPTY] >>
  imp_res_tac type_ds_tenv_ok >>
  TRY(qpat_assum`mod_lift_new_dec_tenv A B = C` (assume_tac o SYM)>>
  PairCases_on`new_tenv2`)>>
  full_simp_tac(srw_ss())[mod_lift_new_dec_tenv_def,bind_var_list2_def,
     typeSoundInvariantsTheory.tenv_val_ok_def]>>
  full_simp_tac(srw_ss())[FEVERY_FEMPTY,FEVERY_FUPDATE] >>
  PairCases_on`new_tenv1`>>full_simp_tac(srw_ss())[weak_new_dec_tenv_def] >>
  imp_res_tac type_specs_tenv_ok >> full_simp_tac(srw_ss())[])

val type_top_check_uniq = Q.store_thm ("type_top_check_uniq",
`!uniq tdecs tenv top tdecs' new_tenv.
  type_top uniq tdecs tenv top tdecs' new_tenv
  ⇒
  type_top F tdecs tenv top tdecs' new_tenv`,
 srw_tac[][type_top_cases] >>
 metis_tac [type_d_check_uniq, type_ds_check_uniq]);

val type_prog_check_uniq = Q.store_thm ("type_prog_check_uniq",
`!uniq tdecs tenv prog tdecs' new_tenv.
  type_prog uniq tdecs tenv prog tdecs' new_tenv
  ⇒
  type_prog F tdecs tenv prog tdecs' new_tenv`,
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_prog_cases] >>
 metis_tac [type_top_check_uniq]);

(* closed *)

val _ = Parse.overload_on("tmenv_dom",``λmenv. {Long m x | (m,x) | ∃e.  FLOOKUP menv m = SOME e ∧ MEM x (MAP FST e)}``);

open boolSimps evalPropsTheory

val tenv_names_def = Define`
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)`
val _ = export_rewrites["tenv_names_def"]

val lookup_tenv_names = store_thm("lookup_tenv_names",
  ``∀tenv n inc x. lookup_tenv_val n inc tenv = SOME x ⇒ n ∈ tenv_names tenv``,
  Induct >> simp[lookup_tenv_val_def] >> metis_tac[])

val tenv_names_bind_var_list = store_thm("tenv_names_bind_var_list",
  ``∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2``,
  ho_match_mp_tac bind_var_list_ind >>
  simp[bind_var_list_def,EXTENSION] >>
  metis_tac[])

val tenv_names_bind_var_list2 = store_thm("tenv_names_bind_var_list2",
  ``∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv``,
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >> simp[bind_var_list2_def] >>
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
  srw_tac[][] >> full_simp_tac(srw_ss())[SUBSET_DEF] >>
  srw_tac[][Once evalPropsTheory.pat_bindings_accum]);

val type_funs_dom = Q.prove (
  `!tenv funs tenv'.
    type_funs tenv funs tenv'
    ⇒
    IMAGE FST (set funs) = IMAGE FST (set tenv')`,
   Induct_on `funs` >>
   srw_tac[][Once type_e_cases] >>
   srw_tac[][] >>
   metis_tac []);

val type_e_closed = prove(
  ``(∀tenv e t.
      type_e tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)) ∧
    (∀tenv es ts.
      type_es tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)) ∧
    (∀tenv funs ts.
      type_funs tenv funs ts ⇒
      FV_defs funs ⊆ (IMAGE Short (tenv_names tenv.v)) ∪ tmenv_dom tenv.m)``,
  ho_match_mp_tac type_e_strongind >>
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
    srw_tac[][] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes` >>
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
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp[MEM_FLAT,MEM_MAP,EXISTS_PROD] >-
      metis_tac[lookup_tenv_names] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD] >>
    srw_tac[][] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac [] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP] >>
    srw_tac[][] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes` >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac) >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >> metis_tac[]) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[opt_bind_name_def] >>
    metis_tac[] ) >>
    (* COMPLETENESS
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[opt_bind_name_def] >>
    metis_tac[] ) >> *)
  strip_tac >- (
    simp[tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac type_funs_dom >>
    full_simp_tac(srw_ss())[SUBSET_DEF] >>
    srw_tac[][] >>
    res_tac >>
    full_simp_tac(srw_ss())[MEM_MAP] >>
    `tenv_names (bind_tvar tvs tenv.v) = tenv_names tenv.v`
               by (srw_tac[][bind_tvar_def] >>
                   every_case_tac >>
                   full_simp_tac(srw_ss())[tenv_names_def]) >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][] >>
    res_tac >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[EXTENSION] >>
    metis_tac []) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  simp[] >>
  srw_tac[][SUBSET_DEF] >>
  res_tac >>
  fsrw_tac[DNF_ss][MEM_MAP,FV_defs_MAP,UNCURRY] >>
  srw_tac[][] >>
  metis_tac []);

val type_d_closed = prove(
  ``∀uniq mno decls tenv d w x.
      type_d uniq mno decls tenv d w x ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)``,
  ho_match_mp_tac type_d_ind >>
  strip_tac >- (
    simp[bind_tvar_def] >>
    rpt gen_tac >>
    Cases_on`tvs=0`>>simp[]>>strip_tac>>
    imp_res_tac (CONJUNCT1 type_e_closed) >> full_simp_tac(srw_ss())[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT1 type_e_closed) >> full_simp_tac(srw_ss())[]) >>
  strip_tac >- (
    srw_tac[][] >>
    imp_res_tac (CONJUNCT2 type_e_closed) >>
    full_simp_tac(srw_ss())[tenv_names_bind_var_list,LET_THM] >>
    `tenv_names (bind_tvar tvs tenv.v) = tenv_names tenv.v`
              by (srw_tac[][bind_tvar_def] >>
                  every_case_tac >>
                  srw_tac[][tenv_names_def]) >>
    full_simp_tac(srw_ss())[SUBSET_DEF] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[MEM_MAP] >>
    res_tac >>
    srw_tac[][] >>
    imp_res_tac type_funs_dom >>
    full_simp_tac(srw_ss())[EXTENSION] >>
    metis_tac[]) >>
  simp[]);

  (*
val type_d_new_dec_vs = Q.prove (
  `!uniq mn decls tenv d decls' new_tenv.
    type_d uniq mn decls tenv d decls' new_tenv
    ⇒
    set (new_dec_vs d) = set (MAP FST tenv')`,
   srw_tac[][type_d_cases, new_dec_vs_def] >>
   srw_tac[][new_dec_vs_def] >>
   imp_res_tac type_p_closed >>
   srw_tac[][tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
   full_simp_tac(srw_ss())[LET_THM, LIST_TO_SET_MAP, FST_pair, IMAGE_COMPOSE] >>
   metis_tac [type_funs_dom]);
   *)

   (*
val type_ds_closed = prove(
  ``∀uniq mn decls tenv ds w x. type_ds uniq mn decls tenv ds w x ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)``,
  ho_match_mp_tac type_ds_ind >>
  srw_tac[][FV_decs_def] >>
  imp_res_tac type_d_closed >>
  full_simp_tac(srw_ss())[tenv_names_bind_var_list2] >>
  srw_tac[][SUBSET_DEF] >>
  `x ∈ IMAGE Short (set (MAP FST tenv')) ∪ IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m`
           by full_simp_tac(srw_ss())[SUBSET_DEF] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_MAP] >>
  metis_tac [type_d_new_dec_vs,MEM_MAP]);
  *)

  (*
val type_top_closed = store_thm("type_top_closed",
  ``∀uniq decls tenv top decls' new_tenv.
      type_top uniq decls tenv top decls' new_tenv
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)``,
  ho_match_mp_tac type_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    metis_tac [type_d_closed]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac type_ds_closed >>
  full_simp_tac(srw_ss())[]);
  *)

val type_env_dom = Q.prove (
  `!ctMap tenvS env tenv.
    type_env ctMap tenvS env tenv ⇒
    IMAGE Short (set (MAP FST env)) = IMAGE Short (tenv_names tenv)`,
   induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   srw_tac[][] >>
   srw_tac[][] >>
   metis_tac []);

val weakM_dom = Q.prove (
  `!tenvM1 tenvM2.
    weakM tenvM1 tenvM2
    ⇒
    tmenv_dom tenvM2 ⊆ tmenv_dom tenvM1`,
   srw_tac[][weakM_def, SUBSET_DEF] >>
   res_tac >>
   srw_tac[][] >>
   full_simp_tac(srw_ss())[weakE_def] >>
   qpat_assum `!x. P x` (mp_tac o Q.SPEC `x'`) >>
   every_case_tac >>
   full_simp_tac(srw_ss())[ALOOKUP_FAILS] >>
   srw_tac[][] >>
   imp_res_tac ALOOKUP_MEM >>
   full_simp_tac(srw_ss())[MEM_MAP] >>
   metis_tac [FST, pair_CASES]);

val type_env_dom2 = Q.prove (
  `!ctMap tenvS env tenv.
    type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇒
    (set (MAP FST env) = set (MAP FST tenv))`,
   induct_on `env` >>
   ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
   full_simp_tac(srw_ss())[bind_var_list2_def, tenv_names_def] >>
   full_simp_tac(srw_ss())[tenv_names_def] >>
   srw_tac[][] >>
   srw_tac[][] >>
   cases_on `tenv` >>
   TRY (PairCases_on `h`) >>
   full_simp_tac(srw_ss())[bind_var_list2_def] >>
   metis_tac []);

val consistent_mod_env_dom = Q.prove (
  `!tenvS tenvC envM tenvM.
    consistent_mod_env tenvS tenvC envM tenvM
    ⇒
    (tmenv_dom tenvM = {Long m x | ∃e. ALOOKUP envM m = SOME e ∧ MEM x (MAP FST e)})`,
   induct_on `envM` >>
   srw_tac[][]
   >- (Cases_on `tenvM` >>
       full_simp_tac(srw_ss())[Once type_v_cases]) >>
   pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
   srw_tac[][] >>
   res_tac >>
   srw_tac[][] >>
   imp_res_tac type_env_dom2 >>
   full_simp_tac(srw_ss())[EXTENSION, FLOOKUP_UPDATE] >>
   srw_tac[][] >>
   eq_tac >>
   srw_tac[][] >>
   every_case_tac >>
   srw_tac[][] >>
   full_simp_tac(srw_ss())[MEM_MAP] >>
   srw_tac[][] >>
   res_tac >>
   full_simp_tac(srw_ss())[] >>
   metis_tac []);

   (*
val type_sound_inv_closed = Q.store_thm ("type_sound_inv_closed",
  `∀uniq top rs new_tenvM new_tenvC new_tenv new_decls new_tenvT decls' store.
    type_top uniq rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top new_decls new_tenvT new_tenvM new_tenvC new_tenv ∧
    type_sound_invariants NONE (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,decls',rs.sem_env,store)
    ⇒
    FV_top top ⊆ all_env_dom (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)`,
  srw_tac[][] >>
  imp_res_tac type_top_closed >>
  `(?err. r = Rerr err) ∨ (?menv env. r = Rval (menv,env))`
          by (cases_on `r` >>
              srw_tac[][] >>
              PairCases_on `a` >>
              full_simp_tac(srw_ss())[])  >>
  full_simp_tac(srw_ss())[all_env_dom_def, type_sound_invariants_def, update_type_sound_inv_def] >>
  srw_tac[][] >>
  imp_res_tac weakM_dom >>
  imp_res_tac type_env_dom >>
  imp_res_tac (GSYM consistent_mod_env_dom) >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac []);
  *)

val _ = export_theory ();
