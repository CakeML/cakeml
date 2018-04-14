(* Theorems about the type system. *)

open preamble
open libTheory astTheory namespaceTheory typeSystemTheory typeSoundInvariantsTheory terminationTheory;
open astPropsTheory;
open namespacePropsTheory;
local open semanticPrimitivesPropsTheory in end

val _ = new_theory "typeSysProps";

val find_recfun_def = semanticPrimitivesTheory.find_recfun_def;
val same_tid_def = semanticPrimitivesTheory.same_tid_def;
val check_dup_ctors_cons = semanticPrimitivesPropsTheory.check_dup_ctors_cons;
val no_dup_types_def = semanticPrimitivesTheory.no_dup_types_def;
val decs_to_types_def = semanticPrimitivesTheory.decs_to_types_def;

(* ----------- Basic stuff ----------- *)

val unchanged_tenv = Q.store_thm ("unchanged_tenv[simp]",
 `!(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv`,
 rw [type_env_component_equality]);

val union_decls_assoc = Q.store_thm ("union_decls_assoc[simp]",
`!decls1 decls2 decls3.
  union_decls decls1 (union_decls decls2 decls3)
  =
  union_decls (union_decls decls1 decls2) decls3`,
 srw_tac[][] >>
 srw_tac[][union_decls_def] >>
 metis_tac [UNION_ASSOC]);

val union_decls_sym = Q.store_thm ("union_decls_sym",
`!decls1 decls2. union_decls decls1 decls2 = union_decls decls2 decls1`,
 rw [union_decls_def] >>
 rw [UNION_COMM]);

val union_decls_mods = Q.store_thm ("union_decls_mods[simp]",
 `(union_decls d1 d2).defined_mods = d1.defined_mods ∪ d2.defined_mods`,
 rw [union_decls_def]);

val union_decls_empty = Q.store_thm ("union_decls_empty[simp]",
  `!d. union_decls empty_decls d = d ∧ union_decls d empty_decls = d`,
 rw [union_decls_def, decls_component_equality, empty_decls_def]);

val extend_dec_tenv_assoc = Q.store_thm ("extend_dec_tenv_assoc[simp]",
  `!tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3`,
 rw [extend_dec_tenv_def]);

val tenv_val_ok_nsEmpty = Q.store_thm ("tenv_val_ok_nsEmpty[simp]",
  `tenv_val_ok nsEmpty`,
 rw [tenv_val_ok_def]);

val tenv_ctor_ok_nsEmpty = Q.store_thm ("tenv_ctor_ok_nsEmpty[simp]",
  `tenv_ctor_ok nsEmpty`,
 rw [tenv_ctor_ok_def]);

val tenv_abbrev_ok_nsEmpty = Q.store_thm ("tenv_abbrev_ok_nsEmpty[simp]",
  `tenv_abbrev_ok nsEmpty`,
 rw [tenv_abbrev_ok_def]);

val tenv_ok_empty = Q.store_thm ("tenv_ok_empty[simp]",
  `tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>`,
 rw [tenv_ok_def, tenv_val_ok_def, tenv_ctor_ok_def, tenv_abbrev_ok_def]);

val type_pes_def = Define `
  type_pes tvs tvs' tenv tenvE pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e tenv (bind_var_list tvs' bindings tenvE) e t2)`;

val type_pes_cons = Q.store_thm ("type_pes_cons",
  `!tvs tvs' tenv tenvE p e pes t1 t2.
    type_pes tvs tvs' tenv tenvE ((p,e)::pes) t1 t2 ⇔
    (ALL_DISTINCT (pat_bindings p []) ∧
     (?bindings.
         type_p tvs tenv p t1 bindings ∧
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2) ∧
     type_pes tvs tvs' tenv tenvE pes t1 t2)`,
 rw [type_pes_def, RES_FORALL] >>
 eq_tac >>
 rw [] >>
 rw []
 >- (
   pop_assum (qspec_then `(p,e)` mp_tac)
   >> rw [])
 >- (
   pop_assum (qspec_then `(p,e)` mp_tac)
   >> rw []
   >> metis_tac [])
 >> metis_tac []);

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
  LENGTH tvs = LENGTH ts ∧
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
  tvs = LENGTH targs + tvs' ∧
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

val check_freevars_subst = Q.store_thm ("check_freevars_subst",
`∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t)`,
ho_match_mp_tac check_freevars_ind >>
srw_tac[][check_freevars_def, deBruijn_inc_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM] >>
cases_on `n < LENGTH targs` >>
srw_tac[][deBruijn_subst_def, check_freevars_def] >>
full_simp_tac(srw_ss())[MEM_EL] >-
metis_tac [] >-
decide_tac >>
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
rw[] >> fs[] >>
metis_tac [subst_inc_cancel, LENGTH_MAP]);

val deBruijn_subst_id = Q.store_thm ("deBruijn_subst_id",
`(!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts))`,
Induct >>
srw_tac[][deBruijn_subst_def, LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST,
    check_freevars_def] >>
metis_tac []);

val deBruijn_subst_freevars = Q.store_thm ("deBruijn_subst_freevars",
`!skip targs t tvs.
  skip = 0 ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t
  ⇒
  check_freevars tvs [] (deBruijn_subst skip targs t)`,
ho_match_mp_tac deBruijn_subst_ind >>
srw_tac[][check_freevars_def, deBruijn_subst_def, EVERY_MAP] >>
full_simp_tac(srw_ss())[EVERY_MEM, MEM_EL] >>
metis_tac []);

(* ---------- tenv_abbrev stuff ---------- *)

val tenv_abbrev_ok_lookup = Q.store_thm ("tenv_abbrev_ok_lookup",
`!tenvT tn tvs t.
  tenv_abbrev_ok tenvT ∧
  nsLookup tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t`,
 rw [tenv_abbrev_ok_def]
 >> drule nsLookup_nsAll
 >> disch_then drule
 >> simp []);

val check_freevars_type_name_subst = Q.store_thm ("check_freevars_type_name_subst",
`!dbmax tvs t tenvT.
  tenv_abbrev_ok tenvT ∧
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
 imp_res_tac tenv_abbrev_ok_lookup >>
 metis_tac [check_freevars_add, numeralTheory.numeral_distrib]);

val tenv_abbrev_ok_merge = Q.store_thm ("tenv_abbrev_ok_merge",
`!tenvT1 tenvT2.
  tenv_abbrev_ok tenvT1 ∧ tenv_abbrev_ok tenvT2
  ⇒
  tenv_abbrev_ok (nsAppend tenvT1 tenvT2)`,
 rw [tenv_abbrev_ok_def]
 >> irule nsAll_nsAppend
 >> rw []);

(* ---------- tenv_ctor stuff ----------*)

val type_ctor_long = Q.store_thm ("type_ctor_long",
  `!ctMap mn id. type_ctor ctMap (Long mn id) = type_ctor ctMap id`,
 rw [FUN_EQ_THM]
 >> PairCases_on `x`
 >> PairCases_on `x'`
 >> simp [type_ctor_def, id_to_n_def]);

val tenv_ctor_ok_merge = Q.store_thm ("tenv_ctor_ok_merge[simp]",
  `!tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2)`,
 rw [tenv_ctor_ok_def]
 >> irule nsAll_nsAppend
 >> rw []);

val tenv_ctor_ok_lookup = Q.store_thm ("tenv_ctor_ok_lookup",
  `!tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
    ⇒
    EVERY (check_freevars 0 tvs) ts`,
 rw [tenv_ctor_ok_def]
 >> drule nsLookup_nsAll
 >> disch_then drule
 >> simp []);

(* ---------- tenv_val_exp stuff ---------- *)

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

val bind_tvar_rewrites = Q.store_thm ("bind_tvar_rewrites[simp]",
  `(!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs e. num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs n t e. num_tvs (Bind_name n tvs t e) = num_tvs e) ∧
   (!tvs e. num_tvs Empty = 0) ∧
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc+tvs) e) ∧
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) ⇔ tenv_val_exp_ok e) ∧
   (!targs tvs e.
     deBruijn_subst_tenvE targs (bind_tvar tvs e) =
     bind_tvar tvs (deBruijn_subst_tenvE targs e))`,
 srw_tac[][bind_tvar_def, deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def,
    tveLookup_def, tenv_val_exp_ok_def]);

val bind_tvar0 = Q.store_thm ("bind_tvar0[simp]",
`!x. bind_tvar 0 x = x`,
  Cases_on `x`
  >> rw [bind_tvar_def]);

val tveLookup_subst_none = Q.store_thm ("tveLookup_subst_none",
`!n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE`,
induct_on `e` >>
srw_tac[][deBruijn_subst_tenvE_def, tveLookup_def]);

val tveLookup_db_merge_none = Q.store_thm ("tveLookup_db_merge_none",
`!n inc e1 e2.
  tveLookup n inc (db_merge e1 e2) = NONE
  ⇔
  tveLookup n inc e1 = NONE ∧ tveLookup n (num_tvs e1 + inc) e2 = NONE`,
 Induct_on `e1`
 >> rw [tveLookup_def, db_merge_def]);

val tveLookup_inc_none = Q.store_thm ("tveLookup_inc_none",
`!n inc e.
  tveLookup n inc e = NONE
  ⇔
  tveLookup n 0 e = NONE`,
 Induct_on `e`
 >> rw [tveLookup_def]);

val tveLookup_freevars = Q.store_thm ("tveLookup_freevars",
  `!n tvs tenvE tvs' t.
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    tveLookup n tvs tenvE = SOME (tvs',t)
    ⇒
    check_freevars tvs' [] t`,
 Induct_on `tenvE`
 >> rw [tveLookup_def, tenv_val_exp_ok_def]
 >> fs []
 >> metis_tac [nil_deBruijn_inc]);

val tveLookup_bvl = Q.store_thm ("tveLookup_bvl",
  `!x tvs tvs' bindings tenvE.
    tveLookup x tvs (bind_var_list tvs' bindings tenvE)
    =
    case ALOOKUP bindings x of
    | SOME t => SOME (tvs',deBruijn_inc tvs' tvs t)
    | NONE => tveLookup x tvs tenvE`,
 Induct_on `bindings`
 >> rw [bind_var_list_def]
 >> PairCases_on `h`
 >> rw [bind_var_list_def, tveLookup_def]);

val bind_var_list_append = Q.store_thm ("bind_var_list_append",
`!n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3)`,
induct_on `te1` >>
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def]);

val num_tvs_bind_var_list = Q.store_thm ("num_tvs_bind_var_list[simp]",
`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE`,
induct_on `env` >>
srw_tac[][num_tvs_def, bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, num_tvs_def]);

val tenv_val_exp_ok_bvl = Q.store_thm ("tenv_val_exp_ok_bvl",
`!tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
 Induct_on `env` >>
 srw_tac[][tenv_val_exp_ok_def, bind_var_list_def] >>
 PairCases_on `h` >>
 srw_tac[][tenv_val_exp_ok_def, bind_var_list_def]
 >> fs []);

val tveLookup_subst_some = Q.store_thm ("tveLookup_subst_some",
  `∀n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t)
    ⇒
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t)`,
 induct_on `e` >>
 srw_tac[][tveLookup_def,deBruijn_subst_tenvE_def, deBruijn_inc_def, num_tvs_def, type_e_subst_lem5]
 >> metis_tac [arithmeticTheory.ADD_ASSOC]);

val num_tvs_db_merge = Q.store_thm ("num_tvs_db_merge[simp]",
`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
induct_on `e1` >>
srw_tac[][num_tvs_def, db_merge_def] >>
decide_tac);

val num_tvs_deBruijn_subst_tenvE = Q.store_thm ("num_tvs_deBruijn_subst_tenvE[simp]",
`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE`,
induct_on `tenvE` >>
srw_tac[][deBruijn_subst_tenvE_def, num_tvs_def]);

val tveLookup_inc_some = Q.store_thm ("tveLookup_inc_some",
`!n inc e tvs t inc2.
   tveLookup n inc e = SOME (tvs, t)
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t'))`,
induct_on `e` >>
srw_tac[][deBruijn_inc_def, tveLookup_def] >>
srw_tac[][] >>
metis_tac [deBruijn_inc_deBruijn_inc]);

val tveLookup_add_inc = Q.store_thm ("tveLookup_add_inc",
`!x inc tenv tvs t inc2.
  (tveLookup x inc tenv = SOME (tvs,t))
  ⇒
  (tveLookup x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t))`,
induct_on `tenv` >>
srw_tac[][tveLookup_def] >>
srw_tac[][deBruijn_inc_deBruijn_inc] >>
metis_tac [arithmeticTheory.ADD_ASSOC]);

val tveLookup_freevars_subst = Q.store_thm ("tveLookup_freevars_subst",
  `!tenvE targs n t inc.
    EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
    tveLookup n inc tenvE = SOME (LENGTH targs,t) ∧
    tenv_val_exp_ok tenvE
    ⇒
    check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)`,
 induct_on `tenvE` >>
 rw [check_freevars_def, num_tvs_def, tveLookup_def, tenv_val_exp_ok_def] >>
 metis_tac [deBruijn_subst_check_freevars, arithmeticTheory.ADD_ASSOC,
            check_freevars_subst_inc]);

val tenv_val_exp_ok_db_merge = Q.store_thm ("tenv_val_exp_ok_db_merge",
`!e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2`,
induct_on `e1` >>
srw_tac[][tenv_val_exp_ok_def, db_merge_def]);

val tveLookup_freevars = Q.prove (
`!e n inc t tvs.
  tenv_val_exp_ok e ∧
  tveLookup n inc e = SOME (tvs, t)
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t`,
 induct_on `e` >>
 srw_tac[][tveLookup_def, num_tvs_def, tenv_val_exp_ok_def] >|
 [metis_tac [arithmeticTheory.ADD_ASSOC],
  imp_res_tac check_freevars_deBruijn_inc >>
      metis_tac [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM],
  metis_tac []]);

val tveLookup_no_tvs = Q.store_thm ("tveLookup_no_tvs",
`!tvs l tenv n t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0
  ⇒
  (tveLookup n tvs tenv = SOME (l,t)
   ⇔
   tveLookup n 0 tenv = SOME (l,t))`,
induct_on `tenv` >>
srw_tac[][tveLookup_def, num_tvs_def, tenv_val_exp_ok_def] >>
eq_tac >>
srw_tac[][] >>
full_simp_tac(srw_ss())[] >>
metis_tac [nil_deBruijn_inc, deBruijn_inc0]);

val deBruijn_subst_E_bvl = Q.store_thm ("deBruijn_subst_E_bvl",
`!tenv1 tenv2 tvs.
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
  =
  bind_var_list tvs
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
          (deBruijn_subst_tenvE targs tenv2)`,
induct_on `tenv1` >>
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, deBruijn_subst_tenvE_def]);

val db_merge_bvl = Q.store_thm ("db_merge_bvl",
`!tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3)`,
induct_on `tenv1` >>
srw_tac[][bind_var_list_def] >>
PairCases_on `h` >>
srw_tac[][bind_var_list_def, db_merge_def]);

val tveLookup_db_merge_some = Q.store_thm ("tveLookup_db_merge_some",
  `!n inc tenvE1 tenvE2 tvs t.
    tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t)
    ⇔
    tveLookup n inc tenvE1 = SOME (tvs,t) ∨
    (tveLookup n inc tenvE1 = NONE ∧
     tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs, t))`,
 Induct_on `tenvE1`
 >> rw [db_merge_def, tveLookup_def]);

(* ---------- type_op ---------- *)

val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def };
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val tctor_thms = { nchotomy = tctor_nchotomy, case_def = tctor_case_def };
val t_thms = { nchotomy = t_nchotomy, case_def = t_case_def };
val word_size_thms = { nchotomy = word_size_nchotomy, case_def = word_size_case_def };
val id_thms = { nchotomy = id_nchotomy, case_def = id_case_def };
val thms = [ op_thms, list_thms, tctor_thms, t_thms, word_size_thms, id_thms ]
val eqs = ([pair_case_eq,bool_case_eq]@(List.map prove_case_eq_thm thms))
val elims = List.map prove_case_elim_thm thms

val type_op_cases = save_thm("type_op_cases",
  ``type_op op ts t3``
  |> (SIMP_CONV(srw_ss())(type_op_def::eqs@elims) THENC
      SIMP_CONV (bool_ss++DNF_ss) [
        PULL_EXISTS,
        GSYM Tchar_def,
        GSYM Tword_def,
        GSYM Tword8_def,
        GSYM Tword64_def,
        GSYM TC_word_def]));

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
    tenv_abbrev_ok tenv.t ∧
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
    tenv_abbrev_ok tenv.t ∧
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
  `(!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv'))`,
 ho_match_mp_tac type_p_ind >>
 srw_tac[][bind_var_list_def, tenv_val_exp_ok_def, num_tvs_def, bind_var_list_append] >>
 `tvs + num_tvs tenv' ≥ tvs` by decide_tac >>
 metis_tac [check_freevars_add]);

val type_p_tenvV_indep = Q.store_thm ("type_p_tenvV_indep",
`(!p tvs tenv t bindings tenvV.
  type_p tvs tenv p t bindings = type_p tvs (tenv with v := tenvV) p t bindings) ∧
 (!ps tvs tenv t bindings tenvV.
  type_ps tvs tenv ps t bindings = type_ps tvs (tenv with v := tenvV) ps t bindings)`,
 Induct >>
 rw [] >>
 ONCE_REWRITE_TAC [type_p_cases] >>
 simp [] >>
 metis_tac []);

(* ---------- type_e, type_es, type_funs ---------- *)

val type_es_list_rel = Q.store_thm ("type_es_list_rel",
`!es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts`,
 induct_on `es` >>
 srw_tac[][] >>
 srw_tac[][Once type_e_cases]);

val type_es_length = Q.store_thm ("type_es_length",
`∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
srw_tac[][Once type_e_cases] >>
srw_tac[][] >>
metis_tac []);

val type_funs_MAP_FST = Q.store_thm("type_funs_MAP_FST",
`!funs tenv tenvE env.
  type_funs tenv tenvE funs env ⇒
  MAP FST funs = MAP FST env`,
  Induct>>srw_tac[][]>>
  pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
  full_simp_tac(srw_ss())[]>>metis_tac[])

val tenv_val_exp_ok_bvl_tvs = Q.store_thm ("tenv_val_exp_ok_bvl_tvs",
  `!funs tenv env tvs bindings tenvE.
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list tvs env tenvE)`,
 induct_on `funs`
 >> rw []
 >> qpat_x_assum `type_funs _ _ _ _` mp_tac
 >> simp [Once type_e_cases]
 >> rw [check_freevars_def]
 >> rw [check_freevars_def, bind_var_list_def, tenv_val_exp_ok_def]
 >> metis_tac []);

val tenv_val_exp_ok_bvl_funs = Q.store_thm ("tenv_val_exp_ok_bvl_funs",
  `!funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
 induct_on `funs`
 >> rw []
 >> qpat_x_assum `type_funs _ _ _ _` mp_tac
 >> simp [Once type_e_cases]
 >> rw [check_freevars_def]
 >> rw [check_freevars_def, bind_var_list_def, tenv_val_exp_ok_def]
 >> metis_tac []);

val type_e_freevars = Q.store_thm ("type_e_freevars",
`(!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env))`,
 ho_match_mp_tac type_e_strongind >>
 srw_tac[][check_freevars_def, num_tvs_def, type_op_cases,
     tenv_val_ok_def, bind_tvar_def, bind_var_list_def, opt_bind_name_def] >>
 full_simp_tac(srw_ss())[check_freevars_def,Tchar_def,Tword_def,Tword64_def]
 >- metis_tac [deBruijn_subst_check_freevars]
 >- metis_tac []
 >- (
   fs [lookup_var_def, lookup_varE_def]
   >> every_case_tac
   >> fs []
   >> rw []
   >- (
     drule nsLookup_nsAll
     >> disch_then drule
     >> simp []
     >> rw []
     >> irule deBruijn_subst_check_freevars2
     >> simp [])
   >- metis_tac [tveLookup_freevars_subst, DECIDE ``x+0n = x ∧ 0n+x = x``]
   >- (
     drule nsLookup_nsAll
     >> disch_then drule
     >> simp []
     >> rw []
     >> irule deBruijn_subst_check_freevars2
     >> simp []))
 >- fs [tenv_val_exp_ok_def]
 >- (cases_on `pes` >>
     full_simp_tac(srw_ss())[] >>
     fs [FORALL_PROD, RES_FORALL]
     >> metis_tac [pair_CASES, type_p_freevars, tenv_val_exp_ok_bvl])
 >- (every_case_tac >>
     fs [num_tvs_def, tenv_val_exp_ok_def])
 >- metis_tac [tenv_val_exp_ok_bvl_funs, num_tvs_bind_var_list]);

val type_e_subst = Q.store_thm ("type_e_subst",
`(!tenv tenvE e t. type_e tenv tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                   e
                   (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                  es
                  (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
 (!tenv tenvE funs env. type_funs tenv tenvE funs env ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                      funs
                      (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env))`,
 ho_match_mp_tac type_e_strongind >>
 srw_tac[][] >>
 ONCE_REWRITE_TAC [type_e_cases] >>
 srw_tac[][deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_name_def,
     num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE] >>
 full_simp_tac(srw_ss())[deBruijn_subst_def, deBruijn_subst_tenvE_def, opt_bind_name_def,
     num_tvs_def, OPTION_MAP_DEF,
     num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, tenv_val_ok_def, Tchar_def]
 >- simp[Tword_def,deBruijn_subst_def]
 >- simp[Tword_def,deBruijn_subst_def,Tword64_def]
 >- metis_tac [check_freevars_lem]
 >- (full_simp_tac(srw_ss())[RES_FORALL] >>
     srw_tac[][] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     qpat_x_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
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
                     SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bvl,
                                            db_merge_bvl]))  >>
         srw_tac[][]
         >> irule tenv_val_exp_ok_bvl
         >> simp []
         >> drule (CONJUNCT1 type_p_freevars)
         >> rw []))
 >- (full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
     srw_tac[][] >>
     metis_tac [check_freevars_lem, EVERY_MEM])
 >- metis_tac [type_subst_deBruijn_subst_list, tenv_ctor_ok_lookup]
 >- metis_tac [type_subst_deBruijn_subst_list, tenv_ctor_ok_lookup]
 >- (
   qpat_x_assum `lookup_var _ _ _ = _` mp_tac
   >> simp [Once lookup_var_def]
   >> CASE_TAC
   >> rw [lookup_var_def]
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)`
       >> rw []
       >- (
         irule (CONJUNCT1 deBruijn_subst2)
         >> drule nsLookup_nsAll
         >> disch_then drule
         >> simp [])
       >- (
         fs [EVERY_MAP, EVERY_MEM]
         >> rw []
         >> simp_tac std_ss [Once arithmeticTheory.ADD_COMM]
         >> irule (SIMP_RULE (srw_ss()) [] type_e_subst_lem3)
         >> rw [EVERY_MEM]))
     >- (
       Cases_on `n`
       >> fs [lookup_varE_def]
       >> rename1 `tveLookup n2 0 _`
       >> `tveLookup n2 0 (db_merge (deBruijn_subst_tenvE targs' tenvE1)
                               (bind_tvar tvs' tenvE2)) = NONE`
         suffices_by rw []
       >> fs [tveLookup_inc_none, tveLookup_subst_none,
              tveLookup_db_merge_none]))
   >- (
     Cases_on `n`
     >> fs [lookup_varE_def, lookup_var_def]
     >> CASE_TAC
     >> rw []
     >> rename1 `tveLookup n2 0 _`
     >- (
       `tveLookup n2 0 (db_merge tenvE1 (bind_tvar (LENGTH targs') tenvE2)) = NONE`
         suffices_by fs []
       >> fs [tveLookup_db_merge_none, tveLookup_subst_none, tveLookup_inc_none])
     >> rename1 `tveLookup n _ (db_merge (deBruijn_subst_tenvE _ _) _) = SOME r`
     >> `?tvs t'. r = (tvs,t')` by metis_tac [pair_CASES]
     >> fs []
     >> rw [type_e_subst_lem7]
     >> qexists_tac `(MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs)`
     >> rw []
     >- (
       fs [tveLookup_db_merge_some]
       >> imp_res_tac tveLookup_subst_some
       >> fs [tveLookup_db_merge_none, tveLookup_subst_none, tveLookup_inc_none]
       >- metis_tac [NOT_SOME_NONE, tveLookup_subst_none]
       >> rpt (irule (METIS_PROVE [] ``x = y ⇒ f x = f y``))
       >> pop_assum kall_tac
       >> pop_assum kall_tac
       >> imp_res_tac tveLookup_inc_some
       >> pop_assum kall_tac
       >> first_x_assum (qspec_then `LENGTH targs' + num_tvs tenvE1` strip_assume_tac)
       >> rw []
       >> fs []
       >> rw []
       >> drule tenv_val_exp_ok_db_merge
       >> rw []
       >> drule tveLookup_no_tvs
       >> rw []
       >> fs []
       >> drule tveLookup_freevars
       >> disch_then drule
       >> rw []
       >> irule nil_deBruijn_subst
       >> fs []
       >> `!x y. x + y ≥ x:num` by decide_tac
       >> metis_tac [check_freevars_add])
     >- (
       fs [EVERY_MAP, EVERY_MEM]
       >> rw []
       >> simp_tac std_ss [Once arithmeticTheory.ADD_COMM]
       >> irule (SIMP_RULE (srw_ss()) [] type_e_subst_lem3)
       >> rw [EVERY_MEM])
     >- (
       fs [tveLookup_db_merge_some]
       >> imp_res_tac tveLookup_subst_some
       >> fs [tveLookup_db_merge_none, tveLookup_subst_none, tveLookup_inc_none]
       >- metis_tac [NOT_SOME_NONE, tveLookup_subst_none]
       >> imp_res_tac tveLookup_inc_some
       >> pop_assum kall_tac
       >> first_x_assum (qspec_then `LENGTH targs' + num_tvs tenvE1` strip_assume_tac)
       >> rw []
       >> fs [])))
 >- (qpat_x_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'`
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     full_simp_tac(srw_ss())[num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     metis_tac [type_e_subst_lem3])
 >- (qpat_x_assum `!tenvE1' targs' tvs'. P tenvE1' targs' tvs'`
           (ASSUME_TAC o Q.SPEC `Bind_name n 0 t1 tenvE1`) >>
     full_simp_tac(srw_ss())[num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def] >>
     pop_assum irule
     >> srw_tac [] [tenv_val_exp_ok_def])
 >- (
   rw [GSYM PULL_EXISTS, CONJ_ASSOC]
   >- (
     full_simp_tac(srw_ss())[type_op_cases] >>
     srw_tac[][] >>
     TRY(cases_on`wz`\\CHANGED_TAC(fs[Tword_def,Tword8_def,Tword64_def])) >>
     full_simp_tac(srw_ss())[deBruijn_subst_def,Tchar_def,Tword_def,Tword8_def,Tword64_def] >>
     metis_tac [])
   >- metis_tac [SIMP_RULE (srw_ss()) [PULL_FORALL] type_e_subst_lem3, ADD_COMM])
 >- (full_simp_tac(srw_ss())[RES_FORALL] >>
     qexists_tac `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t` >>
     srw_tac[][] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     qpat_x_assum `!x. MEM x pes ⇒ P x` (MP_TAC o Q.SPEC `(x0,x1)`) >>
     srw_tac[][] >>
     qexists_tac `MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t))
                      bindings` >>
     srw_tac[][] >- (
       REWRITE_TAC [GSYM type_p_tenvV_indep] >>
       metis_tac [type_p_subst]) >>
     pop_assum (MATCH_MP_TAC o
                SIMP_RULE (srw_ss()) [num_tvs_bind_var_list, deBruijn_subst_E_bvl,
                                      db_merge_bvl] o
                Q.SPECL [`bind_var_list 0 bindings tenvE1`, `targs`, `tvs`])
     >> rw []
     >> irule tenv_val_exp_ok_bvl
     >> simp []
     >> drule (CONJUNCT1 type_p_freevars)
     >> rw [])
     (* COMPLETENESS
 >- (disj1_tac >>
     srw_tac[][] >>
     qexists_tac `deBruijn_subst (tvs + num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs) t` >>
     qexists_tac `tvs` >>
     srw_tac[][] >|
     [qpat_x_assum `∀tenvE1' targs' tvs''.
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
          srw_tac[][] >>
          full_simp_tac(srw_ss())[MAP_MAP_o, combinTheory.o_DEF, deBruijn_inc_deBruijn_inc] >>
          metis_tac [],
      every_case_tac >>
          full_simp_tac(srw_ss())[tenv_ok_def] >>
          FIRST_X_ASSUM
                 (MP_TAC o
                  Q.SPECL [`Bind_name x tvs t tenvE1`, `targs`, `tvs'`]) >>
          srw_tac[][db_merge_def, deBruijn_subst_tenvE_def,
              num_tvs_def] >>
          imp_res_tac type_e_freevars >>
          full_simp_tac(srw_ss())[tenv_ok_def, num_tvs_def, num_tvs_db_merge]])
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
     srw_tac[][db_merge_def, deBruijn_subst_tenvE_def, num_tvs_def] >>
     imp_res_tac type_e_freevars >>
     full_simp_tac(srw_ss())[tenv_val_ok_def, num_tvs_def, num_tvs_db_merge] >>
     first_x_assum match_mp_tac >>
     srw_tac[][] >>
     rev_full_simp_tac(srw_ss())[tenv_val_ok_def, num_tvs_def, num_tvs_db_merge]
     >> srw_tac [] [tenv_val_exp_ok_def])
     (* COMPLETENESS
 >- (qexists_tac `MAP (λ(x,t').
                 (x,
                  deBruijn_subst (tvs + num_tvs tenvE1)
                    (MAP (deBruijn_inc 0 (tvs + num_tvs tenvE1)) targs)
                    t')) env` >>
     qexists_tac `tvs` >>
     srw_tac[][] >|
     [qpat_x_assum `∀tenvE1' targs' tvs''.
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
          srw_tac[][db_merge_bvl, num_tvs_bind_var_list,
              deBruijn_subst_E_bvl] >>
          pop_assum match_mp_tac >>
          match_mp_tac tenv_val_exp_ok_bvl >>
          srw_tac[][] >>
          metis_tac [],
      qpat_x_assum `∀tenvE1' targs' tvs''.
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
          srw_tac[][num_tvs_bind_var_list, deBruijn_subst_E_bvl,
          db_merge_bvl] >>
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
        srw_tac[][db_merge_bvl, num_tvs_bind_var_list,
            deBruijn_subst_E_bvl] >>
        pop_assum match_mp_tac >>
        metis_tac [tenv_val_exp_ok_bvl_funs])
    >- (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`bind_var_list 0 env tenvE1`, `targs`, `tvs`]) >>
        srw_tac[][num_tvs_bind_var_list, deBruijn_subst_E_bvl,
        db_merge_bvl] >>
        pop_assum match_mp_tac >>
        metis_tac [tenv_val_exp_ok_bvl_funs]))
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
     srw_tac[][deBruijn_subst_tenvE_def, db_merge_def, num_tvs_def]
     >> pop_assum irule
     >> srw_tac [] [tenv_val_exp_ok_def])
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
  `∀tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings n = SOME t
    ⇒
    ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)`,
 induct_on `funs`
 >> rw []
 >> qpat_x_assum `type_funs _ _ _ _` mp_tac
 >> simp [Once type_e_cases]
 >> rw []
 >> fs []
 >> every_case_tac
 >> fs [deBruijn_subst_def, check_freevars_def]
 >>metis_tac [type_e_freevars, num_tvs_def]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.store_thm ("type_funs_lookup",
`∀fn tenvE funs bindings n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃t. ALOOKUP bindings fn = SOME t)`,
Induct_on `funs` >>
srw_tac[][] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
full_simp_tac(srw_ss())[] >>
full_simp_tac(srw_ss())[] >>
srw_tac[][] >>
metis_tac []);

(* Functions in the type environment can be found *)
val type_funs_find_recfun = Q.store_thm ("type_funs_find_recfun",
`∀fn env funs bindings e tenv tenvE t.
  ALOOKUP bindings fn = SOME t ∧
  type_funs tenv tenvE funs bindings
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
  `∀fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) ∧
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings fn = SOME (Tfn t1 t2)
    ⇒
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2)`,
 induct_on `funs`
 >> rw [Once find_recfun_def]
 >> qpat_x_assum `type_funs _ _ _ _` mp_tac
 >> simp [Once type_e_cases]
 >> rw []
 >> fs []
 >> every_case_tac
 >> fs []
 >> rw []
 >> metis_tac []);

(* No duplicate function definitions in a single let rec *)
val type_funs_distinct = Q.store_thm ("type_funs_distinct",
`∀tenv tenvE funs bindings .
  type_funs tenv tenvE funs bindings
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

val type_funs_tenv_exp_ok = Q.store_thm ("type_funs_tenv_exp_ok",
  `!funs env tenv tenvE tvs bindings.
    num_tvs tenvE = 0 ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs env
    ⇒
    tenv_val_exp_ok (bind_var_list tvs env Empty)`,
 induct_on `funs`
 >> rw []
 >> pop_assum mp_tac
 >> simp [Once type_e_cases]
 >> rw [bind_var_list_def, tenv_val_exp_ok_def]
 >> rw [bind_var_list_def, tenv_val_exp_ok_def]
 >> first_x_assum irule
 >> metis_tac []);

val type_e_subst_lem = Q.prove (
`∀tenv tenvE e t targs tvs targs'.
  type_e tenv (Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t ∧
  num_tvs tenvE = 0 ∧
  tenv_abbrev_ok tenv.t ∧
  tenv_ctor_ok tenv.c ∧
  tenv_val_ok tenv.v ∧
  tenv_val_exp_ok (bind_tvar (LENGTH targs) tenvE) ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t1
  ⇒
  type_e tenv (Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e (deBruijn_subst 0 targs t)`,
 srw_tac[][] >>
 drule (GEN_ALL (CONJUNCT1 type_e_subst))
 >> simp [tenv_val_exp_ok_def]
 >> rpt (disch_then drule)
 >> disch_then (qspec_then `Bind_name x 0 t1 Empty` mp_tac)
 >> simp [db_merge_def, deBruijn_subst_tenvE_def, deBruijn_inc0]);

(* ---------- tid_exn_to_tc ---------- *)

val tid_exn_to_tc_11 = Q.store_thm ("tid_exn_to_tc_11",
`!x y. (tid_exn_to_tc x = tid_exn_to_tc y) = same_tid x y`,
cases_on `x` >>
cases_on `y` >>
srw_tac[][tid_exn_to_tc_def, same_tid_def]);

val tid_exn_not = Q.store_thm ("tid_exn_not",
`(!tn. tid_exn_to_tc tn ≠ TC_int) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_char) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_string) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_ref) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_tup) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_fn) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word8) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word64) ∧
 (!tn wz. tid_exn_to_tc tn ≠ TC_word wz) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_word8array) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_vector) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_array)`,
 srw_tac[][] >>
 cases_on `tn` >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 Cases_on`wz` \\ EVAL_TAC >>
 metis_tac []);

(* ---------- ctMap stuff ---------- *)

val ctMap_ok_merge_imp = Q.store_thm ("ctMap_ok_merge_imp",
`!tenvC1 tenvC2.
  ctMap_ok tenvC1 ∧ ctMap_ok tenvC2 ⇒
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

val ctMap_ok_type_decs = Q.store_thm ("ctMap_ok_type_decs",
 `!mn tds. tenv_abbrev_ok tenvT ∧ check_ctor_tenv tenvT tds ⇒ ctMap_ok (type_decs_to_ctMap mn tenvT tds)`,
 rw [check_ctor_tenv_def, ctMap_ok_def, type_decs_to_ctMap_def, FEVERY_ALL_FLOOKUP, FUPDATE_LIST_alist_to_fmap]
 >> drule ALOOKUP_MEM
 >> simp [MEM_FLAT, MEM_MAP]
 >> pairarg_tac
 >> simp []
 >> pairarg_tac
 >> simp []
 >> rw []
 >> pairarg_tac
 >> fs [MEM_MAP]
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [EVERY_MEM]
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [MEM_MAP]
 >> metis_tac [check_freevars_type_name_subst]);

val consistent_ctMap_union = Q.store_thm ("consistent_ctMap_union",
 `!tdecs1 tdecs2 ctMap1 ctMap2.
  consistent_ctMap tdecs1 ctMap1 ∧
  consistent_ctMap tdecs2 ctMap2
  ⇒
  consistent_ctMap (union_decls tdecs1 tdecs2) (FUNION ctMap1 ctMap2)`,
 rw [consistent_ctMap_def, RES_FORALL]
 >> pairarg_tac
 >> fs []
 >> CASE_TAC
 >> fs [union_decls_def]
 >> first_x_assum drule
 >> simp []);

val consistent_ctMap_union2 = Q.store_thm ("consistent_ctMap_union2",
 `!tdecs1 tdecs2 ctMap.
  consistent_ctMap tdecs2 ctMap
  ⇒
  consistent_ctMap (union_decls tdecs1 tdecs2) ctMap`,
 rw [consistent_ctMap_def, RES_FORALL]
 >> pairarg_tac
 >> fs []
 >> CASE_TAC
 >> fs [union_decls_def]
 >> first_x_assum drule
 >> simp []);

val consistent_ctMap_disjoint = Q.store_thm ("consistent_ctMap_disjoint",
`!mn (tds:type_def) (ctMap:ctMap) tdecs tabbrev.
  DISJOINT (set (MAP (λ(tvs,tn,ctors). mk_id mn tn) tds)) tdecs.defined_types ∧
  consistent_ctMap tdecs ctMap
  ⇒
  DISJOINT (IMAGE SND (FDOM (type_decs_to_ctMap mn tabbrev tds))) (IMAGE SND (FDOM ctMap))` ,
 rw [consistent_ctMap_def,
     type_decs_to_ctMap_def, RES_FORALL, FUPDATE_LIST_alist_to_fmap, DISJOINT_DEF,
     EXTENSION, MEM_MAP]
 >> rw [METIS_PROVE [] ``y ∨ x ⇔ ~y ⇒ x``]
 >> fs [MEM_FLAT, MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs [MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs []
 >> CCONTR_TAC
 >> fs []
 >> first_x_assum drule
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [METIS_PROVE [] ``y ∨ x ⇔ ~y ⇒ x``, PULL_EXISTS]
 >> first_x_assum drule
 >> simp []);

val still_has_exns = Q.store_thm ("still_has_exns",
`!ctMap1 ctMap2.
  (DISJOINT (FDOM ctMap1) (FDOM ctMap2) ∨ DISJOINT (FDOM ctMap2) (FDOM ctMap1)) ∧
  ctMap_has_exns ctMap1
  ⇒
  ctMap_has_exns (FUNION ctMap2 ctMap1)`,
 srw_tac[][FLOOKUP_FUNION, ctMap_has_exns_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
 metis_tac []);

val still_has_lists = Q.store_thm ("still_has_lists",
`!ctMap1 ctMap2.
  (DISJOINT (IMAGE SND (FDOM ctMap1)) (IMAGE SND (FDOM ctMap2)) ∨
   DISJOINT (IMAGE SND (FDOM ctMap2)) (IMAGE SND (FDOM ctMap1))) ∧
  ctMap_has_lists ctMap1
  ⇒
  ctMap_has_lists (FUNION ctMap2 ctMap1)`,
 srw_tac[][FLOOKUP_FUNION, ctMap_has_lists_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
 metis_tac [SND]);

val still_has_bools = Q.store_thm ("still_has_bools",
`!ctMap1 ctMap2.
  (DISJOINT (IMAGE SND (FDOM ctMap1)) (IMAGE SND (FDOM ctMap2)) ∨
   DISJOINT (IMAGE SND (FDOM ctMap2)) (IMAGE SND (FDOM ctMap1))) ∧
  ctMap_has_bools ctMap1
  ⇒
  ctMap_has_bools (FUNION ctMap2 ctMap1)`,
 srw_tac[][FLOOKUP_FUNION, ctMap_has_bools_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
 metis_tac [SND]);

val all_distinct_map_fst_lemma = Q.prove (
`!l v. ALL_DISTINCT (MAP (\(x,y). x) l) ⇒ ALL_DISTINCT (MAP (\(x,y). (x, v)) l)`,
 Induct_on `l`
 >> rw [MEM_MAP]
 >> pairarg_tac
 >> rw []
 >> pairarg_tac
 >> rw []
 >> fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD]
 >> metis_tac []);

val check_ctor_tenv_type_decs_to_ctMap_lemma = Q.prove (
  `!tenvT tds mn tvs tn c cn ts.
    check_ctor_tenv tenvT (REVERSE tds) ∧
    MEM (tvs,tn,c) (REVERSE tds) ∧
    MEM (cn,ts) c
    ⇒
    FLOOKUP (type_decs_to_ctMap mn tenvT (REVERSE tds)) (cn, TypeId (mk_id mn tn)) = SOME (tvs, MAP (type_name_subst tenvT) ts)`,
 Induct_on `tds`
 >> rw [check_ctor_tenv_def]
 >> fs [MEM_MAP]
 >- (
   simp [type_decs_to_ctMap_def, flookup_fupdate_list, REVERSE_APPEND, ALOOKUP_APPEND]
   >> `ALL_DISTINCT (MAP FST (MAP (λ(cn,ts). ((cn,TypeId (mk_id mn tn)),tvs, MAP (type_name_subst tenvT) ts)) c))`
     by (
       rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
       >> fs [check_dup_ctors_thm, ALL_DISTINCT_APPEND]
       >> metis_tac [all_distinct_map_fst_lemma])
   >> simp [alookup_distinct_reverse]
   >> `ALOOKUP (MAP (λ(cn,ts).  ((cn,TypeId (mk_id mn tn)),tvs, MAP (type_name_subst tenvT) ts)) c)
               (cn,TypeId (mk_id mn tn)) = SOME (tvs,MAP (type_name_subst tenvT) ts)`
     suffices_by rw []
   >> irule ALOOKUP_ALL_DISTINCT_MEM
   >> simp [MEM_MAP]
   >> qexists_tac `(cn,ts)`
   >> simp [])
 >- (
   fs [check_ctor_tenv_def, GSYM CONJ_ASSOC, ALL_DISTINCT_APPEND]
   >> `check_dup_ctors (REVERSE tds)` by fs [check_dup_ctors_thm, ALL_DISTINCT_APPEND]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [type_decs_to_ctMap_def, flookup_fupdate_list, ALOOKUP_APPEND, REVERSE_APPEND]
   >> pairarg_tac
   >> rw []
   >> fs []
   >> `ALOOKUP (REVERSE (MAP (λ(cn,ts). ((cn,TypeId (mk_id mn tn')),tvs', MAP (type_name_subst tenvT) ts)) ctors))
               (cn,TypeId (mk_id mn tn)) = NONE`
     suffices_by rw []
   >> fs [MEM_MAP]
   >> first_x_assum (qspec_then `(tvs,tn,c)` mp_tac)
   >> rw [ALOOKUP_NONE, MEM_MAP]
   >> rw [METIS_PROVE [] ``x ∨ y ⇔ ~x ⇒ y``]
   >> pairarg_tac
   >> fs []));

val check_ctor_tenv_type_decs_to_ctMap = Q.store_thm ("check_ctor_tenv_type_decs_to_ctMap",
  `!tenvT tds mn tvs tn c cn ts.
    check_ctor_tenv tenvT tds ∧
    MEM (tvs,tn,c) tds ∧
    MEM (cn,ts) c
    ⇒
    FLOOKUP (type_decs_to_ctMap mn tenvT tds) (cn, TypeId (mk_id mn tn)) = SOME (tvs, MAP (type_name_subst tenvT) ts)`,
 metis_tac [REVERSE_REVERSE, check_ctor_tenv_type_decs_to_ctMap_lemma]);

(* ---------- consistent_decls ---------- *)

val consistent_decls_union = Q.store_thm ("consistent_decls_union",
 `!defined_types1 defined_types2 tdecs1 tdecs2.
  consistent_decls defined_types1 tdecs1 ∧
  consistent_decls defined_types2 tdecs2
  ⇒
  consistent_decls (defined_types1 ∪ defined_types2) (union_decls tdecs1 tdecs2)`,
 rw [consistent_decls_def, union_decls_def, RES_FORALL]
 >> CASE_TAC
 >> fs []
 >> first_x_assum drule
 >> rw []
 >> metis_tac []);

val consistent_decls_union2 = Q.store_thm ("consistent_decls_union2",
 `!defined_types tdecs1 tdecs2.
  consistent_decls defined_types tdecs2
  ⇒
  consistent_decls defined_types (union_decls tdecs1 tdecs2)`,
 rw [consistent_decls_def, union_decls_def, RES_FORALL]
 >> CASE_TAC
 >> fs []
 >> first_x_assum drule
 >> rw []
 >> metis_tac []);

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

(* ---------- type_v  ---------- *)

val nsLookup_add_tenvE1 = Q.store_thm ("nsLookup_add_tenvE1",
  `!tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t ∧
    tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  Induct_on `tenvE`
  >> rw [tveLookup_def, add_tenvE_def]
  >> fs []
  >> metis_tac [nil_deBruijn_inc]);

val nsLookup_add_tenvE2 = Q.store_thm ("nsLookup_add_tenvE2",
  `!tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE ∧
    nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  Induct_on `tenvE`
  >> rw [tveLookup_def, add_tenvE_def]
  >> fs []
  >> metis_tac []);

val nsLookup_add_tenvE3 = Q.store_thm ("nsLookup_add_tenvE3",
  `!tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t)`,
  Induct_on `tenvE`
  >> rw [tveLookup_def, add_tenvE_def]
  >> fs []
  >> metis_tac []);

val tenv_val_ok_add_tenvE = Q.store_thm ("tenv_val_ok_add_tenvE",
  `!tenvE tenvV.
    num_tvs tenvE = 0 ∧
    tenv_val_exp_ok tenvE ∧
    tenv_val_ok tenvV
    ⇒
    tenv_val_ok (add_tenvE tenvE tenvV)`,
 Induct_on `tenvE`
 >> rw [add_tenvE_def, tenv_val_exp_ok_def]
 >> fs [tenv_val_ok_def]
 >> irule nsAll_nsBind
 >> rw []
 >> rfs []);

val add_tenvE_nsAppend = Q.store_thm ("add_tenvE_nsAppend",
  `!tenvE tenvV. nsAppend (add_tenvE tenvE nsEmpty) tenvV = add_tenvE tenvE tenvV`,
 Induct_on `tenvE`
 >> rw [add_tenvE_def]);

val add_tenvE_bvl = Q.store_thm ("add_tenvE_bvl",
  `!n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV)`,
 Induct_on `bindings`
 >> rw [bind_var_list_def, nsBindList_def]
 >> pairarg_tac
 >> rw []
 >> pairarg_tac
 >> fs []
 >> rw [bind_var_list_def, add_tenvE_def, nsBindList_def]);

val type_v_freevars = Q.store_thm ("type_v_freevars",
`!tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t`,
 ho_match_mp_tac type_v_strongind >>
 srw_tac[][check_freevars_def, tenv_val_ok_def, num_tvs_def, bind_tvar_def, Tchar_def]
 >- rw[Tword_def,check_freevars_def]
 >- rw[Tword64_def,Tword_def,check_freevars_def]
 >- metis_tac [] >>
 res_tac
 >- (
   fs [EVERY2_EVERY, EVERY_MEM]
   >> rfs [MEM_ZIP]
   >> rw [MEM_EL]
   >> first_x_assum (qspec_then `(EL n vs, EL n ts)` mp_tac)
   >> simp [PULL_EXISTS])
 >- (
   fs [tenv_ok_def] >>
   imp_res_tac type_e_freevars >>
   full_simp_tac(srw_ss())[tenv_val_exp_ok_def]  >>
   rev_full_simp_tac(srw_ss())[num_tvs_def])
 >- (
   fs [tenv_ok_def] >>
   imp_res_tac type_e_freevars >>
   full_simp_tac(srw_ss())[tenv_val_exp_ok_def]  >>
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

val remove_lambda_prod = Q.prove (
`(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

val type_subst_lem1 =
(GEN_ALL o
 SIMP_RULE (srw_ss()++ARITH_ss) [] o
 Q.SPECL [`[]`, `t`, `0`, `targs`, `tvs`] o
 SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM])
check_freevars_subst;

val type_subst = Q.store_thm ("type_subst",
  `!tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t ⇒
     tvs = LENGTH targs ∧
     ctMap_ok ctMap ∧
     EVERY (check_freevars tvs' []) targs ∧
     check_freevars (LENGTH targs) [] t
     ⇒
     type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)`,
 ho_match_mp_tac type_v_strongind
 >> rw []
 >> simp [Once type_v_cases, deBruijn_inc_def, deBruijn_subst_def, Tchar_def,
          Tword_def, Tword64_def]
 >> fs [check_freevars_def]
 >- (
   conj_tac
   >- (
     simp [EVERY_MAP]
     >> fs [EVERY_MEM]
     >> rw []
     >> metis_tac [type_subst_lem1, EVERY_MEM])
   >> fs [EVERY2_EVERY, EVERY_MAP]
   >> simp [GSYM FUNION_alist_to_fmap]
   >> rename1 `FLOOKUP ctMap (cn,tn) = SOME (tvs,ts)`
   >> `EVERY (check_freevars 0 tvs) ts` by metis_tac [ctMap_ok_lookup, EVERY_MEM]
   >> `EVERY (check_freevars (LENGTH targs) tvs) ts`
     by (`LENGTH targs ≥ 0` by decide_tac >> metis_tac [EVERY_MEM, check_freevars_add])
   >> simp [GSYM type_subst_deBruijn_subst_list]
   >> simp [GSYM type_subst_deBruijn_inc_list]
   >> rfs [ZIP_MAP, EVERY_MAP, GSYM FUNION_alist_to_fmap]
   >> fs [EVERY_MEM]
   >> rw []
   >> last_x_assum drule
   >> rw []
   >> pop_assum irule
   >> irule check_freevars_subst_single
   >> simp [EVERY_MEM]
   >> first_x_assum irule
   >> rfs [MEM_ZIP, EL_MEM])
 >- (
   fs [EVERY2_EVERY, EVERY_MAP]
   >> simp [ZIP_MAP, EVERY_MAP]
   >> fs [EVERY_MEM]
   >> rw []
   >> last_x_assum drule
   >> pairarg_tac
   >> rw []
   >> pop_assum irule
   >> simp []
   >> rfs [MEM_ZIP, EL_MEM])
 >- (
   qexists_tac `tenv`
   >> qexists_tac `tenvE`
   >> simp [nil_deBruijn_inc, deBruijn_subst_freevars]
   >> rw []
   >- fs [nsAll2_conj, remove_lambda_prod]
   >> match_mp_tac type_e_subst_lem
   >> fs [tenv_val_exp_ok_def, tenv_ok_def])
 >- (qexists_tac `tenv` >>
     qexists_tac `tenvE` >>
     simp [nil_deBruijn_inc , deBruijn_subst_freevars] >>
     qexists_tac `MAP (λ(x,t). (x,deBruijn_subst 0 targs t)) bindings` >>
     srw_tac[][]
     >- fs [nsAll2_conj, remove_lambda_prod]
     >- (first_assum (assume_tac o MATCH_MP (GEN_ALL (hd (tl (tl (CONJUNCTS type_e_subst)))))) >>
         pop_assum (qspecl_then [`tenvE`, `bind_var_list 0 bindings Empty`] mp_tac) >>
         simp [num_tvs_def, deBruijn_subst_tenvE_def, db_merge_def, deBruijn_inc0,
               num_tvs_bind_var_list, db_merge_bvl,
               deBruijn_subst_E_bvl] >>
         disch_then match_mp_tac >>
         srw_tac[][] >>
         fs [tenv_ok_def]
         >> irule tenv_val_exp_ok_bvl_funs
         >> simp [tenv_val_exp_ok_def]
         >> metis_tac [])
     >- (qpat_x_assum `type_funs _ _ _ _` (fn x => ALL_TAC) >>
         induct_on `bindings` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         PairCases_on `h` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         metis_tac []))
 >- simp [nil_deBruijn_subst, nil_deBruijn_inc]
 >- simp [nil_deBruijn_subst, nil_deBruijn_inc]
 >- (
   fs [EVERY_MEM]
   >> simp [nil_deBruijn_subst, nil_deBruijn_inc]));

val check_ctor_tenv_ok = Q.store_thm ("check_ctor_tenv_ok",
`!mn c tenvT.
 check_ctor_tenv tenvT c ∧
 tenv_abbrev_ok tenvT
 ⇒
 tenv_ctor_ok (build_ctor_tenv mn tenvT c)`,
 rw [build_ctor_tenv_def, tenv_ctor_ok_def]
 >> irule nsAll_alist_to_ns
 >> simp [EVERY_REVERSE]
 >> fs [check_ctor_tenv_def, EVERY_MEM, MEM_FLAT, MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs []
 >> pairarg_tac
 >> fs []
 >> pairarg_tac
 >> fs [MEM_MAP]
 >> rw []
 >> pairarg_tac
 >> fs []
 >> rw []
 >> fs [MEM_MAP]
 >> rw []
 >> first_x_assum drule
 >> rw []
 >> first_x_assum drule
 >> rw []
 >> irule check_freevars_type_name_subst
 >> simp []);

(* --------- decls_ok ------------ *)

val decls_ok_union = Q.store_thm ("decls_ok_union",
 `∀d1 d2.
  decls_ok d1 ∧
  decls_ok d2
  ⇒
  decls_ok (union_decls d1 d2)`,
 rw [decls_ok_def, union_decls_def, SUBSET_DEF, decls_to_mods_def, GSPECIFICATION]
 >> full_simp_tac (srw_ss()++DNF_ss) []
 >> metis_tac []);

(* ---------- type_d ---------- *)

val type_d_check_uniq = Q.store_thm ("type_d_check_uniq",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_d uniq tvs tdecs tenv d tdecs' new_tenv
  ⇒
  type_d F tvs tdecs tenv d tdecs' new_tenv`,
 srw_tac[][type_d_cases] >>
 metis_tac []);

val type_d_tenv_ok_helper = Q.store_thm ("type_d_tenv_ok_helper",
 `∀u mn tdecs tenv d tdecs' tenv'.
   type_d u mn tdecs tenv d tdecs' tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok tenv'`,
 rw [type_d_cases]
 >> fs [tenv_ok_def, type_d_cases, tenv_ctor_ok_def, tenv_abbrev_ok_def]
 >> rw []
 >- (
   drule (CONJUNCT1 type_p_freevars)
   >> rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> fs [EVERY_MEM]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> pairarg_tac
   >> fs [tenv_add_tvs_def, MEM_MAP]
   >> pairarg_tac
   >> fs []
   >> rw []
   >> metis_tac [SND])
 >- (
   drule (CONJUNCT1 type_p_freevars)
   >> rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> fs [EVERY_MEM]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> pairarg_tac
   >> fs [tenv_add_tvs_def, MEM_MAP]
   >> pairarg_tac
   >> fs []
   >> rw []
   >> metis_tac [SND])
 >- (
   rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> simp [tenv_add_tvs_def, EVERY_MAP]
   >> drule (List.nth (CONJUNCTS type_e_freevars, 2))
   >> simp [tenv_val_exp_ok_def, EVERY_MAP, LAMBDA_PROD]
   >> disch_then irule
   >> irule tenv_val_exp_ok_bvl_funs
   >> simp [tenv_val_exp_ok_def]
   >> metis_tac [])
 >- (
   irule (SIMP_RULE (srw_ss()) [tenv_ctor_ok_def] check_ctor_tenv_ok)
   >> rw []
   >> simp [tenv_abbrev_ok_def]
   >> irule nsAll_nsAppend
   >> simp []
   >> irule nsAll_alist_to_ns
   >> simp [EVERY_MAP, EVERY_MEM]
   >> rw []
   >> rpt (pairarg_tac >> fs [])
   >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (
   irule nsAll_alist_to_ns
   >> simp [EVERY_MAP, EVERY_MEM]
   >> rw []
   >> rpt (pairarg_tac >> fs [])
   >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
 >- (
   irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def])
 >- (
   fs [EVERY_MAP, EVERY_MEM, check_exn_tenv_def]
   >> rw []
   >> irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def]));

val extend_dec_tenv_ok = Q.store_thm ("extend_dec_tenv_ok",
  `!tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv')`,
 rw [extend_dec_tenv_def, tenv_ok_def]
 >- (
   fs [tenv_val_ok_def]
   >> irule nsAll_nsAppend
   >> simp [])
 >> fs [tenv_abbrev_ok_def]
 >> irule nsAll_nsAppend
 >> simp []);

val type_d_tenv_ok = Q.store_thm ("type_d_tenv_ok",
 `∀u mn tdecs tenv d tdecs' tenv'.
   type_d u mn tdecs tenv d tdecs' tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok (extend_dec_tenv tenv' tenv)`,
 metis_tac [extend_dec_tenv_ok, type_d_tenv_ok_helper]);

val type_d_mod = Q.store_thm ("type_d_mod",
`!uniq mn tdecs tenv d tdecs' new_tenv.
  type_d uniq mn tdecs tenv d tdecs' new_tenv
  ⇒
  tdecs'.defined_mods = {} ∧
  decls_to_mods tdecs' ⊆ { mn }`,
 srw_tac[][type_d_cases, decls_to_mods_def, SUBSET_DEF, FDOM_FUPDATE_LIST] >>
 full_simp_tac(srw_ss())[build_ctor_tenv_def, MEM_FLAT, MEM_MAP] >>
 srw_tac[][empty_decls_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[EXISTS_PROD, empty_decls_def, decls_to_mods_def, mk_id_def, MEM_MAP] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[GSPECIFICATION] >>
 TRY (PairCases_on `y`) >>
 full_simp_tac(srw_ss())[]);

(* ---------- type_ds ---------- *)

val type_ds_empty = Q.store_thm ("type_ds_empty[simp]",
 `!u mn decls tenv decls' r.
  type_ds u mn decls tenv [] decls' r ⇔
  decls' = empty_decls ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |>`,
 rw [Once type_ds_cases]);

val type_ds_sing = Q.store_thm ("type_ds_sing[simp]",
 `!u mn decls tenv d decls' r.
  type_ds u mn decls tenv [d] decls' r ⇔ type_d u mn decls tenv d decls' r`,
 simp [Once type_ds_cases]
 >> rw [extend_dec_tenv_def, type_env_component_equality]
 >> eq_tac
 >> rw []
 >> metis_tac [type_env_component_equality]);

val type_ds_check_uniq = Q.store_thm ("type_ds_check_uniq",
`!uniq tvs tdecs tenv d tdecs' new_tenv.
  type_ds uniq tvs tdecs tenv d tdecs' new_tenv
  ⇒
  type_ds F tvs tdecs tenv d tdecs' new_tenv`,
 ho_match_mp_tac type_ds_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_ds_cases] >>
 metis_tac [type_d_check_uniq]);

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

val type_ds_tenv_ok_helper = Q.store_thm ("type_ds_tenv_ok_helper",
 `∀u mn tdecs tenv ds tdecs' tenv'.
   type_ds u mn tdecs tenv ds tdecs' tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv'`,
 ho_match_mp_tac type_ds_ind
 >> rw []
 >> drule type_d_tenv_ok_helper
 >> rw []
 >> drule type_d_tenv_ok
 >> rw []
 >> fs []
 >> metis_tac [extend_dec_tenv_ok]);

val type_ds_no_dup_types_helper = Q.prove (
`!uniq mn decls tenv ds decls' tenv'.
  type_ds uniq mn decls tenv ds decls' tenv'
  ⇒
  DISJOINT decls.defined_types decls'.defined_types ∧
  decls'.defined_types =
  set (FLAT (MAP (λd.
                case d of
                  Dlet _ v6 v7 => []
                | Dletrec _ v8 => []
                | Dtabbrev _ x y z => []
                | Dtype _ tds => MAP (λ(tvs,tn,ctors). mk_id mn tn) tds
                | Dexn _ v10 v11 => []) ds))`,
 induct_on `ds` >>
 srw_tac[][empty_decls_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_ds_cases,EXISTS_PROD]) >>
 full_simp_tac(srw_ss())[empty_decls_def,EXISTS_PROD,extend_dec_tenv_def] >>
 TRY(PairCases_on`decls''''`)>>
 TRY(PairCases_on`decls'''`)>>
 srw_tac[][] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_d_cases] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[empty_decls_def, union_decls_def] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
 metis_tac []);

val type_ds_no_dup_types = Q.store_thm ("type_ds_no_dup_types",
`!uniq mn decls tenv ds decls' tenv'.
  type_ds uniq mn decls tenv ds decls' tenv'
  ⇒
  no_dup_types ds`,
 induct_on `ds` >>
 srw_tac[][no_dup_types_def, decs_to_types_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
 full_simp_tac(srw_ss())[EXISTS_PROD,extend_dec_tenv_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[no_dup_types_def, type_d_cases, decs_to_types_def] >>
 srw_tac[][ALL_DISTINCT_APPEND]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- full_simp_tac(srw_ss())[check_ctor_tenv_def, LAMBDA_PROD]
 >- metis_tac []
 >- (full_simp_tac(srw_ss())[union_decls_def] >>
     imp_res_tac type_ds_no_dup_types_helper >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION, METIS_PROVE [] ``P ∨ Q ⇔ ¬P ⇒ Q``] >>
     pop_assum kall_tac >>
     pop_assum (qspec_then `mk_id mn e` mp_tac) >>
     `MEM (mk_id mn e) (MAP (λ(tvs,tn,ctors). mk_id mn tn) tdefs)`
               by (full_simp_tac(srw_ss())[MEM_MAP] >>
                   qexists_tac `y` >>
                   srw_tac[][] >>
                   PairCases_on `y` >>
                   srw_tac[][]) >>
     simp [] >>
     rpt (pop_assum (fn _ => all_tac)) >>
     srw_tac[][MEM_FLAT, MEM_MAP] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     srw_tac[][] >>
     rename [`MEM (Dtype locs l) ds`] >>
     FIRST_X_ASSUM (qspecl_then [`MAP (mk_id mn o FST o SND) l`] mp_tac) >>
     srw_tac[][]
     >- (qexists_tac `Dtype locs l` >>
         srw_tac[][LAMBDA_PROD, combinTheory.o_DEF])
     >- (srw_tac[][combinTheory.o_DEF, MEM_MAP, EXISTS_PROD] >>
         srw_tac[][LAMBDA_PROD] >>
         rename [`UNCURRY _ y`] >>
         PairCases_on `y` >>
         full_simp_tac(srw_ss())[] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []);

val type_ds_decls_ok = Q.store_thm ("type_ds_decls_ok",
 `!mn tenv decls' tenv' ds tdecs_no_sig.
  type_ds F mn tdecs_no_sig tenv ds decls' tenv' ∧
  mn ≠ []
  ⇒
  decls_ok (union_decls <|defined_mods := {mn}; defined_types := ∅; defined_exns := ∅ |> decls')`,
 rw [decls_ok_def, union_decls_def]
 >> imp_res_tac type_ds_mod
 >> full_simp_tac (srw_ss()++DNF_ss) [decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
 >> rw []
 >> fs [weak_decls_def, SUBSET_DEF]);

(* ---------- type_specs ---------- *)

val type_specs_tenv_ok = Q.store_thm ("type_specs_tenv_ok",
  `!mn tenvT specs decls' tenv'.
    type_specs mn tenvT specs decls' tenv' ⇒
    tenv_abbrev_ok tenvT
    ⇒
    tenv_ok tenv'`,
 ho_match_mp_tac type_specs_ind
 >> rw []
 >- (
   irule extend_dec_tenv_ok
   >> simp []
   >> rw [tenv_ok_def, tenv_val_ok_def]
   >> irule check_freevars_subst_single
   >> simp [EVERY_MAP, EVERY_GENLIST, check_freevars_def]
   >> irule check_freevars_type_name_subst
   >> simp []
   >> metis_tac [check_freevars_add, DECIDE ``x ≥ 0n``])
 >- (
   match_mp_tac extend_dec_tenv_ok
   >> simp [Once CONJ_SYM]
   >> simp [Once tenv_ok_def, GSYM CONJ_ASSOC]
   >> simp [Once CONJ_SYM]
   >> simp [GSYM CONJ_ASSOC]
   >> conj_asm1_tac
   >- (
     fs [tenv_abbrev_ok_def]
     >> irule nsAll_alist_to_ns
     >> simp [EVERY_MAP, EVERY_MEM]
     >> rw []
     >> pairarg_tac
     >> simp []
     >> rpt (pairarg_tac >> fs [])
     >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
   >> rw []
   >- (
     first_x_assum irule
     >> fs [tenv_abbrev_ok_def]
     >> irule nsAll_nsAppend
     >> metis_tac [])
   >- (
     irule check_ctor_tenv_ok
     >> simp [tenv_abbrev_ok_def]
     >> irule nsAll_nsAppend
     >> fs [tenv_abbrev_ok_def]))
 >- (
   `tenv_abbrev_ok (nsAppend (nsSing tn (tvs,type_name_subst tenvT t)) tenvT)`
     by (
       fs [tenv_abbrev_ok_def]
       >> irule nsAll_nsBind
       >> simp []
       >> irule check_freevars_type_name_subst
       >> simp [tenv_abbrev_ok_def])
   >> fs []
   >> irule extend_dec_tenv_ok
   >> simp [tenv_ok_def, tenv_abbrev_ok_def]
   >> irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def])
 >- (
   fs []
   >> irule extend_dec_tenv_ok
   >> simp [tenv_ok_def, tenv_ctor_ok_def, EVERY_MAP]
   >> fs [check_exn_tenv_def]
   >> fs [EVERY_MEM]
   >> rw []
   >> first_x_assum drule
   >> first_x_assum drule
   >> rw []
   >> irule check_freevars_type_name_subst
   >> simp [])
 >- (
   `tenv_abbrev_ok (nsSing tn (tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))))`
     by simp [tenv_abbrev_ok_def, check_freevars_def, EVERY_MEM, EVERY_MAP]
   >> irule extend_dec_tenv_ok
   >- (
     first_x_assum irule
     >> simp [tenv_abbrev_ok_def]
     >> irule nsAll_nsBind
     >> simp [check_freevars_def, EVERY_MAP, EVERY_MEM]
     >> fs [tenv_abbrev_ok_def])
   >> simp [tenv_ok_def]
   >> fs [tenv_abbrev_ok_def]));

val type_specs_no_mod = Q.store_thm ("type_specs_no_mod",
`!mn tenvT specs decls' new_tenv.
  type_specs mn tenvT specs decls' new_tenv ⇒
  decls'.defined_mods = {}`,
 ho_match_mp_tac type_specs_strongind >>
 srw_tac[][empty_decls_def] >>
 imp_res_tac type_d_mod >>
 full_simp_tac(srw_ss())[union_decls_def]);

val check_signature_tenv_ok = Q.store_thm ("check_signature_tenv_ok",
 `!mn tenv decls tenv' specs decls' tenv'' ds tdecs1 tenvT''.
   check_signature [mn] tenvT'' decls tenv' specs decls' tenv'' ∧
   type_ds F [mn] tdecs1 tenv ds decls tenv' ∧
   tenv_ok tenv ∧
   tenvT'' = tenv.t
   ⇒
   tenv_ok (extend_dec_tenv <| v := nsLift mn tenv''.v; c := nsLift mn tenv''.c; t := nsLift mn tenv''.t |> tenv)`,
 rw [check_signature_cases]
 >- (
   drule type_ds_tenv_ok_helper
   >> rw []
   >> irule extend_dec_tenv_ok
   >> simp []
   >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def, tenv_abbrev_ok_def])
 >- (
   drule type_specs_tenv_ok
   >> rw []
   >> irule extend_dec_tenv_ok
   >> simp []
   >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def, tenv_abbrev_ok_def]));

(* ---------------- type_top, type_prog ---------- *)

val type_prog_empty = Q.store_thm ("type_prog_empty[simp]",
 `!u mn decls tenv decls' r.
  type_prog u decls tenv [] decls' r ⇔ decls' = empty_decls ∧ r = <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>`,
 rw [Once type_prog_cases]);

val type_prog_sing = Q.store_thm ("type_prog_sing[simp]",
 `!u mn decls tenv d decls' r.
  type_prog u decls tenv [d] decls' r ⇔ type_top u decls tenv d decls' r`,
 simp [Once type_prog_cases] >>
 rw [] >>
 eq_tac >>
 rw [extend_dec_tenv_def]);

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

val type_top_decls_ok = Q.store_thm ("type_top_decls_ok",
`!uniq tdecs tenv top tdecs' new_tenv.
  type_top uniq tdecs tenv top tdecs' new_tenv
  ⇒
  decls_ok tdecs'`,
 rw [type_top_cases]
 >> simp [decls_ok_def]
 >- (
   drule type_d_mod
   >> simp_tac (srw_ss()++DNF_ss) [SUBSET_DEF, decls_to_mods_def, SUBSET_DEF, GSPECIFICATION])
 >- (
   rw [union_decls_mods]
   >> fs [union_decls_def, check_signature_cases]
   >> rw []
   >> TRY (drule type_ds_mod)
   >> TRY (drule type_specs_no_mod)
   >> simp_tac (srw_ss()++DNF_ss) [SUBSET_DEF, decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
   >> rw []
   >> fs [weak_decls_def, SUBSET_DEF]));

val type_prog_decls_ok = Q.store_thm ("type_prog_decls_ok",
`!uniq tdecs tenv prog tdecs' new_tenv.
  type_prog uniq tdecs tenv prog tdecs' new_tenv
  ⇒
  decls_ok tdecs'`,
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][] >>
 srw_tac[][Once type_prog_cases]
 >- simp [decls_ok_def, empty_decls_def, decls_to_mods_def]
 >> irule decls_ok_union
 >> simp []
 >> metis_tac [type_top_decls_ok]);

val type_no_dup_top_types_lem = Q.prove (
`!uniq decls1 tenv prog decls1' res.
  type_prog uniq decls1 tenv prog decls1' res
  ⇒
  ALL_DISTINCT (prog_to_top_types prog) ∧
  DISJOINT decls1.defined_types (IMAGE (mk_id []) (set (prog_to_top_types prog)))`,
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][semanticPrimitivesTheory.prog_to_top_types_def] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_top_cases] >>
 srw_tac[][ALL_DISTINCT_APPEND, empty_decls_def]
 >- (full_simp_tac(srw_ss())[type_d_cases, semanticPrimitivesTheory.decs_to_types_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[check_ctor_tenv_def] >>
     full_simp_tac(srw_ss())[LAMBDA_PROD])
 >- (`mk_id [] e ∈ decls1'.defined_types`
            by (full_simp_tac(srw_ss())[type_d_cases, semanticPrimitivesTheory.decs_to_types_def] >>
                srw_tac[][] >>
                full_simp_tac(srw_ss())[mk_id_def] >>
                full_simp_tac(srw_ss())[MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
                metis_tac []) >>
     full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [])
 >- (srw_tac[][semanticPrimitivesTheory.decs_to_types_def] >>
     full_simp_tac(srw_ss())[type_d_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD, mk_id_def, FORALL_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD, mk_id_def, FORALL_PROD] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[type_d_cases, empty_decls_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION, union_decls_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[MEM_MAP,LAMBDA_PROD, EXISTS_PROD, mk_id_def, FORALL_PROD] >>
     metis_tac []));

val type_no_dup_top_types_lem2 = Q.prove (
`!uniq decls1 tenv prog decls1' tenv'.
  type_prog uniq decls1 tenv prog decls1' tenv'
  ⇒
  no_dup_top_types prog (IMAGE TypeId decls1.defined_types)`,
 srw_tac[][semanticPrimitivesTheory.no_dup_top_types_def]
 >- metis_tac [type_no_dup_top_types_lem] >>
 imp_res_tac type_no_dup_top_types_lem >>
 full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
 srw_tac[][] >>
 cases_on `x` >>
 srw_tac[][MEM_MAP] >>
 full_simp_tac(srw_ss())[mk_id_def] >>
 metis_tac []);

val type_no_dup_top_types = Q.store_thm("type_no_dup_top_types",
`!decls1 tenv prog decls1' tenv' uniq decls2 decls_no_sig.
  type_prog uniq decls1 tenv prog decls1' tenv' ∧
  consistent_decls decls2 decls_no_sig ∧
  weak_decls_only_mods decls_no_sig decls1
  ⇒
  no_dup_top_types prog decls2`,
 srw_tac[][] >>
 `no_dup_top_types prog (IMAGE TypeId decls1.defined_types)`
         by metis_tac [type_no_dup_top_types_lem2] >>
 full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_top_types_def] >>
 full_simp_tac(srw_ss())[RES_FORALL, DISJOINT_DEF, SUBSET_DEF, EXTENSION, weak_decls_only_mods_def, consistent_decls_def] >>
 srw_tac[][] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[] >>
 res_tac >>
 every_case_tac >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 srw_tac[][] >>
 metis_tac []);

val type_no_dup_mods_lem = Q.prove (
`!uniq decls1 tenv prog decls1' res.
  type_prog uniq decls1 tenv prog decls1' res
  ⇒
  ALL_DISTINCT (prog_to_mods prog) ∧
  DISJOINT decls1.defined_mods (set (prog_to_mods prog))`,
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][semanticPrimitivesTheory.prog_to_mods_def] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_top_cases] >>
 srw_tac[][ALL_DISTINCT_APPEND, empty_decls_def]
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac []));

val type_no_dup_mods = Q.store_thm ("type_no_dup_mods",
`!uniq decls1 tenv prog decls1' tenv'.
  type_prog uniq decls1 tenv prog decls1' tenv'
  ⇒
  no_dup_mods prog decls1.defined_mods`,
 srw_tac[][semanticPrimitivesTheory.no_dup_mods_def] >>
 metis_tac [type_no_dup_mods_lem, DISJOINT_SYM]);

 (*

(* closed *)

val _ = Parse.overload_on("tmenv_dom",``λmenv. {Long m x | (m,x) | ∃e.  FLOOKUP menv m = SOME e ∧ MEM x (MAP FST e)}``);

open boolSimps semanticPrimitivesPropsTheory

val tenv_names_def = Define`
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)`
val _ = export_rewrites["tenv_names_def"]

val lookup_tenv_names = Q.store_thm("lookup_tenv_names",
  `∀tenv n inc x. lookup_tenv_val n inc tenv = SOME x ⇒ n ∈ tenv_names tenv`,
  Induct >> simp[lookup_tenv_val_def] >> metis_tac[])

val tenv_names_bind_var_list = Q.store_thm("tenv_names_bind_var_list",
  `∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2`,
  ho_match_mp_tac bind_var_list_ind >>
  simp[bind_var_list_def,EXTENSION] >>
  metis_tac[])

val tenv_names_bind_var_list2 = Q.store_thm("tenv_names_bind_var_list2",
  `∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv`,
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >> simp[bind_var_list2_def] >>
  simp[EXTENSION] >> metis_tac[])

val type_p_closed = Q.prove(
  `(∀tvs tcenv p t tenv.
       type_p tvs tcenv p t tenv ⇒
       pat_bindings p [] = MAP FST tenv) ∧
    (∀tvs cenv ps ts tenv.
      type_ps tvs cenv ps ts tenv ⇒
      pats_bindings ps [] = MAP FST tenv)`,
  ho_match_mp_tac type_p_ind >>
  simp[astTheory.pat_bindings_def] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[SUBSET_DEF] >>
  srw_tac[][Once pat_bindings_accum]);

val type_funs_dom = Q.prove (
  `!tenv funs tenv'.
    type_funs tenv funs tenv'
    ⇒
    IMAGE FST (set funs) = IMAGE FST (set tenv')`,
   Induct_on `funs` >>
   srw_tac[][Once type_e_cases] >>
   srw_tac[][] >>
   metis_tac []);

val type_e_closed = Q.prove(
  `(∀tenv e t.
      type_e tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)) ∧
    (∀tenv es ts.
      type_es tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)) ∧
    (∀tenv funs ts.
      type_funs tenv funs ts ⇒
      FV_defs funs ⊆ (IMAGE Short (tenv_names tenv.v)) ∪ tmenv_dom tenv.m)`,
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

val type_d_closed = Q.prove(
  `∀uniq mno decls tenv d w x.
      type_d uniq mno decls tenv d w x ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)`,
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
val type_ds_closed = Q.prove(
  `∀uniq mn decls tenv ds w x. type_ds uniq mn decls tenv ds w x ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)`,
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
val type_top_closed = Q.store_thm("type_top_closed",
  `∀uniq decls tenv top decls' new_tenv.
      type_top uniq decls tenv top decls' new_tenv
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv.v) ∪ tmenv_dom tenv.m)`,
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
   qpat_x_assum `!x. P x` (mp_tac o Q.SPEC `x'`) >>
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
   *)

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
