open preamble;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory funBigStepTheory;
open terminationTheory;
open evalPropsTheory;
open weakeningTheory typeSysPropsTheory typeSoundInvariantsTheory;
open funBigStepPropsTheory;

val _ = new_theory "typeSound";

val disjoint_image = Q.store_thm ("disjoint_image",
 `!s1 s2 f. DISJOINT (IMAGE f s1) (IMAGE f s2) ⇒ DISJOINT s1 s2`,
 rw [DISJOINT_DEF, EXTENSION]
 >> metis_tac []);

val sing_list = Q.prove (
`!l. LENGTH l = 1 ⇔ ?x. l = [x]`,
 Cases
 >> rw []
 >> Cases_on `t`
 >> rw []);

val EVERY_LIST_REL = Q.prove (
`EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y)`,
 induct_on `l` >>
 srw_tac[][REPLICATE]);

val v_unchanged = Q.store_thm ("v_unchanged[simp]",
`!tenv x. tenv with v := tenv.v = tenv`,
 srw_tac[][type_environment_component_equality]);

val type_v_cases_eqn = SIMP_RULE (srw_ss()) [] (List.nth (CONJUNCTS type_v_cases, 0));

val has_lists_v_to_list = Q.prove (
`!ctMap tvs tenvS t3.
  ctMap_has_lists ctMap ∧
  type_v tvs ctMap tenvS v (Tapp [t3] (TC_name (Short "list")))
  ⇒
  ?vs. v_to_list v = SOME vs ∧
  (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs)`,
 measureInduct_on `v_size v` >>
 srw_tac[][] >>
 pop_assum mp_tac >>
 srw_tac[][Once type_v_cases] >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac type_funs_Tfn >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def,Tchar_def] >>
 cases_on `tn` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[ctMap_has_lists_def] >>
 `cn = "::" ∨ cn = "nil"` by metis_tac [NOT_SOME_NONE] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 fs [EVERY2_THM] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][v_to_list_def,v_to_char_list_def] >>
 full_simp_tac(srw_ss())[type_subst_def] >>
 rename1 `type_v _ _ _ v _` >>
 LAST_X_ASSUM (mp_tac o Q.SPEC `v`) >>
 srw_tac[][v_size_def, basicSizeTheory.option_size_def, basicSizeTheory.pair_size_def,
     id_size_def, list_size_def, tid_or_exn_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 res_tac >> srw_tac[][] >>
 full_simp_tac(srw_ss())[flookup_fupdate_list] >> srw_tac[][] >> full_simp_tac(srw_ss())[GSYM Tchar_def] >>
 simp [GSYM PULL_EXISTS] >>
 rw [] >>
 qpat_assum`type_v _ _ _ v Tchar`mp_tac >>
 simp[Once type_v_cases,Tchar_def] >>
 srw_tac[][] >> srw_tac[][v_to_char_list_def] >>
 TRY (
   full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
   qpat_assum`TC_char = X`mp_tac >>
   BasicProvers.CASE_TAC ) >>
 imp_res_tac type_funs_Tfn >> full_simp_tac(srw_ss())[]);

(* Classifying values of basic types *)
val canonical_values_thm = Q.store_thm ("canonical_values_thm",
` (type_v tvs tenvC tenvS v (Tref t1) ⇒ (∃n. v = Loc n)) ∧
  (type_v tvs tenvC tenvS v Tint ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs tenvC tenvS v Tchar ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs tenvC tenvS v Tstring ⇒ (∃s. v = Litv (StrLit s))) ∧
  (type_v tvs ctMap tenvS v (Tapp [] (TC_name (Short "bool"))) ∧ ctMap_has_bools ctMap ⇒
   ∃b. v = Boolv b) ∧
  (type_v tvs tenvC tenvS v (Tfn t1 t2) ⇒
    (∃env n e. v = Closure env n e) ∨
    (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v Tword8 ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword64 ⇒ (∃n. v = Litv (Word64 n))) ∧
  (type_v tvs ctMap tenvS v Tword8array ⇒ (∃n. v = Loc n)) ∧
  (!t3. type_v tvs ctMap tenvS v (Tapp [t3] (TC_name (Short "list"))) ∧ ctMap_has_lists ctMap ⇒
        (?vs. v_to_list v = SOME vs) ∧
        ((t3 = Tchar) ⇒ ?vs. v_to_char_list v = SOME vs)) ∧
  (!t3. type_v tvs ctMap tenvS v (Tapp [t3] TC_vector) ⇒ (?vs. v = Vectorv vs)) ∧
  (!t3. type_v tvs ctMap tenvS v (Tapp [t3] TC_array) ⇒ (∃n. v = Loc n))`,
 srw_tac[][] >>
 full_simp_tac(srw_ss())[Once type_v_cases, deBruijn_subst_def] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 TRY (Cases_on `tn`) >>
 TRY (full_simp_tac(srw_ss())[Tchar_def]>>NO_TAC) >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 imp_res_tac type_funs_Tfn >>
 TRY (full_simp_tac(srw_ss())[Tchar_def]>>NO_TAC) >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >- (
   full_simp_tac(srw_ss())[ctMap_has_bools_def,Boolv_def] >>
   Cases_on`cn = "true"`>>full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[LENGTH_NIL] >>
   rw [] >> fs [] >- metis_tac[] >>
   Cases_on`cn = "false"`>>full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[LENGTH_NIL] >>
   rw [] >> fs []>- metis_tac[] >>
   metis_tac[optionTheory.NOT_SOME_NONE]) >>
 fs[Tword64_def,Tchar_def] >>
 imp_res_tac has_lists_v_to_list >>
 full_simp_tac(srw_ss())[] >>
 fsrw_tac[][GSYM PULL_EXISTS] >>
 fsrw_tac[boolSimps.DNF_ss][] >>
 first_x_assum match_mp_tac >>
 srw_tac[][Once type_v_cases_eqn, tid_exn_to_tc_def] >>
 metis_tac [Tchar_def]);

val eq_same_type = Q.prove (
`(!v1 v2 tvs ctMap cns tenvS t.
  type_v tvs ctMap tenvS v1 t ∧
  type_v tvs ctMap tenvS v2 t
  ⇒
  do_eq v1 v2 ≠ Eq_type_error) ∧
(!vs1 vs2 tvs ctMap cns tenvS ts.
  LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
  LIST_REL (type_v tvs ctMap tenvS) vs2 ts
  ⇒
  do_eq_list vs1 vs2 ≠ Eq_type_error)`,
 ho_match_mp_tac do_eq_ind >>
 srw_tac[][do_eq_def] >>
 ONCE_REWRITE_TAC [type_v_cases_eqn] >>
 srw_tac[][] >>
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[Tchar_def] >>
 srw_tac[][] >>
 imp_res_tac type_funs_Tfn >>
 full_simp_tac(srw_ss())[lit_same_type_def,ctor_same_type_def] >>
 full_simp_tac(srw_ss())[EVERY2_THM] >>
 full_simp_tac(srw_ss())[tid_exn_not] >>
 srw_tac[][]
 >> TRY ( full_simp_tac(srw_ss())[tid_exn_to_tc_11,same_tid_sym] >> NO_TAC)
 >- (full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
     full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (rpt (qpat_assum `type_v x0 x1 x2 x3 x4` mp_tac) >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[combinTheory.o_DEF, EVERY_LIST_REL] >>
     `(\x y. type_v tvs ctMap tenvS x y) = type_v tvs ctMap tenvS` by metis_tac [] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (cases_on `do_eq v1 v2` >>
     full_simp_tac(srw_ss())[]
     >- (cases_on `b` >>
         full_simp_tac(srw_ss())[] >>
         qpat_assum `!x. P x` (mp_tac o Q.SPECL [`tvs`, `ctMap`, `tenvS`, `ys`]) >>
         srw_tac[][METIS_PROVE [] ``(a ∨ b) = (~a ⇒ b)``] >>
         cases_on `vs1` >>
         rw [] >>
         full_simp_tac(srw_ss())[])
     >- metis_tac []));

val consistent_con_env_thm = Q.prove (
`∀ctMap cenv tenvC.
     consistent_con_env ctMap cenv tenvC ⇒
     ∀cn tvs ts tn.
       (lookup_alist_mod_env cn tenvC = SOME (tvs,ts,tn) ⇒
        lookup_alist_mod_env cn cenv = SOME (LENGTH ts,tn) ∧
        FLOOKUP ctMap (id_to_n cn,tn) = SOME (tvs, ts)) ∧
       (lookup_alist_mod_env cn tenvC = NONE ⇒ lookup_alist_mod_env cn cenv = NONE)`,
 srw_tac[][consistent_con_env_def] >>
 cases_on `lookup_alist_mod_env cn cenv` >>
 srw_tac[][]
 >- metis_tac [NOT_SOME_NONE]
 >- (PairCases_on `x` >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [PAIR_EQ, SOME_11])
 >> metis_tac [pair_CASES, SOME_11, PAIR_EQ, NOT_SOME_NONE]);

val type_env2_def = Define `
(type_env2 tenvC tenvS tvs [] [] = T) ∧
(type_env2 tenvC tenvS tvs ((x,v)::env) ((x',t) ::tenv) =
  (check_freevars tvs [] t ∧
   (x = x') ∧
   type_v tvs tenvC tenvS v t ∧
   type_env2 tenvC tenvS tvs env tenv)) ∧
(type_env2 tenvC tenvS tvs _ _ = F)`;

val type_env2_to_type_env = Q.prove (
`!tenvC tenvS tvs env tenv.
  type_env2 tenvC tenvS tvs env tenv ⇒
  type_env tenvC tenvS env (bind_var_list tvs tenv Empty)`,
ho_match_mp_tac (fetch "-" "type_env2_ind") >>
srw_tac[][type_env2_def] >>
srw_tac[][Once type_v_cases, bind_var_list_def]);

val type_env_merge_lem1 = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv
  ⇒
  type_env tenvC tenvS (env' ++ env) (bind_var_list tvs tenv' tenv) ∧ (LENGTH env' = LENGTH tenv')`,
Induct_on `tenv'` >>
srw_tac[][] >>
cases_on `env'` >>
srw_tac[][bind_var_list_def] >>
full_simp_tac(srw_ss())[type_env2_def] >|
[PairCases_on `h` >>
     srw_tac[][bind_var_list_def] >>
     PairCases_on `h'` >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[type_env2_def] >>
     srw_tac[][] >>
     srw_tac[][Once type_v_cases] >>
     metis_tac [],
 PairCases_on `h` >>
     srw_tac[][bind_var_list_def] >>
     PairCases_on `h'` >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[type_env2_def] >>
     srw_tac[][] >>
     srw_tac[][Once type_v_cases] >>
     metis_tac []]);

val type_env_merge_lem2 = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  type_env tenvC tenvS (env' ++ env) (bind_var_list tvs tenv' tenv) ∧
  (LENGTH env' = LENGTH tenv')
  ⇒
   type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv`,
 Induct_on `env'` >>
 srw_tac[][] >>
 cases_on `tenv'` >>
 full_simp_tac(srw_ss())[bind_var_list_def] >>
 srw_tac[][type_env2_def] >>
 qpat_assum `type_env x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 PairCases_on `h` >>
 PairCases_on `h'` >>
 srw_tac[][type_env2_def] >>
 full_simp_tac(srw_ss())[bind_var_list_def] >>
 srw_tac[][type_env2_def] >>
 metis_tac [type_v_freevars]);

val type_env_merge = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  ((type_env tenvC tenvS (env' ++ env) (bind_var_list tvs tenv' tenv) ∧
    (LENGTH env' = LENGTH tenv'))
   =
   (type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv))`,
metis_tac [type_env_merge_lem1, type_env_merge_lem2]);

val type_funs_fst = Q.prove (
`!tenv funs tenv'.
  type_funs tenv funs tenv'
  ⇒
  MAP (λ(f,x,e). f) funs = MAP FST tenv'`,
 induct_on `funs` >>
 srw_tac[][] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
 srw_tac[][] >>
 srw_tac[][] >>
 metis_tac []);

val type_recfun_env_help = Q.prove (
`∀fn funs funs' ctMap tenv bindings tenv0 env tenvS tvs bindings'.
  ALL_DISTINCT (MAP (\(x,y,z). x) funs') ∧
  tenv_ok tenv ∧
  consistent_con_env ctMap env.c tenv.c ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
  type_env ctMap tenvS env.v tenv0 ∧
  type_funs (tenv with v := bind_var_list 0 bindings' (bind_tvar tvs tenv0)) funs' bindings' ∧
  type_funs (tenv with v := bind_var_list 0 bindings' (bind_tvar tvs tenv0)) funs bindings
  ⇒
  type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs) bindings`,
 induct_on `funs` >>
 srw_tac[][] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][Once type_v_cases, type_env2_def] >>
 full_simp_tac(srw_ss())[] >>
 `type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs) bindings''`
               by metis_tac [optionTheory.NOT_SOME_NONE] >>
 srw_tac[][type_env2_def] >>
 full_simp_tac(srw_ss())[] >>
 `ALOOKUP bindings' fn = SOME (Tapp [t1;t2] TC_fn)` by metis_tac [] >|
 [full_simp_tac(srw_ss())[num_tvs_bind_var_list, check_freevars_def] >>
      metis_tac [num_tvs_def, bind_tvar_def, arithmeticTheory.ADD,
                 arithmeticTheory.ADD_COMM, type_v_freevars],
  qexists_tac `tenv with v := tenv0` >>
      srw_tac[][] >>
      qexists_tac `bindings'` >>
      srw_tac[][] >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac type_funs_fst >>
      full_simp_tac(srw_ss())[MEM_MAP] >>
      fs [tenv_ok_def] >>
      metis_tac [FST, pair_CASES,ALOOKUP_MEM,MEM_MAP]]);

val type_recfun_env = Q.prove (
`∀funs ctMap tenvS tvs tenv tenv0 env bindings.
  tenv_ok tenv ∧
  consistent_con_env ctMap env.c tenv.c ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  type_env ctMap tenvS env.v tenv0 ∧
  type_funs (tenv with v := bind_var_list 0 bindings (bind_tvar tvs tenv0)) funs bindings ∧
  ALL_DISTINCT (MAP (\(x,y,z). x) funs)
  ⇒
  type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs) bindings`,
metis_tac [type_recfun_env_help]);

val type_v_exn = SIMP_RULE (srw_ss()) [] (Q.prove (
`!tvs cenv senv.
  ctMap_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME ("Chr",TypeExn (Short "Chr"))) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME ("Subscript",TypeExn (Short "Subscript"))) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME ("Bind",TypeExn (Short "Bind"))) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME ("Div",TypeExn (Short "Div"))) []) Texn`,
 ONCE_REWRITE_TAC [type_v_cases] >>
 srw_tac[][ctMap_has_exns_def, tid_exn_to_tc_def] >>
 metis_tac [type_v_rules]));

val v_to_list_type = Q.prove (
`!v vs.
  ctMap_ok ctMap ∧
  ctMap_has_lists ctMap ∧
  v_to_list v = SOME vs ∧
  type_v 0 ctMap tenvS v (Tapp [t] (TC_name (Short "list")))
  ⇒
  type_v tvs ctMap tenvS (Vectorv vs) (Tapp [t] TC_vector)`,
 ho_match_mp_tac v_to_list_ind >>
 srw_tac[][v_to_list_def]
 >- full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases_eqn] >>
 res_tac >>
 full_simp_tac(srw_ss())[ctMap_has_lists_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_subst_def, flookup_fupdate_list]
 >- metis_tac [type_v_weakening, weakCT_refl, weakS_refl] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 res_tac >>
 FIRST_X_ASSUM (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
 srw_tac[][]);

val char_list_to_v_type = Q.prove (
  `ctMap_has_lists ctMap
   ⇒
   type_v tvs ctMap tenvS (char_list_to_v (EXPLODE str)) (Tapp [Tchar] (TC_name (Short "list")))`,
    Induct_on`str` >> srw_tac[][char_list_to_v_def] >>
    simp[Once type_v_cases,tid_exn_to_tc_def,Tchar_def] >>
    full_simp_tac(srw_ss())[ctMap_has_lists_def,check_freevars_def] >>
    simp[Once type_v_cases] >>
    conj_tac >- (
      simp[Once type_v_cases] >>
      simp[type_subst_def,flookup_fupdate_list,Tchar_def] ) >>
    fs [type_subst_def, flookup_fupdate_list, Tchar_def]);

val v_to_char_list_type = Q.prove (
`!v vs.
  ctMap_has_lists ctMap ∧
  v_to_char_list v = SOME vs ∧
  type_v 0 ctMap tenvS v (Tapp [t] (TC_name (Short "list")))
  ⇒
  type_v tvs ctMap tenvS (Litv (StrLit (IMPLODE vs))) (Tstring)`,
 ho_match_mp_tac v_to_char_list_ind >>
 srw_tac[][v_to_char_list_def]
 >- full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases_eqn]);

val type_v_Boolv = Q.prove(
  `ctMap_has_bools ctMap ⇒
    type_v tvs ctMap tenvS (Boolv b) (Tapp [] (TC_name (Short "bool")))`,
  srw_tac[][Boolv_def] >>
  srw_tac[][Once type_v_cases_eqn,tid_exn_to_tc_def,LENGTH_NIL] >>
  full_simp_tac(srw_ss())[ctMap_has_bools_def] >>
  srw_tac[][Once type_v_cases]);

val opapp_type_sound = Q.store_thm ("opapp_type_sound",
`!ctMap tenvS vs ts t.
 type_op Opapp ts t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs ts
 ⇒
 ?env e tenv.
   tenv_ok tenv ∧
   type_all_env ctMap tenvS env tenv ∧
   type_e tenv e t ∧
   do_opapp vs = SOME (env,e)`,
 rw [type_op_cases]
 >> fs []
 >> rw []
 >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def] canonical_values_thm)
 >> rw [do_opapp_def]
 >- (
   rename1 `type_v _ _ _ (Closure env n e) _`
   >> qpat_assum `type_v _ _ _ (Closure env n e) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> qexists_tac `(tenv with v := Bind_name n 0 t2 (bind_tvar 0 tenv.v))`
   >> rw []
   >> fs [tenv_ok_def, type_all_env_def]
   >> simp [Once type_v_cases, bind_tvar_def])
 >- (
   rename1 `type_v _ _ _ (Recclosure env funs n) _`
   >> qpat_assum `type_v _ _ _ (Recclosure env funs n) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> imp_res_tac type_funs_find_recfun
   >> fs []
   >> rw []
   >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def] type_recfun_lookup)
   >> fs []
   >> qmatch_assum_abbrev_tac `type_e (_ with v := bindings) _ _`
   >> qexists_tac `tenv with v := bindings`
   >> rw []
   >> imp_res_tac type_recfun_env
   >> drule type_env2_to_type_env
   >> rw [Abbr `bindings`]
   >> fs [tenv_ok_def, type_all_env_def]
   >> simp [Once type_v_cases, build_rec_env_merge, bind_tvar_def]
   >> metis_tac [type_env_merge]));

val store_type_extension_def = Define `
store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))`;

val store_type_extension_weakS = Q.store_thm ("store_type_extension_weakS",
`!tenvS1 tenvS2.
  store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1`,
 srw_tac[][store_type_extension_def, weakS_def, FLOOKUP_FUNION] >>
 full_simp_tac(srw_ss())[SUBMAP_DEF, FLOOKUP_DEF, FUNION_DEF] >>
 metis_tac []);

val store_type_extension_refl = Q.store_thm ("store_type_extension_refl",
  `!tenvS. store_type_extension tenvS tenvS`,
 rw [store_type_extension_def] >>
 qexists_tac `FEMPTY` >>
 rw []);

val store_type_extension_trans = Q.store_thm ("store_type_extension_trans",
  `!s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3`,
 rw [store_type_extension_def]
 >> qexists_tac `FUNION tenvS'' tenvS'`
 >> rw [FUNION_ASSOC, FLOOKUP_FUNION]
 >> CASE_TAC
 >> rw []
 >> fs [FLOOKUP_FUNION]
 >> first_x_assum (qspec_then `l` mp_tac)
 >> rw []
 >> every_case_tac
 >> fs []);

val store_assign_type_sound = Q.store_thm ("store_assign_type_sound",
 `!ctMap tenvS store sv st l.
  type_s ctMap tenvS store ∧
  FLOOKUP tenvS l = SOME st ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store'.
    store_assign l sv store = SOME store' ∧
    type_s ctMap tenvS store'`,
 rw [store_assign_def, type_s_def, store_v_same_type_def]
 >- (
   first_x_assum (qspec_then `l` mp_tac)
   >> rw [store_lookup_def]
   >> fs [FLOOKUP_DEF])
 >- (
   first_x_assum (qspec_then `l` mp_tac)
   >> fs [store_lookup_def]
   >> every_case_tac
   >> fs []
   >> Cases_on `st`
   >> fs [type_sv_def])
 >- (
   first_x_assum (qspec_then `l'` mp_tac)
   >> rw [store_lookup_def])
 >- (
   fs [store_lookup_def, EL_LUPDATE]
   >> rw []
   >> fs []));

val store_alloc_type_sound = Q.store_thm ("store_alloc_type_sound",
 `!ctMap tenvS store sv st.
  ctMap_ok ctMap ∧
  type_s ctMap tenvS store ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store' tenvS' n.
    store_type_extension tenvS tenvS' ∧
    store_alloc sv store = (store', n) ∧
    type_s ctMap tenvS' store' ∧
    FLOOKUP tenvS' n = SOME st`,
 rw [store_alloc_def]
 >> qexists_tac `tenvS |+ (LENGTH store, st)`
 >> rw [store_type_extension_def, FLOOKUP_UPDATE]
 >- (
   qexists_tac `FEMPTY |+ (LENGTH store, st)`
   >> fs [type_s_def]
   >> rw [FLOOKUP_UPDATE, fmap_eq_flookup, FLOOKUP_FUNION]
   >> rw []
   >> fs [store_lookup_def]
   >> CCONTR_TAC
   >> fs []
   >> `l < l` by metis_tac [option_nchotomy]
   >> fs [])
 >- (
   fs [type_s_def, store_lookup_def, FLOOKUP_UPDATE, GSYM SNOC_APPEND]
   >> rw []
   >> rw [EL_LENGTH_SNOC, EL_SNOC]
   >> irule type_sv_weakening
   >> rw [weakS_def]
   >> qexists_tac `ctMap`
   >> rw [weakCT_refl]
   >> qexists_tac `tenvS`
   >> rw []
   >> CCONTR_TAC
   >> fs [FLOOKUP_DEF]
   >> fs []
   >> res_tac
   >> fs []));

val store_lookup_type_sound = Q.store_thm ("store_lookup_type_sound",
 `!ctMap tenvS store n st.
  type_s ctMap tenvS store ∧
  FLOOKUP tenvS n = SOME st
  ⇒
  ?sv.
    store_lookup n store = SOME sv ∧
    type_sv ctMap tenvS sv st`,
 rw [type_s_def]
 >> metis_tac []);

val op_type_sound = Q.store_thm ("op_type_sound",
`!ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
 good_ctMap ctMap ∧
 op ≠ Opapp ∧
 type_s ctMap tenvS store ∧
 type_op op ts t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap tenvS' store' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort _) => F`,
 rw [type_op_cases, good_ctMap_def]
 >> fs []
 >> rw []
 >> TRY (Cases_on `wz`)
 >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def, Tref_def, Tword64_def] canonical_values_thm)
 >> rw [do_app_cases, PULL_EXISTS]
 >- ( (* Integer ops *)
   rename1 `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >> Cases_on `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >- (
     fs []
     >> metis_tac [type_v_exn, store_type_extension_refl, prim_exn_def])
   >- (
     fs []
     >> simp [Once type_v_cases]
     >> metis_tac [store_type_extension_refl]))
 >- ( (* Boolean ops *)
   metis_tac [type_v_Boolv, store_type_extension_refl])
 >- ( (* Word8 ops *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Word64 ops *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* 8-bit shift *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* 64 bit shift *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Equality *)
   metis_tac [type_v_Boolv, store_type_extension_refl, eq_result_nchotomy, eq_same_type])
 >- ( (* ref update *)
   simp [Once type_v_cases]
   >> qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> metis_tac [type_sv_def, store_type_extension_refl, store_assign_type_sound])
 >- ( (* rev alloc *)
   simp [Once type_v_cases]
   >> rename1 `type_v _ _ _ v t`
   >> `type_sv ctMap tenvS (Refv v) (Ref_t t)` by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [type_v_freevars])
 >- ( (* deref *)
   qpat_assum `type_v _ _ _ (Loc n) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `type_sv _ _ sv _`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> metis_tac [store_type_extension_refl])
 >- ( (* W8array alloc *)
   rename1 `type_v _ _ _ (Litv (Word8 w)) _`
   >> rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> `type_sv ctMap tenvS (W8array (REPLICATE (Num (ABS n)) w)) W8array_t`
     by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `n < 0`
   >> simp [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* W8array lookup *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> Cases_on `n < 0`
   >> rw [PULL_EXISTS, type_v_exn, prim_exn_def]
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `store_lookup l _ = SOME sv`
   >- (
     Cases_on `sv`
     >> fs [type_sv_def]
     >> metis_tac [store_type_extension_refl])
   >- (
     Cases_on `sv`
     >> fs [type_sv_def]
     >> rename1 `store_lookup _ _ = SOME (W8array ws)`
     >> Cases_on `Num (ABS n) ≥ LENGTH ws`
     >> rw []
     >> simp [type_v_exn]
     >> simp [Once type_v_cases]
     >> metis_tac [store_type_extension_refl]))
 >- ( (* W8array length *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> simp [Once type_v_cases]
   >> rename1 `store_lookup l _ = SOME sv`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >- metis_tac [store_type_extension_refl])
 >- ( (* W8array assignment *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `store_lookup l store = SOME sv`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> Cases_on `n < 0`
   >> fs [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `store_lookup _ _ = SOME (W8array ws)`
   >> Cases_on `Num (ABS n) ≥ LENGTH ws`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `type_v _ _ _ (Litv (Word8 w)) _`
   >> `type_sv ctMap tenvS (W8array (LUPDATE w (Num (ABS n)) ws)) W8array_t`
     by rw [type_sv_def]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Int to Word8 *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Int to Word64 *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Word8 to Int *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Word64 to Int *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Char to Int *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Int to Char *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> Cases_on `n < 0 ∨ n > 255`
   >> rw []
   >> rw []
   >> simp [type_v_exn, prim_exn_def]
   >> fs []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* char boolean op *)
   simp [type_v_Boolv]
   >> metis_tac [store_type_extension_refl])
 >- ( (* string to list *)
   simp [char_list_to_v_type]
   >> metis_tac [store_type_extension_refl])
 >- ( (* list to string *)
   simp []
   >> drule (GEN_ALL v_to_char_list_type)
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- ( (* string length *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* list to vector *)
   metis_tac [v_to_list_type, store_type_extension_refl])
 >- ( (* vector lookup *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> Cases_on `n < 0`
   >> rw [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> Cases_on `Num (ABS n) ≥ LENGTH vs`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> qpat_assum `type_v _ _ _ (Vectorv _) _` mp_tac
   >> simp [Once type_v_cases, EVERY_EL]
   >> rw []
   >> fs []
   >> `Num (ABS n) < LENGTH vs` by decide_tac
   >> metis_tac [store_type_extension_refl])
 >- ( (* vector length *)
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* Array alloc *)
   qpat_assum `type_v _ _ _ _ (Tapp [] TC_int)` mp_tac
   >> rename1 `type_v _ _ _ v t`
   >> rw []
   >> `type_sv ctMap tenvS (Varray (REPLICATE (Num (ABS n)) v)) (Varray_t t)`
     by rw [type_sv_def, EVERY_REPLICATE]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `n < 0`
   >> simp [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl, type_v_freevars])
 >- ( (* Array lookup *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> Cases_on `n < 0`
   >> rw [PULL_EXISTS, type_v_exn, prim_exn_def]
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `store_lookup l store = SOME sv`
   >- (
     Cases_on `sv`
     >> fs [type_sv_def]
     >> metis_tac [store_type_extension_refl])
   >- (
     Cases_on `sv`
     >> fs [type_sv_def]
     >> rename1 `store_lookup _ _ = SOME (Varray vs)`
     >> Cases_on `Num (ABS n) ≥ LENGTH vs`
     >> rw []
     >> simp [type_v_exn]
     >- metis_tac [store_type_extension_refl]
     >> fs [EVERY_EL]
     >> `Num (ABS n) < LENGTH vs` by decide_tac
     >> metis_tac [store_type_extension_refl]))
 >- ( (* Array length *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> simp [Once type_v_cases]
   >> rename1 `store_lookup _ _ = SOME sv`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >- metis_tac [store_type_extension_refl])
 >- ( (* Array update *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `store_lookup l _ = SOME sv`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> Cases_on `n < 0`
   >> fs [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `store_lookup _ _ = SOME (Varray vs)`
   >> Cases_on `Num (ABS n) ≥ LENGTH vs`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> `type_sv ctMap tenvS (Varray (LUPDATE x (Num (ABS n)) vs)) (Varray_t t1)`
     by (
       rw [type_sv_def]
       >> irule IMP_EVERY_LUPDATE
       >> simp [])
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- ( (* FFI call *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> `?ffi' ws'. call_FFI ffi n l = (ffi', ws')` by metis_tac [pair_CASES]
   >> simp []
   >> `type_sv ctMap tenvS (W8array ws') W8array_t` by rw [type_sv_def]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl]));

val build_conv_type_sound = Q.store_thm ("build_conv_type_sound",
`!envc cn vs tvs ts ctMap tenvS ts' tn tenvc tvs' tenvv l.
 consistent_con_env ctMap envc tenvc ∧
 do_con_check envc (SOME cn) l ∧
 num_tvs tenvv = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvv)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 lookup_alist_mod_env cn tenvc = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envc (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' (tid_exn_to_tc tn))`,
 rw []
 >> drule do_con_check_build_conv
 >> disch_then (qspec_then `REVERSE vs` mp_tac)
 >> rw []
 >> qexists_tac `v`
 >> rw []
 >> drule consistent_con_env_thm
 >> rw []
 >> fs [build_conv_def]
 >> res_tac
 >> fs []
 >> rw []
 >> simp [Once type_v_cases, GSYM EVERY2_REVERSE1]
 >> simp [GSYM FUNION_alist_to_fmap]
 >> rfs [bind_tvar_def, num_tvs_def]
 >> Cases_on `tvs`
 >> rfs [num_tvs_def]);

val pat_sound_tac =
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[deBruijn_subst_def, tid_exn_not] >>
 imp_res_tac type_funs_Tfn >>
 full_simp_tac(srw_ss())[Tchar_def]
 >> fs [tid_exn_not]

val pat_type_sound = Q.store_thm ("pat_type_sound",
 `(∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   consistent_con_env ctMap cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap tenvS st ∧
   type_env ctMap tenvS bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     type_env ctMap tenvS bindings' (bind_var_list tvs new_tbindings tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   consistent_con_env ctMap cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap tenvS st ∧
   type_env ctMap tenvS bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     type_env ctMap tenvS bindings' (bind_var_list tvs new_tbindings tbindings)))`,
 ho_match_mp_tac pmatch_ind
 >> rw [pmatch_def]
 >> TRY (qpat_assum `type_p _ _ _ _ _` mp_tac
         >> simp [Once type_p_cases])
 >> rw []
 >> rw [bind_var_list_def, type_env_eqn]
 >- pat_sound_tac
 >- (
   qpat_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule consistent_con_env_thm
   >> rw []
   >> res_tac
   >> fs []
   >> drule type_ps_length
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> fs [GSYM FUNION_alist_to_fmap]
     >> metis_tac [SOME_11, PAIR_EQ, same_ctor_and_same_tid])
   >- (
     fs [same_tid_def, tid_exn_to_tc_def]
     >> every_case_tac
     >> fs [same_tid_def]))
 >- (
   qpat_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- (
   simp [Once type_v_cases, Once type_p_cases]
   >> CCONTR_TAC
   >> fs []
   >> rw []
   >> metis_tac [type_ps_length, LIST_REL_LENGTH])
 >- (
   qpat_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> first_x_assum irule
   >> simp []
   >> metis_tac [type_v_weakening, weakCT_refl, weakS_refl])
 >- (
   first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- (
   rw []
   >> fs [Once type_p_cases]
   >> rw [bind_var_list_def])
 >- (
   rw []
   >> qpat_assum `type_ps _ _ (_::_) _ _` mp_tac
   >> simp [Once type_p_cases]
   >> rw []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> rw []
   >> rw []
   >> fs []
   >> simp [bind_var_list_append]
   >> first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- pat_sound_tac
 >- pat_sound_tac);

val type_pes_def = Define `
  type_pes tvs tenv pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e (tenv with v := bind_var_list tvs bindings tenv.v) e t2)`;

val exp_type_sound = Q.store_thm ("exp_type_sound",
 `(!(s:'ffi state) env es r s' tenv ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    good_ctMap ctMap ∧
    type_all_env ctMap tenvS env tenv ∧
    type_s ctMap tenvS s.refs ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es (tenv with v := bind_tvar tvs tenv.v) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap tenvS' s'.refs ∧
      store_type_extension tenvS tenvS' ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi state) env v pes err_v r s' tenv t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    good_ctMap ctMap ∧
    type_all_env ctMap tenvS env tenv ∧
    type_s ctMap tenvS s.refs ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v (Tapp [] TC_exn) ∧
    type_pes tvs tenv pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap tenvS' s'.refs ∧
      store_type_extension tenvS tenvS' ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort Rtype_error) => F)`,
 ho_match_mp_tac evaluate_ind
 >> simp [evaluate_def, type_es_list_rel, type_all_env_def,
          GSYM CONJ_ASSOC, good_ctMap_def]
 >> rw []
 >- metis_tac [store_type_extension_refl]
 >- (
   split_pair_case_tac
   >> fs []
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rename1 `evaluate _ _ (e2::es) = (s2,r2)`
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> fs [IMP_CONJ_THM]
   >> rpt (disch_then drule)
   >> rw []
   >> rename1 `store_type_extension _ new_tenvS`
   >> `consistent_mod_env new_tenvS ctMap env.m tenv.m`
     by metis_tac [store_type_extension_weakS,
                   weakCT_refl, type_v_weakening, consistent_con_env_def]
   >> `type_env ctMap new_tenvS env.v tenv.v`
     by metis_tac [store_type_extension_weakS,
                   weakCT_refl, type_v_weakening, consistent_con_env_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS, GSYM CONJ_ASSOC]
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `r2`
   >> fs []
   >> rw []
   >> metis_tac [store_type_extension_trans, store_type_extension_weakS,
                 weakCT_refl, type_v_weakening, consistent_con_env_def])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases, Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> rw []
   >> metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> rw []
   >- metis_tac []
   >> Cases_on `e`
   >> fs [type_pes_def]
   >> rw []
   >- (
     `consistent_mod_env tenvS' ctMap env.m tenv.m`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> `type_env ctMap tenvS' env.v tenv.v`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> rw []
     >> Cases_on `r`
     >> fs []
     >> rw []
     >> imp_res_tac evaluate_length
     >> fs [sing_list]
     >> fs [bind_tvar_def]
     >> metis_tac [store_type_extension_trans, type_v_freevars])
   >- metis_tac [])
 >- (
   imp_res_tac type_v_freevars
   >> qpat_assum `type_e _ (Con _ _) _` mp_tac
   >> simp [Once type_e_cases]
   >> fs [is_value_def]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1, r1)`
   >> fs [EVERY_REVERSE, ETA_THM]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> rw [type_es_list_rel, GSYM EVERY2_REVERSE1]
   >> qmatch_assum_abbrev_tac `LIST_REL _ _ types`
   >> first_x_assum (qspec_then `REVERSE types` mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     UNABBREV_ALL_TAC
     >> drule build_conv_type_sound
     >> rpt (disch_then drule)
     >> rw []
     >> fs []
     >> rw []
     >> metis_tac [])
   >- metis_tac []
   >- (
     fs [build_conv_def]
     >> rw []
     >> simp [Once type_v_cases, GSYM EVERY2_REVERSE1]
     >> metis_tac [])
   >- metis_tac [])
 >- (
   CCONTR_TAC
   >> fs []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> CCONTR_TAC
   >> fs []
   >> rw []
   >> fs [do_con_check_def]
   >> imp_res_tac consistent_con_env_thm
   >> fs []
   >> imp_res_tac type_es_length
   >> fs [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> imp_res_tac type_lookup_id
   >> fs []
   >> rw []
   >> qexists_tac `tenvS`
   >> simp [store_type_extension_refl]
   >> irule type_lookup_type_v
   >- fs [consistent_con_env_def]
   >- (
     imp_res_tac type_v_freevars
     >> fs [bind_tvar_def, is_value_def]
     >> Cases_on `tvs = 0`
     >> fs [num_tvs_def])
   >> fs [tenv_ok_def]
   >> metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> simp [Once type_v_cases]
   >> imp_res_tac type_v_freevars
   >> fs [num_tvs_def, bind_tvar_def]
   >> Cases_on `tvs = 0`
   >> fs [num_tvs_def]
   >> metis_tac [store_type_extension_refl])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> fs [is_value_def, type_es_list_rel]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`REVERSE ts`, `0`] mp_tac)
   >> rw [LIST_REL_REVERSE_EQ]
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     Cases_on `op = Opapp`
     >> fs []
     >> rename1 `LIST_REL (type_v 0 _ _) vs _`
     >- (
       drule opapp_type_sound
       >> fs [EVERY2_REVERSE1]
       >> disch_then drule
       >> rw []
       >> fs []
       >> Cases_on `s1.clock = 0`
       >> fs []
       >> rw []
       >- metis_tac []
       >> fs [type_all_env_def]
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [dec_clock_def, PULL_EXISTS]
       >> rename1 `type_e tenv' e t`
       >> disch_then (qspecl_then [`0`, `t`] mp_tac)
       >> simp [bind_tvar_def]
       >> rw []
       >> metis_tac [store_type_extension_trans])
     >- (
       fs [bind_tvar_def]
       >> `good_ctMap ctMap` by simp [good_ctMap_def]
       >> drule op_type_sound
       >> rpt (disch_then drule)
       >> disch_then (qspec_then `s1.ffi` mp_tac)
       >> rw []
       >> rename1 `do_app _ _ _ = SOME ((store1, ffi1), r1)`
       >> Cases_on `r1`
       >> fs []
       >> rw []
       >- metis_tac [store_type_extension_trans]
       >> rename1 `do_app _ _ _ = SOME (_, Rerr err_v)`
       >> Cases_on `err_v`
       >> fs []
       >> rw []
       >> metis_tac [store_type_extension_trans]))
     >- (
       rename1 `evaluate _ _ _ = (s1, Rerr err_v)`
       >> Cases_on `err_v`
       >> fs []
       >> rw []
       >> metis_tac []))
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `(Tapp [] (TC_name (Short "bool")))`] mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     drule (GEN_ALL (List.nth (CONJUNCTS (SPEC_ALL canonical_values_thm), 4)))
     >> disch_then drule
     >> rw []
     >> Cases_on `b`
     >> fs [do_log_def, Boolv_def]
     >> Cases_on `lop`
     >> fs []
     >> rw []
     >- (
       `consistent_mod_env tenvS' ctMap env.m tenv.m`
         by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
       >> `type_env ctMap tenvS' env.v tenv.v`
         by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [PULL_EXISTS]
       >> disch_then (qspecl_then [`0`, `Tapp [] (TC_name (Short "bool"))`] mp_tac)
       >> simp []
       >> rw []
       >> metis_tac [store_type_extension_trans])
     >- metis_tac []
     >- metis_tac []
     >- (
       `consistent_mod_env tenvS' ctMap env.m tenv.m`
         by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
       >> `type_env ctMap tenvS' env.v tenv.v`
         by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [PULL_EXISTS]
       >> disch_then (qspecl_then [`0`, `Tapp [] (TC_name (Short "bool"))`] mp_tac)
       >> simp []
       >> rw []
       >> metis_tac [store_type_extension_trans]))
   >- metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `(Tapp [] (TC_name (Short "bool")))`] mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     drule (GEN_ALL (List.nth (CONJUNCTS (SPEC_ALL canonical_values_thm), 4)))
     >> disch_then drule
     >> rw []
     >> Cases_on `b`
     >> fs [do_if_def, Boolv_def]
     >> rw []
     >> `consistent_mod_env tenvS' ctMap env.m tenv.m`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> `type_env ctMap tenvS' env.v tenv.v`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> fs [PULL_EXISTS]
     >> disch_then (qspecl_then [`0`] mp_tac)
     >> simp []
     >> rw []
     >> metis_tac [store_type_extension_trans])
   >- metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> rw []
   >- (
     fs [type_pes_def]
     >> rw []
     >> `consistent_mod_env tenvS' ctMap env.m tenv.m`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> `type_env ctMap tenvS' env.v tenv.v`
       by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> fs [type_v_exn, Bindv_def]
     >> rpt (disch_then drule)
     >> rw []
     >> Cases_on `r`
     >> fs []
     >> rw []
     >> imp_res_tac evaluate_length
     >> fs [sing_list]
     >> fs [bind_tvar_def]
     >> metis_tac [store_type_extension_trans, type_v_freevars])
   >- metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`] mp_tac)
   >> simp []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     rename1 `type_e (tenv with v := opt_bind_name n 0 t1 tenv.v) e2 t2`
     >> qabbrev_tac `env' = opt_bind n (HD [x]) env.v`
     >> qabbrev_tac `tenv' = tenv with v := opt_bind_name n 0 t1 tenv.v`
     >> `tenv_ok tenv'`
       by (fs [tenv_mod_ok_def, tenv_ok_def, tenv_tabbrev_ok_def, Abbr `tenv'`] >> NO_TAC)
     >> `consistent_mod_env tenvS' ctMap env.m tenv'.m`
       by (
         simp [Abbr `tenv'`] >>
         metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS])
     >> `consistent_con_env ctMap env.c tenv'.c`
       by (rw [Abbr `tenv'`] >> NO_TAC)
     >> `type_env ctMap tenvS' env' tenv'.v`
       by (
         simp [Abbr `tenv'`, Abbr `env'`]
         >> Cases_on `n`
         >> fs [opt_bind_def, opt_bind_name_def, type_env_eqn]
         >> metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS, type_v_freevars])
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> simp [PULL_EXISTS]
     >> disch_then (qspecl_then [`0`] mp_tac)
     >> simp []
     >> disch_then drule
     >> rw []
     >> metis_tac [store_type_extension_trans])
   >- metis_tac [])
 >- (
   fs []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> fs [PULL_EXISTS, is_value_def]
   >> first_x_assum irule
   >> fs []
   >> qexists_tac `tenv with v := bind_var_list 0 bindings (bind_tvar tvs tenv.v)`
   >> simp []
   >> rfs [build_rec_env_merge, bind_tvar_def, tenv_ok_def]
   >> metis_tac [type_env_merge_lem1, type_recfun_env, bind_tvar_def, tenv_ok_def])
 >- (
   CCONTR_TAC
   >> fs []
   >> rw []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> metis_tac [type_funs_distinct])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> fs [PULL_EXISTS]
   >> first_x_assum irule
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- metis_tac [store_type_extension_refl]
 >- (
   fs [type_pes_def, RES_FORALL]
   >> first_assum (qspec_then `(p,e)` mp_tac)
   >> simp_tac (srw_ss()) []
   >> rw []
   >> imp_res_tac type_v_freevars
   >> fs []
   >> qpat_assum `type_v _ _ _ _ (Tapp [] TC_exn)` mp_tac
   >> drule (hd (CONJUNCTS pat_type_sound))
   >> rpt (disch_then drule)
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> metis_tac [])
   >- (
     `tenv_ok (tenv with v := bind_var_list tvs bindings tenv.v)`
       by fs [tenv_ok_def]
     >> first_x_assum drule
     >> simp []
     >> rpt (disch_then drule)
     >> disch_then (qspecl_then [`[t2]`, `0`] mp_tac)
     >> simp [bind_tvar_def]
     >> rw []
     >> Cases_on `r`
     >> fs []
     >> metis_tac [type_v_weakening, weakCT_refl, weakS_refl]))
 >- (
   CCONTR_TAC
   >> fs [type_pes_def, RES_FORALL]
   >> pop_assum (qspec_then `(p,e)` mp_tac)
   >> simp []));

val let_tac =
  rw []
  >> Cases_on `r1`
  >> fs []
  >> rw []
  >- ( (* a value *)
    fs [good_ctMap_def, type_all_env_def]
    >> `type_env ctMap tenvS'' env.v tenv.v`
      by metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
    >> drule (hd (CONJUNCTS pat_type_sound))
    >> `type_env ctMap tenvS'' [] Empty` by simp [Once type_v_cases]
    >> rpt (disch_then drule)
    >> rw []
    >- ( (* No match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> rw [weakCT_refl, Bindv_def, type_v_exn, GSYM PULL_EXISTS]
      >- metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS]
      >> drule (hd (CONJUNCTS evaluate_state_unchanged))
      >> rw [])
    >- ( (* match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> drule (hd (CONJUNCTS evaluate_state_unchanged))
      >> simp [weakCT_refl]
      >> simp [extend_dec_env_def, extend_env_new_decs_def]
      >> fs []
      >> rw [bvl2_to_bvl]
      >> metis_tac [type_v_weakening, weakCT_refl, store_type_extension_weakS, type_env_append]))
  >- ( (* An exception *)
    Cases_on `e'`
    >> fs []
    >- (
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> drule (hd (CONJUNCTS evaluate_state_unchanged))
      >> fs [weakCT_refl, type_all_env_def, good_ctMap_def]
      >> metis_tac [weakCT_refl, type_v_weakening, store_type_extension_weakS])
    >- metis_tac [weakCT_refl]);

val decs_type_sound_invariant_def = Define `
decs_type_sound_invariant mn st env tdecs1 ctMap tenvS tenv ⇔
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap tenvS st.refs ∧
  consistent_decls st.defined_types tdecs1 ∧
  consistent_ctMap tdecs1 ctMap ∧
  mn ∉ IMAGE SOME tdecs1.defined_mods`;

val decs_type_sound = Q.store_thm ("decs_type_sound",
 `∀mn (st:'ffi state) env ds st' new_ctors r tdecs1 ctMap tenvS tenv tdecs1' tenvT' tenvC' tenv'.
   evaluate_decs mn st env ds = (st',new_ctors,r) ∧
   type_ds F mn tdecs1 tenv ds tdecs1' (tenvT',tenvC',tenv') ∧
   decs_type_sound_invariant mn st env tdecs1 ctMap tenvS tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval new_bindings =>
       type_env ctMap' tenvS' new_bindings (bind_var_list2 tenv' Empty) ∧
       MAP FST new_ctors = MAP FST tenvC' ∧
       decs_type_sound_invariant mn st' (extend_dec_env new_bindings new_ctors env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_env_new_decs (tenvT',tenvC',tenv') tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       decs_type_sound_invariant mn st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> rw []
 >> TRY (qpat_assum `type_ds _ _ _ _ _ _ _` mp_tac >> simp [Once type_ds_cases])
 >> rw []
 >- (
   simp [bind_var_list2_def,
         extend_dec_env_def, extend_env_new_decs_def]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl, weakCT_refl])
 >- (
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate_decs _ _ _ _ = (st1, new_ctors1, r1)`
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
     >> fs []
     >> rw []
     >> rename1 `evaluate_decs _ _ (extend_dec_env new_bindings1 _ _) _ = (st2, new_ctors2, r2)`
     >> `?tenvT1 tenvC1 tenv1. new_tenv1 = (tenvT1, tenvC1, tenv1)` by metis_tac [pair_CASES]
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> `?tenvT2 tenvC2 tenv2. new_tenv2 = (tenvT2, tenvC2, tenv2)` by metis_tac [pair_CASES]
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> simp [combine_dec_result_def]
     >> fs [extend_dec_env_append, union_decls_assoc, extend_env_new_decs_append]
     >> fs [append_new_dec_tenv_def]
     >> qexists_tac `ctMap'`
     >> qexists_tac `tenvS'`
     >> rw []
     >- metis_tac [weakCT_trans]
     >- metis_tac [store_type_extension_trans]
     >> Cases_on `r2`
     >> fs []
     >- (
       irule type_env_merge_bvl2
       >> simp []
       >> irule (List.nth (CONJUNCTS type_v_weakening, 1))
       >- fs [decs_type_sound_invariant_def, good_ctMap_def]
       >> qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp [store_type_extension_weakS])
     >- (
       Cases_on `e`
       >> fs []
       >> fs [decs_type_sound_invariant_def, extend_env_new_decs_def,
              type_all_env_def, extend_dec_env_def,
              bind_var_list2_def]
       >> rw []
       >- metis_tac [consistent_con_env_weakening, good_ctMap_def]
       >> irule (List.nth (CONJUNCTS type_v_weakening, 1))
       >- fs [good_ctMap_def]
       >> metis_tac [weakCT_trans, store_type_extension_weakS, store_type_extension_trans]))
   >- (
     rw []
     >> `?tenvT1 tenvC1 tenv1. new_tenv1 = (tenvT1, tenvC1, tenv1)` by metis_tac [pair_CASES]
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> Cases_on `e`
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> rw []
       >> fs [decs_type_sound_invariant_def, extend_env_new_decs_def,
              type_all_env_def, extend_dec_env_def, bind_var_list2_def]
       >> rw []
       >- metis_tac [consistent_decls_weakening, union_decls_assoc, weak_decls_union2, type_ds_mod]
       >- metis_tac [consistent_ctMap_weakening, union_decls_assoc, weak_decls_union2, type_ds_mod]
       >- (
         drule type_ds_mod
         >> fs [union_decls_mods]))
     >- metis_tac []))
 >- (
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (st1, r1)`
   >> drule (hd (CONJUNCTS exp_type_sound))
   >> fs [decs_type_sound_invariant_def]
   >> rpt (disch_then drule)
   >> simp [type_es_list_rel, PULL_EXISTS]
   >> drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> DISCH_TAC
   >> TRY ( (* Only for let poly case *)
     disch_then drule
     >> simp [bind_tvar_def])
   >> TRY ( (* Only for let mono case *)
     disch_then (qspec_then `0` mp_tac)
     >> simp [bind_tvar_def]
     >> disch_then drule)
   >- let_tac
   >- let_tac)
 >- (
   fs [type_d_cases]
   >> fs [])
 >- (
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw []
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> simp [weakCT_refl, store_type_extension_refl, build_rec_env_merge]
   >> fs [decs_type_sound_invariant_def, type_all_env_def]
   >> drule type_recfun_env
   >> rpt (disch_then drule)
   >> strip_tac
   >> drule type_env_merge_lem1
   >> disch_then drule
   >> strip_tac
   >> simp [extend_dec_env_def, extend_env_new_decs_def, bvl2_to_bvl, type_env2_to_type_env])
 >- (
   fs [type_d_cases]
   >> metis_tac [type_funs_distinct])
 >- (
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw [extend_dec_env_def, bind_var_list2_def]
   >> fs [decs_type_sound_invariant_def, union_decls_mods]
   >> qmatch_assum_abbrev_tac `check_ctor_tenv _ new_tabbrev _`
   >> qexists_tac `FUNION (type_decs_to_ctMap mn new_tabbrev tds) ctMap`
   >> qexists_tac `tenvS`
   >> simp [store_type_extension_refl]
   >> simp [Once type_v_cases, GSYM type_defs_to_new_tdecs_def]
   >> drule consistent_ctMap_disjoint
   >> disch_then drule
   >> strip_tac
   >> conj_asm1_tac
   >- metis_tac [disjoint_env_weakCT, disjoint_image]
   >> conj_asm1_tac
   >- (
     simp [build_tdefs_def, build_ctor_tenv_def, REVERSE_FLAT, MAP_MAP_o,
           MAP_FLAT, MAP_REVERSE, combinTheory.o_DEF]
     >> irule (METIS_PROVE [] ``x = y ==> f x = f y``)
     >> irule (METIS_PROVE [] ``x = y ==> f x = f y``)
     >> irule (METIS_PROVE [] ``x = y ==> f x z = f y z``)
     >> simp [FUN_EQ_THM]
     >> strip_tac
     >> pairarg_tac
     >> simp [MAP_MAP_o, combinTheory.o_DEF]
     >> irule (METIS_PROVE [] ``x = y ==> f x z = f y z``)
     >> simp [FUN_EQ_THM]
     >> strip_tac
     >> pairarg_tac
     >> simp [])
   >> conj_asm1_tac
   >- (
     fs [good_ctMap_def]
     >> rw []
     >- (
       irule ctMap_ok_merge_imp
       >> simp []
       >> simp []
       >> fs []
       >> irule ctMap_ok_type_decs
       >- fs [tenv_ok_def, extend_env_new_decs_def, Abbr`new_tabbrev`]
       >> metis_tac [ctMap_ok_type_decs])
     >> TRY (irule still_has_bools)
     >> TRY (irule still_has_exns)
     >> TRY (irule still_has_lists)
     >> simp []
     >> metis_tac [disjoint_image])
   >> conj_tac
   >- (
     fs [type_all_env_def, extend_env_new_decs_def]
     >> conj_tac
     >-  metis_tac [type_v_weakening, good_ctMap_def, weakS_refl]
     >> conj_tac
     >- (
       irule consistent_con_env_merge
       >- metis_tac [consistent_con_env_weakening, good_ctMap_def]
       >> simp [intro_alist_to_fmap]
       >> qspecl_then [`mn`, `tds`] mp_tac consistent_con_env_type_decs
       >> `weakCT (type_decs_to_ctMap mn new_tabbrev tds ⊌ ctMap) (type_decs_to_ctMap mn new_tabbrev tds)`
         by metis_tac [weakCT2]
       >- metis_tac [consistent_con_env_weakening, good_ctMap_def])
     >- (
       simp [bind_var_list2_def]
       >> metis_tac [type_v_weakening, good_ctMap_def, weakS_refl]))
   >> conj_tac
   >- metis_tac [type_s_weakening, good_ctMap_def]
   >> conj_tac
   >- (
     irule consistent_decls_union
     >> simp []
     >> simp [type_defs_to_new_tdecs_def, consistent_decls_def, RES_FORALL]
     >> rw []
     >> CASE_TAC
     >> fs [MEM_MAP]
     >> pairarg_tac
     >> fs []
     >> qexists_tac `(tvs,tn,ctors)`
     >> simp [])
   >- (
     irule consistent_ctMap_union
     >> simp []
     >> simp [type_decs_to_ctMap_def, consistent_ctMap_def, RES_FORALL]
     >> rw []
     >> pairarg_tac
     >> fs [intro_alist_to_fmap, MEM_MAP, MEM_FLAT]
     >> pairarg_tac
     >> fs []
     >> rw []
     >> pairarg_tac
     >> fs [MEM_MAP]
     >> rw []
     >> pairarg_tac
     >> fs []
     >> rw []
     >> qexists_tac `(tvs,tn,ctors)`
     >> rw []))
 >- (
   fs [type_d_cases]
   >> rw []
   >- metis_tac [check_ctor_tenv_dups]
   >- (
     fs [decs_type_sound_invariant_def, consistent_decls_def, RES_FORALL,
         DISJOINT_DEF, EXTENSION]
     >> first_x_assum drule
     >> CASE_TAC
     >> CCONTR_TAC
     >> fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
     >> rw []
     >> fs [type_defs_to_new_tdecs_def, MEM_MAP]
     >> pairarg_tac
     >> fs []
     >> rw []
     >- metis_tac []
     >> fs [METIS_PROVE [] ``x ∨ ¬y ⇔ y ⇒ x``]
     >> first_x_assum drule
     >> rw []
     >> qmatch_abbrev_tac `mn1 = SOME mn2`
     >> Cases_on `mn1`
     >> fs [mk_id_def])
   >- fs [check_ctor_tenv_def, LAMBDA_PROD])
 >- (
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw [extend_dec_env_def, extend_env_new_decs_def]
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> rw [weakCT_refl, store_type_extension_refl, type_env_list_rel]
   >> fs [decs_type_sound_invariant_def, type_all_env_def,
          bind_var_list2_def])
 >- (
   fs [type_d_cases]
   >> rw []
   >> fs [decs_type_sound_invariant_def, consistent_decls_def, RES_FORALL]
   >> first_x_assum drule
   >> simp []
   >> CCONTR_TAC
   >> fs []
   >> Cases_on `mn`
   >> fs [mk_id_def])
 >- (
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw [type_env_list_rel]
   >> fs [decs_type_sound_invariant_def]
   >> qexists_tac `FUNION (FEMPTY |+ ((cn, TypeExn (mk_id mn cn)),([],MAP (type_name_subst tenv.t) ts))) ctMap`
   >> qexists_tac `tenvS`
   >> simp [store_type_extension_refl]
   >> rfs []
   >> conj_asm1_tac
   >- (
     irule disjoint_env_weakCT
     >> simp []
     >> CCONTR_TAC
     >> fs [consistent_ctMap_def, RES_FORALL]
     >> first_x_assum drule
     >> simp [])
   >> conj_asm1_tac
   >- (
     fs [good_ctMap_def]
     >> rw []
     >- (
       irule ctMap_ok_merge_imp
       >> simp []
       >> simp []
       >> fs []
       >> simp [ctMap_ok_def, FEVERY_FUPDATE, FEVERY_FEMPTY, EVERY_MAP]
       >> fs [check_exn_tenv_def, EVERY_MEM]
       >> metis_tac [check_freevars_type_name_subst, tenv_ok_def])
     >> TRY (irule still_has_bools)
     >> TRY (irule still_has_exns)
     >> TRY (irule still_has_lists)
     >> simp []
     >> fs [consistent_ctMap_def, RES_FORALL]
     >> CCONTR_TAC
     >> fs []
     >> first_x_assum drule
     >> pairarg_tac
     >> fs []
     >> rw [])
   >> conj_tac
   >- (
     fs [type_all_env_def, extend_env_new_decs_def, extend_dec_env_def]
     >> conj_tac
     >-  metis_tac [type_v_weakening, good_ctMap_def, weakS_refl]
     >> conj_tac
     >- (
       irule consistent_con_env_merge
       >- metis_tac [consistent_con_env_weakening, good_ctMap_def]
       >> rw [consistent_con_env_def, FLOOKUP_FUNION, FLOOKUP_UPDATE]
       >> rw []
       >> fs [lookup_alist_mod_env_def]
       >> Cases_on `cn'`
       >> fs [id_to_n_def]
       >> rw [])
     >- (
       simp [bind_var_list2_def]
       >> metis_tac [type_v_weakening, good_ctMap_def, weakS_refl]))
   >> conj_tac
   >- metis_tac [type_s_weakening, good_ctMap_def]
   >> conj_tac
   >- (
     irule consistent_decls_union
     >> simp []
     >> simp [consistent_decls_def, RES_FORALL])
   >> conj_tac
   >- (
     irule consistent_ctMap_union
     >> simp []
     >> simp [consistent_ctMap_def, RES_FORALL])
   >- simp [union_decls_def]));

val type_ds_no_dup_types_helper = Q.prove (
`!uniq mn decls tenv ds decls' tenvT' tenvC' tenv'.
  type_ds uniq mn decls tenv ds decls' (tenvT',tenvC',tenv')
  ⇒
  DISJOINT decls.defined_types decls'.defined_types ∧
  decls'.defined_types =
  set (FLAT (MAP (λd.
                case d of
                  Dlet v6 v7 => []
                | Dletrec v8 => []
                | Dtabbrev x y z => []
                | Dtype tds => MAP (λ(tvs,tn,ctors). mk_id mn tn) tds
                | Dexn v10 v11 => []) ds))`,
 induct_on `ds` >>
 srw_tac[][empty_decls_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_ds_cases,EXISTS_PROD]) >>
 full_simp_tac(srw_ss())[empty_decls_def,EXISTS_PROD,extend_env_new_decs_def] >>
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

val type_ds_no_dup_types = Q.prove (
`!uniq mn decls tenv ds decls' tenvT' tenvC' tenv'.
  type_ds uniq mn decls tenv ds decls' (tenvT',tenvC',tenv')
  ⇒
  no_dup_types ds`,
 induct_on `ds` >>
 srw_tac[][no_dup_types_def, decs_to_types_def] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
 full_simp_tac(srw_ss())[EXISTS_PROD,append_new_dec_tenv_def] >>
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
     FIRST_X_ASSUM (qspecl_then [`MAP (mk_id mn o FST o SND) l`] mp_tac) >>
     srw_tac[][]
     >- (qexists_tac `Dtype l` >>
         srw_tac[][LAMBDA_PROD, combinTheory.o_DEF])
     >- (srw_tac[][combinTheory.o_DEF, MEM_MAP, EXISTS_PROD] >>
         srw_tac[][LAMBDA_PROD] >>
         PairCases_on `y` >>
         full_simp_tac(srw_ss())[] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []);

val type_sound_invariant_def = Define `
type_sound_invariant st env tdecs ctMap tenvS tenv ⇔
  ?tdecs_no_sig tenvM_no_sig tenvC_no_sig.
    decls_ok tdecs_no_sig ∧
    tenv_ok tenv ∧
    good_ctMap ctMap ∧
    tenv_mod_ok tenvM_no_sig ∧
    tenv_ctor_ok tenvC_no_sig ∧
    weakM tenvM_no_sig tenv.m ∧
    weakC tenvC_no_sig tenv.c ∧
    type_all_env ctMap tenvS env (tenv with <| m := tenvM_no_sig; c := tenvC_no_sig |>) ∧
    type_s ctMap tenvS st.refs ∧
    weak_decls tdecs_no_sig tdecs ∧
    weak_decls_only_mods tdecs_no_sig tdecs ∧
    consistent_decls st.defined_types tdecs_no_sig ∧
    consistent_ctMap tdecs_no_sig ctMap ∧
    st.defined_mods ⊆ tdecs_no_sig.defined_mods`;

val tops_type_sound_no_extra_checks = Q.store_thm ("tops_type_sound_no_no_extra_checks",
 `∀(st:'ffi state) env tops st' new_ctors r tdecs1 ctMap tenvS tenv tdecs1' new_tenv.
   evaluate_tops st env tops = (st',new_ctors,r) ∧
   type_prog F tdecs1 tenv tops tdecs1' new_tenv ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval (new_mods, new_vals) =>
       type_sound_invariant st' (extend_top_env new_mods new_vals new_ctors env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_env_new_tops new_tenv tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   rw [extend_top_env_def, extend_env_new_tops_def, bind_var_list2_def]
   >> metis_tac [weakCT_refl, store_type_extension_refl])
 >- (
   qpat_assum `type_prog F _ _ (_::_::_) _ _` mp_tac
   >> simp [Once type_prog_cases]
   >> rw []
   >> split_pair_case_tac
   >> rename1 `evaluate_tops st env [top1] = (st1, new_ctors1, r1)`
   >> fs []
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
     >> fs []
     >> split_pair_case_tac
     >> fs []
     >> rw []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> rename1 `weakCT ctMap1 ctMap`
     >> rename1 `store_type_extension tenvS tenvS1`
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> rename1 `weakCT ctMap2 ctMap1`
     >> rename1 `store_type_extension tenvS1 tenvS2`
     >> rename1 `evaluate_tops _ _ (_::_) = (st2, new_ctors2, r2)`
     >> Cases_on `r2`
     >> fs []
     >- (
       split_pair_case_tac
       >> fs []
       >> qexists_tac `ctMap2`
       >> qexists_tac `tenvS2`
       >> rw []
       >- metis_tac [weakCT_trans]
       >- metis_tac [store_type_extension_trans]
       >> simp [combine_mod_result_def]
       >> fs [extend_top_env_def, merge_alist_mod_env_assoc, union_decls_assoc,
              extend_env_new_tops_append])
     >- (
       simp [combine_mod_result_def]
       >> CASE_TAC
       >> fs []
       >- (
         qexists_tac `ctMap2`
         >> qexists_tac `tenvS2`
         >> rw []
         >- metis_tac [weakCT_trans]
         >- metis_tac [store_type_extension_trans]
         >> fs [type_sound_invariant_def, type_all_env_def]
         >> qexists_tac `tdecs_no_sig''`
         >> qexists_tac `tenvM_no_sig`
         >> qexists_tac `tenvC_no_sig`
         >> rw []
         >- metis_tac [type_v_weakening, weakCT_trans, store_type_extension_trans,
                       store_type_extension_weakS, good_ctMap_def]
         >- metis_tac [consistent_con_env_weakening, weakCT_trans, store_type_extension_trans,
                       store_type_extension_weakS, good_ctMap_def]
         >- metis_tac [type_v_weakening, weakCT_trans, store_type_extension_trans,
                       store_type_extension_weakS, good_ctMap_def]
         >- metis_tac [consistent_decls_weakening, union_decls_assoc]
         >- metis_tac [consistent_decls_weakening, union_decls_assoc])
       >- metis_tac []))
   >- (
     first_x_assum drule
     >> disch_then drule
     >> rw []
     >> CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> fs [type_sound_invariant_def, GSYM union_decls_assoc, union_decls_mods, SUBSET_DEF]
       >> qexists_tac `union_decls decls'' tdecs_no_sig'`
       >> qexists_tac `tenvM_no_sig'`
       >> qexists_tac `tenvC_no_sig'`
       >> rw [union_decls_mods]
       >- metis_tac [decls_ok_union, type_prog_decls_ok]
       >> metis_tac [weak_decls_union, weak_decls_only_mods_union,
                     consistent_ctMap_union2, consistent_decls_union2])
     >- metis_tac []))
 >- (
   fs [type_top_cases]
   >> split_pair_case_tac
   >> rename1 `evaluate_decs _ _ _ [_] = (st1, new_ctors1, r1)`
   >> fs []
   >> drule decs_type_sound
   >> `∃new_tenvT new_tenvC new_tenvV. new_tenv' = (new_tenvT, new_tenvC, new_tenvV)`
     by metis_tac [pair_CASES]
   >> fs [type_sound_invariant_def]
   >> `type_d F NONE tdecs_no_sig (tenv with <|m := tenvM_no_sig; c := tenvC_no_sig|>) d tdecs1' (new_tenvT,new_tenvC,new_tenvV)`
     by (
       irule type_d_weakening
       >- fs [tenv_ctor_ok_def]
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw [weakC_refl]
       >> metis_tac [weakM_refl, tenv_ok_def, weak_decls_other_mods_only_mods_NONE])
   >> disch_then drule
   >> `decs_type_sound_invariant NONE st env tdecs_no_sig ctMap tenvS (tenv with <|m := tenvM_no_sig; c := tenvC_no_sig|>)`
     by fs [decs_type_sound_invariant_def, tenv_ok_def]
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> rw []
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def, type_all_env_def,
            extend_env_new_tops_def, lift_new_dec_tenv_def]
     >> rw []
     >> fs [extend_env_new_decs_def, FEVERY_FEMPTY, extend_top_env_def,
            extend_dec_env_def,union_decls_mods, SUBSET_DEF]
     >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
     >> qexists_tac `tenvM_no_sig`
     >> qexists_tac `merge_alist_mod_env ([],new_tenvC) tenvC_no_sig`
     >> rw [union_decls_mods]
     >- metis_tac [decls_ok_union2, type_d_mod]
     >- fs [tenv_ok_def, tenv_ctor_ok_merge]
     >- fs [tenv_ok_def, tenv_ctor_ok_merge]
     >> metis_tac [weakC_merge, weak_decls_union, weak_decls_only_mods_union,evaluate_decs_state_unchanged])
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> fs [type_sound_invariant_def, decs_type_sound_invariant_def,
              union_decls_mods, SUBSET_DEF]
       >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
       >> qexists_tac `tenvM_no_sig`
       >> qexists_tac `tenvC_no_sig`
       >> rw [union_decls_mods]
       >- metis_tac [decls_ok_union2, type_d_mod]
       >> metis_tac [weak_decls_union, weak_decls_only_mods_union, evaluate_decs_state_unchanged])
     >- metis_tac []))
 >- (
   split_pair_case_tac
   >> rename1 `evaluate_decs _ _ _ _ = (st1, new_ctors1, r1)`
   >> drule type_top_decls_ok
   >> fs [type_top_cases]
   >> rw []
   >> drule decs_type_sound
   >> `∃new_tenvT new_tenvC new_tenvV. new_tenv1 = (new_tenvT, new_tenvC, new_tenvV)`
     by metis_tac [pair_CASES]
   >> fs [type_sound_invariant_def]
   >> `type_ds F (SOME mn) tdecs_no_sig (tenv with <|m := tenvM_no_sig; c := tenvC_no_sig|>) ds decls' (new_tenvT,new_tenvC,new_tenvV)`
     by (
       irule type_ds_weakening
       >- fs [tenv_ok_def]
       >- fs [tenv_ok_def]
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw [weakC_refl]
       >- metis_tac [tenv_ok_def]
       >- metis_tac [weak_decls_other_mods_only_mods_SOME])
   >> disch_then drule
   >> `decs_type_sound_invariant (SOME mn) st env tdecs_no_sig ctMap tenvS (tenv with <|m := tenvM_no_sig; c := tenvC_no_sig|>)`
     by (fs [decs_type_sound_invariant_def, type_sound_invariant_def,
             weak_decls_def,tenv_ok_def])
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> rw []
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def]
     >> `?new_tenvT2 new_tenvC2 new_tenvV2. new_tenv2 = (new_tenvT2,new_tenvC2,new_tenvV2)`
       by metis_tac [pair_CASES]
     >> simp [mod_lift_new_dec_tenv_def, extend_env_new_tops_def]
     >> qexists_tac `union_decls (union_decls <|defined_mods := {mn}; defined_types := ∅; defined_exns := ∅ |> decls') tdecs_no_sig`
     >> qexists_tac `tenvM_no_sig |+ (mn,new_tenvV)`
     >> qexists_tac `merge_alist_mod_env ([(mn,new_tenvC)],[]) tenvC_no_sig`
     >> simp [union_decls_mods]
     >> conj_tac
     >- metis_tac [type_ds_decls_ok, decls_ok_union]
     >> conj_asm1_tac
     >- (
       rw []
       >> drule check_signature_tenv_ok
       >> simp [tenv_ok_def, mod_lift_new_dec_tenv_def, extend_env_new_tops_def]
       >> disch_then irule
       >> fs [type_all_env_def]
       >> metis_tac [type_v_freevars, tenv_ok_def])
     >> rw []
     >- (
       irule tenv_mod_ok_pres
       >> simp []
       >> metis_tac [type_v_freevars, tenv_ok_def])
     >- (
       simp [tenv_ctor_ok_merge]
       >> drule type_ds_tenv_ok_helper
       >> simp [tenv_ctor_ok_def, flat_tenv_ctor_ok_def])
     >- (
       rw [GSYM FUPDATE_EQ_FUNION]
       >> irule weakM_bind'
       >> simp []
       >> fs [check_signature_cases]
       >- (
         irule weakE_refl
         >> metis_tac [type_v_freevars, tenv_ok_def])
       >- fs [weak_new_dec_tenv_def])
     >- (
       irule weakC_merge_one_mod2
       >> simp []
       >> fs [check_signature_cases, flat_weakC_refl, weak_new_dec_tenv_def])
     >- (
       qpat_assum `type_all_env _ _ _ _` mp_tac
       >> simp [type_all_env_def, extend_top_env_def, bind_var_list2_def]
       >> rw [GSYM FUPDATE_EQ_FUNION, extend_dec_env_def, extend_env_new_decs_def]
       >- (
         simp [Once type_v_cases]
         >> qexists_tac `new_tenvV`
         >> qexists_tac `tenvM_no_sig`
         >> rw []
         >> fs [check_signature_cases])
       >- (
         irule consistent_con_env_to_mod
         >> simp []
         >- (
           simp [tenv_ctor_ok_merge]
           >> drule type_ds_tenv_ok_helper
           >> simp [tenv_ctor_ok_def, flat_tenv_ctor_ok_def])
         >> fs [type_all_env_def]
         >> metis_tac [consistent_con_env_weakening, good_ctMap_def])
       >- (
         fs [type_all_env_def]
         >> metis_tac [type_v_weakening, good_ctMap_def, store_type_extension_weakS]))
     >- (
       fs [check_signature_cases]
       >> metis_tac [weak_decls_union, union_decls_sym, weak_decls_refl, weak_decls_trans])
     >- (
       fs [check_signature_cases]
       >- metis_tac [weak_decls_only_mods_union]
       >> simp [GSYM union_decls_assoc]
       >> irule weak_decls_only_mods_union
       >> irule weak_decls_only_mods_union2
       >> simp []
       >- metis_tac [type_ds_weak_decls_only_mods])
     >- metis_tac [consistent_decls_union2, union_decls_assoc]
     >- metis_tac [consistent_ctMap_union2, union_decls_assoc]
     >- (
       fs [SUBSET_DEF]
       >> metis_tac [evaluate_decs_state_unchanged]))
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> fs [type_sound_invariant_def, decs_type_sound_invariant_def]
       >> qexists_tac `union_decls (union_decls <|defined_mods := {mn}; defined_types := ∅; defined_exns := ∅ |> decls') tdecs_no_sig`
       >> qexists_tac `tenvM_no_sig`
       >> qexists_tac `tenvC_no_sig`
       >> simp [union_decls_mods]
       >> rw []
       >- metis_tac [type_ds_decls_ok, decls_ok_union]
       >- (
         fs [check_signature_cases]
         >> metis_tac [weak_decls_union, union_decls_sym, weak_decls_refl, weak_decls_trans])
       >- (
         fs [check_signature_cases]
         >- metis_tac [weak_decls_only_mods_union]
         >> simp [GSYM union_decls_assoc]
         >> irule weak_decls_only_mods_union
         >> irule weak_decls_only_mods_union2
         >> simp []
         >- metis_tac [type_ds_weak_decls_only_mods])
       >- metis_tac [consistent_decls_union2, union_decls_assoc]
       >- metis_tac [consistent_ctMap_union2, union_decls_assoc]
       >- (
         fs [SUBSET_DEF]
         >> metis_tac [evaluate_decs_state_unchanged]))
     >- metis_tac []))
 >- (
   fs [type_top_cases]
   >- (
     fs [type_sound_invariant_def, SUBSET_DEF]
     >> metis_tac [weak_decls_def])
   >- metis_tac [type_ds_no_dup_types, pair_CASES]));

val tops_type_sound = Q.store_thm ("tops_type_sound",
 `∀(st:'ffi state) env tops st' new_ctors r checks tdecs1 ctMap tenvS tenv tdecs1' new_tenv.
   evaluate_tops st env tops = (st',new_ctors,r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' new_tenv ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval (new_mods, new_vals) =>
       type_sound_invariant st' (extend_top_env new_mods new_vals new_ctors env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_env_new_tops new_tenv tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 rpt strip_tac
 >> irule tops_type_sound_no_extra_checks
 >> qexists_tac `st`
 >> qexists_tac `tops`
 >> rw []
 >> irule type_prog_check_uniq
 >> metis_tac []);

val prog_type_sound = Q.store_thm ("prog_type_sound",
 `∀(st:'ffi state) env tops st' new_ctors r checks tdecs1 ctMap tenvS tenv tdecs1' new_tenv.
   evaluate_prog st env tops = (st',new_ctors,r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' new_tenv ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval (new_mods, new_vals) =>
       type_sound_invariant st' (extend_top_env new_mods new_vals new_ctors env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_env_new_tops new_tenv tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 REWRITE_TAC [evaluate_prog_def]
 >> rpt strip_tac
 >> irule tops_type_sound
 >> fs []
 >> qexists_tac `checks`
 >> qexists_tac `st`
 >> qexists_tac `tops`
 >> rw []
 >> every_case_tac
 >> fs []
 >- (
   PairCases_on `new_tenv`
   >> drule type_no_dup_mods
   >> fs [type_sound_invariant_def, no_dup_mods_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def])
 >- (
   PairCases_on `new_tenv`
   >> drule type_no_dup_top_types
   >> fs [type_sound_invariant_def]
   >> rpt (disch_then drule)
   >> fs [no_dup_top_types_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def]));

val prim_type_sound_invariants = Q.store_thm("prim_type_sound_invariants",
  `(sem_st,sem_env) = THE (prim_sem_env ffi) ⇒
   ?ctMap. type_sound_invariant sem_st sem_env prim_tdecs ctMap FEMPTY prim_tenv`,
  rw[type_sound_invariant_def,
     initSemEnvTheory.prim_sem_env_eq,initSemEnvTheory.prim_tdecs_def,initSemEnvTheory.prim_tenv_def]
  \\ EVAL_TAC \\ simp[]
  \\ simp[RES_FORALL]
  \\ srw_tac[DNF_ss][]
  \\ simp[FEVERY_ALL_FLOOKUP,
          tenv_tabbrev_ok_def,
          flat_tenv_tabbrev_ok_def]
  \\ qexists_tac`FEMPTY |++ [
      (("Bind",TypeExn (Short "Bind")) , ([],[]));
      (("Chr",TypeExn (Short "Chr")) , ([],[]));
      (("Div",TypeExn (Short "Div")) , ([],[]));
      (("Subscript",TypeExn (Short "Subscript")) , ([],[]));
      (("nil",TypeId (Short "list")) , (["'a"],[]));
      (("::",TypeId (Short "list")) , (["'a"],[Tvar "'a"; Tapp [Tvar "'a"] (TC_name (Short "list"))]));
      (("true",TypeId (Short "bool")) , ([],[]));
      (("false",TypeId (Short "bool")) , ([],[]));
      (("SOME",TypeId (Short "option")), (["'a"],[Tvar "'a"]));
      (("NONE",TypeId (Short "option")), (["'a"],[]))]`
  \\ EVAL_TAC \\ simp[]
  \\ srw_tac[DNF_ss][]
  \\ simp[Once type_v_cases]
  \\ simp[Once type_v_cases]
  \\ qexists_tac`prim_tdecs`
  \\ simp[initSemEnvTheory.prim_tdecs_def]
  \\ qexists_tac`([],[
       ("false",[],[],TypeId(Short"bool"));
       ("true",[],[],TypeId(Short"bool"));
       ("::",["'a"],[Tvar "'a"; Tapp [Tvar "'a"] (TC_name (Short "list"))],TypeId(Short "list"));
       ("nil",["'a"],[],TypeId(Short "list"));
       ("Subscript",[],[],TypeExn (Short "Subscript"));
       ("Div",[],[],TypeExn (Short "Div"));
       ("Chr",[],[],TypeExn (Short "Chr"));
       ("Bind",[],[],TypeExn (Short "Bind"));
       ("NONE",["'a"],[],TypeId (Short "option"));
       ("SOME",["'a"],[Tvar "'a"],TypeId (Short "option"))])`
  \\ rw[UNCURRY]
  \\ EVAL_TAC \\ rw[]
  \\ TRY (
    qmatch_abbrev_tac`_ ≠ SOME _`
    \\ BasicProvers.TOP_CASE_TAC
    \\ rw[] \\ fs[])
  \\ rw[SUBSET_DEF] \\ fs[GSPECIFICATION]
  \\ Cases_on`cn` \\ fs[] \\ EVAL_TAC \\ rw[]);

val _ = export_theory ();
