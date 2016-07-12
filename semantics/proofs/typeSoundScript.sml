open preamble;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory funBigStepTheory;
open terminationTheory;
open evalPropsTheory;
open weakeningTheory typeSysPropsTheory typeSoundInvariantsTheory;
open evalPropsTheory;

val _ = new_theory "typeSound";

val EVERY_LIST_REL = Q.prove (
`EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y)`,
 induct_on `l` >>
 srw_tac[][REPLICATE]);

val list_rel_split = Q.prove (
`!r l1 x l2.
  LIST_REL r (l1 ++ [x]) l2 =
  ?y l2'. l2 = l2'++[y] ∧ LIST_REL r l1 l2' ∧ r x y`,
 Induct_on `l1` >>
 srw_tac[][] >>
 eq_tac >>
 srw_tac[][] >>
 res_tac >>
 srw_tac[][]);

val union_decls_empty = Q.store_thm ("union_decls_empty",
`!decls. union_decls empty_decls decls = decls`,
 srw_tac[][] >>
 srw_tac[][union_decls_def, empty_decls_def, decls_component_equality]);

val union_decls_assoc = Q.store_thm ("union_decls_assoc",
`!decls1 decls2 decls3.
  union_decls decls1 (union_decls decls2 decls3)
  =
  union_decls (union_decls decls1 decls2) decls3`,
 srw_tac[][] >>
 srw_tac[][union_decls_def] >>
 metis_tac [UNION_ASSOC]);

val type_v_cases_eqn = SIMP_RULE (srw_ss()) [] (List.nth (CONJUNCTS type_v_cases, 0));
val type_vs_cases_eqn = SIMP_RULE (srw_ss()) [] (List.nth (CONJUNCTS type_v_cases, 1));
val type_env_cases = SIMP_RULE (srw_ss()) [] (List.nth (CONJUNCTS type_v_cases, 2));
val consistent_mod_cases = SIMP_RULE (srw_ss()) [] (List.nth (CONJUNCTS type_v_cases, 3));

val tid_exn_not = Q.prove (
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
 ntac 3 (full_simp_tac(srw_ss())[Once type_vs_cases_eqn]) >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][v_to_list_def,v_to_char_list_def] >>
 full_simp_tac(srw_ss())[type_subst_def] >>
 LAST_X_ASSUM (mp_tac o Q.SPEC `v'`) >>
 srw_tac[][v_size_def, basicSizeTheory.option_size_def, basicSizeTheory.pair_size_def,
     id_size_def, list_size_def, tid_or_exn_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 res_tac >> srw_tac[][] >>
 full_simp_tac(srw_ss())[flookup_fupdate_list] >> srw_tac[][] >> full_simp_tac(srw_ss())[GSYM Tchar_def] >>
 qpat_assum`type_v X Y Z v Tchar`mp_tac >>
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
 full_simp_tac(srw_ss())[Once type_v_cases, deBruijn_subst_def, type_vs_list_rel] >>
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
   imp_res_tac type_vs_length >>
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
 srw_tac[][Once type_v_cases_eqn, tid_exn_to_tc_def, type_vs_list_rel] >>
 metis_tac [Tchar_def]);

val eq_same_type = Q.prove (
`(!v1 v2 tvs ctMap cns tenvS t.
  type_v tvs ctMap tenvS v1 t ∧
  type_v tvs ctMap tenvS v2 t
  ⇒
  do_eq v1 v2 ≠ Eq_type_error) ∧
(!vs1 vs2 tvs ctMap cns tenvS ts.
  type_vs tvs ctMap tenvS vs1 ts ∧
  type_vs tvs ctMap tenvS vs2 ts
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
 full_simp_tac(srw_ss())[lit_same_type_def,ctor_same_type_def]
 >- (full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
     full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >> TRY ( full_simp_tac(srw_ss())[tid_exn_to_tc_11,same_tid_sym] >> NO_TAC)
 >> TRY (rpt (qpat_assum `type_v x0 x1 x2 x3 x4` mp_tac) >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[combinTheory.o_DEF, type_vs_list_rel, EVERY_LIST_REL] >>
     `(\x y. type_v tvs ctMap tenvS x y) = type_v tvs ctMap tenvS` by metis_tac [] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac []) >>
 full_simp_tac(srw_ss())[Once type_vs_cases_eqn] >>
 full_simp_tac(srw_ss())[tid_exn_not] >>
 srw_tac[][]
 >- (cases_on `do_eq v1 v2` >>
     full_simp_tac(srw_ss())[]
     >- (cases_on `b` >>
         full_simp_tac(srw_ss())[] >>
         qpat_assum `!x. P x` (mp_tac o Q.SPECL [`tvs`, `ctMap`, `tenvS`, `ts'`]) >>
         srw_tac[][METIS_PROVE [] ``(a ∨ b) = (~a ⇒ b)``] >>
         cases_on `vs1` >>
         full_simp_tac(srw_ss())[] >-
         full_simp_tac(srw_ss())[Once type_vs_cases_eqn] >>
         cases_on `ts'` >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[Once type_vs_cases_eqn])
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
  tenv_mod_ok tenv.m ∧
  tenv_tabbrev_ok tenv.t ∧
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
      metis_tac [FST, pair_CASES,ALOOKUP_MEM,MEM_MAP]]);

val type_recfun_env = Q.prove (
`∀funs ctMap tenvS tvs tenv tenv0 env bindings.
  tenv_mod_ok tenv.m ∧
  tenv_tabbrev_ok tenv.t ∧
  consistent_con_env ctMap env.c tenv.c ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  type_env ctMap tenvS env.v tenv0 ∧
  type_funs (tenv with v := bind_var_list 0 bindings (bind_tvar tvs tenv0)) funs bindings ∧
  ALL_DISTINCT (MAP (\(x,y,z). x) funs)
  ⇒
  type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs) bindings`,
metis_tac [type_recfun_env_help]);

val type_raise_eqn = Q.prove (
`!tenv r t.
  type_e tenv (Raise r) t = (type_e tenv r Texn ∧ check_freevars (num_tvs tenv.v) [] t)`,
srw_tac[][Once type_e_cases] >>
metis_tac []);

val type_env_eqn = Q.prove (
`!ctMap tenvS.
  (type_env ctMap tenvS [] Empty = T) ∧
  (!n tvs t v env tenv.
      type_env ctMap tenvS ((n,v) :: env) (Bind_name n tvs t tenv) =
      (type_v tvs ctMap tenvS v t ∧ check_freevars tvs [] t ∧ type_env ctMap tenvS env tenv))`,
srw_tac[][] >>
srw_tac[][Once type_v_cases] >>
full_simp_tac(srw_ss())[] >>
metis_tac [type_v_freevars]);

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

val exn_tenvC_def = Define `
exn_tenvC = ([],MAP (λcn. (cn,[],[],TypeExn (Short cn))) ["Bind"; "Div"])`;

val do_app_exn_tac =
 srw_tac[][Once context_invariant_cases, Once type_ctxts_cases, type_ctxt_cases] >>
 disj1_tac >>
 SIMP_TAC (srw_ss()++boolSimps.DNF_ss) [prim_exn_def] >>
 metis_tac [type_v_exn];

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
 ntac 4 (full_simp_tac(srw_ss())[Once type_vs_cases_eqn]) >>
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
    simp[Once type_v_cases,GSYM Tchar_def,type_subst_def,flookup_fupdate_list] >>
    simp[Once type_v_cases])

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
 ntac 4 (full_simp_tac(srw_ss())[Once type_vs_cases_eqn]) >>
 srw_tac[][Once type_v_cases_eqn]);

val type_v_Boolv = Q.prove(
  `ctMap_has_bools ctMap ⇒
    type_v tvs ctMap tenvS (Boolv b) (Tapp [] (TC_name (Short "bool")))`,
  srw_tac[][Boolv_def] >>
  srw_tac[][Once type_v_cases_eqn,tid_exn_to_tc_def,LENGTH_NIL] >>
  full_simp_tac(srw_ss())[ctMap_has_bools_def] >>
  srw_tac[][Once type_v_cases]);

val type_env_merge_imp = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  type_env2 tenvC tenvS tvs env' tenv' ∧
  type_env tenvC tenvS env tenv ⇒
  type_env tenvC tenvS (env' ++ env) (bind_var_list tvs tenv' tenv)`,
 metis_tac [type_env_merge]);

val v_unchanged = Q.prove (
`!tenv x. tenv with v := tenv.v = tenv`,
 srw_tac[][type_environment_component_equality]);

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

val type_pes_def = Define `
  type_pes tvs tenv pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e (tenv with v := bind_var_list tvs bindings tenv.v) e t2)`;

val opapp_lemma = Q.prove (
`!ctMap tenvS vs ts t.
 type_op Opapp ts t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs ts
 ⇒
 ?env e tenv.
   tenv_tabbrev_ok tenv.t ∧
   tenv_mod_ok tenv.m ∧
   consistent_mod_env tenvS ctMap env.m tenv.m ∧
   consistent_con_env ctMap env.c tenv.c ∧
   type_env ctMap tenvS env.v tenv.v ∧
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
   >> simp [Once type_v_cases, build_rec_env_merge, bind_tvar_def]
   >> metis_tac [type_env_merge]));

val store_assign_lemma = Q.prove (
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

val store_alloc_lemma = Q.prove (
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

val store_lookup_lemma = Q.prove (
 `!ctMap tenvS store n st.
  type_s ctMap tenvS store ∧
  FLOOKUP tenvS n = SOME st
  ⇒
  ?sv.
    store_lookup n store = SOME sv ∧
    type_sv ctMap tenvS sv st`,
 rw [type_s_def]
 >> metis_tac []);

val op_lemma = Q.prove (
`!ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
 ctMap_ok ctMap ∧
 ctMap_has_exns ctMap ∧
 ctMap_has_lists ctMap ∧
 ctMap_has_bools ctMap ∧
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
 rw [type_op_cases]
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
   simp [Once type_v_cases, type_vs_list_rel]
   >> qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> metis_tac [type_sv_def, store_type_extension_refl, store_assign_lemma])
 >- ( (* rev alloc *)
   simp [Once type_v_cases]
   >> rename1 `type_v _ _ _ v t`
   >> `type_sv ctMap tenvS (Refv v) (Ref_t t)` by rw [type_sv_def]
   >> drule store_alloc_lemma
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [type_v_freevars])
 >- ( (* deref *)
   qpat_assum `type_v _ _ _ (Loc n) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_lemma
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
   >> drule store_alloc_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_assign_lemma
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases, type_vs_list_rel]
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
   >> drule store_alloc_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_lookup_lemma
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
   >> drule store_assign_lemma
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases, type_vs_list_rel]
   >> metis_tac [store_type_extension_refl])
 >- ( (* FFI call *)
   qpat_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_lemma
   >> disch_then drule
   >> rw []
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> `?ffi' ws'. call_FFI ffi n l = (ffi', ws')` by metis_tac [pair_CASES]
   >> simp []
   >> `type_sv ctMap tenvS (W8array ws') W8array_t` by rw [type_sv_def]
   >> drule store_assign_lemma
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases, type_vs_list_rel]
   >> metis_tac [store_type_extension_refl]));

val build_conv_lemma = Q.prove (
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
 >> simp [Once type_v_cases, type_vs_list_rel, GSYM EVERY2_REVERSE1]
 >> simp [GSYM FUNION_alist_to_fmap]
 >> rfs [bind_tvar_def, num_tvs_def]
 >> Cases_on `tvs`
 >> rfs [num_tvs_def]);

val evaluate_length = Q.store_thm ("evaluate_length",
 `(!(s:'ffi state) env es s' vs.
   evaluate s env es = (s', Rval vs)
   ⇒
   LENGTH es = LENGTH vs) ∧
  (!(s:'ffi state) env v pes err_v s' vs.
   evaluate_match s env v pes err_v = (s', Rval vs)
   ⇒
   LENGTH vs = 1)`,
 ho_match_mp_tac evaluate_ind
 >> simp [evaluate_def]
 >> rw []
 >> TRY split_pair_case_tac
 >> fs []
 >> every_case_tac
 >> fs []
 >> rw []
 >> Cases_on `r`
 >> fs [list_result_def]
 >> rw []);

val sing_list = Q.prove (
`!l. LENGTH l = 1 ⇔ ?x. l = [x]`,
 Cases
 >> rw []
 >> Cases_on `t`
 >> rw []);

val pat_sound_tac =
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[deBruijn_subst_def, tid_exn_not] >>
 imp_res_tac type_funs_Tfn >>
 full_simp_tac(srw_ss())[Tchar_def]
 >> fs [tid_exn_not]

val pat_type_soundness = Q.store_thm ("pat_type_soundness",
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
   type_vs tvs ctMap tenvS vs ts ∧
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
   simp [Once type_v_cases, Once type_p_cases, type_vs_list_rel]
   >> CCONTR_TAC
   >> fs []
   >> rw []
   >> metis_tac [type_ps_length, LIST_REL_LENGTH])
 >- (
   qpat_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_lemma
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
   fs [type_vs_list_rel]
   >> rw []
   >> fs [Once type_p_cases]
   >> rw [bind_var_list_def])
 >- (
   fs [type_vs_list_rel]
   >> rw []
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

val exp_type_soundness = Q.store_thm ("exp_type_soundness",
 `(!(s:'ffi state) env es r s' tenv ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_tabbrev_ok tenv.t ∧
    tenv_mod_ok tenv.m ∧
    ctMap_ok ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap ∧
    ctMap_has_bools ctMap ∧
    consistent_mod_env tenvS ctMap env.m tenv.m ∧
    consistent_con_env ctMap env.c tenv.c ∧
    type_env ctMap tenvS env.v tenv.v ∧
    type_s ctMap tenvS s.refs ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es (tenv with v := bind_tvar tvs tenv.v) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap tenvS' s'.refs ∧
      store_type_extension tenvS tenvS' ∧
      case r of
         | Rval vs => type_vs tvs ctMap tenvS' vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi state) env v pes err_v r s' tenv t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_tabbrev_ok tenv.t ∧
    tenv_mod_ok tenv.m ∧
    ctMap_ok ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap ∧
    ctMap_has_bools ctMap ∧
    consistent_mod_env tenvS ctMap env.m tenv.m ∧
    consistent_con_env ctMap env.c tenv.c ∧
    type_env ctMap tenvS env.v tenv.v ∧
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
 >> simp [evaluate_def, type_es_list_rel, type_vs_list_rel]
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
     >> fs [bind_tvar_def, v_unchanged]
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
     >> drule build_conv_lemma
     >> rpt (disch_then drule)
     >> rw []
     >> fs []
     >> rw []
     >> metis_tac [])
   >- metis_tac []
   >- (
     fs [build_conv_def]
     >> rw []
     >> simp [Once type_v_cases, type_vs_list_rel, GSYM EVERY2_REVERSE1]
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
       drule opapp_lemma
       >> fs [EVERY2_REVERSE1]
       >> disch_then drule
       >> rw []
       >> fs []
       >> Cases_on `s1.clock = 0`
       >> fs []
       >> rw []
       >- metis_tac []
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [dec_clock_def, PULL_EXISTS]
       >> rename1 `type_e tenv' e t`
       >> disch_then (qspecl_then [`0`, `t`] mp_tac)
       >> simp [bind_tvar_def, v_unchanged]
       >> rw []
       >> metis_tac [store_type_extension_trans])
     >- (
       fs [bind_tvar_def, v_unchanged]
       >> drule op_lemma
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
   >> rfs [is_value_def, bind_tvar_def, v_unchanged]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `(Tapp [] (TC_name (Short "bool")))`] mp_tac)
   >> simp [v_unchanged]
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
       >> simp [v_unchanged]
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
       >> simp [v_unchanged]
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
   >> rfs [is_value_def, bind_tvar_def, v_unchanged]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `(Tapp [] (TC_name (Short "bool")))`] mp_tac)
   >> simp [v_unchanged]
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
     >> simp [v_unchanged]
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
     >> fs [bind_tvar_def, v_unchanged]
     >> metis_tac [store_type_extension_trans, type_v_freevars])
   >- metis_tac [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def, v_unchanged]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`] mp_tac)
   >> simp [v_unchanged]
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     rename1 `type_e (tenv with v := opt_bind_name n 0 t1 tenv.v) e2 t2`
     >> qabbrev_tac `env' = opt_bind n (HD [x]) env.v`
     >> qabbrev_tac `tenv' = tenv with v := opt_bind_name n 0 t1 tenv.v`
     >> `tenv_tabbrev_ok tenv'.t`
       by (rw [tenv_tabbrev_ok_def, Abbr `tenv'`] >> NO_TAC)
     >> `tenv_mod_ok tenv'.m`
       by (fs [tenv_mod_ok_def, Abbr `tenv'`] >> NO_TAC)
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
     >> simp [v_unchanged]
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
   >> rfs [build_rec_env_merge, bind_tvar_def]
   >> metis_tac [type_env_merge_lem1, type_recfun_env, bind_tvar_def])
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
   >> rfs [is_value_def, v_unchanged, bind_tvar_def]
   >> fs [PULL_EXISTS]
   >> first_x_assum irule
   >> rw [v_unchanged]
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
   >> drule (hd (CONJUNCTS pat_type_soundness))
   >> rpt (disch_then drule)
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> metis_tac [])
   >- (
     `tenv_tabbrev_ok (tenv with v := bind_var_list tvs bindings tenv.v).t`
       by rw []
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

val mem_lem = Q.prove (
`(!v. ~MEM (x,v) l) ⇔ ~MEM x (MAP FST l)`,
 simp[FORALL_PROD, MEM_MAP]);

val decs_type_sound_invariant_def = Define `
decs_type_sound_invariant mn tdecs1 ctMap tenvS tenv st env ⇔
  tenv_tabbrev_ok tenv.t ∧
  tenv_mod_ok tenv.m ∧
  ctMap_ok ctMap ∧
  ctMap_has_exns ctMap ∧
  ctMap_has_lists ctMap ∧
  ctMap_has_bools ctMap ∧
  consistent_con_env ctMap env.c tenv.c ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  type_env ctMap tenvS env.v tenv.v ∧
  type_s ctMap tenvS st.refs ∧
  consistent_decls st.defined_types tdecs1 ∧
  consistent_ctMap tdecs1 ctMap ∧
  mn ∉ IMAGE SOME tdecs1.defined_mods`;

val define_types_lem = Q.prove (
`!x y.
  <| defined_mods := x.defined_mods; defined_types := y; defined_exns := x.defined_exns |>
  =
  (x with defined_types := y)`,
 srw_tac[][decls_component_equality]);

val define_exns_lem = Q.prove (
`!x y.
  <| defined_mods := x.defined_mods; defined_types := x.defined_types; defined_exns := y |>
  =
  (x with defined_exns := y)`,
 srw_tac[][decls_component_equality]);

val dec_type_soundness = Q.store_thm ("dec_type_soundness",
`!mn tenv d tenvT' tenvC' tenv' tenvS env st tdecs1 tdecs1' ctMap.
  type_d F mn tdecs1 tenv d tdecs1' (tenvT',tenvC',tenv') ∧
  decs_type_sound_invariant mn tdecs1 ctMap tenvS tenv st env
  ⇒
  dec_diverges env st d ∨
  ?st' r tenvS'.
     (r ≠ Rerr (Rabort Rtype_error)) ∧
     evaluate_dec F mn env st d (st', r) ∧
     consistent_decls st'.defined_types (union_decls tdecs1' tdecs1) ∧
     store_type_extension tenvS tenvS' ∧
     type_s ctMap tenvS' st'.refs ∧
     (!cenv' env'.
         (r = Rval (cenv',env')) ⇒
         (MAP FST cenv' = MAP FST tenvC') ∧
         consistent_ctMap (union_decls tdecs1' tdecs1) (FUNION (flat_to_ctMap tenvC') ctMap) ∧
         consistent_con_env (FUNION (flat_to_ctMap tenvC') ctMap)
         (merge_alist_mod_env ([],cenv') env.c) (merge_alist_mod_env ([],tenvC') tenv.c) ∧
         type_env (FUNION (flat_to_ctMap tenvC') ctMap) tenvS' (env' ++ env.v) (bind_var_list2 tenv' tenv.v) ∧
         type_env (FUNION (flat_to_ctMap tenvC') ctMap) tenvS' env'
         (bind_var_list2 tenv' Empty)) ∧
     (!err. (r = Rerr (Rraise err)) ⇒ type_v 0 ctMap tenvS' err Texn)`,
 srw_tac[][decs_type_sound_invariant_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 imp_res_tac type_d_tenvT_ok >>
 `ctMap_ok (flat_to_ctMap tenvC' ⊌ ctMap)` by metis_tac [FST,SND,ctMap_ok_pres] >>
 full_simp_tac(srw_ss())[type_d_cases] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[dec_diverges_def, evaluate_dec_cases] >>
 full_simp_tac(srw_ss())[union_decls_empty]
 >- (`∃st2 r tenvS'. r ≠ Rerr (Rabort Rtype_error) ∧ small_eval env (st.refs,st.ffi) e [] (st2,r) ∧
                type_s ctMap tenvS' (FST st2) ∧
                store_type_extension tenvS tenvS' ∧
                (!v. (r = Rval v) ==> type_v tvs ctMap tenvS' v t) ∧
                (!err. (r = Rerr (Rraise err)) ⇒ type_v 0 ctMap tenvS' err Texn)`
                         by metis_tac [exp_type_soundness, PAIR, FST] >>
     cases_on `r` >>
     full_simp_tac(srw_ss())[]
     >- (`(pmatch env.c (FST st2) p a [] = No_match) ∨
          (?new_env. pmatch env.c (FST st2) p a [] = Match new_env)`
                   by metis_tac [pmatch_type_progress]
         >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`, `Rerr (Rraise Bindv)`, `tenvS'`] >>
             srw_tac[][Bindv_def, GSYM small_big_exp_equiv, to_small_st_def] >>
             metis_tac [type_v_exn])
         >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`, `Rval ([],new_env)`, `tenvS'`] >>
             `pmatch env.c (FST st2) p a ([]++env.v) = Match (new_env++env.v)`
                      by metis_tac [pmatch_append] >>
             `type_env ctMap tenvS [] Empty` by metis_tac [type_v_rules] >>
             `type_env ctMap tenvS' new_env (bind_var_list tvs bindings Empty) ∧
              type_env ctMap tenvS' (new_env ++ env.v) (bind_var_list tvs bindings tenv.v)`
                          by (imp_res_tac pmatch_type_preservation >>
                              metis_tac [APPEND, APPEND_NIL,type_v_weakening, weakM_refl, weakC_refl,v_unchanged,
                                        store_type_extension_weakS, weakCT_refl, consistent_con_env_def]) >>
             srw_tac[][GSYM small_big_exp_equiv, to_small_st_def]
             >- metis_tac [FST, pair_CASES, small_big_exp_equiv] >>
             srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
             Cases_on `tenv.c` >>
             Cases_on `env.c` >>
             srw_tac[][flat_to_ctMap_def, merge_mod_env_def, merge_alist_mod_env_def] >>
             metis_tac [bvl2_to_bvl, small_big_exp_equiv]))
     >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`,`Rerr e'`,`tenvS'`] >>
         srw_tac[][] >>
         srw_tac[][store_type_extension_def, GSYM small_big_exp_equiv, to_small_st_def] >>
         metis_tac []))
 >- (assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO, FORALL_PROD] exp_type_soundness) >>
     rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
     pop_assum (qspecl_then [`st.ffi`, `e`, `t`, `0`] mp_tac) >>
     simp [bind_tvar_def, v_unchanged] >>
     srw_tac[][] >>
     rename1 `small_eval _ _ _ _ (st2,res)` >>
     cases_on `res` >>
     full_simp_tac(srw_ss())[]
     >- (`(pmatch env.c (FST st2) p a [] = No_match) ∨
          (?new_env. pmatch env.c (FST st2) p a [] = Match new_env)`
                    by (metis_tac [pmatch_type_progress])
         >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`,`Rerr (Rraise Bindv)`, `tenvS'`] >>
             srw_tac[][GSYM small_big_exp_equiv, to_small_st_def] >>
             metis_tac [Bindv_def, type_v_exn, pair_CASES, FST])
         >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`,`Rval ([],new_env)`, `tenvS'`] >>
             `pmatch env.c (FST st2) p a ([]++env.v) = Match (new_env++env.v)`
                        by metis_tac [pmatch_append] >>
             `type_p 0 tenv p t bindings` by metis_tac [] >>
             `type_env ctMap tenvS [] Empty` by metis_tac [type_v_rules] >>
             `type_env ctMap tenvS' new_env (bind_var_list 0 bindings Empty) ∧
              type_env ctMap tenvS' (new_env ++ env.v) (bind_var_list 0 bindings tenv.v)`
                      by (imp_res_tac pmatch_type_preservation >>
                          metis_tac [APPEND, APPEND_NIL, type_v_weakening, weakM_refl, weakC_refl,
                                    store_type_extension_weakS, weakCT_refl, consistent_con_env_def]) >>
             srw_tac[][GSYM small_big_exp_equiv, to_small_st_def]
             >- metis_tac [pair_CASES, FST] >>
             srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
             Cases_on `tenv.c` >>
             Cases_on `env.c` >>
             srw_tac[][flat_to_ctMap_def, merge_mod_env_def, merge_alist_mod_env_def] >>
             metis_tac [bvl2_to_bvl, small_big_exp_equiv]))
     >- (MAP_EVERY qexists_tac [`st with <| ffi := SND st2; refs := FST st2 |>`, `Rerr e'`,`tenvS'`] >>
         srw_tac[][] >>
         srw_tac[][GSYM small_big_exp_equiv, to_small_st_def, store_type_extension_def]))
 >- (imp_res_tac type_funs_distinct >>
     `type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs) bindings`
                  by metis_tac [type_recfun_env] >>
     imp_res_tac type_env_merge_lem1 >>
     MAP_EVERY qexists_tac [`st`, `Rval ([],build_rec_env funs env [])`, `tenvS`] >>
     srw_tac[][]
     >- metis_tac [store_type_extension_refl]
     >- (srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST] >>
         Cases_on `tenv.c` >>
         Cases_on `env.c` >>
         srw_tac[][flat_to_ctMap_def, merge_mod_env_def, merge_alist_mod_env_def])
     >- (srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST] >>
         Cases_on `tenv.c` >>
         Cases_on `env.c` >>
         srw_tac[][flat_to_ctMap_def, merge_mod_env_def, merge_alist_mod_env_def]) >>
     srw_tac[][flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST] >>
     full_simp_tac(srw_ss())[flat_to_ctMap_def, build_rec_env_merge] >>
     srw_tac[][store_type_extension_def] >>
     metis_tac [bvl2_to_bvl, type_env2_to_type_env])
 >- (MAP_EVERY qexists_tac [`st with defined_types := type_defs_to_new_tdecs mn tdefs ∪ st.defined_types`,`Rval (build_tdefs mn tdefs,[])`,`tenvS`] >>
     qabbrev_tac `flat_envT = FEMPTY |++ MAP (λ(tvs,tn,ctors). (tn,tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn)))) tdefs` >>
     `DISJOINT (FDOM (flat_to_ctMap (build_ctor_tenv mn (merge_mod_env (FEMPTY,flat_envT) tenv.t) tdefs))) (FDOM ctMap)`
                    by metis_tac [consistent_decls_disjoint] >>
     `tenv_tabbrev_ok (merge_mod_env (FEMPTY,flat_envT) tenv.t)`
              by (match_mp_tac tenv_tabbrev_ok_merge >>
                  srw_tac[][tenv_tabbrev_ok_def, FEVERY_FEMPTY]) >>
     srw_tac[][]
     >- metis_tac [check_ctor_tenv_dups]
     >- (full_simp_tac(srw_ss())[RES_FORALL,SUBSET_DEF, DISJOINT_DEF, EXTENSION, consistent_decls_def] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[type_defs_to_new_tdecs_def, MEM_MAP, FORALL_PROD] >>
         srw_tac[][] >>
         CCONTR_TAC >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         res_tac >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         cases_on `mn` >>
         full_simp_tac(srw_ss())[mk_id_def] >>
         srw_tac[][] >>
         metis_tac [])
     >- full_simp_tac(srw_ss())[check_ctor_tenv_def, LAMBDA_PROD]
     >- (full_simp_tac(srw_ss())[union_decls_def, consistent_decls_def, RES_FORALL] >>
         srw_tac[][] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[MEM_MAP, type_defs_to_new_tdecs_def]
         >- (PairCases_on `y` >>
             full_simp_tac(srw_ss())[EXISTS_PROD] >>
             srw_tac[][] >>
             metis_tac [])
         >- (PairCases_on `y` >>
             full_simp_tac(srw_ss())[EXISTS_PROD] >>
             srw_tac[][] >>
             metis_tac [])
         >- (res_tac >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (res_tac >>
             every_case_tac >>
             full_simp_tac(srw_ss())[]))
     >- metis_tac [store_type_extension_refl]
     >- (srw_tac[][build_tdefs_def, build_ctor_tenv_def, mem_lem, MAP_REVERSE, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
         srw_tac[][LAMBDA_PROD, MAP_MAP_o, combinTheory.o_DEF])
     >- (srw_tac[][union_decls_def] >>
         metis_tac [consistent_ctMap_extend, define_types_lem])
     >- (
       qspecl_then [`ctMap`, `env.c`, `tenv with t := merge_mod_env (FEMPTY,flat_envT) tenv.t`] mp_tac extend_consistent_con >>
       simp [])
     >- (srw_tac[][bind_var_list2_def] >>
         `weakCT (FUNION (flat_to_ctMap (build_ctor_tenv mn (merge_mod_env (FEMPTY,flat_envT) tenv.t) tdefs)) ctMap) ctMap`
                       by metis_tac [disjoint_env_weakCT] >>
         imp_res_tac type_v_weakening >>
         first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [AND_IMP_INTRO]) >>
         srw_tac[][weakS_refl])
     >- metis_tac [type_env_eqn, bind_var_list2_def])
 >- (qexists_tac `tenvS` >>
     srw_tac[][store_type_extension_refl, flat_to_ctMap_def, flat_to_ctMap_list_def, FUPDATE_LIST_THM,
         bind_var_list2_def] >>
     srw_tac[][Once type_v_cases] >>
     Cases_on `env.c` >>
     PairCases_on `tenvC` >>
     srw_tac[][merge_alist_mod_env_def])
 >- (Q.LIST_EXISTS_TAC [`st with <| defined_types := {TypeExn (mk_id mn cn)} ∪ st.defined_types |>`,
                        `Rval ([(cn,LENGTH ts,TypeExn (mk_id mn cn))],[])`,
                        `tenvS`] >>
     `DISJOINT
       (FDOM (flat_to_ctMap [(cn, ([]:tvarN list,ts,TypeExn (mk_id mn cn)))]))
       (FDOM ctMap)`
                 by metis_tac [consistent_decls_disjoint_exn] >>
     srw_tac[][]
     >- (full_simp_tac(srw_ss())[consistent_decls_def, RES_FORALL] >>
         CCONTR_TAC >>
         full_simp_tac(srw_ss())[] >>
         res_tac >>
         every_case_tac >>
         full_simp_tac(srw_ss())[]
         >- metis_tac [] >>
         cases_on `mn` >>
         full_simp_tac(srw_ss())[mk_id_def])
     >- (full_simp_tac(srw_ss())[union_decls_def, consistent_decls_def, RES_FORALL] >>
         srw_tac[][] >>
         srw_tac[][] >>
         every_case_tac >>
         srw_tac[][] >>
         res_tac >>
         full_simp_tac(srw_ss())[])
     >- (srw_tac[][store_type_extension_def] >>
         qexists_tac `FEMPTY` >>
         srw_tac[][])
     >- (srw_tac[][union_decls_def] >>
         metis_tac [consistent_ctMap_extend_exn, define_exns_lem])
     >- (match_mp_tac (SIMP_RULE (srw_ss()) [] extend_consistent_con_exn) >>
         full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION, flat_to_ctMap_def, flat_to_ctMap_list_def,
             FDOM_FUPDATE_LIST])
     >- (srw_tac[][bind_var_list2_def] >>
         `DISJOINT (FDOM (flat_to_ctMap [(cn,[]:tvarN list, MAP (type_name_subst tenv.t) ts,TypeExn (mk_id mn cn))])) (FDOM ctMap)`
                   by full_simp_tac(srw_ss())[flat_to_ctMap_def, FDOM_FUPDATE_LIST, flat_to_ctMap_list_def] >>
         `weakCT (FUNION (flat_to_ctMap [(cn, ([],MAP (type_name_subst tenv.t) ts,TypeExn (mk_id mn cn)) )]) ctMap) ctMap`
                by metis_tac [disjoint_env_weakCT] >>
         `ctMap_ok (FUNION (flat_to_ctMap [(cn, ([],MAP (type_name_subst tenv.t) ts,TypeExn (mk_id mn cn)))]) ctMap)`
                       by (match_mp_tac ctMap_ok_merge_imp >>
                           full_simp_tac(srw_ss())[consistent_con_env_def] >>
                           srw_tac[][flat_to_ctMap_def, flat_to_ctMap_list_def, ctMap_ok_def,
                               FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
                           every_case_tac >>
                           full_simp_tac(srw_ss())[] >>
                           srw_tac[][] >>
                           full_simp_tac(srw_ss())[check_exn_tenv_def]>>
                           full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP]>>rpt strip_tac>>
                           metis_tac[check_freevars_type_name_subst]) >>
         metis_tac [type_v_weakening, weakM_refl, weakC_refl,
                    consistent_con_env_def, weakS_refl])
     >- metis_tac [type_env_eqn, bind_var_list2_def]));

val store_type_extension_trans = Q.prove (
`!tenvS1 tenvS2 tenvS3.
  store_type_extension tenvS1 tenvS2 ∧
  store_type_extension tenvS2 tenvS3 ⇒
  store_type_extension tenvS1 tenvS3`,
 srw_tac[][store_type_extension_def] >>
 full_simp_tac(srw_ss())[FLOOKUP_FUNION] >>
 qexists_tac `FUNION tenvS'' tenvS'` >>
 srw_tac[][FUNION_ASSOC, FLOOKUP_FUNION] >>
 full_case_tac >-
 metis_tac [] >>
 qpat_assum `!l. P l` (MP_TAC o Q.SPEC `l`) >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]);

val still_has_exns = Q.prove (
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

val still_has_lists = Q.prove (
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

val still_has_bools = Q.prove (
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

val swap_imp = PROVE[]``(a ⇒ b ⇒ c) ⇔ (b ⇒ a ⇒ c)``;

val decs_type_soundness = Q.store_thm ("decs_type_soundness",
`!uniq mn tdecs1 tenv ds tdecs1' res.
  type_ds uniq mn tdecs1 tenv ds tdecs1' res ⇒
  ∀tenvS env st ctMap tenvT' tenvC' tenv'.
  res = (tenvT',tenvC',tenv') ∧
  uniq = F ∧
  decs_type_sound_invariant mn tdecs1 ctMap tenvS tenv st env
  ⇒
  decs_diverges mn env st ds ∨
  ?st' r cenv' tenvS'.
     (r ≠ Rerr (Rabort Rtype_error)) ∧
     evaluate_decs F mn env st ds (st', cenv', r) ∧
     consistent_decls st'.defined_types (union_decls tdecs1' tdecs1) ∧
     store_type_extension tenvS tenvS' ∧
     (!err.
         (r = Rerr err) ⇒
         (?tenvC1 tenvC2.
           (!err'. (err = Rraise err') ⇒ type_v 0 (FUNION (flat_to_ctMap tenvC2) ctMap) tenvS' err' Texn) ∧
           (tenvC' = tenvC1++tenvC2) ∧
           type_s (FUNION (flat_to_ctMap tenvC2) ctMap) tenvS' st'.refs ∧
           consistent_ctMap (union_decls tdecs1' tdecs1) (FUNION (flat_to_ctMap tenvC2) ctMap) ∧
           consistent_con_env (FUNION (flat_to_ctMap tenvC2) ctMap) (merge_alist_mod_env ([],cenv') env.c) (merge_alist_mod_env ([],tenvC2) tenv.c))) ∧
     (!env'.
         (r = Rval env') ⇒
         (MAP FST cenv' = MAP FST tenvC') ∧
         consistent_con_env (FUNION (flat_to_ctMap tenvC') ctMap) (merge_alist_mod_env ([],cenv') env.c) (merge_alist_mod_env ([],tenvC') tenv.c) ∧
         consistent_ctMap (union_decls tdecs1' tdecs1) (FUNION (flat_to_ctMap tenvC') ctMap) ∧
         type_s (FUNION (flat_to_ctMap tenvC') ctMap) tenvS' st'.refs ∧
         type_env (FUNION (flat_to_ctMap tenvC') ctMap) tenvS' env' (bind_var_list2 tenv' Empty) ∧
         type_env (FUNION (flat_to_ctMap tenvC') ctMap) tenvS' (env'++env.v) (bind_var_list2 tenv' tenv.v))`,
 ho_match_mp_tac type_ds_strongind >>
 srw_tac[][METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 srw_tac[][Once evaluate_decs_cases, bind_var_list2_def] >>
 srw_tac[][] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once decs_diverges_cases]) >>
 full_simp_tac(srw_ss())[empty_to_ctMap]
 >- (full_simp_tac(srw_ss())[union_decls_empty, decs_type_sound_invariant_def] >>
     qexists_tac `tenvS` >>
     srw_tac[][store_type_extension_def]
     >- (qexists_tac `FEMPTY` >>
          srw_tac[][])
     >- metis_tac [type_v_rules])
 >- (assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dec_type_soundness) >>
     PairCases_on`new_tenv1` >>
     rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
     pop_assum mp_tac >>
     simp [] >>
     srw_tac[][] >>
     rename1 `type_s _ tenvS' st'.refs` >>
     `(?cenv'' env''. (?err. r = Rerr err) ∨ r = Rval (cenv'',env''))`
                   by (cases_on `r` >> metis_tac [pair_CASES]) >>
     full_simp_tac(srw_ss())[GSYM union_decls_assoc]
     >- (Q.LIST_EXISTS_TAC [`st'`, `Rerr err`, `[]`, `tenvS'`] >>
         srw_tac[][]
         >- metis_tac [consistent_decls_weakening, weak_decls_union2, type_ds_mod]
         >- (Q.LIST_EXISTS_TAC [`tenvC'`, `[]`] >>
             srw_tac[][flat_to_ctMap_def, flat_to_ctMap_list_def, FUPDATE_LIST]
             >- metis_tac [weak_decls_union2, type_d_mod, type_ds_mod, consistent_ctMap_weakening, decs_type_sound_invariant_def] >>
             Cases_on `tenv.c` >>
             Cases_on `env.c` >>
             srw_tac[][merge_mod_env_def, merge_alist_mod_env_def] >>
             metis_tac [weak_decls_union2, type_d_mod, type_ds_mod, consistent_ctMap_weakening, decs_type_sound_invariant_def]))
     >- (
     srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(equal"evaluate_dec" o fst o dest_const o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     PairCases_on`res`>>
     full_simp_tac(srw_ss())[append_new_dec_tenv_def] >> rpt var_eq_tac >>
     `¬decs_diverges mn (extend_dec_env env'' cenv'' env) st' ds`
                  by metis_tac [pair_CASES] >>
     first_x_assum(fn th =>
       first_assum(mp_tac o MATCH_MP (CONV_RULE(STRIP_QUANT_CONV(HO_REWR_CONV(swap_imp))) th))) >>
     disch_then(qspecl_then[`tenvS'`,`flat_to_ctMap new_tenv11 ⊌ ctMap`]mp_tac) >>
     impl_tac >- (
         full_simp_tac(srw_ss())[decs_type_sound_invariant_def, extend_dec_env_def] >>
         simp [extend_env_new_decs_def] >> srw_tac[][]
         >- (imp_res_tac type_d_tenvT_ok >>
             match_mp_tac tenv_tabbrev_ok_merge >>
             srw_tac[][tenv_tabbrev_ok_def, FEVERY_FEMPTY] >> full_simp_tac(srw_ss())[])
         >- metis_tac [ctMap_ok_pres,FST,SND]
         >- metis_tac [still_has_exns, type_d_ctMap_disjoint,FST,SND]
         >- metis_tac [still_has_lists, type_d_ctMap_disjoint,FST,SND]
         >- metis_tac [still_has_bools, type_d_ctMap_disjoint,FST,SND]
         >- metis_tac [type_v_weakening, store_type_extension_weakS, disjoint_env_weakCT,
                       type_d_ctMap_disjoint, ctMap_ok_pres,FST,SND]
         >- metis_tac [type_d_ctMap_disjoint, disjoint_env_weakCT, weakM_refl, type_s_weakening, ctMap_ok_pres,FST,SND]
         >- (imp_res_tac type_d_mod >>
             full_simp_tac(srw_ss())[union_decls_def])) >>
     strip_tac >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(equal"evaluate_decs" o fst o dest_const o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qexists_tac`tenvS''` >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(equal"store_type_extension" o fst o dest_const o fst o strip_comb))) >>
     conj_tac >- metis_tac[store_type_extension_trans] >>
     Cases_on`r`>>full_simp_tac(srw_ss())[combine_dec_result_def] >>
     TRY(
       CONV_TAC SWAP_EXISTS_CONV >>
       qexists_tac`tenvC2 ++ new_tenv11`) >>
     full_simp_tac(srw_ss())[flat_to_ctMap_append,FUNION_ASSOC,extend_dec_env_def,
        merge_alist_mod_env_empty_assoc,extend_env_new_decs_def] >>
     qmatch_assum_abbrev_tac`consistent_ctMap _ (f1 ⊌ f2 ⊌ ctMap)` >>
     `ctMap_ok (f1 ⊌ f2 ⊌ ctMap)` by full_simp_tac(srw_ss())[consistent_con_env_def] >>
     `DISJOINT (FDOM f1) (FDOM (FUNION f2 ctMap))`
                by (
       unabbrev_all_tac >> srw_tac[][] >>
       imp_res_tac type_ds_ctMap_disjoint >>
       full_simp_tac(srw_ss())[flat_to_ctMap_append] ) >>
     metis_tac[type_v_weakening,store_type_extension_weakS,
               consistent_con_env_def, type_env_merge_bvl2,
               disjoint_env_weakCT, DISJOINT_SYM,
               FUNION_ASSOC,bvl2_append])));

val consistent_mod_env_dom = Q.prove (
`!tenvS ctMap menv tenvM.
  consistent_mod_env tenvS ctMap menv tenvM ⇒
  (set (MAP FST menv) = FDOM tenvM)`,
 induct_on `menv` >>
 srw_tac[][] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[] >>
 metis_tac []);

val type_env_eqn2 = Q.prove (
`(!tenvM tenvC tenvS.
   type_env tenvC tenvS [] Empty = T) ∧
 (!tenvM tenvC tenvS n v n' tvs t envE tenv.
   type_env tenvC tenvS ((n,v)::envE) (Bind_name n' tvs t tenv) =
     ((n = n') ∧ type_v tvs tenvC tenvS v t ∧
      type_env tenvC tenvS envE tenv))`,
srw_tac[][] >-
srw_tac[][Once type_v_cases] >>
srw_tac[][Once type_v_cases] >>
metis_tac []);

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
 srw_tac[][] >>
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
 srw_tac[][no_dup_types_def] >>
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

val no_new_mods = Q.prove (
`!x uniq mn decls1 tenv d decls1' tenvT' tenvC' tenv'.
  type_d uniq mn decls1 tenv d decls1' (tenvT',tenvC',tenv') ∧
  decls1.defined_mods = x
  ⇒
  (union_decls decls1' decls1).defined_mods = x`,
 srw_tac[][] >>
 imp_res_tac type_d_mod >>
 full_simp_tac(srw_ss())[union_decls_def]);

val top_type_soundness_lem = Q.prove (
`!decls1 (tenv : type_environment) (env : v environment) st decls1' tenvT' tenvM' tenvC' tenv' top.
  type_sound_invariants NONE (decls1,tenv,st,env) ∧
  type_top F decls1 tenv top decls1' (tenvT',tenvM',tenvC',tenv') ∧
  ¬top_diverges env st top
  ⇒
  ?r cenv2 st'.
    r ≠ Rerr (Rabort Rtype_error) ∧
    evaluate_top F env st top (st',cenv2,r) ∧
    type_sound_invariants (SOME r) (update_type_sound_inv (decls1,tenv,st,env) decls1' tenvT' tenvM' tenvC' tenv' st' cenv2 r)`,
 srw_tac[][type_sound_invariants_def] >>
 `num_tvs tenv.v = 0` by metis_tac [type_v_freevars] >>
 full_simp_tac(srw_ss())[type_top_cases, top_diverges_cases] >>
 srw_tac[][evaluate_top_cases]
 >- (`weak_decls_other_mods NONE decls_no_sig decls1`
              by (full_simp_tac(srw_ss())[weak_decls_other_mods_def, weak_decls_only_mods_def, mk_id_def] >>
                  metis_tac []) >>
     `type_d F NONE decls_no_sig <| t := tenv.t; m := tenvM_no_sig; c := tenvC_no_sig; v := tenv.v |>
             d decls1' new_tenv`
                  by (match_mp_tac type_d_weakening >>
                      srw_tac[][] >>
                      metis_tac [weak_decls_refl,weak_decls_other_mods_refl, type_d_weakening, consistent_con_env_def]) >>
     `decs_type_sound_invariant NONE decls_no_sig ctMap tenvS <| t := tenv.t; m := tenvM_no_sig; c := tenvC_no_sig; v := tenv.v |> st env`
                  by (srw_tac[][decs_type_sound_invariant_def] >>
                      metis_tac [consistent_con_env_def]) >>
     `?new_tenv_t new_tenv_c new_tenv_v. new_tenv = (new_tenv_t, new_tenv_c, new_tenv_v)` by metis_tac [pair_CASES] >>
     assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dec_type_soundness) >>
     full_simp_tac(srw_ss())[] >>
     rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
     pop_assum mp_tac >>
     simp [] >>
     srw_tac[][] >>
     rename1 `type_s _ tenvS' st'.refs` >>
     `(?err. r = Rerr err) ∨ (?new_c new_v. r = Rval (new_c,new_v))`
                by (cases_on `r` >> metis_tac [pair_CASES]) >>
     srw_tac[][]
     >- (MAP_EVERY qexists_tac [`Rerr err`, `([],[])`, `st'`] >>
         srw_tac[][type_sound_invariants_def, update_type_sound_inv_def] >>
         MAP_EVERY qexists_tac [`ctMap`, `tenvS'`, `union_decls decls1' decls_no_sig`, `tenvM_no_sig`, `tenvC_no_sig`] >>
         srw_tac[][]
         >- metis_tac [consistent_ctMap_weakening, type_d_mod, weak_decls_union2]
         >- metis_tac [type_v_weakening, store_type_extension_weakS, weakCT_refl, consistent_con_env_def]
         >- metis_tac [type_v_weakening, store_type_extension_weakS, weakCT_refl, consistent_con_env_def]
         >- (imp_res_tac type_d_mod >>
             full_simp_tac(srw_ss())[decls_ok_def, union_decls_def, decls_to_mods_def, SUBSET_DEF, EXTENSION] >>
             full_simp_tac(srw_ss())[GSPECIFICATION] >>
             metis_tac [])
         >- metis_tac [weak_decls_union]
         >- metis_tac [weak_decls_only_mods_union]
         >- metis_tac [no_new_mods, eval_d_no_new_mods, FST])
     >- (MAP_EVERY qexists_tac [`Rval ([],new_v)`,`([],new_c)`, `st'`] >>
         srw_tac[][type_sound_invariants_def, update_type_sound_inv_def] >>
         `weakCT (FUNION (flat_to_ctMap new_tenv_c) ctMap) ctMap`
                    by metis_tac [disjoint_env_weakCT, type_d_ctMap_disjoint, FST, SND] >>
         MAP_EVERY qexists_tac [`FUNION (flat_to_ctMap new_tenv_c) ctMap`, `tenvS'`, `union_decls decls1' decls_no_sig`, `tenvM_no_sig`, `merge_alist_mod_env ([],new_tenv_c) tenvC_no_sig`] >>
         full_simp_tac(srw_ss())[lift_new_dec_tenv_def] >>
         srw_tac[][extend_top_env_def]
         >- metis_tac [still_has_exns, type_d_ctMap_disjoint, FST, SND]
         >- metis_tac [still_has_lists, type_d_ctMap_disjoint, FST, SND]
         >- metis_tac [still_has_bools, type_d_ctMap_disjoint, FST, SND]
         >- (imp_res_tac type_d_tenvT_ok >>
             match_mp_tac tenv_tabbrev_ok_merge >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][tenv_tabbrev_ok_def, FEVERY_FEMPTY])
         >- metis_tac [FST, SND, type_v_weakening, store_type_extension_weakS, consistent_con_env_def, weakCT_refl]
         >- metis_tac [type_s_weakening, weakM_refl, consistent_con_env_def]
         >- metis_tac [weakC_merge]
         >- (imp_res_tac type_d_mod >>
             full_simp_tac(srw_ss())[GSPECIFICATION, decls_ok_def, union_decls_def, decls_to_mods_def, SUBSET_DEF, EXTENSION] >>
             metis_tac [])
         >- metis_tac [weak_decls_union]
         >- metis_tac [weak_decls_only_mods_union]
         >- metis_tac [no_new_mods, eval_d_no_new_mods, FST]))
 >- (full_simp_tac(srw_ss())[] >>
     metis_tac [type_ds_no_dup_types])
 >- metis_tac [type_ds_no_dup_types, FST, SND, pair_CASES]
 >- (`weak_decls_other_mods (SOME mn) decls_no_sig decls1`
                     by (full_simp_tac(srw_ss())[weak_decls_def, weak_decls_other_mods_def] >>
                         full_simp_tac(srw_ss())[SUBSET_DEF,mk_id_def,decls_ok_def] >>
                         fsrw_tac[boolSimps.DNF_ss][decls_to_mods_def,GSPECIFICATION] >>
                         metis_tac[]) >>
     `type_ds F (SOME mn) decls_no_sig <| t := tenv.t; m := tenvM_no_sig; c := tenvC_no_sig; v := tenv.v |> ds decls' new_tenv1`
                  by (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] type_ds_weakening) >>
                      srw_tac[][] >>
                      metis_tac [consistent_con_env_def]) >>
     `decs_type_sound_invariant (SOME mn) decls_no_sig ctMap tenvS <| t := tenv.t; m := tenvM_no_sig; c := tenvC_no_sig; v := tenv.v |> st env`
                  by (srw_tac[][decs_type_sound_invariant_def] >>
                      full_simp_tac(srw_ss())[weak_decls_def] >>
                      metis_tac [consistent_con_env_def]) >>
     `?new_tenv_t new_tenv_c new_tenv_v. new_tenv1 = (new_tenv_t, new_tenv_c, new_tenv_v)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO, PULL_FORALL] decs_type_soundness) >>
     rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
     pop_assum mp_tac >>
     simp [] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[GSYM PULL_FORALL] >>
     rename1 `evaluate_decs _ _ _ _ _ (st',cenv2,r)` >>
     `(?err. r = Rerr err) ∨ (?env2. r = Rval env2)`
                by (cases_on `r` >> metis_tac []) >>
     srw_tac[][]
     >- (MAP_EVERY qexists_tac [`Rerr err`, `([(mn,cenv2)],[])`, `st' with defined_mods := {mn} ∪ st'.defined_mods`] >>
         simp [type_sound_invariants_def, update_type_sound_inv_def] >>
         conj_tac
         >- (qexists_tac `st'` >>
             simp [] >>
             imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[check_signature_cases] >>
             imp_res_tac type_specs_no_mod >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[] >>
             metis_tac [type_ds_no_dup_types]) >>
         `DISJOINT (FDOM (flat_to_ctMap (tenvC1++tenvC2))) (FDOM ctMap)`
                      by metis_tac [type_ds_ctMap_disjoint] >>
         `DISJOINT (FDOM (flat_to_ctMap tenvC2)) (FDOM ctMap)`
                      by (full_simp_tac(srw_ss())[flat_to_ctMap_append]) >>
         `weakCT (FUNION (flat_to_ctMap tenvC2) ctMap) ctMap`
                      by (match_mp_tac disjoint_env_weakCT >>
                          srw_tac[][] >>
                          full_simp_tac(srw_ss())[]) >>
         `?new_tenv_t2 new_tenv_c2 new_tenv_v2. new_tenv2 = (new_tenv_t2, new_tenv_c2, new_tenv_v2)` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss())[mod_lift_new_dec_tenv_def] >>
         `flat_tenv_ctor_ok tenvC2` by metis_tac [type_ds_tenvC_ok, flat_tenv_ctor_ok_def, EVERY_APPEND, FST, SND] >>
         `ctMap_ok (FUNION (flat_to_ctMap tenvC2) ctMap)`
                    by (match_mp_tac ctMap_ok_merge_imp >>
                        srw_tac[][] >>
                        metis_tac [flat_tenvC_ok_ctMap, consistent_con_env_def]) >>
         MAP_EVERY qexists_tac [`FUNION (flat_to_ctMap tenvC2) ctMap`, `tenvS'`,
                                `(union_decls (union_decls <|defined_mods := {mn}; defined_types := {}; defined_exns := {}|> decls') decls_no_sig)`,
                                `tenvM_no_sig`, `tenvC_no_sig`] >>
         srw_tac[][]
         >- (srw_tac[][GSYM union_decls_assoc] >>
             imp_res_tac consistent_decls_add_mod >>
             full_simp_tac(srw_ss())[union_decls_def])
         >- (full_simp_tac(srw_ss())[consistent_ctMap_def, union_decls_def])
         >- metis_tac [still_has_exns]
         >- (`DISJOINT (IMAGE SND (FDOM (flat_to_ctMap (tenvC1++tenvC2)))) (IMAGE SND (FDOM ctMap))`
                       by metis_tac [type_ds_ctMap_disjoint] >>
             full_simp_tac(srw_ss())[flat_to_ctMap_append] >>
             metis_tac [still_has_lists])
         >- (`DISJOINT (IMAGE SND (FDOM (flat_to_ctMap (tenvC1++tenvC2)))) (IMAGE SND (FDOM ctMap))`
                       by metis_tac [type_ds_ctMap_disjoint] >>
             full_simp_tac(srw_ss())[flat_to_ctMap_append] >>
             metis_tac [still_has_bools])
         >- metis_tac [type_v_weakening, store_type_extension_weakS]
         >- metis_tac [consistent_con_env_weakening]
         >- metis_tac [type_v_weakening, store_type_extension_weakS]
         >- (imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[GSPECIFICATION, decls_ok_def, union_decls_def, decls_to_mods_def, SUBSET_DEF, EXTENSION] >>
             metis_tac [])
         >- (full_simp_tac(srw_ss())[check_signature_cases, union_decls_def, weak_decls_def, SUBSET_DEF] >>
             metis_tac [])
         >- (full_simp_tac(srw_ss())[weak_decls_def, check_signature_cases, union_decls_def, weak_decls_only_mods_def, SUBSET_DEF,
                 mk_id_def, weak_decls_other_mods_def]
             >- metis_tac [] >>
             imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[decls_to_mods_def, SUBSET_DEF, GSPECIFICATION] >>
             metis_tac [SOME_11, NOT_SOME_NONE])
         >- (imp_res_tac eval_ds_no_new_mods >>
             full_simp_tac(srw_ss())[] >>
             `decls''.defined_mods = {}`
                      by (full_simp_tac(srw_ss())[check_signature_cases] >>
                          srw_tac[][] >>
                          imp_res_tac type_ds_mod >>
                          imp_res_tac type_specs_no_mod >>
                          full_simp_tac(srw_ss())[]) >>
             srw_tac[][union_decls_def]))
     >- (MAP_EVERY qexists_tac [`Rval ([(mn,env2)],[])`, `([(mn,cenv2)],[])`, `st' with defined_mods := {mn} ∪ st'.defined_mods`] >>
         simp [type_sound_invariants_def, update_type_sound_inv_def] >>
         conj_tac
         >- (imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[check_signature_cases] >>
             imp_res_tac type_specs_no_mod >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[] >>
             metis_tac [type_ds_no_dup_types]) >>
         `DISJOINT (FDOM (flat_to_ctMap new_tenv_c)) (FDOM ctMap)`
                      by metis_tac [type_ds_ctMap_disjoint] >>
         `weakCT (FUNION (flat_to_ctMap new_tenv_c) ctMap) ctMap`
                      by (match_mp_tac disjoint_env_weakCT >>
                          srw_tac[][] >>
                          full_simp_tac(srw_ss())[]) >>
         `?new_tenv_t2 new_tenv_c2 new_tenv_v2. new_tenv2 = (new_tenv_t2, new_tenv_c2, new_tenv_v2)` by metis_tac [pair_CASES] >>
         full_simp_tac(srw_ss())[mod_lift_new_dec_tenv_def] >>
         `flat_tenv_ctor_ok new_tenv_c` by metis_tac [FST, SND, type_ds_tenvC_ok, flat_tenv_ctor_ok_def, EVERY_APPEND] >>
         `ctMap_ok (FUNION (flat_to_ctMap new_tenv_c) ctMap)`
                    by (match_mp_tac ctMap_ok_merge_imp >>
                        metis_tac [flat_tenvC_ok_ctMap, consistent_con_env_def]) >>
         `tenv_mod_ok (tenvM_no_sig |+ (mn,new_tenv_v))`
                   by metis_tac [tenv_mod_ok_pres, type_v_freevars] >>
         `tenv_val_ok (bind_var_list2 [] Empty)`
                      by (metis_tac [tenv_val_ok_def, bind_var_list2_def]) >>
         `tenv_val_ok (bind_var_list2 new_tenv_v2 Empty)`
                      by (full_simp_tac(srw_ss())[check_signature_cases] >>
                          metis_tac [type_v_freevars, type_specs_tenv_ok, FST, SND]) >>
         MAP_EVERY qexists_tac [`flat_to_ctMap new_tenv_c ⊌ ctMap`, `tenvS'`, `(union_decls (union_decls <|defined_mods := {mn}; defined_types := {}; defined_exns := {}|> decls') decls_no_sig)`,
                                `tenvM_no_sig |+ (mn,new_tenv_v)`,
                                `merge_alist_mod_env ([(mn,new_tenv_c)],[]) tenvC_no_sig`] >>
         srw_tac[][extend_top_env_def]
         >- (srw_tac[][GSYM union_decls_assoc] >>
             imp_res_tac consistent_decls_add_mod >>
             full_simp_tac(srw_ss())[union_decls_def])
         >- (full_simp_tac(srw_ss())[consistent_ctMap_def, union_decls_def])
         >- metis_tac [still_has_exns]
         >- metis_tac [still_has_lists, type_ds_ctMap_disjoint]
         >- metis_tac [still_has_bools, type_ds_ctMap_disjoint]
         >- (imp_res_tac type_ds_tenvT_ok >>
             match_mp_tac tenv_tabbrev_ok_merge >>
             full_simp_tac(srw_ss())[tenv_tabbrev_ok_merge, check_signature_cases] >>
             imp_res_tac type_specs_tenv_ok >>
             full_simp_tac(srw_ss())[tenv_tabbrev_ok_def, flat_tenv_tabbrev_ok_def, FEVERY_FEMPTY, FEVERY_FUPDATE])
         >- (srw_tac[][FUNION_FUPDATE_1] >>
             metis_tac [tenv_mod_ok_pres])
         >- (srw_tac[][Once type_v_cases] >>
             metis_tac [type_v_weakening,store_type_extension_weakS, weakM_bind,
                        weakM_refl, disjoint_env_weakCT, DISJOINT_SYM])
         >- metis_tac [consistent_con_env_to_mod, consistent_con_env_weakening]
         >- (srw_tac[][bind_var_list2_def] >>
             metis_tac [type_v_weakening,store_type_extension_weakS])
         >- (srw_tac[][FUNION_FUPDATE_1] >>
             match_mp_tac weakM_bind' >>
             simp [] >>
             full_simp_tac(srw_ss())[check_signature_cases, weak_new_dec_tenv_def] >>
             metis_tac [weakE_refl])
         >- (full_simp_tac(srw_ss())[check_signature_cases] >>
             match_mp_tac weakC_merge_one_mod2 >>
             simp [flat_weakC_refl] >>
             full_simp_tac(srw_ss())[weak_new_dec_tenv_def])
         >- (imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[GSPECIFICATION, decls_ok_def, union_decls_def, decls_to_mods_def, SUBSET_DEF, EXTENSION] >>
             metis_tac [])
         >- (full_simp_tac(srw_ss())[check_signature_cases, union_decls_def, weak_decls_def, SUBSET_DEF] >>
             metis_tac [])
         >- (full_simp_tac(srw_ss())[weak_decls_def, check_signature_cases, union_decls_def, weak_decls_only_mods_def, SUBSET_DEF,
                 mk_id_def, weak_decls_other_mods_def]
             >- metis_tac [] >>
             imp_res_tac type_ds_mod >>
             full_simp_tac(srw_ss())[decls_to_mods_def, SUBSET_DEF, GSPECIFICATION] >>
             metis_tac [SOME_11, NOT_SOME_NONE])
         >- (imp_res_tac eval_ds_no_new_mods >>
             full_simp_tac(srw_ss())[] >>
             `decls''.defined_mods = {}`
                      by (full_simp_tac(srw_ss())[check_signature_cases] >>
                          srw_tac[][] >>
                          imp_res_tac type_ds_mod >>
                          imp_res_tac type_specs_no_mod >>
                          full_simp_tac(srw_ss())[]) >>
             srw_tac[][union_decls_def]))));

val top_type_soundness = Q.store_thm ("top_type_soundness",
`!uniq decls1 tenv env st decls1' tenvT' tenvM' tenvC' tenv' top.
  type_sound_invariants NONE (decls1,tenv,st,env) ∧
  type_top uniq decls1 tenv top decls1' (tenvT',tenvM',tenvC',tenv') ∧
  ¬top_diverges env st top
  ⇒
  ?r cenv2 st'.
    (r ≠ Rerr (Rabort Rtype_error)) ∧
    evaluate_top F env st top (st',cenv2,r) ∧
    type_sound_invariants (SOME r) (update_type_sound_inv (decls1,tenv,st,env) decls1' tenvT' tenvM' tenvC' tenv' st' cenv2 r)`,
 metis_tac [top_type_soundness_lem, type_top_check_uniq]);

val FST_union_decls = Q.prove (
`!d1 d2. (union_decls d1 d2).defined_mods = d1.defined_mods ∪ d2.defined_mods`,
 srw_tac[][] >>
 srw_tac[][union_decls_def]);

val prog_type_soundness = Q.store_thm ("prog_type_soundness",
`!uniq decls1 tenv env st decls1' tenvT' tenvM' tenvC' tenv' prog.
  type_sound_invariants (NONE:('b,v) result option) (decls1,tenv,st,env) ∧
  type_prog uniq decls1 tenv prog decls1' (tenvT',tenvM',tenvC',tenv') ∧
  ¬prog_diverges env st prog
  ⇒
  ?cenv2 st'.
    (?envM2 envE2.
      evaluate_prog F env st prog (st',cenv2,Rval (envM2,envE2)) ∧
      type_sound_invariants (NONE:('b,v) result option) (update_type_sound_inv (decls1,tenv,st,env) decls1' tenvT' tenvM' tenvC' tenv' st' cenv2 (Rval (envM2,envE2)))) ∨
    (?err mods.
      err ≠ Rabort Rtype_error ∧
      mods ⊆ decls1'.defined_mods ∧
      evaluate_prog F env st prog (st',cenv2,Rerr err))`,
 induct_on `prog` >>
 srw_tac[][] >>
 ONCE_REWRITE_TAC [evaluate_prog_cases] >>
 qpat_assum `type_prog x2 x3 x4 x5 x6 x7` mp_tac  >>
 simp_tac (srw_ss()) [Once type_prog_cases, EXISTS_OR_THM]
 >- (srw_tac[][update_type_sound_inv_def, empty_decls_def, extend_top_env_def] >>
     Cases_on `tenv.c` >>
     Cases_on `tenv.t` >>
     Cases_on `env.c` >>
     srw_tac[][union_decls_def, merge_alist_mod_env_def,merge_mod_env_def, bind_var_list2_def] >>
     `<|v := env.v; c := (q'',r''); m := env.m|> = env` by srw_tac[][environment_component_equality] >>
     `<|m := tenv.m; c := (q,r); v := tenv.v; t := (q',r')|> = tenv` by srw_tac[][type_environment_component_equality] >>
     `<|defined_mods := decls1.defined_mods;
        defined_types := decls1.defined_types;
        defined_exns := decls1.defined_exns|> = decls1` by srw_tac[][decls_component_equality] >>
     srw_tac[][]) >>
 srw_tac[][] >>
 qpat_assum `~(prog_diverges x0 x1 x2)` mp_tac >>
 srw_tac[][Once prog_diverges_cases] >>
 `?new_tenv_t new_tenv_m new_tenv_c new_tenv_v. new_tenv1 = (new_tenv_t, new_tenv_m, new_tenv_c, new_tenv_v)` by metis_tac [pair_CASES] >>
 `?new_tenv_t2 new_tenv_m2 new_tenv_c2 new_tenv_v2. new_tenv2 = (new_tenv_t2, new_tenv_m2, new_tenv_c2, new_tenv_v2)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[] >>
 assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] top_type_soundness) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
 full_simp_tac(srw_ss())[] >>
 rename1 `evaluate_top _ _ _ top (st',cenv2,r)` >>
 `type_sound_invariants (NONE:('b,v) result option)
        (update_type_sound_inv (decls1,tenv,st,env) decls'
           new_tenv_t new_tenv_m new_tenv_c new_tenv_v st' cenv2 r)`
             by (full_simp_tac(srw_ss())[type_sound_invariants_def, update_type_sound_inv_def] >>
                 every_case_tac >>
                 full_simp_tac(srw_ss())[type_sound_invariants_def] >>
                 metis_tac []) >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [update_type_sound_inv_def]) >>
 srw_tac[][] >>
 `(?envM' env'. r = Rval (envM',env')) ∨ (?err. r = Rerr err)`
            by (cases_on `r` >>
                full_simp_tac(srw_ss())[] >>
                cases_on `a` >>
                full_simp_tac(srw_ss())[]) >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[extend_env_new_tops_def]
 >- (last_x_assum (fn ind => first_assum (fn inst => assume_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] ind) inst))) >>
     first_x_assum (fn ind => first_assum (assume_tac o MATCH_MP ind)) >>
     `¬prog_diverges (extend_top_env envM' env' cenv2 env) st' prog` by metis_tac [] >>
     full_simp_tac(srw_ss())[]
     >- (disj1_tac >>
         simp [PULL_EXISTS] >>
         CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``bigStep$evaluate_prog`` o fst o strip_comb))) >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp [combine_mod_result_def] >>
         full_simp_tac(srw_ss())[update_type_sound_inv_def, FUNION_ASSOC, combine_mod_result_def, union_decls_assoc, merge_alist_mod_env_assoc, bvl2_append, merge_alist_mod_env_assoc, merge_mod_env_assoc, extend_top_env_def, append_new_top_tenv_def])
     >- (disj2_tac >>
         srw_tac[DNF_ss][] >> disj1_tac >>
         CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``bigStep$evaluate_prog`` o fst o strip_comb))) >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         srw_tac[][FST_union_decls] >>
         full_simp_tac(srw_ss())[combine_mod_result_def, FST_union_decls, UNION_ASSOC] >>
         metis_tac[SUBSET_REFL]))
 >- (disj2_tac >>
     srw_tac[DNF_ss][] >> disj2_tac >>
     CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``bigStep$evaluate_top`` o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     metis_tac[SUBSET_REFL]));

val type_no_dup_top_types_lem = Q.prove (
`!uniq decls1 tenv prog decls1' res.
  type_prog uniq decls1 tenv prog decls1' res
  ⇒
  ALL_DISTINCT (prog_to_top_types prog) ∧
  DISJOINT decls1.defined_types (IMAGE (mk_id NONE) (set (prog_to_top_types prog)))`,
 ho_match_mp_tac type_prog_ind >>
 srw_tac[][prog_to_top_types_def] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_top_cases] >>
 srw_tac[][ALL_DISTINCT_APPEND, empty_decls_def]
 >- (full_simp_tac(srw_ss())[type_d_cases, decs_to_types_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[check_ctor_tenv_def] >>
     full_simp_tac(srw_ss())[LAMBDA_PROD])
 >- (`mk_id NONE e ∈ decls'.defined_types`
            by (full_simp_tac(srw_ss())[type_d_cases, decs_to_types_def] >>
                srw_tac[][] >>
                full_simp_tac(srw_ss())[mk_id_def] >>
                full_simp_tac(srw_ss())[MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
                metis_tac []) >>
     full_simp_tac(srw_ss())[union_decls_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac [])
 >- (srw_tac[][decs_to_types_def] >>
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
`!uniq decls1 tenv prog decls1' tenvT' tenvM' tenvC' tenv'.
  type_prog uniq decls1 tenv prog decls1' (tenvT',tenvM',tenvC',tenv')
  ⇒
  no_dup_top_types prog (IMAGE TypeId decls1.defined_types)`,
 srw_tac[][no_dup_top_types_def]
 >- metis_tac [type_no_dup_top_types_lem] >>
 imp_res_tac type_no_dup_top_types_lem >>
 full_simp_tac(srw_ss())[DISJOINT_DEF, EXTENSION] >>
 srw_tac[][] >>
 cases_on `x` >>
 srw_tac[][MEM_MAP] >>
 full_simp_tac(srw_ss())[mk_id_def] >>
 metis_tac []);

val type_no_dup_top_types = Q.store_thm("type_no_dup_top_types",
`!decls1 tenv prog decls1' tenvT' tenvM' tenvC' tenv'.
  type_prog uniq decls1 tenv prog decls1' (tenvT',tenvM',tenvC',tenv') ∧
  consistent_decls decls2 decls_no_sig ∧
  weak_decls_only_mods decls_no_sig decls1
  ⇒
  no_dup_top_types prog decls2`,
 srw_tac[][] >>
 `no_dup_top_types prog (IMAGE TypeId decls1.defined_types)`
         by metis_tac [type_no_dup_top_types_lem2] >>
 full_simp_tac(srw_ss())[no_dup_top_types_def] >>
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
 srw_tac[][prog_to_mods_def] >>
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
`!uniq decls1 tenv prog decls1' tenvT' tenvM' tenvC' tenv'.
  type_prog uniq decls1 tenv prog decls1' (tenvT',tenvM',tenvC',tenv')
  ⇒
  no_dup_mods prog decls1.defined_mods`,
 srw_tac[][no_dup_mods_def] >>
 metis_tac [type_no_dup_mods_lem, DISJOINT_SYM]);

val whole_prog_type_soundness = Q.store_thm ("whole_prog_type_soundness",
`!uniq decls1 tenv env st decls1' tenvT' tenvM' tenvC' tenv' prog.
  type_sound_invariants (NONE:('a,v) result option) (decls1,tenv,st,env) ∧
  type_prog uniq decls1 tenv prog decls1' (tenvT',tenvM',tenvC',tenv') ∧
  ¬prog_diverges env st prog ⇒
  ?cenv2 st'.
    (?envM2 envE2.
      evaluate_whole_prog F env st prog (st',cenv2,Rval (envM2,envE2)) ∧
      type_sound_invariants (NONE:('a,v) result option) (update_type_sound_inv (decls1,tenv,st,env) decls1' tenvT' tenvM' tenvC' tenv' st' cenv2 (Rval (envM2,envE2)))) ∨
    (?err mods.
      err ≠ Rabort Rtype_error ∧
      mods ⊆ decls1'.defined_mods ∧
      evaluate_prog F env st prog (st',cenv2,Rerr err))`,
 srw_tac[][evaluate_whole_prog_def] >>
 imp_res_tac prog_type_soundness >>
 full_simp_tac(srw_ss())[]
 >- (MAP_EVERY qexists_tac [`cenv2`, `st'`] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`envM2`, `envE2`] >>
     simp [] >>
     full_simp_tac(srw_ss())[type_sound_invariants_def] >>
     imp_res_tac type_no_dup_mods >>
     imp_res_tac type_no_dup_top_types >>
     full_simp_tac(srw_ss())[] >>
     rev_full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[no_dup_mods_def, no_dup_top_types_def]) >>
 metis_tac []);
 *)

val prim_type_sound_invariants = Q.store_thm("prim_type_sound_invariants",
  `(sem_st,sem_env) = THE (prim_sem_env ffi) ⇒
   type_sound_invariants (NONE:(unit,v) semanticPrimitives$result option) (prim_tdecs,prim_tenv,sem_st,sem_env)`,
  rw[type_sound_invariants_def,
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
  \\ qexists_tac`FEMPTY` \\ simp[]
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
