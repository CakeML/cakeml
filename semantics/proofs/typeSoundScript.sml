open preamble;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory evaluateTheory;
open terminationTheory;
open namespacePropsTheory;
open semanticPrimitivesPropsTheory;
open evaluatePropsTheory;
open weakeningTheory typeSysPropsTheory typeSoundInvariantsTheory;
open semanticsTheory;
local open primSemEnvTheory in end;

val _ = new_theory "typeSound";

val list_rel_flat = Q.store_thm ("list_rel_flat",
  `!R l1 l2. LIST_REL (LIST_REL R) l1 l2 ⇒ LIST_REL R (FLAT l1) (FLAT l2)`,
 Induct_on `l1`
 >> rw [FLAT]
 >> rw [FLAT]
 >> irule EVERY2_APPEND_suff
 >> rw []);

val fst_triple = Q.prove (
`(\(x,y,z). x) = FST`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

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
 srw_tac[][type_env_component_equality]);

val has_lists_v_to_list = Q.prove (
`!ctMap tvs tenvS t3.
  ctMap_has_lists ctMap ∧
  type_v tvs ctMap tenvS v (Tapp [t3] (TC_name (Short "list")))
  ⇒
  ?vs. v_to_list v = SOME vs ∧
  (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
  (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str)`,
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
 srw_tac[][v_to_list_def,v_to_char_list_def,vs_to_string_def] >>
 full_simp_tac(srw_ss())[type_subst_def] >>
 rename1 `type_v _ _ _ v _` >>
 LAST_X_ASSUM (mp_tac o Q.SPEC `v`) >>
 srw_tac[][v_size_def, basicSizeTheory.option_size_def, basicSizeTheory.pair_size_def,
     namespaceTheory.id_size_def, list_size_def, tid_or_exn_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 res_tac >> srw_tac[][] >>
 full_simp_tac(srw_ss())[flookup_fupdate_list] >> srw_tac[][] >> full_simp_tac(srw_ss())[GSYM Tchar_def] >>
 simp [GSYM PULL_EXISTS] >>
 rw [] >>
 TRY (
   qmatch_goalsub_rename_tac`vs_to_string (v1::_)`
   \\ qpat_x_assum`type_v _ _ _ v1 _`mp_tac
   \\ simp[Once type_v_cases,Tstring_def,Tchar_def]
   \\ strip_tac \\ simp[vs_to_string_def]
   \\ imp_res_tac type_funs_Tfn \\ fs[]
   \\ fs[tid_exn_to_tc_def]
   \\ every_case_tac \\ fs[] \\ NO_TAC) \\
 qpat_x_assum`type_v _ _ _ _ Tchar`mp_tac >>
 simp[Once type_v_cases,Tchar_def] >>
 srw_tac[][] >> srw_tac[][v_to_char_list_def] >>
 TRY (
   full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
   qpat_x_assum`TC_char = X`mp_tac >>
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
 qmatch_goalsub_abbrev_tac`_ v = SOME _` >>
 imp_res_tac has_lists_v_to_list >>
 first_x_assum(qspec_then`v`mp_tac) >>
 simp[Once type_v_cases,Tchar_def,Abbr`v`,tid_exn_to_tc_def] >>
 rw[] >> metis_tac[]);

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
 ONCE_REWRITE_TAC [type_v_cases] >>
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
 >- (full_simp_tac(srw_ss())[Once type_v_cases] >>
     full_simp_tac(srw_ss())[Once type_v_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (rpt (qpat_x_assum `type_v x0 x1 x2 x3 x4` mp_tac) >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     ONCE_REWRITE_TAC [type_v_cases] >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[combinTheory.o_DEF, EVERY_LIST_REL] >>
     `(\x y. type_v tvs ctMap tenvS x y) = type_v tvs ctMap tenvS` by metis_tac [] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (FULL_CASE_TAC \\
     full_simp_tac(srw_ss())[bool_case_eq]
     \\ metis_tac[]));

val type_env_conv_thm = Q.prove (
  `∀ctMap envC tenvC.
     nsAll2 (type_ctor ctMap) envC tenvC ⇒
     ∀cn tvs ts tn.
       (nsLookup tenvC cn = SOME (tvs,ts,tn) ⇒
        nsLookup envC cn = SOME (LENGTH ts,tn) ∧
        FLOOKUP ctMap (id_to_n cn,tn) = SOME (tvs, ts)) ∧
       (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)`,
 rw []
 >> imp_res_tac nsAll2_nsLookup2
 >> TRY (PairCases_on `v1`)
 >> fs [type_ctor_def]
 >> metis_tac [nsAll2_nsLookup_none]);

val type_funs_fst = Q.prove (
`!tenv tenvE funs tenv'.
  type_funs tenv tenvE funs tenv'
  ⇒
  MAP FST funs = MAP FST tenv'`,
 induct_on `funs` >>
 srw_tac[][] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
 srw_tac[][] >>
 srw_tac[][] >>
 metis_tac []);

val type_recfun_env_help = Q.prove (
`∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
  ALL_DISTINCT (MAP FST funs') ∧
  tenv_ok tenv ∧
  type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
  tenv_val_exp_ok tenvE ∧
  num_tvs tenvE = 0 ∧
  (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
  type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
  type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
  ⇒
  LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
    (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
    (MAP (λ(x,t). (x,tvs,t)) bindings)`,
 induct_on `funs`
 >> srw_tac[][]
 >> pop_assum mp_tac
 >> simp [Once type_e_cases]
 >> rw []
 >> rw []
 >- (
   simp [Once type_v_cases]
   >> qexists_tac `tenv`
   >> qexists_tac `tenvE`
   >> rw []
   >> fs [type_all_env_def]
   >> simp []
   >> qexists_tac `bindings'`
   >> rw []
   >> imp_res_tac type_funs_fst
   >> fs []
   >> first_x_assum (qspec_then `fn` mp_tac)
   >> rw []
   >> drule ALOOKUP_MEM
   >> rw [MEM_MAP]
   >> metis_tac [FST])
 >- (
   first_x_assum irule
   >> simp []
   >> qexists_tac `bindings'`
   >> qexists_tac `tenv`
   >> qexists_tac `tenvE`
   >> simp []
   >> rw []
   >> fs []
   >> metis_tac [SOME_11, NOT_SOME_NONE]));

val type_recfun_env = Q.prove (
`∀funs ctMap tenvS tvs tenv tenvE env bindings.
  tenv_ok tenv ∧
  type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
  tenv_val_exp_ok tenvE ∧
  num_tvs tenvE = 0 ∧
  type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
  ALL_DISTINCT (MAP FST funs)
  ⇒
  LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
    (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
    (MAP (λ(x,t). (x,tvs,t)) bindings)`,
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
 >- full_simp_tac(srw_ss())[Once type_v_cases] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_x_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases] >>
 res_tac >>
 full_simp_tac(srw_ss())[ctMap_has_lists_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_subst_def, flookup_fupdate_list]
 >- metis_tac [type_v_weakening, weakCT_refl, weakS_refl] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 res_tac >>
 FIRST_X_ASSUM (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][]);

val v_to_char_list_type = Q.prove (
`!v vs.
  ctMap_has_lists ctMap ∧
  v_to_char_list v = SOME vs ∧
  type_v 0 ctMap tenvS v (Tapp [t] (TC_name (Short "list")))
  ⇒
  type_v tvs ctMap tenvS (Litv (StrLit (IMPLODE vs))) (Tstring)`,
 ho_match_mp_tac v_to_char_list_ind >>
 srw_tac[][v_to_char_list_def]
 >- full_simp_tac(srw_ss())[Once type_v_cases] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_x_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases]);

val type_v_Boolv = Q.prove(
  `ctMap_has_bools ctMap ⇒
    type_v tvs ctMap tenvS (Boolv b) (Tapp [] (TC_name (Short "bool")))`,
  srw_tac[][Boolv_def] >>
  srw_tac[][Once type_v_cases,tid_exn_to_tc_def,LENGTH_NIL] >>
  full_simp_tac(srw_ss())[ctMap_has_bools_def] >>
  srw_tac[][Once type_v_cases]);

val remove_lambda_prod = Q.prove (
`(\(x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

val opapp_type_sound = Q.store_thm ("opapp_type_sound",
`!ctMap tenvS vs ts t.
 type_op Opapp ts t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs ts
 ⇒
 ?env e tenv tenvE.
   tenv_ok tenv ∧
   tenv_val_exp_ok tenvE ∧
   num_tvs tenvE = 0 ∧
   type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
   type_e tenv tenvE e t ∧
   do_opapp vs = SOME (env,e)`,
 rw [type_op_cases]
 >> fs []
 >> rw []
 >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def] canonical_values_thm)
 >> rw [do_opapp_def]
 >- (
   rename1 `type_v _ _ _ (Closure env n e) _`
   >> qpat_x_assum `type_v _ _ _ (Closure env n e) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> qexists_tac `tenv`
   >> qexists_tac `Bind_name n 0 t2 (bind_tvar 0 tenvE)`
   >> rw []
   >> fs [tenv_ok_def, type_all_env_def, tenv_val_exp_ok_def, bind_tvar_def]
   >> simp [add_tenvE_def]
   >> irule nsAll2_nsBind
   >> simp [])
 >- (
   rename1 `type_v _ _ _ (Recclosure env funs n) _`
   >> qpat_x_assum `type_v _ _ _ (Recclosure env funs n) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> imp_res_tac type_funs_find_recfun
   >> fs []
   >> rw []
   >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def] type_recfun_lookup)
   >> fs []
   >> qmatch_assum_abbrev_tac `type_e _ b _ _`
   >> qexists_tac `tenv`
   >> qexists_tac `b`
   >> fs [type_all_env_def]
   >> unabbrev_all_tac
   >> rw [tenv_val_exp_ok_def, add_tenvE_def]
   >- metis_tac [type_v_freevars]
   >- (
     irule tenv_val_exp_ok_bvl_funs
     >> simp []
     >> metis_tac [])
   >- (
     irule nsAll2_nsBind
     >> simp [build_rec_env_merge, nsAppend_to_nsBindList, add_tenvE_bvl]
     >> irule nsAll2_nsBindList
     >> simp []
     >> irule type_recfun_env
     >> simp [type_all_env_def]
     >> metis_tac [])
   >- (
     simp [remove_lambda_prod]
     >> metis_tac [])));

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
  type_s ctMap store tenvS ∧
  FLOOKUP tenvS l = SOME st ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store'.
    store_assign l sv store = SOME store' ∧
    type_s ctMap store' tenvS`,
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
  type_s ctMap store tenvS ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store' tenvS' n.
    store_type_extension tenvS tenvS' ∧
    store_alloc sv store = (store', n) ∧
    type_s ctMap store' tenvS' ∧
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
  type_s ctMap store tenvS ∧
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
 type_s ctMap store tenvS ∧
 type_op op ts t ∧
 check_freevars 0 [] t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort _) => F`,
 rw [type_op_cases, good_ctMap_def]
 >> fs []
 >> rw []
 >> TRY (Cases_on `wz`)
 >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def, Tref_def] canonical_values_thm)
 >> rw [do_app_cases, PULL_EXISTS]
 >> TRY ( (* ref alloc *)
   rename1 `Tapp [_] TC_ref`
   >> simp [Once type_v_cases]
   >> rename1 `type_v _ _ _ v t`
   >> `type_sv ctMap tenvS (Refv v) (Ref_t t)` by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [type_v_freevars])
 >> TRY ( (* deref *)
   qpat_x_assum `type_v _ _ _ (Loc n) (Tapp [_] TC_ref)` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> rename1 `type_sv _ _ sv _`
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* W8array length *)
   qpat_x_assum `type_v _ _ _ (Loc _) (Tapp [] TC_word8array)` mp_tac
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
 >> TRY ( (* Int to Char *)
   rename1`prim_exn "Chr"`
   >> rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> Cases_on `n < 0 ∨ n > 255`
   >> rw []
   >> rw []
   >> simp [type_v_exn, prim_exn_def]
   >> fs []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* string concat *)
   rename1`vs_to_string`
   \\ simp[Once type_v_cases]
   \\ imp_res_tac has_lists_v_to_list
   \\ fs[Tstring_def]
   \\ rveq \\ fs[]
   \\ metis_tac[store_type_extension_refl] )
 >> TRY ( (* list to vector *)
   rename1`Vectorv _`
   >> metis_tac [v_to_list_type, store_type_extension_refl])
 >> TRY ( (* Array length *)
   qpat_x_assum `type_v _ _ _ (Loc _) (Tapp [_] TC_array)` mp_tac
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
 >> TRY ( (* FFI call *)
   rename1`call_FFI`
   >> qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule store_lookup_type_sound
   >> disch_then drule
   >> rw []
   >> Cases_on `sv`
   >> fs [type_sv_def]
   >> rename [`MAP _ conf`]
   >> `?ffi' ws'. call_FFI ffi n (MAP (λc. n2w (ORD c)) conf) l = (ffi', ws')` by metis_tac [pair_CASES]
   >> simp []
   >> `type_sv ctMap tenvS (W8array ws') W8array_t` by rw [type_sv_def]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Integer ops *)
   rename1 `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >> Cases_on `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >- (
     fs []
     >> metis_tac [type_v_exn, store_type_extension_refl, prim_exn_def])
   >- (
     fs []
     >> simp [Once type_v_cases]
     >> metis_tac [store_type_extension_refl]))
 >> TRY ( (* Boolean ops *)
   rename1`opb_lookup` >>
   metis_tac [type_v_Boolv, store_type_extension_refl])
 >> TRY ( (* Word8 ops *)
   rename1`opw8_lookup`
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Word64 ops *)
   rename1`opw64_lookup`
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* FP cmp *)
   rename1`fp_cmp` >>
   metis_tac[type_v_Boolv,store_type_extension_refl])
 >> TRY ( (* FP uop *)
   rename1`fp_uop`>>
   simp[Once type_v_cases]>>
   metis_tac [store_type_extension_refl])
 >> TRY ( (* FP bop *)
   rename1`fp_bop`>>
   simp[Once type_v_cases]>>
   metis_tac [store_type_extension_refl])
 >> TRY ( (* Equality *)
   rename1`do_eq`
   >> metis_tac [type_v_Boolv, store_type_extension_refl, eq_result_nchotomy, eq_same_type])
 >> TRY ( (* ref update *)
   qmatch_asmsub_rename_tac`Tapp [_] TC_ref`
   >> simp [Once type_v_cases]
   >> qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> metis_tac [type_sv_def, store_type_extension_refl, store_assign_type_sound])
 >> TRY ( (* W8array alloc *)
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
 >> TRY ( (* W8array lookup *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
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
 >> TRY ( (* string lookup *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> rename1 `type_v _ _ _ (Litv (StrLit s)) _`
   >> Cases_on `n < 0`
   >> rw [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> Cases_on `Num (ABS n) ≥ LENGTH s`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> qpat_x_assum `type_v _ _ _ (Litv (StrLit _)) _` mp_tac
   >> simp [Once type_v_cases, EVERY_EL]
   >> simp[Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* vector lookup *)
   rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> rename1 `type_v _ _ _ (Vectorv vs) _`
   >> Cases_on `n < 0`
   >> rw [type_v_exn, prim_exn_def]
   >- metis_tac [store_type_extension_refl]
   >> Cases_on `Num (ABS n) ≥ LENGTH vs`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> qpat_x_assum `type_v _ _ _ (Vectorv _) _` mp_tac
   >> simp [Once type_v_cases, EVERY_EL]
   >> rw []
   >> fs []
   >> `Num (ABS n) < LENGTH vs` by decide_tac
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Array alloc *)
   qpat_x_assum `type_v _ _ _ _ (Tapp [] TC_int)` mp_tac
   >> rename1`REPLICATE`
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
 >> TRY ( (* Empty array alloc *)
   rename1`Tapp [t1] TC_array` >>
   `type_sv ctMap tenvS (Varray []) (Varray_t t1)`
     by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> fs [check_freevars_def]
   >> rename1 `type_v _ _ _ v (Tapp [] TC_tup)`
   >> `v = Conv NONE []`
     by (
       qpat_x_assum `type_v _ _ _ _ (Tapp [] TC_tup)` mp_tac >>
       simp [Once type_v_cases] >>
       rw [Tchar_def, tid_exn_to_tc_def]
       >- (Cases_on `tn` >> fs []) >>
       imp_res_tac type_funs_Tfn >>
       fs [])
   >> metis_tac [store_type_extension_refl, type_v_freevars])
 >> TRY ( (* Array lookup *)
   qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
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
 >> TRY ( (* copy string *)
   rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn,prim_exn_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   >- metis_tac[store_type_extension_refl] )
 >> TRY ( (* copy byte array *)
   rename1`copy_array`
   \\ qpat_x_assum`type_v _ _ _ (Loc _) _`mp_tac
   \\ simp[Once type_v_cases]
   \\ strip_tac
   \\ imp_res_tac store_lookup_type_sound \\ fs[] \\ rw[]
   \\ rename1`store_lookup _ _ = SOME sv`
   \\ Cases_on`sv` \\ TRY(fs[type_sv_def] \\ NO_TAC)
   \\ simp[]
   \\ TRY (
     qpat_x_assum`type_v _ _ _ (Loc _) _`mp_tac
     \\ simp[Once type_v_cases]
     \\ strip_tac
     \\ imp_res_tac store_lookup_type_sound \\ fs[] \\ rw[]
     \\ rename1`store_lookup _ _ = SOME sv`
     \\ Cases_on`sv` \\ TRY(fs[type_sv_def] \\ NO_TAC) )
   \\ simp[]
   \\ rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn,prim_exn_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   \\ TRY (
     qmatch_goalsub_rename_tac`store_assign _ (W8array xx)`
     \\ `type_sv ctMap tenvS (W8array xx) W8array_t` by simp[type_sv_def])
   >- metis_tac[store_type_extension_refl,store_assign_type_sound] )
 >> TRY ( (* W8array assignment *)
   qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
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
 >> TRY ( (* Array update *)
   qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
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
   >> rename1`FLOOKUP _ _ = SOME (Varray_t t)`
   >> `type_sv ctMap tenvS (Varray (LUPDATE x (Num (ABS n)) vs)) (Varray_t t)`
     by (
       rw [type_sv_def]
       >> irule IMP_EVERY_LUPDATE
       >> simp [])
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> (
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl]));

val build_conv_type_sound = Q.store_thm ("build_conv_type_sound",
`!envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' (tid_exn_to_tc tn))`,
 rw []
 >> drule do_con_check_build_conv
 >> disch_then (qspec_then `REVERSE vs` mp_tac)
 >> rw []
 >> qexists_tac `v`
 >> rw []
 >> drule type_env_conv_thm
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
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings)))`,
 ho_match_mp_tac pmatch_ind
 >> rw [pmatch_def]
 >> TRY (qpat_x_assum `type_p _ _ _ _ _` mp_tac
         >> simp [Once type_p_cases])
 >> rw []
 >> rw [bind_var_list_def]
 >- pat_sound_tac
 >- (
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule type_env_conv_thm
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
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
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
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
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
   qpat_x_assum `type_ps _ _ (_::_) _ _` mp_tac
   >> simp [Once type_p_cases]
   >> rw []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> rw []
   >> rw []
   >> fs []
   >> REWRITE_TAC [GSYM APPEND_ASSOC]
   >> first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- pat_sound_tac
 >- pat_sound_tac);

val lookup_var_sound = Q.store_thm ("lookup_var_sound",
  `!n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)`,
 rw [lookup_var_def, type_all_env_def]
 >> `nsLookup (add_tenvE tenvE tenv.v) n = SOME (LENGTH targs, t)`
   suffices_by (
     rw []
     >> imp_res_tac nsAll2_nsLookup2
     >> fs []
     >> rw []
     >> irule (GEN_ALL type_subst)
     >> simp []
     >> drule type_v_freevars
     >> rw [])
 >> fs [lookup_varE_def]
 >> every_case_tac
 >> fs []
 >- metis_tac [nsLookup_add_tenvE2]
 >- (
   irule nsLookup_add_tenvE1
   >- metis_tac []
   >> fs [tenv_val_exp_ok_def]
   >> metis_tac [tveLookup_freevars])
 >- metis_tac [nsLookup_add_tenvE3]);

val exp_type_sound = Q.store_thm ("exp_type_sound",
 `(!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v (Tapp [] TC_exn) ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort Rtype_error) => F)`,
 ho_match_mp_tac evaluate_ind
 >> simp [evaluate_def, type_es_list_rel, GSYM CONJ_ASSOC, good_ctMap_def]
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
   >> `type_all_env ctMap new_tenvS env (tenv with v := add_tenvE tenvE tenv.v)`
     by metis_tac [store_type_extension_weakS, type_all_env_weakening, weakCT_refl]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS, GSYM CONJ_ASSOC]
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `r2`
   >> fs []
   >> rw []
   >> metis_tac [store_type_extension_trans, store_type_extension_weakS,
                 weakCT_refl, type_all_env_weakening, type_v_weakening])
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
     rename1`type_v 0 ctMap tenvS' _ _` >>
     `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
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
   qpat_x_assum `type_e _ _ (Con _ _) _` mp_tac
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
     >> fs [type_all_env_def]
     >> drule build_conv_type_sound
     >> rpt (disch_then drule)
     >> simp []
     >> rpt (disch_then drule)
     >> simp []
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
   >> fs [do_con_check_def, type_all_env_def]
   >> imp_res_tac type_env_conv_thm
   >> fs []
   >> imp_res_tac type_es_length
   >> fs [])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> drule lookup_var_sound
   >> rpt (disch_then drule)
   >> rw []
   >> fs [is_value_def]
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> simp [Once type_v_cases]
   >> fs [is_value_def, num_tvs_def, bind_tvar_def, type_all_env_def]
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
       >> rename1 `type_e tenv' tenvE' e t`
       >> rename1 `type_s _ _ tenvS'`
       >> disch_then (qspecl_then [`0`, `tenvS'`, `t`] mp_tac)
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
       rename1`type_s _ _ tenvS'` >>
       `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
         by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
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
       rename1`type_s _ _ tenvS'` >>
       `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
         by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
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
     >> rename1`type_s _ _ tenvS'`
     >> Cases_on `b`
     >> fs [do_if_def, Boolv_def]
     >> rw []
     >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
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
     >> rename1`type_s _ _ tenvS'`
     >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
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
     rename1 `type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2` >>
     rename1 `type_s _ _ tenvS'`
     >> qabbrev_tac `env' = nsOptBind n (HD [x]) env.v`
     >> qabbrev_tac `tenv' = opt_bind_name n 0 t1 tenvE`
     >> drule type_v_freevars
     >> rw []
     >> `tenv_val_exp_ok tenv'`
       by (Cases_on `n` >> fs [opt_bind_name_def, tenv_val_exp_ok_def, Abbr `tenv'`] >> NO_TAC)
     >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> simp [PULL_EXISTS]
     >> disch_then (qspecl_then [`0`] mp_tac)
     >> `num_tvs tenv' = 0`
       by (Cases_on `n` >> fs [opt_bind_name_def, Abbr `tenv'`] >> NO_TAC)
     >> simp []
     >> `type_all_env ctMap tenvS' (env with v := env') (tenv with v := add_tenvE tenv' tenv.v)`
       by (
         fs [type_all_env_def, Abbr `env'`, Abbr `tenv'`]
         >> Cases_on `n`
         >> fs [opt_bind_name_def, namespaceTheory.nsOptBind_def, add_tenvE_def]
         >> irule nsAll2_nsBind
         >> simp [])
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
   >> qexists_tac `tenv`
   >> qexists_tac `bind_var_list 0 bindings (bind_tvar tvs tenvE)`
   >> simp []
   >> rfs [build_rec_env_merge, bind_tvar_def, tenv_ok_def]
   >> rw []
   >- (
     irule tenv_val_exp_ok_bvl_funs
     >> simp []
     >> metis_tac [])
   >> fs [type_all_env_def]
   >> simp [build_rec_env_merge, nsAppend_to_nsBindList, add_tenvE_bvl]
   >> irule nsAll2_nsBindList
   >> simp []
   >> irule type_recfun_env
   >> simp [type_all_env_def]
   >> fs [fst_triple]
   >> metis_tac [tenv_ok_def])
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
   >> qpat_x_assum `type_v _ _ _ _ (Tapp [] TC_exn)` mp_tac
   >> drule (hd (CONJUNCTS pat_type_sound))
   >> fs [type_all_env_def]
   >> rpt (disch_then drule)
   >> disch_then (qspecl_then [`[]`, `[]`] mp_tac)
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> metis_tac [])
   >- (
     `tenv_val_exp_ok (bind_var_list tvs bindings tenvE)`
       by metis_tac [type_p_bvl]
     >> rename1`pmatch _ _ _ _ _ = Match bindings'`
     >> `nsAll2 (λi v (tvs,t). type_v tvs ctMap tenvS v t)
           (nsAppend (alist_to_ns bindings') env.v)
           (add_tenvE (bind_var_list tvs bindings tenvE) tenv.v)`
       by (
         simp [nsAppend_to_nsBindList, add_tenvE_bvl]
         >> irule nsAll2_nsBindList
         >> simp []
         >> fs [LIST_REL_EL_EQN]
         >> rw []
         >> rfs []
         >> first_x_assum drule
         >> rpt (pairarg_tac >> simp [])
         >> fs []
         >> rfs [EL_MAP])
     >> first_x_assum drule
     >> simp []
     >> rpt (disch_then drule)
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
    `type_all_env ctMap tenvS'' env tenv`
      by metis_tac [good_ctMap_def, type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
    >> fs [good_ctMap_def, type_all_env_def]
    >> drule (CONJUNCT1 pat_type_sound)
    >> rpt (disch_then drule)
    >> disch_then (qspecl_then [`[]`, `[]`] mp_tac)
    >> rw []
    >- ( (* No match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> rw [weakCT_refl, Bindv_def, type_v_exn]
      >> drule (hd (CONJUNCTS evaluate_state_unchanged))
      >> rw [empty_decls_def])
    >- ( (* match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> drule (CONJUNCT1 evaluate_state_unchanged)
      >> simp [weakCT_refl]
      >> simp [extend_dec_env_def, extend_dec_tenv_def]
      >> fs []
      >> strip_tac
      >> conj_asm1_tac
      >- (
        irule nsAll2_alist_to_ns
        >> fs [tenv_add_tvs_def, EVERY2_MAP, LAMBDA_PROD])
      >> rw [empty_decls_def]
      >> irule nsAll2_nsAppend
      >> simp []))
  >- ( (* An exception *)
    Cases_on `e'`
    >> fs []
    >- (
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> drule (CONJUNCT1 evaluate_state_unchanged)
      >> fs [weakCT_refl, type_all_env_def, good_ctMap_def]
      >> rw [empty_decls_def]
      >> irule nsAll2_mono
      >> qexists_tac `(λi v (tvs,t). type_v tvs ctMap tenvS v t)`
      >> rw []
      >> pairarg_tac
      >> fs []
      >> metis_tac [weakCT_refl, type_v_weakening, store_type_extension_weakS])
    >- metis_tac [weakCT_refl]);

val decs_type_sound_invariant_def = Define `
decs_type_sound_invariant mn st env tdecs1 ctMap tenvS tenv ⇔
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS ∧
  consistent_decls st.defined_types tdecs1 ∧
  consistent_ctMap tdecs1 ctMap ∧
  mn ∉ tdecs1.defined_mods`;

val decs_type_sound = Q.store_thm ("decs_type_sound",
 `∀mn (st:'ffi semanticPrimitives$state) env ds st' r tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_decs mn st env ds = (st',r) ∧
   type_ds F mn tdecs1 tenv ds tdecs1' tenv' ∧
   decs_type_sound_invariant mn st env tdecs1 ctMap tenvS tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       decs_type_sound_invariant mn st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       decs_type_sound_invariant mn st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> rw []
 >> TRY (qpat_x_assum `type_ds _ _ _ _ _ _ _` mp_tac >> simp [Once type_ds_cases])
 >> rw []
 >- ( (* case [] *)
   simp [extend_dec_env_def, extend_dec_tenv_def, type_all_env_def]
   >> metis_tac [store_type_extension_refl, weakCT_refl])
 >- ( (* case d1::d2::ds *)
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate_decs _ _ _ _ = (st1, r1)`
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
     >> fs []
     >> rw []
     >> rename1 `evaluate_decs _ _ (extend_dec_env env1 _) _ = (st2, r2)`
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> simp [combine_dec_result_def]
     >> rename[`weakCT ctMap1 ctMap`,`weakCT ctMap0 ctMap1`]
     >> qexists_tac `ctMap0`
     >> rename[`store_type_extenison tenvS tenvS0`,`store_type_extension tenvS0 tenvS1`]
     >> qexists_tac `tenvS1`
     >> rw []
     >- metis_tac [weakCT_trans]
     >- metis_tac [store_type_extension_trans]
     >> Cases_on `r2`
     >> fs []
     >- (
       fs [decs_type_sound_invariant_def, good_ctMap_def, extend_dec_env_def]
       >> fs [extend_dec_tenv_def, extend_dec_env_def]
       >> `type_all_env ctMap0 tenvS1 env1 tenv1`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS]
       >> fs [type_all_env_def]
       >> metis_tac [nsAll2_nsAppend])
     >- (
       Cases_on `e`
       >> fs []
       >> fs [decs_type_sound_invariant_def]
       >- metis_tac [type_all_env_weakening, weakCT_trans,
                     store_type_extension_weakS, store_type_extension_trans]))
   >- (
     rw []
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
       >> fs [decs_type_sound_invariant_def, extend_dec_tenv_def,
              type_all_env_def, extend_dec_env_def]
       >> rw []
       >- metis_tac [consistent_decls_weakening, union_decls_assoc, weak_decls_union2, type_ds_mod]
       >- metis_tac [consistent_ctMap_weakening, union_decls_assoc, weak_decls_union2, type_ds_mod]
       >- (
         drule type_ds_mod
         >> fs [union_decls_mods]))
     >- metis_tac []))
 >- ( (* case let *)
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (st1, r1)`
   >> drule (hd (CONJUNCTS exp_type_sound))
   >> fs [decs_type_sound_invariant_def]
   >> disch_then drule
   >> disch_then (qspec_then `Empty` mp_tac)
   >> simp [tenv_val_exp_ok_def, add_tenvE_def]
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
 >- ( (* case let, duplicate bindings *)
   fs [type_d_cases]
   >> fs [])
 >- ( (* case letrec *)
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw []
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> simp [weakCT_refl, store_type_extension_refl, build_rec_env_merge]
   >> fs [decs_type_sound_invariant_def]
   >> fs [extend_dec_env_def, extend_dec_tenv_def]
   >> reverse conj_asm1_tac
   >- (
     fs [type_all_env_def]
     >> irule nsAll2_nsAppend
     >> simp [])
   >> `type_all_env ctMap tenvS env (tenv with v := add_tenvE Empty tenv.v)`
     by rw [add_tenvE_def]
   >> drule type_recfun_env
   >> rpt (disch_then drule)
   >> simp [tenv_val_exp_ok_def]
   >> disch_then drule
   >> strip_tac
   >> fs [type_all_env_def, fst_triple]
   >> irule nsAll2_alist_to_ns
   >> rfs [EVERY2_MAP, tenv_add_tvs_def])
 >- ( (* case letrec duplicate bindings *)
   fs [type_d_cases]
   >> metis_tac [type_funs_distinct])
 >- ( (* case type definition *)
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw [extend_dec_env_def]
   >> fs [decs_type_sound_invariant_def, union_decls_mods]
   >> qmatch_assum_abbrev_tac `check_ctor_tenv new_tabbrev _`
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
     drule check_ctor_tenv_type_decs_to_ctMap
     >> rw []
     >> fs [type_all_env_def, build_tdefs_def, build_ctor_tenv_def]
     >> irule nsAll2_alist_to_ns
     >> simp [LIST_REL_REVERSE_EQ]
     >> irule list_rel_flat
     >> simp [EVERY2_MAP]
     >> simp [LIST_REL_EL_EQN]
     >> ntac 2 strip_tac
     >> pairarg_tac
     >> fs []
     >> ntac 2 strip_tac
     >> simp [EL_MAP]
     >> rpt (pairarg_tac >> fs [])
     >> rw [type_ctor_def, FLOOKUP_FUNION, namespaceTheory.id_to_n_def]
     >> fs [MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC]
     >> first_x_assum drule
     >> simp []
     >> disch_then drule
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
       >- fs [tenv_ok_def, Abbr`new_tabbrev`, extend_dec_tenv_def]
       >> metis_tac [ctMap_ok_type_decs])
     >> TRY (irule still_has_bools)
     >> TRY (irule still_has_exns)
     >> TRY (irule still_has_lists)
     >> simp []
     >> metis_tac [disjoint_image])
   >> conj_tac
   >- (
     `type_all_env (type_decs_to_ctMap mn new_tabbrev tds ⊌ ctMap) tenvS env tenv`
       by metis_tac [type_all_env_weakening, weakS_refl]
     >> fs [type_all_env_def, extend_dec_tenv_def]
     >> irule nsAll2_nsAppend
     >> simp [])
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
 >- ( (* case type def not distinct *)
   fs [type_d_cases]
   >> rw []
   >- metis_tac [check_ctor_tenv_def]
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
     >> Cases_on `mn`
     >> fs [namespaceTheory.mk_id_def]
     >> Cases_on `t`
     >> fs [namespaceTheory.mk_id_def]
     >> rw []
     >> fs [])
   >- fs [check_ctor_tenv_def, LAMBDA_PROD])
 >- ( (* case type abbrev *)
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw [extend_dec_env_def, extend_dec_tenv_def]
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> rw [weakCT_refl, store_type_extension_refl]
   >> fs [decs_type_sound_invariant_def, type_all_env_def])
 >- ( (* case bad exception *)
   fs [type_d_cases]
   >> rw []
   >> fs [decs_type_sound_invariant_def, consistent_decls_def, RES_FORALL]
   >> first_x_assum drule
   >> simp []
   >> CCONTR_TAC
   >> fs []
   >> Cases_on `mn`
   >> fs [namespaceTheory.mk_id_def]
   >> Cases_on `t`
   >> fs [namespaceTheory.mk_id_def])
 >- ( (* case exception *)
   drule type_d_tenv_ok
   >> fs [type_d_cases]
   >> rw []
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
     fs [type_all_env_def]
     >> simp [type_ctor_def, FLOOKUP_FUNION, namespaceTheory.id_to_n_def, FLOOKUP_UPDATE])
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
     qmatch_assum_abbrev_tac `weakCT ctMap' _`
     >> `type_all_env ctMap' tenvS env tenv`
       by metis_tac [type_all_env_weakening, weakS_refl]
     >> fs [type_all_env_def, extend_dec_tenv_def, extend_dec_env_def]
     >> irule nsAll2_nsBind
     >> simp [])
   >> conj_tac
   >- metis_tac [type_s_weakening, good_ctMap_def]
   >> conj_tac
   >- (
     irule consistent_decls_union
     >> simp []
     >> simp [consistent_decls_def, RES_FORALL])
   >- (
     irule consistent_ctMap_union
     >> simp []
     >> simp [consistent_ctMap_def, RES_FORALL])));

val type_sound_invariant_def = Define `
type_sound_invariant st env tdecs ctMap tenvS tenv ⇔
  ?tdecs_no_sig tenv_no_sig.
    decls_ok tdecs_no_sig ∧
    tenv_ok tenv ∧
    tenv_ok tenv_no_sig ∧
    good_ctMap ctMap ∧
    weak tenv_no_sig tenv ∧
    type_all_env ctMap tenvS env tenv_no_sig ∧
    type_s ctMap st.refs tenvS ∧
    weak_decls tdecs_no_sig tdecs ∧
    weak_decls_only_mods tdecs_no_sig tdecs ∧
    consistent_decls st.defined_types tdecs_no_sig ∧
    consistent_ctMap tdecs_no_sig ctMap ∧
    st.defined_mods ⊆ tdecs_no_sig.defined_mods`;

val tscheme_inst2_lemma = Q.prove (
  `(λid. tscheme_inst2 (Long mn id)) = tscheme_inst2`,
 rw [FUN_EQ_THM]
 >> PairCases_on `x`
 >> PairCases_on `x'`
 >> rw [tscheme_inst2_def]);

val tops_type_sound_no_extra_checks = Q.store_thm ("tops_type_sound_no_no_extra_checks",
 `∀(st:'ffi semanticPrimitives$state) env tops st' env' r tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_tops st env tops = (st',r) ∧
   type_prog F tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T`,
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   rw [extend_dec_env_def, extend_dec_tenv_def, type_all_env_def]
   >> metis_tac [weakCT_refl, store_type_extension_refl])
 >- (
   qpat_x_assum `type_prog F _ _ (_::_::_) _ _` mp_tac
   >> simp [Once type_prog_cases]
   >> rw []
   >> split_pair_case_tac
   >> rename1 `evaluate_tops st env [top1] = (st1, r1)`
   >> fs []
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
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
     >> rename1 `evaluate_tops _ _ (_::_) = (st2, r2)`
     >> Cases_on `r2`
     >> fs []
     >- (
       qexists_tac `ctMap2`
       >> qexists_tac `tenvS2`
       >> rw []
       >- metis_tac [weakCT_trans]
       >- metis_tac [store_type_extension_trans]
       (* >> `type_all_env ctMap2 tenvS2 a tenv1`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS] *)
       >> simp [combine_dec_result_def]
       >> fs [extend_dec_env_def, type_all_env_def, extend_dec_tenv_def]
       >> metis_tac [nsAll2_nsAppend])
     >- (
       simp [combine_dec_result_def]
       >> CASE_TAC
       >> fs []
       >- (
         qexists_tac `ctMap2`
         >> qexists_tac `tenvS2`
         >> rw []
         >- metis_tac [weakCT_trans]
         >- metis_tac [store_type_extension_trans]
         >> fs [type_sound_invariant_def]
         >> qexists_tac `tdecs_no_sig''`
         >> qexists_tac `tenv_no_sig`
         >> rw []
         >> metis_tac [type_all_env_weakening, weakCT_trans, store_type_extension_trans,
                       store_type_extension_weakS, good_ctMap_def])
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
       >> fs [type_sound_invariant_def]
       >> qexists_tac `union_decls decls2 tdecs_no_sig'`
       >> qexists_tac `tenv_no_sig'`
       >> simp []
       >> rw []
       >- metis_tac [decls_ok_union, type_prog_decls_ok]
       >> fs [SUBSET_DEF]
       >> metis_tac [weak_decls_union, union_decls_assoc, weak_decls_only_mods_union, consistent_ctMap_union2, consistent_decls_union2])
     >- metis_tac []))
 >- (
   fs [type_top_cases]
   >> rename1 `evaluate_decs _ _ _ [_] = (st1, r1)`
   >> fs []
   >> drule decs_type_sound
   >> fs [type_sound_invariant_def]
   >> `type_d F [] tdecs_no_sig tenv_no_sig d tdecs1' tenv'`
     by (
       irule type_d_weakening
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw []
       >> metis_tac [tenv_ok_def, weak_decls_other_mods_only_mods_NIL])
   >> disch_then drule
   >> `decs_type_sound_invariant [] st env tdecs_no_sig ctMap tenvS tenv_no_sig`
     by fs [decs_type_sound_invariant_def, tenv_ok_def, decls_ok_def]
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> rw []
     >> rename1 `type_all_env _ _ env' tenv'`
     >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
     >> qexists_tac `extend_dec_tenv tenv' tenv_no_sig`
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def, SUBSET_DEF]
     >> rw []
     >- (
       irule decls_ok_union
       >> simp []
       >> drule type_d_mod
       >> rw [decls_ok_def])
     >- metis_tac [type_d_tenv_ok]
     >- (
       fs [weak_def]
       >> rw []
       >- fs [extend_dec_tenv_def]
       >> irule weak_tenv_extend_dec_tenv
       >> simp []
       >> drule type_d_tenv_ok_helper
       >> fs [tenv_ok_def, extend_dec_tenv_def])
     >- metis_tac [weak_decls_union]
     >- metis_tac [weak_decls_only_mods_union]
     >- metis_tac [evaluate_decs_state_unchanged])
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
       >> qexists_tac `tenv_no_sig`
       >> fs [type_sound_invariant_def, decs_type_sound_invariant_def, SUBSET_DEF]
       >> rw []
       >- (
         irule decls_ok_union
         >> simp []
         >> drule type_d_mod
         >> rw [decls_ok_def])
       >- metis_tac [weak_decls_union]
       >- metis_tac [weak_decls_only_mods_union]
       >- metis_tac [evaluate_decs_state_unchanged])
     >- metis_tac []))
 >- (
   split_pair_case_tac
   >> rename1 `evaluate_decs _ _ _ _ = (st1, r1)`
   >> drule type_top_decls_ok
   >> fs [type_top_cases]
   >> rw []
   >> drule decs_type_sound
   >> fs [type_sound_invariant_def]
   >> `type_ds F [mn] tdecs_no_sig tenv_no_sig ds decls_impl tenv_impl`
     by (
       irule type_ds_weakening
       >> simp []
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw []
       >> irule weak_decls_other_mods_only_mods_SOME
       >> simp [])
   >> disch_then drule
   >> `decs_type_sound_invariant [mn] st env tdecs_no_sig ctMap tenvS tenv_no_sig`
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
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def]
     >> qexists_tac `union_decls (union_decls <|defined_mods := {[mn]}; defined_types := ∅; defined_exns := ∅ |> decls_impl) tdecs_no_sig`
     >> rename1 `type_all_env _ _ (extend_dec_env env' _) _`
     >> qexists_tac `extend_dec_tenv <| v := nsLift mn tenv_impl.v; c := nsLift mn tenv_impl.c; t := nsLift mn tenv_spec.t |> tenv_no_sig`
     >> simp [union_decls_mods]
     >> conj_asm1_tac
     >- (
       drule type_ds_decls_ok
       >> simp []
       >> metis_tac [decls_ok_union])
     >> conj_asm1_tac
     >- (
       drule check_signature_tenv_ok
       >> simp [tenvLift_def]
       >> disch_then irule
       >> simp []
       >> metis_tac [])
     >> conj_asm1_tac
     >- (
       drule type_ds_tenv_ok_helper
       >> simp []
       >> rw []
       >> irule extend_dec_tenv_ok
       >> simp []
       >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def, tenv_abbrev_ok_def]
       >> fs [check_signature_cases]
       >> drule type_specs_tenv_ok
       >> simp [tenv_abbrev_ok_def, tenv_ok_def])
     >> rw []
     >- (
       fs [weak_def]
       >> rw []
       >- fs [extend_dec_tenv_def, tenvLift_def]
       >> fs [check_signature_cases]
       >- (
         rw [tenvLift_def]
         >> irule weak_tenv_extend_dec_tenv
         >> simp [tenv_val_ok_def]
         >> drule type_ds_tenv_ok_helper
         >> rw [tenv_ok_def, tenv_val_ok_def])
       >> fs [weak_tenv_def, extend_dec_tenv_def, tenvLift_def]
       >> rw []
       >> irule nsSub_nsAppend_lift
       >> simp [tscheme_inst2_lemma, type_ctor_long]
       >- metis_tac []
       >> irule nsSub_refl
       >> qexists_tac `\x y. T`
       >> rw []
       >> PairCases_on `x`
       >> rw [weak_tenvT_def])
     >- (
       `type_all_env ctMap'' tenvS'' env tenv_no_sig`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS]
       >> rw [type_all_env_def, extend_dec_env_def, extend_dec_tenv_def]
       >> irule nsAll2_nsAppend
       >> simp []
       >> fs [type_all_env_def, type_ctor_long]
       >> metis_tac [])
     >- (
       fs [check_signature_cases]
       >> metis_tac [weak_decls_union3, weak_decls_union, weak_decls_trans])
       >- (
         fs [check_signature_cases]
         >- metis_tac [weak_decls_only_mods_union]
         >> rw_tac std_ss [GSYM union_decls_assoc]
         >> irule weak_decls_only_mods_union
         >> irule weak_decls_only_mods_union2
         >> simp []
         >> drule type_ds_weak_decls_only_mods
         >> simp [])
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
       >> qexists_tac `union_decls (union_decls <|defined_mods := {[mn]}; defined_types := ∅; defined_exns := ∅ |> decls_impl) tdecs_no_sig`
       >> qexists_tac `tenv_no_sig`
       >> simp [union_decls_mods]
       >> rw []
       >- (
         drule type_ds_decls_ok
         >> simp []
         >> metis_tac [decls_ok_union])
       >- (
         fs [check_signature_cases]
         >> metis_tac [weak_decls_union, weak_decls_trans, weak_decls_union3])
       >- (
         fs [check_signature_cases]
         >- metis_tac [weak_decls_only_mods_union]
         >> rw_tac std_ss [GSYM union_decls_assoc]
         >> irule weak_decls_only_mods_union
         >> irule weak_decls_only_mods_union2
         >> simp []
         >> drule type_ds_weak_decls_only_mods
         >> simp [])
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
 `∀(st:'ffi semanticPrimitives$state) env tops st' r checks tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_tops st env tops = (st',r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
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
 `∀(st:'ffi semanticPrimitives$state) env tops st' r checks tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_prog st env tops = (st',r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
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
   drule type_no_dup_mods
   >> fs [type_sound_invariant_def, no_dup_mods_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def])
 >- (
   drule type_no_dup_top_types
   >> fs [type_sound_invariant_def]
   >> rpt (disch_then drule)
   >> fs [no_dup_top_types_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def]));

val semantics_type_sound = Q.store_thm ("semantics_type_sound",
 `∀(st:'ffi semanticPrimitives$state) env tops st' new_ctors r checks tdecs1 ctMap tenvS tenv tdecs1' new_tenv.
   semantics_prog st env tops r ∧
   type_prog checks tdecs1 tenv tops tdecs1' new_tenv ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   r ≠ Fail`,
 rw []
 >> CCONTR_TAC
 >> fs [semantics_prog_def]
 >> Cases_on `evaluate_prog_with_clock st env k tops`
 >> fs []
 >> rw []
 >> fs [evaluate_prog_with_clock_def]
 >> pairarg_tac
 >> fs []
 >> rw []
 >> drule prog_type_sound
 >> disch_then drule
 >> simp []
 >> fs [type_sound_invariant_def]
 >> metis_tac []);

val prim_type_sound_invariants = Q.store_thm("prim_type_sound_invariants",
  `(sem_st,prim_env) = THE (prim_sem_env ffi) ⇒
   ?ctMap. type_sound_invariant sem_st prim_env prim_tdecs ctMap FEMPTY prim_tenv`,
  rw[type_sound_invariant_def,
     primSemEnvTheory.prim_sem_env_eq,primSemEnvTheory.prim_tdecs_def,primSemEnvTheory.prim_tenv_def]
  \\ EVAL_TAC \\ simp[]
  \\ simp[RES_FORALL]
  \\ srw_tac[DNF_ss][]
  \\ simp[FEVERY_ALL_FLOOKUP, tenv_abbrev_ok_def]
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
  \\ simp[primSemEnvTheory.prim_tdecs_def]
  \\ qexists_tac `<| v := nsEmpty;
                     c := alist_to_ns [
       ("false",[],[],TypeId(Short"bool"));
       ("true",[],[],TypeId(Short"bool"));
       ("::",["'a"],[Tvar "'a"; Tapp [Tvar "'a"] (TC_name (Short "list"))],TypeId(Short "list"));
       ("nil",["'a"],[],TypeId(Short "list"));
       ("Subscript",[],[],TypeExn (Short "Subscript"));
       ("Div",[],[],TypeExn (Short "Div"));
       ("Chr",[],[],TypeExn (Short "Chr"));
       ("Bind",[],[],TypeExn (Short "Bind"));
       ("NONE",["'a"],[],TypeId (Short "option"));
       ("SOME",["'a"],[Tvar "'a"],TypeId (Short "option"))];
                     t := nsEmpty |>`
  \\ simp [UNCURRY, namespaceTheory.id_to_mods_def]
  \\ EVAL_TAC \\ rw[]
  >> TRY (Cases_on `id`)
  >> TRY (Cases_on `path`)
  \\ TRY (
    qmatch_abbrev_tac`_ ≠ SOME _`
    \\ BasicProvers.TOP_CASE_TAC
    \\ rw[] \\ fs[])
  \\ rw[SUBSET_DEF] \\ fs[GSPECIFICATION, namespaceTheory.nsLookup_def, namespaceTheory.nsLookupMod_def]
  \\ EVAL_TAC
  >> pop_assum mp_tac
  >> rpt (CASE_TAC >> rw [] >> EVAL_TAC >> rw [namespaceTheory.id_to_n_def]));

val _ = export_theory ();
