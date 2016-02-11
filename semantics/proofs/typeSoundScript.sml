open preamble;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory;
open smallStepTheory bigStepTheory;
open terminationTheory;
open evalPropsTheory;
open weakeningTheory typeSysPropsTheory bigSmallEquivTheory;
open typeSoundInvariantsTheory evalPropsTheory;

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
 (!tn. tid_exn_to_tc tn ≠ TC_word8array) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_vector) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_array)`,
 srw_tac[][] >>
 cases_on `tn` >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
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
`∀tvs tenvC tenvS v t1 t2.
  (type_v tvs tenvC tenvS v (Tref t1) ⇒ (∃n. v = Loc n)) ∧
  (type_v tvs tenvC tenvS v Tint ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs tenvC tenvS v Tchar ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs tenvC tenvS v Tstring ⇒ (∃s. v = Litv (StrLit s))) ∧
  (ctMap_has_bools ctMap ∧ type_v tvs ctMap tenvS v (Tapp [] (TC_name (Short "bool"))) ⇒
   ∃b. v = Boolv b) ∧
  (type_v tvs tenvC tenvS v (Tfn t1 t2) ⇒
    (∃env n e. v = Closure env n e) ∨
    (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v Tword8 ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword8array ⇒ (∃n. v = Loc n)) ∧
  (!t3. ctMap_has_lists ctMap ∧ type_v tvs ctMap tenvS v (Tapp [t3] (TC_name (Short "list"))) ⇒
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
   imp_res_tac type_vs_length >>
   Cases_on`cn = "true"`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[LENGTH_NIL]>- metis_tac[] >>
   Cases_on`cn = "false"`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[LENGTH_NIL]>- metis_tac[] >>
   metis_tac[optionTheory.NOT_SOME_NONE]) >>
 imp_res_tac has_lists_v_to_list >>
 full_simp_tac(srw_ss())[] >>
 fsrw_tac[][GSYM PULL_EXISTS] >>
 fsrw_tac[boolSimps.DNF_ss][] >>
 first_x_assum match_mp_tac >>
 srw_tac[][Once type_v_cases_eqn, tid_exn_to_tc_def] >>
 metis_tac []);

val tac =
full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[deBruijn_subst_def, tid_exn_not] >>
imp_res_tac type_funs_Tfn >>
full_simp_tac(srw_ss())[Tchar_def] >>
metis_tac [tid_exn_not];

(* Well-typed pattern matches either match or not, but they don't raise type
 * errors *)
val pmatch_type_progress = Q.prove (
`(∀cenv st p v env t tenv tenvS tvs tvs'' tenvC ctMap.
  consistent_con_env ctMap cenv tenvC ∧
  type_p tvs'' tenvC p t tenv ∧
  type_v tvs ctMap tenvS v t ∧
  type_s ctMap tenvS st
  ⇒
  (pmatch cenv st p v env = No_match) ∨
  (∃env'. pmatch cenv st p v env = Match env')) ∧
 (∀cenv st ps vs env ts tenv tenvS tvs tvs'' tenvC ctMap.
  consistent_con_env ctMap cenv tenvC ∧
  type_ps tvs'' tenvC ps ts tenv ∧
  type_vs tvs ctMap tenvS vs ts ∧
  type_s ctMap tenvS st
  ⇒
  (pmatch_list cenv st ps vs env = No_match) ∨
  (∃env'. pmatch_list cenv st ps vs env = Match env'))`,
 ho_match_mp_tac pmatch_ind >>
 srw_tac[][] >>
 srw_tac[][pmatch_def] >>
 full_simp_tac(srw_ss())[lit_same_type_def]
 >- (full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[Tchar_def])
 >- (full_simp_tac(srw_ss())[Once type_v_cases_eqn, Once (hd (CONJUNCTS type_p_cases))] >>
     srw_tac[][] >>
     cases_on `lookup_alist_mod_env n cenv` >>
     srw_tac[][]
     >- (full_simp_tac(srw_ss())[consistent_con_env_def] >>
         metis_tac [NOT_SOME_NONE]) >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[] >>
     `∃tvs ts. lookup_alist_mod_env n tenvC = SOME (tvs,ts,x1) ∧
               FLOOKUP ctMap (id_to_n n, x1) = SOME (tvs,ts)` by metis_tac [consistent_con_env_def] >>
     full_simp_tac(srw_ss())[tid_exn_to_tc_11] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac same_ctor_and_same_tid >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[GSYM FUNION_alist_to_fmap]
     >- metis_tac []
     >- metis_tac [same_tid_sym]
     >- (full_simp_tac(srw_ss())[consistent_con_env_def] >>
         metis_tac [type_ps_length, type_vs_length, LENGTH_MAP, SOME_11, PAIR_EQ]))
 >- (qpat_assum `type_v b c d e f` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     qpat_assum `type_p b0 a b c d` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     every_case_tac >>
     srw_tac[][] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[Once type_p_cases, Once type_v_cases] >>
     srw_tac[][] >>
     imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[] >>
     cases_on `ts` >>
     full_simp_tac(srw_ss())[])
 >- (qpat_assum `type_v b c d e f` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     qpat_assum `type_p b0 a b c d` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     every_case_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[type_s_def] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- (qpat_assum `type_ps tvs tenvC (p::ps) ts tenv`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_vs tvs ctMap tenvS (v::vs) ts`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[] >>
     cases_on `ts` >>
     full_simp_tac(srw_ss())[])
 >- (imp_res_tac type_ps_length >> imp_res_tac type_vs_length >>
     full_simp_tac(srw_ss())[] >>
     cases_on `ts` >>
     full_simp_tac(srw_ss())[]));

val final_state_def = Define `
  (final_state (env,st,Val v,[]) = T) ∧
  (final_state (env,st,Val v,[(Craise (), err)]) = T) ∧
  (final_state _ = F)`;

val not_final_state = Q.prove (
`!menv cenv st env e c.
  ¬final_state (env,st,Exp e,c) =
    ((?x y. c = x::y) ∨
     (?e1. e = Raise e1) ∨
     (?e1 pes. e = Handle e1 pes) ∨
     (?l. e = Lit l) ∨
     (?cn es. e = Con cn es) ∨
     (?v. e = Var v) ∨
     (?x e'. e = Fun x e') \/
     (?op es. e = App op es) ∨
     (?op e1 e2. e = Log op e1 e2) ∨
     (?e1 e2 e3. e = If e1 e2 e3) ∨
     (?e' pes. e = Mat e' pes) ∨
     (?n e1 e2. e = Let n e1 e2) ∨
     (?funs e'. e = Letrec funs e'))`,
srw_tac[][] >>
cases_on `e` >>
cases_on `c` >>
srw_tac[][final_state_def]);

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

(* A well-typed expression state is either a value with no continuation, or it
 * can step to another state, or it steps to a BindError. *)
val exp_type_progress = Q.prove (
`∀dec_tvs ctMap st e t env c tenvS.
  type_state dec_tvs ctMap tenvS (env, st, e, c) t ∧
  ctMap_has_lists ctMap ∧
  ctMap_has_bools ctMap ∧
  ¬(final_state (env, st, e, c))
  ⇒
  (∃env' st' e' c'. e_step (env, st, e, c) = Estep (env', st', e', c'))`,
 srw_tac[][] >>
 srw_tac[][e_step_def] >>
 full_simp_tac(srw_ss())[type_state_cases, push_def, return_def] >>
 srw_tac[][]
 >- (full_simp_tac(srw_ss())[Once type_e_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[not_final_state] >|
     [srw_tac[][] >>
          every_case_tac >>
          full_simp_tac(srw_ss())[return_def] >>
          imp_res_tac type_es_length >>
          full_simp_tac(srw_ss())[] >>
          metis_tac [do_con_check_build_conv, NOT_SOME_NONE],
      full_simp_tac(srw_ss())[do_con_check_def] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          imp_res_tac consistent_con_env_thm >>
          full_simp_tac(srw_ss())[] >>
          imp_res_tac type_es_length >>
          full_simp_tac(srw_ss())[],
      full_simp_tac(srw_ss())[do_con_check_def] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          imp_res_tac consistent_con_env_thm >>
          srw_tac[][] >>
          every_case_tac >>
          full_simp_tac(srw_ss())[return_def] >>
          imp_res_tac type_es_length >>
          full_simp_tac(srw_ss())[build_conv_def],
      full_simp_tac(srw_ss())[do_con_check_def] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          imp_res_tac consistent_con_env_thm >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          metis_tac [type_es_length, LENGTH_MAP],
      imp_res_tac type_lookup_id >>
          full_simp_tac(srw_ss())[] >>
          every_case_tac >>
          metis_tac [NOT_SOME_NONE],
      every_case_tac >>
          srw_tac[][application_def] >>
          every_case_tac >>
          full_simp_tac(srw_ss())[do_app_def, type_op_def, LIST_REL_NIL, type_es_list_rel] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[],
      metis_tac [type_funs_distinct]])
 >- (srw_tac[][continue_def] >>
     full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, return_def, push_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[final_state_def] >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac (SIMP_RULE (srw_ss()) [] canonical_values_thm) >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][]
     >- (every_case_tac >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         full_simp_tac(srw_ss())[Once context_invariant_cases, final_state_def])
     >- (cases_on `es` >>
         srw_tac[][application_def] >>
         full_simp_tac(srw_ss())[type_op_cases, type_es_list_rel, type_vs_list_rel, LIST_REL_NIL] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac (SIMP_RULE (srw_ss()) [] canonical_values_thm) >>
         srw_tac[][do_opapp_def, do_app_def, return_def]
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[is_ccon_def] >>
             full_simp_tac(srw_ss())[Once type_v_cases] >>
             imp_res_tac type_funs_find_recfun >>
             full_simp_tac(srw_ss())[])
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[is_ccon_def] >>
             full_simp_tac(srw_ss())[Once type_v_cases] >>
             imp_res_tac type_funs_find_recfun >>
             full_simp_tac(srw_ss())[])
         >- (cases_on `do_eq v x` >>
             full_simp_tac(srw_ss())[Once context_invariant_cases] >>
             srw_tac [ARITH_ss] [] >>
             metis_tac [eq_same_type])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n) z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             simp[store_v_same_type_def] >>
             every_case_tac >> full_simp_tac(srw_ss())[])
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[store_alloc_def])
         >- (qpat_assum `type_v a ctMap senv (Loc n) z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[store_alloc_def])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n') z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[is_ccon_def, store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[LET_THM] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n) z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (
             full_simp_tac(srw_ss())[METIS_PROVE [REVERSE_REVERSE] ``REVERSE x = y ⇔ x = REVERSE y``] >>
             srw_tac[][] >>
             imp_res_tac (SIMP_RULE (srw_ss()) [] canonical_values_thm) >>
             srw_tac[][] >>
             qpat_assum `type_v a ctMap senv (Loc n''') z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[LET_THM] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             full_simp_tac(srw_ss())[store_v_same_type_def])
         >- every_case_tac
         >- srw_tac [boolSimps.DNF_ss] [markerTheory.Abbrev_def]
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[store_alloc_def])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n') z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[is_ccon_def, store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[LET_THM] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n) z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (
             full_simp_tac(srw_ss())[METIS_PROVE [REVERSE_REVERSE] ``REVERSE x = y ⇔ x = REVERSE y``] >>
             srw_tac[][] >>
             imp_res_tac (SIMP_RULE (srw_ss()) [] canonical_values_thm) >>
             srw_tac[][] >>
             qpat_assum `type_v a ctMap senv (Loc n''') z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[LET_THM] >>
             srw_tac[][] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             full_simp_tac(srw_ss())[store_v_same_type_def])
         >- (
             qpat_assum `type_v a ctMap senv (Loc n') z` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[store_assign_def, store_lookup_def] >>
             srw_tac[][] >>
             Cases_on `EL n' s` >>
             full_simp_tac(srw_ss())[] >>
             Cases_on `call_FFI tr n l` >>
             srw_tac[][]
             >- (every_case_tac >>
                 full_simp_tac(srw_ss())[LET_THM] >>
                 srw_tac[][] >>
                 full_simp_tac(srw_ss())[store_v_same_type_def])))
     >- (srw_tac[][do_log_def,Boolv_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[])
     >- (srw_tac[][do_if_def,Boolv_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[RES_FORALL] >>
         srw_tac[][] >>
         qpat_assum `∀x. (x = (q,r)) ∨ P x ⇒ Q x` (MP_TAC o Q.SPEC `(q,r)`) >>
         srw_tac[][] >>
         CCONTR_TAC >>
         full_simp_tac(srw_ss())[] >>
         metis_tac [pmatch_type_progress, match_result_distinct])
     >- (imp_res_tac consistent_con_env_thm >>
         full_simp_tac(srw_ss())[do_con_check_def] >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac type_es_length >>
         imp_res_tac type_vs_length >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,build_conv_def] >>
         `LENGTH ts2 = 0` by decide_tac >>
         cases_on `es` >>
         full_simp_tac(srw_ss())[])
     >- (full_simp_tac(srw_ss())[] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac consistent_con_env_thm >>
         imp_res_tac type_es_length >>
         imp_res_tac type_vs_length >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac consistent_con_env_thm >>
         imp_res_tac type_es_length >>
         imp_res_tac type_vs_length >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,build_conv_def])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac consistent_con_env_thm >>
         imp_res_tac type_es_length >>
         imp_res_tac type_vs_length >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,build_conv_def])));

(* A successful pattern match gives a binding environment with the type given by
* the pattern type checker *)
val pmatch_type_preservation = Q.prove (
`(∀(cenv : env_ctor) st p v env env' tenvC ctMap tenv t tenv' tenvS tvs.
  (pmatch cenv st p v env = Match env') ∧
  consistent_con_env ctMap cenv tenvC ∧
  type_v tvs ctMap tenvS v t ∧
  type_p tvs tenvC p t tenv' ∧
  type_s ctMap tenvS st ∧
  type_env ctMap tenvS env tenv ⇒
  type_env ctMap tenvS env' (bind_var_list tvs tenv' tenv)) ∧
 (∀(cenv : env_ctor) st ps vs env env' tenvC ctMap tenv tenv' ts tenvS tvs.
  (pmatch_list cenv st ps vs env = Match env') ∧
  consistent_con_env ctMap cenv tenvC ∧
  type_vs tvs ctMap tenvS vs ts ∧
  type_ps tvs tenvC ps ts tenv' ∧
  type_s ctMap tenvS st ∧
  type_env ctMap tenvS env tenv ⇒
  type_env ctMap tenvS env' (bind_var_list tvs tenv' tenv))`,
 ho_match_mp_tac pmatch_ind >>
 srw_tac[][pmatch_def]
 >- (full_simp_tac(srw_ss())[Once type_p_cases, bind_var_list_def] >>
     srw_tac[][] >>
     srw_tac[][Once type_v_cases] >>
     srw_tac[][])
 >- full_simp_tac(srw_ss())[Once type_p_cases, bind_var_list_def]
 >- (cases_on `lookup_alist_mod_env n cenv` >>
     full_simp_tac(srw_ss())[] >>
     PairCases_on `x` >>
     full_simp_tac(srw_ss())[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[] >>
     FIRST_X_ASSUM match_mp_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[Once type_v_cases_eqn, Once (hd (CONJUNCTS type_p_cases))] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[tid_exn_to_tc_11, consistent_con_env_def] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     imp_res_tac same_ctor_and_same_tid >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[GSYM FUNION_alist_to_fmap] >>
     metis_tac [])
 >- (cases_on `(LENGTH ps = x0) ∧ (LENGTH vs = x0)` >>
     full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[] >>
     qpat_assum `type_v tvs ctMap senv vpat t`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[Once type_p_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     cases_on `ps` >>
     full_simp_tac(srw_ss())[] >>
     qpat_assum `type_ps a0 a c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (full_simp_tac(srw_ss())[store_lookup_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     qpat_assum `type_p x1 x2 x3 x4 x5` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_v x1 x2 x3 x4 x5` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [consistent_con_env_def, type_v_weakening, weakCT_refl, weakS_refl, weakM_refl])
 >- full_simp_tac(srw_ss())[Once type_p_cases, bind_var_list_def]
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     qpat_assum `type_vs tva ctMap senv (v::vs) ts`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     full_simp_tac(srw_ss())[] >>
     qpat_assum `type_ps a0 a1 c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][bind_var_list_append] >>
     metis_tac []));

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
`∀fn funs ctMap tenvS tvs tenv tenv0 env bindings.
  tenv_mod_ok tenv.m ∧
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

val ctxt_inv_not_poly = Q.prove (
`!dec_tvs c tvs.
  context_invariant dec_tvs c tvs ⇒ ¬poly_context c ⇒ (tvs = 0)`,
ho_match_mp_tac context_invariant_ind >>
srw_tac[][poly_context_def] >>
cases_on `c` >>
full_simp_tac(srw_ss())[] >-
metis_tac [NOT_EVERY] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[] >>
cases_on `h0` >>
full_simp_tac(srw_ss())[] >>
metis_tac [NOT_EVERY]);

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

(* If a step can be taken from a well-typed state, the resulting state has the
* same type *)
val exp_type_preservation = Q.prove (
`∀dec_tvs ctMap st env e c t st' env' e' c' tenvS.
  ctMap_ok ctMap ∧
  ctMap_has_exns ctMap ∧
  ctMap_has_lists ctMap ∧
  ctMap_has_bools ctMap ∧
  type_state dec_tvs ctMap tenvS (env, st, e, c) t ∧
  (e_step (env, st, e, c) = Estep (env', st', e', c'))
  ⇒
  ∃tenvS'. type_state dec_tvs ctMap tenvS' (env', st', e', c') t ∧
          ((tenvS' = tenvS) ∨
           (?l t. (FLOOKUP tenvS l = NONE) ∧ (tenvS' = tenvS |+ (l,t))))`,
 srw_tac[][type_state_cases] >>
 full_simp_tac(srw_ss())[e_step_def] >>
 `check_freevars tvs [] t ∧ check_freevars tvs [] t1` by metis_tac [type_ctxts_freevars]
 >- (cases_on `e''` >>
     full_simp_tac(srw_ss())[push_def, is_value_def] >>
     srw_tac[][]
     >- (qpat_assum `type_e b1 c1 d1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases] >>
         srw_tac[][type_ctxt_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         metis_tac [check_freevars_def, EVERY_DEF])
     >- (qpat_assum `type_e b1 c1 d1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases] >>
         srw_tac[][type_ctxt_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[return_def] >>
         srw_tac[][] >>
         qpat_assum `type_e tenv (Lit l) t1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         srw_tac[][Once type_v_cases_eqn] >>
         metis_tac [])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[return_def] >>
         srw_tac[][]
         >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE] >>
         qpat_assum `type_e tenv (Con s'' epat) t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[SWAP_REVERSE_SYM, type_es_list_rel, type_vs_list_rel] >>
         srw_tac[][]
         >- (full_simp_tac(srw_ss())[build_conv_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             qexists_tac `tenvS` >>
             srw_tac[][] >>
             qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
             srw_tac[][] >>
             srw_tac[][Once type_v_cases] >>
             srw_tac[][Once type_v_cases] >>
             imp_res_tac consistent_con_env_thm >>
             full_simp_tac(srw_ss())[check_freevars_def] >>
             metis_tac [check_freevars_def, consistent_con_env_def])
         >- (full_simp_tac(srw_ss())[build_conv_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             qexists_tac `tenvS` >>
             srw_tac[][] >>
             qexists_tac `Tapp [] TC_tup` >>
             srw_tac[][] >>
             srw_tac[][Once type_v_cases] >>
             srw_tac[][Once type_v_cases] >>
             metis_tac [check_freevars_def])
         >- (full_simp_tac(srw_ss())[build_conv_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][PULL_EXISTS, Once type_ctxts_cases, type_ctxt_cases] >>
             srw_tac[][] >>
             ONCE_REWRITE_TAC [context_invariant_cases] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[type_es_list_rel, type_vs_list_rel, list_rel_split, GSYM
                 EVERY2_REVERSE1,MAP_EQ_APPEND, MAP_EQ_SING] >>
             srw_tac[][] >>
             MAP_EVERY qexists_tac [`tenvS`, `tenv`, `tvs`, `tenv`] >>
             simp [] >>
             MAP_EVERY qexists_tac [`REVERSE l10`, `ts'`] >>
             simp [] >>
             full_simp_tac(srw_ss())[GSYM FUNION_alist_to_fmap, MAP_REVERSE] >>
             full_simp_tac(srw_ss())[is_ccon_def] >>
             imp_res_tac ctxt_inv_not_poly >>
             srw_tac[][] >>
             res_tac >>
             full_simp_tac(srw_ss())[EVERY_REVERSE] >>
             metis_tac [check_freevars_def])
         >- (full_simp_tac(srw_ss())[build_conv_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][PULL_EXISTS, Once type_ctxts_cases, type_ctxt_cases] >>
             srw_tac[][] >>
             ONCE_REWRITE_TAC [context_invariant_cases] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[type_es_list_rel, type_vs_list_rel, list_rel_split, GSYM
                 EVERY2_REVERSE1,MAP_EQ_APPEND, MAP_EQ_SING] >>
             srw_tac[][] >>
             MAP_EVERY qexists_tac [`tenvS`, `y`, `tenv`, `tvs`, `tenv`] >>
             simp [] >>
             MAP_EVERY qexists_tac [`REVERSE l2'`] >>
             simp [] >>
             full_simp_tac(srw_ss())[GSYM FUNION_alist_to_fmap, MAP_REVERSE] >>
             full_simp_tac(srw_ss())[is_ccon_def] >>
             imp_res_tac ctxt_inv_not_poly >>
             srw_tac[][] >>
             res_tac >>
             full_simp_tac(srw_ss())[EVERY_REVERSE] >>
             full_simp_tac(srw_ss())[check_freevars_def] >>
             metis_tac []))
     >- (qexists_tac `tenvS` >>
         srw_tac[][] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[return_def] >>
         srw_tac[][] >>
         qexists_tac `t1` >>
         srw_tac[][] >>
         qpat_assum `type_e tenv (Var i) t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         qexists_tac `tvs` >>
         srw_tac[][] >>
         imp_res_tac type_v_freevars >>
         `num_tvs (bind_tvar tvs tenv.v) = tvs`
                  by (full_simp_tac(srw_ss())[bind_tvar_def] >>
                      cases_on `tvs` >>
                      full_simp_tac(srw_ss())[num_tvs_def]) >>
         metis_tac [type_lookup_type_v])
     >- (full_simp_tac(srw_ss())[return_def] >>
         srw_tac[][] >>
         qpat_assum `type_e tenv (Fun s'' e'') t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][] >>
         srw_tac[][bind_tvar_def, Once type_v_cases_eqn] >>
         full_simp_tac(srw_ss())[bind_tvar_def, check_freevars_def] >>
         metis_tac [check_freevars_def])
     >- (cases_on `REVERSE l` >>
         full_simp_tac(srw_ss())[]
         >- (full_simp_tac(srw_ss())[application_def] >>
             cases_on `o'` >>
             full_simp_tac(srw_ss())[do_app_def, do_opapp_def]) >>
         qpat_assum `type_e x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[SWAP_REVERSE_SYM, bind_tvar_def, check_freevars_def, type_es_list_rel, type_vs_list_rel] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[PULL_EXISTS, list_rel_split, GSYM EVERY2_REVERSE1] >>
         MAP_EVERY qexists_tac [`tenvS`, `y`, `tenv`, `tenv`, `t1`, `REVERSE l2'`] >>
         srw_tac[][] >>
         metis_tac [v_unchanged, arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,REVERSE_REVERSE,
                    num_tvs_def, type_v_freevars, tenv_val_ok_def, type_e_freevars])
     >- (qpat_assum `type_e x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         metis_tac [v_unchanged, type_e_freevars, type_v_freevars])
     >- (qpat_assum `type_e x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         metis_tac [v_unchanged, type_e_freevars, type_v_freevars])
     >- (qpat_assum `type_e x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         metis_tac [v_unchanged, type_e_freevars, type_v_freevars, type_v_exn])
     >- (qpat_assum `type_e x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         full_simp_tac(srw_ss())[bind_tvar_def]
         (* COMPLETENESS
         >- (qexists_tac `tenvS` >>
             srw_tac[][] >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `t1'` >>
             qexists_tac `tenv` >>
             qexists_tac `tvs` >>
             srw_tac[][] >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `tenv` >>
             qexists_tac `t1` >>
             srw_tac[][] >-
             metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                        num_tvs_def, type_v_freevars, tenv_val_ok_def,
                        type_e_freevars] >>
             full_simp_tac(srw_ss())[is_ccon_def] >>
             metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                        num_tvs_def, type_v_freevars, tenv_val_ok_def,
                        type_e_freevars])
                        *)
         >- (qexists_tac `tenvS` >>
             srw_tac[][] >>
             qexists_tac `t1'` >>
             qexists_tac `tenv` >>
             srw_tac[][] >>
             qexists_tac `0` >>
             srw_tac[][] >>
             qexists_tac `tenv` >>
             qexists_tac `t1` >>
             srw_tac[][] >>
             metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                        num_tvs_def, type_v_freevars, tenv_val_ok_def,
                        type_e_freevars, v_unchanged]))
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         qpat_assum `type_e tenv epat t1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][build_rec_env_merge] >>
         qexists_tac `tenvS` >>
         srw_tac[][] >>
         qexists_tac `t1` >>
         (* COMPLETENESS qexists_tac `bind_var_list tvs tenv' tenv` >>*)
         qexists_tac `tenv with v := bind_var_list 0 bindings tenv.v` >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[bind_tvar_def] >>
         qexists_tac `0` >>
         srw_tac[][] >>
         match_mp_tac type_env_merge_imp >>
         simp [] >>
         match_mp_tac type_recfun_env >>
         metis_tac [bind_tvar_def]))
 >- (full_simp_tac(srw_ss())[continue_def, push_def] >>
     cases_on `c` >>
     full_simp_tac(srw_ss())[] >>
     cases_on `h` >>
     full_simp_tac(srw_ss())[] >>
     cases_on `q` >>
     full_simp_tac(srw_ss())[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[return_def] >>
     srw_tac[][] >>
     qpat_assum `type_ctxts x1 x2 x3 x4 x5 x6` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >>
     full_simp_tac(srw_ss())[type_ctxt_cases] >>
     srw_tac[][] >>
     qpat_assum `context_invariant x0 x1 x2` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once context_invariant_cases]) >>
     full_simp_tac(srw_ss())[oneTheory.one]
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         cases_on `l` >>
         full_simp_tac(srw_ss())[RES_FORALL] >-
         metis_tac [] >>
         first_x_assum (qspec_then `h` assume_tac) >>
         full_simp_tac(srw_ss())[] >>
         PairCases_on `h` >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac type_e_freevars >>
         full_simp_tac(srw_ss())[] >>
         metis_tac [num_tvs_bind_var_list, type_v_freevars, tenv_val_ok_bind_var_list, type_p_freevars])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases, opt_bind_name_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac type_e_freevars >>
         full_simp_tac(srw_ss())[] >>
         metis_tac [opt_bind_name_def, tenv_val_ok_def, arithmeticTheory.ADD_0, num_tvs_def, type_e_freevars, type_v_freevars])
     >- (full_simp_tac(srw_ss())[Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         imp_res_tac type_e_freevars >>
         full_simp_tac(srw_ss())[] >>
         rev_full_simp_tac(srw_ss())[tenv_val_ok_def, num_tvs_def] >>
         metis_tac [bind_tvar_def, EVERY_DEF, type_e_freevars, type_v_freevars, check_freevars_def, EVERY_APPEND, EVERY_REVERSE])
     >- metis_tac []
     >- (full_simp_tac(srw_ss())[type_op_cases] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[application_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[do_app_cases, return_def, type_vs_list_rel, type_es_list_rel] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         SIMP_TAC (srw_ss()++boolSimps.DNF_ss) []
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac [])
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac [])
         >- (srw_tac[][Once context_invariant_cases, Once type_ctxts_cases, type_ctxt_cases] >>
             disj1_tac >>
             SIMP_TAC (srw_ss()++boolSimps.DNF_ss) [prim_exn_def] >>
             metis_tac [type_v_exn])
         >- (srw_tac[][Once context_invariant_cases, Once type_ctxts_cases, type_ctxt_cases] >>
             disj1_tac >>
             SIMP_TAC (srw_ss()++boolSimps.DNF_ss) [prim_exn_def] >>
             metis_tac [type_v_exn])
         >- ( metis_tac [type_v_Boolv])
         >- (full_simp_tac(srw_ss())[do_opapp_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][]
             >- (qpat_assum `type_v a ctMap senv (Closure l s' e0) t1'`
                    (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
                 full_simp_tac(srw_ss())[] >>
                 srw_tac[][] >>
                 srw_tac[][Once type_env_cases] >>
                 full_simp_tac(srw_ss())[bind_tvar_def] >>
                 disj1_tac >>
                 qexists_tac `t2` >>
                 qexists_tac `tenv' with v :=  Bind_name s' 0 t2' tenv'.v` >>
                 qexists_tac `0` >>
                 simp [PULL_FORALL])
             >- (qpat_assum `type_v a ctMap senv (Recclosure l0 l1 s') t1'`
                        (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
                 full_simp_tac(srw_ss())[] >>
                 srw_tac[][] >>
                 imp_res_tac type_recfun_lookup >>
                 srw_tac[][] >>
                 disj1_tac >>
                 qexists_tac `t2` >>
                 qexists_tac `tenv' with v := Bind_name q 0 t2' (bind_var_list 0 tenv'' (bind_tvar 0 tenv'.v))` >>
                 srw_tac[][] >>
                 srw_tac[][Once type_env_cases] >>
                 full_simp_tac(srw_ss())[check_freevars_def] >>
                 srw_tac[][build_rec_env_merge] >>
                 full_simp_tac(srw_ss())[bind_tvar_def] >>
                 qexists_tac `0` >>
                 srw_tac[][] >>
                 full_simp_tac(srw_ss())[] >>
                 metis_tac [bind_tvar_def, type_recfun_env, type_env_merge]))
         >- ( metis_tac [type_v_Boolv])
         >- (srw_tac[][Once type_v_cases_eqn] >>
             disj1_tac >>
             simp[PULL_EXISTS] >>
             qexists_tac `0` >>
             qexists_tac`[]` >>
             full_simp_tac(srw_ss())[type_s_def, store_lookup_def, store_assign_def] >>
             reverse(srw_tac[][EL_LUPDATE]) >- srw_tac[][Once type_v_cases] >>
             res_tac >>
             cases_on `EL l s` >>
             full_simp_tac(srw_ss())[] >>
             qpat_assum `type_v x0 x1 x2 (Loc l) x3` (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[])
         >- (disj2_tac >>
             srw_tac[][Once type_v_cases_eqn] >>
             full_simp_tac(srw_ss())[store_alloc_def, store_lookup_def] >>
             srw_tac[][FLOOKUP_UPDATE] >>
             qexists_tac `Tapp [t1] TC_ref` >>
             qexists_tac `0` >>
             qexists_tac `LENGTH s` >>
             srw_tac[][] >>
             `FLOOKUP tenvS (LENGTH s) = NONE`
                           by (full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
                               `~(LENGTH s < LENGTH s)` by decide_tac >>
                               `~(?t. FLOOKUP tenvS (LENGTH s) = SOME t)` by metis_tac [] >>
                               full_simp_tac(srw_ss())[] >>
                               cases_on `FLOOKUP tenvS (LENGTH s)` >>
                               full_simp_tac(srw_ss())[])
             >- metis_tac [type_ctxts_weakening, weakCT_refl, weakC_refl, weakM_refl, weakS_bind]
             >- (full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
                 srw_tac[][FLOOKUP_UPDATE]
                 >- decide_tac
                 >- (srw_tac[][EL_LENGTH_APPEND] >>
                     metis_tac [type_v_weakening, weakS_bind, weakC_refl, weakM_refl, weakCT_refl])
                 >- (`l < LENGTH s` by decide_tac >>
                     srw_tac[][EL_APPEND1] >>
                     res_tac  >>
                     cases_on `EL l s` >>
                     full_simp_tac(srw_ss())[] >>
                     cases_on `st` >>
                     full_simp_tac(srw_ss())[EVERY_MEM] >>
                     metis_tac [type_v_weakening, weakS_bind, weakCT_refl, weakC_refl, weakM_refl])))
         >- (full_simp_tac(srw_ss())[store_lookup_def] >>
             qpat_assum `type_v x0 x1 x2 (Loc l) x3` (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             disj1_tac >>
             full_simp_tac(srw_ss())[type_s_def] >>
             res_tac >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[store_lookup_def] >>
             metis_tac [])
         >- (disj2_tac >>
             srw_tac[][Once type_v_cases_eqn] >>
             full_simp_tac(srw_ss())[store_alloc_def, store_lookup_def] >>
             srw_tac[][FLOOKUP_UPDATE] >>
             qexists_tac `Tapp [] TC_word8array` >>
             qexists_tac `0` >>
             qexists_tac `LENGTH s` >>
             srw_tac[][] >>
             `FLOOKUP tenvS (LENGTH s) = NONE`
                           by (full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
                               `~(LENGTH s < LENGTH s)` by decide_tac >>
                               `~(?t. FLOOKUP tenvS (LENGTH s) = SOME t)` by metis_tac [] >>
                               full_simp_tac(srw_ss())[] >>
                               cases_on `FLOOKUP tenvS (LENGTH s)` >>
                               full_simp_tac(srw_ss())[])
             >- metis_tac [type_ctxts_weakening, weakCT_refl, weakC_refl, weakM_refl, weakS_bind]
             >- (full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
                 srw_tac[][FLOOKUP_UPDATE]
                 >- decide_tac
                 >- (srw_tac[][EL_LENGTH_APPEND] >>
                     metis_tac [type_v_weakening, weakS_bind, weakC_refl, weakM_refl, weakCT_refl])
                 >- (`l < LENGTH s` by decide_tac >>
                     srw_tac[][EL_APPEND1] >>
                     res_tac  >>
                     cases_on `EL l s` >>
                     full_simp_tac(srw_ss())[] >>
                     cases_on `st` >>
                     full_simp_tac(srw_ss())[EVERY_MEM] >>
                     metis_tac [type_v_weakening, weakS_bind, weakCT_refl, weakC_refl, weakM_refl])))
         >- do_app_exn_tac
         >- (srw_tac[][Once type_v_cases_eqn] >>
             full_simp_tac(srw_ss())[store_lookup_def] >>
             qpat_assum `type_v x0 x1 x2 (Loc l) x3` (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             disj1_tac >>
             metis_tac [])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac [])
         >- (srw_tac[][Once type_v_cases_eqn] >>
             disj1_tac >>
             simp[PULL_EXISTS] >>
             qexists_tac `0` >>
             qexists_tac`[]` >>
             full_simp_tac(srw_ss())[type_s_def, store_lookup_def, store_assign_def] >>
             reverse(srw_tac[][EL_LUPDATE]) >- srw_tac[][Once type_v_cases] >>
             res_tac >>
             cases_on `EL l s` >>
             full_simp_tac(srw_ss())[])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac[])
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac[])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (metis_tac[type_v_Boolv])
         >- metis_tac[char_list_to_v_type]
         >- metis_tac[v_to_char_list_type,Tstring_def]
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac[])
         >- metis_tac [v_to_list_type]
         >- (qpat_assum `type_v 0 ctMap tenvS (Vectorv vs) (Tapp [t2] TC_vector)`
                        (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[EVERY_LIST_REL] >>
             full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
             `Num (ABS i''') < LENGTH vs` by decide_tac >>
             res_tac >>
             metis_tac [EL_REPLICATE])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac [])
         >- (disj2_tac >>
             srw_tac[][Once type_v_cases_eqn] >>
             full_simp_tac(srw_ss())[FLOOKUP_UPDATE, store_alloc_def, store_lookup_def] >>
             srw_tac[][] >>
             qexists_tac `Tapp [t1'] TC_array` >>
             qexists_tac `0` >>
             qexists_tac `LENGTH s` >>
             srw_tac[][] >>
             `FLOOKUP tenvS (LENGTH s) = NONE`
                           by (full_simp_tac(srw_ss())[type_s_def, store_lookup_def] >>
                               `~(LENGTH s < LENGTH s)` by decide_tac >>
                               `~(?t. FLOOKUP tenvS (LENGTH s) = SOME t)` by metis_tac [] >>
                               full_simp_tac(srw_ss())[] >>
                               cases_on `FLOOKUP tenvS (LENGTH s)` >>
                               full_simp_tac(srw_ss())[])
             >- metis_tac [type_ctxts_weakening, weakCT_refl, weakC_refl, weakM_refl, weakS_bind]
             >- (full_simp_tac(srw_ss())[FLOOKUP_UPDATE, type_s_def, store_lookup_def] >>
                 srw_tac[][]
                 >- decide_tac
                 >- (srw_tac[][EL_LENGTH_APPEND, EVERY_REPLICATE] >>
                     metis_tac [type_v_weakening, weakS_bind, weakC_refl, weakM_refl, weakCT_refl])
                 >- (`l < LENGTH s` by decide_tac >>
                     srw_tac[][EL_APPEND1] >>
                     res_tac  >>
                     cases_on `EL l s` >>
                     full_simp_tac(srw_ss())[] >>
                     cases_on `st` >>
                     full_simp_tac(srw_ss())[EVERY_MEM] >>
                     metis_tac [type_v_weakening, weakS_bind, weakCT_refl, weakC_refl, weakM_refl]))
             >- full_simp_tac(srw_ss())[check_freevars_def])
         >- do_app_exn_tac
         >- (full_simp_tac(srw_ss())[store_lookup_def] >>
             qpat_assum `type_v x0 x1 x2 (Loc l) x3` (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             disj1_tac >>
             full_simp_tac(srw_ss())[type_s_def] >>
             `Num (ABS i'''') < LENGTH vs` by decide_tac >>
             res_tac >>
             every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[store_lookup_def, EVERY_EL] >>
             metis_tac [])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (srw_tac[][Once type_v_cases_eqn] >>
             metis_tac [])
         >- (srw_tac[][Once type_v_cases_eqn] >>
             disj1_tac >>
             simp[PULL_EXISTS] >>
             qexists_tac `0` >>
             qexists_tac`[]` >>
             full_simp_tac(srw_ss())[type_s_def, store_lookup_def, store_assign_def] >>
             reverse(srw_tac[][EL_LUPDATE]) >- srw_tac[][Once type_v_cases] >>
             res_tac >>
             srw_tac[][EL_LUPDATE] >>
             Cases_on `EL l s` >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             qpat_assum `type_v x0 x1 x2 (Loc l) x3` (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases_eqn]) >>
             full_simp_tac(srw_ss())[EVERY_MEM, MEM_LUPDATE] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[] >>
             FIRST_X_ASSUM match_mp_tac >>
             srw_tac[][MEM_EL] >>
             metis_tac [])
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- do_app_exn_tac
         >- (every_case_tac >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             disj1_tac >>
             simp [Once type_v_cases, type_vs_list_rel] >>
             qexists_tac `0` >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[type_s_def, store_assign_def, store_lookup_def] >>
             srw_tac[][EL_LUPDATE] >>
             res_tac >>
             Cases_on `EL l s` >>
             full_simp_tac(srw_ss())[]))
     >- (srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[bind_tvar_def, type_es_list_rel, type_vs_list_rel] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[PULL_EXISTS] >>
         qexists_tac `tenvS` >>
         qexists_tac `y` >>
         qexists_tac `tenv` >>
         srw_tac[][v_unchanged] >>
         qexists_tac `tenv` >>
         qexists_tac `t2` >>
         srw_tac[][] >>
         qexists_tac `ys` >>
         qexists_tac `t1` >>
         qexists_tac `ts1` >>
         metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,APPEND,APPEND_ASSOC,
                    num_tvs_def, type_v_freevars, tenv_val_ok_def, type_e_freevars])
     >- (full_simp_tac(srw_ss())[do_log_thm] >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         full_simp_tac(srw_ss())[Once type_v_cases_eqn] >>
         metis_tac [bind_tvar_def, SIMP_RULE (srw_ss()) [] type_e_rules, v_unchanged])
     >- (full_simp_tac(srw_ss())[do_log_thm] >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         metis_tac[])
     >- (full_simp_tac(srw_ss())[do_if_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         metis_tac [bind_tvar_def, v_unchanged])
     >- (srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[RES_FORALL] >>
         `check_freevars 0 [] t2` by metis_tac [type_ctxts_freevars] >>
         metis_tac [])
     >- (srw_tac[][Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[RES_FORALL] >>
         `check_freevars 0 [] t2` by metis_tac [type_ctxts_freevars] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[RES_FORALL, FORALL_PROD] >>
         first_x_assum (qspecl_then [`q`, `r'`] strip_assume_tac) >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][PULL_EXISTS] >>
         qexists_tac `tenvS` >>
         qexists_tac `t2` >>
         qexists_tac `tenv with v := bind_var_list 0 tenv' tenv.v` >>
         qexists_tac `0` >>
         full_simp_tac(srw_ss())[] >>
         metis_tac [bind_tvar_def, pmatch_type_preservation, v_unchanged])
     >- (full_simp_tac(srw_ss())[is_ccon_def] >>
         srw_tac[][Once type_env_cases, opt_bind_def] >>
         qexists_tac `tenvS` >>
         srw_tac[][] >>
         qexists_tac `t2` >>
         qexists_tac `tenv with v := opt_bind_name o' tvs t1 tenv.v` >>
         qexists_tac `0` >>
         srw_tac[][opt_bind_name_def] >>
         srw_tac[][bind_tvar_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[opt_bind_name_def] >>
         qpat_assum `type_env x0 x1 x2 x3` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
         srw_tac[][])
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         cases_on `lookup_alist_mod_env cn cenv'` >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac consistent_con_env_thm >>
         srw_tac[][Once type_v_cases_eqn] >>
         imp_res_tac type_es_length >>
         full_simp_tac(srw_ss())[] >>
         `ts2 = []` by
                 (cases_on `ts2` >>
                  full_simp_tac(srw_ss())[]) >>
         full_simp_tac(srw_ss())[type_vs_list_rel] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         metis_tac [ctxt_inv_not_poly, MAP_REVERSE])
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         srw_tac[][Once type_v_cases_eqn] >>
         imp_res_tac type_es_length >>
         full_simp_tac(srw_ss())[] >>
         `ts2 = []` by (cases_on `ts2` >> full_simp_tac(srw_ss())[]) >>
         full_simp_tac(srw_ss())[type_vs_list_rel] >>
         srw_tac[][] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         metis_tac [ctxt_inv_not_poly, MAP_REVERSE, type_vs_end])
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         cases_on `lookup_alist_mod_env cn cenv'` >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac consistent_con_env_thm >>
         full_simp_tac(srw_ss())[type_vs_list_rel, type_es_list_rel, PULL_EXISTS] >>
         srw_tac[][type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][PULL_EXISTS, type_vs_list_rel, type_es_list_rel] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         MAP_EVERY qexists_tac [`tenvS`, `tenv`, `tvs`, `tenv`, `t'''::ts1`] >>
         simp [SWAP_REVERSE_SYM] >>
         Cases_on `ts2` >>
         full_simp_tac(srw_ss())[] >>
         qexists_tac `ts'` >>
         simp [])
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         cases_on `lookup_alist_mod_env cn cenv'` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac consistent_con_env_thm >>
         full_simp_tac(srw_ss())[type_vs_list_rel, type_es_list_rel, PULL_EXISTS] >>
         srw_tac[][type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][PULL_EXISTS, type_vs_list_rel, type_es_list_rel] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         MAP_EVERY qexists_tac [`tenvS`, `y`, `tenv`, `tvs`, `tenv`, `ys`] >>
         simp [SWAP_REVERSE_SYM] >>
         imp_res_tac ctxt_inv_not_poly >>
         imp_res_tac type_ctxts_freevars >>
         metis_tac [check_freevars_def, EVERY_APPEND, EVERY_DEF, APPEND, APPEND_ASSOC])
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         cases_on `lookup_alist_mod_env cn cenv'` >>
         full_simp_tac(srw_ss())[] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac consistent_con_env_thm >>
         full_simp_tac(srw_ss())[type_vs_list_rel, type_es_list_rel, PULL_EXISTS] >>
         srw_tac[][type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][PULL_EXISTS, type_vs_list_rel, type_es_list_rel] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         MAP_EVERY qexists_tac [`tenvS`, `tenv`, `tvs`, `tenv`, `t'''::ts1`] >>
         simp [SWAP_REVERSE_SYM] >>
         Cases_on `ts2` >>
         full_simp_tac(srw_ss())[] >>
         qexists_tac `ts'` >>
         simp [])
     >- (full_simp_tac(srw_ss())[build_conv_def] >>
         cases_on `lookup_alist_mod_env cn cenv'` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         imp_res_tac consistent_con_env_thm >>
         full_simp_tac(srw_ss())[type_vs_list_rel, type_es_list_rel, PULL_EXISTS] >>
         srw_tac[][type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         srw_tac[][PULL_EXISTS, type_vs_list_rel, type_es_list_rel] >>
         full_simp_tac(srw_ss())[is_ccon_def] >>
         MAP_EVERY qexists_tac [`tenvS`, `y`, `tenv`, `tvs`, `tenv`, `ys`] >>
         simp [SWAP_REVERSE_SYM] >>
         imp_res_tac ctxt_inv_not_poly >>
         imp_res_tac type_ctxts_freevars >>
         metis_tac [check_freevars_def, EVERY_APPEND, EVERY_DEF, APPEND, APPEND_ASSOC])));

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

val exp_type_soundness_help = Q.prove (
`!state1 state2. e_step_reln^* state1 state2 ⇒
  ∀ctMap tenvS st env e c st' env' e' c' t dec_tvs.
    (state1 = (env,st,e,c)) ∧
    (state2 = (env',st',e',c')) ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap ∧
    ctMap_has_bools ctMap ∧
    ctMap_ok ctMap ∧
    type_state dec_tvs ctMap tenvS state1 t
    ⇒
    ?tenvS'. type_state dec_tvs ctMap tenvS' state2 t ∧
             store_type_extension tenvS tenvS'`,
 ho_match_mp_tac RTC_INDUCT >>
 srw_tac[][e_step_reln_def] >-
 (srw_tac[][store_type_extension_def] >>
      qexists_tac `tenvS` >>
      srw_tac[][] >>
      qexists_tac `FEMPTY` >>
      srw_tac[][]) >>
 `?env1' store1' ev1' ctxt1'. state1' = (env1',store1',ev1',ctxt1')` by (PairCases_on `state1'` >> metis_tac []) >>
 `?tenvS'. type_state dec_tvs ctMap tenvS' state1' t ∧
                ((tenvS' = tenvS) ∨
                 ?l t. (FLOOKUP tenvS l = NONE) ∧ (tenvS' = tenvS |+ (l,t)))`
                        by metis_tac [exp_type_preservation] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 `∃tenvS'.
     type_state dec_tvs ctMap tenvS' (env',st',e',c') t ∧
     store_type_extension (tenvS |+ (l,t')) tenvS'`
          by metis_tac [] >>
 qexists_tac `tenvS'` >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[store_type_extension_def, FLOOKUP_UPDATE] >>
 srw_tac[][] >>
 qexists_tac `FUNION (FEMPTY |+ (l,t')) tenvS''` >>
 srw_tac[][FUNION_FUPDATE_1, FUNION_FUPDATE_2] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [NOT_SOME_NONE]);

val exp_type_soundness = Q.store_thm ("exp_type_soundness",
`!ctMap tenvS tenv env st e t tvs.
  tenv_mod_ok tenv.m ∧
  ctMap_has_exns ctMap ∧
  ctMap_has_lists ctMap ∧
  ctMap_has_bools ctMap ∧
  consistent_mod_env tenvS ctMap env.m tenv.m ∧
  consistent_con_env ctMap env.c tenv.c ∧
  type_env ctMap tenvS env.v tenv.v ∧
  type_s ctMap tenvS (FST st) ∧
  (tvs ≠ 0 ⇒ is_value e) ∧
  type_e (tenv with v := bind_tvar tvs tenv.v) e t
  ⇒
  e_diverges env st e ∨
  (?st' r. (r ≠ Rerr (Rabort Rtype_error)) ∧
          small_eval env st e [] (st',r) ∧
          (?tenvS'.
            type_s ctMap tenvS' (FST st') ∧
            store_type_extension tenvS tenvS' ∧
            (!v. (r = Rval v) ⇒ type_v tvs ctMap tenvS' v t) ∧
            (!err. (r = Rerr (Rraise err)) ⇒ type_v 0 ctMap tenvS' err Texn)))`,
 srw_tac[][e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 `type_state tvs ctMap tenvS (env,st,Exp e,[]) t`
         by (srw_tac[][type_state_cases] >>
             PairCases_on `st` >>
             srw_tac[][] >>
             qexists_tac `t` >>
             qexists_tac `tenv` >>
             qexists_tac `tvs` >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[] >|
             [srw_tac[][Once context_invariant_cases],
              srw_tac[][Once type_ctxts_cases] >>
                  `num_tvs tenv.v = 0` by metis_tac [type_v_freevars] >>
                  `num_tvs (bind_tvar tvs tenv.v) = tvs`
                             by srw_tac[][bind_tvar_rewrites] >>
                  imp_res_tac type_e_freevars >>
                  full_simp_tac(srw_ss())[] >>
                  metis_tac [bind_tvar_rewrites, type_v_freevars]]) >>
 `?tenvS'. type_state tvs ctMap tenvS' (env',s',e',c') t ∧ store_type_extension tenvS tenvS'`
         by metis_tac [exp_type_soundness_help, consistent_con_env_def] >>
 full_simp_tac(srw_ss())[e_step_reln_def] >>
 `final_state (env',s',e',c')` by metis_tac [exp_type_progress] >>
 Cases_on `e'` >>
 Cases_on `c'` >>
 TRY (Cases_on `e''`) >>
 full_simp_tac(srw_ss())[final_state_def] >>
 qexists_tac `s'`
 >- (full_simp_tac(srw_ss())[small_eval_def] >>
     full_simp_tac(srw_ss())[type_state_cases] >>
     full_simp_tac(srw_ss())[Once context_invariant_cases, Once type_ctxts_cases] >>
     qexists_tac `Rval v` >>
     srw_tac[][] >>
     metis_tac [small_eval_def, result_distinct, result_11])
 >- (full_simp_tac(srw_ss())[small_eval_def] >>
     full_simp_tac(srw_ss())[type_state_cases] >>
     full_simp_tac(srw_ss())[Once context_invariant_cases, Once type_ctxts_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[final_state_def] >>
     cases_on `t'` >>
     full_simp_tac(srw_ss())[final_state_def, type_ctxt_cases] >>
     qexists_tac `Rerr (Rraise v)` >>
     srw_tac[][] >>
     metis_tac [small_eval_def, result_distinct, result_11, error_result_distinct]));

val store_type_extension_refl = Q.prove (
`!s. store_type_extension s s`,
 srw_tac[][store_type_extension_def] >>
 qexists_tac `FEMPTY` >>
 srw_tac[][]);

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
     qcase_tac `small_eval _ _ _ _ (st2,res)` >>
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
             `type_p 0 tenv.c p t bindings` by metis_tac [] >>
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
     qcase_tac `type_s _ tenvS' st'.refs` >>
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
     CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal"evaluate_dec" o fst o dest_const o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     PairCases_on`res`>>
     full_simp_tac(srw_ss())[append_new_dec_tenv_def] >> rpt var_eq_tac >>
     `¬decs_diverges mn (extend_dec_env env'' cenv'' env) st' ds`
                  by metis_tac [pair_CASES] >>
     first_x_assum(fn th =>
       first_assum(mp_tac o MATCH_MP (CONV_RULE(STRIP_QUANT_CONV(HO_REWR_CONV(swap_imp))) th))) >>
     disch_then(qspecl_then[`tenvS'`,`flat_to_ctMap new_tenv11 ⊌ ctMap`]mp_tac) >>
     discharge_hyps >- (
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
     first_assum(match_exists_tac o concl) >> simp[] >>
     qexists_tac`tenvS''` >>
     simp[GSYM CONJ_ASSOC] >>
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
     qcase_tac `type_s _ tenvS' st'.refs` >>
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
     qcase_tac `evaluate_decs _ _ _ _ _ (st',cenv2,r)` >>
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
 qcase_tac `evaluate_top _ _ _ top (st',cenv2,r)` >>
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
         CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``bigStep$evaluate_prog`` o fst o strip_comb))) >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp [combine_mod_result_def] >>
         full_simp_tac(srw_ss())[update_type_sound_inv_def, FUNION_ASSOC, combine_mod_result_def, union_decls_assoc, merge_alist_mod_env_assoc, bvl2_append, merge_alist_mod_env_assoc, merge_mod_env_assoc, extend_top_env_def, append_new_top_tenv_def])
     >- (disj2_tac >>
         srw_tac[DNF_ss][] >> disj1_tac >>
         CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``bigStep$evaluate_prog`` o fst o strip_comb))) >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         srw_tac[][FST_union_decls] >>
         full_simp_tac(srw_ss())[combine_mod_result_def, FST_union_decls, UNION_ASSOC] >>
         metis_tac[SUBSET_REFL]))
 >- (disj2_tac >>
     srw_tac[DNF_ss][] >> disj2_tac >>
     CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``bigStep$evaluate_top`` o fst o strip_comb))) >>
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

val type_no_dup_top_types = Q.prove (
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

val type_no_dup_mods = Q.prove (
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

val _ = export_theory ();
