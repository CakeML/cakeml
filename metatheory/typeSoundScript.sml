open preamble;
open pairTheory optionTheory alistTheory;
open miscTheory;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory;
open smallStepTheory bigStepTheory replTheory;
open terminationTheory;
open libPropsTheory;
open weakeningTheory typeSysPropsTheory bigSmallEquivTheory;
open initialEnvTheory;
open typeSoundInvariantsTheory evalPropsTheory;

val _ = new_theory "typeSound";

val type_v_cases_eqn = List.nth (CONJUNCTS type_v_cases, 0);
val type_vs_cases_eqn = List.nth (CONJUNCTS type_v_cases, 1);
val type_env_cases = List.nth (CONJUNCTS type_v_cases, 2);
val consistent_mod_cases = List.nth (CONJUNCTS type_v_cases, 3);

val tid_exn_not = Q.prove (
`(!tn. tid_exn_to_tc tn ≠ TC_bool) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_int) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_ref) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_unit) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_tup) ∧
 (!tn. tid_exn_to_tc tn ≠ TC_fn)`,
 rw [] >>
 cases_on `tn` >>
 fs [tid_exn_to_tc_def] >>
 metis_tac []);

(* Classifying values of basic types *)
val canonical_values_thm = Q.prove (
`∀tvs tenvC tenvS v t1 t2.
  (type_v tvs tenvC tenvS v (Tref t1) ⇒ (∃n. v = Loc n)) ∧
  (type_v tvs tenvC tenvS v Tint ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs tenvC tenvS v Tbool ⇒ (∃n. v = Litv (Bool n))) ∧
  (type_v tvs tenvC tenvS v Tunit ⇒ (∃n. v = Litv Unit)) ∧
  (type_v tvs tenvC tenvS v (Tfn t1 t2) ⇒
    (∃env n topt e. v = Closure env n e) ∨
    (∃env funs n. v = Recclosure env funs n))`,
rw [] >>
fs [Once type_v_cases, deBruijn_subst_def] >>
fs [Tfn_def, Tint_def, Tbool_def, Tunit_def, Tref_def] >>
rw [] >>
TRY (Cases_on `tn`) >>
fs [tid_exn_to_tc_def] >>
metis_tac [Tfn_def, type_funs_Tfn, t_distinct, t_11, tc0_distinct]);

val tac =
fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
rw [] >>
fs [deBruijn_subst_def, Tbool_def, Tunit_def, Tint_def, Tref_def, tid_exn_not, Tfn_def] >>
metis_tac [Tfn_def, type_funs_Tfn, t_distinct, t_11, tc0_distinct, tid_exn_not];

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
 rw [] >>
 rw [pmatch_def] >>
 fs [lit_same_type_def] 
 >- (fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [Tint_def, Tbool_def, Tref_def, Tunit_def])
 >- (fs [Once type_v_cases_eqn, Once (hd (CONJUNCTS type_p_cases))] >>
     rw [] >>
     cases_on `lookup_con_id n cenv` >>
     rw [] 
     >- (fs [consistent_con_env_def] >>
         metis_tac [NOT_SOME_NONE]) >>
     PairCases_on `x` >>
     fs [] >>
     `∃tvs ts. lookup_con_id n tenvC = SOME (tvs,ts,x1) ∧
               FLOOKUP ctMap (id_to_n n, x1) = SOME (tvs,ts)` by metis_tac [consistent_con_env_def] >>
     fs [tid_exn_to_tc_11] >>
     rw [] >>
     fs [] >>
     imp_res_tac same_ctor_and_same_tid >>
     rw [] >>
     fs []
     >- metis_tac []
     >- metis_tac [same_tid_sym]
     >- (fs [consistent_con_env_def] >>
         metis_tac [type_ps_length, type_vs_length, LENGTH_MAP, SOME_11, PAIR_EQ]))
 >- (qpat_assum `type_v b c d e f` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     qpat_assum `type_p b0 a b c d` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     every_case_tac >>
     rw [] >>
     metis_tac [])
 >- (fs [Once type_p_cases, Once type_v_cases] >>
     rw [] >>
     imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length >>
     fs [] >>
     cases_on `ts` >>
     fs [])
 >- (qpat_assum `type_v b c d e f` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     qpat_assum `type_p b0 a b c d` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     every_case_tac >>
     rw [] >>
     fs [type_s_def] >>
     res_tac >>
     fs [Tref_def] >>
     rw [] >>
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
 >- (qpat_assum `type_ps tvs tenvC (p::ps) ts tenv`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_vs tvs ctMap tenvS (v::vs) ts`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [])
 >- (imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length >>
     fs [] >>
     cases_on `ts` >>
     fs [])
 >- (imp_res_tac type_ps_length >> imp_res_tac type_vs_length >>
     fs [] >>
     cases_on `ts` >>
     fs []));

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
     (?op e1 e2. e = App op e1 e2) ∨
     (?uop e1. e = Uapp uop e1) ∨
     (?op e1 e2. e = Log op e1 e2) ∨
     (?e1 e2 e3. e = If e1 e2 e3) ∨
     (?e' pes. e = Mat e' pes) ∨
     (?n e1 e2. e = Let n e1 e2) ∨
     (?funs e'. e = Letrec funs e'))`,
rw [] >>
cases_on `e` >>
cases_on `c` >>
rw [final_state_def]);

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
 rw [do_eq_def] >>
 rw [type_v_cases_eqn] >>
 rw [Tbool_def, Tint_def, Tref_def, Tunit_def, Tfn_def] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 imp_res_tac type_funs_Tfn >>
 fs [Tfn_def] 
 >- (fs [type_v_cases_eqn] >>
     rw [] >>
     fs [] >>
     metis_tac []) >>
 fs [Once type_vs_cases_eqn] >>
 rw [] >>
 cases_on `do_eq v1 v2` >>
 fs [tid_exn_not]
 >- (cases_on `b` >>
     fs [] >>
     qpat_assum `!x. P x` (mp_tac o Q.SPECL [`tvs`, `ctMap`, `tenvS`, `ts'`]) >>
     rw [METIS_PROVE [] ``(a ∨ b) = (~a ⇒ b)``] >>
     cases_on `vs1` >>
     fs [] >-
     fs [Once type_vs_cases_eqn] >>
     cases_on `ts'` >>
     fs [] >>
     fs [Once type_vs_cases_eqn])
 >- metis_tac []);

val consistent_con_env_thm = Q.prove (
`∀ctMap cenv tenvC.
     consistent_con_env ctMap cenv tenvC ⇒
     ∀cn tvs ts tn.
       (lookup_con_id cn tenvC = SOME (tvs,ts,tn) ⇒
        lookup_con_id cn cenv = SOME (LENGTH ts,tn) ∧
        FLOOKUP ctMap (id_to_n cn,tn) = SOME (tvs, ts)) ∧
       (lookup_con_id cn tenvC = NONE ⇒ lookup_con_id cn cenv = NONE)`,
 rw [consistent_con_env_def] >>
 cases_on `lookup_con_id cn cenv` >>
 rw []
 >- metis_tac [NOT_SOME_NONE]
 >- (PairCases_on `x` >>
     fs [] >>
     metis_tac [PAIR_EQ, SOME_11])
 >> metis_tac [pair_CASES, SOME_11, PAIR_EQ, NOT_SOME_NONE]);

(* A well-typed expression state is either a value with no continuation, or it
 * can step to another state, or it steps to a BindError. *)
val exp_type_progress = Q.prove (
`∀dec_tvs tenvC st e t menv cenv env c tenvS.
  type_state dec_tvs tenvC tenvS ((menv,cenv,env), st, e, c) t ∧
  ¬(final_state ((menv,cenv,env), st, e, c))
  ⇒
  (∃menv' cenv' env' st' e' c'. e_step ((menv,cenv,env), st, e, c) = Estep ((menv',cenv',env'), st', e', c'))`,
 rw [] >>
 rw [e_step_def] >>
 fs [type_state_cases, push_def, return_def] >>
 rw []
 >- (fs [Once type_e_cases] >>
     rw [] >>
     fs [not_final_state, all_env_to_cenv_def, all_env_to_menv_def] >|
     [rw [] >>
          every_case_tac >>
          fs [return_def] >>
          imp_res_tac type_es_length >>
          fs [] >>
          metis_tac [do_con_check_build_conv, NOT_SOME_NONE],
      fs [do_con_check_def] >>
          rw [] >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          fs [] >>
          imp_res_tac type_es_length >>
          fs [],
      fs [do_con_check_def] >>
          rw [] >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          rw [] >>
          every_case_tac >>
          fs [return_def] >>
          imp_res_tac type_es_length >>
          fs [build_conv_def],
      fs [do_con_check_def] >>
          rw [] >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          rw [] >>
          fs [] >>
          metis_tac [type_es_length, LENGTH_MAP],
      imp_res_tac type_lookup_id >>
          fs [] >>
          every_case_tac >>
          metis_tac [NOT_SOME_NONE],
      metis_tac [type_funs_distinct]])
 >- (rw [continue_def] >>
     fs [Once type_ctxts_cases, type_ctxt_cases, return_def, push_def] >>
     rw [] >>
     fs [final_state_def] >>
     fs [] >>
     fs [type_op_cases] >>
     rw [] >>
     imp_res_tac canonical_values_thm >>
     fs [] >>
     rw [] >>
     fs [do_app_def, do_if_def, do_log_def] >|
     [every_case_tac >>
          rw [] >>
          fs [is_ccon_def] >>
          fs [Once context_invariant_cases, final_state_def],
      rw [do_uapp_def] >>
          every_case_tac >>
          rw [store_alloc_def] >>
          fs [Once type_v_cases] >>
          rw [] >>
          fs [type_uop_cases] >>
          fs [type_s_def] >>
          rw [] >>
          imp_res_tac type_funs_Tfn >>
          fs [tid_exn_not, Tbool_def, Tint_def, Tref_def, Tunit_def, Tfn_def] >>
          metis_tac [optionTheory.NOT_SOME_NONE],
      every_case_tac >>
          fs [exn_env_def],
      every_case_tac >>
          fs [] >>
          qpat_assum `type_v a tenvC senv (Recclosure x2 x3 x4) tpat`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
          fs [] >>
          imp_res_tac type_funs_find_recfun >>
          fs [],
      every_case_tac >>
          fs [] >>
          qpat_assum `type_v a tenvC senv (Recclosure x2 x3 x4) tpat`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
          fs [] >>
          imp_res_tac type_funs_find_recfun >>
          fs [],
      cases_on `do_eq v' v` >>
          fs [Once context_invariant_cases] >>
          srw_tac [ARITH_ss] [exn_env_def] >> 
          metis_tac [eq_same_type],
      qpat_assum `type_v a tenvC senv (Loc n) z` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
          fs [type_s_def] >>
          res_tac >>
          fs [store_assign_def, store_lookup_def],
      every_case_tac >>
          fs [],
      every_case_tac >>
          fs [],
      every_case_tac >>
          fs [RES_FORALL] >>
          rw [] >>
          qpat_assum `∀x. (x = (q,r)) ∨ P x ⇒ Q x`
                   (MP_TAC o Q.SPEC `(q,r)`) >>
          rw [] >>
          CCONTR_TAC >>
          fs [] >>
          metis_tac [pmatch_type_progress, match_result_distinct],
      imp_res_tac consistent_con_env_thm >>
          fs [do_con_check_def, all_env_to_cenv_def] >>
          fs [] >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def] >>
          `LENGTH ts2 = 0` by decide_tac >>
          cases_on `es` >>
          fs [],
      fs [all_env_to_cenv_def] >>
          every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def],
      every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def],
      every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def]]));

(* A successful pattern match gives a binding environment with the type given by
* the pattern type checker *)
val pmatch_type_preservation = Q.prove (
`(∀(cenv : envC) st p v env env' (tenvC:tenvC) ctMap tenv t tenv' tenvS tvs.
  (pmatch cenv st p v env = Match env') ∧
  consistent_con_env ctMap cenv tenvC ∧
  type_v tvs ctMap tenvS v t ∧
  type_p tvs tenvC p t tenv' ∧
  type_s ctMap tenvS st ∧
  type_env ctMap tenvS env tenv ⇒
  type_env ctMap tenvS env' (bind_var_list tvs tenv' tenv)) ∧
 (∀(cenv : envC) st ps vs env env' (tenvC:tenvC) ctMap tenv tenv' ts tenvS tvs.
  (pmatch_list cenv st ps vs env = Match env') ∧
  consistent_con_env ctMap cenv tenvC ∧
  type_vs tvs ctMap tenvS vs ts ∧
  type_ps tvs tenvC ps ts tenv' ∧
  type_s ctMap tenvS st ∧
  type_env ctMap tenvS env tenv ⇒
  type_env ctMap tenvS env' (bind_var_list tvs tenv' tenv))`,
 ho_match_mp_tac pmatch_ind >>
 rw [pmatch_def]
 >- (fs [Once type_p_cases, bind_var_list_def, bind_def] >>
     rw [] >>
     rw [Once type_v_cases] >>
     rw [emp_def, bind_def, bind_tenv_def])
 >- fs [Once type_p_cases, bind_var_list_def]
 >- (cases_on `lookup_con_id n cenv` >>
     fs [] >>
     PairCases_on `x` >>
     fs [] >>
     every_case_tac >>
     fs [] >>
     fs [] >>
     FIRST_X_ASSUM match_mp_tac >>
     rw [] >>
     fs [Once type_v_cases_eqn, Once (hd (CONJUNCTS type_p_cases))] >>
     rw [] >>
     fs [] >>
     rw [] >>
     fs [tid_exn_to_tc_11, consistent_con_env_def] >>
     res_tac >>
     fs [] >>
     rw [] >>
     imp_res_tac same_ctor_and_same_tid >>
     rw [] >>
     fs [] >>
     metis_tac [])
 >- (cases_on `(LENGTH ps = x0) ∧ (LENGTH vs = x0)` >>
     fs [] >>
     fs [] >>
     qpat_assum `type_v tvs ctMap senv vpat t`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [Once type_p_cases] >>
     rw [] >>
     fs [] >>
     rw [] >>
     cases_on `ps` >>
     fs [] >>
     qpat_assum `type_ps a0 a c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     fs [] >>
     metis_tac [])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [] >>
     qpat_assum `type_p x1 x2 x3 x4 x5` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_v x1 x2 x3 x4 x5` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     rw [] >>
     fs [type_s_def, store_lookup_def, Tref_def] >>
     `type_v tvs ctMap tenvS (EL lnum st) t''` by
                 metis_tac [consistent_con_env_def, type_v_weakening, weakCT_refl, weakS_refl, weakM_refl] >>
     metis_tac [])
 >- fs [Once type_p_cases, bind_var_list_def]
 >- (every_case_tac >>
     fs [] >>
     qpat_assum `type_vs tva ctMap senv (v::vs) ts`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     qpat_assum `type_ps a0 a1 c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     fs [] >>
     rw [bind_var_list_append] >>
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
rw [type_env2_def] >>
rw [Once type_v_cases, bind_var_list_def, emp_def, bind_def, bind_tenv_def]);

val type_env_merge_lem1 = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv
  ⇒
  type_env tenvC tenvS (merge env' env) (bind_var_list tvs tenv' tenv) ∧ (LENGTH env' = LENGTH tenv')`,
Induct_on `tenv'` >>
rw [merge_def] >>
cases_on `env'` >>
rw [bind_var_list_def] >>
fs [type_env2_def] >|
[PairCases_on `h` >>
     rw [bind_var_list_def] >>
     PairCases_on `h'` >>
     fs [] >>
     fs [type_env2_def] >>
     rw [] >>
     rw [Once type_v_cases, bind_def, emp_def, bind_tenv_def] >>
     metis_tac [merge_def],
 PairCases_on `h` >>
     rw [bind_var_list_def] >>
     PairCases_on `h'` >>
     fs [] >>
     fs [type_env2_def] >>
     rw [] >>
     rw [Once type_v_cases, bind_def, emp_def, bind_tenv_def] >>
     metis_tac [merge_def]]);

val type_env_merge_lem2 = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  type_env tenvC tenvS (merge env' env) (bind_var_list tvs tenv' tenv) ∧
  (LENGTH env' = LENGTH tenv')
  ⇒
  type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv`,
Induct_on `env'` >>
rw [merge_def] >>
cases_on `tenv'` >>
fs [bind_var_list_def] >>
rw [type_env2_def] >>
qpat_assum `type_env x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
PairCases_on `h` >>
PairCases_on `h'` >>
rw [type_env2_def] >>
fs [emp_def, bind_def, bind_var_list_def, bind_tenv_def, merge_def] >>
rw [type_env2_def] >>
metis_tac [type_v_freevars]);

val type_env_merge = Q.prove (
`∀tenvC env env' tenv tenv' tvs tenvS.
  ((type_env tenvC tenvS (merge env' env) (bind_var_list tvs tenv' tenv) ∧
    (LENGTH env' = LENGTH tenv'))
   =
   (type_env2 tenvC tenvS tvs env' tenv' ∧ type_env tenvC tenvS env tenv))`,
metis_tac [type_env_merge_lem1, type_env_merge_lem2]);

val type_recfun_env_help = Q.prove (
`∀fn funs funs' tenvM tenvC ctMap tenv tenv' tenv0 env tenvS tvs.
  tenvM_ok tenvM ∧
  consistent_con_env ctMap cenv tenvC ∧
  consistent_mod_env tenvS ctMap menv tenvM ∧
  (!fn t. (lookup fn tenv = SOME t) ⇒ (lookup fn tenv' = SOME t)) ∧
  type_env ctMap tenvS env tenv0 ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv' (bind_tvar tvs tenv0)) funs' tenv' ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv' (bind_tvar tvs tenv0)) funs tenv
  ⇒
  type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs) tenv`,
induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
fs [emp_def] >>
rw [bind_def, Once type_v_cases, type_env2_def] >>
`type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs) env'`
              by metis_tac [optionTheory.NOT_SOME_NONE, lookup_def, bind_def] >>
rw [type_env2_def] >>
fs [Tfn_def] >>
`lookup fn tenv' = SOME (Tapp [t1;t2] TC_fn)` by metis_tac [lookup_def, bind_def] >|
[fs [num_tvs_bind_var_list, check_freevars_def] >>
     metis_tac [num_tvs_def, bind_tvar_def, arithmeticTheory.ADD, 
                arithmeticTheory.ADD_COMM, type_v_freevars],
 qexists_tac `tenvM` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv0` >>
     rw [] >>
     qexists_tac `tenv'` >>
     rw []]);

val type_recfun_env = Q.prove (
`∀fn funs tenvM tenvC ctMap tenvS tvs tenv tenv0 menv cenv env.
  tenvM_ok tenvM ∧
  consistent_con_env ctMap cenv tenvC ∧
  consistent_mod_env tenvS ctMap menv tenvM ∧
  type_env ctMap tenvS env tenv0 ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv (bind_tvar tvs tenv0)) funs tenv
  ⇒
  type_env2 ctMap tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs fn)) funs) tenv`,
metis_tac [type_recfun_env_help]);

val type_raise_eqn = Q.prove (
`!tenvM tenvC tenv r t. 
  type_e tenvM tenvC tenv (Raise r) t = (type_e tenvM tenvC tenv r Texn ∧ check_freevars (num_tvs tenv) [] t)`,
rw [Once type_e_cases] >>
metis_tac []);

val type_env_eqn = Q.prove (
`!ctMap tenvS. 
  (type_env ctMap tenvS emp Empty = T) ∧
  (!n tvs t v env tenv. 
      type_env ctMap tenvS (bind n v env) (bind_tenv n tvs t tenv) = 
      (type_v tvs ctMap tenvS v t ∧ check_freevars tvs [] t ∧ type_env ctMap tenvS env tenv))`,
rw [] >>
rw [Once type_v_cases] >>
fs [bind_def, emp_def, bind_tenv_def] >>
metis_tac [type_v_freevars]);

val ctxt_inv_not_poly = Q.prove (
`!dec_tvs c tvs.
  context_invariant dec_tvs c tvs ⇒ ¬poly_context c ⇒ (tvs = 0)`,
ho_match_mp_tac context_invariant_ind >>
rw [poly_context_def] >>
cases_on `c` >>
fs [] >-
metis_tac [NOT_EVERY] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0` >>
fs [] >>
metis_tac [NOT_EVERY]);

val type_v_exn = Q.prove (
`!tvs cenv senv.
  ctMap_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME ("Bind",TypeExn NONE)) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME ("Div",TypeExn NONE)) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME ("Eq",TypeExn NONE)) []) Texn`,
 ONCE_REWRITE_TAC [type_v_cases] >>
 rw [ctMap_has_exns_def, Texn_def, tid_exn_to_tc_def] >>
 metis_tac [type_v_rules]);

val exn_tenvC_def = Define `
exn_tenvC = (emp,MAP (λcn. (cn,[],[],TypeExn NONE)) ["Bind"; "Div"; "Eq"])`;

val type_e_exn = Q.prove (
`!tenvM tenv.
  ctMap_ok ctMap ∧
  ctMap_has_exns ctMap ∧
  ((menv,cenv,env) = exn_env)
  ⇒
  type_e tenvM exn_tenvC tenv (Con (SOME (Short "Bind")) []) Texn ∧
  type_e tenvM exn_tenvC tenv (Con (SOME (Short "Div")) []) Texn ∧
  type_e tenvM exn_tenvC tenv (Con (SOME (Short "Eq")) []) Texn ∧
  consistent_con_env ctMap cenv exn_tenvC`,
 NTAC 2 (ONCE_REWRITE_TAC [type_e_cases]) >>
 rw [consistent_con_env_def, Texn_def, tid_exn_to_tc_def] >>
 fs [exn_env_def, exn_tenvC_def] >>
 res_tac >>
 fs [] >>
 rw [flat_tenvC_ok_def, tenvC_ok_def] >>
 fs [id_to_n_def, ctMap_has_exns_def, lookup_con_id_def, emp_def] >>
 every_case_tac >>
 fs []);

(* If a step can be taken from a well-typed state, the resulting state has the
* same type *)
val exp_type_preservation = Q.prove (
`∀dec_tvs ctMap menv cenv st env e c t menv' cenv' st' env' e' c' tenvS.
  ctMap_ok ctMap ∧
  ctMap_has_exns ctMap ∧
  type_state dec_tvs ctMap tenvS ((menv,cenv,env), st, e, c) t ∧
  (e_step ((menv,cenv,env), st, e, c) = Estep ((menv',cenv',env'), st', e', c'))
  ⇒
  ∃tenvS'. type_state dec_tvs ctMap tenvS' ((menv',cenv',env'), st', e', c') t ∧
          ((tenvS' = tenvS) ∨
           (?l t. (lookup l tenvS = NONE) ∧ (tenvS' = bind l t tenvS)))`,
 rw [type_state_cases] >>
 fs [e_step_def] >>
 `check_freevars tvs [] t ∧ check_freevars tvs [] t1` by metis_tac [type_ctxts_freevars]
 >- (cases_on `e''` >>
     fs [push_def, is_value_def] >>
     rw []
     >- (qpat_assum `type_e a0 a1 b1 c1 d1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases] >>
         rw [type_ctxt_cases] >>
         fs [bind_tvar_def] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         metis_tac [check_freevars_def, Texn_def, EVERY_DEF])
     >- (qpat_assum `type_e a0 a1 b1 c1 d1` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases] >>
         rw [type_ctxt_cases] >>
         fs [bind_tvar_def] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         metis_tac [])
     >- (fs [return_def] >>
         rw [] >>
         qpat_assum `type_e tenvM tenvC tenv (Lit l) t1`
                   (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [] >>
         rw [Once type_v_cases_eqn] >>
         metis_tac [])
     >- (every_case_tac >>
         fs [return_def] >>
         rw [] >>
         qpat_assum `type_e tenvM tenvC tenv (Con s'' epat) t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [] >>
         qpat_assum `type_es tenvM tenvC tenv epat ts`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs []
         >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
         >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
         >- (fs [build_conv_def, all_env_to_cenv_def] >>
             every_case_tac >>
             fs [] >>
             qexists_tac `tenvS` >>
             rw [] >>
             qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
             rw [] >>
             rw [Once type_v_cases] >>
             rw [Once type_v_cases] >>
             imp_res_tac consistent_con_env_thm >>
             fs [check_freevars_def] >>
             metis_tac [check_freevars_def, consistent_con_env_def])
         >- (fs [build_conv_def, all_env_to_cenv_def] >>
             every_case_tac >>
             fs [] >>
             qexists_tac `tenvS` >>
             rw [] >>
             qexists_tac `Tapp [] TC_tup` >>
             rw [] >>
             rw [Once type_v_cases] >>
             rw [Once type_v_cases] >>
             metis_tac [check_freevars_def])
         >- (fs [build_conv_def, all_env_to_cenv_def] >>
             every_case_tac >>
             fs [] >>
             qexists_tac `tenvS` >>
             rw [] >>
             rw [Once type_ctxts_cases, type_ctxt_cases] >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `t''`>>
             ONCE_REWRITE_TAC [context_invariant_cases] >>
             rw [] >>
             qexists_tac `tenv` >>
             qexists_tac `tvs` >>
             rw [] >-
             metis_tac [] >>
             fs [is_ccon_def] >>
             imp_res_tac ctxt_inv_not_poly >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `tenv` >>
             qexists_tac `Tapp ts' (tid_exn_to_tc tn)`>>
             rw [] >>
             cases_on `ts` >>
             fs [] >>
             rw [] >>
             rw [] >>
             qexists_tac `[]` >>
             qexists_tac `t'''` >>
             rw [] >>
             metis_tac [type_v_rules, APPEND, check_freevars_def])
         >- (fs [build_conv_def, all_env_to_cenv_def] >>
             every_case_tac >>
             fs [] >>
             qexists_tac `tenvS` >>
             rw [] >>
             rw [Once type_ctxts_cases, type_ctxt_cases] >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `t''`>>
             qexists_tac `tenv`>>
             ONCE_REWRITE_TAC [context_invariant_cases] >>
             rw [] >>
             qexists_tac `tvs` >>
             rw [] >-
             metis_tac [] >>
             fs [is_ccon_def] >>
             imp_res_tac ctxt_inv_not_poly >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `tenv`>>
             qexists_tac `Tapp (t''::ts') TC_tup`>>
             rw [] >>
             qexists_tac `[]` >>
             qexists_tac `ts'` >>
             rw [] >>
             metis_tac [type_v_rules, EVERY_DEF, check_freevars_def]))
     >- (qexists_tac `tenvS` >>
         rw [] >>
         every_case_tac >>
         fs [return_def] >>
         rw [] >>
         qexists_tac `t1` >>
         rw [] >>
         qpat_assum `type_e tenvM tenvC tenv (Var i) t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [] >>
         qexists_tac `tvs` >>
         rw [] >>
         imp_res_tac type_v_freevars >>
         `num_tvs (bind_tvar tvs tenv) = tvs` 
                  by (fs [bind_tvar_def] >>
                      cases_on `tvs` >>
                      fs [num_tvs_def]) >>
         metis_tac [type_lookup_type_v])
     >- (fs [return_def] >>
         rw [] >>
         qpat_assum `type_e tenvM tenvC tenv (Fun s'' e'') t1`
                  (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [] >>
         rw [bind_tvar_def, Once type_v_cases_eqn] >>
         fs [bind_tvar_def, Tfn_def, check_freevars_def] >>
         metis_tac [check_freevars_def])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [type_uop_cases] >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         rw [type_uop_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [Tref_def, bind_tvar_def, check_freevars_def] >-
         metis_tac [check_freevars_def] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `Tapp [t1] TC_ref` >>
         rw [check_freevars_def] >>
         metis_tac [])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [bind_tvar_def] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [bind_tvar_def] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [bind_tvar_def] >>
         metis_tac [])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [bind_tvar_def] >>
         metis_tac [type_e_freevars, type_v_freevars, type_v_exn])
     >- (qpat_assum `type_e x0 x1 x2 x3 x4` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         fs [bind_tvar_def] >|
         [qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `tenvC` >>
              qexists_tac `t1'` >>
              qexists_tac `tenv` >>
              qexists_tac `tvs` >>
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `tenvC` >>
              qexists_tac `tenv` >>
              qexists_tac `t1` >>
              rw [] >-
              metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                         num_tvs_def, type_v_freevars, tenv_ok_def,
                         type_e_freevars] >>
              fs [is_ccon_def] >>
              metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                         num_tvs_def, type_v_freevars, tenv_ok_def,
                         type_e_freevars],
          qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `tenvC` >>
              qexists_tac `t1'` >>
              qexists_tac `tenv` >>
              rw [] >>
              qexists_tac `0` >>
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `tenvC` >>
              qexists_tac `tenv` >>
              qexists_tac `t1` >>
              rw [] >>
              metis_tac [arithmeticTheory.ADD, arithmeticTheory.ADD_COMM,
                         num_tvs_def, type_v_freevars, tenv_ok_def,
                         type_e_freevars]])
     >- (every_case_tac >>
         fs [] >>
         rw [] >>
         qpat_assum `type_e tenvM tenvC tenv epat t1`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [build_rec_env_merge] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t1` >>
         qexists_tac `bind_var_list tvs tenv' tenv` >>
         rw [] >>
         fs [bind_tvar_def, all_env_to_cenv_def, all_env_to_menv_def, all_env_to_env_def] >>
         qexists_tac `0` >>
         rw [] >>
         metis_tac [type_recfun_env, type_env_merge, bind_tvar_def]))
 >- (fs [continue_def, push_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [] >>
     every_case_tac >>
     fs [return_def] >>
     rw [] >>
     qpat_assum `type_ctxts x1 x2 x3 x4 x5 x6` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >>
     fs [type_ctxt_cases] >>
     rw [] >>
     qpat_assum `context_invariant x0 x1 x2` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once context_invariant_cases]) >>
     fs [oneTheory.one]
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         cases_on `l` >>
         fs [RES_FORALL] >-
         metis_tac [] >>
         qpat_assum `!x. P x` (ASSUME_TAC o Q.SPEC `h`) >>
         fs [] >>
         PairCases_on `h` >>
         fs [] >>
         metis_tac [num_tvs_bind_var_list, type_e_freevars, type_v_freevars, tenv_ok_bind_var_list, type_p_freevars])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [tenv_ok_def, arithmeticTheory.ADD_0, num_tvs_def, bind_tenv_def, type_e_freevars, type_v_freevars])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [bind_tvar_def, EVERY_DEF, type_e_freevars, type_v_freevars, check_freevars_def, EVERY_APPEND])
     >- (fs [Once type_ctxts_cases, type_ctxt_cases, Once context_invariant_cases] >>
         metis_tac [type_e_freevars, type_v_freevars])
     >- metis_tac []
     >- (rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [bind_tvar_def] >>
         fs [bind_tvar_rewrites] >>
         metis_tac [type_v_freevars, type_e_freevars])
     >- (fs [is_ccon_def] >>
         fs [do_app_cases] >>
         rw [] >>
         fs [type_op_cases] >>
         rw [] >|
         [fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `[]` >>
              qexists_tac `exn_tenvC` >>
              qexists_tac `Tapp [] TC_int` >>
              rw [check_freevars_def] >>
              imp_res_tac type_e_exn >>
              qexists_tac `Empty` >>
              qexists_tac `0` >>
              fs [exn_env_def] >>
              rw [tenvM_ok_def, Once consistent_mod_cases, Once type_env_cases, emp_def],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `[]` >>
              qexists_tac `exn_tenvC` >>
              qexists_tac `Tapp [] TC_int` >>
              rw [check_freevars_def] >>
              imp_res_tac type_e_exn >>
              qexists_tac `Empty` >>
              qexists_tac `0` >>
              fs [exn_env_def] >>
              rw [tenvM_ok_def, Once consistent_mod_cases, Once type_env_cases, emp_def],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              fs [Tint_def] >>
              metis_tac [],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              fs [Tint_def] >>
              metis_tac [],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              fs [Tint_def] >>
              metis_tac [],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              fs [Tint_def] >>
              metis_tac [],
          fs [Tbool_def] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              imp_res_tac type_e_exn >>
              MAP_EVERY qexists_tac [`[]`, `exn_tenvC`, `Tapp [] TC_bool`, `Empty`, `0`] >>
              fs [exn_env_def] >>
              rw [tenvM_ok_def, Once consistent_mod_cases, Once type_env_cases, emp_def] >>
              metis_tac [check_freevars_def, EVERY_DEF],
          qpat_assum `type_v a ctMap senv (Closure l s' e) t1'`
                    (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
              fs [] >>
              rw [] >>
              rw [Once type_env_cases] >>
              fs [Tfn_def, bind_tvar_def] >>
              metis_tac [],
          qpat_assum `type_v a ctMap senv (Recclosure l l0 s') t1'`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
              fs [] >>
              rw [] >>
              imp_res_tac type_recfun_lookup >>
              rw [] >>
              qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `menv` >>
              qexists_tac `tenvC'` >>
              qexists_tac `t2` >>
              qexists_tac `bind_tenv n'' 0 t1 (bind_var_list 0 tenv'' (bind_tvar 0 tenv'))` >>
              rw [] >>
              rw [Once type_env_cases, bind_def, bind_tenv_def] >>
              fs [check_freevars_def] >>
              rw [build_rec_env_merge] >>
              fs [bind_tvar_def] >>
              qexists_tac `0` >>
              rw [] >>
              fs [bind_tenv_def] >>
              metis_tac [bind_tvar_def, type_recfun_env, type_env_merge],
          fs [] >>
              rw [Once type_e_cases] >>
              qpat_assum `type_v x1 x2 x3 x4 x5` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
              rw [] >>
              fs [store_assign_def, type_s_def, store_lookup_def] >>
              rw [EL_LUPDATE] >>
              qexists_tac `tenvS` >>
              fs [Tref_def] >> 
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `tenvC` >>
              qexists_tac `tenv` >>
              rw [] >>
              qexists_tac `0` >>
              rw [] >>
              metis_tac [check_freevars_def]])
     >- (fs [do_log_def] >>
         every_case_tac >>
         fs [] >>
         rw [] >>
         fs [Once type_v_cases_eqn] >>
         metis_tac [bind_tvar_def, type_e_rules])
     >- (fs [do_if_def] >>
         every_case_tac >>
         fs [] >>
         rw [] >>
         metis_tac [bind_tvar_def])
     >- (rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         fs [RES_FORALL] >>
         `check_freevars 0 [] t2` by metis_tac [type_ctxts_freevars] >>
         metis_tac [])
     >- (rw [Once type_ctxts_cases, type_ctxt_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         fs [RES_FORALL] >>
         `check_freevars 0 [] t2` by metis_tac [type_ctxts_freevars] >>
         metis_tac [])
     >- (fs [RES_FORALL, FORALL_PROD] >>
         rw [] >>
         metis_tac [bind_tvar_def, pmatch_type_preservation])
     >- (fs [is_ccon_def] >>
         rw [Once type_env_cases, bind_def] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t2` >>
         qexists_tac `bind_tenv s tvs t1 tenv` >>
         qexists_tac `0` >> 
         rw [emp_def, bind_tenv_def] >>
         rw [bind_tvar_def] >>
         metis_tac [bind_tenv_def])
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- metis_tac [do_con_check_build_conv, NOT_SOME_NONE]
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup_con_id cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac consistent_con_env_thm >>
         rw [Once type_v_cases_eqn] >>
         imp_res_tac type_es_length >>
         fs [] >>
         `ts2 = []` by
                 (cases_on `ts2` >>
                  fs []) >>
         fs [] >>
         rw [] >>
         rw [type_vs_end] >>
         fs [is_ccon_def] >>
         metis_tac [ctxt_inv_not_poly, rich_listTheory.MAP_REVERSE])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         rw [Once type_v_cases_eqn] >>
         imp_res_tac type_es_length >>
         fs [] >>
         `ts2 = []` by
         (cases_on `ts2` >>
         fs []) >>
         fs [] >>
         rw [] >>
         rw [type_vs_end] >>
         fs [is_ccon_def] >>
         metis_tac [ctxt_inv_not_poly, rich_listTheory.MAP_REVERSE, type_vs_end])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup_con_id cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac consistent_con_env_thm >>
         qpat_assum `type_es tenvM tenvC tenv' (e'::t'') ts2`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t''''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
         rw [] >>
         cases_on `ts2` >>
         fs [] >>
         rw [] >>
         qexists_tac `ts1++[t''']` >>
         rw [] >>
         metis_tac [type_vs_end])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup_con_id cn cenv'` >>
         fs [] >>
         qpat_assum `type_es tenvM tenvC tenv' (e'::t'') ts2`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t'''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp (ts1 ++ [t1] ++ t'''::ts) TC_tup` >>
         rw [] >>
         qexists_tac `ts1++[t1]` >>
         rw [] >>
         `tenv_ok (bind_tvar tvs tenv) ∧ (num_tvs tenv = 0)` 
                        by (rw [bind_tvar_rewrites] >>
                            metis_tac [type_v_freevars]) >>
         `check_freevars (num_tvs (bind_tvar tvs tenv)) [] t'''` 
                     by metis_tac [type_e_freevars] >>
         fs [bind_tvar_rewrites] >>
         metis_tac [type_vs_end, arithmeticTheory.ADD_0])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup_con_id cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac consistent_con_env_thm >>
         qpat_assum `type_es tenvM tenvC tenv' (e'::t'') ts2`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t''''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
         rw [] >>
         cases_on `ts2` >>
         fs [] >>
         rw [] >>
         qexists_tac `ts1++[t''']` >>
         rw [] >>
         metis_tac [type_vs_end])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         qpat_assum `type_es tenvM tenvC tenv' (e'::t'') ts2`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
         fs [] >>
         rw [type_ctxt_cases, Once type_ctxts_cases] >>
         ONCE_REWRITE_TAC [context_invariant_cases] >>
         rw [] >>
         qexists_tac `tenvS` >>
         rw [] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `t'''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenvC` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp (ts1 ++ [t1] ++ t'''::ts) TC_tup` >>
         rw [] >>
         qexists_tac `ts1++[t1]` >>
         rw [] >>
         `tenv_ok (bind_tvar tvs tenv) ∧ (num_tvs tenv = 0)` 
                        by (rw [bind_tvar_rewrites] >>
                            metis_tac [type_v_freevars]) >>
         `check_freevars (num_tvs (bind_tvar tvs tenv)) [] t'''` 
                     by metis_tac [type_e_freevars] >>
         fs [bind_tvar_rewrites] >>
         metis_tac [type_vs_end, arithmeticTheory.ADD_0])
     >- (cases_on `u` >>
         fs [type_uop_cases, do_uapp_def, store_alloc_def, LET_THM] >>
         rw [] >|
         [rw [Once type_v_cases_eqn] >>
              qexists_tac `bind (LENGTH st) t1 tenvS` >>
              rw [] >|
              [qexists_tac `Tref t1` >>
                   qexists_tac `0` >>
                   rw [] >>
                   `lookup (LENGTH st) tenvS = NONE`
                           by (fs [type_s_def, store_lookup_def] >>
                               `~(LENGTH st < LENGTH st)` by decide_tac >>
                               `~(?t. lookup (LENGTH st) tenvS = SOME t)` by metis_tac [] >>
                               fs [] >>
                               cases_on `lookup (LENGTH st) tenvS` >>
                               fs []) >|
                   [metis_tac [type_ctxts_weakening, weakCT_refl, weakC_refl, weakM_refl, weakS_bind],
                    fs [type_s_def, lookup_def, bind_def, store_lookup_def] >>
                        rw [] >-
                        decide_tac >|
                        [rw [rich_listTheory.EL_LENGTH_APPEND] >>
                             metis_tac [bind_def, type_v_weakening, weakS_bind, weakC_refl, weakM_refl, weakCT_refl],
                         `l < LENGTH st` by decide_tac >>
                             rw [rich_listTheory.EL_APPEND1] >>
                             metis_tac [type_v_weakening, weakS_bind, weakCT_refl, weakC_refl, weakM_refl, bind_def]],
                    rw [lookup_def, bind_def]],
               disj2_tac >>
                   qexists_tac `LENGTH st` >>
                   qexists_tac `t1` >>
                   rw [] >>
                   fs [type_s_def, store_lookup_def] >>
                   `~(LENGTH st < LENGTH st)` by decide_tac >>
                   `!t. lookup (LENGTH st) tenvS ≠ SOME t` by metis_tac [] >>
                   cases_on `lookup (LENGTH st) tenvS` >>
                   fs []],
          cases_on `v` >>
              fs [store_lookup_def] >>
              cases_on `n < LENGTH st` >>
              fs [] >>
              rw [] >>
              qpat_assum `type_v a0 a1 b2 c3 d4`
                     (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
               fs [type_s_def, store_lookup_def, Tref_def] >>
               metis_tac []])));

val store_type_extension_def = Define `
store_type_extension tenvS1 tenvS2 = 
  ?tenvS'. (tenvS2 = merge tenvS' tenvS1) ∧ 
           (!l. (lookup l tenvS' = NONE) ∨ (lookup l tenvS1 = NONE))`;

val store_type_extension_weakS = Q.store_thm ("store_type_extension_weakS",
`!tenvS1 tenvS2.
  store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1`,
rw [store_type_extension_def, weakS_def, lookup_append, merge_def] >>
rw [lookup_append] >>
cases_on `lookup l tenvS'` >>
rw [] >>
metis_tac [optionTheory.NOT_SOME_NONE]);

val exp_type_soundness_help = Q.prove (
`!state1 state2. e_step_reln^* state1 state2 ⇒
  ∀ctMap tenvS st env e c st' env' e' c' t dec_tvs.
    (state1 = (env,st,e,c)) ∧
    (state2 = (env',st',e',c')) ∧
    ctMap_has_exns ctMap ∧
    ctMap_ok ctMap ∧
    type_state dec_tvs ctMap tenvS state1 t
    ⇒
    ?tenvS'. type_state dec_tvs ctMap tenvS' state2 t ∧
             store_type_extension tenvS tenvS'`,
 ho_match_mp_tac RTC_INDUCT >>
 rw [e_step_reln_def] >-
 (rw [store_type_extension_def] >>
      qexists_tac `tenvS` >>
      rw [merge_def]) >>
 `?menv1' cenv1' envE1' store1' ev1' ctxt1'. state1' = ((menv1',cenv1',envE1'),store1',ev1',ctxt1')` by (PairCases_on `state1'` >> metis_tac []) >>
 `?menv cenv envE. env = (menv,cenv,envE)` by (PairCases_on `env` >> metis_tac []) >>
 `?tenvS'. type_state dec_tvs ctMap tenvS' state1' t ∧
                ((tenvS' = tenvS) ∨
                 ?l t. (lookup l tenvS = NONE) ∧ (tenvS' = bind l t tenvS))`
                        by metis_tac [exp_type_preservation] >>
 fs [] >>
 `store_type_extension tenvS tenvS'`
          by (fs [store_type_extension_def, merge_def] >>
              metis_tac [APPEND, bind_def, lookup_def]) >>
 rw [] >>
 res_tac >>
 qexists_tac `tenvS'` >>
 fs [store_type_extension_def, merge_def, bind_def, lookup_def, lookup_append] >>
 rw [] 
 >- metis_tac [] >>
 full_case_tac >>
 metis_tac [NOT_SOME_NONE]);

val exp_type_soundness = Q.store_thm ("exp_type_soundness",
`!tenvM ctMap tenvC tenvS tenv st e t menv cenv env tvs.
  tenvM_ok tenvM ∧
  ctMap_has_exns ctMap ∧
  consistent_mod_env tenvS ctMap menv tenvM ∧
  consistent_con_env ctMap cenv tenvC ∧
  type_env ctMap tenvS env tenv ∧
  type_s ctMap tenvS st ∧
  (tvs ≠ 0 ⇒ is_value e) ∧
  type_e tenvM tenvC (bind_tvar tvs tenv) e t
  ⇒
  e_diverges (menv,cenv,env) st e ∨
  (?st' r. (r ≠ Rerr Rtype_error) ∧ 
          small_eval (menv,cenv,env) st e [] (st',r) ∧
          (?tenvS'.
            type_s ctMap tenvS' st' ∧
            store_type_extension tenvS tenvS' ∧
            (!v. (r = Rval v) ⇒ type_v tvs ctMap tenvS' v t)))`,
 rw [e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 `type_state tvs ctMap tenvS ((menv,cenv,env),st,Exp e,[]) t`
         by (rw [type_state_cases] >>
             qexists_tac `tenvM` >>
             qexists_tac `tenvC` >>
             qexists_tac `t` >>
             qexists_tac `tenv` >>
             qexists_tac `tvs` >>
             rw [] >|
             [rw [Once context_invariant_cases],
              rw [Once type_ctxts_cases] >>
                  `num_tvs tenv = 0` by metis_tac [type_v_freevars] >>
                  `num_tvs (bind_tvar tvs tenv) = tvs`
                             by rw [bind_tvar_rewrites] >>
                  metis_tac [bind_tvar_rewrites, type_v_freevars, type_e_freevars]]) >>
 `?tenvS'. type_state tvs ctMap tenvS' (env',s',e',c') t ∧ store_type_extension tenvS tenvS'`
         by metis_tac [exp_type_soundness_help, consistent_con_env_def] >>
 fs [e_step_reln_def] >>
 `final_state (env',s',e',c')` by (PairCases_on `env'` >> metis_tac [exp_type_progress]) >>
 Cases_on `e'` >>
 Cases_on `c'` >>
 TRY (Cases_on `e''`) >>
 fs [final_state_def] >>
 qexists_tac `s'` 
 >- (fs [small_eval_def] >>
     fs [type_state_cases] >>
     fs [Once context_invariant_cases, Once type_ctxts_cases] >>
     metis_tac [small_eval_def, result_distinct, result_11])
 >- (fs [small_eval_def] >>
     fs [type_state_cases] >>
     fs [Once context_invariant_cases, Once type_ctxts_cases] >>
     rw [] >>
     fs [final_state_def] >>
     cases_on `t'` >>
     fs [final_state_def, type_ctxt_cases] >>
     metis_tac [small_eval_def, result_distinct, result_11, error_result_distinct]));

val store_type_extension_refl = Q.prove (
`!s. store_type_extension s s`,
 rw [store_type_extension_def] >>
 qexists_tac `[]` >>
 rw [merge_def]);

val dec_type_soundness = Q.store_thm ("dec_type_soundness",
`!mn tenvM tenvC tenv d tenvC' tenv' tenvS menv cenv env st.
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  tenvM_ok tenvM ∧
  ctMap_has_exns (to_ctMap tenvC) ∧
  consistent_con_env (to_ctMap tenvC) cenv tenvC ∧
  consistent_mod_env tenvS (to_ctMap tenvC) menv tenvM ∧
  type_env (to_ctMap tenvC) tenvS env tenv ∧
  type_s (to_ctMap tenvC) tenvS st
  ⇒
  dec_diverges (menv,cenv,env) st d ∨
  ?st' r tenvS'. 
     (r ≠ Rerr Rtype_error) ∧ 
     evaluate_dec mn (menv,cenv,env) st d (st', r) ∧
     store_type_extension tenvS tenvS' ∧
     type_s (to_ctMap tenvC) tenvS' st' ∧
     DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM (to_ctMap tenvC)) ∧
     (!cenv' env'. 
         (r = Rval (cenv',env')) ⇒
         (MAP FST cenv' = MAP FST tenvC') ∧
         consistent_con_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) (merge_envC (emp,cenv') cenv) (merge_tenvC (emp,tenvC') tenvC) ∧
         type_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) tenvS' (env' ++ env) (bind_var_list2 tenv' tenv) ∧
         type_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) tenvS' env' (bind_var_list2 tenv' Empty))`,
 rw [METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 fs [type_d_cases] >>
 rw [] >>
 fs [dec_diverges_def, merge_def, emp_def, evaluate_dec_cases] >>
 fs []
 >- (`∃st2 r tenvS'. r ≠ Rerr Rtype_error ∧ small_eval (menv,cenv,env) st e [] (st2,r) ∧
                type_s (to_ctMap tenvC) tenvS' st2 ∧ 
                store_type_extension tenvS tenvS' ∧
                (!v. (r = Rval v) ==> type_v tvs (to_ctMap tenvC) tenvS' v t)`
                         by metis_tac [exp_type_soundness] >>
     cases_on `r` >>
     fs []
     >- (`(pmatch cenv st2 p a [] = No_match) ∨
          (?new_env. pmatch cenv st2 p a [] = Match new_env)`
                   by (metis_tac [pmatch_type_progress])
         >- (MAP_EVERY qexists_tac [`st2`, `Rerr (Rraise (Conv (SOME ("Bind", TypeExn NONE)) []))`, `tenvS'`] >>
             rw []
             >- metis_tac [small_big_exp_equiv, all_env_to_cenv_def]
             >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST])
         >- (MAP_EVERY qexists_tac [`st2`, `Rval ([],new_env)`, `tenvS'`] >>
             `pmatch cenv st2 p a ([]++env) = Match (new_env++env)`
                      by metis_tac [pmatch_append] >>
             `type_env (to_ctMap tenvC) tenvS [] Empty` by metis_tac [type_v_rules, emp_def] >>
             `type_env (to_ctMap tenvC) tenvS' new_env (bind_var_list tvs tenv'' Empty) ∧
              type_env (to_ctMap tenvC) tenvS' (new_env ++ env) (bind_var_list tvs tenv'' tenv)` 
                          by (imp_res_tac pmatch_type_preservation >>
                              metis_tac [merge_def, APPEND, APPEND_NIL,type_v_weakening, weakM_refl, weakC_refl,
                                        store_type_extension_weakS, weakCT_refl, consistent_con_env_def]) >>
             rw []
             >- metis_tac [all_env_to_cenv_def, small_big_exp_equiv]
             >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST] >>
             rw [flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
             PairCases_on `tenvC` >>
             PairCases_on `cenv` >>
             rw [flat_to_ctMap_def, merge_envC_def, merge_def, merge_tenvC_def] >>
             metis_tac [bvl2_to_bvl, small_big_exp_equiv, all_env_to_cenv_def]))
     >- (MAP_EVERY qexists_tac [`st2`,`Rerr e'`,`tenvS'`] >>
         rw []
         >- (rw [store_type_extension_def, merge_def, to_ctMap_def] >>
             metis_tac [small_big_exp_equiv])
         >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST]))
 >- (`∃st2 r tenvS'. r ≠ Rerr Rtype_error ∧ small_eval (menv,cenv,env) st e [] (st2,r) ∧
                type_s (to_ctMap tenvC) tenvS' st2 ∧ 
                store_type_extension tenvS tenvS' ∧
                (!v. (r = Rval v) ==> type_v (0:num) (to_ctMap tenvC) tenvS' v t)`
                         by metis_tac [exp_type_soundness, bind_tvar_def] >>
     cases_on `r` >>
     fs []
     >- (`(pmatch cenv st2 p a [] = No_match) ∨
          (?new_env. pmatch cenv st2 p a [] = Match new_env)`
                    by (metis_tac [pmatch_type_progress])
         >- (MAP_EVERY qexists_tac [`st2`, `Rerr (Rraise (Conv (SOME ("Bind", TypeExn NONE)) []))`, `tenvS'`] >>
             rw []
             >- metis_tac [small_big_exp_equiv, all_env_to_cenv_def]
             >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST])
         >- (MAP_EVERY qexists_tac [`st2`, `Rval ([],new_env)`, `tenvS'`] >>
             `pmatch cenv st2 p a ([]++env) = Match (new_env++env)`
                        by metis_tac [pmatch_append] >>
             `type_p 0 tenvC p t tenv''` by metis_tac [] >>
             `type_env (to_ctMap tenvC) tenvS [] Empty` by metis_tac [type_v_rules, emp_def] >>
             `type_env (to_ctMap tenvC) tenvS' new_env (bind_var_list 0 tenv'' Empty) ∧
              type_env (to_ctMap tenvC) tenvS' (new_env ++ env) (bind_var_list 0 tenv'' tenv)`
                      by (imp_res_tac pmatch_type_preservation >>
                          metis_tac [merge_def, APPEND, APPEND_NIL, type_v_weakening, weakM_refl, weakC_refl,
                                    store_type_extension_weakS, weakCT_refl, consistent_con_env_def]) >>
             rw []
             >- metis_tac [all_env_to_cenv_def, small_big_exp_equiv]
             >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST] >>
             rw [flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
             PairCases_on `tenvC` >>
             PairCases_on `cenv` >>
             rw [flat_to_ctMap_def, merge_envC_def, merge_def, merge_tenvC_def] >>
             metis_tac [bvl2_to_bvl, small_big_exp_equiv, all_env_to_cenv_def]))
     >- (MAP_EVERY qexists_tac [`st2`,`Rerr e'`,`tenvS'`] >>
         rw []
         >- (rw [store_type_extension_def, merge_def, to_ctMap_def] >>
             metis_tac [small_big_exp_equiv])
         >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST]))
 >- (`type_env2 (to_ctMap tenvC) tenvS tvs (MAP (\(fn,n,e). (fn, Recclosure (menv,cenv,env) funs fn)) funs) tenv''`
                  by metis_tac [type_recfun_env] >>
     imp_res_tac type_env_merge_lem1 >>
     MAP_EVERY qexists_tac [`st`, `Rval ([],build_rec_env funs (menv,cenv,env) [])`, `tenvS`] >>
     rw [] 
     >- metis_tac [type_funs_distinct]
     >- metis_tac [store_type_extension_refl]
     >- rw [to_ctMap_def, flat_to_ctMap_list_def, flat_to_ctMap_def, FDOM_FUPDATE_LIST]
     >- (rw [flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
         PairCases_on `tenvC` >>
         PairCases_on `cenv` >>
         rw [flat_to_ctMap_def, merge_envC_def, merge_def, merge_tenvC_def]) >>
     rw [flat_to_ctMap_list_def, flat_to_ctMap_def, FUPDATE_LIST, FUNION_FEMPTY_1] >>
     fs [flat_to_ctMap_def, build_rec_env_merge, merge_def, emp_def] >>
     rw [store_type_extension_def, merge_def, to_ctMap_def] >>
     metis_tac [bvl2_to_bvl, type_env2_to_type_env, to_ctMap_def])
 >- (MAP_EVERY qexists_tac [`st`,`Rval (build_tdefs mn tdecs,[])`,`tenvS`] >>
     imp_res_tac extend_consistent_con >>
     fs [emp_def] >>
     rw []
     >- metis_tac [check_ctor_tenv_dups]
     >- metis_tac [store_type_extension_refl]
     >- metis_tac [check_ctor_disjoint_env]
     >- (rpt (pop_assum (fn _ => all_tac)) >>
        rw [build_tdefs_def, build_ctor_tenv_def] >>
        induct_on `tdecs` >>
        rw [] >>
        PairCases_on `h` >>
        rw [] >>
        induct_on `h2` >>
        rw [] >>
        PairCases_on `h` >>
        rw [])
     >- (rw [bind_var_list2_def] >>
         `weakCT (FUNION (flat_to_ctMap (build_ctor_tenv mn tdecs)) (to_ctMap tenvC)) (to_ctMap tenvC)`
                       by metis_tac [disjoint_env_weakCT, merge_def, check_ctor_disjoint_env] >>
         metis_tac [type_v_weakening, weakM_refl, weakC_refl, merge_def,
                    consistent_con_env_def, weakS_refl, ctMap_ok_def])
     >- metis_tac [type_env_eqn, emp_def, bind_var_list2_def])
 >- (qexists_tac `tenvS` >>
     `DISJOINT (FDOM (flat_to_ctMap (bind cn ([]:tvarN list,ts,TypeExn mn) []))) (FDOM (to_ctMap tenvC))`
                 by metis_tac [emp_def, check_exn_tenv_disjoint] >>
     rw []
     >- rw [store_type_extension_def, merge_def]
     >- rw [bind_def]
     >- metis_tac [extend_consistent_con_exn, merge_def, emp_def]
     >- (rw [bind_var_list2_def] >>
         `weakCT (FUNION  (flat_to_ctMap (bind cn ([],ts,TypeExn mn) [])) (to_ctMap tenvC)) (to_ctMap tenvC)`
                       by metis_tac [disjoint_env_weakCT, merge_def] >>
         `ctMap_ok (FUNION (flat_to_ctMap (bind cn ([],ts,TypeExn mn) [])) (to_ctMap tenvC))`
                       by (match_mp_tac ctMap_ok_merge_imp >>
                           fs [consistent_con_env_def] >>
                           rw [to_ctMap_def, bind_def, flat_to_ctMap_def, flat_to_ctMap_list_def, ctMap_ok_def,
                               FEVERY_ALL_FLOOKUP, flookup_fupdate_list] >>
                           every_case_tac >>
                           fs [] >>
                           rw [] >>
                           fs [check_exn_tenv_def]) >>
         metis_tac [type_v_weakening, weakM_refl, weakC_refl, merge_def,
                    consistent_con_env_def, weakS_refl])
     >- metis_tac [type_env_eqn, emp_def, bind_var_list2_def]));

val store_type_extension_trans = Q.prove (
`!tenvS1 tenvS2 tenvS3.
  store_type_extension tenvS1 tenvS2 ∧
  store_type_extension tenvS2 tenvS3 ⇒
  store_type_extension tenvS1 tenvS3`,
rw [store_type_extension_def, merge_def, lookup_append] >>
qexists_tac `tenvS'' ++ tenvS'` >>
fs [lookup_append] >>
rw [] >>
full_case_tac >-
metis_tac [] >>
qpat_assum `!l. P l` (MP_TAC o Q.SPEC `l`) >>
rw [] >>
every_case_tac >>
fs []);

val still_has_exns = Q.prove (
`!tenvC1 tenvC2.
  (DISJOINT (FDOM tenvC1) (FDOM tenvC2) ∨ DISJOINT (FDOM tenvC2) (FDOM tenvC1)) ∧
  ctMap_has_exns tenvC1
  ⇒
  ctMap_has_exns (FUNION tenvC2 tenvC1)`,
 rw [FLOOKUP_FUNION, ctMap_has_exns_def] >>
 every_case_tac >>
 fs [] >>
 fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
 metis_tac []);

val decs_type_soundness = Q.store_thm ("decs_type_soundness",
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  ∀tenvS menv cenv env st.
  tenvM_ok tenvM ∧
  ctMap_has_exns (to_ctMap tenvC) ∧
  consistent_mod_env tenvS (to_ctMap tenvC) menv tenvM ∧
  consistent_con_env (to_ctMap tenvC) cenv tenvC ∧
  type_env (to_ctMap tenvC) tenvS env tenv ∧
  type_s (to_ctMap tenvC) tenvS st
  ⇒
  decs_diverges mn (menv,cenv,env) st ds ∨
  ?st' r cenv' tenvS'. 
     (r ≠ Rerr Rtype_error) ∧ 
     evaluate_decs mn (menv,cenv,env) st ds (st', cenv', r) ∧
     store_type_extension tenvS tenvS' ∧
     DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM (to_ctMap tenvC)) ∧
     (!err.
         (r = Rerr err) ⇒
         (?tenvC1 tenvC2. 
           (tenvC' = tenvC1++tenvC2) ∧
           type_s (FUNION (flat_to_ctMap tenvC2) (to_ctMap tenvC)) tenvS' st' ∧
           consistent_con_env (FUNION (flat_to_ctMap tenvC2) (to_ctMap tenvC)) (merge_envC (emp,cenv') cenv) (merge_tenvC (emp,tenvC2) tenvC))) ∧
     (!env'. 
         (r = Rval env') ⇒
         (MAP FST cenv' = MAP FST tenvC') ∧
         consistent_con_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) (merge_envC (emp,cenv') cenv) (merge_tenvC (emp,tenvC') tenvC) ∧
         type_s (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) tenvS' st' ∧
         type_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) tenvS' env' (bind_var_list2 tenv' Empty) ∧
         type_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC)) tenvS' (env'++env) (bind_var_list2 tenv' tenv))`,
 ho_match_mp_tac type_ds_strongind >>
 rw [METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 rw [Once evaluate_decs_cases, bind_var_list2_def, emp_def] >>
 rw [] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once decs_diverges_cases]) >>
 fs [merge_def, emp_def, empty_to_ctMap]
 >- (qexists_tac `tenvS` >>
     rw [store_type_extension_def]
     >- (qexists_tac `[]` >>
          rw [merge_def])
     >- (PairCases_on `cenv` >>
         PairCases_on `tenvC` >>
         fs [merge_envC_def, merge_tenvC_def, merge_def])
     >- metis_tac [type_v_rules, emp_def])
 >- (`?st' r tenvS'. 
        (r ≠ Rerr Rtype_error) ∧ 
        evaluate_dec mn (menv,cenv,env) st d (st',r) ∧
        store_type_extension tenvS tenvS' ∧
        type_s (to_ctMap tenvC) tenvS' st' ∧
        DISJOINT (FDOM (flat_to_ctMap cenv')) (FDOM (to_ctMap tenvC)) ∧
        ∀cenv'' env''.
          (r = Rval (cenv'',env'')) ⇒
          (MAP FST cenv'' = MAP FST cenv') ∧
          consistent_con_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)) (merge_envC (emp,cenv'') cenv) (merge_tenvC (emp,cenv') tenvC) ∧
          type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)) tenvS' (env''++env) (bind_var_list2 tenv' tenv) ∧
          type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)) tenvS' env'' (bind_var_list2 tenv' Empty)`
                     by metis_tac [dec_type_soundness] >>
     `ctMap_has_exns (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC))` by metis_tac [still_has_exns] >>
     `ctMap_ok (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC))` by metis_tac [ctMap_ok_pres, consistent_con_env_def] >>
     `consistent_mod_env tenvS' (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)) menv tenvM` 
              by metis_tac [type_v_weakening, merge_def, store_type_extension_weakS, disjoint_env_weakCT, DISJOINT_SYM] >>
     `type_s (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)) tenvS' st'` 
                     by metis_tac [merge_def, disjoint_env_weakCT, weakM_refl, type_s_weakening] >>
     `(?cenv'' env''. r = Rval (cenv'',env'')) ∨ (?err. r = Rerr err)` 
                   by (cases_on `r` >> metis_tac [pair_CASES]) >>
     fs [] >>
     rw []
     >- (fs [to_ctMap_merge_empty, emp_def] >>
         rw [] >>
         `¬decs_diverges mn (menv, merge_envC ([],cenv'') cenv, env'' ++ env) st' ds` by metis_tac [] >>
         qpat_assum `∀tenvS' menv' cenv'' env' st'. P tenvS' menv' cenv'' env' st'`
                    (MP_TAC o Q.SPECL [`tenvS'`, `menv`, `merge_envC ([],cenv'') cenv`, `env''++env`, `st'`]) >>
         rw [] >>
         MAP_EVERY qexists_tac [`st'''`, `combine_dec_result env'' r`, `merge cenv''' cenv''`, `tenvS'''`] >>
         rw []
         >- (cases_on `r` >>
             rw [combine_dec_result_def])
         >- metis_tac [merge_def, result_case_def]
         >- metis_tac [store_type_extension_trans]
         >- (fs [flat_to_ctMap_append] >>
             metis_tac [DISJOINT_SYM])
         >- (cases_on `r` >> 
             fs [combine_dec_result_def] >> 
             rw [] >>
             metis_tac [FUNION_ASSOC, merge_def, flat_to_ctMap_append, merge_envC_empty_assoc, 
                        merge_tenvC_empty_assoc, APPEND_ASSOC])
         >- (cases_on `r` >>
             fs [merge_def, combine_dec_result_def])
         >- (cases_on `r` >> 
             fs [combine_dec_result_def] >> 
             rw [] >>
             metis_tac [APPEND_ASSOC, merge_def, flat_to_ctMap_append, merge_envC_empty_assoc, 
                        merge_tenvC_empty_assoc, FUNION_ASSOC])
         >- (cases_on `r` >> 
             fs [combine_dec_result_def, flat_to_ctMap_append] >> 
             rw [] >>
             metis_tac [FUNION_ASSOC])
         >- (cases_on `r` >> 
             fs [combine_dec_result_def] >> 
             rw [] >>
             `ctMap_ok (FUNION (flat_to_ctMap tenvC') (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)))` 
                             by metis_tac [consistent_con_env_def] >>
             fs [flat_to_ctMap_append] >>
             `DISJOINT (FDOM (flat_to_ctMap tenvC')) (FDOM (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC)))`
                        by rw [FDOM_FUNION] >>
             metis_tac [type_env_merge_bvl2, type_v_weakening,store_type_extension_weakS, 
                        disjoint_env_weakCT, DISJOINT_SYM, APPEND_ASSOC, 
                        FUNION_ASSOC, merge_def, weakM_refl])
         >- (cases_on `r` >> 
             fs [combine_dec_result_def] >> 
             rw [] >>
             metis_tac [FUNION_ASSOC, merge_def, bvl2_append, flat_to_ctMap_append]))
     >- (MAP_EVERY qexists_tac [`st'`, `Rerr err`, `[]`, `tenvS'`] >>
         rw [] >>
         imp_res_tac type_d_ctMap_ok >>
         imp_res_tac type_ds_ctMap_ok
         >- (fs [flat_to_ctMap_append, to_ctMap_merge_empty] >>
             metis_tac [DISJOINT_SYM])
         >- (MAP_EVERY qexists_tac [`tenvC'++cenv'`, `[]`] >>
             rw [empty_to_ctMap] >>
             PairCases_on `tenvC` >>
             PairCases_on `cenv` >>
             rw [merge_envC_def, merge_tenvC_def, merge_def]))));

val consistent_mod_env_dom = Q.prove (
`!tenvS ctMap menv tenvM.
  consistent_mod_env tenvS ctMap menv tenvM ⇒
  (MAP FST menv = MAP FST tenvM)`,
 induct_on `tenvM` >>
 rw [] >>
 cases_on `menv` >>
 fs [] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 rw [] >>
 fs [] >>
 res_tac);

val update_type_sound_inv_def = Define `
update_type_sound_inv top (tenvM:tenvM,tenvC:tenvC,tenv:tenvE,envM:envM,envC:envC,envE:envE,store) tenvM' tenvC' tenv' store' envC' r =
  case r of
     | Rval (envM',envE') => 
         (tenvM'++tenvM,merge_tenvC tenvC' tenvC,bind_var_list2 tenv' tenv,
          envM'++envM,merge_envC envC' envC,envE'++envE,store')
     | Rerr _ => (strip_mod_env tenvM'++tenvM,tenvC,tenv,strip_mod_env tenvM'++envM,merge_envC (top_to_cenv top) envC,envE,store')`;

val type_env_eqn = Q.prove (
`(!tenvM tenvC tenvS.
   type_env tenvC tenvS [] Empty = T) ∧
 (!tenvM tenvC tenvS n v n' tvs t envE tenv.
   type_env tenvC tenvS ((n,v)::envE) (Bind_name n' tvs t tenv) = 
     ((n = n') ∧ type_v tvs tenvC tenvS v t ∧ 
      type_env tenvC tenvS envE tenv))`,
rw [] >-
rw [Once type_v_cases, emp_def] >>
rw [Once type_v_cases, bind_def, bind_tenv_def] >>
metis_tac []);

val decs_to_cenv_dom = Q.prove (
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !envC mn'.
    (mn = SOME mn') ⇒
    (MAP FST (decs_to_cenv (SOME mn') ds) = MAP FST tenvC')`,
 ho_match_mp_tac type_ds_ind >>
 rw [type_d_cases, merge_def, decs_to_cenv_def, emp_def] >>
 fs [emp_def, bind_def, build_tdefs_def, build_ctor_tenv_def, dec_to_cenv_def] >>
 rpt (pop_assum (fn _ => all_tac)) >>
 induct_on `tdecs` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 induct_on `h2` >>
 rw [] >>
 PairCases_on `h` >>
 rw []);

val consistent_con_env_decs_to_cenv = Q.prove (
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !envC mn'.
    (mn = SOME mn') ∧
    consistent_con_env (to_ctMap tenvC) envC tenvC
    ⇒
    consistent_con_env (FUNION (flat_to_ctMap tenvC') (to_ctMap tenvC))
                       (merge_envC (emp,decs_to_cenv (SOME mn') ds) envC) 
                       (merge_tenvC (emp,tenvC') tenvC)`,
 ho_match_mp_tac type_ds_ind >>
 rw [decs_to_cenv_def, emp_def, empty_to_ctMap, merge_envC_empty] >>
 fs [dec_to_cenv_def, type_d_cases, merge_def, emp_def] >>
 rw [] >>
 fs [merge_envC_empty, flat_to_ctMap_append, to_ctMap_merge_empty, empty_to_ctMap] >>
 fs [FUNION_ASSOC]
 >- (FIRST_X_ASSUM (mp_tac o Q.SPEC `merge_envC ([],build_tdefs (SOME mn') (tdecs:type_def)) envC`) >>
     fs [merge_envC_empty_assoc, merge_tenvC_empty_assoc] >>
     rw [] >>
     metis_tac [emp_def, extend_consistent_con])
 >- (FIRST_X_ASSUM (mp_tac o Q.SPEC `merge_envC ([], bind cn (LENGTH (ts:t list),TypeExn (SOME mn')) []) envC`) >>
     fs [merge_envC_empty_assoc, merge_tenvC_empty_assoc] >>
     rw [] >>
     metis_tac [emp_def, extend_consistent_con_exn]));


val top_type_soundness = Q.store_thm ("top_type_soundness",
`!tenvM tenvC tenv envM envC envE store1 tenvM' tenvC' tenv' top.
  type_sound_invariants (tenvM,tenvC,tenv,envM,envC,envE,store1) ∧
  type_top tenvM tenvC tenv top tenvM' tenvC' tenv' ∧
  ¬top_diverges (envM, envC, envE) store1 top ⇒
  ?r cenv2 store2. 
    (r ≠ Rerr Rtype_error) ∧
    evaluate_top (envM, envC, envE) store1 top (store2,cenv2,r) ∧
    type_sound_invariants (update_type_sound_inv top (tenvM,tenvC,tenv,envM,envC,envE,store1) tenvM' tenvC' tenv' store2 cenv2 r)`,
 rw [type_sound_invariants_def] >>
 `num_tvs tenv = 0` by metis_tac [type_v_freevars] >>
 fs [type_top_cases, top_diverges_cases] >>
 rw [evaluate_top_cases]
 >- (`weakCT_only_other_mods NONE (to_ctMap tenvC_no_sig) (to_ctMap tenvC)` 
          by (fs [weakCT_only_other_mods_def, weakenCT_only_mods_def] >>
              rw [] >>
              cases_on `tn` >>
              fs [FLOOKUP_DEF] >>
              TRY (cases_on `i`) >>
              TRY (cases_on `o'`) >>
              fs [] >>
              res_tac >>
              fs [] >>
              metis_tac [pair_CASES]) >>
     `type_d NONE tenvM_no_sig tenvC_no_sig tenv d cenv' tenv'` 
                    by metis_tac [type_d_weakening, consistent_con_env_def] >>
     `?r store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_dec NONE (envM, envC, envE) store1 d (store2,r) ∧
        store_type_extension tenvS tenvS' ∧
        type_s (to_ctMap tenvC_no_sig) tenvS' store2 ∧
        DISJOINT (FDOM (flat_to_ctMap cenv')) (FDOM (to_ctMap tenvC_no_sig)) ∧
        ∀cenv1 env1.
         (r = Rval (cenv1,env1)) ⇒
         consistent_con_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) (merge_envC (emp,cenv1) envC) (merge_tenvC (emp,cenv') tenvC_no_sig) ∧
         type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS'
           (env1 ++ envE) (bind_var_list2 tenv' tenv) ∧
         type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS' env1
           (bind_var_list2 tenv' Empty)`
                by metis_tac [dec_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?cenv1 env1. r = Rval (cenv1,env1))` 
                by (cases_on `r` >> metis_tac [pair_CASES]) >>
     rw []
     >- (MAP_EVERY qexists_tac [`Rerr err`, `(emp,emp)`, `store2`] >>
         rw [type_sound_invariants_def, update_type_sound_inv_def] >>
         MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `tenvC_no_sig`] >>
         rw [replTheory.strip_mod_env_def, emp_def]
         >- metis_tac [type_v_weakening, store_type_extension_weakS, weakCT_refl, consistent_con_env_def]
         >- (rw [top_to_cenv_def] >>
             cases_on `d` >>
             fs [evaluate_dec_cases, dec_to_cenv_def] >>
             Cases_on `envC` >>
             rw [merge_envC_def, merge_def, emp_def])
         >- metis_tac [type_v_weakening, store_type_extension_weakS, consistent_con_env_def, weakCT_refl, weakM_refl])
     >- (MAP_EVERY qexists_tac [`Rval (emp,env1)`,`(emp,cenv1)`, `store2`] >>
         imp_res_tac type_d_mod >>
         rw [type_sound_invariants_def, update_type_sound_inv_def] >>
         `weakCT (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) (to_ctMap tenvC_no_sig)`
                    by metis_tac [merge_def, disjoint_env_weakCT] >>
         MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `merge_tenvC (emp,cenv') tenvC_no_sig`] >>
         rw [emp_def, to_ctMap_merge_empty]
         >- metis_tac [still_has_exns]
         >- (rw [ctMap_to_mods_append] >>
             fs [SUBSET_DEF])
         >- (PairCases_on `tenvC_no_sig` >>
             fs [merge_def, merge_tenvC_def])
         >- metis_tac [type_v_weakening, store_type_extension_weakS, consistent_con_env_def, weakCT_refl]
         >- metis_tac [emp_def]
         >- metis_tac [type_s_weakening, weakM_refl, consistent_con_env_def]
         >- metis_tac [weakC_merge, merge_def]
         >- (fs [weakenCT_only_mods_def] >>
             rw [FLOOKUP_FUNION] >>
             every_case_tac >>
             fs [] >>
             metis_tac [])))
 >- metis_tac [consistent_mod_env_dom, all_env_to_menv_def]
 >- (`weakCT_only_other_mods (SOME mn) (to_ctMap tenvC_no_sig) (to_ctMap tenvC)`
          by (fs [weakCT_only_other_mods_def, weakenCT_only_mods_def, ctMap_to_mods_def, SUBSET_DEF] >>
              rw [] >>
              cases_on `tn` >>
              fs [FLOOKUP_DEF] >>
              TRY (cases_on `i`) >>
              TRY (cases_on `o'`) >>
              fs [] >>
              every_case_tac >>
              fs [] >> 
              res_tac >>
              fs [MEM_MAP] >>
              rw [] >>
              metis_tac [FST, pair_CASES]) >>
     `type_ds (SOME mn) tenvM_no_sig tenvC_no_sig tenv ds cenv' tenv''`
              by metis_tac [type_ds_weakening, consistent_con_env_def, tenvC_ok_ctMap] >>
     `?r cenv2 store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_decs (SOME mn) (envM, envC, envE) store1 ds (store2,cenv2,r) ∧
        store_type_extension tenvS tenvS' ∧
        DISJOINT (FDOM (flat_to_ctMap cenv')) (FDOM (to_ctMap tenvC_no_sig)) ∧
        (∀err.
           r = Rerr err ⇒
           ∃tenvC1 tenvC2.
             cenv' = tenvC1 ++ tenvC2 ∧
             type_s (FUNION (flat_to_ctMap tenvC2) (to_ctMap tenvC_no_sig)) tenvS' store2 ∧
             consistent_con_env (FUNION (flat_to_ctMap tenvC2) (to_ctMap tenvC_no_sig)) (merge_envC (emp,cenv2) envC) (merge_tenvC (emp,tenvC2) tenvC_no_sig)) ∧
        (∀env'.
           r = Rval env' ⇒
           MAP FST cenv' = MAP FST cenv2 ∧
           type_s (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS' store2 ∧
           consistent_con_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) (merge_envC (emp,cenv2) envC) (merge_tenvC (emp,cenv') tenvC_no_sig) ∧
           type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS' env' (bind_var_list2 tenv'' Empty) ∧
           type_env (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS' (env' ++ envE) (bind_var_list2 tenv'' tenv))`
                      by metis_tac [decs_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?env2. r = Rval env2)` 
                by (cases_on `r` >> metis_tac []) >>
     rw []
     >- (MAP_EVERY qexists_tac [`Rerr err`, `([(mn,cenv2)],emp)`, `store2`] >>
         imp_res_tac type_ds_mod >>
         imp_res_tac type_ds_ctMap_ok >>
         `ctMap_ok (FUNION (flat_to_ctMap (tenvC1 ++ tenvC2)) (to_ctMap tenvC_no_sig))`
                  by (match_mp_tac ctMap_ok_merge_imp >>
                      fs [to_ctMap_def, consistent_con_env_def, ctMap_ok_def]) >>
         rw [type_sound_invariants_def, update_type_sound_inv_def] >-
         metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
         `weakM (bind mn [] tenvM_no_sig) tenvM_no_sig`
                      by (match_mp_tac weakM_bind >>
                          rw [weakM_refl]) >>
         `weakCT (FUNION (flat_to_ctMap (tenvC1 ++ tenvC2)) (to_ctMap tenvC_no_sig)) (to_ctMap tenvC_no_sig)` 
                      by (match_mp_tac disjoint_env_weakCT >>
                          rw [] >>
                          fs []) >>
         fs [bind_def, merge_def] >>
         `tenvM_ok ((mn,[])::tenvM_no_sig)` by fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def] >>
         `DISJOINT (FDOM (to_ctMap ([(mn,tenvC1 ++ tenvC2)],emp))) (FDOM (to_ctMap tenvC_no_sig))`
                       by (fs [to_ctMap_def, to_ctMap_list_def, emp_def, flat_to_ctMap_list_def,
                               flat_to_ctMap_def]) >>
         `weakCT (FUNION (flat_to_ctMap (tenvC1 ++ tenvC2)) (to_ctMap tenvC_no_sig))
                 (FUNION (flat_to_ctMap tenvC2) (to_ctMap tenvC_no_sig))`
                 by (rw [flat_to_ctMap_append, GSYM FUNION_ASSOC] >>
                     match_mp_tac disjoint_env_weakCT >>
                     fs [FDOM_FUNION, flat_to_ctMap_list_append, ALL_DISTINCT_APPEND,
                         DISJOINT_DEF, EXTENSION, flat_to_ctMap_def, FDOM_FUPDATE_LIST,
                         MEM_MAP, MEM_REVERSE] >>
                     metis_tac []) >>
         MAP_EVERY qexists_tac [`tenvS'`, `(mn,[])::tenvM_no_sig`, `merge_tenvC ([(mn, tenvC1++tenvC2)],emp) tenvC_no_sig`] >>
         rw [to_ctMap_merge, to_ctMap_one_mod]
         >- metis_tac [still_has_exns]
         >- (rw [replTheory.strip_mod_env_def] >>
             fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def])
         >- (fs [ctMap_to_mods_append, SUBSET_DEF] >>
             rw [] >>
             metis_tac [])
         >- rw [replTheory.strip_mod_env_def]
         >- (PairCases_on `tenvC_no_sig` >>
             fs [merge_def, merge_tenvC_def])
         >- (rw [Once type_v_cases, replTheory.strip_mod_env_def, bind_var_list2_def, type_env_eqn] >>
             metis_tac [merge_def, type_v_weakening, store_type_extension_weakS])
         >- (rw [top_to_cenv_def] >>
             match_mp_tac consistent_con_env_to_mod >>
             rw []
             >- metis_tac [decs_to_cenv_dom, MAP_APPEND]
             >- metis_tac [consistent_con_env_weakening]
             >- metis_tac [consistent_con_env_decs_to_cenv])
         >- metis_tac [APPEND_ASSOC, merge_def, type_v_weakening, store_type_extension_weakS]
         >- metis_tac [type_s_weakening, store_type_extension_weakS, merge_def]
         >- (rw [replTheory.strip_mod_env_def] >>
             rw [GSYM bind_def] >>
             match_mp_tac weakM_bind2 >>
             rw [bind_def, tenv_ok_def, bind_var_list2_def])
         >- metis_tac [weakC_merge_one_mod]
         >- metis_tac [weakenCT_only_mods_pres])
     >- (MAP_EVERY qexists_tac [`Rval ([(mn,env2)],emp)`, `([(mn,cenv2)],emp)`, `store2`] >>
         imp_res_tac type_ds_ctMap_ok >>
         imp_res_tac type_ds_mod >>
         `ctMap_ok (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig))`
                 by (fs [to_ctMap_def, consistent_con_env_def, ctMap_ok_def]) >>
         rw [type_sound_invariants_def, update_type_sound_inv_def] >-
         metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
         `tenvM_ok (bind mn tenv'' tenvM_no_sig)`
                   by metis_tac [tenvM_ok_pres, type_v_freevars] >>
         `type_s (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) tenvS' store2`
                  by metis_tac [type_s_weakening, weakC_refl, weakM_bind, weakM_refl] >>
         `tenv_ok (bind_var_list2 emp Empty)`
                      by (metis_tac [emp_def, tenv_ok_def, bind_var_list2_def]) >>
         `tenv_ok (bind_var_list2 tenv''' Empty)`
                      by (fs [check_signature_cases] >>
                          metis_tac [type_v_freevars, type_specs_tenv_ok]) >>
         `weakCT (FUNION (flat_to_ctMap cenv') (to_ctMap tenvC_no_sig)) (to_ctMap tenvC_no_sig)` 
                      by (match_mp_tac disjoint_env_weakCT >>
                          rw [] >>
                          fs []) >>
         MAP_EVERY qexists_tac [`tenvS'`, `bind mn tenv'' tenvM_no_sig`, `merge_tenvC ([(mn,cenv')],emp) tenvC_no_sig`] >>
         rw [to_ctMap_merge, to_ctMap_one_mod, emp_def]
         >- metis_tac [still_has_exns]
         >- metis_tac [tenvM_ok_pres, bind_def]
         >- (fs [bind_def, ctMap_to_mods_append, SUBSET_DEF] >>
             rw [] >>
             metis_tac [])
         >- rw [bind_def]
         >- (PairCases_on `tenvC_no_sig` >>
             fs [bind_def, merge_tenvC_def, merge_def])
         >- (rw [bind_def, Once type_v_cases] >>
             metis_tac [type_v_weakening,store_type_extension_weakS, weakM_bind,tenvC_ok_ctMap,
                        weakM_refl, bind_def, merge_def, disjoint_env_weakCT, DISJOINT_SYM])
         >- metis_tac [emp_def, consistent_con_env_to_mod, consistent_con_env_weakening]
         >- (rw [bind_var_list2_def] >>
             metis_tac [merge_def, type_v_weakening,store_type_extension_weakS])
         >- (`weakE tenv'' tenv'''` by (fs [check_signature_cases] >> metis_tac [weakE_refl]) >>
             metis_tac [bind_def, weakM_bind'])
         >- (fs [check_signature_cases] >>
             metis_tac [weakC_merge_one_mod2, flat_weakC_refl, emp_def])
         >- (match_mp_tac weaken_CT_only_mods_add >>
             rw [] >>
             fs [check_signature_cases] >>
             `ctMap_to_mods (flat_to_ctMap (emp:flat_tenvC)) ⊆ {SOME mn}` 
                       by rw [ctMap_to_mods_def, flat_to_ctMap_def, emp_def, flat_to_ctMap_list_def,
                              FDOM_FUPDATE_LIST] >>
             metis_tac [type_specs_mod]))));

val thms = [to_ctMap_def, init_tenvC_def, emp_def, to_ctMap_list_def, flat_to_ctMap_list_def]; 

val to_ctMap_init_tenvC = 
  SIMP_CONV (srw_ss()) thms ``to_ctMap init_tenvC``;

val type_check_v_tac = 
 rw [Once type_v_cases, type_env_eqn, Tfn_def, Tint_def, Tbool_def, Tref_def] >>
 MAP_EVERY qexists_tac [`[]`, `init_tenvC`, `Empty`] >>
 rw [tenvM_ok_def, type_env_eqn, check_freevars_def, Once consistent_mod_cases] >>
 NTAC 10 (rw [Once type_e_cases, Tfn_def, Tint_def, Tbool_def, num_tvs_def, bind_tvar_def,
              t_lookup_var_id_def, check_freevars_def, lookup_tenv_def, bind_tenv_def,
              deBruijn_inc_def, deBruijn_subst_def,
              METIS_PROVE [] ``(?x. P ∧ Q x) = (P ∧ ?x. Q x)``,
              LENGTH_NIL_SYM, type_op_cases, Tref_def, type_uop_cases]);

val initial_type_sound_invariants = Q.store_thm ("initial_type_sound_invariant",
`type_sound_invariants ([],init_tenvC,init_tenv,[],init_envC,init_env,[])`,
 rw [type_sound_invariants_def] >>
 MAP_EVERY qexists_tac [`[]`, `init_tenvC`] >>
 `consistent_con_env (to_ctMap (init_tenvC:tenvC)) init_envC init_tenvC`
         by (rw [to_ctMap_init_tenvC] >>
             rw [consistent_con_env_def, init_envC_def, init_tenvC_def, emp_def, tenvC_ok_def, 
                 flat_tenvC_ok_def, check_freevars_def, ctMap_ok_def, FEVERY_ALL_FLOOKUP,
                 flookup_fupdate_list, lookup_con_id_def]
             >- (every_case_tac >>
                 fs [] >>
                 rw [check_freevars_def])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])) >>
 rw []
 >- rw [tenvM_ok_def]
 >- rw [ctMap_has_exns_def, to_ctMap_init_tenvC, flookup_fupdate_list]
 >- rw [tenvM_ok_def]
 >- rw [ctMap_to_mods_def, to_ctMap_init_tenvC, SUBSET_DEF, FDOM_FUPDATE_LIST]
 >- rw [init_tenvC_def, emp_def]
 >- rw [Once type_v_cases]
 >- (rw [init_env_def, emp_def, init_tenv_def, type_env_eqn] >>
     type_check_v_tac)
 >- rw [type_s_def, store_lookup_def] 
 >- rw [weakM_def]
 >- rw [weakC_refl]
 >- rw [weakenCT_only_mods_refl]);

val _ = export_theory ();
