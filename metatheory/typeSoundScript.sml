open preamble;
open pairTheory optionTheory;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory;
open smallStepTheory bigStepTheory replTheory;
open terminationTheory;
open weakeningTheory typeSysPropsTheory bigSmallEquivTheory;
open initialEnvTheory;
open typeSoundInvariantsTheory bigClockTheory;

val _ = new_theory "typeSound";

val type_v_cases_eqn = List.nth (CONJUNCTS type_v_cases, 0);
val type_vs_cases_eqn = List.nth (CONJUNCTS type_v_cases, 1);
val type_env_cases = List.nth (CONJUNCTS type_v_cases, 2);
val consistent_mod_cases = List.nth (CONJUNCTS type_v_cases, 3);

val build_rec_env_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure env funs' f) env') env' funs =
merge (MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs) env'`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
`∀funs funs' env env'.
  build_rec_env funs env env' =
  merge (MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs) env'`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val consistent_con_env_lookup = Q.prove (
`!tenvCT envC tenvC cn tvs ts tn.
  consistent_con_env tenvCT envC tenvC ∧
  lookup cn tenvC = SOME (tvs,ts,tn)
  ⇒
  lookup (cn,tn) tenvCT = SOME (tvs, ts)`,
 rw [consistent_con_env_def] >>
 cases_on `lookup cn envC` >>
 fs [] >>
 res_tac >>
 fs [] >>
 PairCases_on `x` >>
 res_tac >>
 fs [] >>
 rw []);
 
val type_ctxts_freevars = Q.prove (
`!tvs tenvCT tenvS cs t1 t2.
  type_ctxts tvs tenvCT tenvS cs t1 t2 ⇒
  tenvCT_ok tenvCT ⇒
  check_freevars tvs [] t1 ∧ check_freevars tvs [] t2`,
 ho_match_mp_tac type_ctxts_ind >>
 rw [type_ctxt_cases, check_freevars_def, Tbool_def] >>
 rw [check_freevars_def] 
 >- rw [Texn_def, check_freevars_def]
 >- (cases_on `pes` >>
     fs [RES_FORALL] >>
     qpat_assum `!x. (x = h) ∨ MEM x t ⇒ P x` (ASSUME_TAC o Q.SPEC `h`) >>
     fs [] >>
     PairCases_on `h` >>
     fs [] >>
     fs [Once context_invariant_cases] >>
     metis_tac [type_p_freevars])
 >- (imp_res_tac tenvCT_ok_lookup >>
     fs [] >>
     match_mp_tac check_freevars_subst_single >>
     rw [] >>
     imp_res_tac consistent_con_env_lookup >>
     res_tac >>
     fs [] >>
     metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ,
                arithmeticTheory.GREATER_EQ])
 >- rw [Texn_def, check_freevars_def]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
 >- metis_tac [check_freevars_add, arithmeticTheory.ZERO_LESS_EQ, arithmeticTheory.GREATER_EQ]
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
 >- (imp_res_tac tenvCT_ok_lookup >>
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

(* Everything in the type environment is also in the execution environment *)
val type_lookup_lem = Q.prove (
`∀tenvC env tenvS tenv v n t' idx.
  type_env tenvC tenvS env tenv ∧
  (lookup_tenv n idx tenv = SOME t')
  ⇒
  (∃v'. lookup n env = SOME v')`,
induct_on `tenv` >>
rw [Once type_v_cases, lookup_def, bind_def] >>
fs [lookup_tenv_def, bind_tenv_def] >-
metis_tac [] >>
every_case_tac >>
fs [] >>
metis_tac []);

val type_lookup = Q.prove (
`∀tenvC env tenvS tenv v n t' idx tvs.
  type_env tenvC tenvS env tenv ∧
  (lookup_tenv n idx (bind_tvar tvs tenv) = SOME t')
  ⇒
  (∃v'. lookup n env = SOME v')`,
induct_on `tvs` >>
rw [bind_tvar_def] >-
metis_tac [type_lookup_lem] >>
fs [bind_tvar_def, lookup_tenv_def] >>
rw [] >>
every_case_tac >>
fs [lookup_tenv_def] >>
`!x y. x + SUC y = (x + 1) + y` by decide_tac >>
metis_tac []);

val type_lookup_id = Q.prove (
`∀tenvS tenvC menv tenvM (cenv : envC) tenv.
  type_env tenvC tenvS env tenv ∧
  consistent_mod_env tenvS tenvC menv tenvM 
  ⇒
  ((t_lookup_var_id n tenvM (bind_tvar tvs tenv) = SOME (tvs', t)) ⇒ 
     (∃v. (lookup_var_id n (menv,cenv,env) = SOME v)))`,
 induct_on `tenvM` >>
 rw [t_lookup_var_id_def] >>
 cases_on `n` >>
 fs [] >>
 rw [lookup_var_id_def, t_lookup_var_id_def] >>
 imp_res_tac type_lookup
 >- (Cases_on `v'` >>
     fs [])
 >- (Cases_on `v'` >>
     fs [])
 >- (qpat_assum `consistent_mod_env tenvS x0 x1 x2` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     rw [] >>
     fs [t_lookup_var_id_def, lookup_var_id_def]
     >- (match_mp_tac type_lookup >>
         cases_on `lookup mn' tenvM` >>
         fs [lookup_tenv_def, bind_tvar_def, bvl2_lookup] >>
         metis_tac [])
     >- metis_tac []));

val type_vs_length_lem = Q.prove (
`∀tvs tenvC tenvS vs ts.
  type_vs tvs tenvC tenvS vs ts ⇒ (LENGTH vs = LENGTH ts)`,
induct_on `vs` >>
rw [Once type_v_cases] >>
rw [] >>
metis_tac []);

(* Typing lists of values from the end *)
val type_vs_end_lem = Q.prove (
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
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
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
`(∀cenv st p v env t tenv tenvS tvs tvs'' tenvC tenvCT.
  consistent_con_env tenvCT cenv tenvC ∧
  type_p tvs'' tenvC p t tenv ∧
  type_v tvs tenvCT tenvS v t ∧
  type_s tenvCT tenvS st
  ⇒
  (pmatch cenv st p v env = No_match) ∨
  (∃env'. pmatch cenv st p v env = Match env')) ∧
 (∀cenv st ps vs env ts tenv tenvS tvs tvs'' tenvC tenvCT.
  consistent_con_env tenvCT cenv tenvC ∧
  type_ps tvs'' tenvC ps ts tenv ∧
  type_vs tvs tenvCT tenvS vs ts ∧
  type_s tenvCT tenvS st
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
     cases_on `lookup n cenv` >>
     rw [] >>
     imp_res_tac consistent_con_env_lookup >>
     fs [consistent_con_env_def] >-
     metis_tac [NOT_SOME_NONE] >>
     PairCases_on `x` >>
     fs [] >>
     rw [] >>
     fs [tid_exn_to_tc_11]
     >- metis_tac [] >>
     metis_tac [type_ps_length, type_vs_length_lem, LENGTH_MAP, SOME_11, PAIR_EQ])
 >- (fs [Once type_p_cases, Once type_v_cases] >>
     fs [consistent_con_env_def] >>
     rw [] >>
     fs [tid_exn_to_tc_11] >>
     fs [] >>
     fs [] >>
     rw [] >>
     every_case_tac >>
     fs [] >-
     metis_tac [NOT_SOME_NONE] >>
     metis_tac [type_ps_length, type_vs_length_lem, LENGTH_MAP, SOME_11, PAIR_EQ])
 >- (qpat_assum `type_v b c d e f` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     qpat_assum `type_p b0 a b c d` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     every_case_tac >>
     rw [] >>
     metis_tac [])
 >- (fs [Once type_p_cases, Once type_v_cases] >>
     rw [] >>
     imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length_lem >>
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
     qpat_assum `type_vs tvs tenvCT tenvS (v::vs) ts`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [])
 >- (imp_res_tac type_ps_length >>
     imp_res_tac type_vs_length_lem >>
     fs [] >>
     cases_on `ts` >>
     fs [])
 >- (imp_res_tac type_ps_length >> imp_res_tac type_vs_length_lem >>
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
`(!v1 v2 tvs tenvCT cns tenvS t.
  type_v tvs tenvCT tenvS v1 t ∧
  type_v tvs tenvCT tenvS v2 t 
  ⇒
  do_eq v1 v2 ≠ Eq_type_error) ∧
(!vs1 vs2 tvs tenvCT cns tenvS ts.
  type_vs tvs tenvCT tenvS vs1 ts ∧
  type_vs tvs tenvCT tenvS vs2 ts 
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
     qpat_assum `!x. P x` (mp_tac o Q.SPECL [`tvs`, `tenvCT`, `tenvS`, `ts'`]) >>
     rw [METIS_PROVE [] ``(a ∨ b) = (~a ⇒ b)``] >>
     cases_on `vs1` >>
     fs [] >-
     fs [Once type_vs_cases_eqn] >>
     cases_on `ts'` >>
     fs [] >>
     fs [Once type_vs_cases_eqn])
 >- metis_tac []);

val consistent_con_env_thm = Q.prove (
`∀tenvCT cenv tenvC.
     consistent_con_env tenvCT cenv tenvC ⇒
     ∀cn tvs ts tn.
       (lookup cn tenvC = SOME (tvs,ts,tn) ⇒
        lookup cn cenv = SOME (LENGTH ts,tn)) ∧
       (lookup cn tenvC = NONE ⇒ lookup cn cenv = NONE)`,
 rw [consistent_con_env_def] >>
 cases_on `lookup cn cenv` >>
 rw []
 >- metis_tac [NOT_SOME_NONE]
 >- (PairCases_on `x` >>
     fs [] >>
     metis_tac [PAIR_EQ, SOME_11])
 >- metis_tac [pair_CASES, SOME_11, PAIR_EQ, NOT_SOME_NONE]);

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
          fs [],
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
          srw_tac [ARITH_ss] [] >> 
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
          imp_res_tac type_vs_length_lem >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def] >>
          `LENGTH ts2 = 0` by decide_tac >>
          cases_on `es` >>
          fs [],
      fs [all_env_to_cenv_def] >>
          every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length_lem >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def],
      every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length_lem >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def],
      every_case_tac >>
          fs [] >>
          imp_res_tac consistent_con_env_thm >>
          imp_res_tac type_es_length >>
          imp_res_tac type_vs_length_lem >>
          full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def,lookup_def, build_conv_def]]));

(* A successful pattern match gives a binding environment with the type given by
* the pattern type checker *)
val pmatch_type_preservation = Q.prove (
`(∀(cenv : envC) st p v env env' (tenvC:tenvC) tenvCT tenv t tenv' tenvS tvs.
  (pmatch cenv st p v env = Match env') ∧
  consistent_con_env tenvCT cenv tenvC ∧
  type_v tvs tenvCT tenvS v t ∧
  type_p tvs tenvC p t tenv' ∧
  type_s tenvCT tenvS st ∧
  type_env tenvCT tenvS env tenv ⇒
  type_env tenvCT tenvS env' (bind_var_list tvs tenv' tenv)) ∧
 (∀(cenv : envC) st ps vs env env' (tenvC:tenvC) tenvCT tenv tenv' ts tenvS tvs.
  (pmatch_list cenv st ps vs env = Match env') ∧
  consistent_con_env tenvCT cenv tenvC ∧
  type_vs tvs tenvCT tenvS vs ts ∧
  type_ps tvs tenvC ps ts tenv' ∧
  type_s tenvCT tenvS st ∧
  type_env tenvCT tenvS env tenv ⇒
  type_env tenvCT tenvS env' (bind_var_list tvs tenv' tenv))`,
 ho_match_mp_tac pmatch_ind >>
 rw [pmatch_def]
 >- (fs [Once type_p_cases, bind_var_list_def, bind_def] >>
     rw [] >>
     rw [Once type_v_cases] >>
     rw [emp_def, bind_def, bind_tenv_def])
 >- fs [Once type_p_cases, bind_var_list_def]
 >- (cases_on `lookup n cenv` >>
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
     metis_tac [])
 >- (every_case_tac >>
     fs [])
 >- (cases_on `(LENGTH ps = x0) ∧ (LENGTH vs = x0)` >>
     fs [] >>
     fs [] >>
     qpat_assum `type_v tvs tenvCT senv vpat t`
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
     `type_v tvs tenvCT tenvS (EL lnum st) t''` by
                 metis_tac [type_v_weakening, weakCT_refl, weakS_refl, weakM_refl] >>
     metis_tac [])
 >- fs [Once type_p_cases, bind_var_list_def]
 >- (every_case_tac >>
     fs [] >>
     qpat_assum `type_vs tva tenvCT senv (v::vs) ts`
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
`∀fn funs funs' tenvM tenvC tenvCT tenv tenv' tenv0 env tenvS tvs.
  tenvM_ok tenvM ∧
  envC_has_exns cenv ∧
  consistent_con_env tenvCT cenv tenvC ∧
  consistent_mod_env tenvS tenvCT menv tenvM ∧
  (!fn t. (lookup fn tenv = SOME t) ⇒ (lookup fn tenv' = SOME t)) ∧
  type_env tenvCT tenvS env tenv0 ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv' (bind_tvar tvs tenv0)) funs' tenv' ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv' (bind_tvar tvs tenv0)) funs tenv
  ⇒
  type_env2 tenvCT tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs) tenv`,
induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
fs [emp_def] >>
rw [bind_def, Once type_v_cases, type_env2_def] >>
`type_env2 tenvCT tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs) env'`
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
`∀fn funs tenvM tenvC tenvCT tenvS tvs tenv tenv0 menv cenv env.
  tenvM_ok tenvM ∧
  envC_has_exns cenv ∧
  consistent_con_env tenvCT cenv tenvC ∧
  consistent_mod_env tenvS tenvCT menv tenvM ∧
  type_env tenvCT tenvS env tenv0 ∧
  type_funs tenvM tenvC (bind_var_list 0 tenv (bind_tvar tvs tenv0)) funs tenv
  ⇒
  type_env2 tenvCT tenvS tvs (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs fn)) funs) tenv`,
metis_tac [type_recfun_env_help]);

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

val type_subst = Q.prove (
`(!tvs tenvCT tenvS v t. type_v tvs tenvCT tenvS v t ⇒
    ∀targs tvs'.
      (tvs = LENGTH targs) ∧
      tenvCT_ok tenvCT ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars (LENGTH targs) [] t
      ⇒
      type_v tvs' tenvCT tenvS v
             (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs' t))) ∧
 (!tvs tenvCT tenvS vs ts. type_vs tvs tenvCT tenvS vs ts ⇒
   ∀targs tvs'.
     (tvs = LENGTH targs) ∧
     tenvCT_ok tenvCT ∧
     EVERY (check_freevars tvs' []) targs ∧
     EVERY (check_freevars (LENGTH targs) []) ts
     ⇒
     type_vs tvs' tenvCT tenvS vs
             (MAP (deBruijn_subst 0 targs) (MAP (deBruijn_inc (LENGTH targs) tvs') ts))) ∧
 (!tenvCT tenvS env tenv. type_env tenvCT tenvS env tenv ⇒ 
    type_env tenvCT tenvS env tenv) ∧
 (!tenvCT tenvS envM tenvM. consistent_mod_env tenvCT tenvS envM tenvM ⇒ 
    consistent_mod_env tenvCT tenvS envM tenvM)`,
 ho_match_mp_tac type_v_strongind >>
 rw [] >>
 rw [Once type_v_cases] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 fs [check_freevars_def, Tfn_def, Tint_def, Tbool_def, Tref_def, Tunit_def] >>
 rw [deBruijn_inc_def, deBruijn_subst_def] >>
 rw [nil_deBruijn_inc, deBruijn_subst_check_freevars, type_subst_lem3,
     nil_deBruijn_subst]
 >- (rw [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [type_subst_lem1, EVERY_MEM])
 >- (`EVERY (check_freevars 0 tvs') ts` by metis_tac [tenvCT_ok_lookup, EVERY_MEM] >>
     `EVERY (check_freevars (LENGTH targs) tvs') ts`
           by (`LENGTH targs ≥ 0` by decide_tac >>
               metis_tac [EVERY_MEM, check_freevars_add]) >>
     `type_vs tvs'' tenvCT tenvS vs
              (MAP (deBruijn_subst 0 targs)
                 (MAP (deBruijn_inc (LENGTH targs) tvs'')
                    (MAP (type_subst (ZIP (tvs',ts'))) ts)))`
            by metis_tac [check_freevars_subst_list] >>
     pop_assum mp_tac >>
     rw [type_subst_deBruijn_subst_list, type_subst_deBruijn_inc_list] >>
     metis_tac [])
 >- metis_tac []
 >- (qexists_tac `menv` >>
 >- (qexists_tac `menv` >>
     qexists_tac `tenvC` >>
     qexists_tac `tenv` >>
     rw [] >>
     match_mp_tac type_e_subst_lem >>
     rw [tenv_ok_def, bind_tvar_def] >>
     metis_tac [type_v_freevars, tenvCT_ok_lookup])
 >- (qexists_tac `menv` >>
     qexists_tac `tenv` >>
     qexists_tac `MAP (λ(x,t). (x,deBruijn_subst 0 targs t)) tenv'` >>
     rw [] >|
     [match_mp_tac type_funs_subst_lem >>
          rw [] >-
          metis_tac [type_v_freevars] >-
          metis_tac [restrict_tenvC_ok] >>
          match_mp_tac tenv_ok_bind_var_list_funs >>
          metis_tac [tenv_ok_bind_var_list_funs, type_v_freevars, bind_tvar_rewrites],
      qpat_assum `type_funs w0 w x y z` (fn x => ALL_TAC) >>
          induct_on `tenv'` >>
          fs [lookup_def] >>
          rw [] >>
          PairCases_on `h` >>
          fs [] >>
          rw [] >>
          metis_tac []])
 >- (fs [bind_def, bind_tenv_def] >>
     metis_tac [type_v_rules])
 >- (fs [bind_def, bind_tenv_def] >>
     rw [Once type_v_cases, bind_def, bind_tenv_def]));

(* They value of a binding in the execution environment has the type given by
 * the type environment. *)
val type_lookup_lem2 = Q.prove (
`∀tenvC env tenv tvs tenvS v x t targs tparams idx.
  tenvC_ok tenvC ∧
  type_env tenvC tenvS env tenv ∧
  EVERY (check_freevars tvs []) targs ∧
  (lookup_tenv x 0 (bind_tvar tvs tenv) = SOME (LENGTH targs, t)) ∧
  (lookup x env = SOME v)
  ⇒
  type_v tvs tenvC tenvS v (deBruijn_subst 0 targs t)`,
induct_on `tenv` >>
rw [] >>
fs [lookup_tenv_def, bind_tvar_def] >>
qpat_assum `type_env tenvC tenvS env tenv_pat`
        (MP_TAC o SIMP_RULE (srw_ss ())
                         [Once type_env_cases]) >>
rw [] >>
fs [lookup_def, bind_def, emp_def, bind_tenv_def] >>
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

val consistent_mod_env_lookup = Q.prove (
`!tenvS tenvC menv tenvM tenv env n.
  consistent_mod_env tenvS tenvC menv tenvM ∧
  (lookup n menv = SOME env) ∧
  (lookup n tenvM = SOME tenv)
  ⇒
  type_env tenvC tenvS env (bind_var_list2 tenv Empty)`,
induct_on `tenvM` >>
rw [] >>
cases_on `menv` >>
fs [] >>
qpat_assum `consistent_mod_env x0 x1 x2 x3` (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once consistent_mod_cases]) >>
fs [] >>
rw [] >>
fs [] >>
every_case_tac >>
fs [] >>
metis_tac []);

val type_lookup_lem3 = Q.prove (
`∀tenvM tenvC menv env tenv tvs tenvS v x t targs tparams idx.
  tenvM_ok tenvM ∧
  tenvC_ok tenvC ∧
  type_env tenvC tenvS env tenv ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  EVERY (check_freevars tvs []) targs ∧
  (t_lookup_var_id x tenvM (bind_tvar tvs tenv) = SOME (LENGTH targs, t)) ∧
  (lookup_var_id x (menv,cenv,env) = SOME v)
  ⇒
  type_v tvs tenvC tenvS v (deBruijn_subst 0 targs t)`,
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

val type_raise_eqn = Q.prove (
`!tenvM tenvC tenv r t. 
  type_e tenvM tenvC tenv (Raise r) t = (type_e tenvM tenvC tenv r Texn ∧ check_freevars (num_tvs tenv) [] t)`,
rw [Once type_e_cases] >>
metis_tac []);

val type_env_eqn = Q.prove (
`!tenvC tenvS. 
  (type_env tenvC tenvS emp Empty = T) ∧
  (!n tvs t v env tenv. 
      type_env tenvC tenvS (bind n v env) (bind_tenv n tvs t tenv) = 
      (type_v tvs tenvC tenvS v t ∧ check_freevars tvs [] t ∧ type_env tenvC tenvS env tenv))`,
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

val tenvC_has_exns_def = Define `
tenvC_has_exns tenvC =
  ((lookup (Short "Bind") tenvC = SOME ([],[],TypeExn)) ∧
   (lookup (Short "Div") tenvC = SOME ([],[],TypeExn)) ∧
   (lookup (Short "Eq") tenvC = SOME ([],[],TypeExn)))`;

val type_v_exn = Q.prove (
`!tvs cenv senv.
  tenvC_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME (Short "Bind",TypeExn)) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME (Short "Div",TypeExn)) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME (Short "Eq",TypeExn)) []) Texn`,
 ONCE_REWRITE_TAC [type_v_cases] >>
 rw [tenvC_has_exns_def, Texn_def, tid_exn_to_tc_def] >>
 metis_tac [type_v_rules]);

val restrict_tenvC_imp = Q.prove (
`(lookup x envC = SOME a) ∧ (lookup x tenvC = SOME b)
 ⇒
 (lookup x (restrict_tenvC tenvC (MAP FST envC)) = SOME b)`,
 induct_on `tenvC` >>
 rw [restrict_tenvC_def] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 rw [] >>
 fs [restrict_tenvC_def] >>
 rw [] >>
 metis_tac [lookup_notin, NOT_SOME_NONE]);

val type_e_exn = Q.prove (
`!menv cenv env envC.
  envC_has_exns envC ∧
  tenvC_has_exns cenv ⇒
  type_e menv (restrict_tenvC cenv (MAP FST envC)) env (Con (SOME (Short "Bind")) []) Texn ∧
  type_e menv (restrict_tenvC cenv (MAP FST envC)) env (Con (SOME (Short "Div")) []) Texn ∧
  type_e menv (restrict_tenvC cenv (MAP FST envC)) env (Con (SOME (Short "Eq")) []) Texn`,
 NTAC 2 (ONCE_REWRITE_TAC [type_e_cases]) >>
 rw [envC_has_exns_def, tenvC_has_exns_def, Texn_def, tid_exn_to_tc_def] >>
 imp_res_tac restrict_tenvC_imp >>
 fs []);

(* If a step can be taken from a well-typed state, the resulting state has the
* same type *)
val exp_type_preservation = Q.prove (
`∀dec_tvs tenvC menv cenv st env e c t menv' cenv' st' env' e' c' tenvS.
  tenvC_ok tenvC ∧
  tenvC_has_exns tenvC ∧
  type_state dec_tvs tenvC tenvS ((menv,cenv,env), st, e, c) t ∧
  (e_step ((menv,cenv,env), st, e, c) = Estep ((menv',cenv',env'), st', e', c'))
  ⇒
  ∃tenvS'. type_state dec_tvs tenvC tenvS' ((menv',cenv',env'), st', e', c') t ∧
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
             imp_res_tac lookup_restrict_tenvC >>
             metis_tac [check_freevars_def, lookup_restrict_tenvC])
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
         metis_tac [type_lookup_lem3])
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
              qexists_tac `t1'` >>
              qexists_tac `tenv` >>
              qexists_tac `tvs` >>
              rw [] >>
              qexists_tac `tenvM` >>
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
              qexists_tac `t1'` >>
              qexists_tac `tenv` >>
              rw [] >>
              qexists_tac `0` >>
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
              qexists_tac `tenvM` >>
              qexists_tac `Tapp [] TC_int` >>
              rw [check_freevars_def] >>
              metis_tac [type_e_exn],
          fs [Tint_def, type_v_cases_eqn] >>
              rw [] >>
              rw [Once type_e_cases] >>
              qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `tenvM` >>
              qexists_tac `Tapp [] TC_int` >>
              rw [check_freevars_def] >>
              metis_tac [type_e_exn],
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
              metis_tac [type_e_exn, check_freevars_def, EVERY_DEF],
          qpat_assum `type_v a tenvC senv (Closure l s' e) t1'`
                    (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
              fs [] >>
              rw [] >>
              rw [Once type_env_cases] >>
              fs [Tfn_def, bind_tvar_def] >>
              metis_tac [],
          qpat_assum `type_v a tenvC senv (Recclosure l l0 s') t1'`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
              fs [] >>
              rw [] >>
              imp_res_tac type_recfun_lookup >>
              rw [] >>
              qexists_tac `tenvS` >>
              rw [] >>
              qexists_tac `menv` >>
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
         cases_on `lookup cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac lookup_restrict_tenvC >>
         imp_res_tac consistent_con_env_thm >>
         rw [Once type_v_cases_eqn] >>
         imp_res_tac type_es_length >>
         fs [] >>
         `ts2 = []` by
                 (cases_on `ts2` >>
                  fs []) >>
         fs [] >>
         rw [] >>
         rw [type_vs_end_lem] >>
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
         rw [type_vs_end_lem] >>
         fs [is_ccon_def] >>
         metis_tac [ctxt_inv_not_poly, rich_listTheory.MAP_REVERSE, type_vs_end_lem])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac lookup_restrict_tenvC >>
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
         qexists_tac `t''''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
         rw [] >>
         cases_on `ts2` >>
         fs [] >>
         rw [] >>
         qexists_tac `ts1++[t''']` >>
         rw [] >>
         metis_tac [type_vs_end_lem])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup cn cenv'` >>
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
         qexists_tac `t'''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
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
         metis_tac [type_vs_end_lem, arithmeticTheory.ADD_0])
     >- (fs [all_env_to_cenv_def, build_conv_def] >>
         cases_on `lookup cn cenv'` >>
         fs [] >>
         PairCases_on `x'` >>
         fs [] >>
         rw [] >>
         imp_res_tac lookup_restrict_tenvC >>
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
         qexists_tac `t''''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
         qexists_tac `tenv` >>
         qexists_tac `Tapp ts' (tid_exn_to_tc tn)` >>
         rw [] >>
         cases_on `ts2` >>
         fs [] >>
         rw [] >>
         qexists_tac `ts1++[t''']` >>
         rw [] >>
         metis_tac [type_vs_end_lem])
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
         qexists_tac `t'''` >>
         qexists_tac `tenv` >>
         qexists_tac `tvs` >>
         rw [] >>
         fs [is_ccon_def] >>
         qexists_tac `tenvM` >>
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
         metis_tac [type_vs_end_lem, arithmeticTheory.ADD_0])
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
                   [metis_tac [type_ctxts_weakening, weakC_refl, weakM_refl, weakS_bind],
                    fs [type_s_def, lookup_def, bind_def, store_lookup_def] >>
                        rw [] >-
                        decide_tac >|
                        [rw [rich_listTheory.EL_LENGTH_APPEND] >>
                             metis_tac [bind_def, type_v_weakening, weakS_bind, weakC_refl, weakM_refl],
                         `l < LENGTH st` by decide_tac >>
                             rw [rich_listTheory.EL_APPEND1] >>
                             metis_tac [type_v_weakening, weakS_bind, weakC_refl, weakM_refl, bind_def]],
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
  ∀tenvC tenvS st env e c st' env' e' c' t dec_tvs.
    (state1 = (env,st,e,c)) ∧
    (state2 = (env',st',e',c')) ∧
    tenvC_ok tenvC ∧
    tenvC_has_exns tenvC ∧
    type_state dec_tvs tenvC tenvS state1 t
    ⇒
    ?tenvS'. type_state dec_tvs tenvC tenvS' state2 t ∧
             store_type_extension tenvS tenvS'`,
ho_match_mp_tac RTC_INDUCT >>
rw [e_step_reln_def] >-
(rw [store_type_extension_def] >>
     qexists_tac `tenvS` >>
     rw [merge_def]) >>
PairCases_on `state1'` >>
PairCases_on `env` >>
`?tenvS'. type_state dec_tvs tenvC tenvS' ((state1'0,state1'1,state1'2),state1'3,state1'4,state1'5) t ∧
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
`!tenvM tenvC tenvS tenv st e t menv cenv env tvs.
  tenvM_ok tenvM ∧
  tenvC_ok tenvC ∧
  envC_has_exns cenv ∧
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv (restrict_tenvC tenvC (MAP FST cenv)) ∧
  type_env tenvC tenvS env tenv ∧
  type_s tenvC tenvS st ∧
  (tvs ≠ 0 ⇒ is_value e) ∧
  type_e tenvM (restrict_tenvC tenvC (MAP FST cenv)) (bind_tvar tvs tenv) e t
  ⇒
  e_diverges (menv,cenv,env) st e ∨
  (?st' r. (r ≠ Rerr Rtype_error) ∧ 
          small_eval (menv,cenv,env) st e [] (st',r) ∧
          (?tenvS'.
            type_s tenvC tenvS' st' ∧
            store_type_extension tenvS tenvS' ∧
            (!v. (r = Rval v) ⇒ type_v tvs tenvC tenvS' v t)))`,
rw [e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
`type_state tvs tenvC tenvS ((menv,cenv,env),st,Exp e,[]) t`
         by (rw [type_state_cases] >>
             qexists_tac `tenvM` >>
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
`?tenvS'. type_state tvs tenvC tenvS' (env',s',e',c') t ∧ store_type_extension tenvS tenvS'`
        by metis_tac [exp_type_soundness_help] >>
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

val consistent_cenv_no_dups = Q.prove (
`!l cenv tenvC.
  consistent_con_env cenv tenvC ∧
  check_dup_ctors mn tenvC l
  ⇒
  check_dup_ctors mn cenv l`,
induct_on `l` >>
rw [check_dup_ctors_def] >>
fs [RES_FORALL] >>
rw [] >|
[PairCases_on `h` >>
     fs [] >>
     rw [] >>
     `(λ(tvs,tn,condefs).
        ∀x. MEM x condefs ⇒ (λ(n,ts). lookup (mk_id mn n) tenvC = NONE) x) (h0,h1,h2)`
              by metis_tac [] >>
     fs [] >>
     rw [] >>
     PairCases_on  `x` >>
     fs [] >>
     RES_TAC >>
     fs [] >>
     metis_tac [consistent_con_env_thm],
 `(λ(tvs,tn,condefs).
    ∀x. MEM x condefs ⇒ (λ(n,ts). lookup (mk_id mn n) tenvC = NONE) x) x`
              by metis_tac [] >>
     PairCases_on `x` >>
     fs [] >>
     rw [] >>
     fs [] >>
     RES_TAC >>
     fs [] >>
     PairCases_on `x` >>
     fs [] >>
     metis_tac [consistent_con_env_thm]]);

val consistent_con_preservation = Q.prove (
`!mn tenvC tds cenv.
  check_ctor_tenv mn tenvC tds ∧
  consistent_con_env cenv tenvC
  ⇒
  consistent_con_env (merge (build_tdefs mn tds) cenv) (merge (build_ctor_tenv mn tds) tenvC)`,
metis_tac [merge_def,extend_consistent_con]);

val pmatch_append = Q.prove (
`(!(cenv : envC) (st : v store) p v env env' env''.
    (pmatch cenv st p v env = Match env') ⇒
    (pmatch cenv st p v (env++env'') = Match (env'++env''))) ∧
 (!(cenv : envC) (st : v store) ps v env env' env''.
    (pmatch_list cenv st ps v env = Match env') ⇒
    (pmatch_list cenv st ps v (env++env'') = Match (env'++env'')))`,
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, bind_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val tenvC_ok_pres = Q.prove (
`!mn tenvM tenvC tenv d tenvC' tenv'.
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  tenvC_ok tenvC 
  ⇒
  tenvC_ok (tenvC' ++ tenvC)`,
rw [] >>
imp_res_tac type_d_tenvC_ok >>
rw [GSYM merge_def] >>
rw [tenvC_ok_merge]);

val lookup_restrict_tenvC_notin = Q.prove (
`!cn cenv tenvC.
  (lookup cn (restrict_tenvC tenvC cns) = NONE) ⇒ cn ∉ set cns ∨ (lookup cn tenvC = NONE)`,
 induct_on `tenvC` >>
 rw [] >>
 PairCases_on `h` >>
 fs [restrict_tenvC_def] >>
 every_case_tac >>
 fs []);

val consistent_con_env_domhelp = Q.prove (
`!cenv tenvC.
  (∀cn tvs ts tn. (lookup cn tenvC = SOME (tvs,ts,tn) ⇒ lookup cn cenv = SOME (LENGTH ts,tn))) ⇒
  set (MAP FST tenvC) ⊆ set (MAP FST cenv)`,
 rw [MEM_MAP, SUBSET_DEF, EXTENSION] >>
 PairCases_on `y` >>
 fs [] >>
 `?a b c. lookup y0 tenvC = SOME (a,b,c)`
          by (CCONTR_TAC >>
              `lookup y0 tenvC = NONE` by metis_tac [pair_CASES, option_nchotomy] >>
              fs [lookup_notin, MEM_MAP] >>
              pop_assum (mp_tac o Q.SPEC `(y0,y1,y2,y3)`) >>
              rw []) >>
 res_tac >>
 rw [] >>
 imp_res_tac lookup_in >>
 imp_res_tac lookup_in2 >>
 fs [MEM_MAP] >>
 rw [] >>
 metis_tac [pair_CASES, PAIR_EQ, FST, SND])

val consistent_con_env_helperlem = Q.prove (
`!ns tenvC.
  set (MAP FST tenvC) ⊆ set ns ⇒ 
  restrict_tenvC tenvC ns = tenvC`,
 induct_on `tenvC` >>
 rw [restrict_tenvC_def] >>
 PairCases_on `h` >>
 rw [restrict_tenvC_def] >>
 fs []);

val consistent_con_env_lem = Q.prove (
`!cenv tenvC.
  consistent_con_env cenv tenvC ⇒ 
  restrict_tenvC tenvC (MAP FST cenv) = tenvC`,
 metis_tac [consistent_con_env_def, consistent_con_env_domhelp, consistent_con_env_helperlem, SUBSET_REFL]);

val consistent_has_exns = Q.prove (
`!tenvC cenv.
  consistent_con_env cenv tenvC ∧ tenvC_has_exns tenvC ⇒ envC_has_exns cenv`,
 rw [consistent_con_env_def, tenvC_has_exns_def, envC_has_exns_def] >>
 res_tac >>
 fs []);

val dec_type_soundness = Q.store_thm ("dec_type_soundness",
`!mn tenvM tenvC tenv d tenvC' tenv' tenvS menv cenv env st.
  type_d mn tenvM tenvC tenv d tenvC' tenv' ∧
  tenvM_ok tenvM ∧
  tenvC_ok tenvC ∧
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvC tenvS env tenv ∧
  type_s tenvC tenvS st
  ⇒
  dec_diverges (menv,cenv,env) st d ∨
  ?st' r tenvS'. 
     (r ≠ Rerr Rtype_error) ∧ 
     evaluate_dec mn (menv,cenv,env) st d (st', r) ∧
     store_type_extension tenvS tenvS' ∧
     type_s tenvC tenvS' st' ∧
     disjoint_env tenvC tenvC' ∧
     (!cenv' env'. 
         (r = Rval (cenv',env')) ⇒
         consistent_con_env (cenv' ++ cenv) (tenvC' ++ tenvC) ∧
         type_env (tenvC' ++ tenvC) tenvS' (env' ++ env) (bind_var_list2 tenv' tenv) ∧
         type_env (tenvC' ++ tenvC) tenvS' env' (bind_var_list2 tenv' Empty))`,
 rw [METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 fs [type_d_cases] >>
 rw [] >>
 fs [dec_diverges_def, merge_def, emp_def, evaluate_dec_cases] >>
 fs [] >>
 imp_res_tac consistent_has_exns
 >- (`∃st2 r tenvS'. r ≠ Rerr Rtype_error ∧ small_eval (menv,cenv,env) st e [] (st2,r) ∧
                type_s tenvC tenvS' st2 ∧ 
                store_type_extension tenvS tenvS' ∧
                (!v. (r = Rval v) ==> type_v tvs tenvC tenvS' v t)`
                         by metis_tac [exp_type_soundness, consistent_con_env_lem] >>
     cases_on `r` >>
     fs [] >|
     [`(pmatch cenv st2 p a [] = No_match) ∨
       (?new_env. pmatch cenv st2 p a [] = Match new_env)`
                 by (metis_tac [pmatch_type_progress, consistent_con_env_lem]) >|
          [qexists_tac `st2` >>
               qexists_tac `Rerr (Rraise (Conv (SOME (Short "Bind", TypeExn)) []))` >>
               rw [] >>
               rw [] >>
               fs [merge_def, disjoint_env_def] >>
               metis_tac [small_big_exp_equiv, all_env_to_cenv_def],
           qexists_tac `st2` >>
               qexists_tac `Rval ([],new_env)` >>
               rw [] >>
               `pmatch cenv st2 p a ([]++env) = Match (new_env++env)`
                        by metis_tac [pmatch_append] >>
               `type_env tenvC tenvS [] Empty` by metis_tac [type_v_rules, emp_def] >>
               `type_p tvs (restrict_tenvC tenvC (MAP FST cenv)) p t tenv''`
                             by metis_tac [consistent_con_env_lem] >>
               imp_res_tac pmatch_type_preservation >>
               `type_env tenvC tenvS' new_env (bind_var_list tvs tenv'' Empty) ∧
                type_env tenvC tenvS' (new_env ++ env) (bind_var_list tvs tenv'' tenv)` 
                            by metis_tac [merge_def, APPEND, APPEND_NIL,type_v_weakening, weakM_refl, weakC_refl,
                                          store_type_extension_weakS, pmatch_type_preservation, 
                                          consistent_con_env_lem] >>
               fs [merge_def, disjoint_env_def] >>
               metis_tac [bvl2_to_bvl, small_big_exp_equiv, all_env_to_cenv_def]],
      qexists_tac `st2` >>
          qexists_tac `Rerr e'` >>
          rw [] >>
          qexists_tac `tenvS'` >>
          rw [store_type_extension_def, merge_def, disjoint_env_def] >>
          metis_tac [small_big_exp_equiv]])
 >- (`∃st2 r tenvS'. r ≠ Rerr Rtype_error ∧ small_eval (menv,cenv,env) st e [] (st2,r) ∧
                type_s tenvC tenvS' st2 ∧ 
                store_type_extension tenvS tenvS' ∧
                (!v. (r = Rval v) ==> type_v (0:num) tenvC tenvS' v t)`
                         by metis_tac [exp_type_soundness, bind_tvar_def, consistent_con_env_lem] >>
     cases_on `r` >>
     fs [] >|
     [`(pmatch cenv st2 p a [] = No_match) ∨
       (?new_env. pmatch cenv st2 p a [] = Match new_env)`
                 by (metis_tac [pmatch_type_progress, consistent_con_env_lem]) >|
          [qexists_tac `st2` >>
               qexists_tac `Rerr (Rraise (Conv (SOME (Short "Bind", TypeExn)) []))` >>
               rw [] >>
               fs [disjoint_env_def] >>
               metis_tac [small_big_exp_equiv, all_env_to_cenv_def],
           qexists_tac `st2` >>
               qexists_tac `Rval ([],new_env)` >>
               rw [] >>
               `pmatch cenv st2 p a ([]++env) = Match (new_env++env)`
                        by metis_tac [pmatch_append] >>
               `type_p 0 (restrict_tenvC tenvC (MAP FST cenv)) p t tenv''`
                             by metis_tac [consistent_con_env_lem] >>
               imp_res_tac pmatch_type_preservation >>
               `type_env tenvC tenvS [] Empty` by metis_tac [type_v_rules, emp_def] >>
               `type_env tenvC tenvS' new_env (bind_var_list 0 tenv'' Empty) ∧
                type_env tenvC tenvS' (new_env ++ env) (bind_var_list 0 tenv'' tenv)`
                        by metis_tac [merge_def, APPEND, APPEND_NIL, type_v_weakening, weakM_refl, weakC_refl,
                                      store_type_extension_weakS, pmatch_type_preservation, 
                                      consistent_con_env_lem] >>
               fs [merge_def, disjoint_env_def] >>
               metis_tac [bvl2_to_bvl, small_big_exp_equiv, all_env_to_cenv_def]],
      qexists_tac `st2` >>
          qexists_tac `Rerr e'` >>
          rw [] >>
          qexists_tac `tenvS'` >>
          rw [store_type_extension_def, merge_def, disjoint_env_def] >>
          metis_tac [small_big_exp_equiv]])
 >- (`type_env2 tenvC tenvS tvs (MAP (\(fn,n,e). (fn, Recclosure (menv,cenv,env) funs fn)) funs) tenv''`
                  by metis_tac [type_recfun_env, consistent_con_env_lem] >>
     imp_res_tac type_env_merge_lem1 >>
     qexists_tac `st` >>
     qexists_tac `Rval ([],build_rec_env funs (menv,cenv,env) [])` >>
     rw [] >>
     qexists_tac `tenvS` >>
     rw [] >-
     metis_tac [type_funs_distinct] >>
     fs [build_rec_env_merge, merge_def, emp_def] >>
     rw [store_type_extension_def, merge_def, disjoint_env_def] >>
     metis_tac [bvl2_to_bvl, type_env2_to_type_env])
 >- (qexists_tac `st` >>
     qexists_tac `Rval (build_tdefs mn tdecs,[])` >>
     rw [] >>
     qexists_tac `tenvS` >>
     rw [] >>
     imp_res_tac consistent_con_preservation >>
     `type_env (merge (build_ctor_tenv mn tdecs) tenvC) tenvS env tenv`
             by metis_tac [check_ctor_tenv_dups, type_v_weakening, weakM_refl, 
                           weakS_refl, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM] >>
     `type_s (build_ctor_tenv mn tdecs ++ tenvC) tenvS st`
             by (fs [type_s_def] >>
                 rw [] >>
                 metis_tac [check_ctor_tenv_dups, type_v_weakening, weakM_refl, 
                            weakS_refl, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM, merge_def]) >>
     fs [merge_def, store_type_extension_def, bind_var_list2_def, all_env_to_cenv_def] >>
     metis_tac [check_ctor_tenv_dups, consistent_cenv_no_dups,
                check_ctor_tenv_def, bind_var_list2_def, type_v_rules, emp_def])
 >- (qexists_tac `st` >>
     qexists_tac `Rval (bind (mk_id mn cn) (LENGTH ts,TypeExn) [],[])` >>
     rw []  >>
     qexists_tac `tenvS` >>
     rw []
     >- metis_tac [consistent_con_env_thm, all_env_to_cenv_def]
     >- rw [store_type_extension_def, merge_def]
     >- (rw [bind_def, disjoint_env_def, DISJOINT_DEF, EXTENSION] >>
         metis_tac [lookup_notin])
     >- (rw [consistent_con_env_def, bind_def] >>
         every_case_tac >>
         fs [] >>
         metis_tac [consistent_con_env_thm])
     >- (rw [bind_def, bind_var_list2_def] >>
         `weakC ((mk_id mn cn,[],ts,TypeExn)::tenvC) tenvC ` 
                      by (rw [weakC_def] >>
                          every_case_tac) >>
         metis_tac [type_v_weakening, weakS_refl, weakM_refl])
     >- (rw [bind_def, bind_var_list2_def] >>
         metis_tac [emp_def, type_env_eqn])));

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

val type_env_merge_bvl2 = Q.prove (
`!tenvM tenvC tenvS env1 tenv1 env2 tenv2.
  type_env tenvC tenvS env2 (bind_var_list2 tenv2 Empty) ∧
  type_env tenvC tenvS env1 (bind_var_list2 tenv1 Empty) ⇒
  type_env tenvC tenvS (merge env1 env2) (bind_var_list2 (tenv1 ++ tenv2) Empty)`,
induct_on `env1` >>
cases_on `tenv1` >>
rw [merge_def] >>
rw [Once type_v_cases] >>
rw [emp_def, bind_def] >>
PairCases_on `h` >>
fs [bind_var_list2_def, bind_tenv_def] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
fs [bind_def, emp_def, bind_tenv_def] >>
metis_tac [merge_def]);

val still_has_exns = Q.prove (
`!tenvC1 tenvC2.
 (disjoint_env tenvC1 tenvC2 ∨ disjoint_env tenvC2 tenvC1) ∧
 tenvC_has_exns tenvC1
 ⇒
 tenvC_has_exns (tenvC2 ++ tenvC1)`,
metis_tac [lookup_disjoint, tenvC_has_exns_def, merge_def, disjoint_env_def, DISJOINT_SYM]);

val decs_type_soundness = Q.store_thm ("decs_type_soundness",
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  ∀tenvS menv cenv env st.
  tenvM_ok tenvM ∧
  tenvC_ok tenvC ∧
  tenvC_has_exns tenvC ∧
  consistent_mod_env tenvS tenvC menv tenvM ∧
  consistent_con_env cenv tenvC ∧
  type_env tenvC tenvS env tenv ∧
  type_s tenvC tenvS st
  ⇒
  decs_diverges mn (menv,cenv,env) st ds ∨
  ?st' r cenv' tenvS'. 
     (r ≠ Rerr Rtype_error) ∧ 
     evaluate_decs mn (menv,cenv,env) st ds (st', cenv', r) ∧
     store_type_extension tenvS tenvS' ∧
     disjoint_env tenvC tenvC' ∧
     (!err.
         (r = Rerr err) ⇒
         (?tenvC1 tenvC2. 
           (tenvC' = tenvC1++tenvC2) ∧
           type_s (tenvC2 ++ tenvC) tenvS' st' ∧
           consistent_con_env (cenv' ++ cenv) (tenvC2 ++ tenvC))) ∧
     (!env'. 
         (r = Rval env') ⇒
         consistent_con_env (cenv' ++ cenv) (tenvC' ++ tenvC) ∧
         type_s (tenvC' ++ tenvC) tenvS' st' ∧
         type_env (tenvC' ++ tenvC) tenvS' env' (bind_var_list2 tenv' Empty) ∧
         type_env (tenvC' ++ tenvC) tenvS' (env'++env) (bind_var_list2 tenv' tenv))`,
 ho_match_mp_tac type_ds_strongind >>
 rw [METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``] >>
 rw [Once evaluate_decs_cases, bind_var_list2_def, emp_def] >>
 rw [] >>
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once decs_diverges_cases]) >>
 fs [merge_def, emp_def]
 >- (qexists_tac `tenvS` >>
     rw [store_type_extension_def, disjoint_env_def] >|
     [qexists_tac `[]` >>
          rw [merge_def],
      metis_tac [type_v_rules, emp_def]])
 >- (`?r st' tenvS'. 
        (r ≠ Rerr Rtype_error) ∧ 
        store_type_extension tenvS tenvS' ∧
        evaluate_dec mn (menv,cenv,env) st d (st',r) ∧
        disjoint_env tenvC cenv' ∧
        type_s tenvC tenvS' st' ∧
        ∀cenv'' env''.
          (r = Rval (cenv'',env'')) ⇒
          consistent_con_env (cenv'' ++ cenv) (cenv' ++ tenvC) ∧
          type_env (cenv' ++ tenvC) tenvS' env'' (bind_var_list2 tenv' Empty) ∧
          type_env (cenv' ++ tenvC) tenvS' (env''++env) (bind_var_list2 tenv' tenv)`
                     by metis_tac [dec_type_soundness] >>
     imp_res_tac tenvC_ok_pres >>
     `consistent_mod_env tenvS' (cenv' ++ tenvC) menv tenvM` 
                 by metis_tac [type_v_weakening, merge_def,
                               store_type_extension_weakS, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM] >>
     `type_s (cenv' ++ tenvC) tenvS' st'` 
                     by metis_tac [merge_def, tenvC_ok_merge, disjoint_env_weakC, weakM_refl,
                                   type_s_weakening] >>
     `tenvC_has_exns (cenv' ++ tenvC)` by metis_tac [still_has_exns] >>
     `(?cenv'' env''. r = Rval (cenv'',env'')) ∨ (?err. r = Rerr err)` 
                   by (cases_on `r` >> metis_tac [pair_CASES]) >>
     fs [] >>
     rw [] >|
     [rw [] >>
          `¬decs_diverges mn (menv, cenv'' ++ cenv, env'' ++ env) st' ds` by metis_tac [] >>
          qpat_assum `∀tenvS' menv' cenv'' env' st'. P tenvS' menv' cenv'' env' st'`
                     (MP_TAC o Q.SPECL [`tenvS'`, `menv`, `cenv''++cenv`, `env''++env`, `st'`]) >>
          rw [] >>
          MAP_EVERY qexists_tac [`st''`, `combine_dec_result env'' r`, `merge cenv''' cenv''`, `tenvS''`] >>
          rw [] >|
          [cases_on `r` >>
               rw [combine_dec_result_def],
           metis_tac [merge_def, result_case_def],
           metis_tac [store_type_extension_trans],
           fs [disjoint_env_def] >>
               metis_tac [DISJOINT_SYM],
           cases_on `r` >> 
               fs [combine_dec_result_def] >> 
               rw [] >>
               metis_tac [APPEND_ASSOC, merge_def],
           cases_on `r` >> 
               fs [combine_dec_result_def] >> 
               rw [] >>
               metis_tac [APPEND_ASSOC, merge_def],
           cases_on `r` >> 
               fs [combine_dec_result_def] >> 
               rw [],
           cases_on `r` >> 
               fs [combine_dec_result_def] >> 
               rw [] >>
               metis_tac [type_env_merge_bvl2, type_v_weakening,store_type_extension_weakS, disjoint_env_weakC, 
                          disjoint_env_def, DISJOINT_SYM, disjoint_env_def, APPEND_ASSOC, merge_def, weakM_refl],
           cases_on `r` >> 
               fs [combine_dec_result_def] >> 
               rw [] >>
               metis_tac [merge_def, bvl2_append]],
      MAP_EVERY qexists_tac [`st'`, `Rerr err`, `[]`, `tenvS'`] >>
          rw [] >>
          imp_res_tac type_d_tenvC_ok >>
          imp_res_tac type_ds_tenvC_ok >|
          [fs [disjoint_env_def] >>
               metis_tac [DISJOINT_SYM],
           MAP_EVERY qexists_tac [`tenvC'++cenv'`, `[]`] >>
               rw []]]));

val tenvC_ok_pres2 = Q.prove (
`!mn tenvM tenvC tenv d tenvC' tenv'.
  type_ds mn tenvM tenvC tenv d tenvC' tenv' ⇒
  tenvC_ok tenvC 
  ⇒
  tenvC_ok (tenvC' ++ tenvC)`,
ho_match_mp_tac type_ds_ind >>
rw [emp_def, merge_def] >>
metis_tac [tenvC_ok_pres]);

val consistent_mod_env_dom = Q.prove (
`!tenvS tenvC menv tenvM.
  consistent_mod_env tenvS tenvC menv tenvM ⇒
  (MAP FST menv = MAP FST tenvM)`,
 induct_on `tenvM` >>
 rw [] >>
 cases_on `menv` >>
 fs [] >>
 pop_assum (assume_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 rw [] >>
 fs [] >>
 res_tac);

val tenvM_ok_pres = Q.prove (
`∀tenvM mn tenv. 
 tenvM_ok tenvM ∧
 tenv_ok (bind_var_list2 tenv Empty)
 ⇒
 tenvM_ok (bind mn tenv tenvM)`,
induct_on `tenvM` >>
rw [tenvM_ok_def, bind_def]);

(* For using the type soundess theorem, we have to know there are good
 * constructor and module type environments that don't have bits hidden by a
 * signature. *)
val type_sound_invariants_def = Define `
type_sound_invariants (tenvM,tenvC,tenv,envM,envC,envE,store) ⇔
  ?tenvS tenvM_no_sig tenvC_no_sig. 
    tenvM_ok tenvM_no_sig ∧ 
    tenvC_ok tenvC_no_sig ∧
    tenvC_ok tenvC ∧
    tenvC_has_exns tenvC_no_sig ∧
    tenvM_ok tenvM ∧
    weakC_mods tenvC_no_sig tenvC ⊆ set (MAP SOME (MAP FST tenvM_no_sig)) ∧
    (MAP FST tenvM_no_sig = MAP FST tenvM) ∧
    consistent_mod_env tenvS tenvC_no_sig envM tenvM_no_sig ∧
    consistent_con_env envC tenvC_no_sig ∧
    type_env tenvC_no_sig tenvS envE tenv ∧
    type_s tenvC_no_sig tenvS store ∧
    weakM tenvM_no_sig tenvM ∧
    weakC tenvC_no_sig tenvC`;

val update_type_sound_inv_def = Define `
update_type_sound_inv top (tenvM:tenvM,tenvC:tenvC,tenv:tenvE,envM:envM,envC:envC,envE:envE,store) tenvM' tenvC' tenv' store' envC' r =
  case r of
     | Rval (envM',envE') => 
         (tenvM'++tenvM,tenvC'++tenvC,bind_var_list2 tenv' tenv,
          envM'++envM,envC'++envC,envE'++envE,store')
     | Rerr _ => (strip_mod_env tenvM'++tenvM,tenvC,tenv,strip_mod_env tenvM'++envM,top_to_cenv top++envC,envE,store')`;

val weakM_bind' = Q.prove (
`!mn tenv' tenvM' tenv tenvM.
  weakE tenv' tenv ∧
  weakM tenvM' tenvM
  ⇒
  weakM (bind mn tenv' tenvM') (bind mn tenv tenvM)`,
rw [weakM_def, bind_def, lookup_def] >>
full_case_tac >>
fs []);

val weakC_merge' = Q.prove (
`!tenvC1' tenvC2' tenvC1 tenvC2.
  tenvC_ok (tenvC1'++tenvC2') ∧
  weakC tenvC1' tenvC1 ∧
  weakC tenvC2' tenvC2
  ⇒
  weakC (tenvC1'++tenvC2') (tenvC1++tenvC2)`,
induct_on `tenvC1` >>
rw [tenvC_ok_def, weakC_def, lookup_def] >|
[pop_assum (mp_tac o Q.SPEC `cn`) >>
     cases_on `lookup cn tenvC2` >>
     rw [] >>
     PairCases_on `x` >>
     rw [lookup_append] >>
     cases_on `lookup cn tenvC2'` >>
     rw [] >>
     cases_on `lookup cn tenvC1'` >>
     rw [] >>
     fs [] >>
     PairCases_on `x` >>
     PairCases_on `x'` >>
     rw [] >>
     fs [] >>
     imp_res_tac lookup_in2 >>
     fs [ALL_DISTINCT_APPEND] >>
     metis_tac [],
 pop_assum (mp_tac o Q.SPEC `cn`) >>
     pop_assum (mp_tac o Q.SPEC `cn`) >>
     PairCases_on `h` >>
     rw [lookup_def] >>
     fs [lookup_def, lookup_append] >|
     [cases_on `lookup cn tenvC1'` >>
          fs [],
      cases_on `lookup cn tenvC1'` >>
          cases_on `lookup cn tenvC2'` >>
          cases_on `lookup cn tenvC1` >>
          cases_on `lookup cn tenvC2` >>
          fs [] >>
          PairCases_on `x` >>
          PairCases_on `x'` >>
          fs [] >>
          PairCases_on `x''` >>
          fs [] >>
          imp_res_tac lookup_in2 >>
          fs [ALL_DISTINCT_APPEND] >>
          metis_tac []]]);

val weakC_trans = Q.prove (
`!tenvC1 tenvC2 tenvC3.
  weakC tenvC1 tenvC2 ∧
  weakC tenvC2 tenvC3
  ⇒
  weakC tenvC1 tenvC3`,
rw [weakC_def] >>
pop_assum (mp_tac o Q.SPEC `cn`) >>
pop_assum (mp_tac o Q.SPEC `cn`) >>
cases_on `lookup cn tenvC3` >>
rw [] >>
PairCases_on `x` >>
rw [] >>
cases_on `lookup cn tenvC1` >>
rw [] >>
fs [] >>
cases_on `lookup cn tenvC2` >>
fs [] >>
PairCases_on `x` >>
fs [] >>
PairCases_on `x'` >>
fs []);

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

val consistent_con_env_decs_to_cenv = Q.prove (
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !tenvC'' envC.
    consistent_con_env envC tenvC''
    ⇒
    consistent_con_env (decs_to_cenv mn ds ++ envC) (tenvC' ++ tenvC'')`,
 ho_match_mp_tac type_ds_ind >>
 rw [decs_to_cenv_def, emp_def] >>
 cases_on `d` >>
 fs [type_d_cases, dec_to_cenv_def, emp_def, merge_def] >>
 rw []
 >- metis_tac [extend_consistent_con, APPEND_ASSOC]
 >- (rw [bind_def] >>
     `consistent_con_env ([(mk_id mn s,LENGTH l,TypeExn)] ++ envC) ([(mk_id mn s,[],l,TypeExn)] ++ tenvC'')`
              by (rw [consistent_con_env_def] >>
                  rw [] >>
                  fs [consistent_con_env_def]) >>
     metis_tac [APPEND_ASSOC]));

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
 >- (`weak_other_mods NONE tenvC_no_sig tenvC` by metis_tac [weakC_not_NONE] >>
     `type_d NONE tenvM_no_sig tenvC_no_sig tenv d tenvC' tenv'` by metis_tac [type_d_weakening] >>
     `?r store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_dec NONE (envM, envC, envE) store1 d (store2,r) ∧
        store_type_extension tenvS tenvS' ∧
        type_s tenvC_no_sig tenvS' store2 ∧
        disjoint_env tenvC_no_sig tenvC' ∧
        ∀cenv' env'.
         (r = Rval (cenv',env')) ⇒
         consistent_con_env (cenv' ++ envC) (tenvC' ++ tenvC_no_sig) ∧
         type_env (tenvC' ++ tenvC_no_sig) tenvS'
           (env' ++ envE) (bind_var_list2 tenv' tenv) ∧
         type_env (tenvC' ++ tenvC_no_sig) tenvS' env'
           (bind_var_list2 tenv' Empty)`
                by metis_tac [dec_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?cenv' env'. r = Rval (cenv',env'))` 
                by (cases_on `r` >> metis_tac [pair_CASES]) >>
     rw [] >|
     [MAP_EVERY qexists_tac [`Rerr err`, `emp`, `store2`] >>
          rw [type_sound_invariants_def, update_type_sound_inv_def] >>
          MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `tenvC_no_sig`] >>
          rw [replTheory.strip_mod_env_def, emp_def] >|
          [metis_tac [type_v_weakening, store_type_extension_weakS,
                      weakC_refl],
           rw [top_to_cenv_def] >>
               cases_on `d` >>
               fs [evaluate_dec_cases, dec_to_cenv_def],
           metis_tac [type_v_weakening, store_type_extension_weakS, weakC_refl, weakM_refl]],
      MAP_EVERY qexists_tac [`Rval (emp,env')`,`cenv'`, `store2`] >>
          imp_res_tac type_d_mod >>
          imp_res_tac type_d_tenvC_ok >>
          rw [type_sound_invariants_def, update_type_sound_inv_def] >>
          `weakC (tenvC'++tenvC_no_sig) tenvC_no_sig`
                     by metis_tac [merge_def, disjoint_env_weakC] >>
          MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `tenvC' ++ tenvC_no_sig`] >>
          rw [emp_def] >|
          [rw [GSYM merge_def, tenvC_ok_merge],
           rw [GSYM merge_def, tenvC_ok_merge],
           metis_tac [still_has_exns],
           fs [weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               full_case_tac >>
               fs [] >>
               metis_tac [],
           metis_tac [type_v_weakening, store_type_extension_weakS,
                      weakC_refl],
           metis_tac [type_s_weakening, weakM_refl],
           metis_tac [weakC_merge, merge_def]]])
 >- metis_tac [consistent_mod_env_dom, all_env_to_menv_def]
 >- (`weak_other_mods (SOME mn) tenvC_no_sig tenvC` by metis_tac [weakC_not_SOME] >>
     `type_ds (SOME mn) tenvM_no_sig tenvC_no_sig tenv ds cenv' tenv''`
              by metis_tac [weakC_refl, type_ds_weakening] >>
     `?r cenv'' store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_decs (SOME mn) (envM, envC, envE) store1 ds (store2,cenv'',r) ∧
        store_type_extension tenvS tenvS' ∧
        disjoint_env tenvC_no_sig cenv' ∧
        (∀err.
           r = Rerr err ⇒
           ∃tenvC1 tenvC2.
             cenv' = tenvC1 ++ tenvC2 ∧
             type_s (tenvC2 ++ tenvC_no_sig) tenvS' store2 ∧
             consistent_con_env (cenv'' ++ envC) (tenvC2 ++ tenvC_no_sig)) ∧
        (∀env'.
           r = Rval env' ⇒
           type_s (cenv' ++ tenvC_no_sig) tenvS' store2 ∧
           consistent_con_env (cenv'' ++ envC) (cenv' ++ tenvC_no_sig) ∧
           type_env (cenv' ++ tenvC_no_sig) tenvS' env' (bind_var_list2 tenv'' Empty) ∧
           type_env (cenv' ++ tenvC_no_sig) tenvS' (env' ++ envE) (bind_var_list2 tenv'' tenv))`
                      by metis_tac [decs_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?env''. r = Rval env'')` 
                by (cases_on `r` >> metis_tac []) >>
     rw [] >|
     [MAP_EVERY qexists_tac [`Rerr err`, `cenv''`, `store2`] >>
          imp_res_tac type_ds_mod >>
          imp_res_tac type_ds_tenvC_ok >>
          rw [type_sound_invariants_def, update_type_sound_inv_def] >-
          metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
          `weakM (bind mn [] tenvM_no_sig) tenvM_no_sig`
                       by (match_mp_tac weakM_bind >>
                           rw [weakM_refl]) >>
          `weakC (merge (tenvC1 ++ tenvC2) tenvC_no_sig) tenvC_no_sig` 
                       by (match_mp_tac disjoint_env_weakC >>
                           rw [] >>
                           fs [disjoint_env_def]) >>
          fs [bind_def, merge_def] >>
          `tenvM_ok ((mn,[])::tenvM_no_sig)` by fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def] >>
          `weakC (merge tenvC1 (tenvC2 ++ tenvC_no_sig)) (tenvC2 ++ tenvC_no_sig)`
                 by (match_mp_tac disjoint_env_weakC >>
                     fs [SIMP_RULE (srw_ss()) [merge_def] tenvC_ok_merge, disjoint_env_def] >>
                     metis_tac [DISJOINT_SYM]) >>
          MAP_EVERY qexists_tac [`tenvS'`, `(mn,[])::tenvM_no_sig`, `tenvC1++tenvC2++tenvC_no_sig`] >>
          rw [] >|
          [imp_res_tac type_ds_tenvC_ok >>
               fs [disjoint_env_def, GSYM merge_def, tenvC_ok_merge] >>
               fs [merge_def],
           metis_tac [still_has_exns],
           rw [replTheory.strip_mod_env_def] >>
               fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def],
           fs [weak_other_mods_def, bind_def, tenvC_one_mod_def, weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               every_case_tac >>
               fs [] >>
               metis_tac [optionTheory.option_case_def],
           rw [replTheory.strip_mod_env_def],
           rw [Once type_v_cases, replTheory.strip_mod_env_def, bind_var_list2_def, type_env_eqn] >>
               metis_tac [merge_def, type_v_weakening, type_v_rules,store_type_extension_weakS],
           metis_tac [top_to_cenv_def, consistent_con_env_decs_to_cenv],
           metis_tac [type_v_weakening, store_type_extension_weakS],
           metis_tac [type_s_weakening, store_type_extension_weakS, merge_def, APPEND_ASSOC],
           rw [replTheory.strip_mod_env_def] >>
               rw [GSYM bind_def] >>
               match_mp_tac weakM_bind2 >>
               rw [bind_def, tenv_ok_def, bind_var_list2_def],
           metis_tac [weakC_trans]],
      MAP_EVERY qexists_tac [`Rval ([(mn,env'')],emp)`, `cenv''`, `store2`] >>
          imp_res_tac type_ds_mod >>
          imp_res_tac type_ds_tenvC_ok >>
          rw [type_sound_invariants_def, update_type_sound_inv_def] >-
          metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
          `tenvM_ok (bind mn tenv'' tenvM_no_sig)`
                    by metis_tac [tenvM_ok_pres, type_v_freevars] >>
          `type_s (cenv' ++ tenvC_no_sig) tenvS' store2`
                   by metis_tac [type_s_weakening, weakC_refl, weakM_bind, weakM_refl] >>
          `tenv_ok (bind_var_list2 emp Empty)`
                       by (metis_tac [emp_def, tenv_ok_def, bind_var_list2_def]) >>
          `tenv_ok (bind_var_list2 tenv''' Empty)`
                       by (fs [check_signature_cases] >>
                           metis_tac [type_v_freevars, type_specs_tenv_ok]) >>
          `tenvC_ok (cenv' ++ tenvC_no_sig)` by rw [GSYM merge_def, tenvC_ok_merge] >>
          MAP_EVERY qexists_tac [`tenvS'`, `bind mn tenv'' tenvM_no_sig`, `cenv' ++ tenvC_no_sig`] >>
          rw [emp_def] >|
          [fs [check_signature_cases] >>
               imp_res_tac type_ds_tenvC_ok >>
               rw [GSYM merge_def, tenvC_ok_merge] >>
               `tenvC_ok (emp:tenvC)` by rw [tenvC_ok_def, emp_def] >>
               metis_tac [weakC_disjoint, type_specs_tenvC_ok],
           metis_tac [still_has_exns],
           metis_tac [tenvM_ok_pres, bind_def],
           fs [weak_other_mods_def, bind_def, tenvC_one_mod_def, weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               full_case_tac >>
               fs [] >>
               full_case_tac >>
               fs [] >>
               metis_tac [],
           rw [bind_def],
           rw [bind_def, Once type_v_cases] >>
               metis_tac [type_v_weakening,store_type_extension_weakS, weakM_bind,
                          weakM_refl, bind_def, merge_def, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM],
           rw [bind_var_list2_def] >>
                metis_tac [type_v_weakening, store_type_extension_weakS, weakM_bind, weakM_refl,
                           bind_def, merge_def, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM],
           `weakE tenv'' tenv'''` by (fs [check_signature_cases] >> metis_tac [weakE_refl]) >>
               metis_tac [bind_def, weakM_bind'],
           `weakC cenv' tenvC'` by (fs [check_signature_cases] >> metis_tac [weakC_refl]) >>
               metis_tac [weakC_merge']]]));

(* This version is for only putting seen constructors into the envC on a failed module *)
val update_type_sound_inv'_def = Define `
update_type_sound_inv' (tenvM:tenvM,tenvC:tenvC,tenv:tenvE,envM:envM,envC:envC,envE:envE,store) tenvM' tenvC' tenv' store' envC' r =
  case r of
     | Rval (envM',envE') => 
         (tenvM'++tenvM,tenvC'++tenvC,bind_var_list2 tenv' tenv,
          envM'++envM,envC'++envC,envE'++envE,store')
     | Rerr _ => (strip_mod_env tenvM'++tenvM,tenvC,tenv,strip_mod_env tenvM'++envM,envC'++envC,envE,store')`;

val top_type_soundness' = Q.store_thm ("top_type_soundness'",
`!tenvM tenvC tenv envM envC envE store1 tenvM' tenvC' tenv' top.
  type_sound_invariants (tenvM,tenvC,tenv,envM,envC,envE,store1) ∧
  type_top tenvM tenvC tenv top tenvM' tenvC' tenv' ∧
  ¬top_diverges (envM,envC,envE) store1 top ⇒
  ?r cenv2 store2. 
    (r ≠ Rerr Rtype_error) ∧
    evaluate_top (envM,envC,envE) store1 top (store2,cenv2,r) ∧
    type_sound_invariants (update_type_sound_inv' (tenvM,tenvC,tenv,envM,envC,envE,store1) tenvM' tenvC' tenv' store2 cenv2 r)`,
 rw [type_sound_invariants_def] >>
 `num_tvs tenv = 0` by metis_tac [type_v_freevars] >>
 fs [type_top_cases, top_diverges_cases] >>
 rw [evaluate_top_cases]
 >- (`weak_other_mods NONE tenvC_no_sig tenvC` by metis_tac [weakC_not_NONE] >>
     `type_d NONE tenvM_no_sig tenvC_no_sig tenv d tenvC' tenv'` by
     metis_tac [type_d_weakening] >>
     `?r store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_dec NONE (envM,envC,envE) store1 d (store2,r) ∧
        store_type_extension tenvS tenvS' ∧
        type_s tenvC_no_sig tenvS' store2 ∧
        disjoint_env tenvC_no_sig tenvC' ∧
        ∀cenv' env'.
         (r = Rval (cenv',env')) ⇒
         consistent_con_env (cenv' ++ envC) (tenvC' ++ tenvC_no_sig) ∧
         type_env (tenvC' ++ tenvC_no_sig) tenvS'
           (env' ++ envE) (bind_var_list2 tenv' tenv) ∧
         type_env (tenvC' ++ tenvC_no_sig) tenvS' env'
           (bind_var_list2 tenv' Empty)`
                by metis_tac [dec_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?cenv' env'. r = Rval (cenv',env'))` 
                by (cases_on `r` >> metis_tac [pair_CASES]) >>
     rw [] >|
     [MAP_EVERY qexists_tac [`Rerr err`, `emp`, `store2`] >>
          rw [type_sound_invariants_def, update_type_sound_inv'_def] >>
          MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `tenvC_no_sig`] >>
          rw [replTheory.strip_mod_env_def, emp_def] >|
          [metis_tac [type_v_weakening, store_type_extension_weakS,
                      weakC_refl],
           metis_tac [type_v_weakening, store_type_extension_weakS, weakC_refl, weakM_refl]],
      MAP_EVERY qexists_tac [`Rval (emp,env')`,`cenv'`, `store2`] >>
          imp_res_tac type_d_mod >>
          imp_res_tac type_d_tenvC_ok >>
          rw [type_sound_invariants_def, update_type_sound_inv'_def] >>
          `weakC (tenvC'++tenvC_no_sig) tenvC_no_sig`
                     by metis_tac [merge_def, disjoint_env_weakC] >>
          MAP_EVERY qexists_tac [`tenvS'`, `tenvM_no_sig`, `tenvC' ++ tenvC_no_sig`] >>
          rw [emp_def] >|
          [rw [GSYM merge_def, tenvC_ok_merge],
           rw [GSYM merge_def, tenvC_ok_merge],
           metis_tac [still_has_exns],
           fs [weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               full_case_tac >>
               fs [] >>
               metis_tac [],
           metis_tac [type_v_weakening, store_type_extension_weakS,
                      weakC_refl],
           metis_tac [type_s_weakening, weakM_refl],
           metis_tac [weakC_merge, merge_def]]])
 >- metis_tac [consistent_mod_env_dom, all_env_to_menv_def]
 >- (`weak_other_mods (SOME mn) tenvC_no_sig tenvC` by metis_tac [weakC_not_SOME] >>
     `type_ds (SOME mn) tenvM_no_sig tenvC_no_sig tenv ds cenv' tenv''`
              by metis_tac [weakC_refl, type_ds_weakening] >>
     `?r cenv'' store2 tenvS'.
        r ≠ Rerr Rtype_error ∧
        evaluate_decs (SOME mn) (envM,envC,envE) store1 ds (store2,cenv'',r) ∧
        store_type_extension tenvS tenvS' ∧
        disjoint_env tenvC_no_sig cenv' ∧
        (∀err.
           r = Rerr err ⇒
           ∃tenvC1 tenvC2.
             cenv' = tenvC1 ++ tenvC2 ∧
             type_s (tenvC2 ++ tenvC_no_sig) tenvS' store2 ∧
             consistent_con_env (cenv'' ++ envC) (tenvC2 ++ tenvC_no_sig)) ∧
        (∀env'.
           r = Rval env' ⇒
           type_s (cenv' ++ tenvC_no_sig) tenvS' store2 ∧
           consistent_con_env (cenv'' ++ envC) (cenv' ++ tenvC_no_sig) ∧
           type_env (cenv' ++ tenvC_no_sig) tenvS' env' (bind_var_list2 tenv'' Empty) ∧
           type_env (cenv' ++ tenvC_no_sig) tenvS' (env' ++ envE) (bind_var_list2 tenv'' tenv))`
                      by metis_tac [decs_type_soundness] >>
     `(?err. r = Rerr err) ∨ (?env''. r = Rval env'')` 
                by (cases_on `r` >> metis_tac []) >>
     rw [] >|
     [MAP_EVERY qexists_tac [`Rerr err`, `cenv''`, `store2`] >>
          rw [type_sound_invariants_def, update_type_sound_inv'_def] >-
          metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
          `weakM (bind mn [] tenvM_no_sig) tenvM_no_sig`
                       by (match_mp_tac weakM_bind >>
                           rw [weakM_refl]) >>
          `weakC (merge tenvC2 tenvC_no_sig) tenvC_no_sig` 
                       by (match_mp_tac disjoint_env_weakC >>
                           rw [] >>
                           fs [disjoint_env_def]) >>
          fs [bind_def, merge_def] >>
          `tenvM_ok ((mn,[])::tenvM_no_sig)` by fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def] >>
          MAP_EVERY qexists_tac [`tenvS'`, `(mn,[])::tenvM_no_sig`, `tenvC2++tenvC_no_sig`] >>
          rw [] >|
          [imp_res_tac type_ds_tenvC_ok >>
               fs [disjoint_env_def, GSYM merge_def, tenvC_ok_merge] >>
               fs [merge_def],
           match_mp_tac still_has_exns >>
               rw [] >>
               fs [disjoint_env_def],
           rw [replTheory.strip_mod_env_def] >>
               fs [tenvM_ok_def, bind_var_list2_def, tenv_ok_def],
           imp_res_tac type_ds_mod >>
               fs [weak_other_mods_def, bind_def, tenvC_one_mod_def, weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               full_case_tac >>
               fs [] >-
               metis_tac [] >>
               cases_on `lookup (mk_id x cn) tenvC1` >>
               fs [] >>
               metis_tac [optionTheory.option_case_def],
           rw [replTheory.strip_mod_env_def],
           rw [Once type_v_cases, replTheory.strip_mod_env_def, bind_var_list2_def, type_env_eqn] >>
               metis_tac [type_v_weakening, store_type_extension_weakS],
           metis_tac [type_v_weakening, store_type_extension_weakS],
           rw [replTheory.strip_mod_env_def] >>
               rw [GSYM bind_def] >>
               match_mp_tac weakM_bind2 >>
               rw [bind_def, tenv_ok_def, bind_var_list2_def],
           metis_tac [weakC_trans]],
      MAP_EVERY qexists_tac [`Rval ([(mn,env'')],emp)`, `cenv''`, `store2`] >>
          imp_res_tac type_ds_mod >>
          imp_res_tac type_ds_tenvC_ok >>
          rw [type_sound_invariants_def, update_type_sound_inv'_def] >-
          metis_tac [consistent_mod_env_dom, all_env_to_menv_def] >>
          `tenvM_ok (bind mn tenv'' tenvM_no_sig)`
                    by metis_tac [tenvM_ok_pres, type_v_freevars] >>
          `type_s (cenv' ++ tenvC_no_sig) tenvS' store2`
                   by metis_tac [type_s_weakening, weakC_refl, weakM_bind, weakM_refl] >>
          `tenv_ok (bind_var_list2 emp Empty)`
                       by (metis_tac [emp_def, tenv_ok_def, bind_var_list2_def]) >>
          `tenv_ok (bind_var_list2 tenv''' Empty)`
                       by (fs [check_signature_cases] >>
                           metis_tac [type_v_freevars, type_specs_tenv_ok]) >>
          `tenvC_ok (cenv' ++ tenvC_no_sig)` by rw [GSYM merge_def, tenvC_ok_merge] >>
          MAP_EVERY qexists_tac [`tenvS'`, `bind mn tenv'' tenvM_no_sig`, `cenv' ++ tenvC_no_sig`] >>
          rw [emp_def] >|
          [fs [check_signature_cases] >>
               imp_res_tac type_ds_tenvC_ok >>
               rw [GSYM merge_def, tenvC_ok_merge] >>
               `tenvC_ok (emp:tenvC)` by rw [tenvC_ok_def, emp_def] >>
               metis_tac [weakC_disjoint, type_specs_tenvC_ok],
           metis_tac [still_has_exns],
           metis_tac [tenvM_ok_pres, bind_def],
           fs [weak_other_mods_def, bind_def, tenvC_one_mod_def, weakC_mods_def, SUBSET_DEF, lookup_append] >>
               rw [] >>
               full_case_tac >>
               fs [] >>
               full_case_tac >>
               fs [] >>
               metis_tac [],
           rw [bind_def],
           rw [bind_def, Once type_v_cases] >>
               metis_tac [type_v_weakening,store_type_extension_weakS, weakM_bind,
                          weakM_refl, bind_def, merge_def, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM],
           rw [bind_var_list2_def] >>
                metis_tac [type_v_weakening, store_type_extension_weakS, weakM_bind, weakM_refl,
                           bind_def, merge_def, disjoint_env_weakC, disjoint_env_def, DISJOINT_SYM],
           `weakE tenv'' tenv'''` by (fs [check_signature_cases] >> metis_tac [weakE_refl]) >>
               metis_tac [bind_def, weakM_bind'],
           `weakC cenv' tenvC'` by (fs [check_signature_cases] >> metis_tac [weakC_refl]) >>
               metis_tac [weakC_merge']]]));

val tac2 =
rw [Once type_v_cases, type_env_eqn, Tfn_def, Tint_def, Tbool_def, 
    consistent_con_env_def, envC_has_exns_def, restrict_tenvC_def] >>
qexists_tac `[]` >>
NTAC 6 (rw [Once type_e_cases, check_freevars_def, num_tvs_def, bind_tenv_def,
            lookup_tenv_def, bind_tvar_def, Tfn_def, Tint_def, type_op_def, 
            type_uop_def, t_lookup_var_id_def, deBruijn_inc_def, deBruijn_subst_def,
            METIS_PROVE [] ``(?x. P ∧ Q x) = (P ∧ ?x. Q x)``, Tbool_def,
            Tref_def, consistent_con_env_def, restrict_tenvC_def, tenvM_ok_def]) >>
full_simp_tac (srw_ss()++ARITH_ss) [restrict_tenvC_def] >>
NTAC 6 (rw [Once consistent_mod_cases]);

val tac = 
tac2 >>
metis_tac [type_env_eqn, EVERY_DEF, LENGTH, DECIDE ``~(0<0:num)``];

val initial_type_sound_invariants = Q.store_thm ("initial_type_sound_invariant",
`type_sound_invariants ([],init_tenvC,init_tenv,[],init_envC,init_env,[])`,
 rw [type_sound_invariants_def, tenvC_has_exns_def,
     tenvM_ok_def, tenvC_ok_def, weakM_def, weakC_def, type_s_def,
     store_lookup_def, lookup_def] >>
 MAP_EVERY qexists_tac [`[]`, `init_tenvC`] >>
 rw [consistent_con_env_def, weakC_mods_def] >>
 fs [same_module_def, init_env_def, init_tenv_def, init_tenvC_def,
     init_envC_def, check_freevars_def] >>
 rw [] >>
 rw [] >>
 fs []
 >- (rw [EXTENSION] >>
     every_case_tac)
 >- NTAC 6 (rw [Once consistent_mod_cases]) >>
 rw [type_env_eqn]
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
 >- (tac2 >>
     qexists_tac `Empty` >>
     rw [type_env_eqn] >>
     qexists_tac `Tapp [Tvar_db 0] TC_ref` >>
     rw [] >>
     qexists_tac `[]` >>
     rw [])
 >- tac
 >- (tac2 >>
     qexists_tac `Empty` >>
     rw [type_env_eqn] >>
     qexists_tac `Tapp [Tvar_db 0] TC_ref` >>
     rw [] >>
     qexists_tac `[]` >>
     rw [])
 >- tac);

val _ = export_theory ();
