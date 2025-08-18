(*
  Correctness for the source_let pass.
 *)
Theory source_letProof
Ancestors
  source_let evaluate evaluateProps semanticPrimitives
  semanticPrimitivesProps misc[qualified] semantics ast
  source_evalProof
Libs
  preamble


Triviality env_c_lemma:
  (<|v := build_rec_env q env env1; c := nsEmpty|> +++ env).c = env.c
Proof
  fs [extend_dec_env_def]
QED

Theorem evaluate_lift_let:
  evaluate_decs s env [d] = (s', res) ∧
  res ≠ Rerr (Rabort Rtype_error) ∧
  lift_let d = SOME (d1, d2) ⇒
    evaluate_decs s env [Dlocal [d1] [d2]] = (s', res)
Proof
  Cases_on ‘d’ \\ simp [Once lift_let_def]
  \\ TOP_CASE_TAC \\ gs []
  >- (
    TOP_CASE_TAC \\ gs []
    \\ TOP_CASE_TAC \\ gvs [dest_Letrec_SOME]
    \\ rw [] \\ gs [evaluate_decs_def, evaluate_def]
    \\ reverse IF_CASES_TAC \\ gs [env_c_lemma]
    >-
     (qsuff_tac ‘~EVERY (λ(n,v,e'). every_exp (one_con_check env.c) e') q’
      \\ rpt strip_tac \\ full_simp_tac bool_ss [] \\ fs []
      \\ fs [EVERY_MEM,EXISTS_MEM,EXISTS_PROD,FORALL_PROD,SF SFY_ss]
      \\ res_tac \\ fs [])
    \\ IF_CASES_TAC \\ gs [env_c_lemma]
    \\ gs [extend_dec_env_def]
    \\ ‘<| v := nsAppend (build_rec_env q env nsEmpty) env.v;
           c := env.c|> =
        env with v := build_rec_env q env env.v’
      by rw [sem_env_component_equality, build_rec_env_merge]
    \\ gs [])
  \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ gvs [dest_Let_SOME]
  \\ rw [] \\ gs [evaluate_decs_def, evaluate_def]
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ rw [] \\ gs [evaluate_decs_def]
  \\ gs [pat_bindings_def, namespaceTheory.nsOptBind_def, pmatch_def]
  \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gvs [CaseEq "bool"]
  \\ CASE_TAC \\ gs [extend_dec_env_def]
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ ‘<| v := nsBind x v env.v; c := env.c |> =
      env with v := nsBind x v env.v’
    by rw [sem_env_component_equality, build_rec_env_merge]
  \\ gs []
QED

Theorem lift_lets_is_prefix:
  ∀ds d ds1 ds2.
    lift_lets ds d = SOME (ds1, ds2) ⇒ REVERSE ds ≼ ds1
Proof
  ho_match_mp_tac lift_lets_ind \\ rw []
  \\ qpat_x_assum ‘lift_lets _ _ = _’ mp_tac
  \\ rw [Once lift_lets_def]
  \\ gvs [CaseEqs ["option", "prod", "list"], IS_PREFIX_APPEND]
QED

Theorem evaluate_lift_lets:
  ∀ds d s env s1 env1 s2 res ds1 ds2.
    evaluate_decs s env (REVERSE ds) = (s1, Rval env1) ∧
    evaluate_decs s1 (extend_dec_env env1 env) [d] = (s2, res) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    lift_lets ds d = SOME (ds1, ds2) ⇒
      evaluate_decs s env [Dlocal ds1 [ds2]] = (s2, res)
Proof
  ho_match_mp_tac lift_lets_ind \\ rw []
  \\ qpat_x_assum ‘lift_lets _ _ = _’ mp_tac
  \\ simp [Once lift_lets_def]
  \\ rename [‘lift_let d’] \\ Cases_on ‘lift_let d’ \\ simp []
  >- (
    rw [CaseEqs ["list"], evaluate_decs_def]
    \\ gs [])
  \\ rw [CaseEqs ["prod", "option"]]
  \\ gs [evaluate_decs_def]
  \\ first_x_assum (qspecl_then [‘s’,‘env’] mp_tac)
  \\ simp [evaluate_decs_append]
  \\ drule_all evaluate_lift_let
  \\ simp [evaluate_decs_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ gs [combine_dec_result_def, extend_dec_env_def]
  \\ drule_then assume_tac lift_lets_is_prefix
  \\ gvs [IS_PREFIX_APPEND]
  \\ rw [evaluate_decs_append, extend_dec_env_def, combine_dec_result_def]
QED

Theorem lift_lets_mod_local[local,simp]:
  (!ds1 ds2. lift_lets [] (Dlocal ds1 ds2) = NONE) /\
  (!mn ds. lift_lets [] (Dmod mn ds) = NONE)
Proof
    once_rewrite_tac [lift_lets_def]
    \\ simp [lift_let_def]
QED

Theorem evaluate_lift_start[local] =
  Q.SPEC ‘[]’ evaluate_lift_lets
  |> SIMP_RULE (srw_ss()) [Once extend_dec_env_def];

Theorem compile_decs_correct:
  ∀s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate_decs s env (compile_decs ds) = (s', res)
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rw [Once compile_decs_def]
  \\ simp [Once compile_decs_def]
  >~ [‘d1::d2::ds’] >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    \\ simp [Once evaluate_decs_def]
    \\ Cases_on `lift_lets [] d1 = NONE` \\ gs []
    >- (
      Cases_on `(?mn1 ds1. d1 = Dmod mn1 ds1) \/
                ?ds2 ds3. d1 = Dlocal ds2 ds3`
      >- (
        gs []
        \\ qpat_x_assum `!s res. _` mp_tac
        \\ simp [Once evaluate_decs_def] \\ strip_tac
        \\ simp [Once evaluate_decs_def]
        \\ CASE_TAC \\ gvs [] \\ strip_tac
        \\ simp [Once evaluate_decs_cons]
        \\ gvs [CaseEqs ["prod", "result"], combine_dec_result_def, SF SFY_ss,
                evaluate_decs_def, compile_decs_def])
      \\ gs [] \\ strip_tac
      \\ `evaluate_decs s env (d1::compile_decs (d2::ds)) = (s',res)`
        suffices_by (rw [] \\ Cases_on `d1` \\ gs [])
      \\ simp [Once evaluate_decs_cons]
      \\ gvs [CaseEqs ["prod", "result"], combine_dec_result_def])
    \\ `?pre1 ds1. lift_lets [] d1 = SOME (pre1,ds1)`
        by (Cases_on `lift_lets [] d1` \\ gs [ABS_PAIR_THM])
    \\ gs [] \\ strip_tac
    \\ simp [Once evaluate_decs_cons]
    \\ CASE_TAC \\ gs []
    \\ Cases_on `evaluate_decs s env [d1]` \\ gs []
    \\ drule evaluate_lift_start \\ gs []
    \\ strip_tac \\ gvs [CaseEqs ["prod", "result"], combine_dec_result_def])
  \\ simp [compile_decs_def]
  >~ [‘[Dmod _ _]’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], combine_dec_result_def])
  >~ [‘[Dlocal (compile_decs _) _]’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], combine_dec_result_def])
  \\ qmatch_goalsub_abbrev_tac `lift_lets [] d`
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ gs [evaluate_lift_start, SF SFY_ss]
QED

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile_decs prog) outcome
Proof
  Cases_on ‘outcome’ \\ gs [SF CONJ_ss]
  >~ [‘Terminate outcome tr’] >- (
    rw [semantics_prog_def]
    \\ gs [evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ gvs []
    \\ drule_all_then assume_tac compile_decs_correct
    \\ qexists_tac ‘k’ \\ simp [])
  >~ [‘Diverge tr’] >- (
    rw [semantics_prog_def]
    >- (
      first_x_assum (qspec_then ‘k’ strip_assume_tac)
      \\ gs [evaluate_prog_with_clock_def]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ drule compile_decs_correct \\ rw [])
    \\ qmatch_asmsub_abbrev_tac ‘IMAGE f1’
    \\ qmatch_goalsub_abbrev_tac ‘IMAGE f2’
    \\ ‘f1 = f2’
      suffices_by (rw [] \\ gs [])
    \\ unabbrev_all_tac
    \\ rw [FUN_EQ_THM]
    \\ gs [evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ gs [])
    \\ last_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
    \\ drule_at_then (Pos (el 2)) drule_all compile_decs_correct \\ rw [])
QED

Theorem compile_semantics_oracle:
  ∀f.
  source_evalProof$is_insert_oracle ci f s.eval_state ∧
  ¬ semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (compile_decs ∘ f))
        env prog outcome
Proof
  rw []
  \\ irule adjust_oracle_semantics_prog
  \\ rw []
  \\ irule compile_decs_correct
  \\ simp []
QED

