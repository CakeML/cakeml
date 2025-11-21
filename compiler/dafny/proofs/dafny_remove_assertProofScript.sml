(*
  Show that removing assert preserves semantics of "good" programs.
*)
Theory dafny_remove_assertProof
Ancestors
  dafny_semanticPrimitives
  dafny_evaluate
  dafny_remove_assert
Libs
  preamble

Definition env_rel_def:
  env_rel env env' ⇔
    env'.prog = remove_assert env.prog
End

Theorem env_rel_get_member_none_aux[local]:
  get_member_aux name members = NONE ⇒
  get_member_aux name (MAP remove_assert_member members) = NONE
Proof
  Induct_on ‘members’ >- (simp [])
  \\ Cases \\ rpt strip_tac
  \\ gvs [get_member_aux_def, remove_assert_member_def]
QED

Theorem env_rel_get_member_none[local]:
  env_rel env env' ∧ get_member name env.prog = NONE ⇒
  get_member name env'.prog = NONE
Proof
  rpt strip_tac
  \\ gvs [env_rel_def]
  \\ namedCases_on ‘env.prog’ ["members"]
  \\ gvs [get_member_def, remove_assert_def]
  \\ drule env_rel_get_member_none_aux \\ simp []
QED

Theorem env_rel_get_member_method_aux[local]:
  get_member_aux name members =
    SOME (Method name' ins req ens rds decrs outs mod body) ⇒
  get_member_aux name (MAP remove_assert_member members) =
    SOME
      (Method name' ins req ens rds decrs outs mod (remove_assert_stmt body))
Proof
  Induct_on ‘members’ >- (simp [get_member_aux_def])
  \\ Cases \\ rpt strip_tac
  \\ gvs [get_member_aux_def, remove_assert_member_def]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem env_rel_get_member_method[local]:
  env_rel env env' ∧
  get_member name env.prog =
  SOME (Method name' ins req ens rds decrs outs mod body) ⇒
  get_member name env'.prog =
    SOME (Method name' ins req ens rds decrs outs mod (remove_assert_stmt body))
Proof
  rpt strip_tac
  \\ gvs [env_rel_def]
  \\ namedCases_on ‘env.prog’ ["members"]
  \\ gvs [get_member_def, remove_assert_def]
  \\ drule env_rel_get_member_method_aux \\ simp []
QED

Theorem env_rel_get_member_function_aux[local]:
  get_member_aux name members =
    SOME (Function name' ins res_t req rds decrs body) ⇒
  get_member_aux name (MAP remove_assert_member members) =
    SOME (Function name' ins res_t req rds decrs body)
Proof
  Induct_on ‘members’ >- (simp [])
  \\ Cases \\ rpt strip_tac
  \\ gvs [get_member_aux_def, remove_assert_member_def]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem env_rel_get_member_function[local]:
  env_rel env env' ∧
  get_member name env.prog = r ∧
  r = SOME (Function name' ins res_t req rds decrs body) ⇒
  get_member name env'.prog = r
Proof
  rpt strip_tac
  \\ gvs [env_rel_def]
  \\ namedCases_on ‘env.prog’ ["members"]
  \\ gvs [get_member_def, remove_assert_def]
  \\ drule env_rel_get_member_function_aux \\ simp []
QED

Theorem env_rel_evaluate_exp[local]:
  (∀s env' e env.
     env_rel env env' ⇒ evaluate_exp s env' e = evaluate_exp s env e) ∧
  (∀s env' es env.
     env_rel env env' ⇒ evaluate_exps s env' es = evaluate_exps s env es)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Lit’] >- (gvs [evaluate_exp_def])
  >~ [‘Var’] >- (gvs [evaluate_exp_def])
  >~ [‘If’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 3 TOP_CASE_TAC \\ simp [])
  >~ [‘UnOp’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘BinOp’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 3 TOP_CASE_TAC \\ gvs []
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ArrLen’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ArrSel’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘FunCall’] >-
   (gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ simp []
    >- (drule_all_then assume_tac env_rel_get_member_none \\ simp [])
    \\ Cases_on ‘member’ \\ simp []
    >- (drule_all_then assume_tac env_rel_get_member_method \\ simp [])
    >-
     (drule env_rel_get_member_function \\ simp []
      \\ disch_then $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ simp []
      \\ ntac 3 TOP_CASE_TAC
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ simp []))
  >~ [‘Forall’] >-
   (last_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def, eval_forall_def])
  >~ [‘Old’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘OldHeap’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘Prev’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘PrevHeap’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘SetPrev’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘Let’] >-
   (gvs [evaluate_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ForallHeap’] >-
   (first_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def]
    \\ ntac 3 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘[]’] >- (gvs [evaluate_exp_def])
  >~ [‘_::_’] >-
   (first_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def]
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
QED

Theorem env_rel_evaluate_rhs_exp[local]:
  env_rel env env' ⇒
  evaluate_rhs_exp s env' e = evaluate_rhs_exp s env e
Proof
  strip_tac
  \\ Cases_on ‘e’
  >~ [‘ExpRhs’] >-
   (simp [evaluate_rhs_exp_def]
    \\ drule_then assume_tac (cj 1 env_rel_evaluate_exp) \\ simp [])
  >~ [‘ArrAlloc’] >-
   (simp [evaluate_rhs_exp_def]
    \\ TOP_CASE_TAC
    \\ drule_then assume_tac (cj 1 env_rel_evaluate_exp) \\ gvs [])
QED

Theorem env_rel_evaluate_rhs_exps[local]:
  ∀s env' es env.
    env_rel env env' ⇒
    evaluate_rhs_exps s env' es = evaluate_rhs_exps s env es
Proof
  Induct_on ‘es’ >- (simp [evaluate_rhs_exps_def])
  \\ rpt strip_tac
  \\ simp [evaluate_rhs_exps_def]
  \\ drule_then assume_tac env_rel_evaluate_rhs_exp \\ simp []
  \\ ntac 2 TOP_CASE_TAC
  \\ last_x_assum $ drule_then assume_tac \\ simp []
QED

Theorem env_rel_assign_value[local]:
  env_rel env env' ⇒
  assign_value s env' lhs rhs = assign_value s env lhs rhs
Proof
  strip_tac
  \\ Cases_on ‘lhs’ >- (simp [assign_value_def])
  \\ simp [assign_value_def]
  \\ TOP_CASE_TAC
  \\ drule_all_then assume_tac (cj 1 env_rel_evaluate_exp) \\ gvs []
QED

Theorem env_rel_assign_values[local]:
  ∀s env' lhss rhss env.
    env_rel env env' ⇒
    assign_values s env' lhss rhss = assign_values s env lhss rhss
Proof
  ho_match_mp_tac assign_values_ind
  \\ rpt strip_tac
  \\ gvs [assign_values_def]
  \\ drule_then assume_tac env_rel_assign_value \\ gvs []
  \\ ntac 2 TOP_CASE_TAC \\ simp []
QED

Theorem correct_remove_assert_stmt:
  ∀s env stmt s' env' r.
    evaluate_stmt s env stmt = (s', r) ∧ env_rel env env' ∧
    r ≠ Rstop (Serr Rfail) ∧ r ≠ Rstop (Serr Rtimeout) ⇒
    evaluate_stmt s env' (remove_assert_stmt stmt) = (s', r)
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ simp [remove_assert_stmt_def]
  \\ rpt strip_tac
  >~ [‘Skip’] >- (gvs [evaluate_stmt_def])
  >~ [‘Assert’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ rename [‘Rerr err’] \\ Cases_on ‘err’ \\ gvs [])
  >~ [‘Then’] >- (gvs [evaluate_stmt_def, AllCaseEqs()])
  >~ [‘If’] >-
   (drule_then assume_tac (cj 1 env_rel_evaluate_exp)
    \\ gvs [evaluate_stmt_def, oneline do_cond_def, AllCaseEqs()])
  >~ [‘Dec local’] >-
   (qpat_x_assum ‘evaluate_stmt _ _ _ = _ ’ mp_tac
    \\ simp [evaluate_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ TOP_CASE_TAC \\ rpt strip_tac \\ gvs [])
  >~ [‘Assign’] >-
   (gvs [evaluate_stmt_def]
    \\ drule_then assume_tac env_rel_evaluate_rhs_exps \\ simp []
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ drule_then assume_tac env_rel_assign_values \\ simp [])
  >~ [‘While’] >-
   (qpat_x_assum ‘evaluate_stmt _ _ _ = _’ mp_tac
    \\ simp [evaluate_stmt_def]
    \\ IF_CASES_TAC >- (simp [])
    \\ simp []
    \\ drule_then assume_tac (cj 1 env_rel_evaluate_exp) \\ simp []
    \\ ntac 2 TOP_CASE_TAC
    \\ IF_CASES_TAC >- (simp [])
    \\ reverse IF_CASES_TAC >- (simp [])
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC >- (rpt strip_tac \\ gvs [])
    \\ strip_tac \\ gvs []
    \\ last_x_assum drule
    \\ simp [STOP_def, remove_assert_stmt_def])
  >~ [‘Print’] >-
   (drule_then assume_tac (cj 1 env_rel_evaluate_exp)
    \\ gvs [evaluate_stmt_def])
  >~ [‘MetCall’] >-
   (qpat_x_assum ‘evaluate_stmt _ _ _ = _’ mp_tac
    \\ simp [evaluate_stmt_def]
    \\ TOP_CASE_TAC >- (simp [])
    \\ reverse TOP_CASE_TAC >- (simp [])
    \\ drule_all_then assume_tac env_rel_get_member_method \\ simp []
    \\ TOP_CASE_TAC
    \\ drule_then assume_tac (cj 2 env_rel_evaluate_exp) \\ simp []
    \\ ntac 2 TOP_CASE_TAC
    \\ IF_CASES_TAC >- (simp [])
    \\ simp []
    \\ TOP_CASE_TAC
    \\ TOP_CASE_TAC  >- (simp [])
    \\ reverse TOP_CASE_TAC >- (rpt strip_tac \\ gvs [])
    \\ gvs []
    \\ TOP_CASE_TAC
    \\ IF_CASES_TAC >- (simp [])
    \\ simp []
    \\ strip_tac \\ drule env_rel_assign_values \\ simp [])
  >~ [‘Return’] >- (gvs [evaluate_stmt_def])
QED

Theorem member_name_remove_assert_member_eq[local]:
  MAP member_name (MAP remove_assert_member members) =
  MAP member_name members
Proof
  Induct_on ‘members’ >- (simp [])
  \\ Cases \\ gvs [remove_assert_member_def]
QED

Theorem correct_remove_assert:
  evaluate_program ck prog = (s,Rcont) ⇒
  evaluate_program ck (remove_assert prog) = (s,Rcont)
Proof
  namedCases_on ‘prog’ ["members"]
  \\ simp [remove_assert_def, evaluate_program_def]
  \\ simp [member_name_remove_assert_member_eq]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [mk_env_def]
  \\ strip_tac
  \\ drule correct_remove_assert_stmt \\ simp [remove_assert_stmt_def]
  \\ disch_then irule
  \\ simp [env_rel_def, remove_assert_def]
QED
