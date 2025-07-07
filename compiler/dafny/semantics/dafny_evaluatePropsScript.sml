(*
  Properties of Dafny's functional big-step semantics.
*)
Theory dafny_evaluateProps
Ancestors
  dafny_evaluate dafny_semanticPrimitives
Libs
  preamble


(* After evaluate, only the value of locals can have changed. *)

Theorem evaluate_exp_locals:
  (∀s env e s' r.
     evaluate_exp s env e = (s', r) ⇒
     MAP FST s'.locals = MAP FST s.locals) ∧
  (∀s env es s' r.
     evaluate_exps s env es = (s', r) ⇒
     MAP FST s'.locals = MAP FST s.locals)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, set_up_call_def, restore_caller_def, unuse_old_def,
          AllCaseEqs()]
QED

Theorem evaluate_rhs_exp_locals:
  ∀s env e.
    evaluate_rhs_exp s env e = (s', r) ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  Cases_on ‘e’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_locals \\ gvs []
QED

Theorem evaluate_rhs_exps_locals:
  ∀s env es s' r.
    evaluate_rhs_exps s env es = (s', r) ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_rhs_exp_locals \\ gvs []
  \\ res_tac \\ gvs []
QED

Triviality update_local_aux_locals:
  ∀locals var val locals'.
    update_local_aux locals var val = SOME locals' ⇒
    MAP FST locals = MAP FST locals'
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [update_local_aux_def] \\ PairCases_on ‘h’
  \\ gvs [update_local_aux_def, AllCaseEqs()] \\ res_tac
QED

Triviality update_local_locals:
  ∀s var val s'.
    update_local s var val = SOME s' ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  rpt strip_tac
  \\ gvs [update_local_def, AllCaseEqs()]
  \\ imp_res_tac update_local_aux_locals \\ gvs []
QED

Theorem assign_value_locals:
  ∀s env lhs rhs s' r.
    assign_value s env lhs rhs = (s', r) ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  \\ gvs [assign_value_def, update_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_locals
  \\ imp_res_tac update_local_locals
  \\ gvs []
QED

Theorem assign_values_locals:
  ∀s env lhss vals s' r.
    assign_values s env lhss vals = (s', r) ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘vals’ \\ rpt strip_tac
  \\ gvs [assign_values_def, AllCaseEqs()]
  \\ imp_res_tac assign_value_locals \\ gvs []
  \\ res_tac \\ gvs []
QED

Theorem evaluate_stmt_locals:
  ∀s env stmt s' r.
    evaluate_stmt s env stmt = (s', r) ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt strip_tac
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def, declare_local_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ rename [‘pop_local s₁’]
    \\ ‘s₁.locals ≠ []’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs [pop_local_def, AllCaseEqs()])
  \\ gvs [evaluate_stmt_def, dec_clock_def, print_string_def,
          restore_caller_def, set_up_call_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_locals
  \\ imp_res_tac assign_values_locals
  \\ imp_res_tac evaluate_rhs_exps_locals \\ gvs []
QED

(* evaluating x elements successfully results in x values *)

Theorem evaluate_rhs_exps_len_eq:
  ∀s env es s' vs.
    evaluate_rhs_exps s env es = (s', Rval vs) ⇒ LENGTH vs = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, AllCaseEqs()]
  \\ res_tac
QED

