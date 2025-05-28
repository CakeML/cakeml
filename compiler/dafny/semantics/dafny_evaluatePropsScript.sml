(*
  Properties of Dafny's functional big-step semantics.
*)

open preamble
open quantHeuristicsTheory  (* LIST_LENGTH_1 *)
open dafny_evaluateTheory
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluateProps";

(* Lemmas about the length of locals *)

Theorem evaluate_exp_len_locals:
  (∀s env e s' r.
     evaluate_exp s env e = (s', r) ⇒ LENGTH s'.locals = LENGTH s.locals) ∧
  (∀s env es s' r.
     evaluate_exps s env es = (s', r) ⇒ LENGTH s'.locals = LENGTH s.locals)
Proof
  ho_match_mp_tac evaluate_exp_ind \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, set_up_call_def, restore_locals_def, AllCaseEqs()]
QED

Theorem declare_local_len_inc:
  ∀s v. LENGTH (declare_local s v).locals = LENGTH s.locals + 1
Proof
  gvs [declare_local_def]
QED

Triviality pop_local_len_dec:
  ∀s s'. pop_local s = SOME s' ⇒ LENGTH s'.locals = LENGTH s.locals - 1
Proof
  rpt strip_tac \\ gvs [pop_local_def, AllCaseEqs()]
QED

Triviality update_local_aux_len_locals:
  ∀locals var val locals'.
    update_local_aux locals var val = SOME locals' ⇒
    LENGTH locals = LENGTH locals'
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [update_local_aux_def] \\ PairCases_on ‘h’
  \\ gvs [update_local_aux_def, AllCaseEqs()] \\ res_tac
QED

Triviality update_local_len_locals:
  ∀s var val s'.
    update_local s var val = SOME s' ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  rpt strip_tac
  \\ gvs [update_local_def, AllCaseEqs()]
  \\ imp_res_tac update_local_aux_len_locals \\ gvs []
QED

Triviality assign_value_len_locals:
  ∀s env lhs rhs s' r.
    assign_value s env lhs rhs = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  \\ gvs [assign_value_def, update_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals \\ gvs []
  \\ imp_res_tac update_local_len_locals
QED

Triviality assign_values_len_locals:
  ∀s env lhss vals s' r.
    assign_values s env lhss vals = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘vals’ \\ rpt strip_tac
  \\ gvs [assign_values_def, AllCaseEqs()]
  \\ imp_res_tac assign_value_len_locals \\ res_tac \\ gvs []
QED

Theorem evaluate_rhs_exp_len_locals:
  ∀s env e.
    evaluate_rhs_exp s env e = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Cases_on ‘e’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals \\ gvs []
QED

Theorem evaluate_rhs_exps_len_locals:
  ∀s env es s' r.
    evaluate_rhs_exps s env es = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, AllCaseEqs ()]
  \\ imp_res_tac evaluate_rhs_exp_len_locals \\ res_tac \\ gvs []
QED

Theorem locals_not_empty_pop_locals_some:
  ∀s. 0 < LENGTH s.locals ⇒ ∃s'. pop_local s = SOME s'
Proof
  rpt strip_tac \\ gvs [pop_local_def, LIST_LENGTH_1]
QED

Theorem evaluate_stmt_len_locals:
  ∀s env scope s' r.
    evaluate_stmt s env scope = (s', r) ⇒
    LENGTH s'.locals = LENGTH s.locals
Proof
  ho_match_mp_tac evaluate_stmt_ind \\ rpt strip_tac
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [declare_local_len_inc, AllCaseEqs()] \\ rename [‘pop_local s₁’]
    >- (‘0 < LENGTH s₁.locals’ by gvs []
        \\ imp_res_tac locals_not_empty_pop_locals_some \\ gvs [])
    \\ imp_res_tac pop_local_len_dec \\ gvs [])
  \\ gvs [evaluate_stmt_def, dec_clock_def, print_string_def,
          restore_locals_def, set_up_call_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_len_locals
  \\ imp_res_tac assign_values_len_locals
  \\ imp_res_tac evaluate_rhs_exps_len_locals \\ gvs []
QED

val _ = export_theory ();
