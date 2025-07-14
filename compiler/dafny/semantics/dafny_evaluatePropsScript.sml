(*
  Properties of Dafny's functional big-step semantics.
*)
Theory dafny_evaluateProps
Ancestors
  dafny_evaluate dafny_semanticPrimitives
Libs
  preamble


(* evaluating x elements successfully results in x values *)

Theorem evaluate_exps_len_eq:
  ∀es s env s' vs.
    evaluate_exps s env es = (s', Rval vs) ⇒ LENGTH vs = LENGTH es
Proof
  Induct \\ simp [evaluate_exp_def]
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs()]
  \\ res_tac
QED

Theorem evaluate_rhs_exps_len_eq:
  ∀s env es s' vs.
    evaluate_rhs_exps s env es = (s', Rval vs) ⇒ LENGTH vs = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_rhs_exps_def, AllCaseEqs()]
  \\ res_tac
QED

(* Evaluating an expression only changes the clock. *)

Theorem evaluate_exp_with_clock:
  (∀s env e s' r.
     evaluate_exp s env e = (s', r) ⇒ ∃ck. s' = s with clock := ck) ∧
  (∀s env es s' r.
     evaluate_exps s env es = (s', r) ⇒ ∃ck. s' = s with clock := ck)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Let vars body’] >-
   (gvs [evaluate_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [AllCaseEqs()]
    \\ simp [state_component_equality]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac evaluate_exps_len_eq
    \\ gvs [UNZIP_MAP]
    \\ gvs [pop_locals_def, safe_drop_def, push_locals_len]
    \\ DEP_REWRITE_TAC [drop_push_locals]
    \\ gvs [push_locals_def])
  \\ gvs [evaluate_exp_def, unuse_old_def, use_old_def, restore_caller_def,
          set_up_call_def, dec_clock_def, AllCaseEqs()]
  \\ simp [state_component_equality]
QED

Triviality snd_tuple:
  SND x = z ⇔ ∃y. x = (y, z)
Proof
  Cases_on ‘x’ \\ gvs []
QED

(* We can add extra ticks to the clock if we didn't timeout before *)
Theorem evaluate_exp_add_to_clock:
  (∀s env e s' r extra.
     evaluate_exp s env e = (s', r) ∧ r ≠ Rerr Rtimeout_error ⇒
     evaluate_exp (s with clock := s.clock + extra) env e =
     (s' with clock := s'.clock + extra, r)) ∧
  (∀s env es s' r extra.
     evaluate_exps s env es = (s', r) ∧ r ≠ Rerr Rtimeout_error ⇒
     evaluate_exps (s with clock := s.clock + extra) env es =
     (s' with clock := s'.clock + extra, r))
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Forall (vn, t) term’] >-
   (gvs [evaluate_exp_def, snd_tuple, PULL_EXISTS, AllCaseEqs()]
    >- (first_assum $ irule_at (Pos hd)
        \\ last_x_assum drule \\ gvs [push_local_def])
    >- (rpt strip_tac
        \\ first_x_assum drule
        \\ rpt strip_tac \\ gvs []
        \\ reverse $ last_x_assum drule \\ simp []
        >- (qexists ‘extra’ \\ gvs [push_local_def])
        >- (qexists ‘extra’ \\ gvs [push_local_def])
        \\ disch_then $ qspec_then ‘extra’ mp_tac \\ gvs [push_local_def])
    \\ rename [‘v ∈ _’]
    \\ qexists ‘v’
    \\ rpt conj_tac \\ gvs []
    >- (qx_genl_tac [‘v₁’, ‘y’] \\ disch_tac
        \\ namedCases_on ‘evaluate_exp (push_local s vn v₁) env term’ ["s₁ r"]
        \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
        >- (Cases_on ‘err’ \\ gvs [])
        \\ last_x_assum drule \\ simp []
        \\ disch_then $ qspec_then ‘extra’ mp_tac
        \\ gvs [push_local_def])
    >- (qx_genl_tac [‘v₁’, ‘y’] \\ disch_tac
        \\ namedCases_on ‘evaluate_exp (push_local s vn v₁) env term’ ["s₁ r"]
        \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
        >- (Cases_on ‘err’ \\ gvs [])
        \\ last_x_assum drule \\ simp []
        \\ disch_then $ qspec_then ‘extra’ mp_tac
        \\ gvs [push_local_def])
    \\ qx_gen_tac ‘y’
    \\ first_assum $ qspec_then ‘y’ assume_tac
    \\ namedCases_on ‘evaluate_exp (push_local s vn v) env term’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
    >- (Cases_on ‘err’ \\ gvs [])
    \\ last_x_assum drule \\ gvs []
    \\ disch_then $ qspec_then ‘extra’ mp_tac
    \\ gvs [push_local_def])
  >~ [‘Let vars body’] >-
   (gvs [evaluate_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env rhss’ ["s₁ r₁"] \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ namedCases_on ‘r₁’ ["vs", "err"] \\ gvs []
    \\ first_x_assum $ qspec_then ‘extra’ assume_tac
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp s₂’
    \\ namedCases_on ‘evaluate_exp s₂ env body’ ["s₃ r₁"] \\ gvs [Abbr ‘s₂’]
    \\ imp_res_tac evaluate_exps_len_eq
    \\ gvs [UNZIP_MAP]
    \\ ‘LENGTH vars ≤ LENGTH s₃.locals’ by
      (imp_res_tac evaluate_exp_with_clock \\ gvs [push_locals_def])
    \\ gvs [pop_locals_def, safe_drop_def, push_locals_def])
  >~ [‘FunCall’] >-
   (gvs [evaluate_exp_def, set_up_call_def, restore_caller_def,
         dec_clock_def, AllCaseEqs()])
  >~ [‘Old’] >-
   (gvs [evaluate_exp_def, use_old_def, unuse_old_def, AllCaseEqs()])
  >~ [‘ArrSel’] >-
   (gvs [evaluate_exp_def, index_array_def, AllCaseEqs()])
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
QED

(* After evaluate, only the value of locals can have changed. *)

Triviality evaluate_exp_locals:
  (∀s env e s' r.
     evaluate_exp s env e = (s', r) ⇒
     MAP FST s'.locals = MAP FST s.locals) ∧
  (∀s env es s' r.
     evaluate_exps s env es = (s', r) ⇒
     MAP FST s'.locals = MAP FST s.locals)
Proof
  rpt strip_tac
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
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

Triviality CONS_LENGTH:
  xs = x::xs' ⇒ 1 ≤ LENGTH xs
Proof
  gvs []
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
    \\ rename [‘pop_locals _ s₁’]
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ ‘1 ≤ LENGTH s₁.locals’ by (imp_res_tac CONS_LENGTH \\ gvs [])
    \\ gvs [MAP_DROP])
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
