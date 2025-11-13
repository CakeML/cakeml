(*
  Properties of Dafny's functional big-step semantics.
*)
Theory dafny_evaluateProps
Ancestors
  dafny_semanticPrimitives
  dafnyProps
  dafny_evaluate
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
          unuse_prev_def, use_prev_def, unset_prev_def, set_prev_def,
          unuse_prev_heap_def, use_prev_heap_def,
          unuse_old_heap_def, use_old_heap_def,
          set_up_call_def, dec_clock_def, AllCaseEqs()]
  \\ simp [state_component_equality]
QED

(* After evaluate, only the value of locals can have changed. *)

Theorem evaluate_exp_locals[local]:
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

(* todo move to dafnyProp *)
Theorem update_local_aux_locals:
  ∀locals var val locals'.
    update_local_aux locals var val = SOME locals' ⇒
    MAP FST locals = MAP FST locals'
Proof
  Induct_on ‘locals’ \\ rpt strip_tac
  \\ gvs [update_local_aux_def] \\ PairCases_on ‘h’
  \\ gvs [update_local_aux_def, AllCaseEqs()] \\ res_tac
QED

(* todo move to dafnyProp *)
Theorem update_local_locals[local]:
  ∀s var val s'.
    update_local s var val = SOME s' ⇒
    MAP FST s'.locals = MAP FST s.locals
Proof
  rpt strip_tac
  \\ gvs [update_local_def, AllCaseEqs()]
  \\ imp_res_tac update_local_aux_locals \\ gvs []
QED

(* todo move to dafnyProp *)
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

(* todo move to dafnyProp *)
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

Theorem CONS_LENGTH[local]:
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
  \\ gvs [evaluate_stmt_def, dec_clock_def, restore_caller_def, set_up_call_def,
          AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_locals
  \\ imp_res_tac assign_values_locals
  \\ imp_res_tac evaluate_rhs_exps_locals \\ gvs []
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
  >~ [‘ForallHeap mods term’] >-
   (gvs [evaluate_exp_def, snd_tuple, eval_forall_def,
         PULL_EXISTS, AllCaseEqs()]
    >- (first_assum $ irule_at (Pos hd)
        \\ last_x_assum drule \\ gvs [push_local_def])
    >- (rpt strip_tac
        \\ first_x_assum drule
        \\ rpt strip_tac \\ gvs []
        \\ reverse $ last_x_assum drule \\ simp []
        >- (qexists ‘extra’ \\ gvs [push_local_def])
        >- (qexists ‘extra’ \\ gvs [push_local_def])
        \\ disch_then $ qspec_then ‘extra’ mp_tac \\ gvs [push_local_def])
    \\ rename [‘hs ∈ _’]
    \\ qexists ‘hs’
    \\ rpt conj_tac \\ gvs []
    >- (qx_genl_tac [‘hs₁’, ‘y’] \\ disch_tac
        \\ namedCases_on ‘evaluate_exp (s' with heap := hs₁) env term’ ["s₁ r"]
        \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
        >- (Cases_on ‘err’ \\ gvs [])
        \\ last_x_assum drule \\ simp []
        \\ disch_then $ qspec_then ‘extra’ mp_tac
        \\ gvs [])
    >- (qx_genl_tac [‘hs₁’, ‘y’] \\ disch_tac
        \\ namedCases_on ‘evaluate_exp (s' with heap := hs₁) env term’ ["s₁ r"]
        \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
        >- (Cases_on ‘err’ \\ gvs [])
        \\ last_x_assum drule \\ simp []
        \\ disch_then $ qspec_then ‘extra’ mp_tac
        \\ gvs [push_local_def])
    \\ qx_gen_tac ‘y’
    \\ first_assum $ qspec_then ‘y’ assume_tac
    \\ namedCases_on ‘evaluate_exp (s' with heap := hs) env term’ ["s₁ r"]
    \\ reverse $ namedCases_on ‘r’ ["v₂", "err"]
    >- (Cases_on ‘err’ \\ gvs [])
    \\ last_x_assum drule \\ gvs []
    \\ disch_then $ qspec_then ‘extra’ mp_tac
    \\ gvs [push_local_def])
  >~ [‘Forall (vn, t) term’] >-
   (gvs [evaluate_exp_def, snd_tuple, eval_forall_def,
         PULL_EXISTS, AllCaseEqs()]
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
  >~ [‘OldHeap’] >-
   (gvs [evaluate_exp_def, use_old_heap_def, unuse_old_heap_def, AllCaseEqs()])
  >~ [‘Prev’] >-
   (gvs [evaluate_exp_def, use_prev_def, unuse_prev_def, AllCaseEqs()])
  >~ [‘PrevHeap’] >-
   (gvs [evaluate_exp_def, use_prev_heap_def, unuse_prev_heap_def, AllCaseEqs()])
  >~ [‘SetPrev’] >-
   (gvs [evaluate_exp_def, set_prev_def, unset_prev_def, AllCaseEqs()])
  >~ [‘ArrSel’] >-
   (gvs [evaluate_exp_def, index_array_def, AllCaseEqs()])
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
QED

Theorem assign_value_add_to_clock:
  ∀s env lhs val s' r extra.
    assign_value s env lhs val = (s', r) ∧
    r ≠ Rstop (Serr Rtimeout_error) ⇒
    assign_value (s with clock := s.clock + extra) env lhs val =
    (s' with clock := s'.clock + extra, r)
Proof
  Cases_on ‘lhs’ \\ rpt strip_tac
  >~ [‘VarLhs’] >-
   (gvs [assign_value_def, CaseEq "option"]
    >- (irule update_local_none_with_clock \\ simp [])
    \\ imp_res_tac update_local_some_clock_eq \\ gvs []
    \\ irule update_local_some_with_clock \\ simp [])
  >~ [‘ArrSelLhs arr idx’] >-
   (gvs [assign_value_def]
    \\ namedCases_on ‘evaluate_exp s env arr’ ["s₁ r₁"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
    \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ simp []
    \\ namedCases_on ‘r₁’ ["arr_v", "err"] \\ gvs []
    \\ namedCases_on ‘evaluate_exp (s with clock := ck) env idx’
         ["s₂ r₂"]
    \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ gvs []
    \\ ‘r₂ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
    \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ simp []
    \\ namedCases_on ‘r₂’ ["idx_v", "err"] \\ gvs []
    \\ gvs [AllCaseEqs()]
    >- (drule update_array_none_with_clock \\ simp [])
    \\ imp_res_tac update_array_some_clock_eq
    \\ drule update_array_some_with_clock \\ gvs [])
QED

Theorem assign_values_add_to_clock:
  ∀s env lhss vals s' r extra.
    assign_values s env lhss vals = (s', r) ∧
    r ≠ Rstop (Serr Rtimeout_error) ⇒
    assign_values (s with clock := s.clock + extra) env lhss vals =
    (s' with clock := s'.clock + extra, r)
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘vals’ \\ rpt strip_tac
  \\ gvs [assign_values_def, AllCaseEqs()]
  \\ imp_res_tac assign_value_add_to_clock \\ gvs []
QED

Theorem evaluate_rhs_exp_add_to_clock:
  ∀s env e s' r extra.
    evaluate_rhs_exp s env e = (s', r) ∧ r ≠ Rerr Rtimeout_error ⇒
    evaluate_rhs_exp (s with clock := s.clock + extra) env e =
    (s' with clock := s'.clock + extra, r)
Proof
  Induct_on ‘e’ \\ rpt strip_tac
  >~ [‘ExpRhs e’] >-
   (gvs [evaluate_rhs_exp_def]
    \\ imp_res_tac (cj 1 evaluate_exp_add_to_clock) \\ gvs [])
  >~ [‘ArrAlloc len init’] >-
   (gvs [evaluate_rhs_exp_def]
    \\ namedCases_on ‘evaluate_exp s env len’ ["s₁ r₁"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
    \\ drule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ simp []
    \\ namedCases_on ‘r₁’ ["len_v", "err"] \\ gvs []
    \\ namedCases_on ‘evaluate_exp (s with clock := ck) env init’ ["s₂ r₂"]
    \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ gvs []
    \\ ‘r₂ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
    \\ drule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ simp []
    \\ namedCases_on ‘r₂’ ["init_v", "err"] \\ gvs []
    \\ gvs [AllCaseEqs()]
    >- (drule alloc_array_none_with_clock \\ simp [])
    \\ imp_res_tac alloc_array_some_clock_eq
    \\ drule alloc_array_some_with_clock \\ simp [])
QED

Theorem evaluate_rhs_exps_add_to_clock:
  ∀s env es s' r extra.
    evaluate_rhs_exps s env es = (s', r) ∧ r ≠ Rerr Rtimeout_error ⇒
    evaluate_rhs_exps (s with clock := s.clock + extra) env es =
    (s' with clock := s'.clock + extra, r)
Proof
  Induct_on ‘es’ \\ gvs [evaluate_rhs_exps_def]
  \\ qx_genl_tac [‘e’, ‘s’, ‘env’, ‘s'’, ‘r’, ‘extra’]
  \\ rpt strip_tac
  \\ namedCases_on ‘evaluate_rhs_exp s env e’ ["s₁ r₁"] \\ gvs []
  \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
  \\ drule evaluate_rhs_exp_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘extra’ assume_tac
  \\ Cases_on ‘r₁’ \\ gvs []
  \\ namedCases_on ‘evaluate_rhs_exps s₁ env es’ ["s₂ r₂"] \\ gvs []
  \\ ‘r₂ ≠ Rerr Rtimeout_error’ by (gvs [AllCaseEqs()])
  \\ last_x_assum drule \\ simp []
  \\ Cases_on ‘r₂’ \\ gvs []
QED

Theorem evaluate_stmt_add_to_clock:
  ∀s env stmt s' r extra.
    evaluate_stmt s env stmt = (s', r) ∧ r ≠ Rstop (Serr Rtimeout_error) ⇒
    evaluate_stmt (s with clock := s.clock + extra) env stmt =
    (s' with clock := s'.clock + extra, r)
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r₁"] \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule_all (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ gvs [AllCaseEqs()])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_stmt s env stmt₁’ ["s₁ r₁"] \\ gvs []
    \\ Cases_on ‘r₁’ \\ gvs [])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_exp s env tst’ ["s₂ r₁"] \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (Cases_on ‘r₁’ \\ gvs [])
    \\ drule_all (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then kall_tac
    \\ namedCases_on ‘r₁’ ["tst_v", "err"] \\ gvs []
    \\ gvs [CaseEq "option"])
  >~ [‘Dec local stmt’] >-
   (gvs [evaluate_stmt_def]
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt s₁’
    \\ namedCases_on ‘evaluate_stmt s₁ env stmt’ ["s₂ r₁"] \\ gvs []
    \\ simp [Abbr ‘s₁’]
    \\ ‘s₂.locals ≠ []’ by
      (spose_not_then assume_tac
       \\ imp_res_tac evaluate_stmt_locals
       \\ gvs [declare_local_def])
    \\ imp_res_tac pop_local_some \\ gvs []
    \\ last_x_assum $ qspec_then ‘extra’ assume_tac
    \\ gvs [declare_local_with_clock]
    \\ imp_res_tac pop_locals_some_clock
    \\ simp [state_component_equality]
    \\ imp_res_tac pop_locals_clock_eq \\ simp [])
  >~ [‘Assign ass’] >-
   (gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_rhs_exps s env (MAP SND ass)’ ["s₁ r₁"] \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (Cases_on ‘r₁’ \\ gvs [])
    \\ dxrule evaluate_rhs_exps_add_to_clock \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ simp []
    \\ namedCases_on ‘r₁’ ["vals", "err"] \\ gvs []
    \\ dxrule assign_values_add_to_clock \\ simp [])
  >~ [‘While grd invs decrs mods body’] >-
   (gvs [evaluate_stmt_def]
    \\ Cases_on ‘s.clock = 0’ \\ gvs []
    \\ gvs [dec_clock_def]
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp s₁’
    \\ namedCases_on ‘evaluate_exp s₁ env grd’ ["s₂ r₁"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs [Abbr ‘s₁’]
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (Cases_on ‘r₁’ \\ gvs [])
    \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac
    \\ namedCases_on ‘r₁’ ["grd_v", "err"] \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ namedCases_on ‘evaluate_stmt (s with clock := ck) env body’ ["s₃ r₂"]
    \\ gvs []
    \\ ‘r₂ ≠ Rstop (Serr Rtimeout_error)’ by (Cases_on ‘r₂’ \\ gvs [])
    \\ fs []
    \\ Cases_on ‘r₂’ \\ gvs [])
  >~ [‘Print e t’] >-
   (gvs [evaluate_stmt_def]
    \\ namedCases_on ‘evaluate_exp s env e’ ["s₁ r₁"] \\ gvs []
    \\ drule (cj 1 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (Cases_on ‘r₁’ \\ gvs [])
    \\ dxrule (cj 1 evaluate_exp_add_to_clock)
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["v", "err"] \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  >~ [‘MetCall lhss name args’] >-
   (gvs [evaluate_stmt_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "mem₁"] \\ gvs []
    \\ Cases_on ‘mem₁’ \\ gvs []
    \\ rename [‘Method name ins _ _ _ _ outs _ body’]
    \\ namedCases_on ‘evaluate_exps s env args’ ["s₁ r₁"] \\ gvs []
    \\ drule (cj 2 evaluate_exp_with_clock)
    \\ disch_then $ qx_choose_then ‘ck’ assume_tac \\ gvs []
    \\ ‘r₁ ≠ Rerr Rtimeout_error’ by (Cases_on ‘r₁’ \\ gvs [])
    \\ dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
    \\ disch_then $ qspec_then ‘extra’ assume_tac \\ gvs []
    \\ namedCases_on ‘r₁’ ["in_vs", "err"] \\ gvs []
    \\ namedCases_on
         ‘set_up_call (s with clock := ck) (MAP FST ins) in_vs (MAP FST outs)’
         ["", "s₂"]
    \\ gvs []
    >- (drule set_up_call_none_with_clock \\ simp [])
    \\ drule set_up_call_clock_eq
    \\ disch_tac \\ gvs []
    \\ dxrule set_up_call_some_with_clock
    \\ disch_then $ qspec_then ‘extra + s₂.clock’ assume_tac \\ gvs []
    \\ Cases_on ‘s₂.clock = 0’ \\ gvs []
    \\ gvs [dec_clock_def]
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt s₂'’
    \\ namedCases_on ‘evaluate_stmt s₂' env body’ ["s₃ r₃"]
    \\ gvs [Abbr ‘s₂'’]
    \\ ‘r₃ ≠ Rstop (Serr Rtimeout_error)’ by (gvs [AllCaseEqs()]) \\ fs []
    \\ namedCases_on ‘r₃’ ["", "stp"] \\ gvs []
    \\ gvs [restore_caller_cur_with_clock, restore_caller_prev_with_clock]
    \\ reverse $ Cases_on ‘stp’ \\ gvs []
    \\ namedCases_on ‘OPT_MMAP (read_local s₃.locals) (MAP FST outs)’
        ["", "out_vs"]
    \\ gvs []
    \\ IF_CASES_TAC \\ gvs []
    \\ drule assign_values_add_to_clock \\ simp [])
  >~ [‘Return’] >-
   (gvs [evaluate_stmt_def])
QED

(* {locals,heap}_{old,prev} is preserved *)

Theorem assign_value_Rcont_const:
  assign_value st env lhs v = (st', Rcont) ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
  st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  disch_tac
  \\ Cases_on ‘lhs’
  \\ gvs [assign_value_def, update_local_def, update_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

Theorem assign_values_Rcont_const:
  ∀lhss vs st env st'.
    assign_values st env lhss vs = (st', Rcont) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
    st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  Induct \\ namedCases_on ‘vs’ ["", "v vs₁"]
  \\ simp [assign_values_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac assign_value_Rcont_const
  \\ res_tac \\ gvs []
QED

Theorem evaluate_rhs_exp_Rval_const:
  evaluate_rhs_exp st env rhs = (st', Rval v) ⇒
  st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
  st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  disch_tac
  \\ Cases_on ‘rhs’
  \\ gvs [evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs()]
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

Theorem evaluate_rhs_exps_Rval_const:
  ∀rhss st st' env vs.
    evaluate_rhs_exps st env rhss = (st', Rval vs) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
    st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  Induct \\ gvs [evaluate_rhs_exps_def]
  \\ rpt gen_tac \\ disch_tac
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ imp_res_tac evaluate_rhs_exp_Rval_const \\ gvs []
QED

Theorem evaluate_stmt_Rcont_const:
  ∀st env stmt st'.
    evaluate_stmt st env stmt = (st', Rcont) ⇒
    st'.locals_old = st.locals_old ∧ st'.heap_old = st.heap_old ∧
    st'.locals_prev = st.locals_prev ∧ st'.heap_prev = st.heap_prev
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_tac)
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ res_tac \\ gvs [])
  >~ [‘If grd thn els’] >-
   (strip_tac
    \\ gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ gvs [oneline do_cond_def, AllCaseEqs()]
    \\ res_tac \\ gvs [])
  >~ [‘Dec local scope’] >-
   (gvs [evaluate_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [pop_locals_def, safe_drop_def, declare_local_def, AllCaseEqs()]
    \\ last_x_assum drule \\ gvs [])
  >~ [‘Assign ass’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_rhs_exps_Rval_const
    \\ imp_res_tac assign_values_Rcont_const \\ gvs [])
  >~ [‘While grd invs decrs mods body’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs [dec_clock_def])
  >~ [‘Print e t’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock
    \\ gvs [])
  >~ [‘MetCall lhss name args’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
    \\ imp_res_tac assign_values_Rcont_const \\ gvs []
    \\ gvs [restore_caller_def])
  >~ [‘Return’] >-
   (gvs [evaluate_stmt_def])
QED

Theorem evaluate_exp_old_Rval_eq:
  evaluate_exp st₁ env (Old e) = (st₁', Rval v) ∧
  st₁.locals_old = st.locals_old ∧ st₁.heap_old = st.heap_old ∧
  st₁.locals_prev = st.locals_prev ∧ st₁.heap_prev = st.heap_prev ⇒
  ∃ck st'. evaluate_exp (st with clock := ck) env (Old e) = (st', Rval v)
Proof
  rpt strip_tac
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
  \\ qexists ‘st₁.clock’
  \\ ‘use_old st₁ =
      use_old (st with clock := st₁.clock)’ by
    (gvs [use_old_def, state_component_equality])
  \\ gvs []
QED
