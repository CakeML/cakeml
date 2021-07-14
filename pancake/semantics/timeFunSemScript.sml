(*
  semantics for timeLang
*)

open preamble
     timeLangTheory
     timeSemTheory

val _ = new_theory "timeFunSem";


Datatype:
  input_delay = Delay
              | Input num
End

(* a well-formed program will not produce NONE in eval_term *)
(* now returns (label, state) option *)
Definition eval_term_def:
  (eval_term st (SOME i)
                (Tm (Input in_signal)
                    cnds
                    clks
                    dest
                    difs) =
   if i = in_signal ∧
      EVERY (λck. ck IN FDOM st.clocks) clks ∧
      EVERY (λ(t,c).
              ∃v. FLOOKUP st.clocks c = SOME v ∧
                  v ≤ t) difs
   then SOME (LAction (Input in_signal),
              st with  <| clocks   := resetClocks st.clocks clks
                          ; ioAction := SOME (Input in_signal)
                          ; location := dest
                          ; waitTime := calculate_wtime st clks difs|>)
   else NONE) ∧

  (eval_term st NONE
                (Tm (Output out_signal)
                    cnds
                    clks
                    dest
                    difs) =
   if EVERY (λck. ck IN FDOM st.clocks) clks ∧
      EVERY (λ(t,c).
              ∃v. FLOOKUP st.clocks c = SOME v ∧
                  v ≤ t) difs
   then SOME (LAction (Output out_signal),
              st with  <| clocks   := resetClocks st.clocks clks
                          ; ioAction := SOME (Output out_signal)
                          ; location := dest
                          ; waitTime := calculate_wtime st clks difs|>)
   else NONE) ∧
  (eval_term st _ _ = NONE)
End


Definition machine_bounds_def:
  machine_bounds st m tms ⇔
    tms_conds_eval st tms ∧
    conds_eval_lt_dimword m st tms ∧
    terms_time_range m tms ∧
    input_terms_actions m tms ∧
    terms_wtimes_ffi_bound m st tms ∧
    max_clocks st.clocks m
End

(* now returns (label, state) option *)
Definition pick_eval_input_term_def:
  (pick_eval_input_term st i m (tm::tms) =
   case tm of
   | Tm (Input in_signal) cnds clks dest difs =>
       if in_signal = i ∧
          EVERY (λcnd. evalCond st cnd) cnds
       then eval_term st (SOME i) tm
       else pick_eval_input_term st i m tms
   | _ => pick_eval_input_term st i m tms) ∧
  (pick_eval_input_term st i m [] =
   if i + 1 < m then SOME (LPanic (PanicInput i), st)
   else NONE)
End

Definition pick_eval_output_term_def:
  (pick_eval_output_term st (tm::tms) =
   case tm of
   | Tm (Output out_signal) cnds clks dest difs =>
       if EVERY (λcnd. evalCond st cnd) cnds
       then eval_term st NONE tm
       else pick_eval_output_term st tms
   | _ => pick_eval_output_term st tms) ∧
  (pick_eval_output_term st [] = SOME (LPanic PanicTimeout, st))
End


Definition eval_input_def:
  eval_input prog m n i st =
  case ALOOKUP prog st.location of
  | SOME tms =>
      if n < m ∧ machine_bounds (resetOutput st) m tms
      then pick_eval_input_term (resetOutput st) i m tms
      else NONE
  | _ => NONE
End

Definition eval_output_def:
  eval_output prog m n st =
  case ALOOKUP prog st.location of
  | SOME tms =>
      if n < m ∧ machine_bounds (resetOutput st) m tms
      then pick_eval_output_term (resetOutput st) tms
      else NONE
  | _ => NONE
End


Definition eval_delay_wtime_none_def:
  eval_delay_wtime_none st m n =
  if n + 1 < m ∧
     max_clocks (delay_clocks (st.clocks) (n + 1)) m
  then SOME
       (LDelay 1 ,
        st with
           <|clocks := delay_clocks (st.clocks) 1;
             ioAction := NONE|>)
  else NONE
End

Definition eval_delay_wtime_some_def:
  eval_delay_wtime_some st m n w =
  if 1 ≤ w ∧ w < m ∧ n + 1 < m ∧
     max_clocks (delay_clocks (st.clocks) (n + 1)) m
  then SOME
       (LDelay 1 ,
        st with
           <|clocks := delay_clocks (st.clocks) 1;
             waitTime := SOME (w - 1);
             ioAction := NONE|>)
  else NONE
End

(* rearrange the check on system time *)
Definition eval_step_def:
  eval_step prog m n (or:input_delay) st =
  case st.waitTime of
  | NONE =>
      (case or of
       | Delay => eval_delay_wtime_none st m n
       | Input i => eval_input prog m n i st)
  | SOME w =>
      if w = 0
      then eval_output prog m n st
      else
        (case or of
         | Delay => eval_delay_wtime_some st m n w
         | Input i =>
             if w ≠ 0 ∧ w < m
             then eval_input prog m n i st
             else NONE)
End


Definition next_oracle_def:
  next_oracle (f:num -> input_delay) =
    λn. f (n+1)
End

Definition set_oracle_def:
  (set_oracle (Input _) (or:num -> input_delay) = next_oracle or) ∧
  (set_oracle (Output _) or = or)
End

(*
Definition eval_steps_def:
  (eval_steps 0 prog m n _ st =
   if n < m ∧
      (case st.waitTime of
       | SOME w => w < m
       | NONE => T)
   then SOME ([],[])
   else NONE) ∧
  (eval_steps (SUC k) prog m n or st =
   case eval_step prog m n (or 0) st of
   | SOME (lbl, st') =>
       let n' =
             case lbl of
             | LDelay d => d + n
             | _ => n;
           noracle =
             case lbl of
             | LDelay _ => next_oracle or
             | LAction act => set_oracle act or
       in
         (case eval_steps k prog m n' noracle st' of
          | NONE => NONE
          | SOME (lbls', sts') => SOME (lbl::lbls', st'::sts'))
   | NONE => NONE)
End
*)


Definition eval_steps_def:
  (eval_steps 0 _ _ _ _ st = SOME ([],[])) ∧
  (eval_steps (SUC k) prog m n or st =
   if m - 1 <= n then SOME ([], [])
   else
     (case eval_step prog m n (or 0) st of
      | SOME (lbl, st') =>
          let n' =
              case lbl of
              | LDelay d => d + n
              | _ => n;
              noracle =
              case lbl of
              | LDelay _ => next_oracle or
              | LAction act => set_oracle act or
       in
         (case eval_steps k prog m n' noracle st' of
          | NONE => NONE
          | SOME (lbls', sts') => SOME (lbl::lbls', st'::sts'))
         | NONE => NONE))
End

(*
Definition eval_steps_def:
  (eval_steps 0 _ _ _ _ st = SOME ([],[])) ∧
  (eval_steps (SUC k) prog m n or st =
   case eval_step prog m n (or 0) st of
   | SOME (lbl, st') =>
       let n' =
           case lbl of
           | LDelay d => d + n
           | _ => n;
           noracle =
           case lbl of
           | LDelay _ => next_oracle or
           | LAction act => set_oracle act or
       in
         (case eval_steps k prog m n' noracle st' of
          | NONE => NONE
          | SOME (lbls', sts') => SOME (lbl::lbls', st'::sts'))
         | NONE => NONE)
End
*)

Theorem label_from_pick_eval_input_term:
  ∀tms i st lbl st' m.
    pick_eval_input_term st i m tms = SOME (lbl,st') ⇒
    lbl = LAction (Input i) ∨
    lbl = LPanic (PanicInput i)
Proof
  Induct >> rw [] >>
  gvs [pick_eval_input_term_def] >>
  every_case_tac >> gvs [eval_term_def] >>
  res_tac >> gvs []
QED

Theorem label_from_pick_eval_output_term:
  ∀tms st lbl st'.
    pick_eval_output_term st tms = SOME (lbl,st') ⇒
    (∃os. lbl = LAction (Output os)) ∨
    lbl = LPanic PanicTimeout
Proof
  Induct >> rw [] >>
  gvs [pick_eval_output_term_def] >>
  every_case_tac >> gvs [eval_term_def] >>
  res_tac >> gvs []
QED


Theorem pick_eval_input_term_imp_pickTerm:
  ∀tms st m i st'.
    machine_bounds (resetOutput st) m tms ∧
    pick_eval_input_term (resetOutput st) i m tms =
    SOME (LAction (Input i), st') ⇒
    pickTerm (resetOutput st) m (SOME i) tms st' (LAction (Input i)) ∧
    st'.ioAction = SOME (Input i)
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  gs []
  >- gs [pick_eval_input_term_def] >>
  gs [pick_eval_input_term_def] >>
  cases_on ‘h’ >> gs [] >>
  cases_on ‘i'’ >> gs []
  >- (
    FULL_CASE_TAC >> gs []
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      gs [machine_bounds_def] >>
      gs [eval_term_def, evalTerm_cases] >>
      rveq >> gs [state_component_equality]) >>
    cheat
    (*
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
            terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
            terms_in_signals_def]) >>
      strip_tac >>
      gs [machine_bounds_def, terms_time_range_def,
          conds_eval_lt_dimword_def, input_terms_actions_def,
          terms_in_signals_def]) >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [] >>
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
    impl_tac
    >- (
      gs [] >>
      gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
          terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
          terms_in_signals_def]) >>
    strip_tac >>
    gs [machine_bounds_def, terms_time_range_def,
        conds_eval_lt_dimword_def, input_terms_actions_def,
        terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    disj2_tac >>
    disj1_tac >>
    rw [] >>
    res_tac >> gs []  >>
    FULL_CASE_TAC >> gs []*)) >>
  rewrite_tac [Once pickTerm_cases] >>
  gs [] >>
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
  impl_tac
  >- (
    gs [] >>
    gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
        terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
        terms_in_signals_def]) >>
  strip_tac >>
  gs [machine_bounds_def, terms_time_range_def,
      conds_eval_lt_dimword_def, input_terms_actions_def,
      terms_in_signals_def]
QED

Theorem pick_eval_output_term_imp_pickTerm:
  ∀tms st m os st'.
    machine_bounds (resetOutput st) m tms ∧
    pick_eval_output_term (resetOutput st) tms =
    SOME (LAction (Output os),st') ⇒
    pickTerm (resetOutput st) m NONE tms st' (LAction (Output os)) ∧
    st'.ioAction = SOME (Output os)
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  gs []
  >- gs [pick_eval_output_term_def] >>
  gs [pick_eval_output_term_def] >>
  cases_on ‘h’ >> gs [] >>
  reverse (cases_on ‘i’) >> gs []
  >- (
    FULL_CASE_TAC >> gs [] >> rveq >> gs []
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      gs [machine_bounds_def, terms_time_range_def,
          conds_eval_lt_dimword_def, input_terms_actions_def,
          terms_in_signals_def] >>
      gs [eval_term_def, evalTerm_cases] >>
      rveq >> gs [state_component_equality]) >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [] >>
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘os’, ‘st'’] mp_tac) >>
    impl_tac
    >- (
      gs [] >>
      gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
          terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
          terms_in_signals_def]) >>
    strip_tac >>
    gs [machine_bounds_def, terms_time_range_def,
        conds_eval_lt_dimword_def, input_terms_actions_def,
        terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    disj2_tac >>
    rw [] >>
    res_tac >> gs []  >>
    FULL_CASE_TAC >> gs []) >>
  rewrite_tac [Once pickTerm_cases] >>
  gs [] >>
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘os’, ‘st'’] mp_tac) >>
  impl_tac
  >- (
    gs [] >>
    gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
        terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
        terms_in_signals_def]) >>
  strip_tac >>
  gs [machine_bounds_def, terms_time_range_def,
      conds_eval_lt_dimword_def, input_terms_actions_def,
      terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
      timeLangTheory.termConditions_def]
QED

Theorem pick_input_term_panic_sts_eq:
  ∀tms st m i st'.
    pick_eval_input_term st i m tms =
    SOME (LPanic (PanicInput i), st') ⇒
    st = st'
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  gs [pick_eval_input_term_def] >>
  every_case_tac >> gvs [eval_term_def] >>
  res_tac >> gvs []
QED

Theorem pick_eval_input_term_panic_imp_pickTerm:
  ∀tms st m i st'.
    machine_bounds (resetOutput st) m tms ∧
    pick_eval_input_term (resetOutput st) i m tms =
    SOME (LPanic (PanicInput i), st') ⇒
    pickTerm (resetOutput st) m (SOME i) tms st' (LPanic (PanicInput i))
Proof
  (*
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  gs []
  >- (
    gs [pick_eval_input_term_def] >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [machine_bounds_def]) >>
  gs [pick_eval_input_term_def] >>
  cases_on ‘h’ >> gs [] >>
  cases_on ‘i'’ >> gs []
  >- (
    FULL_CASE_TAC >> gs []
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      gvs [machine_bounds_def] >>
      gs [eval_term_def, evalTerm_cases] >>
      rveq >> gs [state_component_equality])
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
            terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
            terms_in_signals_def]) >>
      strip_tac >>
      gs [machine_bounds_def, terms_time_range_def,
          conds_eval_lt_dimword_def, input_terms_actions_def,
          terms_in_signals_def]) >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [] >>
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
    impl_tac
    >- (
      gs [] >>
      gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
          terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
          terms_in_signals_def]) >>
    strip_tac >>
    gs [machine_bounds_def, terms_time_range_def,
        conds_eval_lt_dimword_def, input_terms_actions_def,
        terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    disj1_tac >>
    rw [] >>
    res_tac >> gs []  >>
    FULL_CASE_TAC >> gs []) >>
  rewrite_tac [Once pickTerm_cases] >>
  gs [] >>
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘i’, ‘st'’] mp_tac) >>
  impl_tac
  >- (
    gs [] >>
    gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
        terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
        terms_in_signals_def]) >>
  strip_tac >>
  gs [machine_bounds_def, terms_time_range_def,
      conds_eval_lt_dimword_def, input_terms_actions_def,
      terms_in_signals_def] *)
  cheat
QED

Theorem pick_eval_output_term_panic_imp_pickTerm:
  ∀tms st m st'.
    machine_bounds (resetOutput st) m tms ∧
    pick_eval_output_term (resetOutput st) tms =
    SOME (LPanic PanicTimeout, st') ⇒
    pickTerm (resetOutput st) m NONE tms st' (LPanic PanicTimeout)
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  gs []
  >- (
    gs [pick_eval_output_term_def] >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [machine_bounds_def]) >>
  gs [pick_eval_output_term_def] >>
  cases_on ‘h’ >> gs [] >>
  reverse (cases_on ‘i’) >> gs []
  >- (
    FULL_CASE_TAC >> gs [] >> rveq >> gs []
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      gs [machine_bounds_def, terms_time_range_def,
          conds_eval_lt_dimword_def, input_terms_actions_def,
          terms_in_signals_def] >>
      gs [eval_term_def, evalTerm_cases] >>
      rveq >> gs [state_component_equality]) >>
    rewrite_tac [Once pickTerm_cases] >>
    gs [] >>
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘st'’] mp_tac) >>
    impl_tac
    >- (
      gs [] >>
      gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
          terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
          terms_in_signals_def]) >>
    strip_tac >>
    gs [machine_bounds_def, terms_time_range_def,
        conds_eval_lt_dimword_def, input_terms_actions_def,
        terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    rw [] >>
    res_tac >> gs []  >>
    FULL_CASE_TAC >> gs []) >>
  rewrite_tac [Once pickTerm_cases] >>
  gs [] >>
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘st'’] mp_tac) >>
  impl_tac
  >- (
    gs [] >>
    gs [machine_bounds_def, tms_conds_eval_def, conds_eval_lt_dimword_def,
        terms_time_range_def, input_terms_actions_def, terms_wtimes_ffi_bound_def,
        terms_in_signals_def]) >>
  strip_tac >>
  gs [machine_bounds_def, terms_time_range_def,
      conds_eval_lt_dimword_def, input_terms_actions_def,
      terms_in_signals_def, tms_conds_eval_def,  tm_conds_eval_def,
      timeLangTheory.termConditions_def]
QED


Theorem eval_step_imp_step:
  eval_step prog m n or st = SOME (label, st') ⇒
  step prog label m n st st'
Proof
  rw [] >>
  fs [eval_step_def] >>
  cases_on ‘st.waitTime’ >> gs [] >>
  cases_on ‘or’ >> gs []
  >- (
    gs [eval_delay_wtime_none_def] >>
    rveq >>
    gs [step_cases, mkState_def] >>
    gs [state_component_equality])
  >- (
    gs [eval_input_def] >>
    FULL_CASE_TAC >> gvs [] >>
    qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
    qmatch_asmsub_rename_tac ‘pick_eval_input_term _ i _ _ = _’ >>
    drule label_from_pick_eval_input_term >>
    strip_tac >> gvs []
    >- (
      imp_res_tac pick_eval_input_term_imp_pickTerm >>
      gs [step_cases, mkState_def]) >>
    drule_all pick_eval_input_term_panic_imp_pickTerm >>
    gs [step_cases, mkState_def])
  >- (
    FULL_CASE_TAC >> gs []
    >- (
      gs [eval_output_def] >>
      every_case_tac >> rveq >> gs [] >>
      rveq >> gs [] >>
      qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
      drule label_from_pick_eval_output_term >>
      strip_tac >> gvs []
      >- (
        imp_res_tac pick_eval_output_term_imp_pickTerm >>
        gs [step_cases, mkState_def]) >>
      drule_all pick_eval_output_term_panic_imp_pickTerm >>
      gs [step_cases, mkState_def]) >>
    gs [eval_delay_wtime_some_def] >>
    rveq >>
    gs [step_cases, mkState_def] >>
    gs [state_component_equality]) >>
  cases_on ‘x = 0’ >> gs []
  >- (
    gs [eval_output_def] >>
    every_case_tac >> rveq >> gs [] >>
    rveq >> gs [] >>
    qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
    drule label_from_pick_eval_output_term >>
    strip_tac >> gvs []
    >- (
      imp_res_tac pick_eval_output_term_imp_pickTerm >>
      gs [step_cases, mkState_def]) >>
    drule_all pick_eval_output_term_panic_imp_pickTerm >>
    gs [step_cases, mkState_def]) >>
  gs [eval_input_def] >>
  FULL_CASE_TAC >> gs [] >> rveq >> gs [] >>
  qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
  qmatch_asmsub_rename_tac ‘pick_eval_input_term _ i _ _ = _’ >>
  drule label_from_pick_eval_input_term >>
  strip_tac >> gvs []
  >- (
    imp_res_tac pick_eval_input_term_imp_pickTerm >>
    gs [step_cases, mkState_def]) >>
  drule_all pick_eval_input_term_panic_imp_pickTerm >>
  gs [step_cases, mkState_def]
QED


Theorem eval_steps_imp_steps:
  ∀k prog m n or st labels sts.
    eval_steps k prog m n or st = SOME (labels, sts) ⇒
    steps prog labels m n st sts
Proof
  Induct >> rw []
  >- fs [eval_steps_def, steps_def] >>
  gs [eval_steps_def] >>
  every_case_tac >> gvs [] >>
  TRY (cases_on ‘p’) >> gvs [] >>
  gs [steps_def] >>
  imp_res_tac eval_step_imp_step >>
  gs [] >>
  res_tac >> gs []
QED

val _ = export_theory();
