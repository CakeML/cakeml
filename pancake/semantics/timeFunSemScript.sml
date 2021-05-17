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


Definition next_oracle_def:
  next_oracle (f:num -> input_delay) =
    λn. f (n+1)
End

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
   then SOME (st with  <| clocks   := resetClocks st.clocks clks
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
   then SOME (st with  <| clocks   := resetClocks st.clocks clks
                         ; ioAction := SOME (Output out_signal)
                         ; location := dest
                         ; waitTime := calculate_wtime st clks difs|>)
   else NONE) ∧
  (eval_term st _ _ = NONE)
End


Definition machine_bounds_def:
  machine_bounds st max m tms ⇔
    tms_conds_eval st tms ∧
    conds_eval_lt_dimword m st tms ∧
    terms_time_range m tms ∧
    input_terms_actions max tms ∧
    terms_wtimes_ffi_bound m st tms ∧
    max_clocks st.clocks m
End

Definition pick_eval_input_term_def:
  (pick_eval_input_term st i (tm::tms) =
   case tm of
   | Tm (Input in_signal) cnds clks dest difs =>
       if in_signal = i ∧
          EVERY (λcnd. evalCond st cnd) cnds
       then eval_term st (SOME i) tm
       else pick_eval_input_term st i tms
   | _ => pick_eval_input_term st i tms) ∧
  (pick_eval_input_term _ _ [] = NONE)
End

Definition pick_eval_output_term_def:
  (pick_eval_output_term st (tm::tms) =
   case tm of
   | Tm (Output out_signal) cnds clks dest difs =>
       if EVERY (λcnd. evalCond st cnd) cnds
       then (SOME out_signal, eval_term st NONE tm)
       else pick_eval_output_term st tms
   | _ => pick_eval_output_term st tms) ∧
  (pick_eval_output_term _ [] = (NONE, NONE))
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
  if 1 ≤ w ∧ w + n < m ∧
     max_clocks (delay_clocks (st.clocks) (n + 1)) m
  then SOME
       (LDelay 1 ,
        st with
           <|clocks := delay_clocks (st.clocks) 1;
             waitTime := SOME (w - 1);
             ioAction := NONE|>)
  else NONE
End


Definition eval_input_def:
  eval_input prog m n i st =
  case ALOOKUP prog st.location of
  | SOME tms =>
      if n < m ∧ machine_bounds (resetOutput st) m (m - n) tms
      then (case pick_eval_input_term (resetOutput st) i tms of
            | SOME st' => SOME (LAction (Input i), st')
            | _ => NONE)
      else NONE
  | _ => NONE
End

Definition eval_output_def:
  eval_output prog m n st =
  case ALOOKUP prog st.location of
  | SOME tms =>
      if n < m ∧ machine_bounds (resetOutput st) m (m - n) tms
      then (case pick_eval_output_term (resetOutput st) tms of
            | (SOME os, SOME st') => SOME (LAction (Output os), st')
            | _ => NONE)
      else NONE
  | _ => NONE
End


Definition eval_step_def:
  eval_step prog m n (or:num -> input_delay) st =
  case st.waitTime of
  | NONE =>
      (case or 0 of
       | Delay => eval_delay_wtime_none st m n
       | Input i => eval_input prog m n i st)
  | SOME w =>
      if w = 0
      then eval_output prog m n st
      else
        (case or 0 of
         | Delay => eval_delay_wtime_some st m n w
         | Input i =>
             if w + n < m
             then eval_input prog m n i st
             else NONE)
End

Definition set_oracle_def:
  (set_oracle (Input _) (or:num -> input_delay) = next_oracle or) ∧
  (set_oracle (Output _) or = or)
End

Definition eval_steps_def:
  (eval_steps 0 prog m n _ st =
   if n < m ∧
      (case st.waitTime of
       | SOME w => w ≠ 0
       | NONE => T)
   then SOME ([],[])
   else NONE) ∧
  (eval_steps (SUC k) prog m n or st =
   case eval_step prog m n or st of
   | SOME (lbl, st') =>
       let n' =
             case lbl of
             | LDelay d => d + n
             | LAction _ => n;
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


Theorem pick_eval_input_term_imp_pickTerm:
  ∀tms st m n i st'.
    machine_bounds (resetOutput st) m (m − n) tms ∧
    pick_eval_input_term (resetOutput st) i tms = SOME st' ⇒
    pickTerm (resetOutput st) m (m − n) (SOME i) tms st' ∧
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
      rveq >> gs [state_component_equality])
    >- (
      rewrite_tac [Once pickTerm_cases] >>
      gs [] >>
      last_x_assum (qspecl_then [‘st’, ‘m’, ‘n’, ‘i’, ‘st'’] mp_tac) >>
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
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘n’, ‘i’, ‘st'’] mp_tac) >>
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
    FULL_CASE_TAC >> gs []) >>
  rewrite_tac [Once pickTerm_cases] >>
  gs [] >>
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘n’, ‘i’, ‘st'’] mp_tac) >>
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
  ∀tms st m n os st'.
    machine_bounds (resetOutput st) m (m − n) tms ∧
    pick_eval_output_term (resetOutput st) tms = (SOME os,SOME st') ⇒
    pickTerm (resetOutput st) m (m − n) NONE tms st' ∧
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
    last_x_assum (qspecl_then [‘st’, ‘m’, ‘n’, ‘os’, ‘st'’] mp_tac) >>
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
  last_x_assum (qspecl_then [‘st’, ‘m’, ‘n’, ‘os’, ‘st'’] mp_tac) >>
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
  cases_on ‘or 0’ >> gs []
  >- (
    gs [eval_delay_wtime_none_def] >>
    rveq >>
    gs [step_cases, mkState_def] >>
    gs [state_component_equality])
  >- (
    gs [eval_input_def] >>
    FULL_CASE_TAC >> gs [] >>
    FULL_CASE_TAC >> gs [] >> rveq >> gs [] >>
    qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
    imp_res_tac pick_eval_input_term_imp_pickTerm >>
    gs [step_cases, mkState_def])
  >- (
    FULL_CASE_TAC >> gs []
    >- (
      gs [eval_output_def] >>
      every_case_tac >> rveq >> gs [] >>
      rveq >> gs [] >>
      qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
      imp_res_tac pick_eval_output_term_imp_pickTerm >>
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
    imp_res_tac pick_eval_output_term_imp_pickTerm >>
    gs [step_cases, mkState_def]) >>
  gs [eval_input_def] >>
  FULL_CASE_TAC >> gs [] >>
  FULL_CASE_TAC >> gs [] >> rveq >> gs [] >>
  qmatch_asmsub_rename_tac ‘ALOOKUP _ _ = SOME tms’ >>
  imp_res_tac pick_eval_input_term_imp_pickTerm >>
  gs [step_cases, mkState_def]
QED

(*
Theorem eval_steps_imp_steps:
  ∀k prog m n or st labels sts.
    eval_steps k prog m n or st = SOME (labels, sts) ⇒
    steps prog labels m n st sts
Proof
  Induct >> rw []
  >- fs [eval_steps_def, steps_def] >>
  gs [eval_steps_def] >>
  every_case_tac >> gs [] >> rveq >> gs [] >>
  gs [steps_def] >>
  imp_res_tac eval_step_imp_step >>
  gs [] >>
  res_tac >> gs []
QED
*)

val _ = export_theory();
