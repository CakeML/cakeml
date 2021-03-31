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


Definition eval_pick_term_def:
  (eval_pick_term st i (tm::tms) =
   case tm of
   | Tm (Input in_signal) cnds clks dest difs =>
       if in_signal = i ∧ EVERY (λcnd. evalCond st cnd) cnds
       then eval_term st (SOME i) tm
       else eval_pick_term st i tms
   | _ => eval_pick_term st i tms) ∧
  (eval_pick_term _ _ [] = NONE)
End


Definition machine_bounds_def:
  machine_bounds st max m tms ⇔
    conds_eval_lt_dimword m st tms ∧
    terms_time_range m tms ∧
    input_terms_actions max tms ∧
    terms_wtimes_ffi_bound m st tms ∧
    max_clocks st.clocks m
End


Definition eval_delay_def:
  eval_delay st =
  (LDelay 1 ,
   st with
      <|clocks := delay_clocks (st.clocks) 1;
        ioAction := NONE|>)
End

Definition eval_input_def:
  eval_input prog m n i st =
  case ALOOKUP prog st.location of
  | SOME tms =>
      if machine_bounds st m (m - n) tms
      then (case eval_pick_term st i tms of
            | SOME st' => SOME (LAction (Input i), st')
            | _ => NONE)
      else NONE
  | _ => NONE
End


Definition eval_step_def:
  eval_step prog m n or orn st =
  case st.waitTime of
  | NONE =>
      (case or orn of
       | Delay => SOME (eval_delay st)
       | Input i => eval_input prog m n i st)
  | SOME w =>
      if w = 0
      then (case ALOOKUP prog st.location of
            | SOME tms =>
                if machine_bounds st m (m - n) tms
                then SOME (LAction (Output ARB), ARB)
                else NONE
            | _ => NONE)
      else
        (case or orn of
         | Delay => SOME (eval_delay st)
         | Input i => eval_input prog m n i st)
End







(*
 step_eval s or = SOME (s',label) ==>
  step label s s'
*)


(*
Plan:
  - define new alt version of steps that separates input from output
  - require that steps_eval is total
  step_eval s or = SOME (s',labels)
  step_eval s or = SOME (s',label) ==>
  step label s s'
  or is an oracle that answers the question: is there an input, is there delay?
  the type of or is something like a sequence of optional inputs,
  where SOME i means input i now and NONE means a delay of length 1
    : num -> num option
  perhaps num option is not descriptive enough, how about:
Datatype:
  input_or_delay = Delay (* always one in length *) | Input num
End
  steps_eval k s or -- runs step_eval for k iterations while propagating early failures
  pick_eval (tm::tms)  =
    case tm of
    | Input in_signal =>
        if ... then NONE else
        if ... then SOME (...) else
          pick_eval tms
    | ...
       timeFunSem instead of timeSem

*)

val _ = export_theory();
