(*
  semantics for timeLang
*)

open preamble
     timeLangTheory

val _ = new_theory "timeSem";

Datatype:
  panic = PanicTimeout
        | PanicInput in_signal
End

Datatype:
  label = LDelay time
        | LAction ioAction
        | LPanic panic
End

Datatype:
  state =
  <| clocks   : clock |-> time
   ; location : loc
   ; ioAction : ioAction option
   ; waitTime : time option
  |>
End


Definition mkState_def:
  mkState cks loc io wt =
  <| clocks   := cks
   ; location := loc
   ; ioAction := io
   ; waitTime := wt
  |>
End

Definition resetOutput_def:
  resetOutput st =
  st with
  <| ioAction := NONE
   ; waitTime := NONE
  |>
End

Definition resetClocks_def:
  resetClocks fm xs =
    fm |++ ZIP (xs,MAP (λx. 0:time) xs)
End

(* TODO: rephrase this def *)

Definition list_min_option_def:
  (list_min_option ([]:num list) = NONE) /\
  (list_min_option (x::xs) =
   case list_min_option xs of
   | NONE => SOME x
   | SOME y => SOME (if x < y then x else y))
End

Definition delay_clocks_def:
  delay_clocks fm (d:num) = FEMPTY |++
                            (MAP (λ(x,y). (x,y+d))
                            (fmap_to_alist fm))
End


Definition minusT_def:
  minusT (t1:time) (t2:time) = t1 - t2
End

(* inner case for generating induction theorem *)

Definition evalExpr_def:
  evalExpr st e =
  case e of
  | ELit t => SOME t
  | EClock c => FLOOKUP st.clocks c
  | ESub e1 e2 =>
      case (evalExpr st e1, evalExpr st e2) of
      | SOME t1,SOME t2 =>
                  if t2 ≤ t1 then SOME (minusT t1 t2)
                  else NONE
      | _=> NONE
End


Definition evalCond_def:
  (evalCond st (CndLe e1 e2) =
    case (evalExpr st e1,evalExpr st e2) of
    | SOME t1,SOME t2 => t1 ≤ t2
    | _ => F) ∧
  (evalCond st (CndLt e1 e2) =
    case (evalExpr st e1,evalExpr st e2) of
    | SOME t1,SOME t2 => t1 < t2
    | _ => F)
End


Definition evalDiff_def:
  evalDiff st ((t,c): time # clock) =
    evalExpr st (ESub (ELit t) (EClock c))
End


Definition calculate_wtime_def:
  calculate_wtime st clks diffs =
  let
    st = st with clocks := resetClocks st.clocks clks
  in
    list_min_option (MAP (THE o evalDiff st) diffs)
End


Inductive evalTerm:
  (∀st in_signal cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ∧
     EVERY (λ(t,c).
             ∃v. FLOOKUP st.clocks c = SOME v ∧
                 v ≤ t) diffs ==>
     evalTerm st (SOME in_signal)
              (Tm (Input in_signal)
                  cnds
                  clks
                  dest
                  diffs)
              (st with  <| clocks   := resetClocks st.clocks clks
                         ; ioAction := SOME (Input in_signal)
                         ; location := dest
                         ; waitTime := calculate_wtime st clks diffs|>)) /\
  (∀st out_signal cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ∧
     EVERY (λ(t,c).
             ∃v. FLOOKUP st.clocks c = SOME v ∧
                 v ≤ t) diffs ==>
     evalTerm st NONE
              (Tm (Output out_signal)
                  cnds
                  clks
                  dest
                  diffs)
              (st with  <| clocks   := resetClocks st.clocks clks
                         ; ioAction := SOME (Output out_signal)
                         ; location := dest
                         ; waitTime := calculate_wtime st clks diffs|>))
End

Definition max_clocks_def:
  max_clocks fm (m:num) ⇔
  ∀ck n.
    FLOOKUP fm ck = SOME n ⇒
    n < m
End


Definition tm_conds_eval_def:
  tm_conds_eval s tm =
    EVERY (λcnd.
            EVERY (λe. case (evalExpr s e) of
                       | SOME n => T
                       | _ => F) (destCond cnd))
          (termConditions tm)
End


Definition tms_conds_eval_def:
  tms_conds_eval s tms =
    EVERY (tm_conds_eval s) tms
End

Definition tm_conds_eval_limit_def:
  tm_conds_eval_limit m s tm =
    EVERY (λcnd.
            EVERY (λe. case (evalExpr s e) of
                       | SOME n => n < m
                       | _ => F) (destCond cnd))
          (termConditions tm)
End


Definition conds_eval_lt_dimword_def:
  conds_eval_lt_dimword m s tms =
    EVERY (tm_conds_eval_limit m s) tms
End


Definition time_range_def:
  time_range wt (m:num) ⇔
    EVERY (λ(t,c). t < m) wt
End


Definition term_time_range_def:
  term_time_range m tm =
    time_range (termWaitTimes tm) m
End

Definition terms_time_range_def:
  terms_time_range m tms =
    EVERY (term_time_range m) tms
End

Definition input_terms_actions_def:
  input_terms_actions m tms =
    EVERY (λn. n+1 < m)
          (terms_in_signals tms)
End

Definition terms_wtimes_ffi_bound_def:
  terms_wtimes_ffi_bound m s tms =
    EVERY (λtm.
            case calculate_wtime (resetOutput s) (termClks tm) (termWaitTimes tm) of
            | NONE => T
            | SOME wt => wt < m
          ) tms
End

(* max is dimword *)
(* m is m+n *)
Inductive pickTerm:
  (!st m cnds in_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds ∧
    conds_eval_lt_dimword m st (Tm (Input in_signal) cnds clks dest diffs::tms) ∧
    max_clocks st.clocks m ∧
    terms_time_range m (Tm (Input in_signal) cnds clks dest diffs::tms)  ∧
    input_terms_actions m (Tm (Input in_signal) cnds clks dest diffs::tms) ∧
    terms_wtimes_ffi_bound m st (Tm (Input in_signal) cnds clks dest diffs::tms) ∧
    evalTerm st (SOME in_signal) (Tm (Input in_signal) cnds clks dest diffs) st' ⇒
    pickTerm st m (SOME in_signal) (Tm (Input in_signal) cnds clks dest diffs::tms) st'
             (LAction (Input in_signal))) ∧

  (!st m cnds out_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds ∧
    conds_eval_lt_dimword m st (Tm (Output out_signal) cnds clks dest diffs::tms) ∧
    max_clocks st.clocks m ∧
    terms_time_range m (Tm (Output out_signal) cnds clks dest diffs::tms) ∧
    input_terms_actions m tms ∧
    terms_wtimes_ffi_bound m st (Tm (Output out_signal) cnds clks dest diffs::tms) ∧
    evalTerm st NONE (Tm (Output out_signal) cnds clks dest diffs) st' ⇒
    pickTerm st m NONE (Tm (Output out_signal) cnds clks dest diffs::tms) st'
             (LAction (Output out_signal))) ∧

  (!st m cnds event ioAction clks dest diffs tms st' lbl.
    EVERY (λcnd. EVERY (λe. ∃t. evalExpr st e = SOME t) (destCond cnd)) cnds ∧
    ~(EVERY (λcnd. evalCond st cnd) cnds) ∧
    tm_conds_eval_limit m st (Tm ioAction cnds clks dest diffs) ∧
    term_time_range m (Tm ioAction cnds clks dest diffs) ∧
    input_terms_actions m [(Tm ioAction cnds clks dest diffs)] ∧
    terms_wtimes_ffi_bound m st (Tm ioAction cnds clks dest diffs :: tms) ∧
    pickTerm st m event tms st' lbl ⇒
    pickTerm st m event (Tm ioAction cnds clks dest diffs :: tms) st' lbl) ∧

  (!st m cnds event in_signal clks dest diffs tms st' lbl.
    event <> SOME in_signal ∧
    tm_conds_eval_limit m st (Tm (Input in_signal) cnds clks dest diffs) ∧
    term_time_range m (Tm (Input in_signal) cnds clks dest diffs) ∧
    terms_wtimes_ffi_bound m st (Tm (Input in_signal) cnds clks dest diffs :: tms) ∧
    in_signal + 1 < m ∧
    pickTerm st m event tms st' lbl ⇒
    pickTerm st m event (Tm (Input in_signal) cnds clks dest diffs :: tms) st' lbl) ∧

  (!st m cnds event out_signal clks dest diffs tms st' lbl.
    event <> NONE ∧
    tm_conds_eval_limit m st (Tm (Output out_signal) cnds clks dest diffs) ∧
    term_time_range m (Tm (Output out_signal) cnds clks dest diffs) ∧
    terms_wtimes_ffi_bound m st (Tm (Output out_signal) cnds clks dest diffs :: tms) ∧
    pickTerm st m event tms st' lbl ⇒
    pickTerm st m event (Tm (Output out_signal) cnds clks dest diffs :: tms) st' lbl) ∧

  (!st m.
    max_clocks st.clocks m  ⇒
    pickTerm st m NONE [] st (LPanic PanicTimeout)) ∧

  (!st m in_signal.
    max_clocks st.clocks m ∧
    in_signal + 1 < m ⇒
    pickTerm st m (SOME in_signal) [] st (LPanic (PanicInput in_signal)))
End

(* d + n ≤ m ∧ *)

(* m ≤ w + n *)
(* n would be FST (seq 0), or may be systime time *)
Inductive step:
  (!p m n st d.
    st.waitTime = NONE ∧
    d + n < m ∧
    max_clocks (delay_clocks (st.clocks) (d + n)) m ⇒
    step p (LDelay d) m n st
         (mkState
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE)) ∧

  (!p m n st d w.
    st.waitTime = SOME w ∧
    d ≤ w ∧ w < m ∧ d + n < m ∧
    max_clocks (delay_clocks (st.clocks) (d + n)) m ⇒
    step p (LDelay d) m n st
         (mkState
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          (SOME (w - d)))) ∧

  (!p m n st tms st' in_signal.
    n < m ∧
    ALOOKUP p st.location = SOME tms ∧
    (case st.waitTime of
     | NONE => T
     | SOME wt => wt ≠ 0 ∧ wt < m) ∧
    pickTerm (resetOutput st) m (SOME in_signal) tms st' (LAction (Input in_signal)) ∧
    st'.ioAction = SOME (Input in_signal) ⇒
    step p (LAction (Input in_signal)) m n st st') ∧

  (!p m n st tms st' out_signal.
    n < m ∧
    ALOOKUP p st.location = SOME tms ∧
    st.waitTime = SOME 0 ∧
    pickTerm (resetOutput st) m NONE tms st' (LAction (Output out_signal)) ∧
    st'.ioAction = SOME (Output out_signal) ⇒
    step p (LAction (Output out_signal)) m n st st') ∧

  (!p m n st tms st'.
    n < m ∧
    ALOOKUP p st.location = SOME tms ∧
    st.waitTime = SOME 0 ∧
    pickTerm (resetOutput st) m NONE tms st' (LPanic PanicTimeout) ⇒
    step p (LPanic PanicTimeout) m n st st') ∧

  (!p m n st tms st' in_signal.
    n < m ∧
    ALOOKUP p st.location = SOME tms ∧
    (case st.waitTime of
     | NONE => T
     | SOME wt => wt ≠ 0 ∧ wt < m) ∧
    pickTerm (resetOutput st) m (SOME in_signal) tms st' (LPanic (PanicInput in_signal)) ⇒
    step p (LPanic (PanicInput in_signal)) m n st st')
End

Definition steps_def:
  (steps prog [] m n s [] ⇔
   n < m  ∧
   (case s.waitTime of
    | SOME w => (* w ≠ 0 ∧ *) w < m
    | NONE => T)) ∧
  (steps prog (lbl::lbls) m n s (st::sts) ⇔
     step prog lbl m n s st ∧
     let n' =
         case lbl of
         | LDelay d => d + n
         | _ => n
     in
       steps prog lbls m n' st sts) ∧
  (steps prog _ m _ s _ ⇔ F)
End

Inductive stepTrace:
  (!p m n st.
    stepTrace p m n st st []) ∧

  (!p lbl m n st st' st'' tr.
    step p lbl m n st st' ∧
    stepTrace p m (case lbl of
                   | LDelay d => d + n
                   | LAction _ => n)
              st' st'' tr ⇒
    stepTrace p m n st st'' (lbl::tr))
End


val _ = export_theory();
