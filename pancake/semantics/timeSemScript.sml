(*
  semantics for timeLang
*)

open preamble
     timeLangTheory
     realTheory

val _ = new_theory "timeSem";

(* is it for every state *)
Datatype:
  store =
  <| clocks   : clock |-> time
   ; location : loc
   ; consumed : action option
   ; output   : effect option
   ; waitTime : time option
  |>
End

Definition minusT_def:
  minusT (t1:time) (t2:time) = t1 - t2
End

Definition mkStore_def:
  mkStore cks loc ac eff wt =
  <| clocks   := cks
   ; location := loc
   ; consumed := ac
   ; output   := eff
   ; waitTime := wt
  |>
End

Definition resetOutput_def:
  resetOutput st =
  st with
  <| consumed := NONE
   ; output   := NONE
   ; waitTime := NONE
  |>
End

Definition resetClocks_def:
  resetClocks (st:store) cvs =
  let reset_cvs = MAP (λx. (x,0:time)) cvs in
      st with clocks := st.clocks |++ reset_cvs
End


Definition list_min_option_def:
  (list_min_option ([]:real list) = NONE) /\
  (list_min_option (x::xs) =
   case list_min_option xs of
   | NONE => SOME x
   | SOME y => SOME (if x < y then x else y))
End

Definition delay_clocks_def:
  delay_clocks fm d = fm |++
                         (MAP (λ(x,y). (x,y+d))
                          (fmap_to_alist fm))
End


(*
Definition setLocation_def:
  setLocation (st:store) l = st with location := l
End

Definition setConsumed_def:
  setConsumed (st:store) ac = st with consumed := SOME ac
End

Definition setOutput_def:
  setOutput (st:store) eff = st with output := SOME eff
End

Definition setWait_def:
  setWait (st:store) t = st with waitTime := t
End
*)


Definition evalExpr_def:
  (evalExpr st (ELit t) = t) ∧
  (evalExpr st (ESub e1 e2) =
    minusT (evalExpr st e1) (evalExpr st e2)) ∧
  (evalExpr st (EClock c) =
    case FLOOKUP st.clocks c of
     | NONE => 0
     | SOME t => t)
End

Definition evalCond_def:
  (evalCond st (CndLe e1 e2) = (evalExpr st e1 <= evalExpr st e2)) /\
  (evalCond st (CndLt e1 e2) = (evalExpr st e1 < evalExpr st e2))
End

(* I think that t is run-time,
   and evalDiff would be used to calculate the delay *)
Definition evalDiff_def:
  evalDiff st ((t,c): time # clock) =
    evalExpr st (ESub (ELit t) (EClock c))
End


Definition calculate_wtime_def:
  calculate_wtime st clks diffs =
    list_min_option (MAP (evalDiff (resetClocks st clks)) diffs)
End

Inductive evalTerm:
  (∀st action cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ==>
     evalTerm st (SOME action)
              (Tm (Input action)
                  cnds
                  clks
                  dest
                  diffs)
              (resetClocks
               (st with  <| consumed := SOME action
                          ; location := dest
                          ; waitTime := calculate_wtime st clks diffs|>)
               clks)) /\

  (∀st effect cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ==>
     evalTerm st NONE
              (Tm (Output effect)
                  cnds
                  clks
                  dest
                  diffs)
              (resetClocks
               (st with  <| output   := SOME effect
                          ; location := dest
                          ; waitTime := calculate_wtime st clks diffs|>)
               clks))
End


Inductive pickTerm:
  (!st cnds event action clks dest diffs tms st'.
    EVERY (λx. x) (MAP (evalCond st) cnds) /\
    event = SOME action /\
    evalTerm st event (Tm (Input action) cnds clks dest diffs) st' ==>
    pickTerm st event (Tm (Input action) cnds clks dest diffs :: tms) st') /\

  (!st cnds event effect clks dest diffs tms st'.
    EVERY (λx. x) (MAP (evalCond st) cnds) /\
    event = NONE /\
    evalTerm st event (Tm (Output effect) cnds clks dest diffs) st' ==>
    pickTerm st event (Tm (Output effect) cnds clks dest diffs :: tms) st') /\

  (!st cnds event ioAction clks dest diffs tms st'.
    ~(EVERY (λx. x) (MAP (evalCond st) cnds)) /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm ioAction cnds clks dest diffs :: tms) st') /\

  (!st cnds event action clks dest diffs tms st'.
    event <> SOME action /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm (Input action) cnds clks dest diffs :: tms) st') /\

  (!st cnds event effect clks dest diffs tms st'.
    event <> NONE /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm (Output effect) cnds clks dest diffs :: tms) st')
End

Inductive step:
  (!p st d.
    st.waitTime = NONE /\
    0 <= d ==>
    step p st NONE
         (mkStore
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE
          NONE)
         (LDelay d)) /\
  (!p st d w.
    st.waitTime = SOME w /\
    d < w /\
    0 <= d ==>
    step p st NONE
         (mkStore
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE
          (SOME (w - d)))
         (LDelay d)) /\
  (!p st tms st' event.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) (SOME event) tms st' /\
      st'.consumed = SOME event /\
      st'.output = NONE ==>
      step p st (SOME event) st' (LAction (Input event))) /\
  (!p st tms st' eff.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) NONE tms st' /\
      st'.consumed = NONE /\
      st'.output = SOME eff ==>
      step p st NONE st' (LAction (Output eff)))
End


Inductive stepTrace:
  (!p st.
    stepTrace p st st []) /\
  (!p st st' st'' act lbl tr.
    step p st act st' lbl /\
    stepTrace p st' st'' tr ==>
    stepTrace p st st'' (lbl::tr))
End

(*

Datatype:
  label = LDelay time
        | LAction ioAction
End

        (setWait (setLocation
                        (resetClocks
                         (setConsumed st action)
                         clks)
                        dest)
               (list_min_option (MAP (evalDiff (resetClocks st clks)) diffs)))

        (setWait (setLocation
                        (resetClocks
                         (setOutput st effect)
                         clks)
                        dest)
               (list_min_option (MAP (evalDiff (resetClocks st clks)) diffs)))
*)


val _ = export_theory();
