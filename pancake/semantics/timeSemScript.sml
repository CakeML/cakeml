(*
  semantics for timeLang
*)

open preamble
     timeLangTheory

val _ = new_theory "timeSem";


Datatype:
  label = LDelay time
        | LAction ioAction
End


(*
   in our discussion, Magnus mentioned that its better to
   replace 'consumed' and 'output' components of state to
   something  ioAction : ioAction

   ; consumed : ioAction option
   ; output   : effect option ⇒ ioAction : ioAction


Datatype:
  store =
  <| clocks   : clock |-> time
   ; location : loc
   ; ioAction : ioAction option
     (* without option mayby, not sure *)
   ; waitTime : time option
  |>
End
*)

Datatype:
  store =
  <| clocks   : clock |-> time
   ; location : loc
   ; consumed : in_signal option
   ; output   : out_signal option
   ; waitTime : time option
  |>
End


Definition minusT_def:
  minusT (t1:time) (t2:time) = t1 - t2
End

Definition mkStore_def:
  mkStore cks loc act out wt =
  <| clocks   := cks
   ; location := loc
   ; consumed := act
   ; output   := out
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


(* TODO: rephrase this def *)

Definition list_min_option_def:
  (list_min_option ([]:num list) = NONE) /\
  (list_min_option (x::xs) =
   case list_min_option xs of
   | NONE => SOME x
   | SOME y => SOME (if x < y then x else y))
End

Definition delay_clocks_def:
  delay_clocks fm (d:num) = fm |++
                            (MAP (λ(x,y). (x,y+d))
                            (fmap_to_alist fm))
End

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

Definition evalDiff_def:
  evalDiff st ((t,c): time # clock) =
    evalExpr st (ESub (ELit t) (EClock c))
End


Definition calculate_wtime_def:
  calculate_wtime st clks diffs =
    list_min_option (MAP (evalDiff (resetClocks st clks)) diffs)
End

Inductive evalTerm:
  (∀st in_signal cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ==>
     evalTerm st (SOME in_signal)
              (Tm (Input in_signal)
                  cnds
                  clks
                  dest
                  diffs)
              (resetClocks
               (st with  <| consumed := SOME in_signal
                          ; location := dest
                          ; waitTime := calculate_wtime st clks diffs|>)
               clks)) /\

  (∀st out_signal cnds clks dest diffs.
     EVERY (λck. ck IN FDOM st.clocks) clks ==>
     evalTerm st NONE
              (Tm (Output out_signal)
                  cnds
                  clks
                  dest
                  diffs)
              (resetClocks
               (st with  <| output   := SOME out_signal
                          ; location := dest
                          ; waitTime := calculate_wtime st clks diffs|>)
               clks))
End

Inductive pickTerm:
  (!st cnds event in_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds /\
    event = SOME in_signal /\
    evalTerm st event (Tm (Input in_signal) cnds clks dest diffs) st' ==>
    pickTerm st event (Tm (Input in_signal) cnds clks dest diffs :: tms) st') /\

  (!st cnds event out_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds /\
    event = NONE /\
    evalTerm st event (Tm (Output out_signal) cnds clks dest diffs) st' ==>
    pickTerm st event (Tm (Output out_signal) cnds clks dest diffs :: tms) st') /\

  (!st cnds event ioAction clks dest diffs tms st'.
    ~(EVERY (λcnd. evalCond st cnd) cnds) /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm ioAction cnds clks dest diffs :: tms) st') /\

  (!st cnds event in_signal clks dest diffs tms st'.
    event <> SOME in_signal /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm (Input in_signal) cnds clks dest diffs :: tms) st') /\

  (!st cnds event out_signal clks dest diffs tms st'.
    event <> NONE /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm (Output out_signal) cnds clks dest diffs :: tms) st')
End

Inductive step:
  (!p st d.
    st.waitTime = NONE /\
    (0:num) <= d ==>
    step p (LDelay d) st
         (mkStore
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE
          NONE)) /\

  (!p st d w.
    st.waitTime = SOME w /\
    0 <= d /\ d < w ==>
    step p (LDelay d) st
         (mkStore
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE
          (SOME (w - d)))) /\

  (!p st tms st' in_signal.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) (SOME in_signal) tms st' /\
      st'.consumed = SOME in_signal /\
      st'.output = NONE ==>
      step p (LAction (Input in_signal)) st st') /\

  (!p st tms st' out_signal.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) NONE tms st' /\
      st'.consumed = NONE /\
      st'.output = SOME out_signal ==>
      step p (LAction (Output out_signal)) st st')
End


Inductive stepTrace:
  (!p st.
    stepTrace p st st []) /\
  (!p lbl st st' st'' tr.
    step p lbl st st' /\
    stepTrace p st' st'' tr ==>
    stepTrace p st st'' (lbl::tr))
End

val _ = export_theory();
