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


(*
Definition resetClocks_def:
  resetClocks clks cvars_vals =
    clks |++ MAP (λx. (x,0:time)) cvars_vals
End
*)


(*
Definition resetClocks_def:
  resetClocks (st:state) cvs =
  let reset_cvs = MAP (λx. (x,0:time)) cvs in
      st with clocks := st.clocks |++ reset_cvs
End
*)

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

(*
Definition evalExpr_def:
  (evalExpr st (ELit t) = t) ∧
  (evalExpr st (ESub e1 e2) =
    minusT (evalExpr st e1) (evalExpr st e2)) ∧
  (evalExpr st (EClock c) =
    case FLOOKUP st.clocks c of
     | NONE => 0
     | SOME t => t)
End
*)

(*
Definition evalCond_def:
  (evalCond st (CndLe e1 e2) = (evalExpr st e1 <= evalExpr st e2)) /\
  (evalCond st (CndLt e1 e2) = (evalExpr st e1 < evalExpr st e2))
End
*)

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


Inductive pickTerm:
  (* when each condition is true and input signals match with the first term *)
  (!st cnds in_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds /\
    evalTerm st (SOME in_signal) (Tm (Input in_signal) cnds clks dest diffs) st' ==>
    pickTerm st (SOME in_signal) (Tm (Input in_signal) cnds clks dest diffs :: tms) st') /\

  (* when each condition is true and output signals match with the first term *)
  (!st cnds out_signal clks dest diffs tms st'.
    EVERY (λcnd. evalCond st cnd) cnds /\
    evalTerm st NONE (Tm (Output out_signal) cnds clks dest diffs) st' ==>
    pickTerm st NONE (Tm (Output out_signal) cnds clks dest diffs :: tms) st') /\

  (* when any condition is false, but there is a matching term, then we can append the
     list with the false term  *)
  (!st cnds event ioAction clks dest diffs tms st'.
    ~(EVERY (λcnd. evalCond st cnd) cnds) /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm ioAction cnds clks dest diffs :: tms) st') /\

   (* when the input event does not match, but there is a matching term, then we can append the
      list with the false term *)
  (!st cnds event in_signal clks dest diffs tms st'.
    event <> SOME in_signal /\
    pickTerm st event tms st' ==>
    pickTerm st event (Tm (Input in_signal) cnds clks dest diffs :: tms) st') /\

  (* we can also append this in case of any SOME event with an output term *)
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
         (mkState
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE)) /\

  (!p st d w.
    st.waitTime = SOME w /\
    0 <= d /\ d < w ==>
    step p (LDelay d) st
         (mkState
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          (SOME (w - d)))) /\

  (!p st tms st' in_signal.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) (SOME in_signal) tms st' /\
      st'.ioAction = SOME (Input in_signal) ==>
      step p (LAction (Input in_signal)) st st') /\

  (!p st tms st' out_signal.
      ALOOKUP p st.location = SOME tms /\
      pickTerm (resetOutput st) NONE tms st' /\
      st'.ioAction = SOME (Output out_signal) ==>
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
