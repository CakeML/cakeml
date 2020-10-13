(*
  Abstract syntax for an imperative language
  compiling timed-automata based specifications
*)
open preamble
     mlstringTheory
     realTheory

val _ = new_theory "timeLang";

Type action = ``:num``
Type effect = ``:num``
Type loc    = ``:num``
Type time   = ``:real`` (* time is rational in the Coq formalism,
                           we are modeling it as real *)
Type clock   = ``:mlstring``
Type clocks  = ``:clock list``

Datatype:
  ioAction = Input action
           | Output effect
End


Datatype:
  label = LDelay time
        | LAction ioAction
End

(* time expression *)
Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End

(* relational expressions *)
Datatype:
  cond = CndLe expr expr  (* e <= e *)
       | CndLt expr expr  (* e < e *)
End

Datatype:
  term = Tm ioAction
            (cond list)
            clocks
            loc
            ((time # clock) list) (* (run-time value # clock variable) list for
                                     wait time *)
End

Type program = ``:(loc # term list) list``

Datatype:
  store =
  <| clockVal : clock |-> time
   ; location : loc
   ; consumed : action option
   ; output   :   effect option
   ; waitTime : time option
  |>
End

Definition minusT_def:
  minusT (t1:time) (t2:time) = t1 - t2
End

Definition evalExpr_def:
  (evalExpr st (ELit t) = t) ∧
  (evalExpr st (ESub e1 e2) =
   minusT (evalExpr st e1) (evalExpr st e2)) ∧
  (evalExpr st (EClock c) =
   case FLOOKUP st.clockVal c of
    | NONE => 0
    | SOME t => t)
  (* val_apply clock clock_dec time 0 clocks (clockVal st) c *)
End

Definition evalCond_def:
  (evalCond st (CndLe e1 e2) = (evalExpr st e1 <= evalExpr st e2)) /\
  (evalCond st (CndLt e1 e2) = (evalExpr st e1 < evalExpr st e2))
End

Definition evalDiff_def:
  evalDiff st ((t,c): time # clock) =
    evalExpr st (ESub (ELit t) (EClock c))
End

Definition resetClocks_def:
  resetClocks (st:store) cvs =
  let cvs_zeros = MAP (\x. (x,0:time)) cvs in
      st with clockVal := st.clockVal |++ cvs_zeros
End

Definition setLocation_def:
  setLocation (st:store) l = st with location := l
End

Definition setConsumed_def:
  setConsumed (st:store) ac = st with consumed := SOME ac
End

Definition setOutput_def:
  setOutput (st:store) eff = st with consumed := SOME eff
End

Definition setWait_def:
  setWait (st:store) t = st with waitTime := t
End

Definition mkStore_def:
  mkStore cmap loc ac eff wt =
  <| clockVal := cmap
   ; location := loc
   ; consumed := ac
   ; output   := eff
   ; waitTime := wt
  |>
End

Definition resetOutput_def:
  resetOutput st =
  <| clockVal := st.clockVal
   ; location := st.location
   ; consumed := NONE
   ; output   := NONE
   ; waitTime := NONE
  |>
End

Definition list_min_option_def:
  (list_min_option ([]:real list) = NONE) /\
  (list_min_option (x::xs) =
   case list_min_option xs of
   | NONE => SOME x
   | SOME y => SOME (if x < y then x else y))
End

Definition delay_clock_vals_def:
  delay_clock_vals fm d = fm |++
                             (MAP (λ(x,y). (x,y+d))
                              (fmap_to_alist fm))
End


Inductive evalTerm:
  (∀st event cnds rs dest diffs.
     EVERY (\c. c IN FDOM st.clockVal) rs ==>
     evalTerm st (SOME event)
              (Tm (Input event)
                  cnds
                  rs
                  dest
                  diffs)
              (setWait (setLocation
                        (resetClocks
                         (setConsumed st event)
                         rs)
                        dest)
               (list_min_option (MAP (evalDiff (resetClocks st rs)) diffs)))) /\
  (∀st eff cnds rs dest diffs.
     EVERY (\c. c IN FDOM st.clockVal) rs ==>
     evalTerm st NONE
              (Tm (Output eff)
                  cnds
                  rs
                  dest
                  diffs)
              (setWait (setLocation
                        (resetClocks
                         (setOutput st eff)
                         rs)
                        dest)
               (list_min_option (MAP (evalDiff (resetClocks st rs)) diffs))))
End


(* NB: The second store is also an index, but not introduced as
such to keep order of parameters in sync with evalTerm *)
Inductive pickTerm:
  (!st cnds act event rs dest diffs tms st'.
      EVERY (\x. x) (MAP (evalCond st) cnds) /\
      act = SOME event /\
      evalTerm st act (Tm (Input event) cnds rs dest diffs) st' ==>
      pickTerm st act (Tm (Input event) cnds rs dest diffs :: tms) st') /\
  (!st cnds act eff rs dest diffs tms st'.
      EVERY (\x. x) (MAP (evalCond st) cnds) /\
      act = NONE /\
      evalTerm st act (Tm (Output eff) cnds rs dest diffs) st' ==>
      pickTerm st act (Tm (Output eff) cnds rs dest diffs :: tms) st') /\
  (!st cnds act act' rs dest diffs tms st'.
      ~(EVERY (\x. x) (MAP (evalCond st) cnds)) /\
      pickTerm st act tms st' ==>
      pickTerm st act (Tm act' cnds rs dest diffs :: tms) st') /\
  (!st cnds act event rs dest diffs tms st'.
   act <> SOME event /\
       pickTerm st act tms st' ==>
   pickTerm st act (Tm (Input event) cnds rs dest diffs :: tms) st') /\
  (!st cnds act eff rs dest diffs tms st'.
      act <> NONE /\
      pickTerm st act tms st' ==>
      pickTerm st act (Tm (Output eff) cnds rs dest diffs :: tms) st')
End


Inductive step:
  (!p st d.
    st.waitTime = NONE /\
    0 <= d ==>
    step p st NONE
         (mkStore
          (delay_clock_vals (st.clockVal) d)
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
          (delay_clock_vals (st.clockVal) d)
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


val _ = export_theory();
