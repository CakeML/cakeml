(*
  Definition of CP problem syntax and semantics
*)
open preamble mlintTheory pbcTheory;

val _ = new_theory "cp";

Type assignment = ``:('a -> int)``;

Type varc = ``: 'a + int``;

Type bounds = ``:'a -> int # int``;

Definition varc_def:
  varc (w:'a assignment) (vc:'a varc) =
  case vc of
    INL v => w v
  | INR c => c
End

Definition not_equals_sem_def:
  not_equals_sem (X:'a varc) (Y:'a varc) (w: 'a assignment) =
    (varc w X ≠ varc w Y)
End

Definition all_different_sem_def:
  all_different_sem (As: ('a varc) list) (w: 'a assignment) =
    ALL_DISTINCT (MAP (varc w) As)
End

Definition element_sem_def:
  element_sem (R : 'a varc) (X : 'a varc) (As: ('a varc) list)
    (w: 'a assignment) =
    (1 ≤ varc w X ∧ Num (varc w X) ≤ LENGTH As ∧
      varc w R = varc w (EL (Num (varc w X) - 1) As)
    )
End

(* dummy value of m = 0 introduced when n = 0 *)
Definition element2d_sem_def:
  element2d_sem (R: 'a varc) (X: 'a varc) (Y: 'a varc) (Tss: ('a varc) list list)
                (w: 'a assignment) =
  let
    n = LENGTH Tss;
    m = if n = 0 then 0 else LENGTH $ EL 0 Tss;
    vX = Num $ varc w X;
    vY = Num $ varc w Y
  in
    EVERY (λTs. LENGTH Ts = m) Tss ∧
    1 ≤ vX ∧ vX ≤ n ∧ 1 ≤ vY ∧ vY ≤ m ∧
    EL (vY - 1) $ EL (vX - 1) (MAP (MAP (varc w)) Tss) = varc w R
End

Definition abs_sem_def:
  abs_sem X Y (w: 'a assignment) ⇔
    varc w X = ABS (varc w Y)
End

Type iclin_term = ``:(int # 'a varc) list ``

Definition eval_icterm_def[simp]:
  eval_icterm w (c:int,X) = c * varc w X
End

Definition eval_iclin_term_def:
  eval_iclin_term w (xs:'a iclin_term) =
    iSUM (MAP (eval_icterm w) xs)
End

Definition ilc_sem_def:
  ilc_sem (Xs : 'a iclin_term) op rhs (w:'a assignment) ⇔
  do_op op (eval_iclin_term w Xs) rhs
End

Definition arr_max_sem_def:
  arr_max_sem (M: 'a varc) (As: ('a varc) list) (w: 'a assignment) =
  let
    vM = varc w M;
    vAs = MAP (varc w) As
  in
    MEM vM vAs ∧ EVERY (λe. e ≤ vM) vAs
End

Definition arr_min_sem_def:
  arr_min_sem (M: 'a varc) (As: ('a varc) list) (w: 'a assignment) =
  let
    vM = varc w M;
    vAs = MAP (varc w) As
  in
    MEM vM vAs ∧ EVERY (λe. vM ≤ e) vAs
End

Definition count_sem_def:
  count_sem (Y: 'a varc) (C: 'a varc) (As: ('a varc) list) (w: 'a assignment) =
  (varc w C =
    iSUM $
      MAP (λA. if varc w A = varc w Y then 1 else 0) As)
End

Definition nvalue_sem_def:
  nvalue_sem (Y: 'a varc) (As: 'a list) (w: 'a assignment) =
  (varc w Y ≥ 0 ∧ (Num $ varc w Y = CARD $ set (MAP w As)))
End

Definition table_sem_def:
  table_sem (Xs: ('a varc) list) (Tss: int list list) (w: 'a assignment) =
  let n = LENGTH Xs in
    EVERY (λTs. LENGTH Ts = n) Tss ∧ MEM (MAP (varc w) Xs) Tss
End

Datatype:
  constraint =
    NotEquals ('a varc) ('a varc)
  | AllDifferent ('a varc list)
  | Element ('a varc) ('a varc) ('a varc list)
  | Element2D ('a varc) ('a varc) ('a varc) ('a varc list list)
  | Abs ('a varc) ('a varc)
  | Ilc ('a iclin_term) pbop int
  | ArrMax ('a varc) ('a varc list)
  | ArrMin ('a varc) ('a varc list)
  | Count ('a varc) ('a varc) ('a varc list)
  | Nvalue ('a varc) ('a list)
  | Table ('a varc list) (int list list)
End

Definition constraint_sem_def:
  constraint_sem c (w: 'a assignment) =
  case c of
    NotEquals X Y => not_equals_sem X Y w
  | AllDifferent As => all_different_sem As w
  | Element R X As => element_sem R X As w
  | Element2D R X Y Tss => element2d_sem R X Y Tss w
  | Abs X Y => abs_sem X Y w
  | Ilc Xs op rhs => ilc_sem Xs op rhs w
  | ArrMax M As => arr_max_sem M As w
  | ArrMin M As => arr_min_sem M As w
  | Count Y C As => count_sem Y C As w
  | Nvalue Y As => nvalue_sem Y As w
  | Table Xs Tss => table_sem Xs Tss w
End

Definition valid_assignment_def:
  valid_assignment (bnd: 'a bounds) w ⇔
  ∀x lb ub.
    bnd x = (lb,ub) ⇒
    lb ≤ w x ∧ w x ≤ ub
End

Type constraints = ``: 'a constraint set``;

Definition cp_sat_def:
  cp_sat bnd cs w ⇔
    valid_assignment bnd w ∧
    ∀c. c ∈ cs ⇒ constraint_sem c w
End

(* Satisfiability for a CP decision instance *)
Definition cp_satisfiable_def:
  cp_satisfiable bnd cs ⇔
  ∃w. cp_sat bnd cs w
End

(* Minimality for a CP optimization instance *)
Definition cp_minimal_def:
  cp_minimal bnd cs V (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    w V ≤ w' V
End

(* Maximality for a CP optimization instance *)
Definition cp_maximal_def:
  cp_maximal bnd cs V (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    w' V ≤ w V
End

val _ = export_theory();
