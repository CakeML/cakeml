(*
  Definition of CP problem syntax and semantics
*)
open preamble mlintTheory;

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

Definition abs_sem_def:
  abs_sem X Y (w: 'a assignment) ⇔
    varc w X = ABS (varc w Y)
End

Datatype:
  constraint =
    NotEquals ('a varc) ('a varc)
  | AllDifferent ('a varc list)
  | Element ('a varc) ('a varc) ('a varc list)
  | Abs ('a varc) ('a varc)
End

Definition constraint_sem_def:
  constraint_sem c (w: 'a assignment) =
  case c of
    NotEquals X Y => not_equals_sem X Y w
  | AllDifferent As => all_different_sem As w
  | Element R X As => element_sem R X As w
  | Abs X Y => abs_sem X Y w
End

Definition valid_assignment_def:
  valid_assignment (bnd: 'a bounds) w ⇔
  ∀x lb ub.
    bnd x = (lb,ub) ⇒
    lb ≤ w x ∧ w x ≤ ub
End

Type constraints = ``: 'a constraint set``;

Definition cp_sat :
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
  cp_minimal bnd cs (V:'a varc) (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    varc w V ≤ varc w' V
End

(* Maximality for a CP optimization instance *)
Definition cp_maximal_def:
  cp_maximal bnd cs (V:'a varc) (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    varc w' V ≤ varc w V
End

val _ = export_theory();
