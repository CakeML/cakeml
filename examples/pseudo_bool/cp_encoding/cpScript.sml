(*
  Definition of CP problem syntax and semantics
*)
open preamble mlintTheory;

val _ = new_theory "cp";

Type assignment = ``:('a -> int)``;

Type varc = ``: 'a + int``;

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

Datatype:
  constraint =
    NotEquals ('a varc) ('a varc)
  | AllDifferent ('a varc list)
  | Element ('a varc) ('a varc) ('a varc list)
End

Definition constraint_sem_def:
  constraint_sem c (w: 'a assignment) =
  case c of
    NotEquals X Y => not_equals_sem X Y w
  | AllDifferent As => all_different_sem As w
  | Element R X As => element_sem R X As w
End

Type bounds = ``:'a -> int # int``;

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

Definition cp_satisfiable_def:
  cp_satisfiable bnd cs ⇔
  ∃w. cp_sat bnd cs w
End

Definition cp_minimal_def:
  cp_minimal bnd cs (V:'a varc) (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    varc w V ≤ varc w' V
End

Definition cp_maximal_def:
  cp_maximal bnd cs (V:'a varc) (w: 'a assignment) ⇔
  cp_sat bnd cs w ∧
  ∀w'.
    cp_sat bnd cs w' ⇒
    varc w' V ≤ varc w V
End

(* If we change bnd to be total, then this never happens
Definition cp_min_unbounded_def:
  cp_min_unbounded bnd cs (V:'a varc) ⇔
  (∃w. cp_sat bnd cs w) ∧
  (∀w.
    cp_sat bnd cs w ⇒
    ∃w'. cp_sat bnd cs w' ∧ varc w' V ≤ varc w V)
End
*)

val _ = export_theory();
