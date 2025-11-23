(*
  Definition of CP problem syntax and semantics
*)
Theory cp
Libs
  preamble
Ancestors
  mlint pbc

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

Definition element2d_sem_def:
  element2d_sem (R: 'a varc) (X: 'a varc) (Y: 'a varc) (Tss: ('a varc) list list)
    (w: 'a assignment) =
  let
    vX = varc w X;
    vY = varc w Y
  in
    1 ≤ vX ∧ Num vX ≤ LENGTH Tss ∧ 1 ≤ vY ∧ Num vY ≤ LENGTH $ HD Tss ∧
    EVERY (λTs. LENGTH Ts = LENGTH $ HD Tss) Tss ∧
    varc w R = varc w (EL (Num vY - 1) $ EL (Num vX - 1) Tss)
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
  table_sem (Xs: 'a list) (Tss: int list list) (w: 'a assignment) ⇔
  EVERY (λTs. LENGTH Ts = LENGTH Xs) Tss ∧ MEM (MAP w Xs) Tss
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
  | Table ('a list) (int list list)
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

Datatype:
  objective =
    NoObjective
  | Minimize 'a
  | Maximize 'a
End

Definition cp_sat_def:
  cp_sat bnd cs w ⇔
    valid_assignment bnd w ∧
    ∀c. c ∈ cs ⇒ constraint_sem c w
End

Definition cp_satisfiable_def:
  cp_satisfiable bnd cs ⇔
  ∃w. cp_sat bnd cs w
End

Definition cp_unsatisfiable_def:
  cp_unsatisfiable bnd cs ⇔
    ¬cp_satisfiable bnd cs
End

(* lb is a lower bound on the value of v, NONE means +infinity *)
Definition cp_is_lb_def:
  cp_is_lb bnd cs v lbi ⇔
    case lbi of
      NONE => cp_unsatisfiable bnd cs
    | SOME lb =>
      (∀w. cp_sat bnd cs w ⇒ lb ≤ w v)
End

(* An attainable lower bound on the value of v, NONE means -infinity *)
Definition cp_has_lb_def:
  cp_has_lb bnd cs v lbi ⇔
    case lbi of
      NONE => T
    | SOME lb =>
      (∃w. cp_sat bnd cs w ∧ lb ≤ w v)
End

(* ub is an upper bound on the value of v, NONE means -infinity *)
Definition cp_is_ub_def:
  cp_is_ub bnd cs v ubi ⇔
    case ubi of
      NONE => cp_unsatisfiable bnd cs
    | SOME ub =>
      (∀w. cp_sat bnd cs w ⇒ w v ≤ ub)
End

(* An attainable upper bound on the value of v, NONE means +infinity *)
Definition cp_has_ub_def:
  cp_has_ub bnd cs v ubi ⇔
    case ubi of
      NONE => T
    | SOME ub =>
      (∃w. cp_sat bnd cs w ∧ w v ≤ ub)
End

(* We reuse the conclusion type from PBC to define the meaning of a CP problem.
  The important case is for OBounds, where it depends on the CP problem
*)
Definition cp_sem_concl_def:
  (cp_sem_concl bnd cs obj NoConcl ⇔ T) ∧
  (cp_sem_concl bnd cs obj DSat ⇔ cp_satisfiable bnd cs) ∧
  (cp_sem_concl bnd cs obj DUnsat ⇔ cp_unsatisfiable bnd cs) ∧
  (cp_sem_concl bnd cs obj (OBounds lbi ubi) =
    case obj of
      NoObjective => T
    | Minimize v =>
      cp_is_lb bnd cs v lbi ∧
      cp_has_ub bnd cs v ubi
    | Maximize v =>
      cp_has_lb bnd cs v lbi ∧
      cp_is_ub bnd cs v ubi
  )
End

(* The minimal value for a CP minimization instance *)
Definition cp_minimal_def:
  cp_minimal bnd cs v b ⇔
  ∃w.
    cp_sat bnd cs w ∧ w v = b ∧
    ∀w'.
      cp_sat bnd cs w' ⇒ b ≤ w' v
End

(* The maximal value for a CP maximization instance *)
Definition cp_maximal_def:
  cp_maximal bnd cs v b ⇔
  ∃w.
    cp_sat bnd cs w ∧ w v = b ∧
    ∀w'.
      cp_sat bnd cs w' ⇒ w' v ≤ b
End

Theorem cp_sem_concl_minimize:
  cp_sem_concl bnd cs (Minimize v) (OBounds (SOME b) (SOME b)) ⇒
  cp_minimal bnd cs v b
Proof
  rw[cp_sem_concl_def,cp_minimal_def,cp_is_lb_def,cp_has_ub_def]>>
  first_x_assum drule>>
  rw[]>>first_assum $ irule_at Any>>
  intLib.ARITH_TAC
QED

Theorem cp_sem_concl_maximize:
  cp_sem_concl bnd cs (Maximize v) (OBounds (SOME b) (SOME b)) ⇒
  cp_maximal bnd cs v b
Proof
  rw[cp_sem_concl_def,cp_maximal_def,cp_has_lb_def,cp_is_ub_def]>>
  first_x_assum drule>>
  rw[]>>first_assum $ irule_at Any>>
  intLib.ARITH_TAC
QED

(* Our concrete CP instances will consist of:

- bnd : (mlstring, int # int) alist
- cs : mlstring constraint list
- obj : mlstring objective
*)

Type cp_inst = ``:(mlstring, int # int) alist # mlstring constraint list # mlstring objective``;

(* For any unspecified variable, default to (0,0) *)
Definition bnd_lookup_def:
  bnd_lookup ls x =
    case ALOOKUP ls x of
      NONE => (0i,0i)
    | SOME v => v
End

Definition cp_inst_sem_concl_def:
  cp_inst_sem_concl (inst:cp_inst) concl ⇔
  case inst of (bnd,cs,obj) =>
    cp_sem_concl (bnd_lookup bnd) (set cs) obj concl
End


