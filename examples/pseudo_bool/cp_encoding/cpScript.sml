(*
  Definition of CP problem syntax and semantics
*)
Theory cp
Libs
  preamble
Ancestors
  mlint pbc

Type assignment[pp] = ``:('a -> int)``;

Type varc[pp] = ``: 'a + int``;

Type bounds[pp] = ``:'a -> int # int``;

Definition varc_def:
  varc (w:'a assignment) (vc:'a varc) =
  case vc of
    INL v => w v
  | INR c => c
End

Datatype:
  prim_unop = Negative | Abs
End

Datatype:
  prim_binop =
    Plus | Minus
  (* TODO: future work, not in solver except maybe Times
  | Times | Div | Mod | Pow *)
  | Min | Max
End

Datatype:
  cmpop =
    Equal | NotEqual
  | GreaterEqual | GreaterThan
  | LessEqual | LessThan
End

Type reify[pp] = ``: ('a varc + 'a varc) option``;

(* For binary operations, we have the arguments
  to the operations followed by the RHS,
  e.g., Plus X Y Z means:
  X + Y = Z

  For the reified cmpops, the names are appended
  with -if or -iff, e.g.:
  equal-if
  equal-iff
*)
Datatype:
  prim_constr =
    (* op X Y : op X = Y *)
  | Unop prim_unop ('a varc) ('a varc)
    (* Binop op X Y Z : X op Y = Z *)
  | Binop prim_binop ('a varc) ('a varc) ('a varc)
    (* Cmpop reif op X Y : reify(X cmp Y) *)
  | Cmpop ('a reify) cmpop ('a varc) ('a varc)
End

(* The ones below are general constraints.
  Our policy: keep only general and widely-used ones.
  Those that can be readily encoded using other constraints are removed. *)
Datatype:
  counting_constr =
    (* AllDifferent Xs *)
  | AllDifferent ('a varc list)
    (* NValue Xs Y : Y is num. distinct in Xs *)
  | NValue ('a varc list) ('a varc)
    (* Count Xs Y Z : Z is num. times Y appears in Xs *)
  | Count ('a varc list) ('a varc) ('a varc)
    (* Among Xs iS Y : Y is how many times the values in iS (as set)
       appear in Xs *)
  | Among ('a varc list) (int list) ('a varc)
  (* AtMostOne TODO: future work, not yet in solver *)
End

Type iclin_term[pp] = ``:(int # 'a varc) list ``

(* The op is prefixed with "linear-", e.g.:
  lin-equal-if ((1 X) (2 5) ...) 5 *)
Datatype:
  linear_constr =
    (* Linear op Xs Y : Xs op Y *)
  | Lin ('a reify) cmpop ('a iclin_term) ('a varc)
End

(* The second value is the offset to interpret this index *)
Type array_ind[pp] = ``:('a varc # int)``

Datatype:
  array_constr =
    (* Element Xs Y Z : Xs[Y] = Z *)
  | Element ('a varc list) ('a array_ind) ('a varc)
    (* Element2D Xs Y1 Y2 Z : Xs[Y1][Y2] = Z *)
  | Element2D ('a varc list list) ('a array_ind) ('a array_ind) ('a varc)
    (* ArrayMax Xs Y : Y = max(Xs) *)
  | ArrayMax ('a varc list) ('a varc)
    (* ArrayMin Xs Y : Y = min(Xs) *)
  | ArrayMin ('a varc list) ('a varc)
  (* TODO: future work, not yet in solver
    (* ArrayArgMax Xs Y : Xs[Y] = max(Xs), and Y is leftmost such element *)
  | ArrayArgMax ('a varc list) ('a array_ind)
    (* ArrayArgMin Xs Y : Xs[Y] = max(Xs), and Y is leftmost such element *)
  | ArrayArgMin ('a varc list) ('a array_ind)
    (* In Y Xs: Y is in Xs *)
  | In ('a varc) ('a varc list)
  *)
End

(* NONE represents a wildcard entry for that element *)
Datatype:
  extensional_constr =
    Table ((int option) list list) ('a varc list)
End

Datatype:
  logical_constr =
    (* And Xs Y : Y > 0 ⇔ And_i (X_i > 0) *)
    And ('a varc list) ('a varc)
    (* Or Xs Y : Y > 0 ⇔ Or_i (X_i > 0) *)
  | Or ('a varc list) ('a varc)
    (* Parity Xs : Odd number of (X_i > 0) *)
  | Parity ('a varc list)
End

(* The op is prefixed with "lex-", e.g.:
  lex-less (X Y Z) (A B C) *)
Datatype:
  lexicographical_constr =
    Lex cmpop ('a varc list) ('a varc list)
End

Datatype:
  channeling_constr =
    (* Second arg is inverse of first when viewed
      as functions; second arg in each pair is the index *)
    Inverse ('a varc list # int) ('a varc list # int)
End

Datatype:
  misc_constr =
    (* List is a successor encoding, 0 indexed *)
    Circuit ('a varc list)
    (* Two equation version:
      weights, profits, variables
      total weight, total profit
      dot product of weights & variables = total weight
      dot product of profit & variables = total profit
    TODO Knapsack (int list) (int list) ('a varc list) ('a varc) ('a varc)  *)
End

Datatype:
  constraint =
  | Prim ('a prim_constr)
  | Counting ('a counting_constr)
  | Linear ('a linear_constr)
  | Array ('a array_constr)
  | Extensional ('a extensional_constr)
  | Logical ('a logical_constr)
  | Lexicographical ('a lexicographical_constr)
  | Channeling ('a channeling_constr)
  | Misc ('a misc_constr)
End

(* Semantics *)

(***
  prim_constr
***)
Definition unop_val_def:
  unop_val unop x =
  case unop of
    Negative => - x
  | Abs => ABS x
End

Definition unop_sem_def:
  unop_sem unop X Y w ⇔
  unop_val unop (varc w X) = varc w Y
End

(* Future work
Definition guard_binop_def:
  guard_binop bop y ⇔
  case bop of
    Div => y ≠ 0
  | Mod => y ≠ 0
  | Pow => y ≥ 0
  | _ => T
End
*)

Definition binop_val_def:
  binop_val bop x y =
  case bop of
    Plus => x + y
  | Minus => x - y
  | Min => int_min x y
  | Max => int_max x y
(*
  | Times => x * y
  | Div => x / y
  | Mod => x % y
  | Pow => x ** Num y
*)
End

Definition binop_sem_def:
  binop_sem bop X Y Z w =
  let x = varc w X in
  let y = varc w Y in
  let z = varc w Z in
  (* guard_binop bop y ∧ *)
  binop_val bop x y = z
End

Definition cmpop_val_def:
  cmpop_val cmp x (y:int) =
  case cmp of
    Equal => x = y
  | NotEqual => x ≠ y
  | GreaterEqual => x ≥ y
  | GreaterThan => x > y
  | LessEqual => x ≤ y
  | LessThan => x < y
End

(* NONE : no reification
  INL Z : one-sided reification
  INR Z : full reification *)
Definition reify_sem_def:
  reify_sem Zr w b =
  case Zr of
    NONE => b
  | SOME (INL Z) => varc w Z > 0 ⇒ b
  | SOME (INR Z) => varc w Z > 0 ⇔ b
End

Definition cmpop_sem_def:
  cmpop_sem Zr cmp X Y w =
  let x = varc w X in
  let y = varc w Y in
  reify_sem Zr w (cmpop_val cmp x y)
End

Definition prim_constr_sem_def:
  prim_constr_sem c w =
  case c of
    Unop uop X Y => unop_sem uop X Y w
  | Binop bop X Y Z => binop_sem bop X Y Z w
  | Cmpop Zr cmp X Y => cmpop_sem Zr cmp X Y w
End

(***
  counting_constr
***)
Definition all_different_sem_def:
  all_different_sem Xs w =
    ALL_DISTINCT (MAP (varc w) Xs)
End

Definition n_value_sem_def:
  n_value_sem Xs Y w =
  (varc w Y ≥ 0 ∧
    (Num $ varc w Y =
    CARD $ set (MAP (varc w) Xs)))
End

Definition count_sem_def:
  count_sem Xs Y Z w =
  (varc w Z =
    iSUM $
      MAP
      (λX.
        b2i (varc w X = varc w Y)
      ) Xs)
End

Definition among_sem_def:
  among_sem Xs iS Y w =
  (varc w Y =
    iSUM $
      MAP
      (λX.
        b2i (varc w X ∈ set iS)
      ) Xs)
End

Definition counting_constr_sem_def:
  counting_constr_sem c w =
  case c of
    AllDifferent Xs => all_different_sem Xs w
  | NValue Xs Y => n_value_sem Xs Y w
  | Count Xs Y Z => count_sem Xs Y Z w
  | Among Xs iS Y => among_sem Xs iS Y w
End

(***
  linear_constr
***)
Definition eval_icterm_def[simp]:
  eval_icterm w (c:int,X) = c * varc w X
End

Definition eval_iclin_term_def:
  eval_iclin_term w (xs:'a iclin_term) =
    iSUM (MAP (eval_icterm w) xs)
End

Definition lin_sem_def:
  lin_sem Zr cmp Xs Y w ⇔
  reify_sem Zr w
  (cmpop_val cmp
    (eval_iclin_term w Xs)
    (varc w Y))
End

Definition linear_constr_sem_def:
  linear_constr_sem c w ⇔
  case c of Lin Zr cmp Xs Y =>
    lin_sem Zr cmp Xs Y w
End

(***
  array_constr
***)

(* i is the 0th position, and we offset from there *)
Definition mk_array_ind_def:
  mk_array_ind (Y,i) w =
  varc w Y - i
End

Definition element_sem_def:
  element_sem Xs Yi Z w ⇔
  let y = mk_array_ind Yi w in
  0 ≤ y ∧ Num y < LENGTH Xs ∧
  varc w Z =
    varc w (EL (Num y) Xs)
End

(* TODO *)
Definition element2d_sem_def:
  element2d_sem Xss Y1i Y2i Z w ⇔
  let y1 = mk_array_ind Y1i w in
  let y2 = mk_array_ind Y2i w in
  0 ≤ y1 ∧ Num y1 < LENGTH Xss ∧
  0 ≤ y2 ∧
  (∃l.
    EVERY (λXs. LENGTH Xs = l) Xss ∧
    Num y2 < l) ∧
  varc w Z =
    varc w (
      EL (Num y2)
        (EL (Num y1) Xss))
End

Definition array_max_sem_def:
  array_max_sem Xs Y w =
  let
    y = varc w Y;
    xs = MAP (varc w) Xs
  in
    MEM y xs ∧
    EVERY (λx. x ≤ y) xs
End

Definition array_min_sem_def:
  array_min_sem Xs Y w =
  let
    y = varc w Y;
    xs = MAP (varc w) Xs
  in
    MEM y xs ∧
    EVERY (λx. y ≤ x) xs
End

(*
Definition array_arg_max_sem_def:
  array_arg_max_sem Xs Yi w =
  let
    y = mk_array_ind Yi w;
    xs = MAP (varc w) Xs
  in
    0 ≤ y ∧ Num y < LENGTH xs ∧
    EVERY (λx. x ≤ EL (Num y) xs) xs
End

Definition array_arg_min_sem_def:
  array_arg_min_sem Xs Yi w =
  let
    y = mk_array_ind Yi w;
    xs = MAP (varc w) Xs
  in
    0 ≤ y ∧ Num y < LENGTH xs ∧
    EVERY (λx. EL (Num y) xs ≤ x) xs
End

Definition in_sem_def:
  in_sem Y Xs w =
  let
    y = varc w Y;
    xs = MAP (varc w) Xs
  in
    MEM y xs
End
*)

Definition array_constr_sem_def:
  array_constr_sem c w ⇔
  case c of
    Element Xs Yi Z => element_sem Xs Yi Z w
  | Element2D Xss Y1i Y2i Z =>
      element2d_sem Xss Y1i Y2i Z w
  | ArrayMax Xs Y => array_max_sem Xs Y w
  | ArrayMin Xs Y => array_min_sem Xs Y w
  (*
  | ArrayArgMax Xs Yi =>
      array_arg_max_sem Xs Yi w
  | ArrayArgMin Xs Yi =>
      array_arg_min_sem Xs Yi w
  | In Y Xs => in_sem Y Xs w
  *)
End

(***
  extensional_constr
***)
Definition match_row_def:
  match_row ts xs ⇔
  LIST_REL
    (λt x.
      case t of
        NONE => T
      | SOME v => v = x) ts xs
End

Definition table_sem_def:
  table_sem tss Xs w ⇔
  EVERY (λts. LENGTH ts = LENGTH Xs) tss ∧
  ∃ts. MEM ts tss ∧ match_row ts (MAP (varc w) Xs)
End

Definition extensional_constr_sem_def:
  extensional_constr_sem c w ⇔
  case c of Table tss Xs =>
    table_sem tss Xs w
End

(***
  logical_constr
***)
Definition and_sem_def:
  and_sem Xs Y w =
   reify_sem (SOME (INR Y)) w
    (EVERY (λX. varc w X > 0) Xs)
End

Definition or_sem_def:
  or_sem Xs Y w =
   reify_sem (SOME (INR Y)) w
    (EXISTS (λX. varc w X > 0) Xs)
End

Definition parity_sem_def:
  parity_sem Xs w =
   ODD
   (SUM $
      MAP
      (λX.
        if varc w X > 0 then 1n else 0n
      ) Xs)
End

Definition logical_constr_sem_def:
  logical_constr_sem c w ⇔
  case c of
    And Xs Y => and_sem Xs Y w
  | Or Xs Y => or_sem Xs Y w
  | Parity Xs => parity_sem Xs w
End

(***
  lexicographical_constr
***)

(* Our semantics assumes LENGTH xs = LENGTH ys *)
Definition row_lt_def:
  (row_lt (x::xs) (y::ys) ⇔
    (x:int) < y ∨
    (x = y) ∧ row_lt xs ys) ∧
  (row_lt _ _ ⇔ F)
End

Definition cmpop_row_val_def:
  cmpop_row_val cmp (xs:int list) (ys:int list) =
  case cmp of
    Equal => xs = ys
  | NotEqual => xs ≠ ys
  | GreaterEqual => row_lt ys xs ∨ xs = ys
  | GreaterThan => row_lt ys xs
  | LessEqual => row_lt xs ys ∨ xs = ys
  | LessThan => row_lt xs ys
End

Definition lex_sem_def:
  lex_sem cmp Xs Ys w ⇔
  LENGTH Xs = LENGTH Ys ∧
  cmpop_row_val cmp (MAP (varc w) Xs) (MAP (varc w) Ys)
End

Definition lexicographical_constr_sem_def:
  lexicographical_constr_sem c w ⇔
  case c of Lex cmp Xs Ys =>
    lex_sem cmp Xs Ys w
End

(***
  channeling_constr TODO
***)
Definition inverse_sem_def:
  inverse_sem (Xs,offx) (Ys,offy) w ⇔
  let
    lXs = &LENGTH Xs;
    lYs = &LENGTH Ys
  in
    lXs = lYs ∧
  EVERY (λX.
    let n = mk_array_ind (X,offy) w in
    0 ≤ n ∧ n < lYs) Xs ∧
  EVERY (λY.
    let n = mk_array_ind (Y,offx) w in
    0 ≤ n ∧ n < lXs) Ys ∧
  ∀i j.
    offx ≤ i ∧ i < offx + lXs ∧
    offy ≤ j ∧ j < offy + lYs ⇒
    (
      varc w (EL (Num (i - offx)) Xs) = j ⇔
      varc w (EL (Num (j - offy)) Ys) = i
    )
End

Definition channeling_constr_sem_def:
  channeling_constr_sem c w ⇔
  case c of Inverse Xsi Ysi =>
    inverse_sem Xsi Ysi w
End

(***
  misc_constr TODO
***)
Definition misc_constr_sem_def:
  misc_constr_sem c w ⇔
  T
End

Definition constraint_sem_def:
  constraint_sem c (w: 'a assignment) =
  case c of
    Prim c => prim_constr_sem c w
  | Counting c => counting_constr_sem c w
  | Linear c => linear_constr_sem c w
  | Array c => array_constr_sem c w
  | Extensional c => extensional_constr_sem c w
  | Logical c => logical_constr_sem c w
  | Lexicographical c => lexicographical_constr_sem c w
  | Channeling c => channeling_constr_sem c w
  | Misc c => misc_constr_sem c w
End

Definition valid_assignment_def:
  valid_assignment (bnd: 'a bounds) w ⇔
  ∀x lb ub.
    bnd x = (lb,ub) ⇒
    lb ≤ w x ∧ w x ≤ ub
End

Type constraints[pp] = ``: 'a constraint set``;

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

Type cp_inst[pp] = ``:(mlstring, int # int) alist # mlstring constraint list # mlstring objective``;

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


