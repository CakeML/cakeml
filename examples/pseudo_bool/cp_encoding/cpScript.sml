(*
  Definition of CP problem syntax and semantics
*)
Theory cp
Libs
  preamble
Ancestors
  mlint pbc sorting

Type assignment[pp] = ``:('a -> int)``;

Type varc[pp] = ``: 'a + int``;

Type bounds[pp] = ``:'a -> int # int``;

Definition varc_def:
  varc (w:'a assignment) (vc:'a varc) =
  case vc of
    INL v => w v
  | INR c => c
End

Theorem varc_INL:
  varc wi (INL y) = wi y
Proof
  rw[varc_def]
QED

Theorem varc_INR:
  varc wi (INR y) = y
Proof
  rw[varc_def]
QED

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

Type reify_cmp[pp] = ``: ('a varc # cmpop # int)``;
Type reify[pp] = ``: ('a reify_cmp + 'a reify_cmp) option``;

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

Datatype:
  counting_constr =
    (* AllEqual Xs *)
  | AllEqual ('a varc list)
    (* AllDifferentExcept Xs iS *)
  | AllDifferentExcept ('a varc list) (int list)
    (* SymmetricAllDifferent (Xs,i) *)
  | SymmetricAllDifferent ('a varc list # int)
    (* NValue Xs Y : Y is num. distinct in Xs *)
  | NValue ('a varc list) ('a varc)
    (* Count Xs Y Z : Z is num. times Y appears in Xs *)
  | Count ('a varc list) ('a varc) ('a varc)
    (* Among Xs iS Y : Y is how many times the values in iS (as set)
       appear in Xs *)
  | Among ('a varc list) (int list) ('a varc)
    (* In Xs Y: Y is in Xs *)
  | In ('a varc list) ('a varc)
    (* AtMostOne Xs Y : at most one of Xs equals the value Y *)
  | AtMostOne ('a varc list) ('a varc)
    (* GlobalCardinality Xs vs Cs clsd : for each j, count variable Cs[j]
       equals the number of Xs taking the (constant) cover value vs[j].
       clsd ⇒ every Xs[i] additionally takes some value in vs. *)
  | GlobalCardinality ('a varc list) (int list) ('a varc list) bool
End

Overload AllDifferent = ``λXs. AllDifferentExcept Xs []``;

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
  *)
End

(* NONE represents a wildcard entry for that element *)
Datatype:
  extensional_constr =
    Table ((int option) list list) ('a varc list)
    (* Regular vars nstates trans finals :
       vars (read as a value string) is accepted by the NFA with states
       0..nstates-1, start state 0, transition relation trans
       (EL q trans = list of (symbol,target) edges out of state q),
       and accepting set finals. *)
  | Regular ('a varc list) num ((int # num) list list) (num list)
End

Datatype:
  logical_constr =
    (* And Xs Y : Y > 0 ⇔ And_i (X_i > 0) *)
    And ('a varc list) ('a varc)
    (* Or Xs Y : Y > 0 ⇔ Or_i (X_i > 0) *)
  | Or ('a varc list) ('a varc)
    (* Parity Xs Y : Y > 0 ⇔ Odd number of (X_i > 0) *)
  | Parity ('a varc list) ('a varc)
End

(* The op is prefixed with "lex_", e.g.:
  lex_less_than (X Y Z) (A B C).
  We reuse the cmpop type, but there is no lex= and lex≠ *)
Datatype:
  lexicographical_constr =
    Lex ('a reify) cmpop ('a varc list) ('a varc list)
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
    (* General Knapsack *)
  | Knapsack (int list list) ('a varc list) ('a varc list)
End

(* TODO: under construction *)
Datatype:
  scheduling_constr =
    (* Disjunctive xs ws strct :
      tasks xs[i] with width ws[i], placed on a line with no overlaps.
       strct keeps zero-length tasks; otherwise they are dropped. *)
    Disjunctive ('a varc list) ('a varc list) bool
    (* Disjunctive2D xs ys ws hs strct :
      tasks (xs[i],ys[i]) with rectangle ws[i] x hs[i]
      strct keeps degenerate (zero-area) tasks/rectangles.
      Additionally, the 2D case supports general-valued ws, hs *)
  | Disjunctive2D ('a varc list) ('a varc list)
                  ('a varc list) ('a varc list) bool
    (* Cumulative xs ws hs cap :
      tasks xs[i] width width ws[i] and height hs[i].
      Height at each time point must not exceed cap *)
  | Cumulative ('a varc list) ('a varc list) ('a varc list) ('a varc)
End

Datatype:
  sorting_constr =
    (* Increasing xs strct desc :
       the sequence xs is monotone; (strct,desc) pick the adjacent comparison:
       (F,F) ≤, (T,F) <, (F,T) ≥, (T,T) >.
       Vacuously true for LENGTH xs ≤ 1. *)
    Increasing ('a varc list) bool bool
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
  | Scheduling ('a scheduling_constr)
  | Sorting ('a sorting_constr)
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
  | SOME (INL (Z,cmp,v)) => cmpop_val cmp (varc w Z) v ⇒ b
  | SOME (INR (Z,cmp,v)) => cmpop_val cmp (varc w Z) v ⇔ b
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
Definition all_equal_sem_def:
  all_equal_sem Xs w =
    ∃v. EVERY (λX. varc w X = v) Xs
End

Definition all_different_except_sem_def:
  all_different_except_sem Xs iS w =
    ALL_DISTINCT (FILTER (λv. ¬ MEM v iS) (MAP (varc w) Xs))
End

Definition symmetric_all_different_sem_def:
  symmetric_all_different_sem (Xs,start) w ⇔
  let n = LENGTH Xs in
    (* (a) every value lies in [start, start+n) *)
    EVERY (λX. start ≤ varc w X ∧ varc w X < start + &n) Xs ∧
    (* (b) self-inverse: position (Xs[i] − start) names i back *)
    (∀i. i < n ⇒
       varc w (EL (Num (varc w (EL i Xs) − start)) Xs) = &i + start)
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

Definition in_sem_def:
  in_sem Xs Y w =
  let
    y = varc w Y;
    xs = MAP (varc w) Xs
  in
    MEM y xs
End

Definition at_most_one_sem_def:
  at_most_one_sem Xs Y w ⇔
  iSUM (MAP (λX. b2i (varc w X = varc w Y)) Xs) ≤ 1
End

Definition global_cardinality_sem_def:
  global_cardinality_sem Xs vs Cs clsd w ⇔
  (* for each cover value vs[j], count variable Cs[j] holds its multiplicity *)
  LIST_REL
    (λv C. varc w C = iSUM (MAP (λX. b2i (varc w X = v)) Xs)) vs Cs ∧
  (* clsd: every variable takes some cover value *)
  (clsd ⇒ EVERY (λX. MEM (varc w X) vs) Xs)
End

Definition counting_constr_sem_def:
  counting_constr_sem c w =
  case c of
    AllEqual Xs => all_equal_sem Xs w
  | AllDifferentExcept Xs iS => all_different_except_sem Xs iS w
  | SymmetricAllDifferent p => symmetric_all_different_sem p w
  | NValue Xs Y => n_value_sem Xs Y w
  | Count Xs Y Z => count_sem Xs Y Z w
  | Among Xs iS Y => among_sem Xs iS Y w
  | In Y Xs => in_sem Y Xs w
  | AtMostOne Xs Y => at_most_one_sem Xs Y w
  | GlobalCardinality Xs vs Cs clsd => global_cardinality_sem Xs vs Cs clsd w
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

Theorem eval_iclin_term_CONS:
  eval_iclin_term w (x::xs) = eval_icterm w x + eval_iclin_term w xs
Proof
  simp[eval_iclin_term_def,iSUM_def]
QED

Theorem iSUM_MAP_lin:
  ∀ls a f b. iSUM (MAP (λx. a * f x + b) ls) = a * iSUM (MAP (λx. f x) ls) + b * &LENGTH ls
Proof
  Induct>>
  simp[iSUM_def,MAP,LENGTH]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_lin_const = iSUM_MAP_lin |> CONV_RULE (RESORT_FORALL_CONV List.rev) |> Q.SPEC `0` |> SRULE [] |> SPEC_ALL;

Theorem eval_iclin_term_MAP_neg[simp]:
  eval_iclin_term w (MAP (λ(c,X). (-c,X)) cXs) = -eval_iclin_term w cXs
Proof
  simp[eval_iclin_term_def,iSUM_def,MAP_MAP_o,o_DEF]>>
  ‘(λx. eval_icterm w ((λ(c,X). (-c,X)) x)) =
  (λx. -1 * eval_icterm w x)’ by (
    cong_tac NONE>>
    pairarg_tac>>
    gs[]>>
    intLib.ARITH_TAC)>>
  simp[iSUM_MAP_lin_const]>>
  rename1 ‘λx. f x’>>
  simp[ETA_AX]>>
  intLib.ARITH_TAC
QED

Definition lin_sem_def:
  lin_sem Zr cmp cXs Y w ⇔
  reify_sem Zr w
  (cmpop_val cmp
    (eval_iclin_term w cXs)
    (varc w Y))
End

Definition linear_constr_sem_def:
  linear_constr_sem c w ⇔
  case c of Lin Zr cmp cXs Y =>
    lin_sem Zr cmp cXs Y w
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

(* the edge list for state q is EL q trans.
  out-of-bounds qs have no transitions *)
Definition nfa_edges_def:
  nfa_edges trans q =
    if q < LENGTH trans then EL q trans else []
End

(* nfa accepts a list of values from state q;
  throughout, we check that states are valid (q < nstates)
  (v,q') is an outgoing edge from q to q' labeled v. *)
Definition nfa_accepts_def:
  (nfa_accepts trans finals nstates q [] ⇔
    q < nstates ∧ MEM q finals) ∧
  (nfa_accepts trans finals nstates q (v::vs) ⇔
     q < nstates ∧
     ∃q'. MEM (v,q') (nfa_edges trans q) ∧
          nfa_accepts trans finals nstates q' vs)
End

(* regular_sem: there exists an accepting run of the NFA over the value
   string (MAP (varc w) Xs): start in state 0, every step follows an
   edge, every state is < nstates, and the last state is accepting. *)
Definition regular_sem_def:
  regular_sem Xs nstates trans finals w ⇔
  nfa_accepts trans finals nstates 0 (MAP (varc w) Xs)
End

(* nfa_run reconstructs a canonical accepting run (proof-only, never
   translated): starting in state 0, at each index pick a successor state
   that follows an edge on the i-th value AND from which the remaining
   string is still accepted. When the string is accepted from state 0,
   such a successor always exists, so the choice (@) is meaningful. *)
Definition nfa_run_def:
  nfa_run trans finals nstates as 0 = 0 ∧
  nfa_run trans finals nstates as (SUC i) =
    @q'. MEM (EL i as, q') (nfa_edges trans (nfa_run trans finals nstates as i)) ∧
         nfa_accepts trans finals nstates q' (DROP (SUC i) as)
End

Definition extensional_constr_sem_def:
  extensional_constr_sem c w ⇔
  case c of
    Table tss Xs => table_sem tss Xs w
  | Regular Xs nstates trans finals =>
      regular_sem Xs nstates trans finals w
End

(***
  logical_constr
***)
Definition and_sem_def:
  and_sem Xs Y w =
   reify_sem (SOME (INR (Y, GreaterThan, 0))) w
    (EVERY (λX. varc w X > 0) Xs)
End

Definition or_sem_def:
  or_sem Xs Y w =
   reify_sem (SOME (INR (Y, GreaterThan, 0))) w
    (EXISTS (λX. varc w X > 0) Xs)
End

Definition parity_sem_def:
  parity_sem Xs Y w =
   reify_sem (SOME (INR (Y, GreaterThan, 0))) w
    (ODD (SUM $ MAP (λX. if varc w X > 0 then 1n else 0n) Xs))
End

Definition logical_constr_sem_def:
  logical_constr_sem c w ⇔
  case c of
    And Xs Y => and_sem Xs Y w
  | Or Xs Y => or_sem Xs Y w
  | Parity Xs Y => parity_sem Xs Y w
End

(***
  lexicographical_constr
***)

Definition row_gt_def:
  (row_gt (x::xs) (y::ys) ⇔
    (x:int) > y ∨
    (x = y) ∧ row_gt xs ys) ∧
  (row_gt [] _ ⇔ F) ∧
  (row_gt (x::xs) [] ⇔ T)
End

(* Sanity check *)
Theorem row_gt_alt:
  ∀xs ys.
  row_gt xs ys ⇔
  (∃i.
    i < LENGTH xs ∧
    i < LENGTH ys ∧
    (∀j. j < i ⇒ EL j xs = EL j ys) ∧
    EL i xs > EL i ys) ∨
  LENGTH xs > LENGTH ys ∧
  (∀j. j < LENGTH ys ⇒ EL j xs = EL j ys)
Proof
  ho_match_mp_tac row_gt_ind>>
  rw[row_gt_def]>>
  eq_tac
  >- (
    rw[]
    >- (
      DISJ1_TAC>>
      qexists_tac`0`>>simp[])
    >- (
      DISJ1_TAC>>
      qexists_tac`SUC i`>>simp[]>>
      Cases>>simp[])
    >- (
      DISJ2_TAC>>simp[]>>
      Cases>>fs[]))
  >- (
    rw[]
    >- (
      Cases_on`i`>>gvs[]>>
      DISJ2_TAC>>
      CONJ_TAC >- (
        first_x_assum (qspec_then`0` mp_tac)>>
        simp[])>>
      DISJ1_TAC>>
      first_x_assum $ irule_at Any>>
      rw[]>>
      first_x_assum(qspec_then`SUC j` mp_tac)>>simp[])>>
    DISJ2_TAC>>
    CONJ_TAC >- (
      first_x_assum (qspec_then`0` mp_tac)>>
      simp[])>>
    DISJ2_TAC>>
    rw[]>>
    first_x_assum(qspec_then`SUC j` mp_tac)>>simp[])
QED

Theorem row_ge_alt:
  ∀xs ys.
  row_gt xs ys ∨ xs = ys ⇔
  (∃i.
    i < LENGTH xs ∧
    i < LENGTH ys ∧
    (∀j. j < i ⇒ EL j xs = EL j ys) ∧
    EL i xs > EL i ys) ∨
  LENGTH xs ≥ LENGTH ys ∧
  (∀j. j < LENGTH ys ⇒ EL j xs = EL j ys)
Proof
  rw[row_gt_alt]>>
  eq_tac>>rw[]
  >- metis_tac[]
  >- (DISJ2_TAC>>simp[])
  >-  metis_tac[]
  >- (
    Cases_on`LENGTH xs > LENGTH ys`>>simp[]>>
    DISJ2_TAC>>
    fs[LIST_EQ])
QED

Definition lex_sem_def:
  lex_sem Zr cmp Xs Ys w ⇔
  let xs = MAP (varc w) Xs in
  let ys = MAP (varc w) Ys in
  case cmp of
    Equal => F (* Invalid comparison *)
  | NotEqual => F (* Invalid comparison *)
  | GreaterThan => reify_sem Zr w (row_gt xs ys)
  | GreaterEqual => reify_sem Zr w (row_gt xs ys ∨ xs = ys)
  | LessThan => reify_sem Zr w (row_gt ys xs)
  | LessEqual => reify_sem Zr w (row_gt ys xs ∨ xs = ys)
End

Definition lexicographical_constr_sem_def:
  lexicographical_constr_sem c w ⇔
  case c of Lex Zr cmp Xs Ys =>
    lex_sem Zr cmp Xs Ys w
End

(***
  channeling_constr
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
  misc_constr
***)

(*The idea of this definition:

  Writing len for LENGTH Xs, and f for indexing function (λi. Xs[i]):

  1. For X in Xs: 0 ≤ varc w X < len
  2. For i with 0 ≤ i < len and n with 0 < n < len: f^n i ≠ i

  Informally, the above formulates "for all indices i, it generates
  the entire set of indices via application of f, i.e.,

    {i, f i, f^2 i,...,f^(len-1) i} = {0,1,2,...,len-1}"

  To see this, if for some p and q with 0 < p < q < len we have
  f^p i = f^q i, then f^p i = f^q i = f^(q-p) (f^p i), contradicting 2.

*)

Definition circuit_sem_def:
  circuit_sem Xs w ⇔
  EVERY (λX. 0 ≤ varc w X ∧ Num (varc w X) < LENGTH Xs) Xs ∧
  ∀i. (i < LENGTH Xs ⇒ ∀n. 0 < n ∧ n < LENGTH Xs ⇒
    FUNPOW (λi. Num $ varc w (EL i Xs)) n i ≠ i)
End

Definition knapsack_sem_def:
  knapsack_sem css Xs ts w ⇔
  EVERY (λcs. LENGTH cs = LENGTH Xs) css ∧
  LIST_REL (λcs t. eval_iclin_term w (ZIP (cs,Xs)) = t) css (MAP (varc w) ts)
End

Definition misc_constr_sem_def:
  misc_constr_sem c w ⇔
  case c of
    Circuit Xs => circuit_sem Xs w
  | Knapsack css Xs ts => knapsack_sem css Xs ts w
End

(* Disjunctive:
    For each i, the active intervals are:

    xs[i] ≤ t < xs[i] + ws[i]

    These must be pairwise disjoint for i ≠ j.

    In strict mode, 0-length tasks cannot lie inside another interval. *)
Definition disjunctive_sem_def:
  disjunctive_sem xs ws strct w ⇔
  let xs = MAP (varc w) xs in
  let ws = MAP (varc w) ws in
  LENGTH xs = LENGTH ws ∧
  ∀i j.
    i < LENGTH xs ∧ j < LENGTH xs ∧ i ≠ j ∧
    (strct ∨ (EL i ws > 0 ∧ EL j ws > 0)) ⇒
    EL i xs + EL i ws ≤ EL j xs ∨
    EL j xs + EL j ws ≤ EL i xs
End

(* Disjunctive 2D:
    For each i, the active rectangle is:

    xs[i] ≤ tx < varc w xs[i] + ws[i]
    ys[i] ≤ ty < varc w ys[i] + hs[i]

    Same overlap requirements on area and strict flag. *)
Definition disjunctive2d_sem_def:
  disjunctive2d_sem xs ys ws hs strct w ⇔
  let xs = MAP (varc w) xs in
  let ys = MAP (varc w) ys in
  let ws = MAP (varc w) ws in
  let hs = MAP (varc w) hs in
  LENGTH xs = LENGTH ys ∧
  LENGTH xs = LENGTH ws ∧
  LENGTH xs = LENGTH hs ∧
  ∀i j.
    i < LENGTH xs ∧ j < LENGTH xs ∧ i ≠ j ∧
    (strct ∨
      (EL i ws > 0 ∧ EL j ws > 0 ∧
       EL i hs > 0 ∧ EL j hs > 0)) ⇒
    EL i xs + EL i ws ≤ EL j xs ∨
    EL j xs + EL j ws ≤ EL i xs ∨
    EL i ys + EL i hs ≤ EL j ys ∨
    EL j ys + EL j hs ≤ EL i ys
End

(* Cumulative:
  For each time point t,
    the sum of hs[i] for active tasks (xs[i] ≤ t < xs[i] + ws[i])
    is ≤ cap

  Well-formedness good default: heights and capacity must be
  non-negative (a negative demand/capacity makes the constraint
  infeasible, matching gcs which rejects these at validation).
  Durations need no guard: a non-positive ws[i] yields an empty
  occupancy interval, so the task is simply never active. *)
Definition cumulative_sem_def:
  cumulative_sem xs ws hs cap w ⇔
  let xs = MAP (varc w) xs in
  let ws = MAP (varc w) ws in
  let hs = MAP (varc w) hs in
  let cap = varc w cap in
  LENGTH xs = LENGTH ws ∧
  LENGTH xs = LENGTH hs ∧
  EVERY (λh. 0 ≤ h) hs ∧
  0 ≤ cap ∧
  ∀t.
    iSUM
      (GENLIST
        (λi.
          if EL i xs ≤ t ∧ t < EL i xs + EL i ws
          then EL i hs
          else 0
        ) (LENGTH xs)) ≤ cap
End

Definition scheduling_constr_sem_def:
  scheduling_constr_sem c w ⇔
  case c of
    Disjunctive xs ws strct =>
      disjunctive_sem xs ws strct w
  | Disjunctive2D xs ys ws hs strct =>
      disjunctive2d_sem xs ys ws hs strct w
  | Cumulative xs ws hs cap =>
      cumulative_sem xs ws hs cap w
End

(* adjacent comparison picked by (strct,desc):
   (F,F) ≤, (T,F) <, (F,T) ≥, (T,T) > *)
Definition inc_rel_def[simp]:
  inc_rel strct desc (x:int) y =
  if desc then (if strct then x > y else x ≥ y)
  else (if strct then x < y else x ≤ y)
End

Definition increasing_sem_def:
  increasing_sem xs strct desc w ⇔
  SORTED (inc_rel strct desc) (MAP (varc w) xs)
End

Definition sorting_constr_sem_def:
  sorting_constr_sem c w ⇔
  case c of
    Increasing xs strct desc =>
      increasing_sem xs strct desc w
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
  | Scheduling c => scheduling_constr_sem c w
  | Sorting c => sorting_constr_sem c w
End

Definition valid_assignment_def:
  valid_assignment (bnd: 'a bounds) w ⇔
  ∀x lb ub.
    bnd x = (lb,ub) ⇒
    lb ≤ w x ∧ w x ≤ ub
End

Type constraints[pp] = ``: 'a constraint set``;

(* The syntactic problem type *)
Datatype:
  prob_type =
    Decision
  | Minimize 'a
  | Maximize 'a
  | Enumerate ('a list)
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

(* Projection of w onto the list of variables vs *)
Definition cp_proj_def:
  cp_proj vs ws = IMAGE (λw. MAP w vs) ws
End

(* We reuse the conclusion type from PBC to define the syntactic meaning of a
  CP problem.

  NoConcl, DSat, DUnsat can be used for any problem type.

  But there are special cases for:

  - OBounds, where the CP problem type must be either a maximization or
    minimization problem.

  - EEnum, where the CP problem type must also be enumeration.

  The important case is for OBounds, where it depends on the CP problem. *)
Definition cp_sem_concl_def:
  (cp_sem_concl bnd cs ty NoConcl ⇔ T) ∧
  (cp_sem_concl bnd cs ty DSat ⇔ cp_satisfiable bnd cs) ∧
  (cp_sem_concl bnd cs ty DUnsat ⇔ cp_unsatisfiable bnd cs) ∧
  (cp_sem_concl bnd cs ty (OBounds lbi ubi) ⇔
    case ty of
    | Minimize v =>
      cp_is_lb bnd cs v lbi ∧
      cp_has_ub bnd cs v ubi
    | Maximize v =>
      cp_has_lb bnd cs v lbi ∧
      cp_is_ub bnd cs v ubi
    | _ => F) ∧
  (cp_sem_concl bnd cs ty (EEnum n complete) ⇔
    case ty of
    | Enumerate vs =>
      n ≤ CARD (cp_proj vs {w | cp_sat bnd cs w}) ∧
      (complete ⇒
        CARD (cp_proj vs {w | cp_sat bnd cs w}) ≤ n)
    | _ => F)
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
- prob_ty: mlstring prob_type
*)

Type cp_inst[pp] = ``:(mlstring, int # int) alist #
  (mlstring # mlstring constraint) list # mlstring prob_type``;

(* For any unspecified variable, default to (0,0) *)
Definition bnd_lookup_def:
  bnd_lookup ls x =
    case ALOOKUP ls x of
      NONE => (0i,0i)
    | SOME v => v
End

Definition cp_inst_sem_concl_def:
  cp_inst_sem_concl (inst:cp_inst) concl ⇔
  case inst of (bnd,cs,pty) =>
    cp_sem_concl (bnd_lookup bnd) (set (MAP SND cs)) pty concl
End

Theorem FINITE_int_interval[local]:
  FINITE {i:int | lb ≤ i ∧ i ≤ ub}
Proof
  irule SUBSET_FINITE>>
  qexists_tac`IMAGE (λn. lb + &n) (count (Num (ub - lb) + 1))`>>
  CONJ_TAC >- (irule IMAGE_FINITE>>simp[])>>
  simp[SUBSET_DEF,PULL_EXISTS,IN_IMAGE,IN_COUNT]>>
  rw[]>>
  qexists_tac`Num (x - lb)`>>
  `0 ≤ x - lb` by intLib.ARITH_TAC>>
  `&Num (x - lb) = x - lb` by metis_tac[integerTheory.INT_OF_NUM]>>
  CONJ_TAC >- intLib.ARITH_TAC>>
  `Num (x - lb) ≤ Num (ub - lb)` by (
    irule integerTheory.LE_NUM_OF_INT>>intLib.ARITH_TAC)>>
  simp[]
QED

Theorem FINITE_IMAGE_MAP_valid[local]:
  (∀w. w ∈ ws ⇒ valid_assignment bnd w) ⇒
  FINITE (IMAGE (λw. MAP w vs) ws)
Proof
  Induct_on`vs`>>rw[]
  >- (
    irule SUBSET_FINITE>>
    qexists_tac`{[]}`>>simp[SUBSET_DEF]>>rw[])>>
  irule SUBSET_FINITE>>
  qexists_tac`IMAGE (λ(a,l). a::l)
    (IMAGE (λw. w h) ws CROSS IMAGE (λw. MAP w vs) ws)`>>
  CONJ_TAC >- (
    irule IMAGE_FINITE>>
    irule FINITE_CROSS>>
    reverse CONJ_TAC
    >- (first_x_assum irule>>first_assum ACCEPT_TAC)>>
    irule SUBSET_FINITE>>
    qexists_tac`{i | FST (bnd h) ≤ i ∧ i ≤ SND (bnd h)}`>>
    CONJ_TAC >- irule FINITE_int_interval>>
    simp[SUBSET_DEF,PULL_EXISTS,IN_IMAGE]>>rw[]>>
    first_x_assum drule>>rw[valid_assignment_def]>>
    first_x_assum (qspec_then`h` mp_tac)>>
    Cases_on`bnd h`>>rw[])>>
  rw[SUBSET_DEF]>>
  gvs[IN_IMAGE]>>
  qexists_tac`(w h, MAP w vs)`>>
  simp[IN_CROSS,IN_IMAGE]>>
  metis_tac[]
QED

(* The solution set is FINITE, as long as the
  bound is a function with finite support
  (here, finite support is such that the function is constant
    except on a finite set). *)
Theorem FINITE_cp_proj_cp_sat:
  FINITE (cp_proj vs {w | cp_sat bnd cs w})
Proof
  rw[cp_proj_def]>>
  irule FINITE_IMAGE_MAP_valid>>
  qexists_tac`bnd`>>
  rw[cp_sat_def]
QED

