(*
  Formalisation of a syntax and semantics for MILP
*)
open preamble RatProgTheory;

val _ = new_theory "milp";

val _ = numLib.prefer_num();

(* The left-hand side of a mixed linear constraint *)
Type lin_term = ``:(rat # 'a) list # (rat # 'b) list ``;

(* A valuation maps 'a to reals and 'b to integers *)
Type mix_val = ``: ('a -> real) # ('b -> int)``;

Definition rSUM_def:
  (rSUM [] = 0:real) ∧
  (rSUM (x::xs) = x + rSUM xs)
End

Definition eval_rat_term_def:
  eval_rat_term w (r:rat,x) = (real_of_rat r * w x):real
End

Definition eval_int_term_def:
  eval_int_term w (r:rat,x) = (real_of_rat r * real_of_int (w x)):real
End

Definition eval_lhs_def:
  eval_lhs
    ((w1,w2): ('a,'b) mix_val)
    ((xs,ys):('a,'b) lin_term) =
    rSUM (MAP (eval_rat_term w1) xs) +
    rSUM (MAP (eval_int_term w2) ys)
End

(*
  Constraints have the form:
  c_i l_i ≥ n
  c_i l_i = n
  c_i l_i ≤ n
*)

Datatype:
  linop = Equal | GreaterEqual | LessEqual
End

Type milc = ``:(linop # ('a,'b) lin_term # rat)``

Definition do_op_def[simp]:
  (do_op Equal (l:real) (r:real) ⇔ l = r) ∧
  (do_op GreaterEqual l r ⇔ l ≥ r) ∧
  (do_op LessEqual l r ⇔ l ≤ r)
End

(* satisfaction of a mixed integer linear constraint *)
Definition satisfies_milc_def:
  (satisfies_milc w (lop,xs,n) ⇔
    do_op lop (eval_lhs w xs) (real_of_rat n))
End

(* satisfaction of an MILP *)
Definition satisfies_def:
  satisfies w milp ⇔
  ∀c. c ∈ milp ⇒ satisfies_milc w c
End

(* Define floor and ceiling for rationals *)
Definition RAT_INT_FLOOR_def[nocompute]:
  RAT_INT_FLOOR r = INT_FLOOR (real_of_rat r)
End

Definition RAT_INT_CEILING_def[nocompute]:
  RAT_INT_CEILING r = INT_CEILING (real_of_rat r)

End

Definition RAT_is_int_def:
  RAT_is_int (x:rat) ⇔
  x = rat_of_int (RAT_INT_FLOOR x)
End

(* Computing the int floor of a rational number *)
Theorem RAT_INT_FLOOR_compute:
  RAT_INT_FLOOR r =
  RATN r / & RATD r
Proof
  rw[RAT_INT_FLOOR_def]>>
  simp[RatProgTheory.real_of_rat_def]>>
  Cases_on`RATN r`>>
  simp[]>>
  DEP_REWRITE_TAC[intrealTheory.INT_FLOOR_EQNS]>>
  simp[]
QED

Theorem real_of_int_of_rat:
  real_of_int i = real_of_rat (rat_of_int i)
Proof
  simp[real_of_rat_def]
QED

Theorem RAT_INT_CEILING_compute:
  RAT_INT_CEILING r =
  let i = RAT_INT_FLOOR r in
    if rat_of_int i = r then i else i + 1
Proof
  rw[RAT_INT_CEILING_def,RAT_INT_FLOOR_def]>>
  fs[intrealTheory.INT_CEILING_INT_FLOOR]>>
  fs[real_of_int_of_rat]
QED

(* Rounding up a constraint *)
Definition round_up_def:
  round_up ((xs,ys),n) =
  if xs = [] then
    if EVERY (λ(r,y). RAT_is_int r) ys then
      SOME (rat_of_int (RAT_INT_CEILING n))
    else NONE
  else NONE
End

Theorem INT_FLOOR_real_of_int:
  INT_FLOOR (real_of_int i) = i
Proof
  simp[intrealTheory.INT_FLOOR]
QED

Theorem rSUM_is_int:
  ∀ys.
  EVERY (λ(r,y). RAT_is_int r) ys ⇒
  is_int (rSUM (MAP (eval_int_term w) ys))
Proof
  Induct>>rw[rSUM_def]
  >-
    EVAL_TAC>>
  pairarg_tac>>fs[]>>
  fs[intrealTheory.is_int_def,RAT_is_int_def]>>
  rw[]>>
  simp[eval_int_term_def]>>
  qpat_x_assum`_ = _` SUBST_ALL_TAC>>
  qpat_x_assum`_ = _` SUBST_ALL_TAC>>
  simp[intrealTheory.INT_FLOOR_SUM, GSYM real_of_int_of_rat]>>
  REWRITE_TAC[GSYM intrealTheory.real_of_int_mul]>>
  simp[INT_FLOOR_real_of_int]
QED

Theorem le_real_of_int:
  r ≤ real_of_int i ⇒
  INT_CEILING r ≤ i
Proof
  rw[]>>
  CCONTR_TAC>>fs[integerTheory.INT_NOT_LE]>>
  `real_of_int (INT_CEILING r - 1) < r` by
    metis_tac[intrealTheory.INT_CEILING]>>
  `real_of_int (⌈r⌉ − 1) < real_of_int i` by
    metis_tac[realaxTheory.REAL_LTE_TRANS]>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem round_up_sound:
  satisfies_milc w (GreaterEqual,cs,rhs) ∧
  round_up (cs,rhs) = SOME rhs' ⇒
  satisfies_milc w (GreaterEqual,cs,rhs')
Proof
  rw[satisfies_milc_def]>>
  Cases_on`cs`>>
  fs[round_up_def]>>rw[]>>
  Cases_on`w`>>fs[eval_lhs_def,rSUM_def,realTheory.real_ge]>>
  rename1`eval_int_term w`>>
  drule rSUM_is_int >>
  disch_then(qspec_then`w` assume_tac)>>
  simp[GSYM real_of_int_of_rat]>>
  rename1`is_int ri`>>
  fs[RAT_INT_CEILING_def]>>
  fs[intrealTheory.is_int_def]>>
  pop_assum SUBST_ALL_TAC>>
  gs[]>>
  metis_tac[le_real_of_int]
QED

(* TODO: addition runs into annoying canonicalization again *)

val _ = export_theory();
