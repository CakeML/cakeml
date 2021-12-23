(*
  Formalisation of (un-normalised) pseudo-boolean constraints
*)

open preamble;

val _ = new_theory "pb_preconstraint";

val _ = numLib.prefer_num();

(* TODO: Possibly use mlstring, but need to check how it is supported in PBP *)
Type var = “:num”

Datatype:
  lit = Pos var | Neg num
End

(*
  Un-normalised pseudo-boolean constraints have the form:
  c_i l_i ≥ n OR
  c_i l_i = n OR
  where coefficients c_i and n are arbitrary integers and l_i are literals
*)
Datatype:
  pbc =
    Equal ((int # lit) list) int
  | GreaterEqual ((int # lit) list) int
End

(* integer-valued semantics *)

Definition b2i_def[simp]:
  b2i T = 1i ∧
  b2i F = 0i
End

Definition eval_lit_def[simp]:
  eval_lit w (Pos v) =     b2i (w v) ∧
  eval_lit w (Neg v) = 1 - b2i (w v)
End

Definition eval_term_def[simp]:
  eval_term w (c,l) = c * eval_lit w l
End

Definition iSUM_def:
  (iSUM [] = 0:int) ∧
  (iSUM (x::xs) = x + iSUM xs)
End

Definition eval_lhs_def[simp]:
  eval_lhs w xs = iSUM (MAP (eval_term w) xs)
End

(* satisfaction of a pseudoboolean constraint *)
Definition satisfies_pbc_def:
  (satisfies_pbc w (Equal xs n) ⇔ eval_lhs w xs = n) ∧
  (satisfies_pbc w (GreaterEqual xs n) ⇔ eval_lhs w xs ≥ n)
End

(* satisfaction of a set of pseudoboolean constraints *)
Definition satisfies_def:
  satisfies w pbf ⇔
  ∀c. c ∈ pbf ⇒ satisfies_pbc w c
End

Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

Theorem satisfies_simp[simp]:
  satisfies w EMPTY = T ∧
  satisfies w (c INSERT f) = (satisfies_pbc w c ∧ satisfies w f) ∧
  satisfies w (f ∪ h) = (satisfies w f ∧ satisfies w h)
Proof
  fs [satisfies_def] \\
  metis_tac []
QED

(* Convert a list of pbc to one with ≥ constraints only *)
Definition pbc_ge_def:
  (pbc_ge (GreaterEqual xs n) = [GreaterEqual xs n]) ∧
  (pbc_ge (Equal xs n) =
    let xs' = MAP (λ(c:int,l). (-c,l)) xs in
      [GreaterEqual xs n; GreaterEqual xs' (-n)])
End

Theorem eq_disj:
  (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b
Proof
  metis_tac[]
QED

Theorem eval_term_negate:
  ∀ls.
  (MAP (eval_term w) (MAP (λ(c,l). (-c,l)) ls)) =
  (MAP (\i. -i) (MAP (eval_term w) ls))
Proof
  Induct>>simp[]>>
  Cases>>rw[eval_term_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_negate:
  ∀ls. iSUM (MAP (\i. -i) ls) = -iSUM ls
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem pbc_ge_thm:
  ∀c.
  satisfies w (set (pbc_ge c)) ⇔
  satisfies_pbc w c
Proof
  Cases>>
  simp[pbc_ge_def,satisfies_def]>>
  rw[EQ_IMP_THM]
  >- (
    fs[satisfies_pbc_def,eq_disj,eval_term_negate,iSUM_negate]>>
    intLib.ARITH_TAC) >>
  fs[satisfies_pbc_def,eval_term_negate,iSUM_negate]>>
  intLib.ARITH_TAC
QED

val _ = export_theory();
