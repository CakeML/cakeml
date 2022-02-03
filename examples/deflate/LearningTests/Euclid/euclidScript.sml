(*
  Example from Tutorial
*)

open arithmeticTheory;
 
Definition divides_def:
  divides a b = ∃x. b = a * x
End

set_fixity "divides" (Infix(NONASSOC,450));

Definition prime_def:
  prime p ⇔ p ≠ 1 ∧ ∀x. x divides p ⇒ (x=1) ∨ (x=p)
End

Theorem DIVIDES_0:
  ∀x. x divides 0
Proof
  rw[divides_def]
  \\ qexists_tac ‘0’
  \\ rw[]
QED

Theorem DIVIDES_ZERO:
  ∀x. 0 divides x ⇔ (x = 0)
Proof
  metis_tac [divides_def, MULT_CLAUSES]
QED

Theorem DIVIDES_ONE:
  ∀x. x divides 1 ⇔ (x = 1)
Proof
  metis_tac [divides_def, MULT_CLAUSES, MULT_EQ_1]
QED

Theorem DIVIDES_REFL:
  ∀x. x divides x
Proof
  metis_tac [divides_def, MULT_CLAUSES]
QED

Theorem DIVIDES_TRANS:
  ∀a b c. a divides b ∧ b divides c ⇒ a divides c
Proof
  metis_tac [divides_def, MULT_ASSOC]
QED

Theorem DIVIDES_ADD:
  ∀d a b. d divides a ∧ d divides b ⇒ d divides (a+b)
Proof
  metis_tac [divides_def, LEFT_ADD_DISTRIB]
QED

Theorem DIVIDES_SUB:
  ∀d a b. d divides a ∧ d divides b ⇒ d divides (a-b)
Proof
  metis_tac [divides_def, LEFT_SUB_DISTRIB]
QED

Theorem DIVIDES_ADDL:
  ∀d a b. d divides a ∧ d divides (a+b) ⇒ d divides b
Proof
  metis_tac [ADD_SUB, ADD_SYM, DIVIDES_SUB]
QED

Theorem DIVIDES_LMUL:
  ∀d a x. d divides a ⇒ d divides (x*a)
Proof
  metis_tac [divides_def, MULT_ASSOC, MULT_SYM]
QED

Theorem DIVIDES_RMUL:
  ∀d a x. d divides a ⇒ d divides (a*x)
Proof
  metis_tac [MULT_SYM, DIVIDES_LMUL]
QED

Theorem DIVIDES_LE:
  ∀m n. m divides n ⇒ m <= n ∨ (n=0)
Proof
  rw[divides_def]
  \\ rw[]
QED

(*
Theorem DIVIDES_FACT:
  ∀m n. 0 < m ∧ m ≤ n ⇒ m divides (FACT n)
Proof
  ‘∀m p. 0 < m ==> m divides (FACT(m+p))’ suffices_by metis_tac[LESS_EQ_EXISTS]
  \\ Induct_on ‘p’
  \\ rw[FACT, ADD_CLAUSES, DIVIDES_RMUL]
  \\ Cases_on ‘m’
  \\ fs[FACT, DIVIDES_LMUL, DIVIDES_REFL]
QED
*)

Theorem DIVIDES_FACT:
  ∀m n. 0 < m ∧ m ≤ n ⇒ m divides (FACT n)
Proof
  Induct_on ‘n - m’
  \\ rw[]
  >- (‘m = n’ by rw[]
      \\ ‘∃k. m = SUC k’ by (Cases_on ‘m’ \\ fs[])
      \\ metis_tac [FACT, DIVIDES_RMUL, DIVIDES_REFL])
  >- (‘0 < n’ by rw[]
      \\ ‘∃k. n = SUC k’ by (Cases_on ‘n’ \\ fs[])
      \\ rw[FACT,DIVIDES_RMUL])
QED

Theorem NOT_PRIME_0:
  ~prime 0
Proof
  rw[prime_def, DIVIDES_0]
QED

Theorem NOT_PRIME_1:
  ~prime 1
Proof
  rw[prime_def]
QED
        
Theorem PRIME_2:
  prime 2
Proof
  rw[prime_def]
  \\ drule DIVIDES_LE
  \\ simp[]           
  \\ CCONTR_TAC
  \\ gvs[]
  \\ ‘x=0’ by decide_tac (* M-h M-s to reach subgoal *)
  \\ gvs[divides_def]
QED

Theorem PRIME_POS:
  ∀p. prime p ⇒ 0 < p
Proof
  Cases
  \\ rw[NOT_PRIME_0]
QED

Theorem PRIME_FACTOR:
    ∀n. ~(n = 1) ⇒ ∃p. prime p ∧ p divides n
Proof
  completeInduct_on ‘n’
  \\ rw[]
  \\ Cases_on ‘prime n’
  >- metis_tac [DIVIDES_REFL]
  >- (‘∃x. x divides n ∧ x ≠ 1 ∧ x ≠ n’ by metis_tac [prime_def]
      \\ ‘x < n ∨ (n = 0)’ by metis_tac [DIVIDES_LE, LESS_OR_EQ]
      >- metis_tac [DIVIDES_TRANS]
      >- (rw[]
          \\ metis_tac [PRIME_2, DIVIDES_0]))
QED

Theorem Euclid:
  ∀n. ∃p. n < p ∧ prime p
Proof
  spose_not_then strip_assume_tac
  \\ mp_tac (SPEC “FACT n + 1” PRIME_FACTOR)
  \\ rw [FACT_LESS, DECIDE “~(x=0) ⇔ 0<x ”]
  \\ metis_tac [NOT_PRIME_1, NOT_LESS, PRIME_POS,
               DIVIDES_FACT, DIVIDES_ADDL, DIVIDES_ONE]        
QED
