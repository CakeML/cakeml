open arithmeticTheory;

Definition divides_def:
  divides a b = ∃x. b = a * x
End

set_fixity "divides" (Infix(NONASSOC,450));

Definition prime_def:
  prime p ⇔ p ≠ 1 ∧ ∀x. x divides p ⇒ (x=1) ∨ (x=p)
End

DB.find"divides";
DB.match ["arithmetic"] “x=0 ∨ x'=0”;

Theorem divisibility:
  ∀x. x divides 0
Proof
  rw[divides_def]
  \\ qexists_tac ‘0’
  \\ rw[]
QED
        
