(*
  testestestes
*)
open preamble;

val _ = new_theory "exp";

Datatype:
  exp = Num num | Add exp exp | Sub exp exp
End

Definition sem_def:
  sem (Num n) = n ∧
  sem (Add e1 e2) = sem e1 + sem e2 ∧
  sem (Sub e1 e2) = sem e1 - sem e2
End

val example = EVAL “sem (Add (Num 3) (Sub (Num 4) (Num2)))”

Definition double_def:
  double e = Add e e
End

Theorem double_thm:
  ∀e. sem (double e) = 2 * sem e
Proof
  Induct
  >-(strip_tac
     \\ ‘double (Num n) = Add (Num n) (Num n)’ (* M-h M-s start this goal*)
       by rewrite_tac[double_def]
     \\ asm_rewrite_tac[sem_def]
     \\ simp[])
  >-(rewrite_tac[double_def,sem_def]
     \\ simp[])
  >-(rewrite_tac[double_def,sem_def]
     \\ simp[])
QED

val _ = export_theory();