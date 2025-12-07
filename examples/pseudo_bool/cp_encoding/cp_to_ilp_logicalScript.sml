(*
  Formalization of the CP to ILP phase (logical constraints)
*)
Theory cp_to_ilp_logical
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* And constraint: Y > 0 ⇔ ∀i. Xs[i] > 0 *)
Definition encode_and_def:
  encode_and bnd Xs Y =
  [false_constr]
End

Theorem encode_and_sem_1:
  valid_assignment bnd wi ∧
  and_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_and bnd Xs Y)
Proof
  cheat
QED

Theorem encode_and_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_and bnd Xs Y) ⇒
  and_sem Xs Y wi
Proof
  cheat
QED

(* Or constraint: Y > 0 ⇔ ∃i. Xs[i] > 0 *)
Definition encode_or_def:
  encode_or bnd Xs Y =
  [false_constr]
End

Theorem encode_or_sem_1:
  valid_assignment bnd wi ∧
  or_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_or bnd Xs Y)
Proof
  cheat
QED

Theorem encode_or_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_or bnd Xs Y) ⇒
  or_sem Xs Y wi
Proof
  cheat
QED

(* Parity constraint: ODD number of Xs[i] > 0 *)
Definition encode_parity_def:
  encode_parity bnd Xs =
  [false_constr]
End

Theorem encode_parity_sem_1:
  valid_assignment bnd wi ∧
  parity_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_parity bnd Xs)
Proof
  cheat
QED

Theorem encode_parity_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_parity bnd Xs) ⇒
  parity_sem Xs wi
Proof
  cheat
QED

Definition encode_logical_constr_def:
  encode_logical_constr bnd c name =
  case c of
    And Xs Y => encode_and bnd Xs Y
  | Or Xs Y => encode_or bnd Xs Y
  | Parity Xs => encode_parity bnd Xs
End

Theorem encode_logical_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Logical c) ∧
  logical_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_logical_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_logical_constr_def,logical_constr_sem_def]
  >- metis_tac[encode_and_sem_1]
  >- metis_tac[encode_or_sem_1]
  >- metis_tac[encode_parity_sem_1]
QED

Theorem encode_logical_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_logical_constr bnd c name) ⇒
  logical_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_logical_constr_def,logical_constr_sem_def]
  >- metis_tac[encode_and_sem_2]
  >- metis_tac[encode_or_sem_2]
  >- metis_tac[encode_parity_sem_2]
QED

(* Concrete encodings *)
Definition cencode_logical_constr_def:
  cencode_logical_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_logical_constr_sem:
  valid_assignment bnd wi ∧
  cencode_logical_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_logical_constr bnd c name) ec ec'
Proof
  cheat
QED
