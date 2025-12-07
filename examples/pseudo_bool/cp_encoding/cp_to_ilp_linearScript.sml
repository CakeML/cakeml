(*
  Formalization of the CP to ILP phase (linear constraints)
*)
Theory cp_to_ilp_linear
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Linear constraint: Σ ci·Xi cmp Y *)
Definition encode_lin_def:
  encode_lin bnd Zr cmp Xs Y =
  [false_constr]
End

Theorem encode_lin_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin Zr cmp Xs Y)) ∧
  lin_sem Zr cmp Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin bnd Zr cmp Xs Y)
Proof
  cheat
QED

Theorem encode_lin_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin bnd Zr cmp Xs Y) ⇒
  lin_sem Zr cmp Xs Y wi
Proof
  cheat
QED

Definition encode_linear_constr_def:
  encode_linear_constr bnd c name =
  case c of Lin Zr cmp Xs Y =>
    encode_lin bnd Zr cmp Xs Y
End

Theorem encode_linear_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear c) ∧
  linear_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_linear_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_linear_constr_def,linear_constr_sem_def]>>
  metis_tac[encode_lin_sem_1]
QED

Theorem encode_linear_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_linear_constr bnd c name) ⇒
  linear_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_linear_constr_def,linear_constr_sem_def]>>
  metis_tac[encode_lin_sem_2]
QED

(* Concrete encodings *)
Definition cencode_linear_constr_def:
  cencode_linear_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_linear_constr_sem:
  valid_assignment bnd wi ∧
  cencode_linear_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_linear_constr bnd c name) ec ec'
Proof
  cheat
QED
