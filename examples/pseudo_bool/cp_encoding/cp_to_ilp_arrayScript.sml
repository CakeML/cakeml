(*
  Formalization of the CP to ILP phase (array constraints)
*)
Theory cp_to_ilp_array
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Element: Xs[Y - offset] = Z *)
Definition encode_element_def:
  encode_element bnd Xs Yi Z =
  [false_constr]
End

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem Xs Yi Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element bnd Xs Yi Z)
Proof
  cheat
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element bnd Xs Yi Z) ⇒
  element_sem Xs Yi Z wi
Proof
  cheat
QED

(* Element2D: Xss[Y1 - offset1][Y2 - offset2] = Z *)
Definition encode_element2d_def:
  encode_element2d bnd Xss Y1i Y2i Z =
  [false_constr]
End

Theorem encode_element2d_sem_1:
  valid_assignment bnd wi ∧
  element2d_sem Xss Y1i Y2i Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element2d bnd Xss Y1i Y2i Z)
Proof
  cheat
QED

Theorem encode_element2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element2d bnd Xss Y1i Y2i Z) ⇒
  element2d_sem Xss Y1i Y2i Z wi
Proof
  cheat
QED

(* ArrayMax: Y = max(Xs) *)
Definition encode_array_max_def:
  encode_array_max bnd Xs Y =
  [false_constr]
End

Theorem encode_array_max_sem_1:
  valid_assignment bnd wi ∧
  array_max_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_max bnd Xs Y)
Proof
  cheat
QED

Theorem encode_array_max_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_max bnd Xs Y) ⇒
  array_max_sem Xs Y wi
Proof
  cheat
QED

(* ArrayMin: Y = min(Xs) *)
Definition encode_array_min_def:
  encode_array_min bnd Xs Y =
  [false_constr]
End

Theorem encode_array_min_sem_1:
  valid_assignment bnd wi ∧
  array_min_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_min bnd Xs Y)
Proof
  cheat
QED

Theorem encode_array_min_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_min bnd Xs Y) ⇒
  array_min_sem Xs Y wi
Proof
  cheat
QED

Definition encode_array_constr_def:
  encode_array_constr bnd c name =
  case c of
    Element Xs Yi Z => encode_element bnd Xs Yi Z
  | Element2D Xss Y1i Y2i Z => encode_element2d bnd Xss Y1i Y2i Z
  | ArrayMax Xs Y => encode_array_max bnd Xs Y
  | ArrayMin Xs Y => encode_array_min bnd Xs Y
End

Theorem encode_array_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array c) ∧
  array_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_1]
  >- metis_tac[encode_element2d_sem_1]
  >- metis_tac[encode_array_max_sem_1]
  >- metis_tac[encode_array_min_sem_1]
QED

Theorem encode_array_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_constr bnd c name) ⇒
  array_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_2]
  >- metis_tac[encode_element2d_sem_2]
  >- metis_tac[encode_array_max_sem_2]
  >- metis_tac[encode_array_min_sem_2]
QED

(* Concrete encodings *)
Definition cencode_array_constr_def:
  cencode_array_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_array_constr_sem:
  valid_assignment bnd wi ∧
  cencode_array_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_array_constr bnd c name) ec ec'
Proof
  cheat
QED
