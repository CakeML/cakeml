(*
  Formalization of the CP to ILP phase (channeling constraints)
*)
Theory cp_to_ilp_channeling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Inverse: Xs and Ys are inverse permutations
   Xs[i] = j ⇔ Ys[j] = i
   This is very complex as it involves bidirectional constraints
*)
Definition encode_inverse_def:
  encode_inverse bnd Xsi Ysi =
  let (Xs,offx) = Xsi in
  let (Ys,offy) = Ysi in
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then
    [false_constr]
  else
    (* Bounds constraints *)
    MAP (λX. mk_constraint_ge 1 X (-1) (INR offy) 0) Xs ++
    MAP (λX. mk_constraint_ge (-1) X (1) (INR (offy + &n)) (-1)) Xs ++
    MAP (λY. mk_constraint_ge 1 Y (-1) (INR offx) 0) Ys ++
    MAP (λY. mk_constraint_ge (-1) Y (1) (INR (offx + &n)) (-1)) Ys ++
    (* Channeling constraints: Xs[i] = j ⇔ Ys[j] = i
       This requires complex encoding with element constraints *)
    [false_constr]
End

Theorem encode_inverse_sem_1:
  valid_assignment bnd wi ∧
  inverse_sem Xsi Ysi wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_inverse bnd Xsi Ysi)
Proof
  cheat
QED

Theorem encode_inverse_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_inverse bnd Xsi Ysi) ⇒
  inverse_sem Xsi Ysi wi
Proof
  cheat
QED

Definition encode_channeling_constr_def:
  encode_channeling_constr bnd c name =
  case c of Inverse Xsi Ysi =>
    encode_inverse bnd Xsi Ysi
End

Theorem encode_channeling_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Channeling c) ∧
  channeling_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_channeling_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_1]
QED

Theorem encode_channeling_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_channeling_constr bnd c name) ⇒
  channeling_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_channeling_constr_def:
  cencode_channeling_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_channeling_constr_sem:
  valid_assignment bnd wi ∧
  cencode_channeling_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_channeling_constr bnd c name) ec ec'
Proof
  cheat
QED
