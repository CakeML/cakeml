(*
  Formalization of the CP to ILP phase (scheduling constraints)
*)
Theory cp_to_ilp_scheduling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Disjunctive *)
Definition cencode_disjunctive_def:
  cencode_disjunctive bnd xs ws strct name =
  (* TODO *)
  cfalse_constr
End

Definition encode_disjunctive_def:
  encode_disjunctive bnd xs ws strct name =
  abstr (cencode_disjunctive bnd xs ws strct name)
End

Theorem cencode_disjunctive_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive bnd xs ws strct name = es ⇒
  enc_rel wi es (encode_disjunctive bnd xs ws strct name) ec ec
Proof
  rw[encode_disjunctive_def]
QED

Theorem encode_disjunctive_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive xs ws strct)) ∧
  disjunctive_sem xs ws strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive bnd xs ws strct name)
Proof
  cheat
QED

Theorem encode_disjunctive_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive bnd xs ws strct name) ⇒
  disjunctive_sem xs ws strct wi
Proof
  cheat
QED

(* Disjunctive2D *)
Definition cencode_disjunctive2d_def:
  cencode_disjunctive2d bnd xs ys ws hs strct name =
  (* TODO *)
  cfalse_constr
End

Definition encode_disjunctive2d_def:
  encode_disjunctive2d bnd xs ys ws hs strct name =
  abstr (cencode_disjunctive2d bnd xs ys ws hs strct name)
End

Theorem cencode_disjunctive2d_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive2d bnd xs ys ws hs strct name = es ⇒
  enc_rel wi es (encode_disjunctive2d bnd xs ys ws hs strct name) ec ec
Proof
  rw[encode_disjunctive2d_def]
QED

Theorem encode_disjunctive2d_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive2D xs ys ws hs strct)) ∧
  disjunctive2d_sem xs ys ws hs strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive2d bnd xs ys ws hs strct name)
Proof
  cheat
QED

Theorem encode_disjunctive2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive2d bnd xs ys ws hs strct name) ⇒
  disjunctive2d_sem xs ys ws hs strct wi
Proof
  cheat
QED

(* Cumulative *)
Definition cencode_cumulative_def:
  cencode_cumulative bnd xs ws hs cap name =
  (* TODO *)
  cfalse_constr
End

Definition encode_cumulative_def:
  encode_cumulative bnd xs ws hs cap name =
  abstr (cencode_cumulative bnd xs ws hs cap name)
End

Theorem cencode_cumulative_sem:
  valid_assignment bnd wi ∧
  cencode_cumulative bnd xs ws hs cap name = es ⇒
  enc_rel wi es (encode_cumulative bnd xs ws hs cap name) ec ec
Proof
  rw[encode_cumulative_def]
QED

Theorem encode_cumulative_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Cumulative xs ws hs cap)) ∧
  cumulative_sem xs ws hs cap wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_cumulative bnd xs ws hs cap name)
Proof
  cheat
QED

Theorem encode_cumulative_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_cumulative bnd xs ws hs cap name) ⇒
  cumulative_sem xs ws hs cap wi
Proof
  cheat
QED

Definition encode_scheduling_constr_def:
  encode_scheduling_constr bnd c name =
  case c of
    Disjunctive xs ws strct =>
      encode_disjunctive bnd xs ws strct name
  | Disjunctive2D xs ys ws hs strct =>
      encode_disjunctive2d bnd xs ys ws hs strct name
  | Cumulative xs ws hs cap =>
      encode_cumulative bnd xs ws hs cap name
End

Definition cencode_scheduling_constr_def:
  cencode_scheduling_constr bnd c name ec =
  case c of
    Disjunctive xs ws strct =>
      (cencode_disjunctive bnd xs ws strct name, ec)
  | Disjunctive2D xs ys ws hs strct =>
      (cencode_disjunctive2d bnd xs ys ws hs strct name, ec)
  | Cumulative xs ws hs cap =>
      (cencode_cumulative bnd xs ws hs cap name, ec)
End

Theorem encode_scheduling_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling c) ∧
  scheduling_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_scheduling_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_scheduling_constr_def,scheduling_constr_sem_def]
  >- metis_tac[encode_disjunctive_sem_1]
  >- metis_tac[encode_disjunctive2d_sem_1]
  >- metis_tac[encode_cumulative_sem_1]
QED

Theorem encode_scheduling_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_scheduling_constr bnd c name) ⇒
  scheduling_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_scheduling_constr_def,scheduling_constr_sem_def]
  >- metis_tac[encode_disjunctive_sem_2]
  >- metis_tac[encode_disjunctive2d_sem_2]
  >- metis_tac[encode_cumulative_sem_2]
QED

Theorem cencode_scheduling_constr_sem:
  valid_assignment bnd wi ∧
  cencode_scheduling_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_scheduling_constr bnd c name) ec ec'
Proof
  cheat
QED
