(*
  Formalization of the CP to ILP phase (sorting constraints)
*)
Theory cp_to_ilp_sorting
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* ===================================================================== *)
(* Increasing: a monotone chain over Xs. Emits one adjacent inequality   *)
(* per pair vars[i] ⋈ vars[i+1], where (strct,desc) pick ⋈ (see inc_rel).*)
(* No auxiliaries, no reification, no proof-only variables.              *)
(* Structural kin of all_equal (which emits the ≤ and ≥ halves per pair).*)
(* ===================================================================== *)

(* the adjacent comparison constraint picked by (strct,desc) *)
Definition inc_cmp_def:
  inc_cmp strct desc X Y =
  if desc then (if strct then mk_gt X Y else mk_ge X Y)
  else (if strct then mk_lt X Y else mk_le X Y)
End

Theorem inc_cmp_sem[simp]:
  iconstraint_sem (inc_cmp strct desc X Y) (wi,wb) ⇔
  inc_rel strct desc (varc wi X) (varc wi Y)
Proof
  Cases_on`desc`>>Cases_on`strct`>>rw[inc_cmp_def]>>
  intLib.ARITH_TAC
QED

(* Increasing: linear chain x0 ⋈ x1, x1 ⋈ x2, ... *)
Definition inc_chain_def:
  (inc_chain strct desc i name X [] = []) ∧
  (inc_chain strct desc i name X (Y::Ys) =
    (SOME (mk_name name (toString i)), inc_cmp strct desc X Y)::
    inc_chain strct desc (i+1) name Y Ys)
End

Definition cencode_increasing_def:
  cencode_increasing Xs strct desc name =
  case Xs of [] => Nil
  | (X::Xs) =>
    List (inc_chain strct desc 0 name X Xs)
End

Definition encode_increasing_def:
  encode_increasing Xs strct desc name =
  abstr $ cencode_increasing Xs strct desc name
End

Theorem inc_chain_sem:
  ∀Xs i name X.
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstrl (inc_chain strct desc i name X Xs)) ⇔
  SORTED (inc_rel strct desc) (varc wi X :: MAP (varc wi) Xs)
Proof
  Induct>>rw[inc_chain_def,SORTED_DEF]
QED

Theorem encode_increasing_sem_1:
  increasing_sem Xs strct desc wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_increasing Xs strct desc name)
Proof
  gs[encode_increasing_def,cencode_increasing_def,increasing_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[inc_chain_sem]
QED

Theorem encode_increasing_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_increasing Xs strct desc name) ⇒
  increasing_sem Xs strct desc wi
Proof
  gs[encode_increasing_def,cencode_increasing_def,increasing_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[inc_chain_sem]
QED

(* ===================================================================== *)
(* Category dispatch                                                     *)
(* ===================================================================== *)

Definition encode_sorting_constr_def:
  encode_sorting_constr bnd c name =
  case c of
    Increasing Xs strct desc =>
      encode_increasing Xs strct desc name
  | Sort Xs Ys => []
  | ArgSort Xs Ps offset => []
End

Definition cencode_sorting_constr_def:
  cencode_sorting_constr bnd c name ec =
  case c of
    Increasing Xs strct desc =>
      (cencode_increasing Xs strct desc name, ec)
  | Sort Xs Ys => (Nil, ec)
  | ArgSort Xs Ps offset => (Nil, ec)
End

Theorem encode_sorting_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Sorting c) ∧
  sorting_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_sorting_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_sorting_constr_def,sorting_constr_sem_def]>>
  metis_tac[encode_increasing_sem_1]
QED

Theorem encode_sorting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_sorting_constr bnd c name) ⇒
  sorting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_sorting_constr_def,sorting_constr_sem_def]
  >- metis_tac[encode_increasing_sem_2]
  >- cheat (* TODO: Sort encoding *)
  >- cheat (* TODO: ArgSort encoding *)
QED

Theorem cencode_sorting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_sorting_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_sorting_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  simp[cencode_sorting_constr_def,encode_sorting_constr_def,
    cencode_increasing_def,encode_increasing_def]
QED
