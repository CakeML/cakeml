(*
  Formalization of the CP to ILP phase (counting constraints)
*)
Theory cp_to_ilp_counting
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition neiv_def[simp]:
  neiv name (i:num) j =
    INR (name, Indices [i;j] (SOME $ strlit "ne"))
End

(* AllDifferent: All variables must take distinct values
   For n variables, this requires O(n^2) pairwise inequality constraints *)
Definition encode_all_different_def:
  encode_all_different bnd Xs name =
  FLAT (MAPi (λi X.
    FLAT (MAPi (λj Y.
      if i < j then
        [
          bits_imply bnd [Pos (neiv name i j)] (mk_gt X Y);
          bits_imply bnd [Neg (neiv name i j)] (mk_gt Y X)
        ]
      else []) Xs)) Xs)
End

Theorem encode_all_different_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (AllDifferent Xs)) ∧
  all_different_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different bnd Xs name)
Proof
  rw[encode_all_different_def,all_different_sem_def,EVERY_MEM]>>
  gs[MEM_FLAT,indexedListsTheory.MEM_MAPi]>>
  Cases_on ‘i < j’>>
  gs[reify_avar_def,reify_flag_def]
  >- intLib.ARITH_TAC>>
  gvs[EL_ALL_DISTINCT_EL_EQ]>>
  cheat
QED

Theorem encode_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different bnd Xs name) ⇒
  all_different_sem Xs wi
Proof
  cheat
QED

(* NValue: Y equals the number of distinct values in Xs
   This is very complex and requires auxiliary variables *)
Definition encode_n_value_def:
  encode_n_value bnd Xs Y =
  (* TODO: Complex encoding requiring auxiliary variables
     for each potential value in the domain *)
  [false_constr]
End

Theorem encode_n_value_sem_1:
  valid_assignment bnd wi ∧
  n_value_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_n_value bnd Xs Y)
Proof
  cheat
QED

Theorem encode_n_value_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_n_value bnd Xs Y) ⇒
  n_value_sem Xs Y wi
Proof
  cheat
QED

(* Count: Z equals the number of times Y appears in Xs
   Z = Sum_i [Xs[i] = Y] *)
Definition encode_count_def:
  encode_count bnd Xs Y Z =
  (* Need to encode: Z = Sum_i (Xs[i] = Y)
     This requires equality reification for each Xs[i] = Y *)
  [false_constr]
End

Theorem encode_count_sem_1:
  valid_assignment bnd wi ∧
  count_sem Xs Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_count bnd Xs Y Z)
Proof
  cheat
QED

Theorem encode_count_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_count bnd Xs Y Z) ⇒
  count_sem Xs Y Z wi
Proof
  cheat
QED

(* Among: Y equals the number of times values from iS appear in Xs
   Y = Sum_i [Xs[i] ∈ iS] *)
Definition encode_among_def:
  encode_among bnd Xs iS Y =
  (* Need to encode: Y = Sum_i (Xs[i] ∈ iS)
     For each i, need disjunction: Xs[i] = v1 ∨ Xs[i] = v2 ∨ ... *)
  [false_constr]
End

Theorem encode_among_sem_1:
  valid_assignment bnd wi ∧
  among_sem Xs iS Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_among bnd Xs iS Y)
Proof
  cheat
QED

Theorem encode_among_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_among bnd Xs iS Y) ⇒
  among_sem Xs iS Y wi
Proof
  cheat
QED

Definition encode_counting_constr_def:
  encode_counting_constr bnd c name =
  case c of
    AllDifferent Xs => encode_all_different bnd Xs name
  | NValue Xs Y => encode_n_value bnd Xs Y
  | Count Xs Y Z => encode_count bnd Xs Y Z
  | Among Xs iS Y => encode_among bnd Xs iS Y
End

Theorem encode_counting_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting c) ∧
  counting_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_counting_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_different_sem_1]
  >- metis_tac[encode_n_value_sem_1]
  >- metis_tac[encode_count_sem_1]
  >- metis_tac[encode_among_sem_1]
QED

Theorem encode_counting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_counting_constr bnd c name) ⇒
  counting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_different_sem_2]
  >- metis_tac[encode_n_value_sem_2]
  >- metis_tac[encode_count_sem_2]
  >- metis_tac[encode_among_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_counting_constr_def:
  cencode_counting_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_counting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_counting_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_counting_constr bnd c name) ec ec'
Proof
  cheat
QED
