(*
  Formalization of the CP to ILP phase (lexicographical constraints)
*)
Theory cp_to_ilp_lexicographical
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Lexicographical comparison: Xs lex_cmp Ys
   For Xs < Ys lexicographically:
   ∃i. (∀j < i. Xs[j] = Ys[j]) ∧ Xs[i] < Ys[i]

   This requires auxiliary variables to track the position of first difference
*)
Definition encode_lex_def:
  encode_lex bnd cmp Xs Ys =
  if LENGTH Xs ≠ LENGTH Ys then
    [false_constr]
  else
    (* Complex encoding requiring auxiliary variables for:
       1. Position of first difference
       2. All elements before that position are equal
       3. Comparison at that position *)
    [false_constr]
End

Theorem encode_lex_sem_1:
  valid_assignment bnd wi ∧
  lex_sem cmp Xs Ys wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lex bnd cmp Xs Ys)
Proof
  cheat
QED

Theorem encode_lex_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lex bnd cmp Xs Ys) ⇒
  lex_sem cmp Xs Ys wi
Proof
  cheat
QED

Definition encode_lexicographical_constr_def:
  encode_lexicographical_constr bnd c name =
  case c of Lex cmp Xs Ys =>
    encode_lex bnd cmp Xs Ys
End

Theorem encode_lexicographical_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Lexicographical c) ∧
  lexicographical_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lexicographical_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_lexicographical_constr_def,lexicographical_constr_sem_def]>>
  metis_tac[encode_lex_sem_1]
QED

Theorem encode_lexicographical_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lexicographical_constr bnd c name) ⇒
  lexicographical_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_lexicographical_constr_def,lexicographical_constr_sem_def]>>
  metis_tac[encode_lex_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_lexicographical_constr_def:
  cencode_lexicographical_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_lexicographical_constr_sem:
  valid_assignment bnd wi ∧
  cencode_lexicographical_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_lexicographical_constr bnd c name) ec ec'
Proof
  cheat
QED
