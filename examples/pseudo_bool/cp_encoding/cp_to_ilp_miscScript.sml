(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Misc constraints are not yet implemented in the CP semantics
   (misc_constr_sem always returns T)
   These are placeholders for future work *)

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  []
End

Theorem encode_misc_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Misc c) ∧
  misc_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_misc_constr bnd c name)
Proof
  rw[encode_misc_constr_def]
QED

Theorem encode_misc_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_misc_constr bnd c name) ⇒
  misc_constr_sem c wi
Proof
  rw[encode_misc_constr_def,misc_constr_sem_def]
QED

(* Concrete encodings *)
Definition cencode_misc_constr_def:
  cencode_misc_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_misc_constr_sem:
  valid_assignment bnd wi ∧
  cencode_misc_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_misc_constr bnd c name) ec ec'
Proof
  rw[cencode_misc_constr_def,encode_misc_constr_def]>>
  simp[enc_rel_def]
QED
