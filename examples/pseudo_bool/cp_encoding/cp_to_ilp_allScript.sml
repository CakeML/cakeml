(*
  Formalization of the CP to ILP phase (all together)
*)
Theory cp_to_ilp_all
Libs
  preamble
Ancestors
  cp cp_to_ilp
  cp_to_ilp_prim
  cp_to_ilp_counting
  cp_to_ilp_linear
  cp_to_ilp_array
  cp_to_ilp_extensional
  cp_to_ilp_logical
  cp_to_ilp_lexicographical
  cp_to_ilp_channeling
  cp_to_ilp_misc

Definition encode_constraint_def:
  encode_constraint bnd c name =
  case c of
    Prim c => encode_prim_constr bnd c name
  | Counting c => encode_counting_constr bnd c name
  | Linear c => encode_linear_constr bnd c name
  | Array c => encode_array_constr bnd c name
  | Extensional c => encode_extensional_constr bnd c name
  | Logical c => encode_logical_constr bnd c name
  | Lexicographical c => encode_lexicographical_constr bnd c name
  | Channeling c => encode_channeling_constr bnd c name
  | Misc c => encode_misc_constr bnd c name
End

Theorem encode_cp_one_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME c ∧
  constraint_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_constraint bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_constraint_def,constraint_sem_def]
  >- metis_tac[encode_prim_constr_sem_1]
  >- metis_tac[encode_counting_constr_sem_1]
  >- metis_tac[encode_linear_constr_sem_1]
  >- metis_tac[encode_array_constr_sem_1]
  >- metis_tac[encode_extensional_constr_sem_1]
  >- metis_tac[encode_logical_constr_sem_1]
  >- metis_tac[encode_lexicographical_constr_sem_1]
  >- metis_tac[encode_channeling_constr_sem_1]
  >- metis_tac[encode_misc_constr_sem_1]
QED

Theorem encode_cp_one_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_constraint bnd c name) ⇒
  constraint_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_constraint_def,constraint_sem_def]
  >- metis_tac[encode_prim_constr_sem_2]
  >- metis_tac[encode_counting_constr_sem_2]
  >- metis_tac[encode_linear_constr_sem_2]
  >- metis_tac[encode_array_constr_sem_2]
  >- metis_tac[encode_extensional_constr_sem_2]
  >- metis_tac[encode_logical_constr_sem_2]
  >- metis_tac[encode_lexicographical_constr_sem_2]
  >- metis_tac[encode_channeling_constr_sem_2]
  >- metis_tac[encode_misc_constr_sem_2]
QED

(* An actual implementation will avoid duplicates here *)
Definition encode_constraints_def:
  encode_constraints bnd cs =
  FLAT (MAP (λ(name,c). encode_constraint bnd c name) cs)
End

Theorem encode_constraints_sem_1:
  ALL_DISTINCT (MAP FST cs) ∧
  valid_assignment bnd wi ∧
  EVERY (λc. constraint_sem (SND c) wi) cs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_constraints bnd cs)
Proof
  simp[encode_constraints_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM]>>
  rw[Once EVERY_MEM,MEM_MAP]>>
  pairarg_tac>>gvs[]>>
  irule encode_cp_one_sem_1>>fs[]>>
  drule_all ALOOKUP_ALL_DISTINCT_MEM>>
  metis_tac[SND]
QED

Theorem encode_constraints_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_constraints bnd cs) ⇒
  EVERY (λc. constraint_sem (SND c) wi) cs
Proof
  simp[encode_constraints_def,EVERY_FLAT]>>
  rw[Once EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>
  simp[Once EVERY_MEM]>>
  metis_tac[encode_cp_one_sem_2,PAIR]
QED

Definition cencode_constraint_def:
  cencode_constraint bnd c name ec =
  case c of
    Prim c => cencode_prim_constr bnd c name ec
  | Counting c => cencode_counting_constr bnd c name ec
  | Linear c => cencode_linear_constr bnd c name ec
  | Array c => cencode_array_constr bnd c name ec
  | Extensional c => cencode_extensional_constr bnd c name ec
  | Logical c => cencode_logical_constr bnd c name ec
  | Lexicographical c => cencode_lexicographical_constr bnd c name ec
  | Channeling c => cencode_channeling_constr bnd c name ec
  | Misc c => cencode_misc_constr bnd c name ec
End

Theorem cencode_constraint_sem:
  valid_assignment bnd wi ∧
  cencode_constraint bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_constraint bnd c name) ec ec'
Proof
  rw[encode_constraint_def,cencode_constraint_def]>>
  gvs[AllCaseEqs()]
  >- metis_tac[cencode_prim_constr_sem]
  >- metis_tac[cencode_counting_constr_sem]
  >- metis_tac[cencode_linear_constr_sem]
  >- metis_tac[cencode_array_constr_sem]
  >- metis_tac[cencode_extensional_constr_sem]
  >- metis_tac[cencode_logical_constr_sem]
  >- metis_tac[cencode_lexicographical_constr_sem]
  >- metis_tac[cencode_channeling_constr_sem]
  >- metis_tac[cencode_misc_constr_sem]
QED

Definition cencode_constraints_def:
  cencode_constraints bnd cs ec =
    fold_cenc
      (λnc ec. cencode_constraint bnd (SND nc) (FST nc) ec)
      cs ec
End

Theorem cencode_constraints_sem:
  valid_assignment bnd wi ∧
  cencode_constraints bnd cs ec = (es,ec') ⇒
  enc_rel wi es (encode_constraints bnd cs) ec ec'
Proof
  rw[cencode_constraints_def,encode_constraints_def]>>
  irule enc_rel_fold_cenc>>
  first_x_assum $ irule_at Any>>
  rw[]>>
  pairarg_tac>>gvs[]>>
  metis_tac[cencode_constraint_sem]
QED

Theorem good_reif_init_ec:
  good_reif wb wi init_ec
Proof
  rw[good_reif_def,init_ec_def,has_ge_def,has_eq_def]
QED

Theorem cencode_constraints_thm_1:
  ALL_DISTINCT (MAP FST cs) ∧
  valid_assignment bnd wi ∧
  cencode_constraints bnd cs init_ec = (es,ec') ∧
  EVERY (λc. constraint_sem (SND c) wi) cs ⇒
  ∃wbf.
  EVERY (λx. iconstraint_sem x (wi,wbf))
    (MAP SND (append es))
Proof
  rw[EVERY_MAP]>>
  drule_all encode_constraints_sem_1>>
  strip_tac>>
  drule cencode_constraints_sem>>
  disch_then drule>>
  rw[enc_rel_def]>>
  metis_tac[good_reif_init_ec]
QED

Theorem cencode_constraints_thm_2:
  valid_assignment bnd wi ∧
  cencode_constraints bnd cs init_ec = (es,ec') ∧
  EVERY (λx. iconstraint_sem x (wi,wbf)) (MAP SND (append es)) ⇒
  EVERY (λc. constraint_sem (SND c) wi) cs
Proof
  rw[EVERY_MAP]>>
  irule encode_constraints_sem_2>>
  first_assum (irule_at Any)>>
  drule_all cencode_constraints_sem>>
  rw[enc_rel_def]>>
  first_x_assum drule>>
  impl_keep_tac >-
    simp[good_reif_init_ec]>>
  strip_tac>>
  first_x_assum drule>>
  metis_tac[]
QED

