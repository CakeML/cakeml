(*
  Formalization of the CP to ILP phase (logical constraints)
*)
Theory cp_to_ilp_logical
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* And constraint: Y > 0 ⇔ ∀i. Xs[i] > 0 *)
Definition encode_and_aux_def:
  encode_and_aux bnd Xs Y =
  [
    ([], (-&LENGTH Xs, Pos (INL (Ge Y 1))) :: MAP (λX. (1, Pos (INL (Ge X 1)))) Xs, 0);
    ([], (-1, Neg (INL (Ge Y 1))) :: MAP (λX. (1, Neg (INL (Ge X 1)))) Xs, 0)
  ]
End

Definition encode_and_def:
  encode_and bnd Xs Y =
  FLAT (MAP (λX. encode_ge bnd X 1) Xs) ++
  encode_ge bnd Y 1 ++
  encode_and_aux bnd Xs Y
End

Theorem encode_and_sem_1:
  valid_assignment bnd wi ∧
  and_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_and bnd Xs Y)
Proof
  rw[encode_and_def,encode_and_aux_def,and_sem_def,reify_sem_def]
  >-simp[EVERY_FLAT,EVERY_MAP,reify_avar_def,reify_reif_def]
  >-simp[reify_avar_def,reify_reif_def]>>
  simp[iconstraint_sem_def,reify_avar_def,reify_reif_def,
    eval_lin_term_def,MAP_MAP_o,o_ABS_R]>>
  pop_assum mp_tac>>
  pure_rewrite_tac[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”]>>
  qmatch_goalsub_abbrev_tac ‘-b * c + a ≥ 0’>>
  strip_tac>>
  ‘a ≥ b * c’ suffices_by intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  Cases_on ‘varc wi Y ≥ 1’>>
  gs[EVERY_MEM,EXISTS_MEM]
  >~[‘∃X. MEM X _ ∧ ¬(varc _ X ≥ _)’]
  >-metis_tac[]>>
  irule pbc_encodeTheory.iSUM_ge_0>>
  simp[MEM_MAP,SF DNF_ss,pbc_encodeTheory.b2i_ge_0]
QED

Theorem encode_and_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_and bnd Xs Y) ⇒
  and_sem Xs Y wi
Proof
  rw[encode_and_def,encode_and_aux_def,and_sem_def,reify_sem_def,EVERY_FLAT]>>
  qmatch_asmsub_abbrev_tac ‘EVERY P (MAP _ _)’>>
  fs[EVERY_MAP,EVERY_MEM]>>
  gs[Abbr‘P’,iconstraint_sem_def,eval_lin_term_def,MAP_MAP_o,o_ABS_R]>>
  simp[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”]>>
  Cases_on ‘varc wi Y ≥ 1’>>
  gvs[]>>
  qmatch_asmsub_abbrev_tac ‘-b + a ≥ 0’>>
  ‘a ≥ b’ by intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  qmatch_asmsub_abbrev_tac ‘f Y ≥ 1’
  >-(
    gs[cp_to_ilpTheory.iSUM_MAP_b2i_ge_LENGTH]>>
    metis_tac[])
  >-(
    gs[cp_to_ilpTheory.iSUM_MAP_b2i_ge_1]>>
    metis_tac[])
QED

Definition cencode_and_aux_def:
  cencode_and_aux bnd Xs Y name =
  List $ mk_annotate
    [mk_name name $ strlit"pos"; mk_name name $ strlit"neg"]
    (encode_and_aux bnd Xs Y)
End

Definition cencode_and_def:
  cencode_and bnd Xs Y name ec =
  let
    (xs,ec') = fold_cenc (λX ec. cencode_ge bnd X 1 ec) Xs ec;
    (xs',ec'') = cencode_ge bnd Y 1 ec'
  in
    (Append
      (Append xs xs')
      (cencode_and_aux bnd Xs Y name),
    ec'')
End

Theorem cencode_and_sem:
  valid_assignment bnd wi ∧
  cencode_and bnd Xs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_and bnd Xs Y) ec ec'
Proof
  rw[cencode_and_def,encode_and_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_Append>>
  rename1 ‘cencode_ge _ _ _ ec''’>>
  qexists ‘ec''’>>
  qexists ‘ec'’>>
  CONJ_TAC
  >-(
    qmatch_goalsub_abbrev_tac ‘MAP f _’>>
    qmatch_asmsub_abbrev_tac ‘fold_cenc cf _ _’>>
    irule enc_rel_fold_cenc>>
    qexists ‘cf’>>
    simp[Abbr ‘f’,Abbr ‘cf’]>>
    simp[enc_rel_encode_ge])>>
  CONJ_TAC
  >-simp[enc_rel_encode_ge]>>
  simp[cencode_and_aux_def,encode_and_aux_def,enc_rel_List_refl_mul]
QED

(* Or constraint: Y > 0 ⇔ ∃i. Xs[i] > 0 *)
Definition encode_or_aux_def:
  encode_or_aux bnd Xs Y =
  [
    ([], (-1, Pos (INL (Ge Y 1))) :: MAP (λX. (1, Pos (INL (Ge X 1)))) Xs, 0);
    ([], (-&LENGTH Xs, Neg (INL (Ge Y 1))) :: MAP (λX. (1, Neg (INL (Ge X 1)))) Xs, 0)
  ]
End

Definition encode_or_def:
  encode_or bnd Xs Y =
  FLAT (MAP (λX. encode_ge bnd X 1) Xs) ++
  encode_ge bnd Y 1 ++
  encode_or_aux bnd Xs Y
End

Theorem encode_or_sem_1:
  valid_assignment bnd wi ∧
  or_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_or bnd Xs Y)
Proof
  rw[encode_or_def,encode_or_aux_def,or_sem_def,reify_sem_def]
  >-simp[EVERY_FLAT,EVERY_MAP,reify_avar_def,reify_reif_def]
  >-simp[reify_avar_def,reify_reif_def]>>
  simp[iconstraint_sem_def,reify_avar_def,reify_reif_def,
    eval_lin_term_def,MAP_MAP_o,o_ABS_R]>>
  pop_assum mp_tac>>
  pure_rewrite_tac[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”]>>
  qmatch_goalsub_abbrev_tac ‘-b * c + a ≥ 0’>>
  strip_tac>>
  ‘a ≥ b * c’ suffices_by intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  Cases_on ‘varc wi Y ≥ 1’>>
  gs[EVERY_MEM,EXISTS_MEM]
  >~[‘∃X. MEM X _ ∧ varc _ X ≥ _’]
  >-metis_tac[]
  >~[‘∀X. MEM X _ ⇒ ¬(varc _ X ≥ _)’]
  >-metis_tac[]>>
  irule pbc_encodeTheory.iSUM_ge_0>>
  simp[MEM_MAP,SF DNF_ss,pbc_encodeTheory.b2i_ge_0]
QED

Theorem encode_or_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_or bnd Xs Y) ⇒
  or_sem Xs Y wi
Proof
  rw[encode_or_def,encode_or_aux_def,or_sem_def,reify_sem_def,EVERY_FLAT]>>
  qmatch_asmsub_abbrev_tac ‘EVERY P (MAP _ _)’>>
  fs[EVERY_MAP,EVERY_MEM]>>
  gs[Abbr‘P’,iconstraint_sem_def,eval_lin_term_def,MAP_MAP_o,o_ABS_R]>>
  simp[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”]>>
  Cases_on ‘varc wi Y ≥ 1’>>
  gvs[]>>
  qmatch_asmsub_abbrev_tac ‘-b + a ≥ 0’>>
  ‘a ≥ b’ by intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  qmatch_asmsub_abbrev_tac ‘f Y ≥ 1’
  >-(
    gs[EXISTS_MEM]>>
    metis_tac[])
  >-gs[EVERY_MEM]
QED

Definition cencode_or_aux_def:
  cencode_or_aux bnd Xs Y name =
  List $ mk_annotate
    [mk_name name $ strlit"pos"; mk_name name $ strlit"neg"]
    (encode_or_aux bnd Xs Y)
End

Definition cencode_or_def:
  cencode_or bnd Xs Y name ec =
  let
    (xs,ec') = fold_cenc (λX ec. cencode_ge bnd X 1 ec) Xs ec;
    (xs',ec'') = cencode_ge bnd Y 1 ec'
  in
    (Append
      (Append xs xs')
      (cencode_or_aux bnd Xs Y name),
    ec'')
End

Theorem cencode_or_sem:
  valid_assignment bnd wi ∧
  cencode_or bnd Xs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_or bnd Xs Y) ec ec'
Proof
  rw[cencode_or_def,encode_or_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_Append>>
  rename1 ‘cencode_ge _ _ _ ec''’>>
  qexists ‘ec''’>>
  qexists ‘ec'’>>
  CONJ_TAC
  >-(
    qmatch_goalsub_abbrev_tac ‘MAP f _’>>
    qmatch_asmsub_abbrev_tac ‘fold_cenc cf _ _’>>
    irule enc_rel_fold_cenc>>
    qexists ‘cf’>>
    simp[Abbr ‘f’,Abbr ‘cf’]>>
    simp[enc_rel_encode_ge])>>
  CONJ_TAC
  >-simp[enc_rel_encode_ge]>>
  simp[cencode_or_aux_def,encode_or_aux_def,enc_rel_List_refl_mul]
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
  case c of
  | And Xs Y => cencode_and bnd Xs Y name ec
  | Or Xs Y => cencode_or bnd Xs Y name ec
End

Theorem cencode_logical_constr_sem:
  valid_assignment bnd wi ∧
  cencode_logical_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_logical_constr bnd c name) ec ec'
Proof
  Cases_on‘c’>>
  rw[cencode_logical_constr_def,encode_logical_constr_def]
  >- metis_tac[cencode_and_sem]
  >- metis_tac[cencode_or_sem]
  >- cheat
QED
