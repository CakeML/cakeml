(*
  Formalization of the CP to ILP phase (logical constraints)
*)
Theory cp_to_ilp_logical
Libs
  preamble
Ancestors
  pbc pbc_encode cp ilp cp_to_ilp

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
  gs[iconstraint_sem_def,reify_avar_def,reify_reif_def,
    eval_lin_term_def,MAP_MAP_o,o_ABS_R,cmpop_val_def]>>
  pop_assum mp_tac>>
  pure_rewrite_tac[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”]>>
  qmatch_goalsub_abbrev_tac ‘-b * c + a ≥ 0’>>
  strip_tac>>
  ‘a ≥ b * c’ suffices_by intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  Cases_on ‘varc wi Y ≥ 1’>>
  gs[EVERY_MEM,EXISTS_MEM,cmpop_val_def]
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
  simp[intLib.ARITH_PROVE “(v:int) > 0 ⇔ v ≥ 1”,cmpop_val_def]>>
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
  rw[encode_or_def,encode_or_aux_def,or_sem_def,reify_sem_def,cmpop_val_def]
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
  rw[encode_or_def,encode_or_aux_def,or_sem_def,reify_sem_def,EVERY_FLAT,cmpop_val_def]>>
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

(* encodes that the values of the Boolean variables X and Y are equal *)
Definition encode_bvar_eq_def:
  encode_bvar_eq X Y =
  [
    ([], [(1, Pos X);(-1, Pos Y)], 0);
    ([], [(1, Pos Y);(-1, Pos X)], 0)
  ]
End

Theorem encode_bvar_eq_sem[simp]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_bvar_eq X Y) ⇔
  wb X = wb Y
Proof
  simp[encode_bvar_eq_def,iconstraint_sem_def]>>
  Cases_on‘wb X’>>
  Cases_on‘wb Y’>>
  fs[]
QED

(* encodes that the values of the Boolean variables X, Y and Z satisfy:
   X xor Y = Z
*)
Definition encode_xor_def:
  encode_xor X Y Z =
  [
    ([],[(1,Pos X);(1,Pos Y);(1,Neg Z)], 1);
    ([],[(1,Neg X);(1,Neg Y);(1,Neg Z)], 1);
    ([],[(1,Neg X);(1,Pos Y);(1,Pos Z)], 1);
    ([],[(1,Pos X);(1,Neg Y);(1,Pos Z)], 1)
  ]
End

Theorem encode_xor_sem[simp]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_xor X Y Z) ⇔
  wb Z = (wb X ≠ wb Y)
Proof
  simp[encode_xor_def,iconstraint_sem_def]>>
  Cases_on‘wb X’>>
  Cases_on‘wb Y’>>
  Cases_on‘wb Z’>>
  fs[]
QED

(* Parity constraint: Y > 0 ⇔ ODD number of Xs[i] > 0 *)
Definition cencode_parity_aux_def:
  cencode_parity_aux bnd Y Xs name =
  Append
    (Append
      (List [(SOME $ mk_name name $ strlit"acc",
        [], [(-1,Pos (arri name $ LENGTH Xs))], 0)])
      (List $ mk_annotate
        [
          mk_name name (int_to_string #"-" 0 ^ strlit"ge");
          mk_name name (int_to_string #"-" 0 ^ strlit"le")
        ]
        (encode_bvar_eq (INL (Ge Y 1)) (arri name 0))))
    (flat_app $ MAPi
      (λi X. List $
        mk_annotate
          [
            mk_name name (int_to_string #"-" (&i+1) ^ strlit",(0,0)");
            mk_name name (int_to_string #"-" (&i+1) ^ strlit",(1,1)");
            mk_name name (int_to_string #"-" (&i+1) ^ strlit",(1,0)");
            mk_name name (int_to_string #"-" (&i+1) ^ strlit",(0,1)")
          ]
          (encode_xor (arri name i) (INL (Ge X 1)) (arri name (i+1)))
      )
      Xs)
End

Definition encode_parity_aux_def:
  encode_parity_aux bnd Y Xs name =
  abstr $ cencode_parity_aux bnd Y Xs name
End

Definition encode_parity_def:
  encode_parity bnd Xs Y name =
  FLAT (MAP (λX. encode_ge bnd X 1) (Y::Xs)) ++
  encode_parity_aux bnd Y Xs name
End

Definition cencode_parity_def:
  cencode_parity bnd Xs Y name ec =
  let
    (xs,ec') = fold_cenc (λX ec. cencode_ge bnd X 1 ec) (Y::Xs) ec
  in
    (Append xs (cencode_parity_aux bnd Y Xs name),ec')
End

(**
Y            = x[name][0]
             /
X0     - XOR = x[name][1]
             /
X1     - XOR = x[name][2]
             /
      ...
             /
X(n-1) - XOR = x[name][n]
**)

Theorem encode_parity_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Logical (Parity Xs Y)) ∧
  parity_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_parity bnd Xs Y name)
Proof
  rw[parity_sem_def,encode_parity_def,reify_sem_def,cmpop_val_def]
  >-simp[reify_avar_def,reify_reif_def]
  >-simp[EVERY_FLAT,EVERY_MAP,reify_avar_def,reify_reif_def]>>
  simp[encode_parity_aux_def,cencode_parity_aux_def,iconstraint_sem_def]>>
  rpt CONJ_TAC
  >-(
    simp[reify_avar_def,reify_flag_def]>>
    rename1‘if ODD s then _ else _’>>
    simp[ODD_EVEN,EVEN_ADD]>>
    Cases_on‘EVEN s’>>
    fs[])
  >-(
    simp[reify_avar_def,reify_reif_def,reify_flag_def,
      intLib.ARITH_PROVE“(a:int) ≥ 1 ⇔ a > 0”]>>
    rename1‘if b then _ else _’>>
    Cases_on‘b’>>
    fs[])
  >-(
    simp[EVERY_FLAT,o_ABS_R]>>
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    simp[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
    rw[Abbr‘P’]>>
    simp[reify_avar_def,reify_reif_def,reify_flag_def,
      TAKE_EL_SNOC,MAP_SNOC,SNOC_APPEND,SUM_APPEND,
      intLib.ARITH_PROVE“(a:int) ≥ 1 ⇔ a > 0”]>>
    rename1‘ODD (s + (b1 + if b2 then _ else _)) ⇔ _’>>
    Cases_on‘b2’>>
    simp[ODD_EVEN,EVEN_ADD]>>
    metis_tac[])
QED

Theorem encode_parity_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_parity bnd Xs Y name) ⇒
  parity_sem Xs Y wi
Proof
  rw[parity_sem_def,reify_sem_def,cmpop_val_def]>>
  ‘EVEN (SUM (MAP
    (λX. if varc wi X > 0 then 1 else 0)
    (Y::Xs)))’ suffices_by (
    fs[SUM,EVEN_ADD,ODD_EVEN]>>
    rename1‘if b then _ else _’>>
    Cases_on‘b’>>
    fs[])>>
  pop_assum mp_tac>>
  pure_rewrite_tac[intLib.ARITH_PROVE“(a:int) > 0 ⇔ a ≥ 1”]>>
  qmatch_goalsub_abbrev_tac‘EVEN s’>>
  simp[encode_parity_def,EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac‘EVERY P (MAP _ _)’>>
  simp[EVERY_MAP,EVERY_MEM]>>
  rw[Abbr‘P’]>>
  unabbrev_all_tac>>
  ‘EVEN (SUM (MAP
    (λX. if (wb (INL (Ge X 1))) then 1 else 0)
    (Y::Xs)))’ suffices_by (fs[SUM]>>pop_assum mp_tac>>simp[Cong MAP_CONG])>>
  pop_assum mp_tac>>
  qmatch_goalsub_abbrev_tac‘EVEN s’>>
  simp[encode_parity_aux_def,cencode_parity_aux_def,EVERY_FLAT,o_ABS_R]>>
  qmatch_goalsub_abbrev_tac‘EVERY P (MAPi _ _)’>>
  simp[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  simp[Abbr‘P’,iconstraint_sem_def]>>
  rw[]>>
  ‘¬wb (INR (Index name (LENGTH Xs)))’ by (
    qmatch_asmsub_abbrev_tac‘b2i b’>>Cases_on‘b’>>fs[])>>
  ‘∀m. m ≤ LENGTH Xs ⇒
    wb (INR (Index name m)) =
    ODD (SUM (MAP
      (λX. if wb (INL (Ge X 1)) then 1 else 0)
      (TAKE (m+1) (Y::Xs))))’ by (
    Induct_on‘m’
    >-(simp[]>>rename1‘if b then _ else _’>>Cases_on‘b’>>fs[])>>
    simp[ADD1]>>
    strip_tac>>
    simp[TAKE_EL_SNOC,MAP_SNOC]>>
    simp[SNOC_APPEND,SUM_APPEND]>>
    simp[ODD_EVEN,EVEN_ADD]>>
    qmatch_goalsub_abbrev_tac‘((P ⇎ Q) ⇔ R) ⇔ _’>>
    Cases_on‘R’>>
    fs[]>>
    metis_tac[])>>
  pop_assum $ qspec_then‘LENGTH Xs’ mp_tac>>
  ‘TAKE (LENGTH Xs + 1) (Y::Xs) = Y::Xs’ by simp[TAKE_LENGTH_ID]>>
  pop_assum (fn thm => pure_rewrite_tac[thm])>>
  qmatch_goalsub_abbrev_tac‘ODD t’>>
  simp[EVEN_ODD]
QED

Theorem cencode_parity_sem:
  valid_assignment bnd wi ∧
  cencode_parity bnd Xs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_parity bnd Xs Y name) ec ec'
Proof
  rw[cencode_parity_def,encode_parity_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  fs[fold_cenc_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule_at Any enc_rel_Append>>
  irule_at Any enc_rel_encode_ge>>
  simp[]>>
  irule_at Any enc_rel_fold_cenc>>
  pop_assum $ irule_at Any>>
  simp[enc_rel_encode_ge]>>
  simp[encode_parity_aux_def,enc_rel_abstr]
QED

Definition encode_logical_constr_def:
  encode_logical_constr bnd c name =
  case c of
    And Xs Y => encode_and bnd Xs Y
  | Or Xs Y => encode_or bnd Xs Y
  | Parity Xs Y => encode_parity bnd Xs Y name
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
  | Parity Xs Y => cencode_parity bnd Xs Y name ec
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
  >- metis_tac[cencode_parity_sem]
QED
