(*
  Formalization of the CP to ILP phase (linear constraints)
*)
Theory cp_to_ilp_linear
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition mk_lin_ge_def[simp]:
  mk_lin_ge cXs Y = mk_lin_constraint_ge ((-1i,Y)::cXs) 0
End

Definition mk_lin_le_def[simp]:
  mk_lin_le cXs Y = mk_lin_constraint_ge ((1i,Y)::(MAP (λ(c,X). (-c,X)) cXs)) 0
End

Definition mk_lin_gt_def[simp]:
  mk_lin_gt cXs Y = mk_lin_constraint_ge ((-1i,Y)::cXs) 1
End

Definition mk_lin_lt_def[simp]:
  mk_lin_lt cXs Y = mk_lin_constraint_ge ((1i,Y)::(MAP (λ(c,X). (-c,X)) cXs)) 1
End

Definition cmk_lin_eq_def[simp]:
  cmk_lin_eq name cXs Y =
  [
    (SOME (mk_name name (strlit"ge")), mk_lin_ge cXs Y);
    (SOME (mk_name name (strlit"le")), mk_lin_le cXs Y)
  ]
End

Definition cencode_lin_equal_1_def[simp]:
  cencode_lin_equal_1 bnd Z cXs Y name =
  List (
    MAP (I ## bits_imply bnd [Pos (INL (Ge Z 1))])
      (cmk_lin_eq name cXs Y))
End

Definition cencode_lin_equal_2_def[simp]:
  cencode_lin_equal_2 bnd Z cXs Y name =
  Append
    (cencode_lin_equal_1 bnd Z cXs Y name) $
    Append
      (cbimply_var bnd (gtv name) (mk_lin_gt cXs Y)) $
    Append
      (cbimply_var bnd (ltv name) (mk_lin_lt cXs Y)) $
    (cat_least_one name
      [Pos (ltv name); Pos (gtv name); Pos (INL (Ge Z 1))])
End

Definition encode_lin_equal_def:
  encode_lin_equal bnd Zr cXs Y name =
  case Zr of
    NONE => abstrl (cmk_lin_eq name cXs Y)
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_lin_equal_1 bnd Z cXs Y name)
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_lin_equal_2 bnd Z cXs Y name)
End

Theorem eval_icterm_neg[local]:
  eval_icterm wi ∘ (λ(c,X). (-c,X)) =
  (λx. -1 * eval_icterm wi x)
Proof
  cong_tac NONE>>
  simp[]>>
  pairarg_tac>>
  gs[]>>
  intLib.ARITH_TAC
QED

Theorem eval_iclin_term_MAP_neg[local]:
  eval_iclin_term w (MAP (λ(c,X). (-c,X)) cXs) = -eval_iclin_term w cXs
Proof
  simp[eval_iclin_term_def,iSUM_def,MAP_MAP_o,
    eval_icterm_neg,iSUM_MAP_lin_const]>>
  rename1 ‘λx. f x’>>
  simp[ETA_AX]>>
  intLib.ARITH_TAC
QED

Theorem eval_iclin_term_CONS[local]:
  eval_iclin_term w (x::xs) = eval_icterm w x + eval_iclin_term w xs
Proof
  simp[eval_iclin_term_def,iSUM_def]
QED

Theorem encode_lin_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin reif cmp cXs Y)) ∧
  reify_sem Zr wi
    (eval_iclin_term wi cXs = varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin_equal bnd Zr cXs Y name)
Proof
  rw[reify_sem_def,encode_lin_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def,
    eval_iclin_term_def,eval_iclin_term_CONS,eval_iclin_term_MAP_neg]
  >-intLib.ARITH_TAC
  >-intLib.ARITH_TAC
  >-(
    simp[SF DNF_ss,eval_iclin_term_def,
      reify_avar_def,reify_reif_def,reify_flag_def]>>
    intLib.ARITH_TAC)
QED

Theorem encode_lin_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin_equal bnd Zr cXs Y name) ⇒
  reify_sem Zr wi
    (eval_iclin_term wi cXs = varc wi Y)
Proof
  rw[reify_sem_def,encode_lin_equal_def]>>
  every_case_tac>>
  gvs[eval_iclin_term_CONS,eval_iclin_term_MAP_neg]>>
  intLib.ARITH_TAC
QED

Definition cencode_lin_not_equal_1_def[simp]:
  cencode_lin_not_equal_1 bnd cXs Y name =
  List [
    (SOME (mk_name name (strlit"gt")),
      bits_imply bnd [Pos (nev name)] (mk_lin_gt cXs Y));
    (SOME (mk_name name (strlit"lt")),
      bits_imply bnd [Neg (nev name)] (mk_lin_lt cXs Y))
  ]
End

Definition cencode_lin_not_equal_2_def[simp]:
  cencode_lin_not_equal_2 bnd Z cXs Y name =
  Append
    (cbimply_var bnd (gtv name) (mk_lin_gt cXs Y)) $
  Append
    (cbimply_var bnd (ltv name) (mk_lin_lt cXs Y)) $
  (cat_least_one name
      [Pos (ltv name); Pos (gtv name); Neg (INL (Ge Z 1))])
End

Definition cencode_lin_not_equal_3_def[simp]:
  cencode_lin_not_equal_3 bnd Z cXs Y name =
  Append
    (List (MAP (I ## bits_imply bnd [Neg (INL (Ge Z 1))])
      (cmk_lin_eq name cXs Y))) $
    cencode_lin_not_equal_2 bnd Z cXs Y name
End

Definition encode_lin_not_equal_def:
  encode_lin_not_equal bnd Zr cXs Y name =
  case Zr of
    NONE =>
    abstr (cencode_lin_not_equal_1 bnd cXs Y name)
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_lin_not_equal_2 bnd Z cXs Y name)
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_lin_not_equal_3 bnd Z cXs Y name)
End

Theorem encode_lin_not_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin reif cmp cXs Y)) ∧
  reify_sem Zr wi
    (eval_iclin_term wi cXs ≠ varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin_not_equal bnd Zr cXs Y name)
Proof
  rw[reify_sem_def,encode_lin_not_equal_def]>>
  gvs[AllCasePreds(),eval_iclin_term_CONS,eval_iclin_term_MAP_neg,
    reify_avar_def,reify_reif_def,reify_flag_def]
  >-intLib.ARITH_TAC>>
  simp[SF DNF_ss,reify_avar_def,reify_reif_def,reify_flag_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_not_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin_not_equal bnd Zr cXs Y name) ⇒
  reify_sem Zr wi
    (eval_iclin_term wi cXs ≠ varc wi Y)
Proof
  rw[reify_sem_def,encode_lin_not_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def]>>
  every_case_tac>>
  gvs[eval_iclin_term_CONS,eval_iclin_term_MAP_neg]
  >-(
    rename1 ‘wb v’>>
    Cases_on ‘wb v’>>
    gvs[]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

(* Linear constraint: Σ ci·Xi cmp Y *)
Definition encode_lin_def:
  encode_lin bnd Zr cmp Xs Y =
  [false_constr]
End

Theorem encode_lin_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin Zr cmp Xs Y)) ∧
  lin_sem Zr cmp Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin bnd Zr cmp Xs Y)
Proof
  cheat
QED

Theorem encode_lin_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin bnd Zr cmp Xs Y) ⇒
  lin_sem Zr cmp Xs Y wi
Proof
  cheat
QED

Definition encode_linear_constr_def:
  encode_linear_constr bnd c name =
  case c of Lin Zr cmp Xs Y =>
    encode_lin bnd Zr cmp Xs Y
End

Theorem encode_linear_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear c) ∧
  linear_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_linear_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_linear_constr_def,linear_constr_sem_def]>>
  metis_tac[encode_lin_sem_1]
QED

Theorem encode_linear_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_linear_constr bnd c name) ⇒
  linear_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_linear_constr_def,linear_constr_sem_def]>>
  metis_tac[encode_lin_sem_2]
QED

(* Concrete encodings *)
Definition cencode_lin_equal_def:
  cencode_lin_equal bnd Zr cXs Y name ec =
  case Zr of
    NONE => (List (cmk_lin_eq name cXs Y),ec)
  | SOME (INL Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $ cencode_lin_equal_1 bnd Z cXs Y name, ec')
  | SOME (INR Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $ cencode_lin_equal_2 bnd Z cXs Y name, ec')
End

Theorem cencode_lin_equal_sem:
  valid_assignment bnd wi ∧
  cencode_lin_equal bnd Zr cXs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_lin_equal bnd Zr cXs Y name) ec ec'
Proof
  rw[cencode_lin_equal_def,encode_lin_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >-simp[enc_rel_List_refl_mul]
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[enc_rel_List_refl_mul])
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
QED

Definition cencode_lin_not_equal_def:
  cencode_lin_not_equal bnd Zr cXs Y name ec =
  case Zr of
    NONE => (cencode_lin_not_equal_1 bnd cXs Y name, ec)
  | SOME (INL Z) =>
    let
      (e,ec') = cencode_ge bnd Z 1 ec
    in
      (Append e $
        cencode_lin_not_equal_2 bnd Z cXs Y name, ec')
  | SOME (INR Z) =>
    let
      (e,ec') = cencode_ge bnd Z 1 ec
    in
      (Append e $
        cencode_lin_not_equal_3 bnd Z cXs Y name, ec')
End

Theorem cencode_lin_not_equal_sem:
  valid_assignment bnd wi ∧
  cencode_lin_not_equal bnd Zr cXs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_lin_not_equal bnd Zr cXs Y name) ec ec'
Proof
  rw[cencode_lin_not_equal_def,encode_lin_not_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >-(
    irule enc_rel_abstr_cong>>
    simp[])>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_ge>>
  simp[]>>
  irule enc_rel_abstr_cong>>
  simp[]
QED

Definition cencode_linear_constr_def:
  cencode_linear_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_linear_constr_sem:
  valid_assignment bnd wi ∧
  cencode_linear_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_linear_constr bnd c name) ec ec'
Proof
  cheat
QED
