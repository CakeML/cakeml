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

Theorem encode_lin_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin Zr Equal cXs Y)) ∧
  reify_sem Zr wi
    (eval_iclin_term wi cXs = varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin_equal bnd Zr cXs Y name)
Proof
  rw[reify_sem_def,encode_lin_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def,
    eval_iclin_term_def,eval_iclin_term_CONS]>>
  simp[SF DNF_ss,eval_iclin_term_def,
    reify_avar_def,reify_reif_def,reify_flag_def]>>
  intLib.ARITH_TAC
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
  gvs[eval_iclin_term_CONS]>>
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
  ALOOKUP cs name = SOME (Linear (Lin Zr NotEqual cXs Y)) ∧
  reify_sem Zr wi
    (eval_iclin_term wi cXs ≠ varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin_not_equal bnd Zr cXs Y name)
Proof
  rw[reify_sem_def,encode_lin_not_equal_def]>>
  gvs[AllCasePreds(),eval_iclin_term_CONS,
    reify_avar_def,reify_reif_def,reify_flag_def]>>
  simp[SF DNF_ss,reify_avar_def,reify_reif_def,reify_flag_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_lin_not_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin_not_equal bnd Zr cXs Y name) ⇒
  reify_sem Zr wi
    (eval_iclin_term wi cXs ≠ varc wi Y)
Proof
  rw[reify_sem_def,encode_lin_not_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def]>>
  every_case_tac>>
  gvs[eval_iclin_term_CONS]
  >-(
    rename1 ‘wb v’>>
    Cases_on ‘wb v’>>
    gvs[]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

(* this encompasses ≥, >, ≤, < *)
Definition encode_lin_cmp_aux_def:
  encode_lin_cmp_aux cmp cXs Y =
  case cmp of
    GreaterEqual => mk_lin_ge cXs Y
  | GreaterThan  => mk_lin_gt cXs Y
  | LessEqual    => mk_lin_le cXs Y
  | LessThan     => mk_lin_lt cXs Y
  | _            => false_constr
End

Definition encode_lin_order_cmpops_def:
  encode_lin_order_cmpops bnd Zr cmp cXs Y =
  let constr = encode_lin_cmp_aux cmp cXs Y
  in
    case Zr of
      NONE => [constr]
    | SOME (INL Z) =>
      encode_ge bnd Z 1 ++
      [bits_imply bnd [Pos (INL (Ge Z 1))] constr]
    | SOME (INR Z) =>
      encode_ge bnd Z 1 ++
      bimply_bits bnd [Pos (INL (Ge Z 1))] constr
End

Theorem encode_lin_order_cmpops_sem_1:
  valid_assignment bnd wi ∧ cmp ≠ Equal ∧ cmp ≠ NotEqual ∧
  reify_sem Zr wi (cmpop_val cmp (eval_iclin_term wi cXs) (varc wi Y)) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin_order_cmpops bnd Zr cmp cXs Y)
Proof
  Cases_on ‘cmp’>>
  rw[reify_sem_def,cmpop_val_def,
    encode_lin_order_cmpops_def,
    iconstraint_sem_def,encode_lin_cmp_aux_def]>>
  every_case_tac>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,
    eval_iclin_term_CONS]>>
  intLib.ARITH_TAC
QED

Theorem encode_lin_order_cmpops_sem_2:
  valid_assignment bnd wi ∧ cmp ≠ Equal ∧ cmp ≠ NotEqual ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin_order_cmpops bnd Zr cmp cXs Y) ⇒
  reify_sem Zr wi (cmpop_val cmp (eval_iclin_term wi cXs) (varc wi Y))
Proof
  rw[reify_sem_def,cmpop_val_def,
    encode_lin_order_cmpops_def,encode_lin_cmp_aux_def]>>
  every_case_tac>>
  gvs[eval_iclin_term_CONS]>>
  intLib.ARITH_TAC
QED

(* Linear constraint: Σ ci·Xi cmp Y *)
Definition encode_lin_def:
  encode_lin bnd Zr cmp cXs Y name =
  if cmp = Equal
  then encode_lin_equal bnd Zr cXs Y name
  else if cmp = NotEqual
  then encode_lin_not_equal bnd Zr cXs Y name
  else encode_lin_order_cmpops bnd Zr cmp cXs Y
End

Theorem encode_lin_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Linear (Lin Zr cmp cXs Y)) ∧
  lin_sem Zr cmp cXs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_lin bnd Zr cmp cXs Y name)
Proof
  rw[encode_lin_def,lin_sem_def]
  >-gs[encode_lin_equal_sem_1,cmpop_val_def]
  >-gs[encode_lin_not_equal_sem_1,cmpop_val_def]
  >-metis_tac[encode_lin_order_cmpops_sem_1]
QED

Theorem encode_lin_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_lin bnd Zr cmp cXs Y name) ⇒
  lin_sem Zr cmp cXs Y wi
Proof
  rw[encode_lin_def,lin_sem_def]
  >-(
    simp[cmpop_val_def]>>
    metis_tac[encode_lin_equal_sem_2])
  >-(
    simp[cmpop_val_def]>>
    metis_tac[encode_lin_not_equal_sem_2])
  >-metis_tac[encode_lin_order_cmpops_sem_2]
QED

Definition encode_linear_constr_def:
  encode_linear_constr bnd c name =
  case c of Lin Zr cmp cXs Y =>
    encode_lin bnd Zr cmp cXs Y name
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

Definition cencode_lin_order_cmpops_def:
  cencode_lin_order_cmpops bnd Zr cmp cXs Y name ec =
  let constr = encode_lin_cmp_aux cmp cXs Y
  in
    case Zr of
      NONE =>
      (List [
        (SOME (strlit"c[" ^ name ^ strlit"]"), constr)], ec)
    | SOME (INL Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
      (Append e $
        List [
        (SOME (strlit"c[" ^ name ^ strlit"]"),
          (bits_imply bnd [Pos (INL (Ge Z 1))] constr))], ec')
    | SOME (INR Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
      (Append e $
        List (mk_annotate
        [strlit"c[" ^ name ^ strlit"][r]";
          strlit"c[" ^ name ^ strlit"][f]"]
        (bimply_bits bnd [Pos (INL (Ge Z 1))] constr)), ec')
End

Theorem cencode_lin_order_cmpops_sem:
  valid_assignment bnd wi ∧
  cencode_lin_order_cmpops bnd Zr cmp cXs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_lin_order_cmpops bnd Zr cmp cXs Y) ec ec'
Proof
  rw[cencode_lin_order_cmpops_def,encode_lin_order_cmpops_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >- (
    irule enc_rel_abstr_cong>>
    simp[])
  >- (
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
  >- (
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_List_mk_annotate)
QED

Definition cencode_linear_constr_def:
  cencode_linear_constr bnd c name ec =
  case c of
    Lin Zr cmp cXs Y =>
      if cmp = Equal
      then cencode_lin_equal bnd Zr cXs Y name ec
      else if cmp = NotEqual
      then cencode_lin_not_equal bnd Zr cXs Y name ec
      else cencode_lin_order_cmpops bnd Zr cmp cXs Y name ec
End

Theorem cencode_linear_constr_sem:
  valid_assignment bnd wi ∧
  cencode_linear_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_linear_constr bnd c name) ec ec'
Proof
  Cases_on ‘c’>>
  rename1 ‘Lin Zr cmp cXs Y’>>
  rw[cencode_linear_constr_def,encode_linear_constr_def,encode_lin_def]
  >-simp[cencode_lin_equal_sem]
  >-simp[cencode_lin_not_equal_sem]
  >-metis_tac[cencode_lin_order_cmpops_sem]
QED
