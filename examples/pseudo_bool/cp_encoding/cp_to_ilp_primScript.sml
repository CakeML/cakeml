(*
  Formalization of the CP to ILP phase (prim constraints)
*)
Theory cp_to_ilp_prim
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition ltv_def[simp]:
  ltv name =
    INR (name, Flag (strlit "lt"))
End

Definition gtv_def[simp]:
  gtv name =
    INR (name, Flag (strlit "gt"))
End

Definition nev_def[simp]:
  nev name =
    INR (name, Flag (strlit "ne"))
End

(* the two named equality constraints, held as a list *)
Definition mk_ge_def[simp]:
  mk_ge X Y = mk_constraint_ge 1 (X) (-1) (Y) 0
End

Definition mk_le_def[simp]:
  mk_le X Y = mk_ge Y X
End

Definition cmk_eq_def[simp]:
  cmk_eq name X Y =
  [
    (SOME (mk_name name (strlit"ge")), mk_ge X Y);
    (SOME (mk_name name (strlit"le")), mk_le X Y)
  ]
End

(* For gt and lt, we'll have many different names for them *)
Definition mk_gt_def[simp]:
  mk_gt X Y = mk_constraint_ge 1 X (-1) Y 1
End

Definition mk_lt_def[simp]:
  mk_lt X Y = mk_gt Y X
End

Definition cencode_equal_1_def[simp]:
  cencode_equal_1 bnd Z X Y name =
  List (
    MAP (I ## bits_imply bnd [Pos (INL (Ge Z 1))])
      (cmk_eq name X Y))
End

Definition cencode_equal_2_def[simp]:
  cencode_equal_2 bnd Z X Y name =
  Append
    (cencode_equal_1 bnd Z X Y name) $
    Append
      (cbimply_var bnd (gtv name) (mk_gt X Y)) $
    Append
      (cbimply_var bnd (ltv name) (mk_lt X Y)) $
    (cat_least_one name
      [Pos (ltv name); Pos (gtv name); Pos (INL (Ge Z 1))])
End

Definition encode_equal_def:
  encode_equal bnd Zr X Y name =
  case Zr of
    NONE => abstrl (cmk_eq name X Y)
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_equal_1 bnd Z X Y name)
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_equal_2 bnd Z X Y name)
End

Theorem encode_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Cmpop reif cmp X Y)) ∧
  reify_sem Zr wi
    (varc wi X = varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_equal bnd Zr X Y name)
Proof
  rw[reify_sem_def,encode_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def,iconstraint_sem_def]
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- (
    rw[oneline b2i_def]>>
    simp[SF DNF_ss,reify_avar_def,reify_flag_def,reify_reif_def]>>
    intLib.ARITH_TAC)
QED

Theorem encode_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_equal bnd Zr X Y name) ⇒
  reify_sem Zr wi
    (varc wi X = varc wi Y)
Proof
  rw[reify_sem_def,encode_equal_def]>>
  every_case_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Definition cencode_not_equal_1_def[simp]:
  cencode_not_equal_1 bnd X Y name =
  List [
    (SOME (mk_name name (strlit"gt")),
      bits_imply bnd [Pos (nev name)] (mk_gt X Y));
    (SOME (mk_name name (strlit"lt")),
      bits_imply bnd [Neg (nev name)] (mk_gt Y X))
  ]
End

Definition cencode_not_equal_2_def[simp]:
  cencode_not_equal_2 bnd Z X Y name =
  Append
    (cbimply_var bnd (gtv name) (mk_gt X Y)) $
  Append
    (cbimply_var bnd (ltv name) (mk_gt Y X)) $
  (cat_least_one name
      [Pos (ltv name); Pos (gtv name); Neg (INL (Ge Z 1))])
End

Definition cencode_not_equal_3_def[simp]:
  cencode_not_equal_3 bnd Z X Y name =
  Append
    (List (MAP (I ## bits_imply bnd [Neg (INL (Ge Z 1))])
      (cmk_eq name X Y))) $
  cencode_not_equal_2 bnd Z X Y name
End

Definition encode_not_equal_def:
  encode_not_equal bnd Zr X Y name =
  case Zr of
    NONE =>
    abstr (cencode_not_equal_1 bnd X Y name)
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_not_equal_2 bnd Z X Y name)
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    abstr (cencode_not_equal_3 bnd Z X Y name)
End

Theorem encode_not_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Cmpop reif cmp X Y)) ∧
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_not_equal bnd Zr X Y name)
Proof
  rw[reify_sem_def,encode_not_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_flag_def,reify_reif_def]
  >- intLib.ARITH_TAC
  >- (
    simp[SF DNF_ss,reify_avar_def,reify_flag_def,reify_reif_def]>>
    intLib.ARITH_TAC)
  >- (
    simp[SF DNF_ss,reify_avar_def,reify_flag_def,reify_reif_def]>>
    intLib.ARITH_TAC)
QED

Theorem encode_not_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_not_equal bnd Zr X Y name) ⇒
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y)
Proof
  rw[reify_sem_def,encode_not_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_flag_def,reify_reif_def]>>
  every_case_tac>>gvs[]
  >- (
    rename1`INR f`>>
    Cases_on`wb (INR f)`>>gvs[]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

(* this encompasses ≥, >, ≤, < *)
Definition encode_cmp_aux_def:
  encode_cmp_aux cmp X Y =
  case cmp of
    GreaterEqual => mk_ge X Y
  | GreaterThan  => mk_gt X Y
  | LessEqual    => mk_le X Y
  | LessThan     => mk_lt X Y
  | _            => false_constr
End

Definition encode_order_cmpops_def:
  encode_order_cmpops bnd Zr cmp X Y =
  let constr = encode_cmp_aux cmp X Y
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

Theorem encode_order_cmpops_sem_1:
  valid_assignment bnd wi ∧ cmp ≠ Equal ∧ cmp ≠ NotEqual ∧
  reify_sem Zr wi (cmpop_val cmp (varc wi X) (varc wi Y)) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_order_cmpops bnd Zr cmp X Y)
Proof
  Cases_on ‘cmp’>>
  rw[reify_sem_def,cmpop_val_def,
    encode_order_cmpops_def,
    iconstraint_sem_def,encode_cmp_aux_def]>>
  every_case_tac>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_order_cmpops_sem_2:
  valid_assignment bnd wi ∧ cmp ≠ Equal ∧ cmp ≠ NotEqual ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_order_cmpops bnd Zr cmp X Y) ⇒
  reify_sem Zr wi (cmpop_val cmp (varc wi X) (varc wi Y))
Proof
  rw[reify_sem_def,encode_order_cmpops_def,cmpop_val_def,encode_cmp_aux_def]>>
  every_case_tac>>
  gvs[]>>
  intLib.ARITH_TAC
QED

(* -X ≥ Y *)
Definition mk_nge_def[simp]:
  mk_nge X Y = mk_constraint_ge (-1) (X) (-1) (Y) 0
End

(* -X ≤ Y *)
Definition mk_nle_def[simp]:
  mk_nle X Y = mk_constraint_ge 1 (Y) (1) (X) 0
End

Definition encode_negative_def:
  encode_negative X Y =
  [
    mk_nle X Y;
    mk_nge X Y;
  ]
End

Definition encode_abs_body_def:
  encode_abs_body bnd X Y =
  [
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_ge X Y);
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_le X Y);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_nle X Y);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_nge X Y)
  ]
End

Definition encode_abs_def:
  encode_abs bnd X Y =
  encode_ge bnd X 0 ++
  encode_abs_body bnd X Y
End

(* Theorems for Negative *)
Theorem encode_negative_sem_1:
  unop_sem Negative X Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_negative X Y)
Proof
  rw[encode_negative_def,unop_sem_def,unop_val_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_negative_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_negative X Y) ⇒
  unop_sem Negative X Y wi
Proof
  rw[encode_negative_def,unop_sem_def,unop_val_def]>>
  intLib.ARITH_TAC
QED

(* Theorems for Abs *)
Theorem encode_abs_sem_1:
  valid_assignment bnd wi ∧
  unop_sem Abs X Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_abs bnd X Y)
Proof
  rw[encode_abs_def,encode_abs_body_def, unop_sem_def,
    unop_val_def,reify_avar_def,reify_reif_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_abs_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_abs bnd X Y) ⇒
  unop_sem Abs X Y wi
Proof
  rw[encode_abs_def,encode_abs_body_def,unop_sem_def,unop_val_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def]>>
  every_case_tac>>
  gvs[]>>
  Cases_on ‘wb (INL (Ge X 0))’>>
  gvs[]>>
  intLib.ARITH_TAC
QED

(* Binary operations *)
Definition encode_plus_def:
  encode_plus X Y Z =
  let
    (xygez,rhs1) = split_iclin_term [(1i,X);(1i,Y);(-1i,Z)] [] 0;
    (xylez,rhs2) = split_iclin_term [(-1i,X);(-1i,Y);(1i,Z)] [] 0
  in
    [(xygez,[],rhs1);(xylez,[],rhs2)]
End

Theorem encode_plus_sem_1:
  binop_sem Plus X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_plus X Y Z)
Proof
  rw[encode_plus_def,binop_sem_def,binop_val_def]>>
  rpt(pairarg_tac>>gvs[])>>
  imp_res_tac split_iclin_term_sound>>
  fs[iconstraint_sem_def,eval_iclin_term_def,iSUM_def]>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_plus_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_plus X Y Z) ⇒
  binop_sem Plus X Y Z wi
Proof
  rw[encode_plus_def,binop_sem_def,binop_val_def]>>
  rpt(pairarg_tac>>gvs[])>>
  imp_res_tac split_iclin_term_sound>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  fs[iconstraint_sem_def,eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition cencode_plus_def:
  cencode_plus bnd X Y Z name =
  List
    (mk_annotate
      [mk_name name (strlit"ge"); mk_name name (strlit"le")]
      (encode_plus X Y Z)
    )
End

Definition encode_minus_def:
  encode_minus X Y Z =
  let
    (xygez,rhs1) = split_iclin_term [(1i,X);(-1i,Y);(-1i,Z)] [] 0;
    (xylez,rhs2) = split_iclin_term [(-1i,X);(1i,Y);(1i,Z)] [] 0
  in
    [(xygez,[],rhs1);(xylez,[],rhs2)]
End

Theorem encode_minus_sem_1:
  valid_assignment bnd wi ∧
  binop_sem Minus X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_minus X Y Z)
Proof
  rw[encode_minus_def,binop_sem_def,binop_val_def]>>
  rpt(pairarg_tac>>gvs[])>>
  imp_res_tac split_iclin_term_sound>>
  fs[iconstraint_sem_def,eval_iclin_term_def,iSUM_def]>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_minus_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_minus X Y Z) ⇒
  binop_sem Minus X Y Z wi
Proof
  rw[encode_minus_def,binop_sem_def,binop_val_def]>>
  rpt(pairarg_tac>>gvs[])>>
  imp_res_tac split_iclin_term_sound>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  fs[iconstraint_sem_def,eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition cencode_minus_def:
  cencode_minus bnd X Y Z name =
  List
    (mk_annotate
      [mk_name name (strlit"ge"); mk_name name (strlit"le")]
      (encode_minus X Y Z)
    )
End

(* lle means X ≤ Z, rle means Y ≤ Z*)
Definition cencode_min_def:
  cencode_min bnd X Y Z name =
  let
    lle = INR (name, Flag (strlit "lle"));
    rle = INR (name, Flag (strlit "rle"));
  in
  Append (cvar_imply bnd lle (mk_le X Z)) $
  Append (cvar_imply bnd rle (mk_le Y Z)) $
  Append
    (List
      (mk_annotate
      [mk_name name (strlit"lge"); mk_name name (strlit"rge")]
      [mk_ge X Z; mk_ge Y Z])) $
  cat_least_one name [Pos lle; Pos rle]
End

Definition encode_min_def:
  encode_min bnd X Y Z name =
  abstr (cencode_min bnd X Y Z name)
End

Theorem encode_min_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Binop cmp X Y Z)) ∧
  binop_sem Min X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_min bnd X Y Z name)
Proof
  rw[binop_sem_def,encode_min_def,cencode_min_def,binop_val_def,mk_annotate_def]>>
  gvs[reify_avar_def,reify_flag_def,SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem encode_min_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_min bnd X Y Z name) ⇒
  binop_sem Min X Y Z wi
Proof
  rw[binop_sem_def,encode_min_def,cencode_min_def,binop_val_def,mk_annotate_def]>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Definition cencode_max_def:
  cencode_max bnd X Y Z name =
  let
    lge = INR (name, Flag (strlit "lge"));
    rge = INR (name, Flag (strlit "rge"));
  in
  Append (cvar_imply bnd lge (mk_ge X Z)) $
  Append (cvar_imply bnd rge (mk_ge Y Z)) $
  Append
    (List
      (mk_annotate
      [mk_name name (strlit"lle"); mk_name name (strlit"rle")]
      [mk_le X Z; mk_le Y Z])) $
  cat_least_one name [Pos lge; Pos rge]
End

Definition encode_max_def:
  encode_max bnd X Y Z name =
  abstr (cencode_max bnd X Y Z name)
End

Theorem encode_max_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Binop cmp X Y Z)) ∧
  binop_sem Max X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_max bnd X Y Z name)
Proof
  rw[binop_sem_def,encode_max_def,cencode_max_def,binop_val_def,mk_annotate_def]>>
  gvs[reify_avar_def,reify_flag_def,SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem encode_max_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_max bnd X Y Z name) ⇒
  binop_sem Max X Y Z wi
Proof
  rw[binop_sem_def,encode_max_def,cencode_max_def,binop_val_def,mk_annotate_def]>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Definition encode_prim_constr_def:
  encode_prim_constr bnd c name =
  case c of
    Cmpop Zr cmp X Y =>
      if cmp = Equal
      then encode_equal bnd Zr X Y name
      else if cmp = NotEqual
      then encode_not_equal bnd Zr X Y name
      else encode_order_cmpops bnd Zr cmp X Y
  | Unop uop X Y =>
      (case uop of
        Negative => encode_negative X Y
      | Abs => encode_abs bnd X Y)
  | Binop bop X Y Z =>
      (case bop of
        Plus => encode_plus X Y Z
      | Minus => encode_minus X Y Z
      | Min => encode_min bnd X Y Z name
      | Max => encode_max bnd X Y Z name)
End

Theorem encode_prim_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim c) ∧
  prim_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_prim_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_prim_constr_def,prim_constr_sem_def]
  >- (Cases_on`p`>>gvs[]>>
      metis_tac[encode_negative_sem_1,encode_abs_sem_1])
  >- (Cases_on`p`>>gvs[]>>
      metis_tac[encode_plus_sem_1,encode_minus_sem_1,
                encode_min_sem_1,encode_max_sem_1])
  >- (irule encode_equal_sem_1>>
      gvs[cmpop_sem_def,cmpop_val_def])
  >- (irule encode_not_equal_sem_1>>
      gvs[cmpop_sem_def,cmpop_val_def])
  >> (irule encode_order_cmpops_sem_1>>
      gvs[cmpop_sem_def,cmpop_val_def])
QED

Theorem encode_prim_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_prim_constr bnd c name) ⇒
  prim_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_prim_constr_def,prim_constr_sem_def]
  >- (Cases_on`p`>>gvs[]>>
      metis_tac[encode_negative_sem_2,encode_abs_sem_2])
  >- (Cases_on`p`>>gvs[]>>
      metis_tac[encode_plus_sem_2,encode_minus_sem_2,
                encode_min_sem_2,encode_max_sem_2])
  >- (gvs[cmpop_sem_def,cmpop_val_def]>>
      metis_tac[encode_equal_sem_2])
  >- (gvs[cmpop_sem_def,cmpop_val_def]>>
      metis_tac[encode_not_equal_sem_2])
  >- (gvs[cmpop_sem_def]>>
      metis_tac[encode_order_cmpops_sem_2])
QED

(* Concrete encodings *)
Definition cencode_equal_def:
  cencode_equal bnd Zr X Y name ec =
  case Zr of
    NONE => (List (cmk_eq name X Y),ec)
  | SOME (INL Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $ cencode_equal_1 bnd Z X Y name, ec')
  | SOME (INR Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $  cencode_equal_2 bnd Z X Y name, ec')
End

Theorem cencode_equal_sem:
  valid_assignment bnd wi ∧
  cencode_equal bnd Zr X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_equal bnd Zr X Y name) ec ec'
Proof
  rw[cencode_equal_def,encode_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >- simp[enc_rel_List_refl_mul]
  >- (
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[enc_rel_List_refl_mul])
  >- (
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
QED

Definition cencode_not_equal_def:
  cencode_not_equal bnd Zr X Y name ec =
  case Zr of
    NONE => (cencode_not_equal_1 bnd X Y name, ec)
  | SOME (INL Z) =>
    let
      (e,ec') = cencode_ge bnd Z 1 ec
    in
      (Append e $
        cencode_not_equal_2 bnd Z X Y name, ec')
  | SOME (INR Z) =>
    let
      (e,ec') = cencode_ge bnd Z 1 ec
    in
      (Append e $
        cencode_not_equal_3 bnd Z X Y name, ec')
End

Theorem cencode_not_equal_sem:
  valid_assignment bnd wi ∧
  cencode_not_equal bnd Zr X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_not_equal bnd Zr X Y name) ec ec'
Proof
  rw[cencode_not_equal_def,encode_not_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >- (
    irule enc_rel_abstr_cong>>
    simp[])
  >- (
    pure_rewrite_tac[GSYM APPEND_ASSOC]>>
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
  >- (
    pure_rewrite_tac[GSYM APPEND_ASSOC]>>
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
QED

Definition cencode_order_cmpops_def:
  cencode_order_cmpops bnd Zr cmp X Y name ec =
  let constr = encode_cmp_aux cmp X Y
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

Theorem cencode_order_cmpops_sem:
  valid_assignment bnd wi ∧
  cencode_order_cmpops bnd Zr cmp X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_order_cmpops bnd Zr cmp X Y) ec ec'
Proof
  rw[cencode_order_cmpops_def,encode_order_cmpops_def]>>
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

Definition cencode_negative_def:
  cencode_negative X Y name =
    List (mk_annotate [mk_name name (strlit"le"); mk_name name (strlit"ge")]
      (encode_negative X Y))
End

Definition cencode_abs_def:
  cencode_abs bnd X Y name ec =
  let
    (e,ec') = cencode_ge bnd X 0 ec;
    ls =
      mk_annotate [
        mk_name name (strlit"posge");
        mk_name name (strlit"posle");
        mk_name name (strlit"negle");
        mk_name name (strlit"negge");]
        (encode_abs_body bnd X Y)
  in
    (Append e (List ls) , ec')
End

(* Concrete encodings - TODO *)
Definition cencode_prim_constr_def:
  cencode_prim_constr bnd c name ec =
  case c of
    Cmpop Zr cmp X Y =>
      if cmp = Equal
      then cencode_equal bnd Zr X Y name ec
      else if cmp = NotEqual
      then cencode_not_equal bnd Zr X Y name ec
      else cencode_order_cmpops bnd Zr cmp X Y name ec
  | Unop uop X Y =>
    (case uop of
        Negative => (cencode_negative X Y name,ec)
      | Abs => cencode_abs bnd X Y name ec)
  | Binop bop X Y Z =>
    (case bop of
      Min => (cencode_min bnd X Y Z name, ec)
    | Max => (cencode_max bnd X Y Z name, ec)
    | Plus => (cencode_plus bnd X Y Z name, ec)
    | Minus => (cencode_minus bnd X Y Z name, ec))
End

Theorem cencode_prim_constr_sem:
  valid_assignment bnd wi ∧
  cencode_prim_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_prim_constr bnd c name) ec ec'
Proof
  rw[encode_prim_constr_def,cencode_prim_constr_def]>>
  gvs[AllCaseEqs()]
  >- (
    simp[cencode_negative_def]>>
    metis_tac[enc_rel_List_mk_annotate])
  >- (
    fs[cencode_abs_def,encode_abs_def]>>
    pairarg_tac>>gvs[]>>
    irule enc_rel_Append>>
    metis_tac[enc_rel_List_mk_annotate,enc_rel_encode_ge])
  >- simp[cencode_plus_def,encode_plus_def,enc_rel_List_mk_annotate]
  >- simp[cencode_minus_def,encode_minus_def,enc_rel_List_mk_annotate]
  >- simp[encode_min_def]
  >- simp[encode_max_def]
  >- metis_tac[cencode_equal_sem]
  >- metis_tac[cencode_not_equal_sem]
  >- metis_tac[cencode_order_cmpops_sem]
QED

(*

EVAL``append o FST $ cencode_prim_constr
  (\x. (-5,5))
  (Binop Min (INL (strlit "X")) (INL (strlit "Y")) (INL (strlit "Z")))
  (strlit "foo")
  init_ec``

*)
