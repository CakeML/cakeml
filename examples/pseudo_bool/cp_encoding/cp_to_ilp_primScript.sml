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
Definition cmk_eq_def[simp]:
  cmk_eq name X Y =
  let pref = strlit"c[" ^ name  in
  [
    (SOME (pref ^ strlit "][ge]"),mk_constraint_ge 1 (X) (-1) (Y) 0);
    (SOME (pref ^ strlit "][le]"),mk_constraint_ge 1 (Y) (-1) (X) 0)
  ]
End

(* For gt and lt, we'll have many different names for them *)
Definition mk_gt_def[simp]:
  mk_gt X Y = mk_constraint_ge 1 X (-1) Y 1
End

Definition mk_lt_def[simp]:
  mk_lt X Y = mk_constraint_ge 1 Y (-1) X 1
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
  Append
    (cvar_imply bnd (nev name) (mk_gt X Y))
    (cnvar_imply bnd (nev name) (mk_gt Y X))
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
    GreaterEqual => mk_constraint_ge 1 X (-1) Y 0
  | GreaterThan  => mk_constraint_ge 1 X (-1) Y 1
  | LessEqual    => mk_constraint_ge (-1) X 1 Y 0
  | LessThan     => mk_constraint_ge (-1) X 1 Y 1
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

Definition encode_negative_def:
  encode_negative X Y =
  [
    mk_constraint_ge 1 X 1 Y 0;
    mk_constraint_ge (-1) X (-1) Y 0
  ]
End

Definition encode_abs_def:
  encode_abs bnd X Y =
  encode_ge bnd X 0 ++
  [
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_constraint_ge 1 X (-1) Y 0);
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_constraint_ge (-1) X 1 Y 0);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_constraint_ge 1 X 1 Y 0);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_constraint_ge (-1) X (-1) Y 0)
  ]
End

(* Theorems for Negative *)
Theorem encode_negative_sem_1:
  valid_assignment bnd wi ∧
  unop_sem Negative X Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_negative X Y)
Proof
  rw[encode_negative_def,unop_sem_def,unop_val_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_negative_sem_2:
  valid_assignment bnd wi ∧
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
  rw[encode_abs_def,unop_sem_def,unop_val_def,reify_avar_def,reify_reif_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_abs_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_abs bnd X Y) ⇒
  unop_sem Abs X Y wi
Proof
  rw[encode_abs_def,unop_sem_def,unop_val_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def]>>
  every_case_tac>>
  gvs[]>>
  Cases_on ‘wb (INL (Ge X 0))’>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Definition split_iclin_term_def:
  (split_iclin_term ([]:'a iclin_term)
    (acc:'a ilin_term) rhs = (acc,rhs)) ∧
  (split_iclin_term ((c,X)::xs) acc rhs =
    case X of
      INL v => split_iclin_term xs ((c,v)::acc) rhs
    | INR cc =>
      split_iclin_term xs acc (rhs - c * cc))
End

Theorem split_iclin_term_sound:
  ∀Xs rhs acc xs rhs'.
    split_iclin_term Xs acc rhs = (xs,rhs') ⇒
    eval_iclin_term wi Xs + eval_ilin_term wi acc - rhs =
    eval_ilin_term wi xs - rhs'
Proof
  Induct
  >-simp[split_iclin_term_def, eval_iclin_term_def, eval_ilin_term_def, iSUM_def]
  >-(
    Cases>>
    Cases_on ‘r’>>
    rw[split_iclin_term_def]>>
    last_x_assum $ drule_then mp_tac>>
    rw[eval_iclin_term_def, eval_ilin_term_def, iSUM_def, varc_def]>>
    intLib.ARITH_TAC)
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
  valid_assignment bnd wi ∧
  binop_sem Plus X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_plus X Y Z)
Proof
  rw[encode_plus_def,binop_sem_def,binop_val_def]>>
  pairarg_tac>>
  gvs[]>>
  pairarg_tac>>
  gvs[]>>
  imp_res_tac split_iclin_term_sound>>
  fs[iconstraint_sem_def]>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  simp[eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_plus_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_plus X Y Z) ⇒
  binop_sem Plus X Y Z wi
Proof
  rw[encode_plus_def,binop_sem_def,binop_val_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def]>>
  every_case_tac>>
  pairarg_tac>>
  gvs[]>>
  pairarg_tac>>
  gvs[iconstraint_sem_def]>>
  imp_res_tac split_iclin_term_sound>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  simp[eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

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
  pairarg_tac>>
  gvs[]>>
  pairarg_tac>>
  gvs[]>>
  imp_res_tac split_iclin_term_sound>>
  fs[iconstraint_sem_def]>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  simp[eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_minus_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_minus X Y Z) ⇒
  binop_sem Minus X Y Z wi
Proof
  rw[encode_minus_def,binop_sem_def,binop_val_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def]>>
  every_case_tac>>
  pairarg_tac>>
  gvs[]>>
  pairarg_tac>>
  gvs[iconstraint_sem_def]>>
  imp_res_tac split_iclin_term_sound>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  pop_assum $ qspec_then ‘wi’ mp_tac>>
  simp[eval_iclin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition encode_min_def:
  encode_min bnd X Y Z =
  [false_constr]
End

Theorem encode_min_sem_1:
  valid_assignment bnd wi ∧
  binop_sem Min X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_min bnd X Y Z)
Proof
  cheat
QED

Theorem encode_min_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_min bnd X Y Z) ⇒
  binop_sem Min X Y Z wi
Proof
  cheat
QED

Definition encode_max_def:
  encode_max bnd X Y Z =
  [false_constr]
End

Theorem encode_max_sem_1:
  valid_assignment bnd wi ∧
  binop_sem Max X Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_max bnd X Y Z)
Proof
  cheat
QED

Theorem encode_max_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_max bnd X Y Z) ⇒
  binop_sem Max X Y Z wi
Proof
  cheat
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
      | Min => encode_min bnd X Y Z
      | Max => encode_max bnd X Y Z)
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
  | Unop uop X Y => (List [], ec)
  | Binop bop X Y Z => (List [], ec)
End

Theorem cencode_prim_constr_sem:
  valid_assignment bnd wi ∧
  cencode_prim_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_prim_constr bnd c name) ec ec'
Proof
  cheat
QED

(*

EVAL``append o FST $ cencode_order_cmpops
  (\x. (-5,5))
  NONE
  GreaterEqual
  (INL (strlit "X")) (INL (strlit "Y")) (strlit "foo") init_ec``

  [INL (strlit "x");INL (strlit "y")]) (strlit"t1") init_ec``


*)
