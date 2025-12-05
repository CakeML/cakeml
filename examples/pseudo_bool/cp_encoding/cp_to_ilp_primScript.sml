(*
  Formalization of the CP to ILP phase (prim constraints)
*)
Theory cp_to_ilp_prim
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition lt_var_def[simp]:
  lt_var name =
    INR (name, Flag (strlit "lt"))
End

Definition gt_var_def[simp]:
  gt_var name =
    INR (name, Flag (strlit "gt"))
End

Definition ne_var_def[simp]:
  ne_var name =
    INR (name, Flag (strlit "ne"))
End

Definition at_least_one_def:
  at_least_one ls =
    ([], MAP (λl. (1,l)) ls, 1)
End

Theorem at_least_one_sem[simp]:
  iconstraint_sem (at_least_one ls) (wi,wb) ⇔
  ∃l. MEM l ls ∧ lit wb l
Proof
  rw[iconstraint_sem_def,at_least_one_def,eval_lin_term_def]>>
  simp[MAP_MAP_o,o_DEF]
QED

Definition encode_equal_def:
  encode_equal bnd Zr X Y name =
  let constr =
    [
      mk_constraint_ge 1 (X) (-1) (Y) 0;
      mk_constraint_ge 1 (Y) (-1) (X) 0
    ] in
  case Zr of
    NONE => constr
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    MAP (bits_imply bnd [Pos (INL (Ge Z 1))]) constr
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    MAP (bits_imply bnd [Pos (INL (Ge Z 1))]) constr ++
    [
      bits_imply bnd [Pos (gt_var name)]
        (mk_constraint_ge 1 X (-1) Y 1);
      bits_imply bnd [Pos (lt_var name)]
         (mk_constraint_ge 1 Y (-1) X 1);
      at_least_one
        [Pos (lt_var name); Pos (gt_var name);
          Pos (INL (Ge Z 1))];
    ]
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

Definition encode_not_equal_def:
  encode_not_equal bnd Zr X Y name =
  let xgty = (mk_constraint_ge 1 X (-1) Y 1) in
  let ygtx = (mk_constraint_ge 1 Y (-1) X 1) in
  case Zr of
    NONE =>
    [
      bits_imply bnd [Pos (ne_var name)] xgty;
      bits_imply bnd [Neg (ne_var name)] ygtx
    ]
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    bimply_bits bnd [Pos (gt_var name)] xgty ++
    bimply_bits bnd [Pos (lt_var name)] ygtx ++
    [at_least_one
      [Pos (lt_var name); Pos (gt_var name);
        Neg (INL (Ge Z 1))]]
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    MAP (bits_imply bnd [Neg (INL (Ge Z 1))])
      [
        mk_constraint_ge 1 (X) (-1) (Y) 0;
        mk_constraint_ge 1 (Y) (-1) (X) 0
      ] ++
    [
      bits_imply bnd [Pos (gt_var name)] xgty;
      bits_imply bnd [Pos (lt_var name)] ygtx;
      at_least_one
        [Pos (lt_var name); Pos (gt_var name);
          Neg (INL (Ge Z 1))];
    ]
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
Definition encode_order_cmpops_def:
  encode_order_cmpops bnd Zr cmp X Y =
  let constr =
    (case cmp of
      GreaterEqual => mk_constraint_ge 1 X (-1) Y 0
    | GreaterThan  => mk_constraint_ge 1 X (-1) Y 1
    | LessEqual    => mk_constraint_ge (-1) X 1 Y 0
    | LessThan     => mk_constraint_ge (-1) X 1 Y 1
    | _            => false_constr)
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
    iconstraint_sem_def]>>
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
  rw[reify_sem_def,encode_order_cmpops_def,cmpop_val_def]>>
  every_case_tac>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Definition encode_negative_def:
  encode_negative X Y =
  [
    mk_constraint_ge 1 X (-1) Y 0;
    mk_constraint_ge (-1) X 1 Y 0
  ]
End

Definition encode_abs_def:
  encode_abs bnd X Y =
  [
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_constraint_ge 1 X (-1) Y 0);
    bits_imply bnd [Pos (INL (Ge X 0))] (mk_constraint_ge (-1) X 1 Y 0);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_constraint_ge 1 X 1 Y 0);
    bits_imply bnd [Neg (INL (Ge X 0))] (mk_constraint_ge (-1) X (-1) Y 0)
  ]
End

Definition encode_prim_constr_def:
  encode_prim_constr bnd c name =
  case c of
    Cmpop Zr cmp X Y =>
      if cmp = Equal
      then encode_equal bnd Zr X Y name
      else if cmp = NotEqual
      then encode_not_equal bnd Zr X Y name
      else encode_order_cmpops bnd Zr cmp X Y
  | _ => ARB
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
  >- cheat
  >- cheat
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
  >- cheat
  >- cheat
  >- (gvs[cmpop_sem_def,cmpop_val_def]>>
      metis_tac[encode_equal_sem_2])
  >- (gvs[cmpop_sem_def,cmpop_val_def]>>
      metis_tac[encode_not_equal_sem_2])
  >- (gvs[cmpop_sem_def]>>
      metis_tac[encode_order_cmpops_sem_2])
QED

Definition cencode_equal_def:
  cencode_equal bnd Zr X Y name ec =
  let constr =
    [
      (SOME (strlit "ge"),mk_constraint_ge 1 (X) (-1) (Y) 0);
      (SOME (strlit "le"),mk_constraint_ge 1 (Y) (-1) (X) 0)
    ] in
  case Zr of
    NONE => (List constr,ec)
  | SOME (INL Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $
          List (MAP (I ## bits_imply bnd [Pos (INL (Ge Z 1))]) constr),ec')
  | SOME (INR Z) =>
      let
        (e,ec') = cencode_ge bnd Z 1 ec
      in
        (Append e $
          List (
          MAP (I ## bits_imply bnd [Pos (INL (Ge Z 1))]) constr ++
          [
            (SOME (strlit "gt"),bits_imply bnd [Pos (gt_var name)]
              (mk_constraint_ge 1 X (-1) Y 1));
            (SOME (strlit "lt"),bits_imply bnd [Pos (lt_var name)]
              (mk_constraint_ge 1 Y (-1) X 1));
            (SOME (strlit "al1"),at_least_one
              [
                Pos (lt_var name); Pos (gt_var name);
                Pos (INL (Ge Z 1))
              ]);
          ]),ec')
End

Theorem enc_rel_List_refl_mul:
  set ls' = set $ MAP SND ls ⇒
  enc_rel wi (List ls) ls' ec ec
Proof
  rw[enc_rel_def]>>
  fs[EVERY_MEM,EXTENSION,MEM_MAP]>>
  metis_tac[]
QED

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
  >> (
    pure_rewrite_tac[GSYM APPEND_ASSOC]>>
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_ge>>
    simp[enc_rel_List_refl_mul])
QED

(* HERE *)
Definition cencode_not_equal_def:
  cencode_not_equal bnd Zr X Y name ec =
  let xgty = (mk_constraint_ge 1 X (-1) Y 1) in
  let ygtx = (mk_constraint_ge 1 Y (-1) X 1) in
    case Zr of
      NONE =>
      (List
        [
          (SOME (strlit "gt"),bits_imply bnd [Pos (ne_var name)] xgty);
          (SOME (strlit "lt"),bits_imply bnd [Neg (ne_var name)] ygtx)
        ],ec)
    | SOME (INL Z) =>
        let
          (e,ec') = cencode_ge bnd Z 1 ec
        in
          (Append e $
            List $
              (MAP (λc. (SOME (strlit "gt"),c)) $
                bimply_bits bnd [Pos (gt_var name)] xgty) ++
              (MAP (λc. (SOME (strlit "lt"),c)) $
                bimply_bits bnd [Pos (lt_var name)] ygtx) ++
              [
               (SOME (strlit "al1"),at_least_one
                 [
                   Pos (lt_var name);
                   Pos (gt_var name);
                   Neg (INL (Ge Z 1))
                 ])
              ],ec')
  (*
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    MAP (bits_imply bnd [Neg (INL (Ge Z 1))])
      [
        mk_constraint_ge 1 (X) (-1) (Y) 0;
        mk_constraint_ge 1 (Y) (-1) (X) 0
      ] ++
    [
      bits_imply bnd [Pos (gt_var name)] xgty;
      bits_imply bnd [Pos (lt_var name)] ygtx;
      at_least_one
        [Pos (lt_var name); Pos (gt_var name);
          Neg (INL (Ge Z 1))];
    ]*)
End

Theorem cencode_not_equal_sem:
  valid_assignment bnd wi ∧
  cencode_not_equal bnd Zr X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_not_equal bnd Zr X Y name) ec ec'
Proof
  rw[cencode_not_equal_def,encode_not_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >- simp[enc_rel_List_refl_mul]
  >> cheat
QED
