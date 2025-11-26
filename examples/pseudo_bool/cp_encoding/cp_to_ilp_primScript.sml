(*
  Formalization of the CP to ILP phase (prim constraints)
*)
Theory cp_to_ilp_prim
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition encode_ne_def:
  encode_ne bnd X Y =
    [
      bits_imply bnd [Pos (INR (Ne X Y))] (mk_constraint_ge 1 X (-1) Y 1);
      bits_imply bnd [Neg (INR (Ne X Y))] (mk_constraint_ge 1 Y (-1) X 1)
    ]
End

Definition encode_equal_def:
  encode_equal bnd Zr X Y =
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
      bits_imply bnd
        [Neg (INL (Ge Z 1)); Pos (INR (Ne X Y))]
          (mk_constraint_ge 1 X (-1) Y 1);
      bits_imply bnd
        [Neg (INL (Ge Z 1)); Neg (INR (Ne X Y))]
          (mk_constraint_ge 1 Y (-1) X 1)
    ]
End

Theorem encode_equal_sem_1:
  valid_assignment bnd wi ∧
  reify_sem Zr wi
    (varc wi X = varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi))
    (encode_equal bnd Zr X Y)
Proof
  rw[reify_sem_def,encode_equal_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_reif_def,reify_flag_def]
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC
QED

Theorem encode_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_equal bnd Zr X Y) ⇒
  reify_sem Zr wi
    (varc wi X = varc wi Y)
Proof
  rw[reify_sem_def,encode_equal_def]>>
  every_case_tac>>gvs[]
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC>>
  Cases_on`wb (INR (Ne X Y))`>>gvs[]
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC
QED

Definition encode_not_equal_def:
  encode_not_equal bnd Zr X Y =
  let constr = encode_ne bnd X Y in
  case Zr of
    NONE => constr
  | SOME (INL Z) =>
    encode_ge bnd Z 1 ++
    [
      bits_imply bnd
        [Pos (INL (Ge Z 1)); Pos (INR (Ne X Y))]
          (mk_constraint_ge 1 X (-1) Y 1);
      bits_imply bnd
        [Pos (INL (Ge Z 1)); Neg (INR (Ne X Y))]
          (mk_constraint_ge 1 Y (-1) X 1)
    ]
  | SOME (INR Z) =>
    encode_ge bnd Z 1 ++
    MAP (bits_imply bnd [Neg (INL (Ge Z 1))])
      [
        mk_constraint_ge 1 (X) (-1) (Y) 0;
        mk_constraint_ge 1 (Y) (-1) (X) 0
      ] ++
    [
      bits_imply bnd
        [Pos (INL (Ge Z 1)); Pos (INR (Ne X Y))]
          (mk_constraint_ge 1 X (-1) Y 1);
      bits_imply bnd
        [Pos (INL (Ge Z 1)); Neg (INR (Ne X Y))]
          (mk_constraint_ge 1 Y (-1) X 1)
    ]
End

Theorem encode_not_equal_sem_1:
  valid_assignment bnd wi ∧
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi))
    (encode_not_equal bnd Zr X Y)
Proof
  rw[reify_sem_def,encode_not_equal_def,encode_ne_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_flag_def,reify_reif_def]
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC
  >-  intLib.ARITH_TAC
QED

Theorem encode_not_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_not_equal bnd Zr X Y) ⇒
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y)
Proof
  rw[reify_sem_def,encode_not_equal_def,encode_ne_def]>>
  gvs[AllCasePreds(),reify_avar_def,reify_flag_def,reify_reif_def]>>
  every_case_tac>>gvs[]
  >- (
    Cases_on`wb (INR (Ne X Y))`>>gvs[]>>
    intLib.ARITH_TAC)
  >- (
    Cases_on`wb (INR (Ne X Y))`>>gvs[]>>
    intLib.ARITH_TAC)
  >- (
    Cases_on`wb (INR (Ne X Y))`>>gvs[]>>
    intLib.ARITH_TAC)
QED

Definition encode_prim_constr_def:
  encode_prim_constr bnd c =
  case c of
    Cmpop Zr cmp X Y =>
      (case cmp of
        Equal => encode_equal bnd Zr X Y
      | NotEqual => encode_not_equal bnd Zr X Y
      | _ => ARB)
  | _ => ARB
End

Theorem encode_prim_constr_sem_1:
  valid_assignment bnd wi ∧
  prim_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi))
    (encode_prim_constr bnd c)
Proof
  Cases_on`c`>>
  rw[encode_prim_constr_def,prim_constr_sem_def]
  >- cheat
  >- cheat
  >- (
    gvs[cmpop_sem_def]>>
    every_case_tac>>
    gvs[cmpop_val_def]
    >- metis_tac[encode_equal_sem_1]
    >- metis_tac[encode_not_equal_sem_1]
    >> cheat)
QED

Theorem encode_prim_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_prim_constr bnd c) ⇒
  prim_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_prim_constr_def,prim_constr_sem_def]
  >- cheat
  >- cheat
  >- (
    gvs[cmpop_sem_def]>>
    every_case_tac>>
    gvs[cmpop_val_def]
    >- metis_tac[encode_equal_sem_2]
    >- metis_tac[encode_not_equal_sem_2]
    >> cheat)
QED


