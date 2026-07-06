(*
  Formalization of the CP to ILP phase (prim constraints)
*)
Theory cp_to_ilp_prim
Libs
  preamble
Ancestors
  pbc pbc_encode cp ilp cp_to_ilp int_bitwise int_bitwiseExtra

Definition cmk_eq_def[simp]:
  cmk_eq name X Y =
  [
    (SOME (mk_name name («ge»)), mk_ge X Y);
    (SOME (mk_name name («le»)), mk_le X Y)
  ]
End

Definition cencode_equal_1_def[simp]:
  cencode_equal_1 bnd Zc X Y name =
  List (
    MAP (I ## bits_imply bnd [reif_gen Zc])
      (cmk_eq name X Y))
End

Definition cencode_equal_2_def[simp]:
  cencode_equal_2 bnd Zc X Y name =
  Append
    (cencode_equal_1 bnd Zc X Y name) $
    Append
      (cvar_imply bnd (gtv name) (mk_gt X Y)) $
    Append
      (cvar_imply bnd (ltv name) (mk_lt X Y)) $
    (cat_least_one name «»
      [Pos (ltv name); Pos (gtv name); reif_gen Zc])
End

Definition encode_equal_def:
  encode_equal bnd Zr X Y name =
  case Zr of
    NONE => abstrl (cmk_eq name X Y)
  | SOME (INL Zc) =>
    encode_reif_gen bnd Zc ++
    abstr (cencode_equal_1 bnd Zc X Y name)
  | SOME (INR Zc) =>
    encode_reif_gen bnd Zc ++
    abstr (cencode_equal_2 bnd Zc X Y name)
End

Theorem encode_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Cmpop reif cmp X Y)) ∧
  reify_sem Zr wi
    (varc wi X = varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_equal bnd Zr X Y name)
Proof
  rw[encode_equal_def]>>
  every_case_tac>>
  fs[reify_sem_def]>>
  every_case_tac
  >-intLib.ARITH_TAC>>
  rw[encode_reif_gen_sem,lit_reify_avar_reif_gen,
    reify_avar_def,reify_reif_def,reify_flag_def,SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem encode_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_equal bnd Zr X Y name) ⇒
  reify_sem Zr wi
    (varc wi X = varc wi Y)
Proof
  rw[encode_equal_def]>>
  every_case_tac>>
  simp[reify_sem_def]>>
  every_case_tac
  >-(
    gs[EVERY_APPEND]>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_APPEND,encode_reif_gen_sem]>>
    strip_tac>>
    ntac 2 (first_x_assum drule)>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_APPEND,encode_reif_gen_sem]>>
    rename1 ‘P ⇔ _’>>
    Cases_on ‘P’>>
    intLib.ARITH_TAC)
QED

Definition cencode_not_equal_1_def[simp]:
  cencode_not_equal_1 bnd X Y name =
  List [
    (SOME (mk_name name («gt»)),
      bits_imply bnd [Pos (nev name)] (mk_gt X Y));
    (SOME (mk_name name («lt»)),
      bits_imply bnd [Neg (nev name)] (mk_lt X Y))
  ]
End

Definition cencode_not_equal_2_def[simp]:
  cencode_not_equal_2 bnd Zc X Y name =
  Append
    (cbimply_var bnd (gtv name) (mk_gt X Y)) $
  Append
    (cbimply_var bnd (ltv name) (mk_lt X Y)) $
  (cat_least_one name «»
      [Pos (ltv name); Pos (gtv name); negate (reif_gen Zc)])
End

Definition cencode_not_equal_3_def[simp]:
  cencode_not_equal_3 bnd Zc X Y name =
  Append
    (List (MAP (I ## bits_imply bnd [negate (reif_gen Zc)])
      (cmk_eq name X Y))) $
  cencode_not_equal_2 bnd Zc X Y name
End

Definition encode_not_equal_def:
  encode_not_equal bnd Zr X Y name =
  case Zr of
    NONE =>
    abstr (cencode_not_equal_1 bnd X Y name)
  | SOME (INL Zc) =>
    encode_reif_gen bnd Zc ++
    abstr (cencode_not_equal_2 bnd Zc X Y name)
  | SOME (INR Zc) =>
    encode_reif_gen bnd Zc ++
    abstr (cencode_not_equal_3 bnd Zc X Y name)
End

Theorem encode_not_equal_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Cmpop reif cmp X Y)) ∧
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_not_equal bnd Zr X Y name)
Proof
  rw[encode_not_equal_def]>>
  every_case_tac>>
  fs[reify_sem_def,reify_avar_def,reify_flag_def]>>
  every_case_tac
  >-intLib.ARITH_TAC>>
  rw[encode_reif_gen_sem,lit_reify_avar_reif_gen,
     reify_avar_def,reify_reif_def,reify_flag_def,SF DNF_ss]
  >~[‘_ ∨ _ ∨ ¬P’]
  >-(
    Cases_on ‘P’>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

Theorem encode_not_equal_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_not_equal bnd Zr X Y name) ⇒
  reify_sem Zr wi
    (varc wi X ≠ varc wi Y)
Proof
  rw[encode_not_equal_def]>>
  every_case_tac>>
  simp[reify_sem_def]>>
  every_case_tac
  >-(
    gs[EVERY_APPEND]>>
    rename1 ‘¬P ⇒ _’>>
    Cases_on ‘P’>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_APPEND,encode_reif_gen_sem]>>
    strip_tac>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_APPEND,encode_reif_gen_sem]>>
    rename1 ‘P ⇔ _’>>
    Cases_on ‘P’>>
    intLib.ARITH_TAC)
QED

Definition encode_order_cmpops_def:
  encode_order_cmpops bnd Zr cmp X Y =
  let constr = encode_lex cmp X Y
  in
    case Zr of
      NONE => [constr]
    | SOME (INL Zc) =>
      encode_reif_gen bnd Zc ++
      [bits_imply bnd [reif_gen Zc] constr]
    | SOME (INR Zc) =>
      encode_reif_gen bnd Zc ++
      bimply_bits bnd [reif_gen Zc] constr
End

Theorem encode_order_cmpops_sem_1:
  valid_assignment bnd wi ∧
  reify_sem Zr wi (cmpop_val (Lexop cmp) (varc wi X) (varc wi Y)) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_order_cmpops bnd Zr cmp X Y)
Proof
  rw[encode_order_cmpops_def]>>
  every_case_tac
  >-(
    rw[encode_lex_def]>>
    every_case_tac>>
    fs[reify_sem_def,cmpop_val_def]>>
    intLib.ARITH_TAC)>>
  rename1 ‘reif_gen z’>>
  PairCases_on ‘z’>>
  simp[EVERY_APPEND,reify_avar_def,reify_reif_def,
    encode_reif_gen_sem,lit_reify_avar_reif_gen]>>
  gvs[encode_lex_cmpop_val]>>
  fs[cmpop_val_def,reify_sem_def]
QED

Theorem encode_order_cmpops_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_order_cmpops bnd Zr cmp X Y) ⇒
  reify_sem Zr wi (cmpop_val (Lexop cmp) (varc wi X) (varc wi Y))
Proof
  rw[encode_order_cmpops_def]>>
  every_case_tac>>
  simp[reify_sem_def]
  >-(
    fs[encode_lex_def,cmpop_val_def]>>
    every_case_tac>>
    fs[iconstraint_sem_def]>>
    intLib.ARITH_TAC)>>
  every_case_tac>>
  gvs[EVERY_APPEND,encode_reif_gen_sem,cmpop_val_def]
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
      [mk_name name («ge»); mk_name name («le»)]
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
      [mk_name name («ge»); mk_name name («le»)]
      (encode_minus X Y Z)
    )
End

(* lle means X ≤ Z, rle means Y ≤ Z*)
Definition cencode_min_def:
  cencode_min bnd X Y Z name =
  let
    lle = INR (name, Flag («lle»));
    rle = INR (name, Flag («rle»));
  in
  Append (cvar_imply bnd lle (mk_le X Z)) $
  Append (cvar_imply bnd rle (mk_le Y Z)) $
  Append
    (List
      (mk_annotate
      [mk_name name («lge»); mk_name name («rge»)]
      [mk_ge X Z; mk_ge Y Z])) $
  cat_least_one name «» [Pos lle; Pos rle]
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
    lge = INR (name, Flag («lge»));
    rge = INR (name, Flag («rge»));
  in
  Append (cvar_imply bnd lge (mk_ge X Z)) $
  Append (cvar_imply bnd rge (mk_ge Y Z)) $
  Append
    (List
      (mk_annotate
      [mk_name name («lle»); mk_name name («rle»)]
      [mk_le X Z; mk_le Y Z])) $
  cat_least_one name «» [Pos lge; Pos rge]
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

(* Multiplication X * Y = Z by long multiplication on magnitudes;
   binding spec: ENCODING_MULTIPLY.md *)

(* bits needed for |v| with v ∈ [lb,ub]: |v| < 2 ** mult_width lb ub *)
Definition mult_width_def:
  mult_width lb ub =
  LENGTH (bits_of_num (MAX (Num (ABS lb)) (Num (ABS ub))))
End

(* bit b of |X| (axis = 0) resp. |Y| (axis = 1) *)
Definition mult_binbit_def[simp]:
  mult_binbit name axis b = INR (name, Indices [axis; b] (SOME «bin»))
End

(* product flag: bit i of |X| AND bit j of |Y| *)
Definition mult_prodbit_def[simp]:
  mult_prodbit name i j = INR (name, Indices [i; j] (SOME «prod»))
End

(* BinRep(|X|) resp. BinRep(|Y|) as a positive bit sum *)
Definition mult_bin_term_def:
  mult_bin_term name axis w = pos_num (mult_binbit name axis) w
End

(* BinRep(|XY|) = Σ_{i<n,j<m} 2^(i+j) · prod_ij *)
Definition mult_prod_term_def:
  mult_prod_term pf n m =
  FLAT (GENLIST (λi. GENLIST (λj. (&(2 ** (i + j)), Pos (pf i j))) m) n)
End

(* c·Zc + bs ≥ k, folding a constant Zc into the RHS *)
Definition mult_varc_row_def:
  mult_varc_row c Zc bs k =
  case Zc of
    INL v => ([(c,v)], bs, k)
  | INR i => ([], bs, k - c * i)
End

(* the four [Zc≥0]-guarded rows pinning eval bs = |Zc| *)
Definition mult_mag_rows_def:
  mult_mag_rows bnd Zc bs =
  let
    g = Pos (INL (Ge Zc 0));
    ng = Neg (INL (Ge Zc 0));
    nbs = flip_coeffs bs
  in
  [
    bits_imply bnd [g] (mult_varc_row 1 Zc nbs 0);
    bits_imply bnd [g] (mult_varc_row (-1) Zc bs 0);
    bits_imply bnd [ng] (mult_varc_row 1 Zc bs 0);
    bits_imply bnd [ng] (mult_varc_row (-1) Zc nbs 0)
  ]
End

(* All fresh rows (the reified atoms come separately, via the ec cache):
   4 magnitude rows each for X, Y; n·m fully reified product flags;
   4 rows pinning |Z| to BinRep(|XY|); 6 sign clauses. *)
Definition cencode_mult_body_def:
  cencode_mult_body bnd X Y Z name =
  let
    (lbx,ubx) = varc_bnd bnd X;
    (lby,uby) = varc_bnd bnd Y;
    n = mult_width lbx ubx;
    m = mult_width lby uby;
    xbs = mult_bin_term name 0 n;
    ybs = mult_bin_term name 1 m;
    pbs = mult_prod_term (mult_prodbit name) n m;
    px0 = Pos (INL (Eq X 0));
    py0 = Pos (INL (Eq Y 0));
    px1 = Pos (INL (Ge X 1));
    py1 = Pos (INL (Ge Y 1));
    nx = Neg (INL (Ge X 0));
    ny = Neg (INL (Ge Y 0));
    zp = ([],[(1,Pos (INL (Ge Z 0)))],1);
    zn = ([],[(1,Neg (INL (Ge Z 0)))],1)
  in
  Append
    (List (mk_annotate
      [mk_name name («Xge0_ge»); mk_name name («Xge0_le»);
       mk_name name («Xlt0_ge»); mk_name name («Xlt0_le»)]
      (mult_mag_rows bnd X xbs))) $
  Append
    (List (mk_annotate
      [mk_name name («Yge0_ge»); mk_name name («Yge0_le»);
       mk_name name («Ylt0_ge»); mk_name name («Ylt0_le»)]
      (mult_mag_rows bnd Y ybs))) $
  Append
    (flat_app (GENLIST (λi.
      flat_app (GENLIST (λj.
        cbimply_var bnd (mult_prodbit name i j)
          ([],[(1,Pos (mult_binbit name 0 i));
               (1,Pos (mult_binbit name 1 j))],2)) m)) n)) $
  Append
    (List (mk_annotate
      [mk_name name («mag_Zge0_ge»); mk_name name («mag_Zge0_le»);
       mk_name name («mag_Zlt0_ge»); mk_name name («mag_Zlt0_le»)]
      (mult_mag_rows bnd Z pbs))) $
    (List (mk_annotate
      [mk_name name («sgn_x0»); mk_name name («sgn_y0»);
       mk_name name («sgn_pp»); mk_name name («sgn_nn»);
       mk_name name («sgn_np»); mk_name name («sgn_pn»)]
      [
        bits_imply bnd [px0] zp;
        bits_imply bnd [py0] zp;
        bits_imply bnd [px1; py1] zp;
        bits_imply bnd [nx; ny] zp;
        bits_imply bnd [nx; py1] zn;
        bits_imply bnd [px1; ny] zn
      ]))
End

Definition cencode_mult_def:
  cencode_mult bnd X Y Z name ec =
  let
    (e1,ec1) = cencode_full_eq bnd X 0 ec;
    (e2,ec2) = cencode_full_eq bnd Y 0 ec1;
    (e3,ec3) = cencode_ge bnd Z 0 ec2
  in
    (Append e1 $ Append e2 $ Append e3 $
      cencode_mult_body bnd X Y Z name, ec3)
End

Definition encode_mult_def:
  encode_mult bnd X Y Z name =
  encode_full_eq bnd X 0 ++
  encode_full_eq bnd Y 0 ++
  encode_ge bnd Z 0 ++
  abstr (cencode_mult_body bnd X Y Z name)
End

Theorem mult_varc_row_sem[local,simp]:
  iconstraint_sem (mult_varc_row c Zc bs k) (wi,wb) ⇔
  c * varc wi Zc + eval_lin_term wb bs ≥ k
Proof
  rw[mult_varc_row_def]>>
  every_case_tac>>
  simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def]>>
  intLib.ARITH_TAC
QED

(* given an exact [Zc ≥ 0] atom, the four rows pin eval bs to |Zc| *)
Theorem mult_mag_rows_sem[local]:
  valid_assignment bnd wi ∧
  (wb (INL (Ge Zc 0)) ⇔ varc wi Zc ≥ 0) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (mult_mag_rows bnd Zc bs) ⇔
   eval_lin_term wb bs = ABS (varc wi Zc))
Proof
  rw[mult_mag_rows_def]>>
  Cases_on ‘wb (INL (Ge Zc 0))’>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Theorem mult_width_bound[local]:
  valid_assignment bnd wi ∧ varc_bnd bnd X = (lb,ub) ⇒
  Num (ABS (varc wi X)) < 2 ** mult_width lb ub
Proof
  simp[mult_width_def]>>
  namedCases_on ‘X’ ["v","c"]>>
  gvs[varc_bnd_def,varc_def]
  >- (
    rw[valid_assignment_def]>>
    first_x_assum (qspec_then ‘v’ mp_tac)>>
    simp[]>>strip_tac>>
    ‘Num (ABS (wi v)) ≤ MAX (Num (ABS lb)) (Num (ABS ub))’ by
      (rw[MAX_DEF]>>intLib.ARITH_TAC)>>
    metis_tac[LESS_LENGTH_bits_of_num,LESS_EQ_LESS_TRANS])>>
  rw[]>>gvs[MAX_DEF]>>
  metis_tac[LESS_LENGTH_bits_of_num]
QED

(* reified magnitude bits evaluate back to |v| *)
Theorem mult_bin_eval[local]:
  Num (ABS v) < 2 ** w ∧
  (∀b. b < w ⇒ (wb (flag b) ⇔ BIT b (Num (ABS v)))) ⇒
  eval_lin_term wb (pos_num flag w) = ABS v
Proof
  rw[]>>
  drule_all pos_num_reify_eq>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem mult_two_pos_sem[local,simp]:
  iconstraint_sem ([],[(1,Pos a);(1,Pos b)],2) (wi,wb) ⇔ wb a ∧ wb b
Proof
  simp[eval_lin_term_def,iSUM_def]>>
  Cases_on ‘wb a’>>Cases_on ‘wb b’>>simp[]
QED

(* one row of the long multiplication *)
Theorem eval_mult_prod_row[local]:
  ∀m.
  (∀j. j < m ⇒ (wb (pf j) ⇔ g ∧ wb (by j))) ⇒
  eval_lin_term wb (GENLIST (λj. (&(2 ** (i + j)), Pos (pf j))) m) =
  &(2 ** i) * b2i g * eval_lin_term wb (pos_num by m)
Proof
  Induct>>
  rw[pos_num_def,GENLIST,SNOC_APPEND]>>
  Cases_on ‘g’>>Cases_on ‘wb (by m)’>>
  gvs[EXP_ADD,integerTheory.INT_LDISTRIB]
QED

(* AND-reified product flags: the shifted sum multiplies out, for ANY bits *)
Theorem eval_mult_prod_term[local]:
  ∀n.
  (∀i j. i < n ∧ j < m ⇒ (wb (pf i j) ⇔ wb (bx i) ∧ wb (by j))) ⇒
  eval_lin_term wb (mult_prod_term pf n m) =
  eval_lin_term wb (pos_num bx n) * eval_lin_term wb (pos_num by m)
Proof
  Induct>>
  rw[mult_prod_term_def,pos_num_def,GENLIST,SNOC_APPEND]>>
  gvs[GSYM pos_num_def,GSYM mult_prod_term_def]>>
  ‘eval_lin_term wb (GENLIST (λj. (&(2 ** (j + n)),Pos (pf n j))) m) =
   &(2 ** n) * b2i (wb (bx n)) * eval_lin_term wb (pos_num by m)’ by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM]>>
     irule eval_mult_prod_row>>rw[])>>
  simp[integerTheory.INT_RDISTRIB]
QED

Theorem mult_prod_block_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λls. abstr ls)
      (GENLIST (λi.
        flat_app (GENLIST (λj.
          cbimply_var bnd (INR (name,Indices [i; j] (SOME «prod»)))
            ([],[(1,Pos (INR (name,Indices [0; i] (SOME «bin»))));
                 (1,Pos (INR (name,Indices [1; j] (SOME «bin»))))],2)) m)) n))) ⇔
   ∀i j. i < n ∧ j < m ⇒
     (wb (INR (name,Indices [i; j] (SOME «prod»))) ⇔
      wb (INR (name,Indices [0; i] (SOME «bin»))) ∧
      wb (INR (name,Indices [1; j] (SOME «bin»)))))
Proof
  rw[append_flat_app,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,cbimply_var_def]>>
  metis_tac[]
QED

Theorem mult_sign_facts[local]:
  ((x:int) = 0 ⇒ x * y ≥ 0) ∧ (y = 0 ⇒ x * y ≥ 0) ∧
  (x ≥ 1 ∧ y ≥ 1 ⇒ x * y ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ x * y ≥ 0) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(x * y ≥ 0)) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(x * y ≥ 0))
Proof
  rw[integerTheory.INT_GE,integerTheory.INT_NOT_LE]>>
  simp[integerTheory.INT_MUL_SIGN_CASES,integerTheory.INT_LE_LT]>>
  intLib.ARITH_TAC
QED

Theorem mult_abs_sign_eq[local]:
  ABS z = ABS p ∧ (0 < p ∧ z ≥ 0 ∨ p < 0 ∧ ¬(z ≥ 0) ∨ p = 0) ⇒ z = p
Proof
  intLib.ARITH_TAC
QED

(* |z| = |x·y| plus the four sign clauses force z = x·y *)
Theorem mult_sign_bridge[local]:
  ABS z = ABS (x * y) ∧
  (x ≥ 1 ∧ y ≥ 1 ⇒ z ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ z ≥ 0) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(z ≥ 0)) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(z ≥ 0)) ⇒
  z = x * y
Proof
  strip_tac>>
  irule mult_abs_sign_eq>>
  simp[]>>
  simp[integerTheory.INT_MUL_SIGN_CASES]>>
  Cases_on ‘0 < x’>>Cases_on ‘0 < y’>>gvs[]>>
  qpat_x_assum ‘ABS _ = _’ kall_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_mult_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Nonlinop Mult X Y Z)) ∧
  varc wi X * varc wi Y = varc wi Z ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_mult bnd X Y Z name)
Proof
  rw[encode_mult_def]>>
  simp[reify_avar_def,reify_reif_def]>>
  rw[cencode_mult_body_def]>>rpt(pairarg_tac>>gvs[])>>
  simp[mult_mag_rows_sem,reify_avar_def,reify_reif_def]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  simp[]>>
  simp[mult_sign_facts]>>
  qpat_x_assum ‘_ * _ = varc _ _’ (assume_tac o GSYM)>>
  gvs[mult_sign_facts]>>
  ‘∀ax b. reify_avar cs wi (INR (name,Indices [ax; b] (SOME «bin»))) ⇔
     BIT b (Num (ABS (varc wi (if ax = 0 then X else Y))))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘∀i j. reify_avar cs wi (INR (name,Indices [i; j] (SOME «prod»))) ⇔
     BIT i (Num (ABS (varc wi X))) ∧ BIT j (Num (ABS (varc wi Y)))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbx ubx)) = ABS (varc wi X)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[mult_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby)) = ABS (varc wi Y)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[mult_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (mult_prod_term (mult_prodbit name) (mult_width lbx ubx)
        (mult_width lby uby)) =
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbx ubx)) *
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  simp[mult_bin_term_def,GSYM integerTheory.INT_ABS_MUL]>>
  rw[EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,cbimply_var_def]>>
  rw[append_flat_app,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST]>>fs[]
QED

Theorem encode_mult_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_mult bnd X Y Z name) ⇒
  varc wi X * varc wi Y = varc wi Z
Proof
  rw[encode_mult_def]>>
  fs[cencode_mult_body_def]>>rpt(pairarg_tac>>gvs[])>>
  gs[mult_mag_rows_sem,mult_prod_block_sem]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  fs[mult_bin_term_def]>>
  ‘eval_lin_term wb (mult_prod_term (mult_prodbit name) (mult_width lbx ubx)
     (mult_width lby uby)) =
   eval_lin_term wb (pos_num (mult_binbit name 0) (mult_width lbx ubx)) *
   eval_lin_term wb (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  gvs[GSYM integerTheory.INT_ABS_MUL]>>
  once_rewrite_tac[EQ_SYM_EQ]>>
  irule mult_sign_bridge>>
  simp[]>>
  metis_tac[integerTheory.INT_ABS_MUL]
QED

Theorem cencode_mult_sem:
  valid_assignment bnd wi ∧
  cencode_mult bnd X Y Z name ec = (es, ec') ⇒
  enc_rel wi es (encode_mult bnd X Y Z name) ec ec'
Proof
  rw[cencode_mult_def,encode_mult_def]>>
  gvs[UNCURRY_EQ]>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  metis_tac[enc_rel_Append,enc_rel_encode_full_eq,
    enc_rel_encode_ge,enc_rel_abstr]
QED

(* ===================================================================== *)
(* Divide / Modulus (truncated): binding spec ENCODING_DIVMOD.md.        *)
(* Both reuse the multiply magnitude/product helpers; the op-specific    *)
(* work is the sign-gated identity / range / sign rows, discharged via   *)
(* the integer bridge lemmas below (INT_QUOT_UNIQUE / INT_REM_UNIQUE     *)
(* for soundness, INT_REMQUOT for completeness).                         *)
(* ===================================================================== *)

(* sign of a product from the signs of its factors *)
Theorem prod_sign[local]:
  (0 ≤ (z:int) ∧ 0 ≤ y ⇒ 0 ≤ z*y) ∧
  (z ≤ 0 ∧ y ≤ 0 ⇒ 0 ≤ z*y) ∧
  (0 ≤ z ∧ y ≤ 0 ⇒ z*y ≤ 0) ∧
  (z ≤ 0 ∧ 0 ≤ y ⇒ z*y ≤ 0)
Proof
  rpt strip_tac>>
  rw[GSYM integerTheory.INT_NOT_LT, integerTheory.INT_MUL_SIGN_CASES]>>
  intLib.ARITH_TAC
QED

(* the sign clauses force the product to take the sign of x *)
Theorem zy_sign[local]:
  y ≠ 0 ∧
  (x ≥ 1 ∧ y ≥ 1 ⇒ z ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ z ≥ 0) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(z ≥ 1)) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(z ≥ 1)) ∧
  (x = 0 ⇒ z * y = 0) ⇒
  (0 ≤ x ⇒ 0 ≤ z * y) ∧ (x < 0 ⇒ z * y ≤ 0)
Proof
  strip_tac>>conj_tac>>strip_tac
  >- (
    Cases_on ‘x = 0’ >- gvs[]>>
    ‘x ≥ 1’ by intLib.ARITH_TAC>>
    Cases_on ‘0 ≤ y’
    >- (‘y ≥ 1’ by intLib.ARITH_TAC>>‘z ≥ 0’ by gs[]>>
        irule (cj 1 prod_sign)>>intLib.ARITH_TAC)
    >- (‘¬(y ≥ 0)’ by intLib.ARITH_TAC>>‘¬(z ≥ 1)’ by gs[]>>
        irule (cj 2 prod_sign)>>intLib.ARITH_TAC))
  >- (
    Cases_on ‘0 ≤ y’
    >- (‘¬(x ≥ 0)’ by intLib.ARITH_TAC>>‘y ≥ 1’ by intLib.ARITH_TAC>>
        ‘¬(z ≥ 1)’ by gs[]>>
        irule (cj 4 prod_sign)>>intLib.ARITH_TAC)
    >- (‘¬(x ≥ 0)’ by intLib.ARITH_TAC>>‘¬(y ≥ 0)’ by intLib.ARITH_TAC>>
        ‘z ≥ 0’ by gs[]>>
        irule (cj 3 prod_sign)>>intLib.ARITH_TAC))
QED

Theorem div_sign_bridge[local]:
  y ≠ 0 ∧
  (x ≥ 1 ∧ y ≥ 1 ⇒ z ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ z ≥ 0) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(z ≥ 1)) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(z ≥ 1)) ∧
  (x = 0 ⇒ ¬(z ≥ 1)) ∧
  (x ≥ 0 ⇒ 0 ≤ x - ABS (z * y) ∧ x - ABS (z * y) ≤ ABS y - 1) ∧
  (¬(x ≥ 1) ⇒ x + ABS (z * y) ≤ 0 ∧ -x - ABS (z * y) ≤ ABS y - 1) ⇒
  x quot y = z
Proof
  rpt strip_tac>>
  ‘0 ≤ ABS (z * y)’ by simp[integerTheory.INT_ABS_POS]>>
  ‘x = 0 ⇒ z * y = 0’ by (strip_tac>>intLib.ARITH_TAC)>>
  drule_all zy_sign>>strip_tac>>
  irule integerTheory.INT_QUOT_UNIQUE>>
  qexists_tac ‘x - z * y’>>
  Cases_on ‘0 ≤ x’>>gs[]>>Cases_on ‘0 < x’>>gs[]>>
  intLib.ARITH_TAC
QED

(* sign of a truncated quotient from the signs of dividend and divisor,
   stated in the sign-gate forms used by the div body rows *)
Theorem quot_sign[local]:
  y ≠ 0 ⇒
  (x ≥ 1 ∧ y ≥ 1 ⇒ x quot y ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ x quot y ≥ 0) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(x quot y ≥ 1)) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(x quot y ≥ 1)) ∧
  (x = 0 ⇒ ¬(x quot y ≥ 1))
Proof
  strip_tac>>
  qspec_then ‘x’ strip_assume_tac integerTheory.INT_NUM_CASES>>
  qspec_then ‘y’ strip_assume_tac integerTheory.INT_NUM_CASES>>
  gvs[integerTheory.INT_QUOT_NEG,integerTheory.INT_QUOT,
      integerTheory.INT_QUOT_0]>>
  rw[]>>intLib.ARITH_TAC
QED

(* |quotient| ≤ |dividend| (needed to bound the free quotient magnitude bits) *)
Theorem quot_abs_le[local]:
  y ≠ 0 ⇒ ABS (x quot y) ≤ ABS x
Proof
  strip_tac>>
  ‘ABS (x quot y * y) ≤ ABS x’ by (irule integerTheory.INT_ABS_QUOT>>simp[])>>
  ‘ABS (x quot y) ≤ ABS (x quot y * y)’ by (
    ‘ABS (x quot y) * ABS y = ABS (x quot y * y)’ by
      simp[integerTheory.INT_ABS_MUL]>>
    ‘1 ≤ ABS y’ by (
      ‘ABS y ≠ 0’ by simp[integerTheory.INT_ABS_EQ0]>>
      ‘0 ≤ ABS y’ by simp[integerTheory.INT_ABS_POS]>>
      intLib.ARITH_TAC)>>
    Cases_on ‘ABS (x quot y) = 0’ >- gvs[]>>
    ‘0 < ABS (x quot y)’ by (
      ‘0 ≤ ABS (x quot y)’ by simp[integerTheory.INT_ABS_POS]>>
      intLib.ARITH_TAC)>>
    ‘ABS (x quot y) * 1 ≤ ABS (x quot y) * ABS y’ by
      metis_tac[integerTheory.INT_LE_MONO]>>
    gvs[])>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

(* the free quotient magnitude fits the dividend's bit width *)
Theorem quot_width_bound[local]:
  valid_assignment bnd wi ∧ varc_bnd bnd X = (lbx,ubx) ∧ varc wi Y ≠ 0 ⇒
  Num (ABS (varc wi X quot varc wi Y)) < 2 ** mult_width lbx ubx
Proof
  rw[]>>
  ‘Num (ABS (varc wi X)) < 2 ** mult_width lbx ubx’ by
    metis_tac[mult_width_bound]>>
  ‘ABS (varc wi X quot varc wi Y) ≤ ABS (varc wi X)’ by
    (irule quot_abs_le>>simp[])>>
  ‘Num (ABS (varc wi X quot varc wi Y)) ≤ Num (ABS (varc wi X))’ by (
    ‘0 ≤ ABS (varc wi X quot varc wi Y) ∧ 0 ≤ ABS (varc wi X)’ by
      simp[integerTheory.INT_ABS_POS]>>
    intLib.ARITH_TAC)>>
  metis_tac[LESS_EQ_LESS_TRANS]
QED

(* sign of quotient*divisor follows the dividend's sign (Q*Y = ±(X - R)) *)
Theorem quot_prod_sign[local]:
  y ≠ 0 ⇒
  (x ≥ 0 ⇒ 0 ≤ x quot y * y) ∧
  (¬(x ≥ 1) ⇒ x quot y * y ≤ 0)
Proof
  strip_tac>>
  ‘(x ≥ 1 ∧ y ≥ 1 ⇒ x quot y ≥ 0) ∧
   (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ x quot y ≥ 0) ∧
   (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(x quot y ≥ 1)) ∧
   (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(x quot y ≥ 1)) ∧
   (x = 0 ⇒ ¬(x quot y ≥ 1))’ by (irule quot_sign>>simp[])>>
  conj_tac>>strip_tac
  >- (
    Cases_on ‘x = 0’ >- gvs[integerTheory.INT_QUOT_0]>>
    ‘x ≥ 1’ by intLib.ARITH_TAC>>
    Cases_on ‘y ≥ 1’
    >- (‘x quot y ≥ 0’ by gs[]>>irule (cj 1 prod_sign)>>intLib.ARITH_TAC)
    >- (‘¬(y ≥ 0)’ by intLib.ARITH_TAC>>‘¬(x quot y ≥ 1)’ by gs[]>>
        irule (cj 2 prod_sign)>>intLib.ARITH_TAC))
  >- (
    Cases_on ‘x = 0’ >- gvs[integerTheory.INT_QUOT_0]>>
    ‘¬(x ≥ 0)’ by intLib.ARITH_TAC>>
    Cases_on ‘y ≥ 1’
    >- (‘¬(x quot y ≥ 1)’ by gs[]>>irule (cj 4 prod_sign)>>intLib.ARITH_TAC)
    >- (‘¬(y ≥ 0)’ by intLib.ARITH_TAC>>‘x quot y ≥ 0’ by gs[]>>
        irule (cj 3 prod_sign)>>intLib.ARITH_TAC))
QED

(* completeness core for modulus: z = x rem y satisfies every mod body row
   (P = |x quot y| * |y| is the free product magnitude) *)
Theorem mod_complete[local]:
  y ≠ 0 ∧ x rem y = z ⇒
  (y ≥ 1 ∨ ¬(y ≥ 0)) ∧
  (x ≥ 0 ⇒ x - z ≥ ABS (x quot y * y)) ∧
  (x ≥ 0 ⇒ x - z ≤ ABS (x quot y * y)) ∧
  (¬(x ≥ 1) ⇒ z - x ≥ ABS (x quot y * y)) ∧
  (¬(x ≥ 1) ⇒ z - x ≤ ABS (x quot y * y)) ∧
  (z ≤ ABS y - 1) ∧
  (-z ≤ ABS y - 1) ∧
  (x ≥ 0 ⇒ z ≥ 0) ∧
  (¬(x ≥ 1) ⇒ z ≤ 0)
Proof
  strip_tac>>
  drule integerTheory.INT_REMQUOT>>
  disch_then (qspec_then ‘x’ strip_assume_tac)>>
  ‘(x ≥ 0 ⇒ 0 ≤ x quot y * y) ∧ (¬(x ≥ 1) ⇒ x quot y * y ≤ 0)’ by
    (irule quot_prod_sign>>simp[])>>
  qpat_x_assum ‘x rem y = z’ (assume_tac o SYM)>>
  qabbrev_tac ‘q = x quot y * y’>>
  qabbrev_tac ‘r = x rem y’>>
  gvs[]>>
  rpt (qpat_x_assum ‘Abbrev _’ kall_tac)>>
  rpt conj_tac>>rw[]>>gs[]>>intLib.ARITH_TAC
QED

(* completeness core for divide: z = x quot y satisfies every div body row,
   stated in the exact PB-row form the encoder emits (P = |z|*|y|) *)
Theorem div_complete[local]:
  y ≠ 0 ∧ x quot y = z ⇒
  (y ≥ 1 ∨ ¬(y ≥ 0)) ∧
  (x ≥ 0 ⇒ x + -(ABS z * ABS y) ≥ 0) ∧
  (x ≥ 0 ⇒ -1 * x + (ABS z * ABS y + ABS y) ≥ 1) ∧
  (¬(x ≥ 1) ⇒ -1 * x + -(ABS z * ABS y) ≥ 0) ∧
  (¬(x ≥ 1) ⇒ x + (ABS z * ABS y + ABS y) ≥ 1) ∧
  (x ≥ 1 ∧ y ≥ 1 ⇒ z ≥ 0) ∧
  (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ z ≥ 0) ∧
  (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(z ≥ 1)) ∧
  (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(z ≥ 1)) ∧
  (x = 0 ⇒ ¬(z ≥ 1))
Proof
  strip_tac>>
  ‘ABS (x quot y * y) ≤ ABS x’ by (irule integerTheory.INT_ABS_QUOT>>simp[])>>
  drule integerTheory.INT_REMQUOT>>
  disch_then (qspec_then ‘x’ strip_assume_tac)>>
  ‘(x ≥ 1 ∧ y ≥ 1 ⇒ x quot y ≥ 0) ∧
   (¬(x ≥ 0) ∧ ¬(y ≥ 0) ⇒ x quot y ≥ 0) ∧
   (x ≥ 1 ∧ ¬(y ≥ 0) ⇒ ¬(x quot y ≥ 1)) ∧
   (¬(x ≥ 0) ∧ y ≥ 1 ⇒ ¬(x quot y ≥ 1)) ∧
   (x = 0 ⇒ ¬(x quot y ≥ 1))’ by (irule quot_sign>>simp[])>>
  qpat_x_assum ‘x quot y = z’ (fn th => fs[th])>>
  ‘ABS z * ABS y = ABS (z * y)’ by simp[integerTheory.INT_ABS_MUL]>>
  qabbrev_tac ‘q = z * y’>>
  qabbrev_tac ‘r = x rem y’>>
  rpt (qpat_x_assum ‘Abbrev _’ kall_tac)>>
  rpt conj_tac>>rw[]>>gs[]>>
  rpt (qpat_x_assum ‘_ ⇒ _’ kall_tac)>>
  rpt (qpat_x_assum ‘ABS _ * ABS _ = _’ kall_tac)>>
  Cases_on ‘0 < q + r’>>gs[]>>intLib.ARITH_TAC
QED

(* soundness core for modulus: the free product magnitude p = n*|y| makes
   x - z a multiple of y; range + sign then pin z = x rem y. *)
Theorem mod_sign_bridge[local]:
  y ≠ 0 ∧ y int_divides p ∧
  (0 ≤ x ⇒ x - z = p) ∧
  (x ≤ 0 ⇒ z - x = p) ∧
  (0 ≤ x ⇒ 0 ≤ z) ∧
  (x ≤ 0 ⇒ z ≤ 0) ∧
  ABS z ≤ ABS y - 1 ⇒
  x rem y = z
Proof
  rw[]>>
  irule integerTheory.INT_REM_UNIQUE>>
  rpt conj_tac
  >- (
    ‘y int_divides (x - z)’ suffices_by
      (simp[integerTheory.INT_DIVIDES]>>strip_tac>>qexists_tac ‘m’>>intLib.ARITH_TAC)>>
    ‘x - z = p ∨ x - z = -p’ by (
      Cases_on ‘0 ≤ x’ >- (gs[])>>
      ‘x ≤ 0’ by intLib.ARITH_TAC>>gs[]>>intLib.ARITH_TAC)>>
    gvs[integerTheory.INT_DIVIDES_NEG])
  >- intLib.ARITH_TAC
  >- (
    IF_CASES_TAC
    >- (‘0 ≤ x’ by intLib.ARITH_TAC>>gs[])
    >- (‘x ≤ 0’ by intLib.ARITH_TAC>>gs[]))
QED

(* Divide Z = X quot Y: axis 0 = |Z| (channelled), axis 1 = |Y| (channelled),
   product P = |Z|*|Y|. Remainder R = X - Z*Y is implicit. *)
Definition cencode_div_body_def:
  cencode_div_body bnd X Y Z name =
  let
    (lby,uby) = varc_bnd bnd Y;
    (lbz,ubz) = varc_bnd bnd Z;
    n = mult_width lbz ubz;
    m = mult_width lby uby;
    zbs = mult_bin_term name 0 n;
    ybs = mult_bin_term name 1 m;
    pbs = mult_prod_term (mult_prodbit name) n m;
    gx0 = Pos (INL (Ge X 0));
    ngx1 = Neg (INL (Ge X 1));
    px0 = Pos (INL (Eq X 0));
    px1 = Pos (INL (Ge X 1));
    nx = Neg (INL (Ge X 0));
    py1 = Pos (INL (Ge Y 1));
    ny = Neg (INL (Ge Y 0));
    zp = ([],[(1,Pos (INL (Ge Z 0)))],1);
    zn = ([],[(1,Neg (INL (Ge Z 1)))],1)
  in
  Append
    (List (mk_annotate
      [mk_name name («Zge0_ge»); mk_name name («Zge0_le»);
       mk_name name («Zlt0_ge»); mk_name name («Zlt0_le»)]
      (mult_mag_rows bnd Z zbs))) $
  Append
    (List (mk_annotate
      [mk_name name («Yge0_ge»); mk_name name («Yge0_le»);
       mk_name name («Ylt0_ge»); mk_name name («Ylt0_le»)]
      (mult_mag_rows bnd Y ybs))) $
  Append
    (flat_app (GENLIST (λi.
      flat_app (GENLIST (λj.
        cbimply_var bnd (mult_prodbit name i j)
          ([],[(1,Pos (mult_binbit name 0 i));
               (1,Pos (mult_binbit name 1 j))],2)) m)) n)) $
    (List (mk_annotate
      [mk_name name («nonzero»);
       mk_name name («rem_pos_lo»); mk_name name («rem_pos_hi»);
       mk_name name («rem_neg_hi»); mk_name name («rem_neg_lo»);
       mk_name name («sgn_pp»); mk_name name («sgn_nn»);
       mk_name name («sgn_pn»); mk_name name («sgn_np»);
       mk_name name («sgn_x0»)]
      [
        ([],[(1,py1);(1,ny)],1);
        bits_imply bnd [gx0] (mult_varc_row 1 X (flip_coeffs pbs) 0);
        bits_imply bnd [gx0] (mult_varc_row (-1) X (pbs ++ ybs) 1);
        bits_imply bnd [ngx1] (mult_varc_row (-1) X (flip_coeffs pbs) 0);
        bits_imply bnd [ngx1] (mult_varc_row 1 X (pbs ++ ybs) 1);
        bits_imply bnd [px1; py1] zp;
        bits_imply bnd [nx; ny] zp;
        bits_imply bnd [px1; ny] zn;
        bits_imply bnd [nx; py1] zn;
        bits_imply bnd [px0] zn
      ]))
End

Definition cencode_div_def:
  cencode_div bnd X Y Z name ec =
  let
    (e1,ec1) = cencode_full_eq bnd X 0 ec;
    (e2,ec2) = cencode_full_eq bnd Y 0 ec1;
    (e3,ec3) = cencode_full_eq bnd Z 0 ec2
  in
    (Append e1 $ Append e2 $ Append e3 $
      cencode_div_body bnd X Y Z name, ec3)
End

Definition encode_div_def:
  encode_div bnd X Y Z name =
  encode_full_eq bnd X 0 ++
  encode_full_eq bnd Y 0 ++
  encode_full_eq bnd Z 0 ++
  abstr (cencode_div_body bnd X Y Z name)
End

Theorem encode_div_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Nonlinop Div X Y Z)) ∧
  varc wi Y ≠ 0 ∧
  varc wi X quot varc wi Y = varc wi Z ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_div bnd X Y Z name)
Proof
  rw[encode_div_def]>>
  simp[reify_avar_def,reify_reif_def]>>
  rw[cencode_div_body_def]>>rpt(pairarg_tac>>gvs[])>>
  simp[mult_mag_rows_sem,reify_avar_def,reify_reif_def]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  simp[]>>
  ‘∀ax b. reify_avar cs wi (INR (name,Indices [ax; b] (SOME «bin»))) ⇔
     BIT b (Num (ABS (varc wi (if ax = 0 then Z else Y))))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘∀i j. reify_avar cs wi (INR (name,Indices [i; j] (SOME «prod»))) ⇔
     BIT i (Num (ABS (varc wi Z))) ∧ BIT j (Num (ABS (varc wi Y)))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbz ubz)) = ABS (varc wi Z)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[mult_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby)) = ABS (varc wi Y)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[mult_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (mult_prod_term (mult_prodbit name) (mult_width lbz ubz)
        (mult_width lby uby)) =
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbz ubz)) *
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  simp[mult_bin_term_def,GSYM integerTheory.INT_ABS_MUL]>>
  qpat_assum ‘varc _ _ ≠ 0’ (fn c1 =>
    qpat_assum ‘_ quot _ = _’ (fn c2 =>
      strip_assume_tac (MATCH_MP (GEN_ALL div_complete) (CONJ c1 c2))))>>
  rw[EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,cbimply_var_def]>>
  rw[append_flat_app,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST]>>
  gs[]
QED

Theorem encode_div_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_div bnd X Y Z name) ⇒
  varc wi Y ≠ 0 ∧
  varc wi X quot varc wi Y = varc wi Z
Proof
  rw[encode_div_def]>>
  fs[cencode_div_body_def]>>rpt(pairarg_tac>>gvs[])>>
  gs[mult_mag_rows_sem,mult_prod_block_sem]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  fs[mult_bin_term_def]>>
  ‘eval_lin_term wb (mult_prod_term (mult_prodbit name) (mult_width lbz ubz)
     (mult_width lby uby)) =
   eval_lin_term wb (pos_num (mult_binbit name 0) (mult_width lbz ubz)) *
   eval_lin_term wb (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  ‘varc wi Y ≠ 0’ by (
    rpt (qpat_x_assum ‘eval_lin_term _ _ = _’ kall_tac)>>
    rpt (qpat_x_assum ‘∀x. _’ kall_tac)>>
    rpt (qpat_x_assum ‘_ ⇔ _’ kall_tac)>>
    intLib.ARITH_TAC)>>
  gvs[]>>
  irule div_sign_bridge>>
  gs[eval_lin_term_append,integerTheory.INT_ABS_MUL]>>
  qabbrev_tac ‘P = ABS (varc wi Z * varc wi Y)’>>
  rpt (qpat_x_assum ‘eval_lin_term _ _ = _’ kall_tac)>>
  rpt (qpat_x_assum ‘∀x. _’ kall_tac)>>
  rpt (qpat_x_assum ‘Abbrev _’ kall_tac)>>
  rpt (qpat_x_assum ‘_ ⇔ _’ kall_tac)>>
  rpt conj_tac>>rw[]>>intLib.ARITH_TAC
QED

Theorem cencode_div_sem:
  valid_assignment bnd wi ∧
  cencode_div bnd X Y Z name ec = (es, ec') ⇒
  enc_rel wi es (encode_div bnd X Y Z name) ec ec'
Proof
  rw[cencode_div_def,encode_div_def]>>
  gvs[UNCURRY_EQ]>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  metis_tac[enc_rel_Append,enc_rel_encode_full_eq,
    enc_rel_encode_ge,enc_rel_abstr]
QED

(* Modulus Z = X rem Y: axis 0 = |quotient| (free magnitude), axis 1 = |Y|
   (channelled), product P = |quotient|*|Y|. The exposed Z is the remainder. *)
Definition cencode_mod_body_def:
  cencode_mod_body bnd X Y Z name =
  let
    (lbx,ubx) = varc_bnd bnd X;
    (lby,uby) = varc_bnd bnd Y;
    n = mult_width lbx ubx;
    m = mult_width lby uby;
    ybs = mult_bin_term name 1 m;
    pbs = mult_prod_term (mult_prodbit name) n m;
    gx0 = Pos (INL (Ge X 0));
    ngx1 = Neg (INL (Ge X 1));
    py1 = Pos (INL (Ge Y 1));
    ny = Neg (INL (Ge Y 0));
    (idp,rp) = split_iclin_term [(1,X);(-1,Z)] [] 0;
    (idn,rn) = split_iclin_term [(-1,X);(1,Z)] [] 0
  in
  Append
    (List (mk_annotate
      [mk_name name («Yge0_ge»); mk_name name («Yge0_le»);
       mk_name name («Ylt0_ge»); mk_name name («Ylt0_le»)]
      (mult_mag_rows bnd Y ybs))) $
  Append
    (flat_app (GENLIST (λi.
      flat_app (GENLIST (λj.
        cbimply_var bnd (mult_prodbit name i j)
          ([],[(1,Pos (mult_binbit name 0 i));
               (1,Pos (mult_binbit name 1 j))],2)) m)) n)) $
    (List (mk_annotate
      [mk_name name («nonzero»);
       mk_name name («id_pos_ge»); mk_name name («id_pos_le»);
       mk_name name («id_neg_ge»); mk_name name («id_neg_le»);
       mk_name name («rng_hi»); mk_name name («rng_lo»);
       mk_name name («sgn_pos»); mk_name name («sgn_neg»)]
      [
        ([],[(1,py1);(1,ny)],1);
        (* [X>=0] ==> X - Z = P *)
        bits_imply bnd [gx0] (idp, flip_coeffs pbs, rp);
        bits_imply bnd [gx0] (idn, pbs, rn);
        (* ~[X>=1] ==> Z - X = P *)
        bits_imply bnd [ngx1] (idn, flip_coeffs pbs, rn);
        bits_imply bnd [ngx1] (idp, pbs, rp);
        (* range |Z| < |Y| (ybs = |Y| pins the bound on the real Z) *)
        mult_varc_row (-1) Z ybs 1;
        mult_varc_row 1 Z ybs 1;
        (* sign(Z) = sign(X) *)
        bits_imply bnd [gx0] (mult_varc_row 1 Z [] 0);
        bits_imply bnd [ngx1] (mult_varc_row (-1) Z [] 0)
      ]))
End

Definition cencode_mod_def:
  cencode_mod bnd X Y Z name ec =
  let
    (e1,ec1) = cencode_full_eq bnd X 0 ec;
    (e2,ec2) = cencode_full_eq bnd Y 0 ec1
  in
    (Append e1 $ Append e2 $
      cencode_mod_body bnd X Y Z name, ec2)
End

Definition encode_mod_def:
  encode_mod bnd X Y Z name =
  encode_full_eq bnd X 0 ++
  encode_full_eq bnd Y 0 ++
  abstr (cencode_mod_body bnd X Y Z name)
End

Theorem encode_mod_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Prim (Nonlinop Mod X Y Z)) ∧
  varc wi Y ≠ 0 ∧
  varc wi X rem varc wi Y = varc wi Z ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_mod bnd X Y Z name)
Proof
  rw[encode_mod_def]>>
  simp[reify_avar_def,reify_reif_def]>>
  rw[cencode_mod_body_def]>>rpt(pairarg_tac>>gvs[])>>
  simp[mult_mag_rows_sem,reify_avar_def,reify_reif_def]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  simp[]>>
  ‘∀ax b. reify_avar cs wi (INR (name,Indices [ax; b] (SOME «bin»))) ⇔
     (if ax = 0 then BIT b (Num (ABS (varc wi X quot varc wi Y)))
      else BIT b (Num (ABS (varc wi Y))))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘∀i j. reify_avar cs wi (INR (name,Indices [i; j] (SOME «prod»))) ⇔
     BIT i (Num (ABS (varc wi X quot varc wi Y))) ∧
     BIT j (Num (ABS (varc wi Y)))’ by
    gvs[reify_avar_def,reify_flag_def]>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbx ubx)) =
   ABS (varc wi X quot varc wi Y)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[quot_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby)) = ABS (varc wi Y)’ by
    (irule mult_bin_eval>>fs[]>>metis_tac[mult_width_bound])>>
  ‘eval_lin_term (reify_avar cs wi)
     (mult_prod_term (mult_prodbit name) (mult_width lbx ubx)
        (mult_width lby uby)) =
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 0) (mult_width lbx ubx)) *
   eval_lin_term (reify_avar cs wi)
     (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  imp_res_tac split_iclin_term_sound>>
  gs[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_append,
     mult_bin_term_def]>>
  qpat_x_assum ‘∀wi'. eval_iclin_term wi' [(1,X); (-1,Z)] = _’
    (qspec_then ‘wi’ assume_tac)>>
  qpat_x_assum ‘∀wi'. eval_iclin_term wi' [(-1,X); (1,Z)] = _’
    (qspec_then ‘wi’ assume_tac)>>
  gs[eval_iclin_term_def,eval_icterm_def,iSUM_def]>>
  qpat_assum ‘varc _ _ ≠ 0’ (fn c1 =>
    qpat_assum ‘_ rem _ = _’ (fn c2 =>
      strip_assume_tac (MATCH_MP (GEN_ALL mod_complete) (CONJ c1 c2))))>>
  rw[EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,cbimply_var_def]>>
  rw[append_flat_app,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST]>>
  gs[integerTheory.INT_ABS_MUL]>>
  qabbrev_tac ‘P = ABS (varc wi X quot varc wi Y * varc wi Y)’>>
  rpt (qpat_x_assum ‘Abbrev _’ kall_tac)>>
  rpt (qpat_x_assum ‘∀ax b. _’ kall_tac)>>
  rpt (qpat_x_assum ‘∀i j. _’ kall_tac)>>
  rpt (qpat_x_assum ‘∀b. _’ kall_tac)>>
  rpt (qpat_x_assum ‘eval_lin_term _ _ = _’ kall_tac)>>
  rpt (qpat_x_assum ‘split_iclin_term _ _ _ = _’ kall_tac)>>
  rpt (qpat_x_assum ‘varc_bnd _ _ = _’ kall_tac)>>
  rpt (qpat_x_assum ‘ALOOKUP _ _ = _’ kall_tac)>>
  rpt (qpat_x_assum ‘_ rem _ = _’ kall_tac)>>
  intLib.ARITH_TAC
QED

Theorem encode_mod_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_mod bnd X Y Z name) ⇒
  varc wi Y ≠ 0 ∧
  varc wi X rem varc wi Y = varc wi Z
Proof
  rw[encode_mod_def]>>
  fs[cencode_mod_body_def]>>rpt(pairarg_tac>>gvs[])>>
  gs[mult_mag_rows_sem,mult_prod_block_sem]>>
  ‘∀b. b2i b ≥ 1 ⇔ b’ by (Cases>>simp[])>>
  fs[mult_bin_term_def]>>
  ‘eval_lin_term wb (mult_prod_term (mult_prodbit name) (mult_width lbx ubx)
     (mult_width lby uby)) =
   eval_lin_term wb (pos_num (mult_binbit name 0) (mult_width lbx ubx)) *
   eval_lin_term wb (pos_num (mult_binbit name 1) (mult_width lby uby))’ by
    (irule eval_mult_prod_term>>fs[])>>
  gvs[]>>
  ‘varc wi Y int_divides
     (eval_lin_term wb (pos_num (mult_binbit name 0) (mult_width lbx ubx)) *
      ABS (varc wi Y))’ by (
    irule integerTheory.INT_DIVIDES_RMUL>>
    rw[integerTheory.INT_ABS,integerTheory.INT_DIVIDES_NEG,
       integerTheory.INT_DIVIDES_REFL])>>
  imp_res_tac split_iclin_term_sound>>
  gs[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_append]>>
  qabbrev_tac ‘P = eval_lin_term wb (pos_num (mult_binbit name 0)
     (mult_width lbx ubx)) * ABS (varc wi Y)’>>
  qpat_x_assum ‘∀wi'. eval_iclin_term wi' [(1,X); (-1,Z)] = _’
    (qspec_then ‘wi’ assume_tac)>>
  qpat_x_assum ‘∀wi'. eval_iclin_term wi' [(-1,X); (1,Z)] = _’
    (qspec_then ‘wi’ assume_tac)>>
  gs[eval_iclin_term_def,eval_icterm_def,iSUM_def]>>
  ‘varc wi Y ≠ 0 ∧ varc wi Y int_divides P ∧
   (0 ≤ varc wi X ⇒ varc wi X - varc wi Z = P) ∧
   (varc wi X ≤ 0 ⇒ varc wi Z - varc wi X = P) ∧
   (0 ≤ varc wi X ⇒ 0 ≤ varc wi Z) ∧
   (varc wi X ≤ 0 ⇒ varc wi Z ≤ 0) ∧
   ABS (varc wi Z) ≤ ABS (varc wi Y) - 1’ by (
    rpt (qpat_x_assum ‘eval_lin_term _ _ = _’ kall_tac)>>
    rpt (qpat_x_assum ‘∀x. _’ kall_tac)>>
    rpt (qpat_x_assum ‘_ ⇔ _’ kall_tac)>>
    rpt (qpat_x_assum ‘Abbrev _’ kall_tac)>>
    rpt conj_tac>>rw[]>>intLib.ARITH_TAC)>>
  metis_tac[mod_sign_bridge]
QED

Theorem cencode_mod_sem:
  valid_assignment bnd wi ∧
  cencode_mod bnd X Y Z name ec = (es, ec') ⇒
  enc_rel wi es (encode_mod bnd X Y Z name) ec ec'
Proof
  rw[cencode_mod_def,encode_mod_def]>>
  gvs[UNCURRY_EQ]>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  metis_tac[enc_rel_Append,enc_rel_encode_full_eq,enc_rel_abstr]
QED

Definition encode_prim_constr_def:
  encode_prim_constr bnd c name =
  case c of
    Cmpop Zr cmp X Y =>
      (case cmp of
        Equal => encode_equal bnd Zr X Y name
      | NotEqual => encode_not_equal bnd Zr X Y name
      | Lexop lex => encode_order_cmpops bnd Zr lex X Y)
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
  | Nonlinop nlop X Y Z =>
      (case nlop of
        Mult => encode_mult bnd X Y Z name
      | Div => encode_div bnd X Y Z name
      | Mod => encode_mod bnd X Y Z name)
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
  >- (Cases_on`p`>>gvs[nlop_sem_def,nlop_val_def,guard_nlop_def]>>
      metis_tac[encode_mult_sem_1,encode_div_sem_1,encode_mod_sem_1])
  >- (
    rename1`cmpop_sem _ p`>>
    Cases_on`p`>>fs[]
    >- (irule encode_order_cmpops_sem_1>>
        gvs[cmpop_sem_def,cmpop_val_def])
    >- (irule encode_equal_sem_1>>
        gvs[cmpop_sem_def,cmpop_val_def])
    >- (irule encode_not_equal_sem_1>>
        gvs[cmpop_sem_def,cmpop_val_def]))
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
  >- (Cases_on`p`>>gvs[nlop_sem_def,nlop_val_def,guard_nlop_def]>>
      metis_tac[encode_mult_sem_2,encode_div_sem_2,encode_mod_sem_2])
  >- (
    rename1`cmpop_sem _ p`>>
    Cases_on`p`>>fs[]
    >- (gvs[cmpop_sem_def]>>
        metis_tac[encode_order_cmpops_sem_2])
    >- (gvs[cmpop_sem_def,cmpop_val_def]>>
        metis_tac[encode_equal_sem_2])
    >- (gvs[cmpop_sem_def,cmpop_val_def]>>
        metis_tac[encode_not_equal_sem_2]))
QED

(* Concrete encodings *)
Definition cencode_equal_def:
  cencode_equal bnd Zr X Y name ec =
  case Zr of
    NONE => (List (cmk_eq name X Y),ec)
  | SOME (INL Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e $ cencode_equal_1 bnd Zc X Y name, ec')
  | SOME (INR Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
        (Append e $ cencode_equal_2 bnd Zc X Y name, ec')
End

Theorem cencode_equal_sem:
  valid_assignment bnd wi ∧
  cencode_equal bnd Zr X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_equal bnd Zr X Y name) ec ec'
Proof
  rw[cencode_equal_def,encode_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >-simp[enc_rel_List_refl_mul]
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_reif_gen>>
    simp[enc_rel_List_refl_mul])
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_reif_gen>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
QED

Definition cencode_not_equal_def:
  cencode_not_equal bnd Zr X Y name ec =
  case Zr of
    NONE => (cencode_not_equal_1 bnd X Y name, ec)
  | SOME (INL Zc) =>
    let
      (e,ec') = cencode_reif_gen bnd Zc ec
    in
      (Append e $
        cencode_not_equal_2 bnd Zc X Y name, ec')
  | SOME (INR Zc) =>
    let
      (e,ec') = cencode_reif_gen bnd Zc ec
    in
      (Append e $
        cencode_not_equal_3 bnd Zc X Y name, ec')
End

Theorem cencode_not_equal_sem:
  valid_assignment bnd wi ∧
  cencode_not_equal bnd Zr X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_not_equal bnd Zr X Y name) ec ec'
Proof
  rw[cencode_not_equal_def,encode_not_equal_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >-(
    irule enc_rel_abstr_cong>>
    simp[])>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_reif_gen>>
  simp[]>>
  irule enc_rel_abstr_cong>>
  simp[]
QED

Definition cencode_order_cmpops_def:
  cencode_order_cmpops bnd Zr cmp X Y name ec =
  let constr = encode_lex cmp X Y
  in
    case Zr of
      NONE =>
      (List [
        (SOME («c[» ^ name ^ «]»), constr)], ec)
    | SOME (INL Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
      (Append e $
        List [
        (SOME («c[» ^ name ^ «]»),
          (bits_imply bnd [reif_gen Zc] constr))], ec')
    | SOME (INR Zc) =>
      let
        (e,ec') = cencode_reif_gen bnd Zc ec
      in
      (Append e $
        List (mk_annotate
        [«c[» ^ name ^ «][r]»;
          «c[» ^ name ^ «][f]»]
        (bimply_bits bnd [reif_gen Zc] constr)), ec')
End

Theorem cencode_order_cmpops_sem:
  valid_assignment bnd wi ∧
  cencode_order_cmpops bnd Zr cmp X Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_order_cmpops bnd Zr cmp X Y) ec ec'
Proof
  rw[cencode_order_cmpops_def,encode_order_cmpops_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]
  >-(
    irule enc_rel_abstr_cong>>
    simp[])
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_reif_gen>>
    simp[]>>
    irule enc_rel_abstr_cong>>
    simp[])
  >-(
    irule enc_rel_Append>>
    irule_at Any enc_rel_encode_reif_gen>>
    simp[]>>
    irule enc_rel_List_mk_annotate)
QED

Definition cencode_negative_def:
  cencode_negative X Y name =
    List (mk_annotate [mk_name name («le»); mk_name name («ge»)]
      (encode_negative X Y))
End

Definition cencode_abs_def:
  cencode_abs bnd X Y name ec =
  let
    (e,ec') = cencode_ge bnd X 0 ec;
    ls =
      mk_annotate [
        mk_name name («posge»);
        mk_name name («posle»);
        mk_name name («negle»);
        mk_name name («negge»);]
        (encode_abs_body bnd X Y)
  in
    (Append e (List ls) , ec')
End

Definition cencode_prim_constr_def:
  cencode_prim_constr bnd c name ec =
  case c of
    Cmpop Zr cmp X Y =>
      (case cmp of
        Equal => cencode_equal bnd Zr X Y name ec
      | NotEqual => cencode_not_equal bnd Zr X Y name ec
      | Lexop lex => cencode_order_cmpops bnd Zr lex X Y name ec)
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
  | Nonlinop nlop X Y Z =>
    (case nlop of
      Mult => cencode_mult bnd X Y Z name ec
    | Div => cencode_div bnd X Y Z name ec
    | Mod => cencode_mod bnd X Y Z name ec)
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
  >- metis_tac[cencode_mult_sem]
  >- metis_tac[cencode_div_sem]
  >- metis_tac[cencode_mod_sem]
  >- metis_tac[cencode_order_cmpops_sem]
  >- metis_tac[cencode_equal_sem]
  >- metis_tac[cencode_not_equal_sem]
QED

