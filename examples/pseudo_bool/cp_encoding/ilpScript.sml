(*
  An ILP-style language designed as an intermediate layer for CP encodings
*)
Theory ilp
Libs
  preamble
Ancestors
  mlint pbc cp pbc_encode int_bitwise

(*
  This "ILP"-style intermediate language is designed for convenience of
  verified encodings from CP (and then to PB).

  It is NOT intended for use as a standalone and NOT a pure ILP formalization.
*)

Type ilin_term[pp] = ``:(int # 'a) list ``

(* A constraint consists of two lists (c_i, X_i), (d_i, l_i) and a RHS *)
Type iconstraint[pp] = ``:'a ilin_term # 'b lin_term # int``

(* An assignment assigns both the integer and boolean variables *)
Type iassignment[pp] = ``:('a -> int) # ('b -> bool)``;

Definition eval_iterm_def[simp]:
  eval_iterm wi (c:int,X) = c * wi X
End

Definition eval_ilin_term_def:
  eval_ilin_term wi (xs:(int # 'a) list) = iSUM (MAP (eval_iterm wi) xs)
End

Definition iconstraint_sem_def:
  iconstraint_sem ((is,bs,c):('a,'b) iconstraint)
    ((wi,wb):('a,'b) iassignment) ⇔
    eval_ilin_term wi is + eval_lin_term wb bs ≥ c
End

(* normalize away varc *)
Definition norm_varcs_aux_def:
  (norm_varcs_aux [] res = res) ∧
  (norm_varcs_aux (vc::vs) (xs,acc) =
    case (vc:'a varc) of
      INL v => norm_varcs_aux vs ((1i,v)::xs,acc)
    | INR c => norm_varcs_aux vs (xs,c+acc))
End

Theorem norm_varcs_aux_sound:
  ∀vcs xs acc xs' acc'.
  norm_varcs_aux vcs (xs,acc) = (xs',acc') ⇒
  iSUM (MAP (varc wi) vcs) + eval_ilin_term wi xs + acc =
  eval_ilin_term wi xs' + acc'
Proof
  Induct>>
  rw[norm_varcs_aux_def,iSUM_def,AllCaseEqs(),varc_def,norm_varcs_aux_def]>>
  fs[]>>
  first_x_assum drule>>
  rw[]>>
  fs[eval_ilin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition norm_varcs_def:
  norm_varcs vcs = norm_varcs_aux vcs ([],0)
End

Theorem norm_varcs_sound:
  norm_varcs vcs = (xs',acc') ⇒
  iSUM (MAP (varc wi) vcs) = eval_ilin_term wi xs' + acc'
Proof
  rw[norm_varcs_def]>>
  drule norm_varcs_aux_sound>>
  simp[eval_ilin_term_def,iSUM_def]
QED

(* twos-compplement representation *)
Definition bit_width_def:
  bit_width bnd X =
    let (lb,ub) = bnd X in
     (lb < 0,
      if lb < 0 then
        MAX (LENGTH (FST (bits_of_int lb)))
            (LENGTH (FST (bits_of_int ub)))
      else LENGTH (FST (bits_of_int ub)))
End

Theorem LESS_EXP_MAX[local]:
  (k:num) < 2 ** MAX m n ⇔ k < 2 ** m ∨ k < 2 ** n
Proof
  rw [MAX_DEF]
  \\ eq_tac \\ rw []
  \\ irule LESS_LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem LESS_EQ_EXP_MAX[local]:
  (k:num) ≤ 2 ** MAX m n ⇔ k ≤ 2 ** m ∨ k ≤ 2 ** n
Proof
  rw [MAX_DEF]
  \\ eq_tac \\ rw []
  \\ irule LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem LESS_LENGTH_bits_of_num:
  ∀k. k < 2 ** LENGTH (bits_of_num k)
Proof
  ho_match_mp_tac bits_of_num_ind \\ rw []
  \\ simp [Once bits_of_num_def]
  \\ rw [] \\ gvs []
QED

Theorem bit_width_lemma1:
  bit_width bnd X = (b,h) ∧ bnd X = (q,r) ∧ &n ≤ r ⇒ n < 2 ** h
Proof
  strip_tac
  \\ gvs [bit_width_def] \\ rw []
  \\ gvs [LESS_EXP_MAX]
  \\ ‘∃k. r = & k’ by intLib.COOPER_TAC
  \\ gvs [bits_of_int_def]
  \\ rpt disj2_tac
  \\ irule LESS_EQ_LESS_TRANS
  \\ irule_at Any LESS_LENGTH_bits_of_num \\ gvs []
QED

Theorem bit_width_lemma2:
  bit_width bnd X = (T,h) ∧ bnd X = (q,r) ∧ q ≤ -&n ⇒
    n ≤ 2**h
Proof
  strip_tac
  \\ gvs [bit_width_def]
  \\ Cases_on ‘q’ \\ gvs []
  \\ rename [‘k ≠ 0:num’]
  \\ ‘- & k - 1 = -& (k + 1):int’ by intLib.COOPER_TAC \\ gvs []
  \\ gvs [bits_of_int_def]
  \\ gvs [int_not_def]
  \\ ‘&(k + 1) − 1 = & k : int’ by intLib.COOPER_TAC \\ gvs []
  \\ qmatch_goalsub_abbrev_tac`MAX lbb ubb`
  \\ qspec_then `Num (&k -1)` assume_tac LESS_LENGTH_bits_of_num
  \\ gvs[]
  \\ `k ≤ 2** lbb` by intLib.ARITH_TAC
  \\ gvs [LESS_EQ_EXP_MAX]
QED

(* Rounding to the nearest powers of two *)
Definition min_iterm_def:
  min_iterm bnd (c,X) =
  let (comp,h) = bit_width bnd X in
    if c < 0i then c * (2 ** h - 1)
    else
      if comp then c * (-(2**h))
      else 0
End

Theorem min_iterm_le:
  valid_assignment bnd w ⇒
  min_iterm bnd t ≤ eval_iterm w t
Proof
  Cases_on`t`>>
  rename1`(x,y)`>>
  rw[valid_assignment_def,eval_iterm_def,min_iterm_def]>>
  pairarg_tac>>fs[]>>
  `?lb ub. bnd y = (lb,ub)` by metis_tac[PAIR]>>
  first_x_assum drule>>gvs[]>>
  strip_tac>>
  rw[]
  >- (
    simp[INT_LE_ANTIMONO]>>
    qsuff_tac`w y < &(2 ** h)` >- intLib.ARITH_TAC>>
    Cases_on `w y < 0` >- intLib.ARITH_TAC>>
    `?yy. w y = & yy` by intLib.ARITH_TAC>>
    fs[]>>
    irule bit_width_lemma1>>
    metis_tac[])
  >- (
    match_mp_tac INT_LE_MONO_IMP>>
    CONJ_TAC >- intLib.ARITH_TAC>>
    drule bit_width_lemma2>>
    disch_then drule>>
    intLib.ARITH_TAC)
  >- (
    gvs[bit_width_def]>>
    irule integerTheory.INT_LE_MUL>>
    intLib.ARITH_TAC)
QED

Definition min_ilin_term_def:
  min_ilin_term bnd (xs:'a ilin_term) =
  iSUM (MAP (min_iterm bnd) xs)
End

Theorem eval_ilin_term_min_ilin_term:
  valid_assignment bnd w ⇒
  min_ilin_term bnd xs ≤ eval_ilin_term w xs
Proof
  rw[min_ilin_term_def,eval_ilin_term_def]>>
  match_mp_tac iSUM_MAP_le>>
  rw[]>>
  metis_tac[min_iterm_le]
QED

(* List of literals imply iconstraint under bounds *)
Definition bits_imply_def:
  bits_imply bnd xs cc =
  case cc of (is,bs,c) =>
    let r = c - min_ilin_term bnd is - min_lin_term bs in
    let rr = int_max r 0 in
    (is, MAP (λx. (rr, negate x)) xs ++ bs, c)
End

Theorem bits_imply_sem[simp]:
  valid_assignment bnd wi ⇒
  iconstraint_sem (bits_imply bnd xs c) (wi,wb) =
    (EVERY (lit wb) xs ⇒ iconstraint_sem c (wi,wb))
Proof
  rw[bits_imply_def]>>
  every_case_tac>>gvs[iconstraint_sem_def]>>
  Cases_on`EVERY (lit wb) xs`
  >- (
    drule eval_lin_term_MAP_negate_0>> rw[])>>
  simp[]>>
  rename1`eval_ilin_term wi is + (_ + eval_lin_term wb bs) ≥ rr`>>
  drule eval_ilin_term_min_ilin_term>>
  disch_then(qspec_then`is` assume_tac)>>
  `min_lin_term bs ≤ eval_lin_term wb bs` by
    metis_tac[eval_lin_term_min_lin_term]>>
  qmatch_goalsub_abbrev_tac`int_max r 0`>>
  drule eval_lin_term_MAP_negate_ge>>
  disch_then(qspec_then`int_max r 0` mp_tac)>>
  impl_tac >- intLib.ARITH_TAC>>
  rw[Abbr`r`]>>
  intLib.ARITH_TAC
QED

Theorem eval_ilin_term_flip_coeffs[simp]:
  eval_ilin_term w (flip_coeffs xs) = - eval_ilin_term w xs
Proof
  simp[eval_ilin_term_def,flip_coeffs_def]>>
  Induct_on`xs`>>rw[iSUM_def]>>
  pairarg_tac>>simp[]>>
  intLib.ARITH_TAC
QED

Definition max_iterm_def:
  max_iterm bnd (c,X) =
  let (comp,h) = bit_width bnd X in
    if c < 0i then
      (if comp then c * (-(2**h))
      else 0)
    else
      c * (2 ** h - 1)
End

Theorem max_iterm_le:
  valid_assignment bnd w ⇒
  eval_iterm w t ≤ max_iterm bnd t
Proof
  Cases_on`t`>>
  rename1`(x,y)`>>
  rw[valid_assignment_def,eval_iterm_def,max_iterm_def]>>
  pairarg_tac>>fs[]>>
  `?lb ub. bnd y = (lb,ub)` by metis_tac[PAIR]>>
  first_x_assum drule>>gvs[]>>
  strip_tac>>
  rw[]
  >- (
    simp[INT_LE_ANTIMONO]>>
    drule bit_width_lemma2>>
    disch_then drule>>
    intLib.ARITH_TAC)
  >- (
    drule INT_LE_ANTIMONO>>
    disch_then (qspecl_then [`0`,`w y`] mp_tac)>>
    simp[]>>
    disch_then kall_tac>>
    gvs[bit_width_def]>>
    intLib.ARITH_TAC)
  >- (
    match_mp_tac INT_LE_MONO_IMP>>
    CONJ_TAC >- intLib.ARITH_TAC>>
    qsuff_tac`w y < &(2 ** h)` >- intLib.ARITH_TAC>>
    Cases_on `w y < 0` >- intLib.ARITH_TAC>>
    `?yy. w y = & yy` by intLib.ARITH_TAC>>
    fs[]>>
    irule bit_width_lemma1>>
    metis_tac[])
QED

Definition max_ilin_term_def:
  max_ilin_term bnd (xs:'a ilin_term) =
  iSUM (MAP (max_iterm bnd) xs)
End

Theorem eval_ilin_term_max_ilin_term:
  valid_assignment bnd w ⇒
  eval_ilin_term w xs ≤ max_ilin_term bnd xs
Proof
  rw[max_ilin_term_def,eval_ilin_term_def]>>
  match_mp_tac iSUM_MAP_le>>
  rw[]>>
  metis_tac[max_iterm_le]
QED

(* constraint implies list of literals *)
Definition imply_bit_aux_def:
  imply_bit_aux bnd cc =
  case cc of (is,bs,c) =>
    let nis = flip_coeffs is in
    let nbs = flip_coeffs bs in
    let nc = 1 - c in
    let r = nc + max_ilin_term bnd is + max_lin_term bs in
    let rr = int_max r 0 in
    (nis, rr, nbs, nc)
End

Definition imply_bit_def:
  imply_bit bnd x cc =
  case imply_bit_aux bnd cc of (nis,rr,nbs,nc) =>
    (nis, (rr, x) :: nbs, nc)
End

Definition imply_bits_def:
  imply_bits bnd xs cc =
  case imply_bit_aux bnd cc of (nis,rr,nbs,nc) =>
    MAP (λx. (nis, (rr, x) :: nbs, nc)) xs
End

Theorem imply_bits_def':
  imply_bits bnd xs cc =
  MAP (λx. imply_bit bnd x cc) xs
Proof
  rw[imply_bits_def,imply_bit_def]>>
  every_case_tac>>simp[]
QED

Theorem imply_bit_sem[simp]:
  valid_assignment bnd wi ⇒
  iconstraint_sem (imply_bit bnd x c) (wi,wb)
  =
  (iconstraint_sem c (wi,wb) ⇒ lit wb x)
Proof
  rw[imply_bit_def,imply_bit_aux_def]>>
  every_case_tac>>
  gvs[iconstraint_sem_def]>>
  rename1`lit wb x`>>
  Cases_on`lit wb x`>>simp[]
  >- (
    rename1`-eval_ilin_term wi is + (_ + -eval_lin_term wb bs) ≥ 1 - rr`>>
    drule eval_ilin_term_max_ilin_term>>
    disch_then(qspec_then`is` assume_tac)>>
    `eval_lin_term wb bs ≤ max_lin_term bs` by
      metis_tac[eval_lin_term_max_lin_term]>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

Theorem imply_bits_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (imply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇒ EVERY (lit wb) xs)
Proof
  rw[imply_bits_def']>>
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  metis_tac[]
QED

(* encodes iff *)
Definition bimply_bit_def:
  bimply_bit bnd x cc =
  [bits_imply bnd [x] cc;
  imply_bit bnd x cc]
End

Definition bimply_bits_def:
  bimply_bits bnd xs cc =
  bits_imply bnd xs cc ::
  imply_bits bnd xs cc
End

Theorem bimply_bit_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (bimply_bit bnd x c)
  =
  (iconstraint_sem c (wi,wb) ⇔ lit wb x)
Proof
  rw[bimply_bit_def]>>
  metis_tac[]
QED

Theorem bimply_bits_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (bimply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇔ EVERY (lit wb) xs)
Proof
  rw[bimply_bits_def]>>
  metis_tac[]
QED

Theorem eval_ilin_term_NIL[simp]:
  eval_ilin_term w [] = 0
Proof
  rw[eval_ilin_term_def,iSUM_def]
QED

