(*
  An ILP-style language designed as an intermediate layer for CP encodings
*)
Theory ilp
Libs
  preamble
Ancestors
  mlint pbc cp pbc_encode

(*
  This "ILP"-style intermediate language is designed for convenience of
  verified encodings from CP (and then to PB).

  It is NOT intended for use as a standalone and NOT a pure ILP formalization.
*)

Type ilin_term = ``:(int # 'a) list ``

(* A constraint consists of two lists (c_i, X_i), (d_i, l_i) and a RHS *)
Type iconstraint = ``:'a ilin_term # 'b lin_term # int``

(* An assignment assigns both the integer and boolean variables *)
Type iassignment = ``:('a -> int) # ('b -> bool)``;

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

Definition min_iterm_def:
  min_iterm bnd (c,X) =
    let (lb,ub) = bnd X in
      if c < 0i then c * ub
      else c * lb
End

Theorem min_iterm_le:
  valid_assignment bnd w ⇒
  min_iterm bnd t ≤ eval_iterm w t
Proof
  Cases_on`t`>>
  rw[valid_assignment_def,eval_iterm_def,min_iterm_def]>>
  pairarg_tac>>gvs[]>>
  first_x_assum drule>>gvs[]>>
  rw[]
  >- (
    DEP_REWRITE_TAC[INT_LE_ANTIMONO]>>
    simp[])
  >>
    match_mp_tac INT_LE_MONO_IMP>>
    intLib.ARITH_TAC
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
    let (lb,ub) = bnd X in
      if c < 0i then c * lb
      else c * ub
End

Theorem max_iterm_le:
  valid_assignment bnd w ⇒
  eval_iterm w t ≤ max_iterm bnd t
Proof
  Cases_on`t`>>
  rw[valid_assignment_def,eval_iterm_def,max_iterm_def]>>
  pairarg_tac>>gvs[]>>rw[]>>
  first_x_assum(qspec_then`r` mp_tac)>>gvs[]>>
  rw[]
  >- (
    DEP_REWRITE_TAC[INT_LE_ANTIMONO]>>
    simp[])
  >>
    match_mp_tac INT_LE_MONO_IMP>>
    intLib.ARITH_TAC
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
Definition imply_bits_def:
  imply_bits bnd xs cc =
  case cc of (is,bs,c) =>
    let nis = flip_coeffs is in
    let nbs = flip_coeffs bs in
    let nc = 1 - c in
    let r = nc + max_ilin_term bnd is + max_lin_term bs in
    let rr = int_max r 0 in
    MAP (λx. (nis, (rr, x) :: nbs, nc)) xs
End

Theorem imply_bits_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (imply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇒ EVERY (lit wb) xs)
Proof
  rw[imply_bits_def]>>
  every_case_tac>>
  gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,PULL_FORALL,iconstraint_sem_def]>>
  ho_match_mp_tac
    (METIS_PROVE []
    ``
      (∀x. (P x ⇒ (Q x ⇔ (A x ⇒ R x)))) ⇒
      ((!x. (P x ⇒ Q x)) ⇔ (!x. (A x ⇒ P x ⇒ R x)))``)>>
  rw[]>>
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

(* encodes iff *)
Definition bimply_bits_def:
  bimply_bits bnd xs cc =
  bits_imply bnd xs cc ::
  imply_bits bnd xs cc
End

Theorem bimply_bits_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (bimply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇔ EVERY (lit wb) xs)
Proof
  rw[bimply_bits_def]>>
  metis_tac[imply_bits_sem,bits_imply_sem]
QED

Theorem eval_ilin_term_NIL[simp]:
  eval_ilin_term w [] = 0
Proof
  rw[eval_ilin_term_def,iSUM_def]
QED

