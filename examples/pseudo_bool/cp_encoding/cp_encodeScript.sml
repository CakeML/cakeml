(*
  Formalization of the CP encoder
*)
open preamble cpTheory ilpTheory pbcTheory pbc_encodeTheory;

val _ = new_theory "cp_encode";

(* The big datatype to represent encoded Boolean variables *)
Datatype:
  ebool =
  | Ge 'a int (* Reifies X ≥ i *)
  | Eq 'a int (* Reifies X = i *)
End

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

(* List of booleans imply iconstraint under bounds *)
Definition bits_imply_def:
  bits_imply bnd xs cc =
  case cc of (is,bs,c) =>
    let r = c - min_ilin_term bnd is - min_lin_term bs in
    let rr = int_max r 0 in
    (is, MAP (λx. (rr, Neg x)) xs ++ bs, c)
End

Theorem bits_imply_sem:
  valid_assignment bnd wi ⇒
  iconstraint_sem (bits_imply bnd xs c) (wi,wb) =
    (EVERY wb xs ⇒ iconstraint_sem c (wi,wb))
Proof
  rw[bits_imply_def]>>
  every_case_tac>>gvs[iconstraint_sem_def]>>
  Cases_on`EVERY wb xs`
  >-
    (drule eval_lin_term_MAP_Neg_0>> rw[])>>
  simp[]>>
  rename1`eval_ilin_term wi is + (_ + eval_lin_term wb bs) ≥ rr`>>
  drule eval_ilin_term_min_ilin_term>>
  disch_then(qspec_then`is` assume_tac)>>
  `min_lin_term bs ≤ eval_lin_term wb bs` by
    metis_tac[eval_lin_term_min_lin_term]>>
  qmatch_goalsub_abbrev_tac`int_max r 0`>>
  drule eval_lin_term_MAP_Neg_ge>>
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

(* constraint implies list of booleans *)
Definition imply_bits_def:
  imply_bits bnd xs cc =
  case cc of (is,bs,c) =>
    let nis = flip_coeffs is in
    let nbs = flip_coeffs bs in
    let nc = 1 - c in
    let r = nc + max_ilin_term bnd is + max_lin_term bs in
    let rr = int_max r 0 in
    MAP (λx. (nis, (rr, Pos x) :: nbs, nc)) xs
End

Theorem imply_bits_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (imply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇒ EVERY wb xs)
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
  rename1`wb x`>>
  Cases_on`wb x`>>simp[]
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

Theorem bimply_bits_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (bimply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇔ EVERY wb xs)
Proof
  rw[bimply_bits_def]>>
  metis_tac[imply_bits_sem,bits_imply_sem]
QED

(* Encoding a single variable X ≥ i *)
Definition encode_ge_def:
  encode_ge bnd X i =
  bimply_bits bnd [Ge X i] ([(1,X)],[],i)
End

Theorem encode_ge_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (Ge X i) ⇔ wi X ≥ i)
Proof
  rw[encode_ge_def]>>
  simp[bimply_bits_sem,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_def]>>
  metis_tac[]
QED

(* Encoding a single variable X = i
  X_{=i} ⇔ X_{>=i} ∧ ~X_{>=i+1}
*)
Definition encode_eq_def:
  encode_eq bnd X i =
  bimply_bits bnd [Eq X i]
    ([],[(1,Pos(Ge X i));(1, Neg (Ge X (i+1)))],2) ++
  encode_ge bnd X i ++
  encode_ge bnd X (i+1)
End

(* TODO: needs to be iff? *)
Theorem encode_eq_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X i)
  ⇒
  (wb (Eq X i) ⇔ wi X = i)
Proof
  rw[encode_eq_def]>>
  gs[bimply_bits_sem,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_def,encode_ge_sem,b2i_alt]>>
  every_case_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

val _ = export_theory();
