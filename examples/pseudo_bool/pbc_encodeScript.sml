(*
  Helper lemmas for developing PB encodings
*)
open preamble mlintTheory pbcTheory;

val _ = new_theory "pbc_encode";

(* TODO integerTheory? *)
Theorem INT_LE_MONO_IMP:
  0 ≤ x ∧ y ≤ z ⇒ x * y ≤ x * (z:int)
Proof
  rw[]>>
  Cases_on`x=0`>>gvs[]>>
  DEP_REWRITE_TAC[integerTheory.INT_LE_MONO]>>
  intLib.ARITH_TAC
QED

Theorem INT_LE_ANTIMONO:
  x < 0i ⇒ (x * y ≤ x * z ⇔ z ≤ y)
Proof
  `x * y = (-x) * (-y)` by simp[]>>
  pop_assum SUBST1_TAC>>
  `x * z = (-x) * (-z)` by simp[]>>
  pop_assum SUBST1_TAC>>
  strip_tac>>
  DEP_REWRITE_TAC[integerTheory.INT_LE_MONO]>>
  simp[]
QED

Theorem b2i_alt:
  b2i b = if b then 1 else 0
Proof
  rw[]
QED

Theorem eval_lit_alt:
  eval_lit w r =
    case r of
    Pos v => b2i (w v)
  | Neg v => 1 - b2i (w v)
Proof
  Cases_on`r`>>gvs[]
QED

Theorem iSUM_MAP_le:
  (∀x. MEM x xs ⇒ f x ≤ g x) ⇒
  iSUM(MAP f xs) ≤ iSUM (MAP g xs)
Proof
  Induct_on`xs`>>rw[iSUM_def]>>
  gvs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_ge:
  (∀x. MEM x xs ⇒ f x ≥ g x) ⇒
  iSUM(MAP f xs) ≥ iSUM (MAP g xs)
Proof
  Induct_on`xs`>>rw[iSUM_def]>>
  gvs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_APPEND[simp]:
  iSUM(x++y) = iSUM x + iSUM y
Proof
  Induct_on`x`>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_ge_0:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_ge_gen:
  ∀ls.
  (∀x. MEM x ls ⇒ x ≥ 0) ∧
  (∃x. MEM x ls ∧ x ≥ n)
  ⇒
  iSUM ls ≥ n
Proof
  Induct>>rw[iSUM_def]
  >- (
    `iSUM ls ≥ 0` by (
      irule iSUM_ge_0>>
      metis_tac[])>>
    intLib.ARITH_TAC)>>
  gs[SF DNF_ss]>>
  last_x_assum drule_all >>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_append[simp]:
  eval_lin_term w (xs++ys) = eval_lin_term w xs + eval_lin_term w ys
Proof
  rw[eval_lin_term_def]
QED

Theorem iSUM_MAP_const[simp]:
  ∀ls c. iSUM (MAP (λv. c) ls) = c * &(LENGTH ls)
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_MAP_Neg_0:
  EVERY w xs ⇒
  eval_lin_term w (MAP (λx. (c, Neg x)) xs) = 0
Proof
  rw[eval_lin_term_def,MAP_MAP_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac`MAP f xs`>>
  `MAP f xs = MAP (λx. 0) xs` by
    fs[MAP_EQ_f,EVERY_MEM,Abbr`f`]>>
  simp[]
QED

Theorem eval_lin_term_MAP_Neg_ge:
  ¬ EVERY w xs ∧ c ≥ 0 ⇒
  eval_lin_term w (MAP (λx. (c, Neg x)) xs) >= c
Proof
  rw[eval_lin_term_def,MAP_MAP_o,o_DEF]>>
  irule iSUM_ge_gen>>
  gvs[MEM_MAP,EXISTS_MEM]>>
  rw[]
  >-
    rw[b2i_alt]>>
  simp[PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  rw[b2i_alt]>>
  intLib.ARITH_TAC
QED

Theorem eval_lit_eq:
  eval_lit w r = 0 ∨ eval_lit w r = 1
Proof
  Cases_on`r`>>rw[b2i_alt]
QED

(* The minimum value obtainable for a lin term *)
Definition min_lin_term_def:
  min_lin_term (xs:'a lin_term) =
  iSUM (MAP (λ(c,x). int_min c 0) xs)
End

Theorem eval_lin_term_min_lin_term:
  min_lin_term xs ≤ eval_lin_term w xs
Proof
  simp[eval_lin_term_def,min_lin_term_def]>>
  match_mp_tac iSUM_MAP_le>>
  Cases>>rw[]>>
  assume_tac eval_lit_eq>>
  gvs[]>>
  intLib.ARITH_TAC
QED

(* The maximum value obtainable for a lin term *)
Definition max_lin_term_def:
  max_lin_term (xs:'a lin_term) =
  iSUM (MAP (λ(c,x). int_max c 0) xs)
End

Theorem eval_lin_term_max_lin_term:
  eval_lin_term w xs ≤ max_lin_term xs
Proof
  simp[eval_lin_term_def,max_lin_term_def]>>
  match_mp_tac iSUM_MAP_le>>
  Cases>>rw[]>>
  assume_tac eval_lit_eq>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Definition flip_coeffs_def:
  flip_coeffs xs =
    (MAP (λ(c:int,x). (-c,x)) xs)
End

Theorem eval_lin_term_flip_coeffs[simp]:
  eval_lin_term w (flip_coeffs xs) = - eval_lin_term w xs
Proof
  simp[eval_lin_term_def,flip_coeffs_def]>>
  Induct_on`xs`>>rw[iSUM_def]>>
  pairarg_tac>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_CONS[simp]:
  eval_lin_term w ((c,x)::rest) =
    c * eval_lit w x + eval_lin_term w rest
Proof
  simp[eval_lin_term_def,iSUM_def]
QED

val _ = export_theory();
