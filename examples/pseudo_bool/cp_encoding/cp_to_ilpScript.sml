(*
  Formalization of the CP to ILP phase
*)
Theory cp_to_ilp
Libs
  preamble
Ancestors
  cp ilp pbc pbc_encode sptree

val eval_raw = LIST_CONJ
  [iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_def];

(* The datatype for auxiliaries variables in the ILP encoding *)
Datatype:
  eilp =
  | Ge 'a int (* Reifies X ≥ i *)
  | Eq 'a int (* Reifies X = i *)
  | Ne ('a + int) ('a + int)  (* Used to force X ≠ Y *)
  | Gem ('a + int) ('a + int) (* Used to force X ≥ Y in Array Max *)
  | Eqc ('a + int) ('a + int) (* Used to force X = Y in Count *)
  | Nv ('a list) int (* Used to force some element in As = v *)
  | Tb ('a list) (int list)
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

Theorem bits_imply_sem:
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

Theorem imply_bits_sem:
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

Theorem bimply_bits_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (bimply_bits bnd xs c)
  =
  (iconstraint_sem c (wi,wb) ⇔ EVERY (lit wb) xs)
Proof
  rw[bimply_bits_def]>>
  metis_tac[imply_bits_sem,bits_imply_sem]
QED

(* Encoding a single variable X_{>=i} ⇔ X ≥ i *)
Definition encode_ge_def:
  encode_ge bnd X i =
  bimply_bits bnd [Pos (Ge X i)] ([(1,X)],[],i)
End

Theorem encode_ge_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (Ge X i) ⇔ wi X ≥ i)
Proof
  rw[encode_ge_def]>>
  simp[bimply_bits_sem,eval_raw]>>
  metis_tac[]
QED

(* Encoding a single variable X = i
  X_{=i} ⇔ X_{>=i} ∧ ~X_{>=i+1}
*)
Definition encode_eq_def:
  encode_eq bnd X i =
  bimply_bits bnd [Pos (Eq X i)]
    ([],[(1,Pos(Ge X i));(1, Neg (Ge X (i+1)))],2)
End

Theorem encode_eq_sem:
  valid_assignment bnd wi ∧
  (wb (Ge X i) ⇔ wi X ≥ i) ∧
  (wb (Ge X (i+1)) ⇔ wi X ≥ i+1)
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X i)
  =
  (wb (Eq X i) ⇔ wi X = i)
Proof
  rw[encode_eq_def]>>
  gs[bimply_bits_sem,eval_raw,b2i_alt]>>
  rw[]>>
  eq_tac>>rw[]>>
  intLib.ARITH_TAC
QED

(* Encodes a * X + b * Y ≥ c where both terms are varc *)
Definition mk_constraint_ge_def:
  mk_constraint_ge (a:int) X (b:int) Y (c:int) =
  case (X,Y) of
    (INL vX, INL vY) =>
      ([(a,vX);(b,vY)],[],c)
  | (INL vX, INR cY) =>
      ([(a,vX)],[],c - b * cY)
  | (INR cX, INL vY) =>
      ([(b,vY)],[],c - a * cX)
  | (INR cX, INR cY) =>
      ([],[],c - a * cX - b * cY)
End

Theorem mk_constraint_ge_sem:
  iconstraint_sem (mk_constraint_ge a X b Y c) (wi,wb) ⇔
  a * (varc wi X) + b * (varc wi Y) ≥ c
Proof
  rw[mk_constraint_ge_def]>>every_case_tac>>
  gvs[varc_def,eval_raw]>>
  intLib.ARITH_TAC
QED

(* X_{=i} ⇒ Ai = R where Ai, R can be Varc *)
Definition encode_element_eq_def:
  encode_element_eq bnd R X (i:num,Ai) =
  [
    bits_imply bnd [Pos (Eq X (&(i+1)))] (mk_constraint_ge 1 Ai (-1) R 0);
    bits_imply bnd [Pos (Eq X (&(i+1)))] (mk_constraint_ge 1 R (-1) Ai 0)
  ]
End

Theorem encode_element_eq_sem:
  valid_assignment bnd wi ∧
  (wb (Eq X &(i+1)) ⇔ wi X = &(i+1))
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element_eq bnd R X (i,Ai))
  =
  (wi X = &(i+1) ⇒ varc wi R = varc wi Ai)
Proof
  rw[encode_element_eq_def,eval_raw,bits_imply_sem,mk_constraint_ge_sem]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* Adds X ≥ 1, - X ≥ -|As| where needed *)
Definition encode_element_var_def:
  encode_element_var (bnd:'a bounds) R X As =
  let (lb:int,ub:int) = bnd X in
  let (len:int) = &(LENGTH As) in
  let ges = FLAT (GENLIST (λi. encode_ge bnd X &(i+1)) (LENGTH As + 1)) in
  let eqs = FLAT (GENLIST (λi. encode_eq bnd X &(i+1)) (LENGTH As)) in
  let xlb = if lb < 1 then [([(1i,X)],[],1i)] else [] in
  let xub = if len < ub then [([(-1i,X)],[],-len)] else [] in
    ges ++ eqs ++ xlb ++ xub ++
    FLAT (MAP (encode_element_eq bnd R X) (enumerate 0n As))
End

(* TODO: copied from npbc_check, move into misc... *)
Theorem MEM_enumerate_index:
  ∀k xs.
  MEM (i,e) (enumerate k xs) ⇒
  ∃j. j < LENGTH xs ∧ i = k + j
Proof
  Induct_on`xs`>>rw[miscTheory.enumerate_def]
  >- intLib.ARITH_TAC>>
  first_x_assum drule>>
  rw[]
  >- intLib.ARITH_TAC
QED

Theorem MEM_enumerate_iff:
  MEM ie (enumerate 0 xs) ⇔
  ∃i e. ie = (i,e) ∧ i < LENGTH xs ∧ EL i xs = e
Proof
  Cases_on`ie`>>
  rename1`MEM (i,e) _ `>>
  Cases_on`i < LENGTH xs`>>fs[MEM_enumerate]
  >- metis_tac[]>>
  CCONTR_TAC>>fs[]>>
  drule MEM_enumerate_index>>
  rw[]
QED

(* TODO: is this style better? *)
Theorem encode_element_var_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element_var bnd R X As)
  =
  (
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As + 1 ⇒
    (wb (Ge X &i) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As ⇒
    (wb (Eq X &i) ⇔ wi X = &i)) ∧
  element_sem R (INL X) As wi)
Proof
  rw[encode_element_var_def]>>
  pairarg_tac>>simp[element_sem_def]>>
  simp[GSYM CONJ_ASSOC]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >- (
    simp[EVERY_FLAT,EVERY_GENLIST,encode_ge_sem]>>
    eq_tac>>rw[]>>
    first_x_assum(qspec_then`i-1` mp_tac)>>simp[])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  (* annoying ... *)
  CONJ_TAC >- (
    simp[EVERY_FLAT,EVERY_GENLIST]>>
    eq_tac>>rw[]
    >- (
      DEP_REWRITE_TAC[GSYM encode_eq_sem]>>
      simp[]>>
      first_x_assum(qspec_then`i-1`mp_tac)>>
      simp[]>>
      first_x_assum(qspec_then`i + 1 `mp_tac)>>
      simp[]>>
      `&(i+1) = &i + 1i` by intLib.ARITH_TAC>>
      simp[])>>
    DEP_REWRITE_TAC[encode_eq_sem]>>
    simp[]>>
    last_x_assum(qspec_then`i + 1 + 1`mp_tac)>>
      `&(i+2) = &(i + 1) + 1i` by intLib.ARITH_TAC>>
    simp[])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >- (
    gvs[varc_def,valid_assignment_def]>>
    first_x_assum drule>>rw[eval_raw]>>
    intLib.ARITH_TAC)>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >- (
    gvs[varc_def,valid_assignment_def]>>
    first_x_assum drule>>rw[eval_raw]>>
    intLib.ARITH_TAC)>>
  strip_tac>>
  rw[EVERY_FLAT,EVERY_MAP]>>
  `∀x. MEM x (enumerate 0 As) ⇒
       (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element_eq bnd R X x) ⇔
       (wi X = &(FST x + 1) ⇒ varc wi R = varc wi (SND x)))` by (
    Cases>>rw[]>>
    match_mp_tac encode_element_eq_sem>>
    simp[]>>
    first_x_assum match_mp_tac>>
    gvs[MEM_enumerate_iff])>>
  `EVERY (λx.
      EVERY (λx. iconstraint_sem x (wi,wb))
      (encode_element_eq bnd R X x)) (enumerate 0 As) ⇔
   EVERY (λx.
      (wi X = &(FST x + 1) ⇒ varc wi R = varc wi (SND x))) (enumerate 0 As)` by
   (match_mp_tac EVERY_CONG>>
   simp[])>>
  simp[EVERY_MEM,MEM_enumerate_iff,PULL_EXISTS] >>
  eq_tac>>rw[]
  >- (
    first_x_assum irule>>
    gvs[varc_def]>>
    intLib.ARITH_TAC)>>
  simp[varc_def]
QED

Definition encode_element_const_def:
  encode_element_const R (X:int) As =
  if 1 ≤ X ∧ X ≤ &(LENGTH As)
  then
    let Ai = EL (Num X -1) As in
    [mk_constraint_ge 1 Ai (-1) R 0;
     mk_constraint_ge 1 R (-1) Ai 0]
  else
    [([],[],1)]
End

Theorem encode_element_const_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element_const R X As)
  =
  element_sem R (INR X) As wi
Proof
  rw[encode_element_const_def,eval_raw,mk_constraint_ge_sem,element_sem_def]
  >- (
    simp[varc_def]>>
    eq_tac>>rw[]>>
    intLib.ARITH_TAC)>>
  fs[varc_def]>>
  intLib.ARITH_TAC
QED

Definition encode_element_def:
  encode_element bnd R X As =
  case X of
    INL vX => encode_element_var bnd R vX As
  | INR cX => encode_element_const R cX As
End

(* TODO: This seem too precise *)
Theorem encode_element_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element bnd R X As)
  =
  (
  (case X of INR _ => T | INL X =>
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As + 1 ⇒
    (wb (Ge X &i) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As ⇒
    (wb (Eq X &i) ⇔ wi X = &i))) ∧
  element_sem R X As wi)
Proof
  rw[encode_element_def]>>
  TOP_CASE_TAC>>gvs[]
  >-
    metis_tac[encode_element_var_sem]
  >>
    metis_tac[encode_element_const_sem]
QED

Definition reify_eilp_def:
  reify_eilp wi eb ⇔
  case eb of
    Ge X i => wi X ≥ i
  | Eq X i => wi X = i
  | Ne X Y => varc wi X > varc wi Y
  | Gem X Y => varc wi X ≥ varc wi Y
  | Eqc X Y => varc wi X = varc wi Y
  | Tb Xs Ts => ARB
  | Nv Xs v => ARB
End

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem R X As wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_eilp wi)) (encode_element bnd R X As)
Proof
  rw[encode_element_def]>>
  TOP_CASE_TAC>>gvs[]
  >- (
    DEP_REWRITE_TAC [encode_element_var_sem]>>
    simp[reify_eilp_def])
  >>
    metis_tac[encode_element_const_sem]
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element bnd R X As) ⇒
  element_sem R X As wi
Proof
  rw[encode_element_def]>>
  every_case_tac>>gvs[]
  >- (
    pop_assum mp_tac>>
    DEP_REWRITE_TAC[encode_element_var_sem]>>
    simp[])
  >>
    metis_tac[encode_element_const_sem]
QED

Definition encode_not_equals_def:
  encode_not_equals bnd X Y =
  [
    bits_imply bnd [Pos (Ne X Y)] (mk_constraint_ge 1 X (-1) Y 1);
    bits_imply bnd [Neg (Ne X Y)] (mk_constraint_ge 1 Y (-1) X 1)
  ]
End

(* Prove together? Or separate? *)
Theorem not_equals_sem_aux:
  (if wb (Ne X Y)
   then varc wi X > varc wi Y
   else varc wi Y > varc wi X) ⇒
  not_equals_sem X Y wi
Proof
  simp[not_equals_sem_def]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem IMP_AND_LEFT:
  (P ⇒ Q) ⇒
  (P ∧ Q ⇔ P)
Proof
  metis_tac[]
QED

Theorem encode_not_equals_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_not_equals bnd X Y)
  =
  (
  (if wb (Ne X Y)
   then varc wi X > varc wi Y
   else varc wi Y > varc wi X) ∧
  not_equals_sem X Y wi)
Proof
  strip_tac>>
  simp[MATCH_MP IMP_AND_LEFT not_equals_sem_aux]>>
  simp[encode_not_equals_def,bits_imply_sem,mk_constraint_ge_sem]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Definition encode_all_different_def:
  encode_all_different bnd As =
  let len = LENGTH As in
  FLAT
  (GENLIST (λi.
    FLAT (GENLIST (λj. if i < j then encode_not_equals bnd (EL i As) (EL j As) else []) len)) len)
End

Theorem all_different_sem_aux:
  (∀i j. i < j ∧ j < LENGTH As ⇒
    let X = EL i As in
    let Y = EL j As in
    if wb (Ne X Y)
    then varc wi X > varc wi Y
    else varc wi Y > varc wi X) ⇒
  all_different_sem As wi
Proof
  rw[all_different_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
  Cases_on`n1 = n2`>>simp[]>>
  wlog_tac `n1 < n2` [`n1`,`n2`]
  >- (
    `n2 < n1` by fs[]>>
    first_x_assum drule_all>>
    simp[])>>
  first_x_assum drule>>
  rw[EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_different_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_all_different bnd As)
  =
  (
  (∀i j. i < j ∧ j < LENGTH As ⇒
    let X = EL i As in
    let Y = EL j As in
    if wb (Ne X Y)
    then varc wi X > varc wi Y
    else varc wi Y > varc wi X) ∧
  all_different_sem As wi)
Proof
  simp[MATCH_MP IMP_AND_LEFT all_different_sem_aux]>>
  rw[encode_all_different_def, EVERY_FLAT, EVERY_GENLIST]>>
  eq_tac>>rw[]>>
  gvs[PULL_FORALL]
  >- (
    first_x_assum(qspecl_then[`i`,`j`] mp_tac)>>
    simp[encode_not_equals_sem])>>
  rw[]>>
  first_x_assum drule_all>>
  metis_tac[encode_not_equals_sem,not_equals_sem_aux]
QED

(* Encoding for Y a variable *)
Definition encode_abs_var_def:
  encode_abs_var bnd X Y =
  let vY = INL Y in
  encode_ge bnd Y 0 ++
  [
    bits_imply bnd [Pos (Ge Y 0)] (mk_constraint_ge 1 X (-1) vY 0);
    bits_imply bnd [Pos (Ge Y 0)] (mk_constraint_ge 1 vY (-1) X 0);
    bits_imply bnd [Neg (Ge Y 0)] (mk_constraint_ge 1 X 1 vY 0);
    bits_imply bnd [Neg (Ge Y 0)] (mk_constraint_ge (-1) X (-1) vY 0);
  ]
End

Theorem encode_abs_var_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs_var bnd X Y)
  =
  (
    (wb (Ge Y 0) ⇔ wi Y ≥ 0) ∧
    abs_sem X (INL Y) wi
  )
Proof
  rw[encode_abs_var_def]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >- simp[encode_ge_sem]>>
  strip_tac>>
  simp[bits_imply_sem,mk_constraint_ge_sem,abs_sem_def]>>
  `varc wi (INL Y) = wi Y` by simp[varc_def]>>
  intLib.ARITH_TAC
QED

Definition encode_abs_const_def:
  encode_abs_const X Y =
  if Y ≥ 0 then
  [
    mk_constraint_ge 1 X (-1) (INR Y) 0;
    mk_constraint_ge (-1) X 1 (INR Y) 0;
  ]
  else
  [
    mk_constraint_ge 1 X 1 (INR Y) 0;
    mk_constraint_ge (-1) X (-1) (INR Y) 0;
  ]
End

Theorem encode_abs_const_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs_const X Y)
  =
  abs_sem X (INR Y) wi
Proof
  rw[encode_abs_const_def]>>
  simp[abs_sem_def,mk_constraint_ge_sem]>>
  `varc wi (INR Y) = Y` by simp[varc_def]>>
  simp[]>>
  intLib.ARITH_TAC
QED

Definition encode_abs_def:
  encode_abs bnd X Y =
  case Y of
    INL vY => encode_abs_var bnd X vY
  | INR cY => encode_abs_const X cY
End

(* TODO: This seem too precise *)
Theorem encode_abs_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs bnd X Y)
  =
  (
  (case Y of INR _ => T | INL Y =>
  (wb (Ge Y 0) ⇔ wi Y ≥ 0)) ∧
  abs_sem X Y wi)
Proof
  rw[encode_abs_def]>>
  TOP_CASE_TAC>>gvs[]
  >-
    metis_tac[encode_abs_var_sem]
  >>
    metis_tac[encode_abs_const_sem]
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

Definition encode_ilc_def:
  encode_ilc (Xs:'a iclin_term) (op:pbop) (rhs:int) =
  let (xs,rhs) = split_iclin_term Xs [] rhs in
  case op of
    GreaterEqual => [(xs, [], rhs)]
  | Greater => [(xs, [] , rhs+1)]
  | LessEqual => [(MAP (λ(x:int, y). (-x, y)) xs, [], -rhs)]
  | Less => [(MAP (λ(x:int, y). (-x, y)) xs, [], -rhs+1)]
  | Equal => [(xs, [], rhs); (MAP (λ(x:int, y). (-x, y)) xs, [], -rhs)]
End

Theorem encode_ilc_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ilc Xs op rhs)
  ⇔
  ilc_sem Xs op rhs wi
Proof
  rw[encode_ilc_def,ilc_sem_def]>>
  pairarg_tac>>gvs[]>>
  CASE_TAC>>
  simp[iconstraint_sem_def, eval_lin_term_def, iSUM_def]>>
  ‘∀xs. eval_ilin_term wi (MAP (λ(x,y). (-x,y)) xs) = -(eval_ilin_term wi xs)’ by (
    Induct
    >-simp[eval_ilin_term_def, iSUM_def]
    >-(
      Cases>>
      pop_assum mp_tac>>
      simp[eval_ilin_term_def, iSUM_def]>>
      intLib.ARITH_TAC))>>
  pop_assum (fn thm => simp[thm])>>
  drule_then (qspec_then ‘wi’ mp_tac) split_iclin_term_sound>>
  rw[Once eval_ilin_term_def, iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_ge_1:
  eval_lin_term wb (MAP (λe. (1, f e)) ls) ≥ 1 ⇔
  ∃e. MEM e ls ∧ lit wb (f e)
Proof
  rw[eval_lin_term_def]>>
  Induct_on ‘ls’>>
  rw[iSUM_def,b2i_alt]
  >-(
    simp[SF DNF_ss]>>
    qmatch_goalsub_abbrev_tac`_ + iSUM lss ≥ _`>>
    `iSUM lss ≥ 0` by (
      irule iSUM_ge_0>>
      simp[Abbr`lss`,MEM_MAP,PULL_EXISTS,b2i_alt]>>
      rw[])>>
    intLib.ARITH_TAC)
  >- metis_tac[]
QED

Theorem iSUM_le_0:
  (∀x. MEM x ls ⇒ x ≤ 0) ⇒ iSUM ls ≤ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_neg_ge_0:
  eval_lin_term wb (MAP (λe. (-1, f e)) ls) ≥ 0 ⇔
  ∀e. MEM e ls ⇒ ¬lit wb (f e)
Proof
  rw[eval_lin_term_def]>>
  Induct_on ‘ls’>>
  rw[iSUM_def,b2i_alt]
  >-(
    simp[SF DNF_ss,integerTheory.INT_GE,integerTheory.INT_NOT_LE]>>
    qmatch_goalsub_abbrev_tac ‘_ + iSUM lss < _’>>
    ‘iSUM lss ≤ 0’ by (
      irule iSUM_le_0>>
      simp[Abbr‘lss’,MEM_MAP,PULL_EXISTS,b2i_alt]>>
      rw[])>>
    intLib.ARITH_TAC)
  >-metis_tac[]
QED

(* Encodes that all As ≥ M *)
Definition encode_Gem_ge_def:
  encode_Gem_ge bnd As M =
  MAP (λA. bits_imply bnd [Pos (Gem A M)] (mk_constraint_ge 1 A (-1) M 0)) As
End

(* iff versions *)
Definition encode_Gem_ge_iff_def:
  encode_Gem_ge_iff bnd As M =
  encode_Gem_ge bnd As M ++
  MAP (λA. bits_imply bnd [Neg (Gem A M)] (mk_constraint_ge 1 M (-1) A 1)) As
End

 (* Encodes that all As ≤ M *)
Definition encode_Gem_le_def:
  encode_Gem_le bnd As M =
  MAP (λA. bits_imply bnd [Pos (Gem M A)] (mk_constraint_ge 1 M (-1) A 0)) As
End

Definition encode_Gem_le_iff_def:
  encode_Gem_le_iff bnd As M =
  encode_Gem_le bnd As M ++
  MAP (λA. bits_imply bnd [Neg (Gem M A)] (mk_constraint_ge 1 A (-1) M 1)) As
End

Theorem encode_Gem_ge_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_ge bnd As M) =
    (∀A. MEM A As ∧ wb (Gem A M) ⇒ varc wi A ≥ varc wi M)
Proof
  rw[encode_Gem_ge_def]>>
  simp[EVERY_MAP,EVERY_MEM,bits_imply_sem,mk_constraint_ge_sem,GSYM integerTheory.INT_POLY_CONV_rth,integerTheory.INT_GE, integerTheory.INT_SUB_LE]>>
  metis_tac[]
QED

Theorem encode_Gem_le_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_le bnd As M) =
    (∀A. MEM A As ∧ wb (Gem M A) ⇒ varc wi A ≤ varc wi M)
Proof
  rw[encode_Gem_le_def]>>
  simp[EVERY_MAP,EVERY_MEM,bits_imply_sem,mk_constraint_ge_sem,GSYM integerTheory.INT_POLY_CONV_rth,integerTheory.INT_GE, integerTheory.INT_SUB_LE]>>
  metis_tac[]
QED

Theorem encode_Gem_ge_iff_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_ge_iff bnd As M) =
    (∀A. MEM A As ⇒ (wb (Gem A M) ⇔ varc wi A ≥ varc wi M))
Proof
  rw[encode_Gem_ge_iff_def,encode_Gem_ge_sem]>>
  simp[EVERY_MAP,EVERY_MEM,bits_imply_sem,mk_constraint_ge_sem,
    intLib.ARITH_PROVE ``X + -1 * (Y:int) ≥ 1 ⇔ ¬ (Y ≥ X)``]>>
  metis_tac[]
QED

Theorem encode_Gem_le_iff_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_le_iff bnd As M) =
    (∀A. MEM A As ⇒ (wb (Gem M A) ⇔ varc wi A ≤ varc wi M))
Proof
  rw[encode_Gem_le_iff_def,encode_Gem_le_sem]>>
  simp[EVERY_MAP,EVERY_MEM,bits_imply_sem,mk_constraint_ge_sem,
    intLib.ARITH_PROVE ``X + -1 * (Y:int) ≥ 1 ⇔ ¬ (X <= Y)``]>>
  metis_tac[]
QED

Definition encode_arr_max_def:
  encode_arr_max bnd M As =
  ([], MAP (λA. (1, Pos (Gem A M))) As, 1) ::
  encode_Gem_ge bnd As M ++
  MAP (λA. mk_constraint_ge 1 M (-1) A 0) As
End

Theorem encode_arr_max_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_arr_max bnd M As) = (
    (∃A. MEM A As ∧ wb (Gem A M)) ∧
    (∀A. MEM A As ∧ wb (Gem A M) ⇒ varc wi A ≥ varc wi M) ∧
    arr_max_sem M As wi)
Proof
  strip_tac>>
  simp[encode_arr_max_def,encode_Gem_ge_sem]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >-
    simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_ge_1]>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>> simp[]>>
  strip_tac>>
  simp[arr_max_sem_def,EVERY_MAP,mk_constraint_ge_sem,GSYM integerTheory.INT_POLY_CONV_rth,
       integerTheory.INT_GE,integerTheory.INT_SUB_LE,MEM_MAP,EVERY_MEM]>>
  iff_tac>>
  rw[]>>
  pop_assum drule>>
  pop_assum drule>>
  rw[integerTheory.INT_GE,GSYM integerTheory.INT_LE_ANTISYM]>>
  simp[SF SFY_ss]
QED

Definition encode_arr_min_def:
  encode_arr_min bnd M As =
  ([], MAP (λA. (1, Pos (Gem M A))) As, 1) ::
  encode_Gem_le bnd As M ++
  MAP (λA. mk_constraint_ge 1 A (-1) M 0) As
End

Theorem encode_arr_min_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_arr_min bnd M As) = (
    (∃A. MEM A As ∧ wb (Gem M A)) ∧
    (∀A. MEM A As ∧ wb (Gem M A) ⇒ varc wi A ≤ varc wi M) ∧
    arr_min_sem M As wi)
Proof
  strip_tac>>
  simp[encode_arr_min_def,encode_Gem_le_sem]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >-
    simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_ge_1]>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>> simp[]>>
  strip_tac>>
  simp[arr_min_sem_def,EVERY_MAP,mk_constraint_ge_sem,GSYM integerTheory.INT_POLY_CONV_rth,
       integerTheory.INT_GE,integerTheory.INT_SUB_LE,MEM_MAP,EVERY_MEM]>>
  iff_tac>>
  rw[]>>
  pop_assum drule>>
  pop_assum drule>>
  rw[integerTheory.INT_GE,GSYM integerTheory.INT_LE_ANTISYM]>>
  simp[SF SFY_ss]
QED

Definition encode_count_def:
  encode_count bnd Y C As =
  let
    ilpc =
    case C of
      INL vC => [
        ([(-1, vC)], MAP (λA. (1, Pos (Eqc A Y))) As, 0);
        ([(1, vC)], MAP (λA. (-1, Pos (Eqc A Y))) As, 0)]
    | INR cC => [
        ([], MAP (λA. (1, Pos (Eqc A Y))) As, cC);
        ([], MAP (λA. (-1, Pos (Eqc A Y))) As, -cC)]
  in
    encode_Gem_ge_iff bnd As Y ++
    encode_Gem_le_iff bnd As Y ++
    MAP (λA. bits_imply bnd [Pos (Eqc A Y)]
                        ([], [(1, Pos (Gem A Y)); (1, Pos (Gem Y A))], 2)) As ++
    MAP (λA. bits_imply bnd [Neg (Eqc A Y)]
                        ([], [(1, Neg (Gem A Y)); (1, Neg (Gem Y A))], 1)) As ++
    ilpc
End

Theorem iSUM_MAP_lin:
  ∀ls a f b. iSUM (MAP (λx. a * f x + b) ls) = a * iSUM (MAP (λx. f x) ls) + b * &LENGTH ls
Proof
  Induct>>
  simp[iSUM_def,MAP,LENGTH]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_lin_const = iSUM_MAP_lin |> CONV_RULE (RESORT_FORALL_CONV List.rev) |> Q.SPEC `0` |> SRULE [] |> SPEC_ALL;

Theorem b2i_ge_2[simp]:
  b2i b1 + b2i b2 ≥ 2 ⇔ b1 ∧ b2
Proof
  rw[b2i_alt]
QED

Theorem b2i_ge_1[simp]:
  b2i b1 + b2i b2 ≥ 1 ⇔ b1 ∨ b2
Proof
  rw[b2i_alt]
QED

Theorem b2i_ge_0:
  b2i b ≥ 0
Proof
  rw[b2i_alt]
QED

Theorem encode_count_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_count bnd Y C As) = (
    EVERY (λA. wb (Gem A Y) ⇔ varc wi A ≥ varc wi Y) As ∧
    EVERY (λA. wb (Gem Y A) ⇔ varc wi Y ≥ varc wi A) As ∧
    EVERY (λA. wb (Eqc A Y) ⇔ varc wi A = varc wi Y) As ∧
    count_sem Y C As wi)
Proof
  strip_tac>>
  simp[encode_count_def]>>
  simp[GSYM CONJ_ASSOC]>>
  ho_match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >-
    simp[encode_Gem_ge_iff_sem,EVERY_MEM]>>
  strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >-
    simp[encode_Gem_le_iff_sem,EVERY_MEM,integerTheory.INT_GE]>>
  strip_tac>>
  simp[CONJ_ASSOC]>>
  ho_match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC >- (
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,bits_imply_sem,iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,iSUM_def]>>
    metis_tac[integerTheory.INT_LE_ANTISYM,integerTheory.INT_GE])>>
  strip_tac
  >- (
    Cases_on ‘C’>>
    simp[count_sem_def]>>
    rw[METIS_PROVE[] “∀P a b. (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b”]>>
    simp[iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
      MAP_MAP_o,combinTheory.o_ABS_R,b2i_alt,iSUM_def,Once varc_def]>>
    ‘iSUM (MAP (λA. if wb (Eqc A Y) then 1 else 0) As) =
     iSUM (MAP (λA. if varc wi A = varc wi Y then 1 else 0) As)’ by
      fs[EVERY_MEM,Cong MAP_CONG]>>
    simp[iSUM_MAP_lin_const]>>
    intLib.ARITH_TAC)
QED

(* domain of X given by bnd (as a list) *)
Definition domlist_def:
  domlist bnd X =
  let
    (lb, ub) = bnd X
  in
    if ub < lb
    then []
    else GENLIST (λn. &n + lb) (Num (ub - lb) + 1)
End

Theorem MEM_domlist:
  valid_assignment bnd wi ⇒
  MEM (wi X) (domlist bnd X)
Proof
  Cases_on ‘bnd X’>>
  rw[domlist_def,valid_assignment_def,MEM_GENLIST]>>
  res_tac
  >-(
    goal_assum $ drule_at Any>>
    intLib.ARITH_TAC)>>
  intLib.ARITH_TAC
QED

(* bijection 0, -1, 1, -2, 2,... ⇔ 0, 1, 2, 3, 4,... and its inverse next *)
Definition intnum_def:
  intnum (n: int) =
  if n < 0 then 2 * Num (-n) - 1
  else 2 * Num n
End

Definition numint_def:
  numint (n: num): int =
  if EVEN n then &((n + 1) DIV 2)
  else -&((n + 1) DIV 2)
End

Theorem numint_inj:
  numint m = numint n ⇒ m = n
Proof
  simp[numint_def]>>
  intLib.ARITH_TAC
QED

Theorem numint_intnum:
  numint (intnum x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Theorem intnum_numint:
  intnum (numint x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Definition numset_to_intlist_def:
  numset_to_intlist t = MAP (numint o FST) $ toSortedAList t
End

Theorem ALL_DISTINCT_numset_to_intlist:
  ALL_DISTINCT $ numset_to_intlist t
Proof
  simp[numset_to_intlist_def,GSYM MAP_MAP_o]>>
  irule ALL_DISTINCT_MAP_INJ>>
  simp[ALL_DISTINCT_MAP_FST_toSortedAList,numint_inj]
QED

(* Union of all int values in domains of Xs *)
Definition union_dom_def:
  union_dom bnd Xs =
  numset_to_intlist $ FOLDL union LN $
    MAP (λX. list_to_num_set $ MAP intnum $ domlist bnd X) Xs
End

Theorem MEM_numset_to_intlist:
  MEM x (numset_to_intlist ns) ⇔
  intnum x ∈ domain ns
Proof
  rw[numset_to_intlist_def,GSYM MAP_MAP_o,MEM_MAP,EXISTS_PROD,
    MEM_toSortedAList,domain_lookup]>>
  metis_tac[intnum_numint,numint_intnum]
QED

Theorem domain_FOLDL_union:
  ∀ls t.
  x ∈ domain (FOLDL union t ls) ⇔
  x ∈ domain t ∨ ∃ns. ns ∈ set ls ∧ x ∈ domain ns
Proof
  Induct>>rw[]>>
  metis_tac[]
QED

Theorem EVERY_MEM_union_dom:
  valid_assignment bnd wi ⇒
  EVERY (λA. MEM (wi A) (union_dom bnd Xs)) Xs
Proof
  rw[EVERY_MEM,union_dom_def,MEM_numset_to_intlist,domain_FOLDL_union]>>
  simp[MEM_MAP,PULL_EXISTS,domain_list_to_num_set]>>
  metis_tac[MEM_domlist]
QED

Theorem ALL_DISTINCT_union_dom:
  ALL_DISTINCT $ union_dom bnd Xs
Proof
  simp[union_dom_def,ALL_DISTINCT_numset_to_intlist]
QED

(* encodes fnvalue_v ⇒ some X = v and ~fnvalue_v ⇒ no X = v *)
Definition encode_some_eq_def:
  encode_some_eq bnd Xs (v: int) = [
    bits_imply bnd [Pos (Nv Xs v)]
      ([], MAP (λA. (1i, Pos (Eq A v))) Xs, 1i);
    bits_imply bnd [Neg (Nv Xs v)]
      ([], MAP (λA. (-1i, Pos (Eq A v))) Xs, 0i)]
End

Theorem encode_some_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λX. wb (Eq X v) ⇔ wi X = v) Xs ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_some_eq bnd Xs v) =
  (wb (Nv Xs v) ⇔ ∃A. MEM A Xs ∧ wb (Eq A v)))
Proof
  rw[encode_some_eq_def,bits_imply_sem,iconstraint_sem_def,eval_ilin_term_def,
    iSUM_def,MAP_MAP_o,eval_lin_term_ge_1,eval_lin_term_neg_ge_0]>>
  metis_tac[]
QED

Definition reify_some_eq_def:
  reify_some_eq bnd Xs v =
  let
    ges = FLAT $ MAP (λX. encode_ge bnd X v ++ encode_ge bnd X (v + 1)) Xs;
    eqs = FLAT $ MAP (λX. encode_eq bnd X v) Xs
  in
    ges ++ eqs ++ encode_some_eq bnd Xs v
End

Theorem FORALL_IMP_EQ = METIS_PROVE []
  ``(∀x. P x ⇒ (Q x ⇔ R x)) ⇒ ((∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x))``;

Theorem reify_some_eq_sem:
  valid_assignment bnd wi ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP (reify_some_eq bnd Xs)
    (union_dom bnd Xs))) ⇔
  ∀v. MEM v (union_dom bnd Xs) ⇒
      EVERY (λX. wb (Ge X v) ⇔ wi X ≥ v) Xs ∧
      EVERY (λX. wb (Ge X (v + 1)) ⇔ wi X ≥ v + 1) Xs ∧
      EVERY (λX. wb (Eq X v) ⇔ wi X = v) Xs ∧
      (wb (Nv Xs v) ⇔ ∃A. MEM A Xs ∧ wb (Eq A v)))
Proof
  rw[reify_some_eq_def,EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_MEM,Once $ GSYM CONJ_ASSOC]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  rw[EVERY_CONJ,GSYM CONJ_ASSOC]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (
    irule EVERY_CONG>>
    rw[]>>
    irule encode_eq_sem>>
    fs[EVERY_MEM])>>
  simp[encode_some_eq_sem]
QED

(* encodes (sum of the bitlist Bs) = Y *)
Definition encode_bitsum_def:
  encode_bitsum Bs Y =
  case Y of
    INL vY => [
      ([(-1i, vY)], MAP (λb. (1i, Pos b)) Bs, 0i);
      ([(1i, vY)], MAP (λb. (-1i, Pos b)) Bs, 0i)]
  | INR cY => [
      ([], MAP (λb. (1i, Pos b)) Bs, cY);
      ([], MAP (λb. (-1i, Pos b)) Bs, -cY)]
End

Theorem encode_bitsum_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_bitsum Bs Y) ⇔
  iSUM $ MAP (b2i o wb) Bs = varc wi Y)
Proof
  rw[encode_bitsum_def]>>
  CASE_TAC>>
  simp[varc_def,iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
    eval_iterm_def,eval_term_def,iSUM_def,MAP_MAP_o,combinTheory.o_ABS_R,
    iSUM_MAP_lin_const]>>
  simp[GSYM combinTheory.o_ABS_R,GSYM combinTheory.I_EQ_IDABS]>>
  intLib.ARITH_TAC
QED

Theorem encode_nvalue_sem_aux:
  valid_assignment bnd wi ∧
  (∀v. MEM v (union_dom bnd Xs) ⇒
    EVERY (λX. wb (Eq X v) ⇔ wi X = v) Xs ∧
    (wb (Nv Xs v) ⇔ ∃A. MEM A Xs ∧ wb (Eq A v))) ⇒
  ∀v. MEM v (MAP wi Xs) ⇔ MEM v (FILTER (λv. wb (Nv Xs v)) (union_dom bnd Xs))
Proof
  rw[MEM_FILTER,MEM_MAP]>>
  iff_tac>>
  strip_tac
  >-(
    CONJ_ASM2_TAC
    >- (
      gvs[EVERY_MEM]>>
      metis_tac[])>>
    drule_then assume_tac EVERY_MEM_union_dom>>
    fs[EVERY_MEM])>>
  gvs[EVERY_MEM]>>
  metis_tac[]
QED

Theorem list_set_eq:
  ∀ls1 ls2. (∀v. MEM v ls1 ⇔ MEM v ls2) ⇔ set ls1 = set ls2
Proof
  rw[SET_EQ_SUBSET]>>
  simp[GSYM SUBSET_DIFF_EMPTY,list_to_set_diff,GSYM NULL_EQ,NULL_FILTER]>>
  metis_tac[]
QED

Theorem iSUM_FILTER:
  iSUM (MAP (b2i o P) ls) = &(LENGTH $ FILTER P ls)
Proof
  Induct_on ‘ls’>>
  rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition encode_nvalue_def:
  encode_nvalue bnd Y Xs =
  let
    vals = union_dom bnd Xs;
  in
    (FLAT $ MAP (reify_some_eq bnd Xs) vals) ++
    encode_bitsum (MAP (λv. Nv Xs v) vals) Y
End

Theorem encode_nvalue_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_nvalue bnd Y Xs) = (
    nvalue_sem Y Xs wi ∧
    ∀v. MEM v (union_dom bnd Xs) ⇒
        EVERY (λX. wb (Ge X v) ⇔ wi X ≥ v) Xs ∧
        EVERY (λX. wb (Ge X (v + 1)) ⇔ wi X ≥ v + 1) Xs ∧
        EVERY (λX. wb (Eq X v) ⇔ wi X = v) Xs ∧
        (wb (Nv Xs v) ⇔ ∃A. MEM A Xs ∧ wb (Eq A v)))
Proof
  rw[encode_nvalue_def,Once CONJ_COMM]>>
  match_mp_tac $ METIS_PROVE[] “(Q ⇔ Q') ∧ (Q' ⇒ (P ⇔ P')) ⇒ (P ∧ Q ⇔ P' ∧ Q')”>>
  CONJ_TAC>>
  simp[reify_some_eq_sem]>>
  strip_tac>>
  ‘∀v. MEM v (union_dom bnd Xs) ⇒
    EVERY (λX. wb (Eq X v) ⇔ wi X = v) Xs ∧
    (wb (Nv Xs v) ⇔ ∃A. MEM A Xs ∧ wb (Eq A v))’ by metis_tac[]>>
  drule_all_then assume_tac encode_nvalue_sem_aux>>
  drule_then
    (fn thm =>
      gs[thm,INST_TYPE[“:'a” |-> “:'a eilp”] iSUM_FILTER,nvalue_sem_def,
        rich_listTheory.FILTER_MAP,combinTheory.o_ABS_R,list_set_eq,
        ALL_DISTINCT_union_dom,FILTER_ALL_DISTINCT,ALL_DISTINCT_CARD_LIST_TO_SET])
    (INST_TYPE[“:'b” |-> “:'a eilp”] encode_bitsum_sem)>>
  qabbrev_tac ‘m = FILTER (λv. wb (Nv Xs v)) (union_dom bnd Xs)’>>
  intLib.ARITH_TAC
QED

(* encodes ftable_i ⇒ some X = v and ~fnvalue_v ⇒ no X = v,
   provided that LENGTH Xs = LENGTH Ys *)
Definition encode_tuple_eq_def:
  encode_tuple_eq bnd Xs Ys = [
    bits_imply bnd [Pos (Tb Xs Ys)]
      ([], MAP (λ(X,Y). (1i, Pos (Eq X Y))) (ZIP (Xs,Ys)), &LENGTH Xs);
    bits_imply bnd [Neg (Tb Xs Ys)]
      ([], MAP (λ(X,Y). (-1i, Pos (Eq X Y))) (ZIP (Xs,Ys)), -&LENGTH Xs + 1)]
End

Definition reify_tuple_eq_def:
  reify_tuple_eq bnd Xs Ys =
  let
    ges = FLAT $ MAP (λ(X,Y). encode_ge bnd X Y ++ encode_ge bnd X (Y + 1)) (ZIP (Xs,Ys));
    eqs = FLAT $ MAP (λ(X,Y). encode_eq bnd X Y) (ZIP (Xs,Ys))
  in
    ges ++ eqs ++ encode_tuple_eq bnd Xs Ys
End

Theorem reify_tuple_eq_sem:
  valid_assignment bnd wi ∧
  LENGTH Xs = LENGTH Ys ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb)) (reify_tuple_eq bnd Xs Ys) ⇔
    LIST_REL (λX. λY.
      (wb (Ge X Y) ⇔ wi X ≥ Y) ∧
      (wb (Ge X (Y + 1)) ⇔ wi X ≥ Y + 1) ∧
      (wb (Eq X Y) ⇔ wi X = Y)) Xs Ys ∧
    (wb (Tb Xs Ys) ⇔
      LIST_REL (λX. λY. wi X = Y) Xs Ys))
Proof
  cheat
QED

Definition encode_table_def:
  encode_table bnd Xs Yss =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) Yss
    then
      (FLAT $ MAP (λYs. reify_tuple_eq bnd Xs Ys) Yss) ++
      [([], MAP (λYs. (1i, Pos (Tb Xs Ys))) Yss, 1)]
    else
      [([], [], 1i)]
End

Theorem MAP_LIST_REL:
  MAP f Xs = Ys ⇔ LIST_REL (λx y. f x = y) Xs Ys
Proof
  ‘MAP f Xs = MAP I Ys ⇔ LIST_REL (λx y. f x = I y) Xs Ys’ suffices_by simp[MAP_ID]>>
  DEP_REWRITE_TAC[MAP_EQ_EVERY2]>>
  ho_match_mp_tac $ METIS_PROVE[] “(P ⇒ Q) ⇒ (Q ∧ P ⇔ P)”>>
  metis_tac[EVERY2_LENGTH]
QED

(* assume that Xs are all variables *)
Theorem encode_table_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_table bnd Xs Yss) = (
    table_sem Xs Yss wi ∧
    (∀Ys. MEM Ys Yss ⇒
      LIST_REL (λX. λY.
        (wb (Ge X Y) ⇔ wi X ≥ Y) ∧
        (wb (Ge X (Y + 1)) ⇔ wi X ≥ Y + 1) ∧
        (wb (Eq X Y) ⇔ wi X = Y)) Xs Ys ∧
      (wb (Tb Xs Ys) ⇔
        LIST_REL (λX. λY. wi X = Y) Xs Ys)) ∧
    (∃Ys. MEM Ys Yss ∧ wb (Tb Xs Ys)))
Proof
  rw[encode_table_def,table_sem_def,iconstraint_sem_def,
     eval_ilin_term_def,eval_lin_term_def,iSUM_def]>>
  last_x_assum $ mp_tac>>
  simp[Once EVERY_MEM]>>
  strip_tac>>
  simp[EVERY_FLAT,EVERY_MAP,Once EVERY_MEM,
    MAP_MAP_o,combinTheory.o_ABS_R]>>
  simp[Once $ GSYM combinTheory.o_ABS_R,iSUM_FILTER]>>
  simp[Once integerTheory.INT_GE,intLib.ARITH_PROVE “1i ≤ m ⇔ 0i < m”,
    GSYM integerTheory.INT_LT_LE1,rich_listTheory.LENGTH_NOT_NULL,
    listTheory.NULL_FILTER]>>
  match_mp_tac (METIS_PROVE[]
    “(P ⇔ Q2) ∧ (Q2 ∧ R ⇒ Q1) ⇒ (P ∧ R ⇔ (Q1 ∧ Q2 ∧ R))”)>>
  CONJ_TAC
  >-(
    ho_match_mp_tac FORALL_IMP_EQ>>
    rw[]>>
    res_tac>>
    drule_then (fn thm => simp[thm]) reify_tuple_eq_sem)>>
  rw[]>>
  res_tac>>
  gvs[GSYM MAP_LIST_REL]
QED

(* The top-level encodings *)
Definition encode_cp_one_def:
  encode_cp_one bnd c =
  case c of
    NotEquals X Y => encode_not_equals bnd X Y
  | AllDifferent As => encode_all_different bnd As
  | Element R X As => encode_element bnd R X As
  | Abs X Y => encode_abs bnd X Y
  | Ilc Xs op rhs => encode_ilc Xs op rhs
End

Theorem encode_cp_one_sem_1:
  valid_assignment bnd wi ∧
  constraint_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_eilp wi)) (encode_cp_one bnd c)
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >- (
    simp[encode_not_equals_sem,reify_eilp_def]>>
    gvs[not_equals_sem_def]>>
    intLib.ARITH_TAC)
  >- (
    simp[encode_all_different_sem,reify_eilp_def]>>
    gvs[all_different_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
    rw[]>>
    first_x_assum(qspecl_then[`i`,`j`] mp_tac)>>
    simp[EL_MAP]>>
    intLib.ARITH_TAC)
  >- (
    simp[encode_element_sem,reify_eilp_def]>>
    every_case_tac>>simp[])
  >- (
    simp[encode_abs_sem,reify_eilp_def]>>
    every_case_tac>>simp[])
  >- (
    simp[encode_ilc_sem,reify_eilp_def]>>
    every_case_tac>>simp[])
QED

Theorem encode_cp_one_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_cp_one bnd c) ⇒
  constraint_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >-
    gvs[encode_not_equals_sem]
  >-
    gvs[encode_all_different_sem]
  >-
    gvs[encode_element_sem]
  >-
    gvs[encode_abs_sem]
  >-
    gvs[encode_ilc_sem]
QED

(* An actual implementation will avoid duplicates here *)
Definition encode_cp_all_def:
  encode_cp_all bnd cs =
  FLAT (MAP (encode_cp_one bnd) cs)
End

Theorem encode_cp_all_sem_1:
  valid_assignment bnd wi ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_eilp wi)) (encode_cp_all bnd cs)
Proof
  simp[encode_cp_all_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM]>>
  rw[Once EVERY_MEM,MEM_MAP]>>
  metis_tac[encode_cp_one_sem_1]
QED

Theorem encode_cp_all_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_cp_all bnd cs) ⇒
  EVERY (λc. constraint_sem c wi) cs
Proof
  simp[encode_cp_all_def,EVERY_FLAT]>>
  rw[Once EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  simp[Once EVERY_MEM]>>
  metis_tac[encode_cp_one_sem_2]
QED

(* === Examples ===

not-equals
  EVAL``encode_not_equals (λX. (-10,10)) (INL X) (INL Y)``
  EVAL``encode_not_equals (λX. (-10,10)) (INL X) (INR 4)``

all-different
  EVAL``encode_all_different (λX. (-10,10)) [INL X; INL Y; INL Z; INR 0i]``

element
  EVAL``encode_element (λX. (-10,10)) (INL R) (INL X) [INL A; INL B; INL C; INL D; INL E]``

abs
  EVAL``encode_abs (λX. (-10,10)) (INL X) (INL Y)``

*)
