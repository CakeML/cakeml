(*
  Formalization of the CP to ILP phase
*)
Theory cp_to_ilp
Libs
  preamble
Ancestors
  cp ilp pbc pbc_encode sptree

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

(* The datatype for reified variables in the ILP encoding *)
Datatype:
  reif =
  | Ge 'a int (* Reifies X ≥ i *)
  | Eq 'a int (* Reifies X = i *)
End

(* The datatype for flags in the ILP encoding *)
Datatype:
  flag =
  | Ne ('a + int) ('a + int)  (* Used to force X ≠ Y *)
  | Gem ('a + int) ('a + int) (* Used to force X ≥ Y in Array Max *)
  | Eqc ('a + int) ('a + int) (* Used to force X = Y in Count *)
  | Nv ('a list) int (* Used to force some element in As = v *)
  | Tb ('a list) (int list)
End

Definition reify_reif_def:
  reify_reif wi reif ⇔
  case reif of
    Ge X i => wi X ≥ i
  | Eq X i => wi X = i
End

Definition reify_flag_def:
  reify_flag wi flag ⇔
  case flag of
  | Ne X Y => varc wi X > varc wi Y
  | Gem X Y => varc wi X ≥ varc wi Y
  | Eqc X Y => varc wi X = varc wi Y
  | Tb Xs Ts => MAP wi Xs = Ts
  | Nv Xs v => MEM v $ MAP wi Xs
End

(*
  In this file, we first design and prove sound the
  abstract encodings into the Boolean variable type:
    ('a reif + 'a flag)

  Later on, we will turn the 'a flag into a counter
*)
Type avar = ``:('a reif + 'a flag)``
Type aiconstraint = ``:('a, 'a avar) iconstraint``

Definition reify_avar_def:
  reify_avar wi eb ⇔
  case eb of
    INL reif => reify_reif wi reif
  | INR flag => reify_flag wi flag
End

(***
  Helper encoding functions
***)

(* Encoding a single variable X_{>=i} ⇔ X ≥ i *)
Definition encode_ge_def:
  encode_ge bnd X i =
  (bimply_bits bnd [Pos (INL (Ge X i))] ([(1,X)],[],i))
End

Theorem encode_ge_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (INL (Ge X i)) ⇔ wi X ≥ i)
Proof
  rw[encode_ge_def]>>
  simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def]>>
  metis_tac[]
QED

(* Encoding a single variable X = i
  X_{=i} ⇔ X_{>=i} ∧ ~X_{>=i+1}
*)
Definition encode_eq_def:
  encode_eq bnd X i =
  (bimply_bits bnd [Pos (INL (Eq X i))]
    ([],[(1,Pos(INL (Ge X i)));(1, Neg (INL (Ge X (i+1))))],2))
End

Theorem encode_eq_sem[simp]:
  valid_assignment bnd wi ∧
  (wb (INL (Ge X i)) ⇔ wi X ≥ i) ∧
  (wb (INL (Ge X (i+1))) ⇔ wi X ≥ i+1)
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X i)
  =
  (wb (INL (Eq X i)) ⇔ wi X = i)
Proof
  rw[encode_eq_def]>>
  gs[iconstraint_sem_def,b2i_alt]>>
  rw[]>>
  eq_tac>>rw[]>>
  intLib.ARITH_TAC
QED

(* encodes X ≥ 1,...,X ≥ n *)
Definition encode_ges_def:
  encode_ges bnd X n =
  FLAT (GENLIST (λi. encode_ge bnd X (&(i + 1))) n)
End

Theorem encode_ges_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ges bnd X n) =
  (∀i. 1 ≤ i ∧ i ≤ n ⇒ (wb (INL (Ge X &i)) ⇔ wi X ≥ &i))
Proof
  rw[encode_ges_def,encode_ge_sem,EVERY_FLAT,EVERY_GENLIST]>>
  iff_tac>>rw[]>>
  ‘∃j. i = j + 1’ by intLib.ARITH_TAC>>
  fs[]
QED

(* encodes X = 1,...,X = n *)
Definition encode_eqs_def:
  encode_eqs bnd X n =
  FLAT (GENLIST (λi. encode_eq bnd X (&(i + 1))) n)
End

Triviality FORALL_LT:
  (∀i. i < n ⇒ P (int_of_num (i + 1))) ⇔ (∀i. 1 ≤ i ∧ i ≤ n ⇒ P $ int_of_num i)
Proof
  iff_tac>>
  rw[]>>
  ‘∃j. i = j + 1’ by intLib.ARITH_TAC>>
  fs[]
QED

Triviality FORALL_IMP_EQ = METIS_PROVE []
  ``(∀x. P x ⇒ (Q x ⇔ R x)) ⇒ ((∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x))``;

Theorem encode_eqs_sem[simp]:
  valid_assignment bnd wi ∧
  (∀i. 1 ≤ i ∧ i ≤ n + 1 ⇒ (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eqs bnd X n) =
  ∀i. 1 ≤ i ∧ i ≤ n ⇒ (wb (INL (Eq X &i)) ⇔ wi X = &i)
Proof
  rw[encode_eqs_def,EVERY_FLAT,EVERY_GENLIST,FORALL_LT]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  rw[]>>
  simp[GSYM integerTheory.INT]
QED

(* Encodes a * X + b * Y ≥ c where both X, Y are varc *)
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

Theorem mk_constraint_ge_sem[simp]:
  iconstraint_sem (mk_constraint_ge a X b Y c) (wi,wb) ⇔
  a * (varc wi X) + b * (varc wi Y) ≥ c
Proof
  rw[mk_constraint_ge_def]>>every_case_tac>>
  gvs[varc_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

(* encode the bound 1 ≤ X ≤ n,
  which commonly occurs when X indexes into an array *)
Definition encode_properindex_def:
  encode_properindex bnd n X =
  let
    (lb,ub) = bnd X;
    xlb = if lb < 1 then [([(1i,X)],[],1i)] else [];
    xub = if &n < ub then [([(-1i,X)],[],-&n)] else [];
  in
    xlb ++ xub
End

Theorem encode_properindex_sem[simp]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_properindex bnd n X) =
  (1 ≤ wi X ∧ wi X ≤ &n)
Proof
  rw[encode_properindex_def]>>
  pairarg_tac>>rw[iconstraint_sem_def,eval_ilin_term_def,iSUM_def]>>
  fs[valid_assignment_def]>>
  first_x_assum drule>>gvs[]>>
  intLib.ARITH_TAC
QED

(***
  NotEquals
***)

Definition encode_not_equals_def:
  encode_not_equals bnd X Y =
  [
    bits_imply bnd [Pos (INR (Ne X Y))] (mk_constraint_ge 1 X (-1) Y 1);
    bits_imply bnd [Neg (INR (Ne X Y))] (mk_constraint_ge 1 Y (-1) X 1)
  ]
End

(* Prove together? Or separate? *)
Theorem not_equals_sem_aux:
  (if wb (INR (Ne X Y))
   then varc wi X > varc wi Y
   else varc wi Y > varc wi X) ⇒
  not_equals_sem X Y wi
Proof
  simp[not_equals_sem_def]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Triviality IMP_AND_LEFT:
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
  (if wb (INR (Ne X Y))
   then varc wi X > varc wi Y
   else varc wi Y > varc wi X) ∧
  not_equals_sem X Y wi)
Proof
  strip_tac>>
  simp[MATCH_MP IMP_AND_LEFT not_equals_sem_aux]>>
  simp[encode_not_equals_def]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(***
  AllDifferent
***)

Definition encode_all_different_def:
  encode_all_different bnd As =
  let len = LENGTH As in
  FLAT
  (GENLIST (λi.
    FLAT (GENLIST (λj.
    if i < j
    then encode_not_equals bnd (EL i As) (EL j As)
    else []) len)) len)
End

Theorem all_different_sem_aux:
  (∀i j. i < j ∧ j < LENGTH As ⇒
    let X = EL i As in
    let Y = EL j As in
    if wb (INR (Ne X Y))
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
    if wb (INR (Ne X Y))
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

(***
  Element
***)

(* X_{=i} ⇒ Ai = R where Ai, R can be Varc *)
Definition encode_element_eq_def:
  encode_element_eq bnd R X (i:num,Ai) =
  [
    bits_imply bnd [Pos (INL (Eq X (&(i+1))))] (mk_constraint_ge 1 Ai (-1) R 0);
    bits_imply bnd [Pos (INL (Eq X (&(i+1))))] (mk_constraint_ge 1 R (-1) Ai 0)
  ]
End

Theorem encode_element_eq_sem:
  valid_assignment bnd wi ∧
  (wb (INL (Eq X &(i+1))) ⇔ wi X = &(i+1))
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element_eq bnd R X (i,Ai))
  =
  (wi X = &(i+1) ⇒ varc wi R = varc wi Ai)
Proof
  rw[encode_element_eq_def]>>
  intLib.ARITH_TAC
QED

(* Adds X ≥ 1, - X ≥ -|As| where needed *)
Definition encode_element_var_def:
  encode_element_var (bnd:'a bounds) R X As =
  let
    n = LENGTH As
  in
    encode_ges bnd X (n + 1) ++ encode_eqs bnd X n ++
    encode_properindex bnd n X ++
    FLAT (MAP (encode_element_eq bnd R X) (enumerate 0n As))
End

Triviality numint_le_2:
  (Num X ≤ Y ⇒ X ≤ &Y) ∧ (1 ≤ X ∧ X ≤ &Y ⇒ 1 ≤ Num X ∧ Num X ≤ Y)
Proof
  intLib.ARITH_TAC
QED

Triviality varc_INL:
  varc w (INL x) = w x
Proof
  simp[varc_def]
QED

Theorem encode_element_var_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element_var bnd R X As)
  =
  (
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As + 1 ⇒
    (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As ⇒
    (wb (INL (Eq X &i)) ⇔ wi X = &i)) ∧
  element_sem R (INL X) As wi)
Proof
  rw[encode_element_var_def]>>
  simp[GSYM CONJ_ASSOC]>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  strip_tac>>
  simp[element_sem_def]>>
  simp[EVERY_FLAT,EVERY_MAP,Once EVERY_MEM,MEM_enumerate_iff,PULL_EXISTS,encode_element_eq_sem,varc_INL]>>
  ho_match_mp_tac LEFT_AND_CONG >>
  simp[]>>strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >>
  CONJ_TAC >- intLib.ARITH_TAC>>
  strip_tac>>
  `∃i. wi X = &(i + 1) ∧ i < LENGTH As` by intLib.ARITH_TAC>>
  simp[]
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
  rw[encode_element_const_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_def,mk_constraint_ge_sem,element_sem_def]
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
    (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As ⇒
    (wb (INL (Eq X &i)) ⇔ wi X = &i))) ∧
  element_sem R X As wi)
Proof
  rw[encode_element_def]>>
  TOP_CASE_TAC>>gvs[]
  >- (
    DEP_REWRITE_TAC[encode_element_var_sem]>>
    metis_tac[])
  >>
    metis_tac[encode_element_const_sem]
QED

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem R X As wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (encode_element bnd R X As)
Proof
  rw[encode_element_def]>>
  TOP_CASE_TAC>>gvs[]
  >- (
    DEP_REWRITE_TAC [encode_element_var_sem]>>
    simp[reify_avar_def,reify_reif_def])
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

(***
  Element2D
***)

(* encode_element2d for constant X and variable Y *)
Definition encode_element2d_cv_def:
  encode_element2d_cv bnd R X Y Tss =
  if EVERY (λTs. LENGTH Ts = LENGTH $ HD Tss) Tss ∧
      1 ≤ X ∧ X ≤ &LENGTH Tss
  then encode_element_var bnd R Y $ EL (Num X - 1) Tss
  else [([],[],1)]
End

Theorem encode_element2d_cv_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d_cv bnd R X Y Tss) = (
  (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) + 1 ⇒ (wb (INL (Ge Y (&j))) ⇔ wi Y ≥ &j)) ∧
  (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) ⇒ (wb (INL (Eq Y (&j))) ⇔ wi Y = &j)) ∧
  element2d_sem R (INR X) (INL Y) Tss wi)
Proof
  strip_tac>>
  simp[encode_element2d_cv_def,element2d_sem_def]>>
  reverse IF_CASES_TAC
  >- (
    fs[iconstraint_sem_def,EXISTS_MEM,varc_def]
    >- metis_tac[]>>
    CCONTR_TAC>>fs[]>>
    intLib.ARITH_TAC)>>
  fs[encode_element_var_sem,varc_def,element_sem_def,EVERY_EL]>>
  `∃i. X = &(i + 1) ∧ i < LENGTH Tss` by
    (qpat_x_assum`!n. _` kall_tac>>
    intLib.ARITH_TAC)>>
  simp[]
QED

(* encode_element2d for variable X and constant Y *)
Definition encode_element2d_vc_def:
  encode_element2d_vc bnd R X Y Tss =
  if EVERY (λTs. LENGTH Ts = LENGTH $ HD Tss) Tss ∧ 0 < LENGTH Tss ∧
    1 ≤ Y ∧ Y ≤ &(LENGTH $ HD Tss)
  then encode_element_var bnd R X $ MAP (EL (Num Y - 1)) Tss
  else [([],[],1)]
End

Theorem EL_LIST2D:
  m < LENGTH ls ⇒ EL m (MAP (EL n) ls) = EL n (EL m ls)
Proof
  strip_tac>>
  irule EL_MAP>>
  simp[]
QED

Theorem encode_element2d_vc_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d_vc bnd R X Y Tss) = (
  (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss + 1 ⇒ (wb (INL (Ge X (&i))) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss ⇒ (wb (INL (Eq X (&i))) ⇔ wi X = &i)) ∧
  element2d_sem R (INL X) (INR Y) Tss wi)
Proof
  strip_tac>>
  simp[encode_element2d_vc_def,element2d_sem_def]>>
  reverse IF_CASES_TAC
  >- (
    fs[iconstraint_sem_def,EXISTS_MEM,varc_def]
    >- metis_tac[]>>
    CCONTR_TAC>>fs[]>>
    intLib.ARITH_TAC)>>
  fs[encode_element_var_sem,varc_def,element_sem_def,EVERY_EL]>>
  `∃i. Y = &(i + 1) ∧ i < LENGTH (HD Tss)` by
    (qpat_x_assum`!n. _` kall_tac>>
    intLib.ARITH_TAC)>>
  simp[]>>
  rpt(match_mp_tac LEFT_AND_CONG>>simp[]>>strip_tac)>>
  DEP_REWRITE_TAC[EL_MAP]>>simp[]
QED

(* encode_element2d for constant X and constant Y *)
Definition encode_element2d_cc_def:
  encode_element2d_cc bnd R X Y Tss =
  if EVERY (λTs. LENGTH Ts = LENGTH $ HD Tss) Tss ∧
    1 ≤ X ∧ X ≤ &LENGTH Tss ∧ 1 ≤ Y ∧ Y ≤ &(LENGTH $ HD Tss)
  then [
    mk_constraint_ge 1 (EL (Num Y - 1) $ EL (Num X - 1) Tss) (-1) R 0;
    mk_constraint_ge 1 R (-1) (EL (Num Y - 1) $ EL (Num X - 1) Tss) 0]
  else [([],[],1)]
End

Theorem encode_element2d_cc_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d_cc bnd R X Y Tss) =
  element2d_sem R (INR X) (INR Y) Tss wi
Proof
  rw[encode_element2d_cc_def,element2d_sem_def,varc_def,iconstraint_sem_def]
  >-intLib.ARITH_TAC>>
  metis_tac[numint_le_2,GSYM NOT_EVERY]
QED

Definition encode_element2d_eq_def:
  encode_element2d_eq bnd R X Y (i:num,j:num,Aij) = [
    bits_imply bnd [Pos (INL (Eq X &(i + 1))); Pos (INL (Eq Y &(j + 1)))]
      (mk_constraint_ge 1 Aij (-1) R 0);
    bits_imply bnd [Pos (INL (Eq X &(i + 1)));Pos (INL (Eq Y &(j + 1)))]
      (mk_constraint_ge 1 R (-1) Aij 0)]
End

Theorem encode_element2d_eq_sem:
  valid_assignment bnd wi ∧
  (wb (INL (Eq X &(i + 1))) ⇔ wi X = &(i + 1)) ∧
  (wb (INL (Eq Y &(j + 1))) ⇔ wi Y = &(j + 1)) ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d_eq bnd R X Y (i,j,Aij)) = (
    wi X = &(i + 1) ∧ wi Y = &(j + 1) ⇒ varc wi R = varc wi Aij)
Proof
  rw[encode_element2d_eq_def,iconstraint_sem_def]>>
  intLib.ARITH_TAC
QED

(* encode_element2d for variable X and variable Y *)
Definition encode_element2d_vv_def:
  encode_element2d_vv bnd R X Y Tss =
  let
    n = LENGTH Tss
  in
    if 0 < n ∧ EVERY (λTs. LENGTH Ts = LENGTH $ HD Tss) Tss
    then
      let
        m = LENGTH $ HD Tss;
        mat = enumerate 0 $ MAP (λTs. enumerate 0 Ts) Tss
      in
        encode_ges bnd X (n + 1) ++ encode_ges bnd Y (m + 1) ++
        encode_eqs bnd X n ++ encode_eqs bnd Y m ++
        encode_properindex bnd n X ++ encode_properindex bnd m Y ++
        (FLAT $ MAP (λ(i,vec).
          FLAT $ MAP (λp. encode_element2d_eq bnd R X Y (i,p)) vec) mat)
    else [([],[],1)]
End

Triviality EVERY_enumerate2d:
  0 < LENGTH Tss ∧ EVERY (λTs. LENGTH Ts = LENGTH (HD Tss)) Tss ⇒
  EVERY (λp. EVERY (λq. R (FST p) q) (SND p))
    (enumerate 0 (MAP (λTs. enumerate 0 Ts) Tss)) = (
  ∀i j. i < LENGTH Tss ∧ j < LENGTH (HD Tss) ⇒
    R i (j, EL j $ EL i Tss))
Proof
  strip_tac>>
  simp[EVERY_MEM,MEM_enumerate_iff,EL_MAP,PULL_EXISTS]>>
  fs[EVERY_EL]>>
  metis_tac[]
QED

Theorem encode_element2d_vv_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d_vv bnd R X Y Tss) = (
    (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss + 1 ⇒ (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ∧
    (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) + 1 ⇒ (wb (INL (Ge Y &j)) ⇔ wi Y ≥ &j)) ∧
    (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss ⇒ (wb (INL (Eq X &i)) ⇔ wi X = &i)) ∧
    (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) ⇒ (wb (INL (Eq Y &j)) ⇔ wi Y = &j)) ∧
    element2d_sem R (INL X) (INL Y) Tss wi)
Proof
  reverse $ rw[encode_element2d_vv_def]
  >-
    fs[iconstraint_sem_def,element2d_sem_def]>>
  simp[GSYM CONJ_ASSOC]>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  simp[element2d_sem_def,varc_INL]>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  CONJ_TAC >- intLib.ARITH_TAC>>
  strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>> strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  CONJ_TAC >- intLib.ARITH_TAC>>
  strip_tac>>
  simp[EVERY_FLAT,EVERY_MAP,iterateTheory.LAMBDA_PAIR] >>
  DEP_REWRITE_TAC[EVERY_enumerate2d]>>
  fs[encode_element2d_eq_sem]>>
  `∃i j. wi X = &(i + 1) ∧ i < LENGTH Tss ∧
    wi Y = &(j + 1) ∧ j < LENGTH (HD Tss)` by
    intLib.ARITH_TAC>>
  simp[]
QED

Definition encode_element2d_def:
  encode_element2d bnd R X Y Tss =
  case (X,Y) of
    (INL vX,INL vY) => encode_element2d_vv bnd R vX vY Tss
  | (INL vX,INR cY) => encode_element2d_vc bnd R vX cY Tss
  | (INR cX,INL vY) => encode_element2d_cv bnd R cX vY Tss
  | (INR cX,INR cY) => encode_element2d_cc bnd R cX cY Tss
End

Theorem encode_element2d_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_element2d bnd R X Y Tss) = (
    (case X of INR _ => T | INL X' =>
      (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss + 1 ⇒ (wb (INL (Ge X' (&i))) ⇔ wi X' ≥ &i)) ∧
      (∀i. 1 ≤ i ∧ i ≤ LENGTH Tss ⇒ (wb (INL (Eq X' (&i))) ⇔ wi X' = &i))) ∧
    (case Y of INR _ => T | INL Y' =>
      (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) + 1 ⇒ (wb (INL (Ge Y' (&j))) ⇔ wi Y' ≥ &j)) ∧
      (∀j. 1 ≤ j ∧ j ≤ LENGTH (HD Tss) ⇒ (wb (INL (Eq Y' (&j))) ⇔ wi Y' = &j))) ∧
    element2d_sem R X Y Tss wi)
Proof
  rw[encode_element2d_def]>>
  TOP_CASE_TAC
  >-(
    TOP_CASE_TAC
    >-(
      simp[encode_element2d_vv_sem]>>
      metis_tac[])>>
    simp[encode_element2d_vc_sem]>>
    metis_tac[])
  >-(
    TOP_CASE_TAC
    >-(
      simp[encode_element2d_cv_sem]>>
      metis_tac[])>>
    simp[encode_element2d_cc_sem])
QED

(***
  Abs
***)

(* Encoding for Y a variable *)
Definition encode_abs_var_body_def:
  encode_abs_var_body bnd X Y =
  let vY = INL Y in
  [
    bits_imply bnd [Pos (INL (Ge Y 0))] (mk_constraint_ge 1 X (-1) vY 0);
    bits_imply bnd [Pos (INL (Ge Y 0))] (mk_constraint_ge 1 vY (-1) X 0);
    bits_imply bnd [Neg (INL (Ge Y 0))] (mk_constraint_ge 1 X 1 vY 0);
    bits_imply bnd [Neg (INL (Ge Y 0))] (mk_constraint_ge (-1) X (-1) vY 0);
  ]
End

Definition encode_abs_var_def:
  encode_abs_var bnd X Y =
  encode_ge bnd Y 0 ++
  encode_abs_var_body bnd X Y
End

Theorem encode_abs_var_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs_var bnd X Y)
  =
  (
    (wb (INL (Ge Y 0)) ⇔ wi Y ≥ 0) ∧
    abs_sem X (INL Y) wi
  )
Proof
  rw[encode_abs_var_def,encode_abs_var_body_def]>>
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

Theorem encode_abs_sem:
  valid_assignment bnd wi
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs bnd X Y)
  =
  (
  (case Y of INR _ => T | INL Y =>
  (wb (INL (Ge Y 0)) ⇔ wi Y ≥ 0)) ∧
  abs_sem X Y wi)
Proof
  rw[encode_abs_def]>>
  TOP_CASE_TAC>>gvs[]
  >-
    metis_tac[encode_abs_var_sem]
  >>
    metis_tac[encode_abs_const_sem]
QED

(***
  Ilc
***)

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
  simp[iconstraint_sem_def]>>
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
  rw[]>>
  intLib.ARITH_TAC
QED

(***
  ArrMax
***)

(* Encodes that all As ≥ M *)
Definition encode_Gem_ge_def:
  encode_Gem_ge bnd As M =
  MAP (λA. bits_imply bnd [Pos (INR (Gem A M))] (mk_constraint_ge 1 A (-1) M 0)) As
End

(* iff versions *)
Definition encode_Gem_ge_iff_def:
  encode_Gem_ge_iff bnd As M =
  encode_Gem_ge bnd As M ++
  MAP (λA. bits_imply bnd [Neg (INR (Gem A M))] (mk_constraint_ge 1 M (-1) A 1)) As
End

 (* Encodes that all As ≤ M *)
Definition encode_Gem_le_def:
  encode_Gem_le bnd As M =
  MAP (λA. bits_imply bnd [Pos (INR (Gem M A))] (mk_constraint_ge 1 M (-1) A 0)) As
End

Definition encode_Gem_le_iff_def:
  encode_Gem_le_iff bnd As M =
  encode_Gem_le bnd As M ++
  MAP (λA. bits_imply bnd [Neg (INR (Gem M A))] (mk_constraint_ge 1 A (-1) M 1)) As
End

Theorem encode_Gem_ge_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_ge bnd As M) =
    (∀A. MEM A As ∧ wb (INR (Gem A M)) ⇒ varc wi A ≥ varc wi M)
Proof
  rw[encode_Gem_ge_def]>>
  simp[EVERY_MAP,EVERY_MEM,AND_IMP_INTRO]>>
  ho_match_mp_tac FORALL_IMP_EQ >>rw[]>>
  intLib.ARITH_TAC
QED

Theorem encode_Gem_le_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_le bnd As M) =
    (∀A. MEM A As ∧ wb (INR (Gem M A)) ⇒ varc wi A ≤ varc wi M)
Proof
  rw[encode_Gem_le_def]>>
  simp[EVERY_MAP,EVERY_MEM,AND_IMP_INTRO]>>
  ho_match_mp_tac FORALL_IMP_EQ >>rw[]>>
  intLib.ARITH_TAC
QED

Theorem encode_Gem_ge_iff_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_ge_iff bnd As M) =
    (∀A. MEM A As ⇒ (wb (INR (Gem A M)) ⇔ varc wi A ≥ varc wi M))
Proof
  rw[encode_Gem_ge_iff_def,encode_Gem_ge_sem]>>
  simp[EVERY_MAP,EVERY_MEM,AND_IMP_INTRO]>>
  simp[intLib.ARITH_PROVE ``X + -1 * (Y:int) ≥ 1 ⇔ ¬ (Y ≥ X)``]>>
  metis_tac[]
QED

Theorem encode_Gem_le_iff_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_Gem_le_iff bnd As M) =
    (∀A. MEM A As ⇒ (wb (INR (Gem M A)) ⇔ varc wi A ≤ varc wi M))
Proof
  rw[encode_Gem_le_iff_def,encode_Gem_le_sem]>>
  simp[EVERY_MAP,EVERY_MEM,AND_IMP_INTRO]>>
  simp[intLib.ARITH_PROVE ``X + -1 * (Y:int) ≥ 1 ⇔ ¬ (X <= Y)``]>>
  metis_tac[]
QED

Definition encode_arr_max_def:
  encode_arr_max bnd M As =
  ([], MAP (λA. (1, Pos (INR (Gem A M)))) As, 1) ::
  encode_Gem_ge bnd As M ++
  MAP (λA. mk_constraint_ge 1 M (-1) A 0) As
End

Theorem encode_arr_max_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_arr_max bnd M As) = (
    (∃A. MEM A As ∧ wb (INR (Gem A M))) ∧
    (∀A. MEM A As ∧ wb (INR (Gem A M)) ⇒ varc wi A ≥ varc wi M) ∧
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

(***
  ArrMin
***)

Definition encode_arr_min_def:
  encode_arr_min bnd M As =
  ([], MAP (λA. (1, Pos (INR (Gem M A)))) As, 1) ::
  encode_Gem_le bnd As M ++
  MAP (λA. mk_constraint_ge 1 A (-1) M 0) As
End

Theorem encode_arr_min_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_arr_min bnd M As) = (
    (∃A. MEM A As ∧ wb (INR (Gem M A))) ∧
    (∀A. MEM A As ∧ wb (INR (Gem M A)) ⇒ varc wi A ≤ varc wi M) ∧
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

(***
  Count
***)

Definition encode_count_def:
  encode_count bnd Y C As =
  let
    ilpc =
    case C of
      INL vC => [
        ([(-1, vC)], MAP (λA. (1, Pos (INR (Eqc A Y)))) As, 0);
        ([(1, vC)], MAP (λA. (-1, Pos (INR (Eqc A Y)))) As, 0)]
    | INR cC => [
        ([], MAP (λA. (1, Pos (INR (Eqc A Y)))) As, cC);
        ([], MAP (λA. (-1, Pos (INR (Eqc A Y)))) As, -cC)]
  in
    encode_Gem_ge_iff bnd As Y ++
    encode_Gem_le_iff bnd As Y ++
    MAP (λA. bits_imply bnd [Pos (INR (Eqc A Y))]
                        ([], [(1, Pos (INR (Gem A Y))); (1, Pos (INR (Gem Y A)))], 2)) As ++
    MAP (λA. bits_imply bnd [Neg (INR (Eqc A Y))]
                        ([], [(1, Neg (INR (Gem A Y))); (1, Neg (INR (Gem Y A)))], 1)) As ++
    ilpc
End

Theorem encode_count_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_count bnd Y C As) = (
    EVERY (λA. wb (INR (Gem A Y)) ⇔ varc wi A ≥ varc wi Y) As ∧
    EVERY (λA. wb (INR (Gem Y A)) ⇔ varc wi Y ≥ varc wi A) As ∧
    EVERY (λA. wb (INR (Eqc A Y)) ⇔ varc wi A = varc wi Y) As ∧
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
    fs[EVERY_MAP,EVERY_MEM,iconstraint_sem_def]>>
    metis_tac[integerTheory.INT_LE_ANTISYM,integerTheory.INT_GE])>>
  strip_tac
  >- (
    Cases_on ‘C’>>
    simp[count_sem_def]>>
    rw[METIS_PROVE[] “∀P a b. (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b”]>>
    simp[iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
      MAP_MAP_o,combinTheory.o_ABS_R,b2i_alt,iSUM_def,Once varc_def]>>
    ‘iSUM (MAP (λA. if wb (INR (Eqc A Y)) then 1 else 0) As) =
     iSUM (MAP (λA. if varc wi A = varc wi Y then 1 else 0) As)’ by
      fs[EVERY_MEM,Cong MAP_CONG]>>
    simp[iSUM_MAP_lin_const]>>
    intLib.ARITH_TAC)
QED

(***
  NValue
***)

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

(* encodes fnvalue_v ⇔ some X = v *)
Definition encode_some_eq_def:
  encode_some_eq bnd Xs (v: int) =
    bimply_bits bnd [Pos (INR (Nv Xs v))]
      ([], MAP (λA. (1i, Pos (INL (Eq A v)))) Xs, 1i)
End

Theorem encode_some_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λX. wb (INL (Eq X v)) ⇔ wi X = v) Xs ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_some_eq bnd Xs v) =
  (wb (INR (Nv Xs v)) ⇔ ∃A. MEM A Xs ∧ wb (INL (Eq A v))))
Proof
  rw[encode_some_eq_def,iconstraint_sem_def,eval_lin_term_ge_1]>>
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

Theorem reify_some_eq_sem:
  valid_assignment bnd wi ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP (reify_some_eq bnd Xs)
    (union_dom bnd Xs))) ⇔
  ∀v. MEM v (union_dom bnd Xs) ⇒
      EVERY (λX. wb (INL (Ge X v)) ⇔ wi X ≥ v) Xs ∧
      EVERY (λX. wb (INL (Ge X (v + 1))) ⇔ wi X ≥ v + 1) Xs ∧
      EVERY (λX. wb (INL (Eq X v)) ⇔ wi X = v) Xs ∧
      (wb (INR (Nv Xs v)) ⇔ ∃A. MEM A Xs ∧ wb (INL (Eq A v))))
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
    EVERY (λX. wb (INL (Eq X v)) ⇔ wi X = v) Xs ∧
    (wb (INR (Nv Xs v)) ⇔ ∃A. MEM A Xs ∧ wb (INL (Eq A v)))) ⇒
  ∀v. MEM v (MAP wi Xs) ⇔ MEM v (FILTER (λv. wb (INR (Nv Xs v))) (union_dom bnd Xs))
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
    encode_bitsum (MAP (λv. INR (Nv Xs v)) vals) Y
End

Theorem encode_nvalue_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_nvalue bnd Y Xs) = (
    nvalue_sem Y Xs wi ∧
    ∀v. MEM v (union_dom bnd Xs) ⇒
        EVERY (λX. wb (INL (Ge X v)) ⇔ wi X ≥ v) Xs ∧
        EVERY (λX. wb (INL (Ge X (v + 1))) ⇔ wi X ≥ v + 1) Xs ∧
        EVERY (λX. wb (INL (Eq X v)) ⇔ wi X = v) Xs ∧
        (wb (INR (Nv Xs v)) ⇔ ∃A. MEM A Xs ∧ wb (INL (Eq A v))))
Proof
  rw[encode_nvalue_def,Once CONJ_COMM]>>
  match_mp_tac $ METIS_PROVE[] “(Q ⇔ Q') ∧ (Q' ⇒ (P ⇔ P')) ⇒ (P ∧ Q ⇔ P' ∧ Q')”>>
  CONJ_TAC>>
  simp[reify_some_eq_sem]>>
  strip_tac>>
  ‘∀v. MEM v (union_dom bnd Xs) ⇒
    EVERY (λX. wb (INL (Eq X v)) ⇔ wi X = v) Xs ∧
    (wb (INR (Nv Xs v)) ⇔ ∃A. MEM A Xs ∧ wb (INL (Eq A v)))’ by metis_tac[]>>
  drule_all_then assume_tac encode_nvalue_sem_aux>>
  DEP_REWRITE_TAC[encode_bitsum_sem]>>
  gs[nvalue_sem_def,iSUM_FILTER,FILTER_MAP,o_DEF,list_set_eq,
     ALL_DISTINCT_union_dom,FILTER_ALL_DISTINCT,ALL_DISTINCT_CARD_LIST_TO_SET]>>
  intLib.ARITH_TAC
QED

(***
  Table
***)

(* encodes ftable_i ⇔ X = Ti, provided that LENGTH X = LENGTH Ti *)
Definition encode_tuple_eq_def:
  encode_tuple_eq bnd Xs Ys =
    bimply_bits bnd [Pos (INR (Tb Xs Ys))]
      ([], MAP2 (λX Y. (1i, Pos (INL (Eq X Y)))) Xs Ys, &LENGTH Xs)
End

Definition reify_tuple_eq_def:
  reify_tuple_eq bnd Xs Ys =
  let
    ges = FLAT $ MAP2 (λX Y. encode_ge bnd X Y ++ encode_ge bnd X (Y + 1)) Xs Ys;
    eqs = FLAT $ MAP2 (λX Y. encode_eq bnd X Y) Xs Ys
  in
    ges ++ eqs ++ encode_tuple_eq bnd Xs Ys
End

Theorem LENGTH_FILTER_GE:
  LENGTH ls ≤ LENGTH (FILTER P ls) ⇔ LENGTH ls = LENGTH (FILTER P ls)
Proof
  metis_tac[GREATER_EQ,LE_ANTISYM,LENGTH_FILTER_LEQ]
QED

Theorem LENGTH_FILTER_EQ:
  LENGTH ls = LENGTH (FILTER P ls) ⇔ EVERY P ls
Proof
  Induct_on ‘ls’>>
  rw[FILTER,ADD1]>>
  irule $ intLib.ARITH_PROVE “(a:num) > b ⇒ a ≠ b”>>
  simp[GREATER_DEF,GSYM LE_LT1,LENGTH_FILTER_LEQ,LENGTH_FILTER_LEQ]
QED

Triviality reify_tuple_eq_aux:
  valid_assignment bnd wi ⇒ (
  LIST_REL (λX Y.
    (wb (INL (Ge X Y)) ⇔ wi X ≥ Y) ∧
    (wb (INL (Ge X (Y + 1))) ⇔ wi X ≥ Y + 1) ∧
    EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X Y)) Xs Ys ⇔
  LIST_REL (λX Y.
    (wb (INL (Ge X Y)) ⇔ wi X ≥ Y) ∧
    (wb (INL (Ge X (Y + 1))) ⇔ wi X ≥ Y + 1) ∧
    (wb (INL (Eq X Y)) ⇔ wi X = Y)) Xs Ys)
Proof
  strip_tac>>
  simp[LIST_REL_EVERY_ZIP,Once EVERY_MEM,Once EQ_SYM_EQ]>>
  simp[Once EVERY_MEM]>>
  ho_match_mp_tac $ METIS_PROVE[]
    “(∀x. Q x ⇒ (R1 x ⇔ R2 x)) ⇒ ((P ∧ ∀x. Q x ⇒ R1 x) ⇔ (P ∧ ∀x. Q x ⇒ R2 x))”>>
  rw[]>>
  pairarg_tac>>
  simp[BETA_THM]>>
  METIS_TAC[encode_eq_sem]
QED

Triviality iff_lem:
  ((R ⇔ P) ⇔ (R ⇔ Q)) ⇔ (P ⇔ Q)
Proof
  metis_tac[]
QED

Theorem encode_tuple_eq_sem:
  valid_assignment bnd wi ∧
  LENGTH Xs = LENGTH Ys ∧
  LIST_REL (λX Y. wb (INL (Eq X Y)) ⇔ wi X = Y) Xs Ys
  ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_tuple_eq bnd Xs Ys) ⇔
  (wb (INR (Tb Xs Ys)) ⇔ LIST_REL (λX Y. wi X = Y) Xs Ys))
Proof
  rw[encode_tuple_eq_def,iconstraint_sem_def]>>
  simp[MAP2_ZIP,EQ_SYM_EQ,iff_lem,eval_lin_term_def,
    MAP_MAP_o,iterateTheory.LAMBDA_PAIR,
    combinTheory.o_ABS_R,iSUM_FILTER]>>
  fs[Once $ GSYM combinTheory.o_ABS_R,iSUM_FILTER,LIST_REL_EVERY_ZIP]>>
  drule_then assume_tac $ cj 2 LENGTH_ZIP>>
  pop_assum (fn thm =>
    pure_rewrite_tac[
      GSYM thm,intReduceTheory.INT_GE_CONV_pth,
      LENGTH_FILTER_GE,LENGTH_FILTER_EQ])>>
  fs[EVERY_MEM]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  fs[EQ_SYM_EQ,iterateTheory.LAMBDA_PAIR]
QED

Theorem reify_tuple_eq_sem:
  valid_assignment bnd wi ∧
  LENGTH Xs = LENGTH Ys ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb))
    (reify_tuple_eq bnd Xs Ys) ⇔
    LIST_REL (λX Y.
      (wb (INL (Ge X Y)) ⇔ wi X ≥ Y) ∧
      (wb (INL (Ge X (Y + 1))) ⇔ wi X ≥ Y + 1) ∧
      (wb (INL (Eq X Y)) ⇔ wi X = Y)) Xs Ys ∧
    (wb (INR (Tb Xs Ys)) ⇔
      LIST_REL (λX Y. wi X = Y) Xs Ys))
Proof
  simp[LIST_REL_CONJ]>>
  rw[reify_tuple_eq_def,EVERY_FLAT]>>
  simp[GSYM CONJ_ASSOC]>>
  simp[Once CONJ_ASSOC, SimpRHS]>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  CONJ_TAC
  >- (
    simp[Once EVERY_MEM]>>
    simp[LIST_REL_EVERY_ZIP,EVERY_MEM,SimpRHS]>>
    simp[MAP2_ZIP,MEM_MAP,PULL_EXISTS,MEM_ZIP]>>
    metis_tac[])>>
  strip_tac>>
  ho_match_mp_tac LEFT_AND_CONG >> simp[]>>
  CONJ_TAC
  >- (
    simp[Once EVERY_MEM]>>
    simp[LIST_REL_EVERY_ZIP,EVERY_MEM,SimpRHS]>>
    simp[MAP2_ZIP,MEM_MAP,PULL_EXISTS,MEM_ZIP]>>
    ho_match_mp_tac FORALL_IMP_EQ>>
    rw[]>>
    DEP_REWRITE_TAC[encode_eq_sem]>>simp[]>>
    gvs[LIST_REL_EL_EQN])>>
  strip_tac>>
  metis_tac[encode_tuple_eq_sem]
QED

Definition encode_table_def:
  encode_table bnd Xs Yss =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) Yss
    then
      (FLAT $ MAP (λYs. reify_tuple_eq bnd Xs Ys) Yss) ++
      [([], MAP (λYs. (1i, Pos (INR (Tb Xs Ys)))) Yss, 1)]
    else
      [([], [], 1i)]
End

Theorem MAP_LIST_REL:
  MAP f Xs = Ys ⇔ LIST_REL (λx y. f x = y) Xs Ys
Proof
  ‘MAP f Xs = MAP I Ys ⇔ LIST_REL (λx y. f x = I y) Xs Ys’ suffices_by simp[MAP_ID]>>
  metis_tac[MAP_EQ_EVERY2,EVERY2_LENGTH]
QED

(* assume that Xs are all variables *)
Theorem encode_table_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_table bnd Xs Yss) = (
    table_sem Xs Yss wi ∧
    (∀Ys. MEM Ys Yss ⇒
      LIST_REL (λX Y.
        (wb (INL (Ge X Y)) ⇔ wi X ≥ Y) ∧
        (wb (INL (Ge X (Y + 1))) ⇔ wi X ≥ Y + 1) ∧
        (wb (INL (Eq X Y)) ⇔ wi X = Y)) Xs Ys ∧
      (wb (INR (Tb Xs Ys)) ⇔
        LIST_REL (λX Y. wi X = Y) Xs Ys)) ∧
    (∃Ys. MEM Ys Yss ∧ wb (INR (Tb Xs Ys))))
Proof
  rw[encode_table_def,table_sem_def,iconstraint_sem_def,
    eval_ilin_term_def,eval_lin_term_def,iSUM_def]>>
  last_x_assum $ mp_tac>>
  simp[Once EVERY_MEM,EVERY_FLAT,EVERY_MAP,Once EVERY_MEM,MAP_MAP_o,
    combinTheory.o_ABS_R]>>
  rw[Once $ GSYM combinTheory.o_ABS_R,iSUM_FILTER,Once integerTheory.INT_GE,
    intLib.ARITH_PROVE “1i ≤ m ⇔ 0i < m”,LENGTH_NOT_NULL,NULL_FILTER]>>
  ho_match_mp_tac (METIS_PROVE[]
    “(∀x. P1 x ⇒ (Q1 x ⇔ Q2 x)) ∧
    ((∀x. P1 x ⇒ Q2 x) ∧ R ⇒ P2) ⇒
    ((∀x. P1 x ⇒ Q1 x) ∧ R ⇔ (P2 ∧ (∀x. P1 x ⇒ Q2 x) ∧ R))”)>>
  CONJ_TAC>>
  rw[]>>
  gvs[reify_tuple_eq_sem,GSYM MAP_LIST_REL]
QED

(* The top-level encodings *)
Definition encode_cp_one_def:
  encode_cp_one bnd c =
  case c of
    NotEquals X Y => encode_not_equals bnd X Y
  | AllDifferent As => encode_all_different bnd As
  | Element R X As => encode_element bnd R X As
  | Element2D R X Y Tss => encode_element2d bnd R X Y Tss
  | Abs X Y => encode_abs bnd X Y
  | Ilc Xs op rhs => encode_ilc Xs op rhs
  | ArrMax M As => encode_arr_max bnd M As
  | ArrMin M As => encode_arr_min bnd M As
  | Count Y C As => encode_count bnd Y C As
  | Nvalue Y Xs => encode_nvalue bnd Y Xs
  | Table Xs Yss => encode_table bnd Xs Yss
End

Theorem encode_cp_one_sem_1:
  valid_assignment bnd wi ∧
  constraint_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (encode_cp_one bnd c)
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >- (
    simp[encode_not_equals_sem,reify_avar_def,reify_flag_def]>>
    gvs[not_equals_sem_def]>>
    intLib.ARITH_TAC)
  >- (
    simp[encode_all_different_sem,reify_avar_def,reify_flag_def]>>
    gvs[all_different_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
    rw[]>>
    first_x_assum(qspecl_then[`i`,`j`] mp_tac)>>
    simp[EL_MAP]>>
    intLib.ARITH_TAC)
  >- (
    simp[encode_element_sem,reify_avar_def,reify_flag_def,reify_reif_def]>>
    every_case_tac>>simp[])
  >- (
    simp[encode_element2d_sem,reify_avar_def,reify_reif_def]>>
    every_case_tac)
  >- (
    simp[encode_abs_sem,reify_avar_def,reify_reif_def]>>
    every_case_tac>>simp[])
  >- (
    simp[encode_ilc_sem,reify_avar_def]>>
    every_case_tac>>simp[])
  >- (
    fs[encode_arr_max_sem,reify_avar_def,reify_flag_def,arr_max_sem_def]>>
    fs[MEM_MAP]>>
    goal_assum $ drule_at Any>>
    simp[integerTheory.int_ge,integerTheory.INT_LE_REFL])
  >- (
    fs[encode_arr_min_sem,reify_avar_def,reify_flag_def,arr_min_sem_def]>>
    fs[MEM_MAP,integerTheory.int_ge]>>
    goal_assum $ drule_at Any>>
    simp[integerTheory.int_ge,integerTheory.INT_LE_REFL])
  >-simp[encode_count_sem,reify_avar_def,reify_flag_def]
  >- (
    fs[encode_nvalue_sem,reify_avar_def,nvalue_sem_def,MEM_MAP,reify_reif_def,reify_flag_def]>>
    metis_tac[])
  >- (
    fs[encode_table_sem,reify_avar_def,table_sem_def,reify_reif_def,reify_flag_def]>>
    rw[LIST_REL_EL_EQN,EVERY_MEM]>>
    fs[MAP_LIST_REL,EVERY_MEM,LIST_REL_EL_EQN])
QED

Theorem encode_cp_one_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_cp_one bnd c) ⇒
  constraint_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >-gvs[encode_not_equals_sem]
  >-gvs[encode_all_different_sem]
  >-gvs[encode_element_sem]
  >-gvs[encode_element2d_sem]
  >-gvs[encode_abs_sem]
  >-gvs[encode_ilc_sem]
  >-gvs[encode_arr_max_sem]
  >-gvs[encode_arr_min_sem]
  >-gvs[encode_count_sem]
  >-gvs[encode_nvalue_sem]
  >-gvs[encode_table_sem]
QED

(* An actual implementation will avoid duplicates here *)
Definition encode_cp_all_def:
  encode_cp_all bnd cs =
  FLAT (MAP (encode_cp_one bnd) cs)
End

Theorem encode_cp_all_sem_1:
  valid_assignment bnd wi ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (encode_cp_all bnd cs)
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
