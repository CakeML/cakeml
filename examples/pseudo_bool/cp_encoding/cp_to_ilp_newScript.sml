(*
  Formalization of the CP to ILP phase
*)
open preamble cpTheory ilpTheory pbcTheory pbc_encodeTheory;

val _ = new_theory "cp_to_ilp_new";

(* The datatype for reified variables in the ILP encoding *)
Datatype:
  reif =
  | Ge 'a int (* Reifies X ≥ i *)
  | Eq 'a int (* Reifies X = i *)
End

(* The datatype for flags in the ILP encoding *)
Datatype:
  flag =
  | Gt ('a + int) ('a + int)  (* Used to force in X ≠ Y *)
  | Gem ('a + int) ('a + int) (* Used to force X ≥ Y in Array Max *)
  | Eqc ('a + int) ('a + int) (* Used to force X = Y in Count *)
  | Nv (('a + int) list) int (* Used to force some element in As = v *)
  | Tb (('a + int) list) (('a + int) list) int
End

Definition reify_reif_def:
  reify_reif wi eb ⇔
  case eb of
    Ge X i => wi X ≥ i
  | Eq X i => wi X = i
End

Definition reify_flag_def:
  reify_flag wi eb ⇔
  case eb of
    Gt X Y => varc wi X > varc wi Y
End

Definition reify_def:
  reify wi e ⇔
  case e of
    INL eb => reify_reif wi eb
  | INR (n,eb) => reify_flag wi eb
End

val eval_raw = LIST_CONJ
  [iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_def];

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
  bimply_bits bnd [Pos (INL (Ge X i))] ([(1,X)],[],i)
End

Theorem encode_ge_sem:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_ge bnd X i)
  =
  (wb (INL (Ge X i)) ⇔ wi X ≥ i)
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
  bimply_bits bnd [Pos (INL (Eq X i))]
    ([],[(1,Pos(INL (Ge X i)));(1, Neg (INL (Ge X (i+1))))],2)
End

Theorem encode_eq_sem:
  valid_assignment bnd wi ∧
  (wb (INL (Ge X i)) ⇔ wi X ≥ i) ∧
  (wb (INL (Ge X (i+1))) ⇔ wi X ≥ i+1)
  ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_eq bnd X i)
  =
  (wb (INL (Eq X i)) ⇔ wi X = i)
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

Definition forget_b_ilp_def:
  forget_b_ilp
    ((is,bs,c):
      ('a, 'a reif + (num # 'a flag)) iconstraint ) =
    (is,MAP (λ(a,b). (a, map_lit (SUM_MAP I FST) b)) bs, c):
      ('a, 'a reif + num) iconstraint
End

Definition forget_b_ilps_def[simp]:
  forget_b_ilps ilps = MAP forget_b_ilp ilps
End

Definition vars_b_ilp_def:
  vars_b_ilp (is,bs,c) =
    set (MAP (lit_var o SND) bs)
End

Definition vars_b_ilps_def[simp]:
  vars_b_ilps ilps =
  BIGUNION (IMAGE vars_b_ilp (set ilps))
End

Definition inj_vars_b_ilps_def:
  inj_vars_b_ilps (ilps : ('a, 'a reif + (num # 'a flag)) iconstraint list) ⇔
  ∀i l l'.
    INR (i,l) ∈ vars_b_ilps ilps ∧
    INR (i,l') ∈ vars_b_ilps ilps ⇒
    l = l'
End

Definition bound_vars_b_ilps_def:
  bound_vars_b_ilps n n' ilps ⇔
  n ≤ n' ∧
  ∀i l.
    INR (i,l) ∈ vars_b_ilps ilps ⇒
    (n:num) ≤ i ∧ i < n'
End

Definition good_b_ilps_def:
  good_b_ilps n n' ilps ⇔
  bound_vars_b_ilps n n' ilps ∧
  inj_vars_b_ilps ilps
End

Theorem good_b_ilps_emp[simp]:
  good_b_ilps n n []
Proof
  rw[good_b_ilps_def,inj_vars_b_ilps_def,bound_vars_b_ilps_def]
QED

Theorem forget_b_ilps_inj_vars_b_ilps_1:
  inj_vars_b_ilps ilps ∧
  (∀i l l'.
    wb (INR (i,l)) = wb (INR (i,l'))) ⇒
  EVERY (λx. iconstraint_sem x (wi,wb)) ilps ⇒
  EVERY (λx. iconstraint_sem x (wi,
      (wb o SUM_MAP I (λb. (b, ARB))))) (forget_b_ilps ilps)
Proof
  cheat
QED

Theorem forget_b_ilps_inj_vars_b_ilps_2:
  inj_vars_b_ilps ilps ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (forget_b_ilps ilps) ⇒
  EVERY (λx. iconstraint_sem x (wi, wb o SUM_MAP I FST)) ilps
Proof
  cheat
QED

Definition select_wb_def:
  select_wb (wb:('a reif + (num # 'a flag) -> bool))
    ilps =
    (let vs = vars_b_ilps ilps in
    wb o SUM_MAP I (λ(i,l). (i, @l. INR (i,l) ∈ vs))) :
      ('a reif + (num # 'a flag) -> bool)
End

Theorem inj_vars_b_ilps_fix:
  inj_vars_b_ilps ilps ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) ilps ⇒
  EVERY (λx. iconstraint_sem x (wi,
    select_wb wb ilps)) ilps
Proof
  cheat
QED

Theorem bound_vars_b_ilps_append:
  bound_vars_b_ilps n1 n1' ilps1 ∧
  bound_vars_b_ilps n2 n2' ilps2 ∧
  n1' ≤ n2 ⇒
  bound_vars_b_ilps n1 n2' (ilps1 ++ ilps2)
Proof
  rw[]>>
  fs[bound_vars_b_ilps_def,PULL_EXISTS]>>rw[]>>
  rpt(first_x_assum drule>>fs[])
QED

Theorem good_b_ilps_append:
  good_b_ilps n1 n1' ilps1 ∧
  good_b_ilps n2 n2' ilps2 ∧
  n1' ≤ n2 ⇒
  good_b_ilps n1 n2' (ilps1 ++ ilps2)
Proof
  rw[good_b_ilps_def]
  >- metis_tac[bound_vars_b_ilps_append]>>
  fs[inj_vars_b_ilps_def,PULL_EXISTS]>>rw[]
  >- metis_tac[]
  >- (
    fs[bound_vars_b_ilps_def,PULL_EXISTS]>>
    rpt (first_x_assum drule_all)>>
    simp[])
  >- (
    fs[bound_vars_b_ilps_def,PULL_EXISTS]>>
    rpt (first_x_assum drule_all)>>
    simp[])
  >- metis_tac[]
QED

Theorem map_lit_negate:
  map_lit f (negate l) =
  negate (map_lit f l)
Proof
  Cases_on`l`>>rw[negate_def,map_lit_def]
QED

Theorem min_lin_term_MAP_map_lit[simp]:
  min_lin_term
    (MAP (λ(a,b). (a,map_lit f b)) cc1) =
  min_lin_term cc1
Proof
  rw[min_lin_term_def,MAP_MAP_o,o_DEF,LAMBDA_PROD]
QED

Theorem forget_b_ilp_bits_imply[simp]:
  forget_b_ilp (bits_imply bnd xs cc) =
  bits_imply bnd (MAP (map_lit (SUM_MAP I FST)) xs)
    (forget_b_ilp cc)
Proof
  PairCases_on`cc`>>
  rw[bits_imply_def,forget_b_ilp_def]>>
  simp[MAP_MAP_o,o_DEF,map_lit_negate]
QED

Theorem forget_b_ilp_mk_constraint_ge[simp]:
  forget_b_ilp (mk_constraint_ge a X b Y c) =
  mk_constraint_ge a X b Y c
Proof
  rw[mk_constraint_ge_def]>>
  every_case_tac>>fs[forget_b_ilp_def]
QED

Definition mk_fresh_def:
  mk_fresh (n:num) rhs =
    (n+1, INR (n, rhs:'a flag))
End

Theorem PAIR_MAP_o[simp]:
  (f1 ## g1) ((f2 ## g2) p) =
  (f1 o f2 ## g1 o g2) p
Proof
  rw[PAIR_MAP]
QED

Theorem lit_var_negate[simp]:
  lit_var (negate x) = lit_var x
Proof
  Cases_on`x`>>rw[]
QED

Theorem vars_b_ilp_bits_imply[simp]:
  vars_b_ilp (bits_imply bnd xs cc) =
  set (MAP lit_var xs) ∪ vars_b_ilp cc
Proof
  PairCases_on`cc`>>
  rw[bits_imply_def,vars_b_ilp_def,MAP_MAP_o,o_DEF,SF ETA_ss]
QED

Theorem vars_b_ilp_mk_constraint_ge[simp]:
  vars_b_ilp (mk_constraint_ge a X b Y c) = {}
Proof
  rw[mk_constraint_ge_def]>>
  every_case_tac>>fs[vars_b_ilp_def]
QED

(*** not_equals ***)
Definition encode_not_equals_def:
  encode_not_equals bnd n X Y =
  (I ##
    (λv.
    [
    bits_imply bnd [Pos v] (mk_constraint_ge 1 X (-1) Y 1);
    bits_imply bnd [Neg v] (mk_constraint_ge 1 Y (-1) X 1)
    ]))
  (mk_fresh n (Gt X Y))
End

Definition cencode_not_equals_def:
  cencode_not_equals bnd n X Y =
  (I ## forget_b_ilps) (encode_not_equals bnd n X Y)
End

Theorem cencode_not_equals_compute =
  SRULE [encode_not_equals_def,mk_fresh_def] cencode_not_equals_def;

Theorem encode_not_equals_sem_1:
  valid_assignment bnd wi ∧
  not_equals_sem X Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi))
    (SND (encode_not_equals bnd n X Y))
Proof
  rw[mk_fresh_def,not_equals_sem_def,encode_not_equals_def,bits_imply_sem,mk_constraint_ge_sem,reify_def,reify_flag_def]>>
  intLib.ARITH_TAC
QED

Theorem encode_not_equals_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (SND (encode_not_equals bnd n X Y)) ⇒
  not_equals_sem X Y wi
Proof
  rw[encode_not_equals_def,not_equals_sem_def]>>
  rfs[bits_imply_sem,mk_constraint_ge_sem]>>
  rename1`wb f`>>
  Cases_on`wb f` >> fs[]>>
  intLib.ARITH_TAC
QED

Theorem encode_not_equals_good_b_ilps:
  encode_not_equals bnd n X Y = (n', ilps) ⇒
  good_b_ilps n n' ilps
Proof
  rw[encode_not_equals_def]>>
  simp[good_b_ilps_def,inj_vars_b_ilps_def,bound_vars_b_ilps_def,vars_b_ilps_def]>>
  gvs[mk_fresh_def]
QED

(*** all_different ***)

(* Step 0: define the abstract encoding *)
Definition encode_all_different_row_def:
  (encode_all_different_row bnd n A [] = (n,[])) ∧
  (encode_all_different_row bnd n A (B::Bs) =
    let (n',B') = encode_not_equals bnd n A B in
    let (n'',Bs') = encode_all_different_row bnd n' A Bs in
      (n'',B' ++ Bs'))
End

Definition encode_all_different_def:
  (encode_all_different bnd n [] = (n,[])) ∧
  (encode_all_different bnd n (A::As) =
    let (n',A') = encode_all_different_row bnd n A As in
    let (n'',As') = encode_all_different bnd n' As in
    (n'',A' ++ As'))
End

Definition all_different_row_sem_def:
  all_different_row_sem w A As ⇔
   ¬ MEM (varc w A) (MAP (varc w) As)
End

(* Step 1: prove the sem_1 and sem_2 theorems *)
Theorem encode_all_different_row_sem_1:
  valid_assignment bnd wi ∧
  all_different_row_sem wi A As ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi))
    (SND (encode_all_different_row bnd n A As))
Proof
  qid_spec_tac`n`>>
  Induct_on`As`>>rw[encode_all_different_row_def]>>
  fs[all_different_row_sem_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_not_equals_sem_1,SND,not_equals_sem_def]
QED

Theorem encode_all_different_row_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (SND (encode_all_different_row bnd n A As)) ⇒
  all_different_row_sem wi A As
Proof
  qid_spec_tac`n`>>
  Induct_on`As`>>rw[encode_all_different_row_def]>>
  fs[all_different_row_sem_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_not_equals_sem_2,SND,not_equals_sem_def]
QED

Theorem encode_all_different_sem_1:
  valid_assignment bnd wi ∧
  all_different_sem As wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi))
    (SND (encode_all_different bnd n As))
Proof
  qid_spec_tac`n`>>
  Induct_on`As`>>rw[encode_all_different_def]>>
  fs[all_different_sem_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_all_different_row_sem_1,SND,all_different_row_sem_def]
QED

Theorem encode_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (SND (encode_all_different bnd n As)) ⇒
  all_different_sem As wi
Proof
  qid_spec_tac`n`>>
  Induct_on`As`>>rw[encode_all_different_def]>>
  fs[all_different_sem_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_all_different_row_sem_2,SND,all_different_row_sem_def]
QED

(* Step 2: define the cencode and prove it correct *)
Definition cencode_all_different_row_def:
  (cencode_all_different_row bnd n A [] = (n,[])) ∧
  (cencode_all_different_row bnd n A (B::Bs) =
    let (n',B') = cencode_not_equals bnd n A B in
    let (n'',Bs') = cencode_all_different_row bnd n' A Bs in
      (n'',B' ++ Bs'))
End

Definition cencode_all_different_def:
  (cencode_all_different bnd n [] = (n,[])) ∧
  (cencode_all_different bnd n (A::As) =
    let (n',A') = cencode_all_different_row bnd n A As in
    let (n'',As') = cencode_all_different bnd n' As in
    (n'',A' ++ As'))
End

Theorem cencode_all_different_row_forget_ilps:
  cencode_all_different_row bnd n A As =
  (I ## forget_b_ilps)
    (encode_all_different_row bnd n A As)
Proof
  qid_spec_tac`n`>>Induct_on`As`>>
  rw[cencode_all_different_row_def,encode_all_different_row_def,cencode_not_equals_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]
QED

Theorem cencode_all_different_forget_ilps:
  cencode_all_different bnd n As =
  (I ## forget_b_ilps)
    (encode_all_different bnd n As)
Proof
  qid_spec_tac`n`>>Induct_on`As`>>
  rw[cencode_all_different_def,encode_all_different_def,cencode_all_different_row_forget_ilps]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]
QED

(* Step 3: bound_vars and inj_vars properties *)
Theorem encode_all_different_row_good_b_ilps:
  encode_all_different_row bnd n A As = (n', ilps) ⇒
  good_b_ilps n n' ilps
Proof
  qid_spec_tac`n`>>qid_spec_tac`ilps`>>
  Induct_on`As`>>
  rw[encode_all_different_row_def]>>
  rpt (pairarg_tac>>gvs[])>>
  irule_at Any good_b_ilps_append>>
  drule encode_not_equals_good_b_ilps>>
  disch_then (irule_at Any)>>
  first_x_assum drule>>
  disch_then (irule_at Any)>>
  simp[]
QED

Theorem encode_all_different_good_b_ilps:
  encode_all_different bnd n As = (n', ilps) ⇒
  good_b_ilps n n' ilps
Proof
  qid_spec_tac`n`>>qid_spec_tac`ilps`>>
  Induct_on`As`>>
  rw[encode_all_different_def]>>
  rpt (pairarg_tac>>gvs[])>>
  irule_at Any good_b_ilps_append>>
  drule encode_all_different_row_good_b_ilps>>
  disch_then (irule_at Any)>>
  first_x_assum drule>>
  disch_then (irule_at Any)>>
  simp[]
QED

(*** abs ***)

(* abs only uses reifications *)

(* Encoding for Y a variable *)
Definition encode_abs_var_def:
  encode_abs_var bnd X Y =
  let vY = INL Y in
  encode_ge bnd Y 0 ++
  [
    bits_imply bnd [Pos (INL (Ge Y 0))] (mk_constraint_ge 1 X (-1) vY 0);
    bits_imply bnd [Pos (INL (Ge Y 0))] (mk_constraint_ge 1 vY (-1) X 0);
    bits_imply bnd [Neg (INL (Ge Y 0))] (mk_constraint_ge 1 X 1 vY 0);
    bits_imply bnd [Neg (INL (Ge Y 0))] (mk_constraint_ge (-1) X (-1) vY 0);
  ]
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

Theorem encode_abs_sem_1:
  valid_assignment bnd wi ∧
  abs_sem X Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi)) (encode_abs bnd X Y)
Proof
  rw[encode_abs_def]>>
  TOP_CASE_TAC>>gvs[]
  >-
    simp[encode_abs_var_sem,reify_def,reify_reif_def]
  >-
    simp[encode_abs_const_sem,reify_def,reify_reif_def]
QED

Theorem encode_abs_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_abs bnd X Y) ⇒
  abs_sem X Y wi
Proof
  rw[encode_abs_def]>>
  every_case_tac>>gvs[]
  >- rfs[encode_abs_var_sem]
  >- rfs[encode_abs_const_sem]
QED

(*** ilc ***)

(* ilc requires no extra variables *)
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

(*** element ***)

(* element only uses reifications *)

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
    (wb (INL (Ge X &i)) ⇔ wi X ≥ &i)) ∧
  (∀i. 1 ≤ i ∧ i ≤ LENGTH As ⇒
    (wb (INL (Eq X &i)) ⇔ wi X = &i)) ∧
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

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem R X As wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi))
    (encode_element bnd R X As)
Proof
  rw[encode_element_def]>>
  TOP_CASE_TAC>>gvs[]
  >- simp[encode_element_var_sem,reify_def,reify_reif_def]
  >- simp[encode_element_const_sem,reify_def,reify_reif_def]
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element bnd R X As) ⇒
  element_sem R X As wi
Proof
  rw[encode_element_def]>>
  every_case_tac>>gvs[]
  >- rfs[encode_element_var_sem]
  >- rfs[encode_element_const_sem]
QED

(* TODO below *)
Definition encode_cp_one_def:
  encode_cp_one bnd n c =
  case c of
    NotEquals X Y => encode_not_equals bnd n X Y
  | AllDifferent As => encode_all_different bnd n As
  | Element R X As => (n, encode_element bnd R X As)
  | Abs X Y => (n, encode_abs bnd X Y)
  | Ilc Xs op rhs => (n, encode_ilc Xs op rhs)
End

Definition cencode_cp_one_def:
  cencode_cp_one bnd n c =
  (I ## forget_b_ilps) (encode_cp_one bnd n c)
End

(* TODO: push the ## inside *)
Theorem cencode_cp_one_compute =
  SRULE [encode_cp_one_def,
    Once
    (TypeBase.case_rand_of ``:'a constraint``),
    GSYM cencode_not_equals_def,
    GSYM cencode_all_different_forget_ilps
  ] cencode_cp_one_def;

Theorem encode_cp_one_sem_1:
  valid_assignment bnd wi ∧
  constraint_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi)) (SND (encode_cp_one bnd n c))
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >- metis_tac[encode_not_equals_sem_1]
  >- metis_tac[encode_all_different_sem_1]
  >- metis_tac[encode_element_sem_1]
  >- cheat
  >- metis_tac[encode_abs_sem_1]
  >- metis_tac[encode_ilc_sem]
  >> cheat
QED

Theorem encode_cp_one_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (SND (encode_cp_one bnd n c)) ⇒
  constraint_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_cp_one_def,constraint_sem_def]
  >- metis_tac[encode_not_equals_sem_2]
  >- metis_tac[encode_all_different_sem_2]
  >- metis_tac[encode_element_sem_2]
  >- cheat
  >- metis_tac[encode_abs_sem_2]
  >- metis_tac[encode_ilc_sem]
  >> cheat
QED

(* An actual implementation will avoid duplicates here,
  probably with an accumulator *)
Definition encode_cp_all_def:
  (encode_cp_all bnd n [] = []) ∧
  (encode_cp_all bnd n (c::cs) =
    let (n',c') = encode_cp_one bnd n c in
    c' ++ encode_cp_all bnd n' cs)
End

Definition cencode_cp_all_def:
  (cencode_cp_all bnd n [] = []) ∧
  (cencode_cp_all bnd n (c::cs) =
    let (n',c') = cencode_cp_one bnd n c in
    c' ++ cencode_cp_all bnd n' cs)
End

Theorem encode_cp_all_sem_1:
  valid_assignment bnd wi ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify wi)) (encode_cp_all bnd n cs)
Proof
  qid_spec_tac`n`>>Induct_on`cs`>>
  rw[encode_cp_all_def]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_cp_one_sem_1,SND]
QED

Theorem encode_cp_all_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_cp_all bnd n cs) ⇒
  EVERY (λc. constraint_sem c wi) cs
Proof
  qid_spec_tac`n`>>Induct_on`cs`>>
  rw[encode_cp_all_def]>>
  pairarg_tac>>gvs[]>>
  metis_tac[encode_cp_one_sem_2,SND]
QED

(* The actual final theorems we want *)
Theorem cencode_cp_all_sem_1:
  valid_assignment bnd wi ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  ∃wb.
  EVERY (λx. iconstraint_sem x (wi,wb)) (cencode_cp_all bnd n cs)
Proof
  cheat
QED

Theorem cencode_cp_all_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_cp_all bnd n cs) ⇒
  EVERY (λc. constraint_sem c wi) cs
Proof
  cheat
QED


(* === Examples ===

not-equals
  EVAL``encode_not_equals (λX. (-10,10)) 5 (INL X) (INL Y)``
  EVAL``encode_not_equals (λX. (-10,10)) 5 (INL X) (INR 4)``

all-different
  EVAL``encode_all_different (λX. (-10,10)) 5 [INL X; INL Y; INL Z; INR 0i]``

element
  EVAL``encode_element (λX. (-10,10)) (INL R) (INL X) [INL A; INL B; INL C; INL D; INL E]``

abs
  EVAL``encode_abs (λX. (-10,10)) (INL X) (INL Y)``

*)

val _ = export_theory();
