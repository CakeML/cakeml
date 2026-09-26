(*
  Stored form of a formula constraint (a slot) and the RUP check on it,
  against a stamped assignment array.
*)
Theory npbc_slot
Ancestors
  npbc npbc_check mlvector
Libs
  preamble

(* A formula slot: no constraint, or a constraint stored as its
  coefficients, its variables, its degree, its largest absolute
  coefficient and its core flag. *)
Datatype:
  slot = Empty | Stored (int vector) (num vector) int num bool
End

Definition max_coeff_def:
  max_coeff ([]:(int # num) list) = 0n ∧
  max_coeff ((i,n)::xs) = MAX (Num (ABS i)) (max_coeff xs)
End

Definition enc_def:
  enc ((l,d):npbc) b =
  Stored (Vector (MAP FST l)) (Vector (MAP SND l)) d (max_coeff l) b
End

Definition enc_opt_def:
  enc_opt NONE = Empty ∧
  enc_opt (SOME (c,b)) = enc c b
End

Definition wf_slot_def:
  wf_slot Empty = T ∧
  wf_slot (Stored cs vs d mc b) = (length cs = length vs)
End

(* Executable reads use sub_unsafe; their indices are in bounds *)
Theorem sub_unsafe_sub[simp]:
  sub_unsafe v n = sub v n
Proof
  Cases_on`v`>>simp[mlvectorTheory.sub_unsafe_def,mlvectorTheory.sub_def]
QED

Definition dec_terms_def:
  dec_terms cs vs i acc =
  if i = 0 then acc
  else
    let i1 = i - 1 in
    dec_terms cs vs i1 ((sub_unsafe cs i1, sub_unsafe vs i1)::acc)
End

Definition dec_def:
  dec s =
  case s of
    Empty => ([],0)
  | Stored cs vs d mc b => (dec_terms cs vs (length cs) [], d)
End

(* The assignment, as in ccnf: an entry below the stamp b is unassigned,
  b is false and b+1 is true *)
Definition dm_rel_def:
  dm_rel dm dml (b:num) ⇔
  0 < b ∧
  ∀n.
    (FLOOKUP dm n = NONE ⇔ (any_el n dml 0 < b)) ∧
    (FLOOKUP dm n = SOME F ⇔ any_el n dml 0 = b) ∧
    (FLOOKUP dm n = SOME T ⇔ any_el n dml 0 = b+1)
End

(* Ensures that the assignment has at least sz entries, all unassigned.
  Advancing the stamp by 2 makes every existing entry read as unassigned. *)
Definition reset_dm_list_def:
  reset_dm_list dml (b:num) sz =
  if LENGTH dml < sz then
    (REPLICATE (2 * sz) (0:num), 1)
  else
    (dml,b+2)
End

(* The slack of a constraint under the assignment, over its terms from
  index i down, stopping once it reaches lim; the flag records that every
  variable read was within the assignment *)
Definition rup_pass1_slot_def:
  rup_pass1_slot (assg:num list) (b:num) cs vs lim i (acc:num) =
  if lim ≤ acc then (acc,T)
  else if i = 0 then (acc,T)
  else
    let i1 = i - 1 in
    let n = sub_unsafe vs i1 in
    if n < LENGTH assg then
      let c = sub_unsafe cs i1 in
      let v = EL n assg in
      rup_pass1_slot assg b cs vs lim i1
        (if v < b ∨ (v = b + 1 ⇔ 0 ≤ c) then acc + Num (ABS c) else acc)
    else (acc,F)
End

(* Assigns the unassigned variables whose literals the slack forces, over
  the terms from index i down *)
Definition rup_pass2_slot_def:
  rup_pass2_slot (assg:num list) (b:num) max cs vs l i =
  if i = 0 then (assg,T)
  else
    let i1 = i - 1 in
    let n = sub_unsafe vs i1 in
    if n < LENGTH assg then
      let c = sub_unsafe cs i1 in
      if EL n assg < b ∧ max < l + Num (ABS (c:int)) then
        rup_pass2_slot (LUPDATE (if 0 ≤ c then b + 1 else b) n assg)
          b max cs vs l i1
      else
        rup_pass2_slot assg b max cs vs l i1
    else (assg,F)
End

(* (conflict found, updated assignment, all reads within the assignment) *)
Definition update_assg_slot_def:
  update_assg_slot assg b s =
  case s of
    Empty => (F,assg,T)
  | Stored cs vs d mc core =>
    if d ≤ 0 then (F,assg,T)
    else
      let l = Num (ABS d) in
      let lim = l + mc in
      let (max,pre) = rup_pass1_slot assg b cs vs lim (length cs) 0 in
      if lim ≤ max then (F,assg,pre)
      else if max < l then (T,assg,pre)
      else
        let (assg',pre') = rup_pass2_slot assg b max cs vs l (length cs) in
        (F,assg',pre ∧ pre')
End

Definition max_var_def:
  max_var ([]:(int # num) list) = 0n ∧
  max_var ((i,n)::xs) = MAX n (max_var xs)
End

(* every variable of the slot is below n *)
Definition slot_bound_def:
  slot_bound Empty n = T ∧
  slot_bound (Stored cs vs d mc b) n = (∀j. j < length vs ⇒ sub vs j < n)
End

(* Ensures that the assignment has at least sz entries *)
Definition grow_assg_def:
  grow_assg dml (b:num) sz =
  if LENGTH dml < sz then
    (REPLICATE (2 * sz) (0:num), 1)
  else
    (dml,b)
End

(* The spec's second pass without the guard on assigned variables *)
Definition rup_pass2_unguarded_def:
  rup_pass2_unguarded assg max [] l = SOME assg ∧
  rup_pass2_unguarded assg max ((k:num,i:int,n:num)::ys) l =
    if max < l + k then
      rup_pass2_unguarded (assg |+ (n,0 ≤ i)) max ys l
    else
      rup_pass2_unguarded assg max ys l
End

(* Tests *)

Theorem dec_enc_test:
  dec (enc ([(2,1);(-3,4)],5) T) = ([(2,1);(-3,4)],5)
Proof
  EVAL_TAC
QED

(* no literal is forced: the first pass stops at lim *)
Theorem update_assg_slot_test_early:
  update_assg_slot [0;0;0] 1 (enc ([(1,1);(1,1);(2,2)],2) T) = (F,[0;0;0],T) ∧
  update_assg FEMPTY ([(1,1);(1,1);(2,2)],2) = SOME FEMPTY
Proof
  EVAL_TAC
QED

(* x1 occurs twice and is forced once *)
Theorem update_assg_slot_test_repeated:
  update_assg_slot [0;0;0] 1 (enc ([(2,1);(2,1);(1,2)],4) T) = (F,[0;2;0],T) ∧
  update_assg FEMPTY ([(2,1);(2,1);(1,2)],4) = SOME (FEMPTY |+ (1,T))
Proof
  EVAL_TAC
QED

(* both signs of x1 are forced; the first assignment (from the back) stays *)
Theorem update_assg_slot_test_opposite:
  update_assg_slot [0;0;0] 1 (enc ([(2,1);(-2,1);(1,2)],4) T) = (F,[0;1;0],T) ∧
  update_assg FEMPTY ([(2,1);(-2,1);(1,2)],4) = SOME (FEMPTY |+ (1,F))
Proof
  EVAL_TAC
QED

(* stamp 3: the entries 1 and 2 are left over from an earlier check *)
Theorem update_assg_slot_test_stamp:
  update_assg_slot [0;2;4;1] 3 (enc ([(1,1);(1,2);(1,3)],1) T) = (F,[0;2;4;1],T) ∧
  update_assg_slot [0;2;4;1] 3 (enc ([(1,1);(1,2)],1) T) = (F,[0;2;4;1],T) ∧
  update_assg_slot [0;2;4;3] 3 (enc ([(1,1);(1,3)],1) T) = (F,[0;4;4;3],T) ∧
  update_assg_slot [0;2;3;3] 3 (enc ([(1,2);(1,3)],1) T) = (T,[0;2;3;3],T)
Proof
  EVAL_TAC
QED

(* a variable outside the assignment clears the flag *)
Theorem update_assg_slot_test_bound:
  SND (SND (update_assg_slot [0;0] 1 (enc ([(1,1);(1,2)],2) T))) = F
Proof
  EVAL_TAC
QED

(* Interface *)

Theorem wf_slot_enc[simp]:
  wf_slot (enc c b)
Proof
  PairCases_on`c`>>
  simp[enc_def,wf_slot_def,mlvectorTheory.length_def]
QED

Theorem enc_NOT_Empty[simp]:
  enc c b ≠ Empty
Proof
  PairCases_on`c`>>
  simp[enc_def]
QED

Theorem dec_terms_thm:
  ∀cs vs i acc l.
    cs = Vector (MAP FST l) ∧ vs = Vector (MAP SND l) ∧ i ≤ LENGTH l ⇒
    dec_terms cs vs i acc = TAKE i l ++ acc
Proof
  ho_match_mp_tac dec_terms_ind>>
  rw[]>>
  simp[Once dec_terms_def]>>
  rw[]>>
  gvs[mlvectorTheory.sub_def,EL_MAP]>>
  qspecl_then [`i-1`,`l`] mp_tac SNOC_EL_TAKE>>
  simp[ADD1,SNOC_APPEND]
QED

Theorem dec_enc[simp]:
  dec (enc c b) = c
Proof
  PairCases_on`c`>>
  simp[enc_def,dec_def,mlvectorTheory.length_def]>>
  qspecl_then [`Vector (MAP FST c0)`,`Vector (MAP SND c0)`,`LENGTH c0`,`[]`,`c0`]
    mp_tac dec_terms_thm>>
  simp[]
QED

Theorem enc_opt_eq_Empty[simp]:
  enc_opt x = Empty ⇔ x = NONE
Proof
  Cases_on`x`>>
  simp[enc_opt_def]>>
  rename1`enc_opt (SOME p)`>>
  PairCases_on`p`>>
  simp[enc_opt_def]
QED

Theorem slot_bound_enc:
  slot_bound (enc c b) n ⇔ EVERY (λ(i,v). v < n) (FST c)
Proof
  PairCases_on`c`>>
  simp[enc_def,slot_bound_def,mlvectorTheory.length_def,mlvectorTheory.sub_def,
    EVERY_EL,EL_MAP,pairTheory.ELIM_UNCURRY]
QED

Theorem slot_bound_mono:
  slot_bound s n ∧ n ≤ m ⇒ slot_bound s m
Proof
  Cases_on`s`>>rw[slot_bound_def]>>
  first_x_assum drule>>
  simp[]
QED

Theorem max_var_bound:
  ∀l. EVERY (λ(i,v). v < max_var l + 1) l
Proof
  Induct>>
  simp[max_var_def,FORALL_PROD]>>
  rw[]
  >- simp[MAX_DEF]>>
  irule MONO_EVERY>>
  first_x_assum (irule_at Any)>>
  simp[FORALL_PROD,MAX_DEF]
QED

Theorem slot_bound_enc_max_var:
  slot_bound (enc c b) (max_var (FST c) + 1)
Proof
  simp[slot_bound_enc,max_var_bound]
QED

Theorem max_var_not:
  max_var (FST (not c)) = max_var (FST c)
Proof
  PairCases_on`c`>>
  simp[not_def]>>
  Induct_on`c0`>>
  simp[max_var_def,FORALL_PROD]
QED

(* RUP *)

Theorem dm_rel_FEMPTY_REPLICATE:
  dm_rel FEMPTY (REPLICATE n 0) 1
Proof
  pure_rewrite_tac[dm_rel_def]>>
  rw[any_el_ALT,EL_REPLICATE]
QED

Theorem dm_rel_imp_any_el:
  dm_rel dm dml b ⇒
  any_el n dml 0 < b+2
Proof
  rw[dm_rel_def]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  Cases_on`FLOOKUP dm n`>>gvs[]
QED

Theorem dm_rel_reset_dm_list:
  dm_rel dm dml b ∧
  reset_dm_list dml b sz = (dml',b') ⇒
  dm_rel FEMPTY dml' b' ∧ sz ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  fs[LENGTH_REPLICATE,dm_rel_FEMPTY_REPLICATE]>>
  drule dm_rel_imp_any_el>>
  rw[dm_rel_def]>>
  qpat_x_assum`∀n. _`(qspec_then`n` assume_tac)>>
  decide_tac
QED

Theorem dm_rel_grow_assg:
  dm_rel dm dml b ∧
  grow_assg dml b sz = (dml',b') ⇒
  (∃dm'. dm_rel dm' dml' b') ∧
  sz ≤ LENGTH dml' ∧ LENGTH dml ≤ LENGTH dml'
Proof
  rw[grow_assg_def]>>
  gvs[]>>
  metis_tac[dm_rel_FEMPTY_REPLICATE]
QED

Theorem reset_dm_list_LENGTH:
  reset_dm_list dml b sz = (dml',b') ⇒
  LENGTH dml ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  simp[]
QED

Theorem max_coeff_MEM:
  ∀ls i n. MEM (i,n) ls ⇒ Num (ABS i) ≤ max_coeff ls
Proof
  Induct>>
  gvs[max_coeff_def,FORALL_PROD]>>
  rw[]>>
  res_tac>>
  gvs[]
QED

Theorem rup_pass1_acc:
  ∀xs acc ys a y.
    rup_pass1 dm xs 0 [] = (a,y) ⇒
    rup_pass1 dm xs acc ys = (acc + a, y ++ ys)
Proof
  Induct>>
  simp[rup_pass1_def,FORALL_PROD]>>
  rpt gen_tac>>
  Cases_on`rup_pass1 dm xs 0 []`>>
  fs[]>>
  Cases_on`FLOOKUP dm p_2`>>
  simp[]>>
  rw[]
QED

Theorem rup_pass1_append:
  ∀xs acc ys zs.
    rup_pass1 dm (xs ++ zs) acc ys =
    rup_pass1 dm zs (FST (rup_pass1 dm xs acc ys)) (SND (rup_pass1 dm xs acc ys))
Proof
  Induct>>
  simp[rup_pass1_def,FORALL_PROD]>>
  rw[]>>
  Cases_on`FLOOKUP dm p_2`>>
  simp[]>>
  rename1`FLOOKUP dm p_2 = SOME v`>>
  Cases_on`v`>>simp[]
QED

Theorem rup_pass1_ys_MEM:
  ∀xs acc ys k i n.
    MEM (k,i,n) (SND (rup_pass1 dm xs acc ys)) ⇒
    MEM (k,i,n) ys ∨ (MEM (i,n) xs ∧ k = Num (ABS i))
Proof
  Induct>>
  simp[rup_pass1_def,FORALL_PROD]>>
  rpt gen_tac>>
  Cases_on`FLOOKUP dm p_2`>>
  simp[]
  >- (
    strip_tac>>
    first_x_assum drule>>
    rw[]>>
    gvs[])>>
  rename1`FLOOKUP dm p_2 = SOME v`>>
  Cases_on`v`>>
  simp[]>>
  strip_tac>>
  first_x_assum drule>>
  rw[]>>
  gvs[]
QED

Theorem rup_pass2_no_prop:
  ∀ys assg max l mc.
    EVERY (λ(k,i,n). k ≤ mc) ys ∧ l + mc ≤ max ⇒
    rup_pass2 assg max ys l = SOME assg
Proof
  Induct>>
  simp[rup_pass2_def,FORALL_PROD]>>
  rw[]>>
  last_x_assum irule>>
  qexists_tac`mc`>>
  gvs[]
QED

Theorem dm_rel_update:
  dm_rel dm assg b ∧ x < LENGTH assg ⇒
  dm_rel (dm |+ (x,v)) (LUPDATE (if v then b + 1 else b) x assg) b
Proof
  rw[dm_rel_def,FLOOKUP_UPDATE,any_el_ALT,EL_LUPDATE]>>
  Cases_on`x = n`>>
  gvs[]
QED

Theorem rup_pass1_TAKE_SUC:
  i < LENGTH l ⇒
  rup_pass1 dm (TAKE (SUC i) l) 0 [] =
  (FST (rup_pass1 dm (TAKE i l) 0 []) + FST (rup_pass1 dm [EL i l] 0 []),
   SND (rup_pass1 dm [EL i l] 0 []) ++ SND (rup_pass1 dm (TAKE i l) 0 []))
Proof
  strip_tac>>
  simp[GSYM SNOC_EL_TAKE,SNOC_APPEND,rup_pass1_append]>>
  Cases_on`rup_pass1 dm (TAKE i l) 0 []`>>
  Cases_on`rup_pass1 dm [EL i l] 0 []`>>
  drule rup_pass1_acc>>
  simp[]
QED

Theorem rup_pass1_one_dm_rel:
  dm_rel dm assg b ∧ n < LENGTH assg ⇒
  rup_pass1 dm [(c,n)] 0 [] =
  if EL n assg < b then (Num (ABS c),[(Num (ABS c),c,n)])
  else if (EL n assg = b + 1 ⇔ 0 ≤ c) then (Num (ABS c),[])
  else (0,[])
Proof
  strip_tac>>
  `(FLOOKUP dm n = NONE ⇔ EL n assg < b) ∧
   (FLOOKUP dm n = SOME F ⇔ EL n assg = b) ∧
   (FLOOKUP dm n = SOME T ⇔ EL n assg = b + 1)` by
    gvs[dm_rel_def,any_el_ALT]>>
  simp[rup_pass1_def]>>
  Cases_on`FLOOKUP dm n`>>
  gvs[]>>
  rename1`FLOOKUP dm n = SOME v`>>
  Cases_on`v`>>
  gvs[]>>
  Cases_on`c < 0`>>
  gvs[GSYM integerTheory.INT_NOT_LT]
QED

Theorem rup_pass1_slot_thm:
  ∀assg b cs vs lim i acc l r pre.
    cs = Vector (MAP FST l) ∧ vs = Vector (MAP SND l) ∧
    dm_rel dm assg b ∧ i ≤ LENGTH l ∧
    (∀j. j < i ⇒ SND (EL j l) < LENGTH assg) ∧
    rup_pass1_slot assg b cs vs lim i acc = (r,pre) ⇒
    pre ∧
    (r < lim ⇒ r = acc + FST (rup_pass1 dm (TAKE i l) 0 [])) ∧
    (lim ≤ r ⇒ lim ≤ acc + FST (rup_pass1 dm (TAKE i l) 0 []))
Proof
  ho_match_mp_tac rup_pass1_slot_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  qpat_x_assum`rup_pass1_slot _ _ _ _ _ _ _ = _` mp_tac>>
  simp[Once rup_pass1_slot_def]>>
  IF_CASES_TAC
  >- (
    rw[]>>
    simp[])>>
  IF_CASES_TAC
  >- (
    rw[]>>
    gvs[rup_pass1_def])>>
  gvs[mlvectorTheory.sub_def,EL_MAP]>>
  `SND (EL (i-1) l) < LENGTH assg` by simp[]>>
  simp[]>>
  strip_tac>>
  qpat_x_assum`∀l' r pre. _` (qspec_then`l` mp_tac)>>
  simp[]>>
  strip_tac>>
  `i - 1 < LENGTH l` by simp[]>>
  drule_then (qspec_then`dm` mp_tac) rup_pass1_TAKE_SUC>>
  `SUC (i - 1) = i` by simp[]>>
  Cases_on`EL (i-1) l`>>
  rename1`EL (i-1) l = (c,n)`>>
  gvs[EL_MAP]>>
  drule_then (drule_then (qspec_then`c` assume_tac)) rup_pass1_one_dm_rel>>
  simp[]>>
  strip_tac>>
  Cases_on`EL n assg < b`>>
  Cases_on`(EL n assg = b + 1 ⇔ 0 ≤ c)`>>
  gvs[]
QED

Theorem rup_pass2_slot_thm:
  ∀assg b max cs vs l0 i l dme dm0.
    cs = Vector (MAP FST l) ∧ vs = Vector (MAP SND l) ∧
    dm_rel dme assg b ∧ dm0 SUBMAP dme ∧ i ≤ LENGTH l ∧
    (∀j. j < i ⇒ SND (EL j l) < LENGTH assg) ⇒
    ∃assg' dm'.
      rup_pass2_slot assg b max cs vs l0 i = (assg',T) ∧
      rup_pass2 dme max (SND (rup_pass1 dm0 (TAKE i l) 0 [])) l0 = SOME dm' ∧
      dm_rel dm' assg' b ∧ LENGTH assg' = LENGTH assg
Proof
  ho_match_mp_tac rup_pass2_slot_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  simp[Once rup_pass2_slot_def]>>
  IF_CASES_TAC
  >- gvs[rup_pass1_def,rup_pass2_def]>>
  gvs[mlvectorTheory.sub_def,EL_MAP]>>
  `SND (EL (i-1) l) < LENGTH assg` by simp[]>>
  `i - 1 < LENGTH l` by simp[]>>
  drule_then (qspec_then`dm0` assume_tac) rup_pass1_TAKE_SUC>>
  `SUC (i - 1) = i` by simp[]>>
  Cases_on`EL (i-1) l`>>
  rename1`EL (i-1) l = (c,n)`>>
  gvs[EL_MAP]>>
  `(FLOOKUP dme n = NONE ⇔ EL n assg < b)` by gvs[dm_rel_def,any_el_ALT]>>
  Cases_on`FLOOKUP dm0 n`
  >- (
    simp[rup_pass1_def,rup_pass2_def]>>
    IF_CASES_TAC
    >- (
      simp[]>>
      qpat_x_assum`EL n assg < b ∧ _ ⇒ _` mp_tac>>
      simp[]>>
      disch_then (qspecl_then [`l`,`dme |+ (n,0 ≤ c)`,`dm0`] mp_tac)>>
      impl_tac
      >- (
        simp[dm_rel_update]>>
        irule SUBMAP_TRANS>>
        qexists_tac`dme`>>
        simp[SUBMAP_FUPDATE_EXTENDED]>>
        gvs[flookup_thm])>>
      strip_tac>>
      `i - 1 < LENGTH l` by simp[]>>
      gvs[EL_MAP])>>
    qpat_x_assum`¬(EL n assg < b) ∨ _ ⇒ _` mp_tac>>
    simp[]>>
    disch_then (qspecl_then [`l`,`dme`,`dm0`] mp_tac)>>
    simp[])>>
  rename1`FLOOKUP dm0 n = SOME v`>>
  `FLOOKUP dme n = SOME v` by metis_tac[FLOOKUP_SUBMAP]>>
  `SND (rup_pass1 dm0 [(c,n)] 0 []) = []` by (
    Cases_on`v`>>
    simp[rup_pass1_def])>>
  gvs[]
QED

(* every variable of the constraint is within the assignment *)
Theorem update_assg_slot_thm:
  dm_rel dm assg b ∧
  EVERY (λ(i,n). n < LENGTH assg) (FST c) ⇒
  ∃res assg'.
    update_assg_slot assg b (enc c b0) = (res,assg',T) ∧
    LENGTH assg' = LENGTH assg ∧
    case update_assg dm c of
      NONE => res ∧ assg' = assg
    | SOME dm' => ¬res ∧ dm_rel dm' assg' b
Proof
  Cases_on`c`>>
  rename1`(l,d)`>>
  rw[enc_def,update_assg_slot_def,update_assg_def,mlvectorTheory.length_def]>>
  `∀j. j < LENGTH l ⇒ SND (EL j l) < LENGTH assg` by (
    rw[]>>
    gvs[EVERY_EL]>>
    first_x_assum drule>>
    Cases_on`EL j l`>>
    simp[])>>
  rpt (pairarg_tac>>gvs[])>>
  rename1`rup_pass1_slot _ _ _ _ _ _ _ = (mx,pre)`>>
  rename1`rup_pass1 dm l 0 [] = (smx,ys)`>>
  rename1`rup_pass2_slot _ _ _ _ _ _ _ = (assg2,pre2)`>>
  qspecl_then [`assg`,`b`,`Vector (MAP FST l)`,`Vector (MAP SND l)`,
    `Num (ABS d) + max_coeff l`,`LENGTH l`,`0`,`l`,`mx`,`pre`]
    mp_tac rup_pass1_slot_thm>>
  simp[]>>
  strip_tac>>
  Cases_on`Num (ABS d) + max_coeff l ≤ mx`
  >- (
    `rup_pass2 dm smx ys (Num (ABS d)) = SOME dm` by (
      irule rup_pass2_no_prop>>
      qexists_tac`max_coeff l`>>
      simp[EVERY_MEM,FORALL_PROD]>>
      rw[]>>
      rename1`MEM (k,i,n) ys`>>
      qspecl_then [`l`,`0`,`[]`,`k`,`i`,`n`] mp_tac rup_pass1_ys_MEM>>
      rw[]>>
      metis_tac[max_coeff_MEM])>>
    gvs[])>>
  gvs[]>>
  Cases_on`mx < Num (ABS d)`>>
  simp[]>>
  qspecl_then [`assg`,`b`,`mx`,`Vector (MAP FST l)`,`Vector (MAP SND l)`,
    `Num (ABS d)`,`LENGTH l`,`l`,`dm`,`dm`] mp_tac rup_pass2_slot_thm>>
  simp[]>>
  strip_tac>>
  gvs[]
QED

(* On a list with no repeated variable, none of them assigned (which is
  what the first pass leaves for a normalised constraint), the guard in
  rup_pass2 never fires *)
Theorem rup_pass2_compact:
  ∀ys assg.
    ALL_DISTINCT (MAP (λ(k,i,n). n) ys) ∧
    EVERY (λ(k,i,n). FLOOKUP assg n = NONE) ys ⇒
    rup_pass2 assg max ys l = rup_pass2_unguarded assg max ys l
Proof
  Induct>>
  simp[rup_pass2_def,rup_pass2_unguarded_def,FORALL_PROD]>>
  rw[]>>
  first_x_assum irule>>
  gvs[EVERY_MEM,FORALL_PROD,MEM_MAP,FLOOKUP_UPDATE]>>
  rw[]>>
  metis_tac[]
QED

(* Readers *)

Definition contr_slot_aux_def:
  contr_slot_aux cs i (rhs:int) =
  if rhs ≤ 0 then F
  else if i = 0 then T
  else
    let i1 = i - 1 in
    contr_slot_aux cs i1 (rhs - ABS (sub_unsafe cs i1))
End

Definition contr_slot_def:
  contr_slot s =
  case s of
    Empty => F
  | Stored cs vs d mc b =>
    &(length cs * mc) < d ∨ contr_slot_aux cs (length cs) d
End

Theorem contr_slot_test:
  contr_slot (enc ([(2,1);(-3,4)],6) T) ∧
  contr_slot (enc ([(2,1);(-3,4)],7) F) ∧
  ¬contr_slot (enc ([(2,1);(-3,4)],5) T) ∧
  ¬contr_slot Empty
Proof
  EVAL_TAC
QED

Theorem contr_slot_aux_thm:
  ∀i rhs.
  contr_slot_aux cs i rhs ⇔
  &SUM (GENLIST (λj. Num (ABS (sub cs j))) i) < rhs
Proof
  Induct>>
  rw[Once contr_slot_aux_def,GENLIST,SUM_SNOC]>>
  intLib.ARITH_TAC
QED

Theorem lslack_le_max_coeff:
  ∀l. SUM (MAP (Num o ABS o FST) l) ≤ LENGTH l * max_coeff l
Proof
  Induct>>simp[FORALL_PROD,max_coeff_def]>>rw[]>>
  `LENGTH l * max_coeff l ≤ LENGTH l * MAX (Num (ABS p_1)) (max_coeff l)` by
    simp[]>>
  `Num (ABS p_1) ≤ MAX (Num (ABS p_1)) (max_coeff l)` by simp[]>>
  simp[MULT_CLAUSES]
QED

Theorem contr_slot_enc:
  contr_slot (enc c b) ⇔ check_contradiction c
Proof
  PairCases_on`c`>>
  simp[contr_slot_def,enc_def,contr_slot_aux_thm,check_contradiction_thm,
    mlvectorTheory.length_def,mlvectorTheory.sub_def]>>
  `SUM (GENLIST (λj. Num (ABS (EL j (MAP FST c0)))) (LENGTH c0)) =
    lslack c0` by (
    simp[lslack_def]>>
    AP_TERM_TAC>>
    simp[LIST_EQ_REWRITE,EL_MAP])>>
  `lslack c0 ≤ LENGTH c0 * max_coeff c0` by
    simp[lslack_def,lslack_le_max_coeff]>>
  simp[]>>
  intLib.ARITH_TAC
QED

Definition eq_terms_def:
  eq_terms cs vs n i [] = (i = n) ∧
  eq_terms cs vs n i ((c,v)::xs) =
    (i < n ∧ sub_unsafe cs i = c ∧ sub_unsafe vs i = (v:num) ∧
     eq_terms cs vs n (i+1) xs)
End

Definition eq_slot_def:
  eq_slot ((l,d):npbc) s =
  case s of
    Empty => (l = [] ∧ d = 0)
  | Stored cs vs d' mc b => d = d' ∧ eq_terms cs vs (length cs) 0 l
End

Definition check_lslack_slot_def:
  check_lslack_slot cs n i (rhs:int) =
  if rhs ≤ 0 then F
  else if n ≤ i then T
  else check_lslack_slot cs n (i+1) (rhs - ABS (sub_unsafe cs i))
Termination
  WF_REL_TAC ‘measure (λ(cs,n,i,rhs). n - i)’
End

Definition check_imp_slot_def:
  check_imp_slot drhs cs vs n i [] rhs =
    check_lslack_slot cs n i rhs ∧
  check_imp_slot drhs cs vs n i ((d,y)::ys) rhs =
    if n ≤ i then T
    else
      let c = sub_unsafe cs i in
      let x = sub_unsafe vs i in
      if x < y then
        let rhs = rhs - ABS c in
        if 0 < rhs then check_imp_slot drhs cs vs n (i+1) ((d,y)::ys) rhs
        else F
      else if y < (x:num) then
        check_imp_slot drhs cs vs n i ys rhs
      else if match_sign c d then
        let rhs = rhs - imp_terms drhs c d in
        if 0 < rhs then check_imp_slot drhs cs vs n (i+1) ys rhs
        else F
      else
        let rhs = rhs - ABS c in
        if 0 < rhs then check_imp_slot drhs cs vs n (i+1) ((d,y)::ys) rhs
        else F
Termination
  WF_REL_TAC ‘measure (λ(drhs,cs,vs,n,i,ys,rhs). (n - i) + LENGTH ys)’>>
  rw[]
End

Definition imp_slot_def:
  imp_slot s ((dls,drhs):npbc) ⇔
  drhs ≤ 0 ∨
  case s of
    Empty => F
  | Stored cs vs crhs mc b =>
    contr_slot s ∨
    (let rhs = crhs - drhs + 1 in
      0 < rhs ∧ check_imp_slot drhs cs vs (length cs) 0 dls rhs)
End

Theorem eq_imp_slot_test:
  eq_slot ([(2,1);(-3,4)],5) (enc ([(2,1);(-3,4)],5) T) ∧
  ¬eq_slot ([(2,1);(-3,4)],4) (enc ([(2,1);(-3,4)],5) T) ∧
  ¬eq_slot ([(2,1)],5) (enc ([(2,1);(-3,4)],5) T) ∧
  imp_slot (enc ([(2,1);(3,4)],5) T) ([(1,1);(3,4)],4) ∧
  ¬imp_slot (enc ([(2,1);(3,4)],5) T) ([(1,1);(3,4)],5) ∧
  imp ([(2,1);(3,4)],5) ([(1,1);(3,4)],4) ∧
  ¬imp ([(2,1);(3,4)],5) ([(1,1);(3,4)],5)
Proof
  EVAL_TAC
QED

Theorem eq_terms_enc:
  ∀l i.
  eq_terms (Vector (MAP FST l')) (Vector (MAP SND l')) (LENGTH l') i l ⇔
  i ≤ LENGTH l' ∧ l = DROP i l'
Proof
  Induct>>
  simp[eq_terms_def,FORALL_PROD,mlvectorTheory.sub_def,DROP_NIL]>>
  rw[]>>
  Cases_on`i < LENGTH l'`>>
  gvs[DROP_EL_CONS,EL_MAP,ADD1,DROP_LENGTH_TOO_LONG]>>
  Cases_on`EL i l'`>>
  gvs[]>>
  metis_tac[]
QED

Theorem eq_slot_enc:
  eq_slot c (enc c' b) ⇔ c = c'
Proof
  PairCases_on`c`>>PairCases_on`c'`>>
  simp[eq_slot_def,enc_def,mlvectorTheory.length_def,eq_terms_enc]>>
  metis_tac[]
QED

Theorem check_lslack_slot_enc:
  ∀cs n i rhs.
  cs = Vector (MAP FST l) ∧ n = LENGTH l ⇒
  (check_lslack_slot cs n i rhs ⇔ check_lslack (DROP i l) rhs)
Proof
  ho_match_mp_tac check_lslack_slot_ind>>
  rw[]>>
  rw[Once check_lslack_slot_def]>>
  Cases_on`i < LENGTH l`
  >- (
    `DROP i l = EL i l :: DROP (i+1) l` by simp[DROP_EL_CONS,ADD1]>>
    Cases_on`EL i l`>>
    gvs[mlvectorTheory.sub_def,EL_MAP]>>
    simp[Once check_lslack_def]>>
    Cases_on`rhs ≤ 0`>>
    gvs[])>>
  `DROP i l = []` by simp[DROP_LENGTH_TOO_LONG]>>
  simp[Once check_lslack_def]
QED

Theorem check_imp_slot_enc:
  ∀drhs cs vs n i ys rhs.
  cs = Vector (MAP FST l) ∧ vs = Vector (MAP SND l) ∧ n = LENGTH l ⇒
  (check_imp_slot drhs cs vs n i ys rhs ⇔
    check_imp_lists drhs (DROP i l) ys rhs)
Proof
  ho_match_mp_tac check_imp_slot_ind>>
  rw[]
  >- simp[Once check_imp_slot_def,Once check_imp_lists_def,
      check_lslack_slot_enc]>>
  Cases_on`i < LENGTH l`
  >- (
    simp[Once check_imp_slot_def]>>
    `DROP i l = EL i l :: DROP (i+1) l` by simp[DROP_EL_CONS,ADD1]>>
    Cases_on`EL i l`>>
    gvs[mlvectorTheory.sub_def,EL_MAP]>>
    simp[Once check_imp_lists_def]>>
    rw[]>>
    gvs[]>>
    metis_tac[LESS_ANTISYM])>>
  `DROP i l = []` by simp[DROP_LENGTH_TOO_LONG]>>
  simp[Once check_imp_slot_def,Once check_imp_lists_def]
QED

Theorem check_imp_slot_Vector:
  check_imp_slot drhs (Vector (MAP FST l)) (Vector (MAP SND l)) (LENGTH l)
    i ys rhs ⇔
  check_imp_lists drhs (DROP i l) ys rhs
Proof
  metis_tac[check_imp_slot_enc]
QED

Theorem imp_slot_enc:
  imp_slot (enc c b) d ⇔ imp c d
Proof
  PairCases_on`c`>>PairCases_on`d`>>
  `contr_slot (enc (c0,c1) b) ⇔ check_contradiction (c0,c1)` by
    simp[contr_slot_enc]>>
  gvs[imp_slot_def,imp_def,check_trivial_def,check_imp_def,enc_def,
    mlvectorTheory.length_def,check_imp_slot_Vector]
QED

Definition subst_aux_slot_def:
  subst_aux_slot f cs vs i old new (k:int) =
  if i = 0 then (old,new,k)
  else
    let i1 = i - 1 in
    let c = sub_unsafe cs i1 in
    let l = sub_unsafe vs i1 in
    case f l of
      NONE => subst_aux_slot f cs vs i1 ((c,l)::old) new k
    | SOME (INL b) =>
      subst_aux_slot f cs vs i1 old new (if is_Pos c = b then k + ABS c else k)
    | SOME (INR (Pos n)) => subst_aux_slot f cs vs i1 old ((c,n)::new) k
    | SOME (INR (Neg n)) => subst_aux_slot f cs vs i1 old ((0-c,n)::new) k
End

Definition subst_same_slot_def:
  subst_same_slot f cs vs i =
  if i = 0 then T
  else
    let i1 = i - 1 in
    case f (sub_unsafe vs i1) of
      NONE => subst_same_slot f cs vs i1
    | SOME (INL b) => is_Pos (sub_unsafe cs i1) = b ∧ subst_same_slot f cs vs i1
    | SOME (INR _) => F
End

Definition subst_slot_def:
  subst_slot f s =
  case s of
    Empty => subst f ([],0)
  | Stored cs vs d mc b =>
    let (old,new,k) = subst_aux_slot f cs vs (length cs) [] [] 0 in
    let (sorted,k2) = clean_up new in
    let (result,k3) = add_lists old sorted in
    (result, d - (k + k2 + &k3))
End

Definition subst_opt_slot_def:
  subst_opt_slot f s =
  case s of
    Empty => NONE
  | Stored cs vs d mc b =>
    if subst_same_slot f cs vs (length cs) then NONE
    else
      let res = subst_slot f s in
      if SND res = 0 ∨ imp_slot s res then NONE
      else SOME res
End

Theorem subst_slot_test:
  let f = (λv. if v = 1 then SOME (INL T)
            else if v = 2 then SOME (INR (Pos 3)) else NONE) in
  let c = ([(2,1);(-3,2);(1,4)],3) in
  subst_slot f (enc c T) = subst f c ∧
  subst_opt_slot f (enc c T) = subst_opt f c ∧
  subst_opt_slot (λv. NONE) (enc c T) = subst_opt (λv. NONE) c ∧
  subst_opt_slot (λv. if v = 1 then SOME (INL T) else NONE) (enc c T) =
    subst_opt (λv. if v = 1 then SOME (INL T) else NONE) c
Proof
  EVAL_TAC
QED

Theorem subst_aux_APPEND:
  ∀xs.
  subst_aux f (xs ++ ys) =
    (FST (subst_aux f xs) ++ FST (subst_aux f ys),
     FST (SND (subst_aux f xs)) ++ FST (SND (subst_aux f ys)),
     SND (SND (subst_aux f xs)) + SND (SND (subst_aux f ys)))
Proof
  Induct>>
  simp[subst_aux_def,FORALL_PROD]>>
  rw[]>>
  rpt (pairarg_tac>>gvs[])>>
  every_case_tac>>gvs[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem subst_aux_slot_thm:
  ∀i old new k.
  i ≤ LENGTH l ⇒
  subst_aux_slot f (Vector (MAP FST l)) (Vector (MAP SND l)) i old new k =
  (FST (subst_aux f (TAKE i l)) ++ old,
   FST (SND (subst_aux f (TAKE i l))) ++ new,
   SND (SND (subst_aux f (TAKE i l))) + k)
Proof
  Induct>>
  rw[Once subst_aux_slot_def,subst_aux_def]>>
  `TAKE (SUC i) l = TAKE i l ++ [EL i l]` by
    simp[GSYM SNOC_EL_TAKE,SNOC_APPEND]>>
  Cases_on`EL i l`>>
  gvs[subst_aux_APPEND,subst_aux_def,mlvectorTheory.sub_def,EL_MAP]>>
  every_case_tac>>gvs[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem subst_slot_enc:
  subst_slot f (enc c b) = subst f c
Proof
  PairCases_on`c`>>
  simp[subst_slot_def,enc_def,subst_def,subst_lhs_def,
    mlvectorTheory.length_def,subst_aux_slot_thm]>>
  rpt (pairarg_tac>>gvs[])
QED

Theorem subst_opt_aux_same_APPEND:
  ∀xs.
  SND (SND (SND (subst_opt_aux f (xs ++ ys)))) ⇔
  SND (SND (SND (subst_opt_aux f xs))) ∧ SND (SND (SND (subst_opt_aux f ys)))
Proof
  Induct>>
  simp[subst_opt_aux_def,FORALL_PROD]>>
  rw[]>>
  rpt (pairarg_tac>>gvs[])>>
  every_case_tac>>gvs[]>>
  metis_tac[]
QED

Theorem subst_same_slot_thm:
  ∀i.
  i ≤ LENGTH l ⇒
  (subst_same_slot f (Vector (MAP FST l)) (Vector (MAP SND l)) i ⇔
    SND (SND (SND (subst_opt_aux f (TAKE i l)))))
Proof
  Induct>>
  rw[Once subst_same_slot_def,subst_opt_aux_def]>>
  `TAKE (SUC i) l = TAKE i l ++ [EL i l]` by
    simp[GSYM SNOC_EL_TAKE,SNOC_APPEND]>>
  Cases_on`EL i l`>>
  gvs[subst_opt_aux_same_APPEND,subst_opt_aux_def,
    mlvectorTheory.sub_def,EL_MAP]>>
  every_case_tac>>gvs[]>>
  metis_tac[]
QED

Theorem subst_opt_slot_alt:
  subst_opt_slot f s =
  if (case s of
        Empty => T
      | Stored cs vs d mc b => subst_same_slot f cs vs (length cs))
  then NONE
  else
    let res = subst_slot f s in
    if SND res = 0 ∨ imp_slot s res then NONE
    else SOME res
Proof
  Cases_on`s`>>
  simp[subst_opt_slot_def]
QED

Theorem subst_opt_slot_enc:
  subst_opt_slot f (enc c b) = subst_opt f c
Proof
  PairCases_on`c`>>
  `(case enc (c0,c1) b of
      Empty => T
    | Stored cs vs d mc b => subst_same_slot f cs vs (length cs)) ⇔
    SND (SND (SND (subst_opt_aux f c0)))` by
    simp[enc_def,mlvectorTheory.length_def,subst_same_slot_thm]>>
  simp[subst_opt_slot_alt,subst_slot_enc,imp_slot_enc,subst_opt_eq,
    subst_def,subst_lhs_def]>>
  rpt (pairarg_tac>>gvs[])>>
  imp_res_tac subst_opt_aux_thm_1>>
  gvs[]
QED

Definition cond_pos_def:
  cond_pos x cc =
    EXISTS (λ(c:int,n:num). 0 ≤ c ∧ n = x) cc
End

Definition cond_neg_def:
  cond_neg x cc =
    EXISTS (λ(c:int,n:num). c < 0 ∧ n = x) cc
End

(* (x occurs with a nonnegative coefficient, x occurs with a negative
  coefficient) *)
Definition restore_scan_def:
  restore_scan cs vs (x:num) i p q =
  if i = 0 then (p,q)
  else
    let i1 = i - 1 in
    if sub_unsafe vs i1 = x then
      let c:int = sub_unsafe cs i1 in
      restore_scan cs vs x i1 (p ∨ 0 ≤ c) (q ∨ c < 0)
    else restore_scan cs vs x i1 p q
End

Definition restore_slot_def:
  restore_slot x s =
  case s of
    Empty => (F,F)
  | Stored cs vs d mc b => restore_scan cs vs x (length cs) F F
End

Theorem restore_slot_test:
  restore_slot 4 (enc ([(2,1);(-3,4);(1,4)],3) T) = (T,T) ∧
  restore_slot 1 (enc ([(2,1);(-3,4);(1,4)],3) T) = (T,F) ∧
  restore_slot 2 (enc ([(2,1);(-3,4);(1,4)],3) T) = (F,F)
Proof
  EVAL_TAC
QED

Theorem dec_terms_GENLIST:
  ∀cs vs i acc.
  dec_terms cs vs i acc = GENLIST (λj. (sub cs j, sub vs j)) i ++ acc
Proof
  ho_match_mp_tac dec_terms_ind>>
  rw[]>>
  simp[Once dec_terms_def]>>
  rw[]>>
  Cases_on`i`>>
  gvs[GENLIST,SNOC_APPEND]
QED

Theorem restore_scan_thm:
  ∀i p q.
  restore_scan cs vs x i p q =
    (p ∨ cond_pos x (GENLIST (λj. (sub cs j, sub vs j)) i),
     q ∨ cond_neg x (GENLIST (λj. (sub cs j, sub vs j)) i))
Proof
  Induct>>
  rw[Once restore_scan_def,cond_pos_def,cond_neg_def,GENLIST,EXISTS_SNOC]>>
  metis_tac[]
QED

Theorem restore_slot_thm:
  restore_slot x s = (cond_pos x (FST (dec s)), cond_neg x (FST (dec s)))
Proof
  Cases_on`s`>>
  simp[restore_slot_def,dec_def,dec_terms_GENLIST,restore_scan_thm]>>
  simp[cond_pos_def,cond_neg_def]
QED

(* Hashing *)

Definition h_base_def:
  h_base = 32768:num
End

Definition h_base_sq_def:
  h_base_sq = 1073741824:num
End

Definition h_mod_def:
  h_mod = 1000000009:num
End

(* Fixed size of the hash table *)
Definition splim_def:
  splim = 2000000:num
End

Definition hash_term_def:
  hash_term (i:int) (n:num) =
  if i ≤ 0 then
    (2 * (Num(ABS i)) + h_base * n) MOD h_mod
  else
    (2 * (Num (ABS i)) - 1 + h_base * n) MOD h_mod
End

Definition hash_pair_def:
  hash_pair (i:int,n:num) = hash_term i n
End

Definition hash_list_def:
  (hash_list [] = 0n) ∧
  (hash_list (x::xs) =
    (hash_pair x + h_base_sq * hash_list xs) MOD h_mod)
End

Definition hash_constraint_def:
  hash_constraint (c,n) =
  ((Num (ABS n) + h_base * hash_list c) MOD h_mod) MOD splim
End

Definition hash_terms_slot_def:
  hash_terms_slot cs vs i acc =
  if i = 0 then acc
  else
    let i1 = i - 1 in
    hash_terms_slot cs vs i1
      ((hash_term (sub_unsafe cs i1) (sub_unsafe vs i1) + h_base_sq * acc)
        MOD h_mod)
End

Definition hash_slot_def:
  hash_slot s =
  case s of
    Empty => hash_constraint ([],0)
  | Stored cs vs d mc b =>
    ((Num (ABS d) + h_base * hash_terms_slot cs vs (length cs) 0) MOD h_mod)
      MOD splim
End

Definition mk_hashset_slot_def:
  (mk_hashset_slot [] acc = acc) ∧
  (mk_hashset_slot (s::ss) acc =
    let h = hash_slot s in
    mk_hashset_slot ss (LUPDATE (s::EL h acc) h acc))
End

Definition in_hashset_slot_def:
  in_hashset_slot c hs =
  EXISTS (eq_slot c) (EL (hash_constraint c) hs)
End

Theorem hash_slot_test:
  hash_slot (enc ([(2,1);(-3,4)],5) T) = hash_constraint ([(2,1);(-3,4)],5)
Proof
  EVAL_TAC
QED

Theorem hash_terms_slot_thm:
  ∀i ys.
  hash_terms_slot cs vs i (hash_list ys) =
  hash_list (GENLIST (λj. (sub cs j, sub vs j)) i ++ ys)
Proof
  Induct>>
  rw[Once hash_terms_slot_def]>>
  simp[GENLIST,SNOC_APPEND]>>
  `(h_base_sq * hash_list ys + hash_term (sub cs i) (sub vs i)) MOD h_mod =
    hash_list ((sub cs i,sub vs i)::ys)` by simp[hash_list_def,hash_pair_def]>>
  pop_assum SUBST1_TAC>>
  first_x_assum (qspec_then`(sub cs i,sub vs i)::ys` SUBST1_TAC)>>
  REWRITE_TAC[GSYM APPEND_ASSOC,APPEND]
QED

Theorem hash_slot_thm:
  hash_slot s = hash_constraint (dec s)
Proof
  Cases_on`s`
  >- simp[hash_slot_def,dec_def]>>
  rename1`Stored cs vs d mc b`>>
  simp[hash_slot_def,dec_def,dec_terms_GENLIST,hash_constraint_def]>>
  qspecl_then [`length cs`,`[]`] mp_tac hash_terms_slot_thm>>
  simp[hash_list_def]
QED

Theorem hash_constraint_lt_splim:
  hash_constraint c < splim
Proof
  PairCases_on`c`>>
  simp[hash_constraint_def,splim_def]
QED

Theorem LENGTH_mk_hashset_slot:
  ∀ss acc. LENGTH (mk_hashset_slot ss acc) = LENGTH acc
Proof
  Induct>>rw[mk_hashset_slot_def]
QED

Theorem in_hashset_slot_mk_hashset_slot:
  ∀ss c acc.
  LENGTH acc = splim ∧
  in_hashset_slot c (mk_hashset_slot ss acc) ⇒
  (∃s. MEM s ss ∧ eq_slot c s) ∨ in_hashset_slot c acc
Proof
  Induct>>
  rw[mk_hashset_slot_def]>>
  first_x_assum (drule_at (Pos last))>>
  impl_tac >- fs[]>>
  strip_tac
  >- metis_tac[]>>
  `hash_slot h < splim` by simp[hash_slot_thm,hash_constraint_lt_splim]>>
  gvs[in_hashset_slot_def,EL_LUPDATE]>>
  every_case_tac>>
  gvs[]>>
  metis_tac[]
QED

(* Slot against slot *)

Definition eq_terms_slots_def:
  eq_terms_slots cs vs cs' vs' i =
  if i = 0 then T
  else
    let i1 = i - 1 in
    sub_unsafe cs i1 = sub_unsafe cs' i1 ∧
    sub_unsafe vs i1 = (sub_unsafe vs' i1:num) ∧
    eq_terms_slots cs vs cs' vs' i1
End

Definition eq_slots_def:
  eq_slots s s' =
  case (s,s') of
    (Empty,Empty) => T
  | (Stored cs vs d mc b, Stored cs' vs' d' mc' b') =>
    d = d' ∧ length cs = length cs' ∧
    eq_terms_slots (cs:int vector) vs cs' vs' (length cs)
  | _ => F
End

Definition in_hashset_slots_def:
  in_hashset_slots s hs =
  EXISTS (eq_slots s) (EL (hash_slot s) hs)
End

Theorem eq_slots_test:
  eq_slots (enc ([(2,1);(-3,4)],5) T) (enc ([(2,1);(-3,4)],5) F) ∧
  ¬eq_slots (enc ([(2,1);(-3,4)],5) T) (enc ([(2,1);(-3,5)],5) T) ∧
  ¬eq_slots (enc ([(2,1)],5) T) (enc ([(2,1);(-3,4)],5) T)
Proof
  EVAL_TAC
QED

Theorem eq_terms_slots_thm:
  ∀i.
  eq_terms_slots cs vs cs' vs' i ⇔
  GENLIST (λj. (sub cs j, sub vs j)) i =
  GENLIST (λj. (sub cs' j, sub vs' j)) i
Proof
  Induct>>
  rw[Once eq_terms_slots_def,GENLIST,SNOC_11]>>
  metis_tac[]
QED

Theorem eq_slots_thm:
  s ≠ Empty ∧ s' ≠ Empty ⇒
  (eq_slots s s' ⇔ dec s = dec s')
Proof
  Cases_on`s`>>Cases_on`s'`>>
  simp[eq_slots_def,dec_def,dec_terms_GENLIST,eq_terms_slots_thm]>>
  rw[EQ_IMP_THM]>>
  metis_tac[LENGTH_GENLIST]
QED

Theorem in_hashset_slots_mk_hashset_slot:
  ∀ss s acc.
  LENGTH acc = splim ∧
  in_hashset_slots s (mk_hashset_slot ss acc) ⇒
  (∃s'. MEM s' ss ∧ eq_slots s s') ∨ in_hashset_slots s acc
Proof
  Induct>>
  rw[mk_hashset_slot_def]>>
  first_x_assum (drule_at (Pos last))>>
  impl_tac >- fs[]>>
  strip_tac
  >- metis_tac[]>>
  `hash_slot h < splim` by simp[hash_slot_thm,hash_constraint_lt_splim]>>
  gvs[in_hashset_slots_def,EL_LUPDATE]>>
  every_case_tac>>
  gvs[]>>
  metis_tac[]
QED

Definition fml_include_slots_def:
  fml_include_slots ss ss' =
  let hs = mk_hashset_slot ss (REPLICATE splim []) in
  EVERY (λs. in_hashset_slots s hs) ss'
End

Theorem fml_include_slots_thm:
  EVERY (λs. s ≠ Empty) ss ∧ EVERY (λs. s ≠ Empty) ss' ∧
  fml_include_slots ss ss' ⇒
  fml_include (MAP dec ss) (MAP dec ss')
Proof
  rw[fml_include_slots_def,fml_include_def,EVERY_MAP]>>
  gvs[EVERY_MEM]>>
  rw[]>>
  first_x_assum drule>>
  strip_tac>>
  drule_at (Pos last) in_hashset_slots_mk_hashset_slot>>
  simp[]>>
  strip_tac
  >- (
    simp[MEM_MAP]>>
    first_assum (irule_at Any)>>
    metis_tac[eq_slots_thm])>>
  `hash_slot x < splim` by simp[hash_slot_thm,hash_constraint_lt_splim]>>
  gvs[in_hashset_slots_def,EL_REPLICATE]
QED

(* Solutions and objective *)

Definition thresh_slot_def:
  thresh_slot g cs vs i len (r:num) =
  if i < len then
    let e:num = g (sub_unsafe cs i) (sub_unsafe vs i) in
    r ≤ e ∨ thresh_slot g cs vs (i+1) len (r - e)
  else F
Termination
  WF_REL_TAC`measure (λ(g,cs,vs,i,len,r). len - i)`
End

Definition eval_term_cv_def:
  eval_term_cv w (c:int) (v:num) = Num (ABS c) * eval_lit w (c < 0) v
End

Definition cube_term_cv_def:
  cube_term_cv cw (c:int) (v:num) =
  case cw v of
    NONE => 0
  | SOME b => Num (ABS c) * eval_lit (K b) (c < 0) v
End

Definition sat_slot_def:
  sat_slot w s =
  case s of
    Empty => T
  | Stored cs vs d mc b =>
    d ≤ 0 ∨ thresh_slot (eval_term_cv w) cs vs 0 (length cs) (Num d)
End

Definition cube_slot_def:
  cube_slot cw s =
  case s of
    Empty => T
  | Stored cs vs d mc b =>
    d ≤ 0 ∨ thresh_slot (cube_term_cv cw) cs vs 0 (length cs) (Num d)
End

Theorem UNCURRY_eval_term_cv:
  UNCURRY (eval_term_cv w) = eval_term w
Proof
  simp[FUN_EQ_THM,FORALL_PROD,eval_term_cv_def]
QED

Theorem UNCURRY_cube_term_cv:
  UNCURRY (cube_term_cv cw) =
  (λcv. case cw (SND cv) of NONE => 0 | SOME b => eval_term (K b) cv)
Proof
  simp[FUN_EQ_THM,FORALL_PROD,cube_term_cv_def]
QED

Definition check_obj_slots_def:
  check_obj_slots obj wm ss bopt =
  let wv = mk_obj_vec wm in
  let w = vec_lookup_d F wv in
  let new = eval_obj obj w in
  if EVERY (sat_slot w) ss
  then
    case bopt of NONE => SOME (new, w)
    | SOME b =>
      if b = new then SOME (new, w) else NONE
  else NONE
End

Definition check_sol_slots_def:
  check_sol_slots wm free ss =
  if EVERY (λ(v,b). lookup v free = NONE) wm then
    let cw = vec_lookup_d (SOME F) (mk_cube_vec wm free) in
    if EVERY (λ(v,b). cw v = SOME b) wm ∧ EVERY (cube_slot cw) ss then
      SOME (λv. case cw v of NONE => F | SOME b => b)
    else NONE
  else NONE
End

Theorem thresh_slot_thm:
  ∀g cs vs i len r.
  0 < r ⇒
  (thresh_slot g cs vs i len r ⇔
    r ≤ SUM (MAP (UNCURRY g)
      (GENLIST (λj. (sub cs (i+j), sub vs (i+j))) (len - i))))
Proof
  ho_match_mp_tac thresh_slot_ind>>
  rw[]>>
  simp[Once thresh_slot_def]>>
  Cases_on`i < len`
  >- (
    simp[]>>
    `len - i = SUC (len - (i+1))` by simp[]>>
    qpat_x_assum`len - i = _` SUBST1_TAC>>
    simp[GENLIST_CONS,combinTheory.o_DEF,ADD1]>>
    Cases_on`r ≤ g (sub cs i) (sub vs i)`>>
    gvs[])>>
  `len - i = 0` by simp[]>>
  qpat_x_assum`len - i = 0` SUBST1_TAC>>
  gvs[]
QED

Theorem sat_slot_thm:
  sat_slot w s ⇔ satisfies_npbc w (dec s)
Proof
  Cases_on`s`
  >- simp[sat_slot_def,dec_def,satisfies_npbc_def]>>
  rename1`Stored cs vs d mc b`>>
  simp[sat_slot_def,dec_def,dec_terms_GENLIST,satisfies_npbc_def]>>
  Cases_on`d ≤ 0`
  >- (simp[]>>intLib.ARITH_TAC)>>
  `0 < Num d` by intLib.ARITH_TAC>>
  simp[thresh_slot_thm,UNCURRY_eval_term_cv]>>
  intLib.ARITH_TAC
QED

Theorem cube_slot_thm:
  cube_slot cw s ⇔ check_cube cw (dec s)
Proof
  Cases_on`s`
  >- simp[cube_slot_def,dec_def,check_cube_correct]>>
  rename1`Stored cs vs d mc b`>>
  simp[cube_slot_def,dec_def,dec_terms_GENLIST,check_cube_correct]>>
  Cases_on`d ≤ 0`
  >- (simp[]>>intLib.ARITH_TAC)>>
  `0 < Num d` by intLib.ARITH_TAC>>
  simp[thresh_slot_thm,UNCURRY_cube_term_cv]>>
  intLib.ARITH_TAC
QED

Theorem check_obj_slots_thm:
  check_obj_slots obj wm ss bopt = check_obj obj wm (MAP dec ss) bopt
Proof
  simp[check_obj_slots_def,check_obj_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
    sat_slot_thm]
QED

Theorem check_sol_slots_thm:
  check_sol_slots wm free ss = check_sol wm free (MAP dec ss)
Proof
  simp[check_sol_slots_def,check_sol_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
    cube_slot_thm]
QED

(* Negation *)

(* Encoding with the largest variable, computed in the same pass as the
  largest coefficient *)
Definition max_cv_def:
  (max_cv [] (m:num) (mv:num) = (m,mv)) ∧
  (max_cv ((c:int,v:num)::l) m mv =
    let k = Num (ABS c) in
    max_cv l (if m < k then k else m) (if mv < v then v else mv))
End

Theorem max_cv_thm:
  ∀l m mv.
  max_cv l m mv = (MAX m (max_coeff l), MAX mv (max_var l))
Proof
  Induct>>
  simp[max_cv_def,max_coeff_def,max_var_def,FORALL_PROD]>>
  rw[MAX_DEF]
QED

Definition enc_mv_def:
  enc_mv ((l,d):npbc) b =
  let (mc,mv) = max_cv l 0 0 in
  (Stored (Vector (MAP FST l)) (Vector (MAP SND l)) d mc b, mv)
End

Theorem enc_mv_enc:
  enc_mv c b = (enc c b, max_var (FST c))
Proof
  PairCases_on`c`>>
  simp[enc_mv_def,max_cv_thm,enc_def]
QED

Definition sum_max_abs_def:
  (sum_max_abs [] (s:num) (m:num) (mv:num) = (s,m,mv)) ∧
  (sum_max_abs ((c:int,v:num)::l) s m mv =
    let k = Num (ABS c) in
    sum_max_abs l (s + k) (if m < k then k else m) (if mv < v then v else mv))
End

Theorem sum_max_abs_thm:
  ∀l s m mv.
  sum_max_abs l s m mv =
  (s + SUM (MAP (λi. Num (ABS (FST i))) l), MAX m (max_coeff l),
   MAX mv (max_var l))
Proof
  Induct>>
  simp[sum_max_abs_def,max_coeff_def,max_var_def,FORALL_PROD]>>
  rw[MAX_DEF]
QED

(* The negation and its largest variable *)
Definition neg_slot_def:
  neg_slot ((l,n):npbc) b =
  let (s,mc,mv) = sum_max_abs l 0 0 0 in
  (Stored (Vector (MAP (λ(c:int,v:num). -c) l)) (Vector (MAP SND l))
    (&s + 1 - n) mc b, mv)
End

Theorem max_coeff_negate:
  ∀l. max_coeff (MAP (λ(c,l). (-c,l)) l) = max_coeff l
Proof
  Induct>>simp[max_coeff_def,FORALL_PROD]
QED

Theorem neg_slot_enc:
  neg_slot c b = (enc (not c) b, max_var (FST c))
Proof
  PairCases_on`c`>>
  simp[neg_slot_def,sum_max_abs_thm,enc_def,not_def,MAP_MAP_o,
    combinTheory.o_DEF,LAMBDA_PROD,max_coeff_negate]>>
  simp[MAP_EQ_f,FORALL_PROD]
QED

(* Largest variable *)

Definition max_var_vs_def:
  max_var_vs vs i (m:num) =
  if i = 0 then m
  else
    let i1 = i - 1 in
    let n = sub_unsafe vs i1 in
    max_var_vs vs i1 (if m < n then n else m)
End

Definition slot_max_var_def:
  slot_max_var s =
  case s of
    Empty => 0
  | Stored cs vs d mc b => max_var_vs vs (length vs) 0
End

Theorem max_var_SNOC:
  ∀l. max_var (SNOC x l) = MAX (SND x) (max_var l)
Proof
  Induct>>
  simp[max_var_def,FORALL_PROD]>>
  PairCases_on`x`>>
  rw[max_var_def,MAX_DEF]
QED

Theorem max_var_vs_thm:
  ∀i m.
  i ≤ LENGTH l ⇒
  max_var_vs (Vector (MAP SND l)) i m = MAX m (max_var (TAKE i l))
Proof
  Induct
  >- simp[Once max_var_vs_def,max_var_def,MAX_DEF]>>
  rw[]>>
  simp[Once max_var_vs_def,mlvectorTheory.sub_def,EL_MAP]>>
  qpat_x_assum`∀m. _` (fn th => simp[th])>>
  `TAKE (SUC i) l = SNOC (EL i l) (TAKE i l)` by simp[TAKE_SUC_BY_TAKE]>>
  gvs[max_var_SNOC]>>
  rw[MAX_DEF]
QED

Theorem slot_max_var_enc[simp]:
  slot_max_var (enc c b) = max_var (FST c)
Proof
  PairCases_on`c`>>
  simp[slot_max_var_def,enc_def,mlvectorTheory.length_def,max_var_vs_thm]
QED


(* Negation of a stored slot, sharing its variable vector *)

(* The negated coefficients and the sum of their absolute values *)
Definition neg_terms_def:
  neg_terms cs i acc (s:num) =
  if i = 0 then (acc,s)
  else
    let i1 = i - 1 in
    let c:int = sub_unsafe cs i1 in
    neg_terms cs i1 ((-c)::acc) (s + Num (ABS c))
End

Definition not_slot_def:
  not_slot s b =
  case s of
    Empty => Empty
  | Stored cs vs d mc b0 =>
    let (ncs,s) = neg_terms cs (length cs) [] 0 in
    Stored (Vector ncs) vs (&s + 1 - d) mc b
End

Theorem neg_terms_thm:
  ∀i acc s.
  i ≤ LENGTH l ⇒
  neg_terms (Vector (MAP FST l)) i acc s =
  (MAP (λ(c,v). -c) (TAKE i l) ++ acc,
   s + SUM (MAP (λi. Num (ABS (FST i))) (TAKE i l)))
Proof
  Induct>>
  rw[Once neg_terms_def]>>
  `TAKE (SUC i) l = SNOC (EL i l) (TAKE i l)` by simp[TAKE_SUC_BY_TAKE]>>
  simp[mlvectorTheory.sub_def,EL_MAP,MAP_SNOC,SUM_SNOC]>>
  Cases_on`EL i l`>>
  simp[SNOC_APPEND]
QED

Theorem not_slot_enc:
  not_slot (enc c b0) b = enc (not c) b
Proof
  PairCases_on`c`>>
  simp[not_slot_def,enc_def,not_def,mlvectorTheory.length_def,
    neg_terms_thm,MAP_MAP_o,combinTheory.o_DEF,
    LAMBDA_PROD,max_coeff_negate]>>
  simp[MAP_EQ_f,FORALL_PROD]
QED

(* A new constraint, its negation (sharing the variable vector) and its
  largest variable *)
Definition neg_pos_slot_def:
  neg_pos_slot ((l,n):npbc) b1 b2 =
  let vs = Vector (MAP SND l) in
  let (s,mc,mv) = sum_max_abs l 0 0 0 in
  (Stored (Vector (MAP FST l)) vs n mc b1,
   Stored (Vector (MAP (λ(c:int,v:num). -c) l)) vs (&s + 1 - n) mc b2,
   mv)
End

Theorem neg_pos_slot_enc:
  neg_pos_slot c b1 b2 = (enc c b1, enc (not c) b2, max_var (FST c))
Proof
  PairCases_on`c`>>
  simp[neg_pos_slot_def,sum_max_abs_thm,enc_def,not_def,MAP_MAP_o,
    combinTheory.o_DEF,LAMBDA_PROD,max_coeff_negate]>>
  simp[MAP_EQ_f,FORALL_PROD]
QED

Definition fresh_vs_def:
  fresh_vs asv vs i =
  if i = 0 then T
  else
    let i1 = i - 1 in
    vec_lookup asv (sub_unsafe vs i1) = NONE ∧ fresh_vs asv vs i1
End

Definition check_fresh_aux_constr_slot_def:
  check_fresh_aux_constr_slot asv s =
  case s of
    Empty => T
  | Stored cs vs d mc b => fresh_vs asv vs (length vs)
End

Theorem fresh_vs_thm:
  ∀i.
  i ≤ LENGTH l ⇒
  (fresh_vs asv (Vector (MAP SND l)) i ⇔
    EVERY (λx. vec_lookup asv x = NONE) (MAP SND (TAKE i l)))
Proof
  Induct>>
  rw[Once fresh_vs_def]>>
  `TAKE (SUC i) l = SNOC (EL i l) (TAKE i l)` by simp[TAKE_SUC_BY_TAKE]>>
  simp[mlvectorTheory.sub_def,EL_MAP,MAP_SNOC,EVERY_SNOC]>>
  metis_tac[]
QED

Theorem check_fresh_aux_constr_slot_enc:
  check_fresh_aux_constr_slot asv (enc c b) ⇔
  check_fresh_aux_constr asv c
Proof
  PairCases_on`c`>>
  simp[check_fresh_aux_constr_slot_def,check_fresh_aux_constr_def,enc_def,
    mlvectorTheory.length_def,fresh_vs_thm]
QED

(* nfc is the slot of the negated constraint *)
Definition check_hash_goals_slot_def:
  check_hash_goals_slot nfc skipped r rsubs =
  EVERY (λ(id,cs).
      lookup id r ≠ NONE ∨
      EXISTS (λnc. imp_slot nfc (not nc)) cs ∨
      MEM id skipped)
    (enumerate 0 rsubs)
End

Theorem check_hash_goals_slot_enc:
  check_hash_goals_slot (enc (not c) b) skipped r rsubs ⇔
  check_hash_goals c skipped r rsubs
Proof
  simp[check_hash_goals_slot_def,check_hash_goals_def,check_hash_imp_def,
    imp_slot_enc]
QED

Theorem neg_sat_slot_test:
  neg_slot ([(2,1);(-3,4);(1,7)],2) T =
    (enc (not ([(2,1);(-3,4);(1,7)],2)) T, 7) ∧
  not_slot (enc ([(2,1);(-3,4);(1,7)],2) F) T =
    enc (not ([(2,1);(-3,4);(1,7)],2)) T ∧
  neg_pos_slot ([(2,1);(-3,4);(1,7)],2) T F =
    (enc ([(2,1);(-3,4);(1,7)],2) T, enc (not ([(2,1);(-3,4);(1,7)],2)) F,
     7) ∧
  enc_mv ([(2,1);(-3,7);(1,4)],2) T = (enc ([(2,1);(-3,7);(1,4)],2) T, 7) ∧
  slot_max_var (enc ([(2,1);(-3,7);(1,4)],2) T) = 7 ∧
  (sat_slot (λv. v = 1) (enc ([(2,1);(-3,4);(1,7)],4) T) ⇔
    satisfies_npbc (λv. v = 1) ([(2,1);(-3,4);(1,7)],4)) ∧
  (sat_slot (λv. v = 7) (enc ([(2,1);(-3,4);(1,7)],5) T) ⇔
    satisfies_npbc (λv. v = 7) ([(2,1);(-3,4);(1,7)],5))
Proof
  EVAL_TAC
QED
