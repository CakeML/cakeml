(*
  Formalization of the ILP to PB phase
*)
Theory ilp_to_pb
Libs
  preamble
Ancestors
  cp ilp pbc pbc_encode int_bitwise int_bitwiseExtra

Datatype:
  epb =
  | Sign 'a    (* Two's complement sign-bit for X *)
  | Bit 'a num (* Bit X i is the i-th bit of X *)
  | Var 'b     (* An input Boolean variable *)
End

Definition reify_epb_def:
  reify_epb (wi:'a -> int,wb: 'b -> bool) epb ⇔
  case epb of
    Sign X => wi X < 0
  | Bit X n => int_bit n (wi X)
  | Var B => wb B
End

Definition unreify_epb_def:
  unreify_epb bnd (w: ('a,'b) epb -> bool) X =
  let (comp,h) = bit_width bnd X in
  let rest = (comp ∧ w (Sign X)) in
  let bs = GENLIST (λi. w (Bit X i)) h in
  int_of_bits (bs,rest)
End

Definition encode_ivar_def:
  encode_ivar bnd (X:'a) =
  let (comp,h) = bit_width bnd X in
  let bits = GENLIST (λi. (&(2**i),Pos (Bit X i))) h in
  if comp then
      (-&(2**h),Pos(Sign X)):: bits
  else (bits:('a,'b) epb lin_term)
End

Theorem encode_ivar_sem_2:
  eval_lin_term w (encode_ivar bnd X) =
  unreify_epb bnd w X
Proof
  rw[encode_ivar_def,unreify_epb_def]>>
  pairarg_tac>>gvs[]>>
  IF_CASES_TAC>>gvs[two_comp_eval]>>
  simp[eval_lin_term_def,MAP_GENLIST,eval_term_def,o_DEF,int_of_bits_def,
       GSYM num_of_bits_GENLIST]
QED

Theorem encode_ivar_sem_1:
  valid_assignment bnd wi ⇒
  eval_lin_term
    (reify_epb (wi,wb)) (encode_ivar bnd X) =
  wi X
Proof
  rw[encode_ivar_def]>>
  pairarg_tac>>gvs[]>>
  `?q r. bnd X = (q,r)` by metis_tac[PAIR]>>
  `q ≤ wi X ∧ wi X ≤ r` by (gvs[valid_assignment_def]>>metis_tac[])>>
  `-&(2 ** h) ≤ wi X ∧ wi X < &(2 ** h)` by (
    conj_tac
    >- (
      Cases_on`0 ≤ wi X` >- (`(0:int) ≤ &(2**h)` by simp[]>>intLib.ARITH_TAC)>>
      `?m. wi X = -&m ∧ 0 < m` by (Cases_on`wi X`>>gvs[]>>intLib.ARITH_TAC)>>
      `q < 0` by intLib.ARITH_TAC>>
      `bit_width bnd X = (T,h)` by gvs[bit_width_def]>>
      `q ≤ -&m` by intLib.ARITH_TAC>>
      drule_all bit_width_lemma2>>
      rw[]>>intLib.ARITH_TAC)>>
    Cases_on`wi X < 0` >- (`(0:int) ≤ &(2**h)` by simp[]>>intLib.ARITH_TAC)>>
    `?n. wi X = &n` by intLib.ARITH_TAC>>
    `&n ≤ r` by intLib.ARITH_TAC>>
    drule_all bit_width_lemma1>>
    rw[]>>intLib.ARITH_TAC)>>
  reverse IF_CASES_TAC
  >- (
    `~(wi X < 0)` by (gvs[bit_width_def]>>intLib.ARITH_TAC)>>
    `?n. wi X = &n` by (Cases_on`wi X`>>gvs[])>>
    gvs[eval_lin_term_def,MAP_GENLIST,iSUM_def,eval_term_def,o_DEF,
        reify_epb_def,int_bit_def]>>
    gvs[iSUM_GENLIST_eq_SUM_GENLIST]>>
    drule_all bit_width_lemma1>>
    gvs[SUM_GENLIST_BIT])>>
  simp[two_comp_eval,reify_epb_def]>>
  irule two_comp_reconstruct>>gvs[]
QED

Definition mul_lin_term_def:
  mul_lin_term d ls =
    MAP (λ(c:int,x). (c*d,x)) ls
End

Definition encode_iconstraint_one_def:
  encode_iconstraint_one bnd (is,bs,c) =
    (
    pbc$GreaterEqual,
    FLAT
      (MAP (λ(d,X).
        mul_lin_term d (encode_ivar bnd X)) is) ++
    MAP (λ(d,l). (d,map_lit Var l)) bs,
    c):(('a,'b) epb pbc)
End

Theorem eval_lin_term_mul_lin_term[simp]:
  ∀c.
  eval_lin_term w (mul_lin_term d c) =
  d * eval_lin_term w c
Proof
  simp[mul_lin_term_def,eval_lin_term_def]>>
  Induct>>rw[iSUM_def]>>
  pairarg_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem encode_iconstraint_one_sem_1:
  valid_assignment bnd wi ⇒
  iconstraint_sem iconstr (wi,wb) =
  satisfies_pbc (reify_epb (wi,wb))
   (encode_iconstraint_one bnd iconstr)
Proof
  `∃is bs c. iconstr = (is,bs,c)`
    by metis_tac[PAIR] >>
  rw[encode_iconstraint_one_def,satisfies_pbc_def,iconstraint_sem_def,eval_lin_term_def,eval_ilin_term_def]>>
  qmatch_goalsub_abbrev_tac`A + B ≥ _ ⇔ X + Y ≥ _`>>
  `A = X ∧ B = Y` suffices_by simp[]>>
  unabbrev_all_tac>>rw[]
  >- (
    simp[iSUM_FLAT,MAP_FLAT,MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    simp[GSYM eval_lin_term_def]>>
    pairarg_tac>>gvs[]>>
    simp[encode_ivar_sem_1])
  >- (
    simp[MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    pairarg_tac>>gvs[]>>
    rename1`MEM (_,l) _`>>
    Cases_on`l`>>
    gvs[lit_def,map_lit_def,reify_epb_def])
QED

Theorem encode_iconstraint_one_sem_2:
  satisfies_pbc w (encode_iconstraint_one bnd iconstr) =
  iconstraint_sem iconstr (unreify_epb bnd w, λx. w (Var x))
Proof
  `∃is bs c. iconstr = (is,bs,c)`
    by metis_tac[PAIR] >>
  rw[encode_iconstraint_one_def,satisfies_pbc_def,iconstraint_sem_def,eval_lin_term_def,eval_ilin_term_def]>>
  qmatch_goalsub_abbrev_tac`A + B ≥ _ ⇔ X + Y ≥ _`>>
  `A = X ∧ B = Y` suffices_by simp[]>>
  unabbrev_all_tac>>rw[]
  >- (
    simp[iSUM_FLAT,MAP_FLAT,MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    simp[GSYM eval_lin_term_def]>>
    pairarg_tac>>gvs[]>>
    simp[encode_ivar_sem_2])
  >- (
    simp[MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    pairarg_tac>>gvs[]>>
    rename1`MEM (_,l) _`>>
    Cases_on`l`>>
    gvs[lit_def,map_lit_def])
QED

Definition encode_iconstraint_all_def:
  encode_iconstraint_all bnd cs =
    MAP (encode_iconstraint_one bnd) cs
End

Theorem encode_iconstraint_all_sem_1:
  valid_assignment bnd wi ⇒
  EVERY (\c. iconstraint_sem c (wi,wb)) ics =
  satisfies (reify_epb (wi,wb))
   (set (encode_iconstraint_all bnd ics))
Proof
  rw[satisfies_def,EVERY_MEM,encode_iconstraint_all_def,MEM_MAP,PULL_EXISTS]>>
  metis_tac[encode_iconstraint_one_sem_1]
QED

Theorem encode_iconstraint_all_sem_2:
  satisfies w
   (set (encode_iconstraint_all bnd ics)) =
  EVERY (\c. iconstraint_sem c (unreify_epb bnd w, λx. w (Var x))) ics
Proof
  rw[satisfies_def,EVERY_MEM,encode_iconstraint_all_def,MEM_MAP,PULL_EXISTS]>>
  metis_tac[encode_iconstraint_one_sem_2]
QED

Definition encode_bound_var_def:
  encode_bound_var bnd X =
  let (lb,ub) = bnd X in
  let bX = encode_ivar bnd (X:'a) in
  [
    (pbc$GreaterEqual,bX,lb);
    (pbc$LessEqual,bX,ub);
  ]
End

Theorem encode_bound_var_sem_1:
  valid_assignment bnd wi ⇒
  satisfies (reify_epb (wi,wb))
   (set (encode_bound_var bnd X))
Proof
  simp[satisfies_def,encode_bound_var_def]>>rw[]>>
  pairarg_tac>>gvs[satisfies_pbc_def]>>
  DEP_REWRITE_TAC[encode_ivar_sem_1]>>
  gvs[valid_assignment_def]>>
  first_x_assum drule>>simp[]>>
  intLib.ARITH_TAC
QED

Definition encode_bound_all_def:
  encode_bound_all bnd Xs =
  FLAT (MAP (encode_bound_var bnd) Xs)
End

Theorem encode_bound_all_sem_1:
  valid_assignment bnd wi ⇒
  satisfies (reify_epb (wi,wb)) (set (encode_bound_all bnd Xs))
Proof
  rw[satisfies_def,encode_bound_all_def,MEM_FLAT,MEM_MAP]>>
  drule encode_bound_var_sem_1>>
  rw[satisfies_def]>>
  metis_tac[]
QED

(* For simplicity, we set all unused vars to have range (0,0) *)
Theorem encode_bound_all_sem_2:
  (∀X. bnd X ≠ (0,0) ⇒ MEM X Xs) ∧
  satisfies w (set (encode_bound_all bnd Xs)) ⇒
  valid_assignment bnd (unreify_epb bnd w)
Proof
  simp[valid_assignment_def]>>
  strip_tac>>
  strip_tac>>
  Cases_on`bnd x = (0,0)`
  >- (
    simp[unreify_epb_def,bit_width_def,bits_of_int_def]>>
    EVAL_TAC)>>
  rpt gen_tac>>strip_tac>>
  first_x_assum drule>>
  fs[satisfies_def,encode_bound_all_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,encode_bound_var_def]>>
  strip_tac>> first_x_assum drule>>
  strip_tac>>
  gvs[satisfies_pbc_def,SF DNF_ss,encode_ivar_sem_2]>>
  intLib.ARITH_TAC
QED

