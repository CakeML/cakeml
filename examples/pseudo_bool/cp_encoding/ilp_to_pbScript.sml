(*
  Formalization of the ILP to PB phase
*)
Theory ilp_to_pb
Libs
  preamble
Ancestors
  cp ilp pbc pbc_encode int_bitwise

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
  let bits = GENLIST (λi. (2**i,Pos (Bit X i))) h in
  if comp then
      (-(2**h),Pos(Sign X)):: bits
  else (bits:('a,'b) epb lin_term)
End

Theorem iSUM_GENLIST_eq_SUM_GENLIST[local]:
  iSUM (GENLIST (λi. &(2 ** i) * b2i (f i)) h) =
  & (SUM (GENLIST (λi. if f i then 2 ** i else 0) h))
Proof
  Induct_on ‘h’ \\ gvs [iSUM_def,GENLIST,SNOC_APPEND,SUM_APPEND]
  \\ Cases_on ‘f h’ \\ gvs [] \\ intLib.COOPER_TAC
QED

Theorem SUM_GENLIST_BIT:
  SUM (GENLIST (λi. if BIT i n then 2 ** i else 0) h) = n MOD 2 ** h
Proof
  Induct_on ‘h’ \\ gvs [GENLIST,SNOC_APPEND,SUM_APPEND]
  \\ pop_assum kall_tac
  \\ ‘∀k n. k MOD 2 ** (SUC n) = BITS n 0 k’ by
     gvs [bitTheory.BITS_def,bitTheory.DIV_2EXP_def,bitTheory.MOD_2EXP_def]
  \\ Cases_on ‘h’ \\ gvs []
  >- (gvs [bitTheory.BIT_def] \\ rw []
      \\ metis_tac [bitTheory.NOT_BITS2])
  \\ gvs [] \\ gvs [bitTheory.BITS_SUC_THM,bitTheory.SBIT_def]
QED

Theorem SUM_GENLIST_LE[local]:
  ∀g h. SUM (GENLIST (λi. if g i then 2 ** i else 0) h) ≤ 2 ** h
Proof
  gen_tac \\ Induct
  \\ gvs [GENLIST,SNOC_APPEND,SUM_APPEND]
  \\ rw [] \\ gvs [EXP]
QED

Theorem encode_ivar_sem_1:
  valid_assignment bnd wi ⇒
  eval_lin_term
    (reify_epb (wi,wb)) (encode_ivar bnd X) =
  wi X
Proof
  rw[encode_ivar_def]>>
  pairarg_tac>>gvs[eval_lin_term_def]>>
  reverse (rw[])>>
  simp[MAP_GENLIST,iSUM_def,eval_term_def,o_DEF,reify_epb_def]
  \\ gvs [valid_assignment_def]
  \\ last_x_assum $ qspec_then ‘X’ assume_tac
  \\ Cases_on ‘bnd X’ \\ gvs []
  >- (
    ‘~(q < 0)’ by gvs [bit_width_def]
    \\ `?n. wi X = &n` by intLib.ARITH_TAC
    \\ gvs [] \\ gvs [int_bit_def]
    \\ gvs [iSUM_GENLIST_eq_SUM_GENLIST]
    \\ drule_all bit_width_lemma1
    \\ gvs [SUM_GENLIST_BIT])
  \\ Cases_on ‘~(wi X < 0)’ \\ gvs [int_bit_def]
  \\ gvs [iSUM_GENLIST_eq_SUM_GENLIST]
  >- (
    `?n. wi X = &n` by intLib.ARITH_TAC
    \\ gvs [] \\ gvs [int_bit_def]
    \\ gvs [iSUM_GENLIST_eq_SUM_GENLIST]
    \\ drule_all bit_width_lemma1
    \\ gvs [SUM_GENLIST_BIT])
  \\ `?n. wi X = -&n` by (Cases_on ‘wi X’ \\ gvs [] \\ intLib.ARITH_TAC)
  \\ gvs [int_not_def]
  \\ ‘& n - 1 = & (n - 1) :int’ by intLib.COOPER_TAC \\ gvs []
  \\ irule (intLib.COOPER_PROVE “k ≤ n ∧ n = k + m ⇒ - & n + & k = -& m :int”)
  \\ conj_tac >- gvs [SUM_GENLIST_LE]
  \\ gvs []
  \\ drule_all bit_width_lemma2 \\ strip_tac
  \\ ‘SUM (GENLIST (λi. if ¬BIT i (n − 1) then 2 ** i else 0) h) =
      2 ** h - n’ suffices_by fs []
  \\ ‘SUM (GENLIST (λi. if ¬BIT i (n − 1) then 2 ** i else 0) h) =
      SUM (GENLIST (λi. if BIT i (2 ** h - n) then 2 ** i else 0) h)’
         suffices_by gvs [SUM_GENLIST_BIT]
  \\ AP_TERM_TAC
  \\ simp [GENLIST_FUN_EQ] \\ rpt strip_tac
  \\ qspecl_then [‘h’,‘i’,‘n’] mp_tac bitTheory.BIT_COMPLEMENT
  \\ Cases_on`n = 2 **h` \\ gvs[]
  \\ qspecl_then [‘h’,‘i’,‘1’] mp_tac bitTheory.BIT_COMPLEMENT
  \\ simp[ONE_MOD]
QED

Theorem num_of_bits_APPEND:
  ∀xs.
  num_of_bits (xs ++ ys) =
  num_of_bits xs + (2 ** LENGTH xs) * (num_of_bits ys)
Proof
  ho_match_mp_tac num_of_bits_ind>>
  rw[num_of_bits_def,EXP]
QED

Theorem num_of_bits_GENLIST:
  &num_of_bits (GENLIST f h)
  =
  iSUM (GENLIST (λi. &(2**i) * b2i (f i)) h)
Proof
 Induct_on`h`>>
 rw[num_of_bits_def,iSUM_def,GENLIST,SNOC_APPEND,num_of_bits_APPEND]>>
 fs[b2i_alt]>>rw[num_of_bits_def]>>
 intLib.ARITH_TAC
QED

Theorem encode_ivar_sem_2:
  eval_lin_term w (encode_ivar bnd X) =
  unreify_epb bnd w X
Proof
  rw[encode_ivar_def,unreify_epb_def]>>
  pairarg_tac>>gvs[eval_lin_term_def]>>
  reverse IF_CASES_TAC>>
  simp[MAP_GENLIST,iSUM_def,eval_term_def,o_DEF,int_of_bits_def]>>
  rw[num_of_bits_GENLIST]>>
  simp[int_not_def]>>
  ntac 2 (pop_assum kall_tac)>>
  Induct_on`h`>>
  fs[iSUM_def,GENLIST,SNOC_APPEND,b2i_alt,EXP]>>
  rw[]>>
  intLib.ARITH_TAC
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

