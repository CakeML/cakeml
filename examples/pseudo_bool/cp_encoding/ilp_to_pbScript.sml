(*
  Formalization of the ILP to PB phase
*)
open preamble ilpTheory pbcTheory pbc_encodeTheory int_bitwiseTheory cpTheory;

val _ = new_theory "ilp_to_pb";

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

Definition bit_width_def:
  bit_width bnd X =
    let (lb,ub) = bnd X in
     (lb < 0,
      if lb < 0 then
        MAX (LENGTH (FST (bits_of_int lb)))
            (LENGTH (FST (bits_of_int ub)))
      else LENGTH (FST (bits_of_int ub)))
End

Definition encode_ivar_def:
  encode_ivar bnd (X:'a) =
  let (comp,h) = bit_width bnd X in
  let bits = GENLIST (λi. (2**i,Pos (Bit X i))) h in
  if comp then
      (-(2**h),Pos(Sign X)):: bits
  else (bits:('a,'b) epb lin_term)
End

Triviality iSUM_GENLIST_eq_SUM_GENLIST:
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

Triviality LESS_EXP_MAX:
  (k:num) < 2 ** MAX m n ⇔ k < 2 ** m ∨ k < 2 ** n
Proof
  rw [MAX_DEF]
  \\ eq_tac \\ rw []
  \\ irule LESS_LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Triviality LESS_EQ_EXP_MAX:
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

Triviality bit_width_lemma1:
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

Triviality bit_width_lemma2:
  bit_width bnd X = (T,h) ∧ bnd X = (q,r) ∧ q ≤ -&n ⇒
    n < 2**h ∨
    (n = 2**h ∧ q = -&n)
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
  \\ reverse (Cases_on`n = k`)
  >- (
    DISJ1_TAC
    \\ gvs [LESS_EXP_MAX]
    \\ intLib.ARITH_TAC)
  >- (
    rw[MAX_DEF]
    \\ `2 ** lbb < 2** ubb` by
      (match_mp_tac bitTheory.TWOEXP_MONO>>
      simp[])
    \\ simp[])
QED

Triviality SUM_GENLIST_LE:
  ∀g h. SUM (GENLIST (λi. if g i then 2 ** i else 0) h) ≤ 2 ** h
Proof
  gen_tac \\ Induct
  \\ gvs [GENLIST,SNOC_APPEND,SUM_APPEND]
  \\ rw [] \\ gvs [EXP]
QED

Theorem encode_ivar_sem:
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
  >- (
    ‘SUM (GENLIST (λi. if ¬BIT i (n − 1) then 2 ** i else 0) h) =
        2 ** h - n’ suffices_by fs []
    \\ ‘SUM (GENLIST (λi. if ¬BIT i (n − 1) then 2 ** i else 0) h) =
        SUM (GENLIST (λi. if BIT i (2 ** h - n) then 2 ** i else 0) h)’
           suffices_by gvs [SUM_GENLIST_BIT]
    \\ AP_TERM_TAC
    \\ simp [GENLIST_FUN_EQ] \\ rpt strip_tac
    \\ qspecl_then [‘h’,‘i’,‘n’] mp_tac bitTheory.BIT_COMPLEMENT
    \\ gvs [] )
  >- (
    ‘SUM (GENLIST (λi. if ¬BIT i (n − 1) then 2 ** i else 0) h) = 0’ by (
      simp[SUM_eq_0,MEM_GENLIST,PULL_EXISTS]
      \\ rpt strip_tac
      \\ qspecl_then [‘h’,‘i’,‘1’] mp_tac bitTheory.BIT_COMPLEMENT
      \\ simp[ONE_MOD])
    \\ simp[] )
QED

Definition mul_lin_term_def:
  mul_lin_term d ls =
    MAP (λ(c:int,x). (c*d,x)) ls
End

Definition encode_iconstraint_def:
  encode_iconstraint bnd (is,bs,c) =
    (
    GreaterEqual,
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

Theorem encode_iconstraint_sem:
  valid_assignment bnd wi ⇒
  iconstraint_sem iconstr (wi,wb) =
  satisfies_pbc (reify_epb (wi,wb))
   (encode_iconstraint bnd iconstr)
Proof
  `∃is bs c. iconstr = (is,bs,c)`
    by metis_tac[PAIR] >>
  rw[encode_iconstraint_def,satisfies_pbc_def,iconstraint_sem_def,eval_lin_term_def,eval_ilin_term_def]>>
  qmatch_goalsub_abbrev_tac`A + B ≥ _ ⇔ X + Y ≥ _`>>
  `A = X ∧ B = Y` suffices_by simp[]>>
  unabbrev_all_tac>>rw[]
  >- (
    simp[iSUM_FLAT,MAP_FLAT,MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    simp[GSYM eval_lin_term_def]>>
    pairarg_tac>>gvs[]>>
    simp[encode_ivar_sem])
  >- (
    simp[MAP_MAP_o,o_DEF]>>
    match_mp_tac iSUM_MAP_eq>>
    rw[]>>
    pairarg_tac>>gvs[]>>
    rename1`MEM (_,l) _`>>
    Cases_on`l`>>
    gvs[lit_def,map_lit_def,reify_epb_def])
QED

val _ = export_theory();
