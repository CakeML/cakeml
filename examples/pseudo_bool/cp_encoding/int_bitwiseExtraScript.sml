(*
  Reusable lemmas and definitions about representing natural numbers and
  integers as (little-endian) bit lists: round-trip, zero-padding, two's
  complement bit-width. Shared infrastructure for the CP encodings, and a
  candidate for upstreaming into int_bitwiseTheory.
*)
Theory int_bitwiseExtra
Libs
  preamble
Ancestors
  int_bitwise pbc pbc_encode

(* twos-complement representation *)
Definition bit_width_def:
  bit_width bnd X =
    let (lb,ub) = bnd X in
     (lb < 0,
      if lb < 0 then
        MAX (LENGTH (FST (bits_of_int lb)))
            (LENGTH (FST (bits_of_int ub)))
      else LENGTH (FST (bits_of_int ub)))
End

Theorem LESS_EXP_MAX[local]:
  (k:num) < 2 ** MAX m n ⇔ k < 2 ** m ∨ k < 2 ** n
Proof
  rw [MAX_DEF]
  \\ eq_tac \\ rw []
  \\ irule LESS_LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem LESS_EQ_EXP_MAX[local]:
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

Theorem bit_width_lemma1:
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

Theorem bit_width_lemma2:
  bit_width bnd X = (T,h) ∧ bnd X = (q,r) ∧ q ≤ -&n ⇒
    n ≤ 2**h
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
  \\ gvs [LESS_EQ_EXP_MAX]
QED

Theorem iSUM_GENLIST_eq_SUM_GENLIST:
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

Theorem SUM_GENLIST_LE:
  ∀g h. SUM (GENLIST (λi. if g i then 2 ** i else 0) h) ≤ 2 ** h
Proof
  gen_tac \\ Induct
  \\ gvs [GENLIST,SNOC_APPEND,SUM_APPEND]
  \\ rw [] \\ gvs [EXP]
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

(* Reading off the first h bits of any natural number n via BIT recovers
   n MOD 2 ** h. The reification of proof-only binary integers uses this:
   bit i is defined for ALL i (BIT i n) even though the encoding only ever
   references finitely many, so no bit-width bound need be threaded. *)
Theorem num_of_bits_GENLIST_BIT:
  num_of_bits (GENLIST (λi. BIT i n) h) = n MOD 2 ** h
Proof
  `(&num_of_bits (GENLIST (λi. BIT i n) h)):int = &(n MOD 2 ** h)` suffices_by simp[]>>
  once_rewrite_tac[num_of_bits_GENLIST]>>
  once_rewrite_tac[iSUM_GENLIST_eq_SUM_GENLIST]>>
  simp[SUM_GENLIST_BIT]
QED

(* bit b of the value of a bit list (b in range) is the b-th element *)
Theorem BIT_num_of_bits_EL:
  ∀L b. b < LENGTH L ⇒ (BIT b (num_of_bits L) ⇔ EL b L)
Proof
  Induct >> simp[] >>
  gen_tac >> Cases_on`b` >> simp[]
  >- (Cases_on`h`>>
      simp[num_of_bits_def,bitTheory.BIT0_ODD,arithmeticTheory.ODD_ADD,
           arithmeticTheory.ODD_MULT])>>
  strip_tac>>
  simp[GSYM bitTheory.BIT_DIV2]>>
  `num_of_bits (h::L) DIV 2 = num_of_bits L` by
    (Cases_on`h`>>
     simp[num_of_bits_def,arithmeticTheory.ADD_DIV_RWT,arithmeticTheory.MULT_DIV])>>
  simp[]>>metis_tac[]
QED

(* bit b of n is the b-th element of its little-endian expansion *)
Theorem BIT_bits_of_num:
  ∀n b. BIT b n ⇔ b < LENGTH (bits_of_num n) ∧ EL b (bits_of_num n)
Proof
  ho_match_mp_tac bits_of_num_ind>>rw[]>>
  Cases_on`n = 0`>>simp[Once bits_of_num_def]>>
  `bits_of_num n = ODD n::bits_of_num (n DIV 2)` by simp[Once bits_of_num_def]>>
  pop_assum SUBST_ALL_TAC>>
  Cases_on`b`>>simp[bitTheory.BIT0_ODD,GSYM bitTheory.BIT_DIV2]>>
  metis_tac[]
QED

(* the little-endian expansion of n < 2^w fits in w bits *)
Theorem LENGTH_bits_of_num_LE:
  ∀w n. n < 2 ** w ⇒ LENGTH (bits_of_num n) ≤ w
Proof
  Induct>>rw[]>>simp[Once bits_of_num_def]>>rw[]>>
  first_x_assum irule>>gvs[EXP,DIV_LT_X]
QED

(* the b-th literal of the binary guard for j is bit b of j *)
Theorem EL_PAD_RIGHT_bits:
  b < w ⇒ EL b (PAD_RIGHT F w (bits_of_num j)) = BIT b j
Proof
  rw[PAD_RIGHT,EL_APPEND_EQN]
  >- (simp[Once BIT_bits_of_num])>>
  simp[EL_GENLIST]>>simp[Once BIT_bits_of_num]
QED

(* two naturals below 2^w agreeing on bits [0,w) are equal *)
Theorem BIT_eq_lt_2EXP:
  a < 2 ** w ∧ b < 2 ** w ∧ (∀k. k < w ⇒ (BIT k a ⇔ BIT k b)) ⇒ a = b
Proof
  rw[]>>
  `GENLIST (λk. BIT k a) w = GENLIST (λk. BIT k b) w` by
    simp[GENLIST_FUN_EQ]>>
  `a MOD 2 ** w = b MOD 2 ** w` by metis_tac[num_of_bits_GENLIST_BIT]>>
  gvs[arithmeticTheory.LESS_MOD]
QED

(* eval of a signed bit-sum is the int_of_bits of its bit assignment *)
Theorem two_comp_eval:
  eval_lin_term w
    ((-&(2 ** h),Pos s)::GENLIST (λb. (&(2 ** b),Pos (f b))) h) =
  int_of_bits (GENLIST (λb. w (f b)) h, w s)
Proof
  rw[eval_lin_term_def]>>
  simp[MAP_GENLIST,iSUM_def,eval_term_def,eval_lit_def,o_DEF,int_of_bits_def]>>
  rw[num_of_bits_GENLIST]>>
  simp[int_not_def]>>
  Induct_on`h`>>
  fs[iSUM_def,GENLIST,SNOC_APPEND,b2i_alt,EXP]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* a signed value in the h-bit two's-complement range round-trips through its
   bit decomposition: reconstruction from its bits recovers the value *)
Theorem two_comp_reconstruct:
  -&(2 ** h) ≤ v ∧ v < &(2 ** h) ⇒
  int_of_bits (GENLIST (λb. int_bit b v) h, v < 0) = v
Proof
  strip_tac>>simp[int_of_bits_def]>>IF_CASES_TAC
  >- (simp[int_bit_def,MAP_GENLIST,combinTheory.o_DEF,num_of_bits_GENLIST_BIT]>>
      `0 ≤ int_not v` by (simp[int_not_def]>>intLib.ARITH_TAC)>>
      `Num (int_not v) < 2 ** h` by (simp[int_not_def]>>intLib.COOPER_TAC)>>
      simp[arithmeticTheory.LESS_MOD]>>
      `&Num (int_not v) = int_not v` by metis_tac[integerTheory.INT_OF_NUM]>>
      simp[int_not_not])>>
  simp[int_bit_def,MAP_GENLIST,combinTheory.o_DEF,num_of_bits_GENLIST_BIT]>>
  `?n. v = &n` by intLib.ARITH_TAC>>gvs[]>>
  `n < 2**h` by intLib.ARITH_TAC>>
  simp[arithmeticTheory.LESS_MOD]
QED
