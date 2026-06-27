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

(* bits_of_num (n:num), zero-padded (with F) on the right to the number of
   bits required for (bnd:num). When n ≤ bnd this is bits_of_num n widened to
   the common bit-width LENGTH (bits_of_num bnd). *)
Definition bits_of_num_bnd_def:
  bits_of_num_bnd (n:num) bnd =
  PAD_RIGHT F (LENGTH (bits_of_num bnd)) (bits_of_num n)
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

Theorem num_of_bits_bits_of_num:
  ∀n. num_of_bits (bits_of_num n) = n
Proof
  ho_match_mp_tac int_bitwiseTheory.bits_of_num_ind>>rw[]>>
  simp[Once int_bitwiseTheory.bits_of_num_def]>>
  rw[int_bitwiseTheory.num_of_bits_def]>>
  Cases_on‘ODD n’>>
  gvs[int_bitwiseTheory.num_of_bits_def,bitTheory.DIV_MULT_THM2,
    arithmeticTheory.MOD_2,arithmeticTheory.ODD_EVEN]
QED

Theorem num_of_bits_F:
  ∀fs. EVERY (λx. ¬x) fs ⇒ num_of_bits fs = 0
Proof
  Induct>>rw[int_bitwiseTheory.num_of_bits_def]
QED

Theorem num_of_bits_GENLIST_F:
  num_of_bits (GENLIST (K F) k) = 0
Proof
  irule num_of_bits_F>>simp[EVERY_GENLIST]
QED

Theorem num_of_bits_PAD_RIGHT_F:
  num_of_bits (PAD_RIGHT F w xs) = num_of_bits xs
Proof
  rw[listTheory.PAD_RIGHT,num_of_bits_APPEND,
    num_of_bits_GENLIST_F]
QED

Theorem LENGTH_bits_of_num_LE:
  ∀m n. n < 2 ** m ⇒ LENGTH (bits_of_num n) ≤ m
Proof
  Induct>>rw[]
  >- (gvs[]>>simp[Once int_bitwiseTheory.bits_of_num_def])>>
  simp[Once int_bitwiseTheory.bits_of_num_def]>>rw[]>>
  last_x_assum irule>>
  gvs[arithmeticTheory.EXP,arithmeticTheory.DIV_LT_X]
QED

Theorem LENGTH_bits_of_num_mono:
  ∀n bnd. n ≤ bnd ⇒ LENGTH (bits_of_num n) ≤ LENGTH (bits_of_num bnd)
Proof
  rw[]>>irule LENGTH_bits_of_num_LE>>
  `bnd < 2 ** LENGTH (bits_of_num bnd)` by simp[LESS_LENGTH_bits_of_num]>>
  simp[]
QED

Theorem num_of_bits_bits_of_num_bnd:
  ∀n bnd. n ≤ bnd ⇒ num_of_bits (bits_of_num_bnd n bnd) = n
Proof
  rw[bits_of_num_bnd_def,num_of_bits_PAD_RIGHT_F,num_of_bits_bits_of_num]
QED

Theorem LENGTH_bits_of_num_bnd:
  ∀n bnd. n ≤ bnd ⇒ LENGTH (bits_of_num_bnd n bnd) = LENGTH (bits_of_num bnd)
Proof
  rw[bits_of_num_bnd_def,listTheory.PAD_RIGHT]>>
  `LENGTH (bits_of_num n) ≤ LENGTH (bits_of_num bnd)` by
    simp[LENGTH_bits_of_num_mono]>>
  simp[]
QED
