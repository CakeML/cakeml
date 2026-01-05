Theory add_carry
Ancestors words arithmetic integer_word
Libs wordsLib

Definition add_carry_def:
  add_carry (a:'a word) (b:'a word) (carry:'a word) =
  let c:'a word = if carry = 0w then 0w else 1w in
  let sum = a+b in
  let t1:'a word = if sum <+ b then 1w else 0w in
  let sum_c = sum+c in
  let t2:'a word = if sum_c <+ c then 1w else 0w in
  (sum_c, t1||t2)
End

Theorem add_carry_aux:
  a+b<+b:'a word ⇒ w2n a + w2n b >= dimword(:'a)
Proof
  rw[word_add_def,WORD_LO]
  >>fs[MATCH_MP ADD_MOD ZERO_LT_dimword]
  >>`w2n b <= w2n a + w2n b` by decide_tac
  >>`(w2n a + w2n b) MOD dimword (:α) < w2n a + w2n b` by decide_tac
  >>metis_tac[prove(“a MOD n < a ⇒ a>=n”, strip_tac>>CCONTR_TAC>>fs[])]
QED

Theorem add_carry_aux':
  ¬(a+b<+b:'a word) ⇒ w2n a + w2n b < dimword(:'a) 
Proof
  `w2n a + w2n b >= dimword(:'a) ⇒ a+b<+b:'a word` suffices_by metis_tac[NOT_LESS,GREATER_EQ]
  >>rw[word_add_def,WORD_LO]
  >>`w2n a < dimword(:'a) ∧ w2n b < dimword(:'a)` by metis_tac[w2n_lt]
  >>subgoal `(w2n a + w2n b) MOD dimword(:'a) + dimword(:'a) = w2n a + w2n b`
  >-(
    `w2n a + w2n b < dimword(:'a)+dimword(:'a)` by decide_tac
    >>`0<dimword(:'a)` by irule ZERO_LT_dimword
    >>drule_all_then assume_tac$prove(“0<c ∧ a+b>=c ∧ a+b<c+c ⇒ (a+b)DIV c = 1”, strip_tac>>`a+b=1*c+(a+b-c) ∧ a+b-c<c` by decide_tac>>metis_tac[DIV_UNIQUE])
    >>qspec_then `w2n a + w2n b` assume_tac $ MATCH_MP DIVISION ZERO_LT_dimword
    >>gvs[]
  )
  >>decide_tac
QED

Theorem add_carry_thm:
  add_carry a b c = (sum, c_out) ⇒
  sum = FST (add_with_carry (a,b,c≠0w)) ∧ c_out = if FST(SND(add_with_carry (a,b,c≠0w))) then 1w else 0w
Proof
  simp[add_carry_def,add_with_carry_def]
  >>(Cases_on`c=0w`>>simp[])
  >-(
    strip_tac
    >>conj_tac
    >-metis_tac[word_add_def]
    >>(Cases_on`a+b<+b`>>fs[])
    >-(dxrule add_carry_aux>>simp[])
    >-(dxrule add_carry_aux'>>simp[])
  )
  >>strip_tac
  >>conj_tac
  >-gvs[word_add_def]
  >>(Cases_on`a+b<+b`>>fs[])
  >-(
    dxrule_then assume_tac add_carry_aux
    >>gvs[]
    >>(IF_CASES_TAC>>simp[])
  )
  >>dxrule_then assume_tac add_carry_aux'
  >>(Cases_on`a+b+1w<+1w`>>fs[])
  >-(dxrule_then assume_tac add_carry_aux>>gvs[word_add_def])
  >-(dxrule_then assume_tac add_carry_aux'>>gvs[word_add_def])
End

Theorem word_bits_1bit:
  (i--i)a = if word_bit i a then 1w else 0w
Proof
  Cases_on `dimindex(:'a)<=i`
  >-simp[WORD_BIT_BITS,WORD_BITS_ZERO3]
  >>`∃n. a = n2w n` by metis_tac[n2w_w2n]
  >>gvs[]
  >>simp[word_bit_n2w,bitTheory.BIT_def,word_bits_n2w,MIN_DEF]
  >>`(if i < dimindex (:α) − 1 then i else (dimindex (:α) − 1)) = i` by (IF_CASES_TAC>>gvs[])
  >>pop_assum(fn eq=>simp[eq])
  >>`BITS i i n = if BITS i i n = 1 then 1 else 0` suffices_by metis_tac[n2w_11]
  >>metis_tac[bitTheory.BIT_def,bitTheory.NOT_BIT]
QED

Theorem lsr_msb:
  a:'a word >>> (dimindex(:'a)-1) = if word_msb a then 1w else 0w
Proof
  simp[word_lsr_n2w,word_msb_def,word_bits_1bit]
  >>`dimindex(:'a)-1<dimindex(:'a)` by simp[DIMINDEX_GT_0]
  >>metis_tac[word_bit]
QED

Definition add_overflow_def:
  add_overflow (a:'a word) (b:'a word) =
  let sum = a+b in
  (sum, (~(a⊕b) && (b⊕sum)) >>> (dimindex(:'a)-1))
End 

Definition sub_overflow_def:
  sub_overflow (a:'a word) (b:'a word) =
  let diff = a-b in
  (diff, ((a⊕b) && ~(b⊕diff)) >>> (dimindex(:'a)-1))
End

Theorem word_msb_xor:
  word_msb(a⊕b) = ¬(word_msb a ⇔ word_msb b)
Proof
  simp[word_msb_def,word_bit]
  >>`∃na nb. a = n2w na ∧ b = n2w nb` by metis_tac[n2w_w2n]
  >>gvs[word_xor_n2w,word_bit_n2w,bitTheory.BITWISE_THM]
QED

Theorem add_overflow_thm:
  add_overflow a b = (sum, ovf) ⇒
  sum = a+b ∧ ovf = (if w2i (a+b) ≠ w2i a + w2i b then 1w else 0w)
Proof
  simp[add_overflow_def]
  >>strip_tac
  >>gvs[lsr_msb,overflow,WORD_MSB_1COMP,word_msb_xor]
  >>(Cases_on`word_msb a`>>Cases_on`word_msb b`>>Cases_on`word_msb(a+b)`>>simp[])
QED

Theorem sub_overflow_thm:
  sub_overflow a b = (diff, ovf) ⇒
  diff = a-b ∧ ovf = (if w2i (a-b) ≠ w2i a - w2i b then 1w else 0w)
Proof
  simp[sub_overflow_def,sub_overflow]
  >>strip_tac
  >>gvs[lsr_msb,WORD_MSB_1COMP,word_msb_xor]
  >>(Cases_on`word_msb a`>>Cases_on`word_msb b`>>Cases_on`word_msb(a+(-1w)*b)`>>simp[])
QED
