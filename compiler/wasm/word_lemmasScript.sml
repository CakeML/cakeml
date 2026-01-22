Theory word_lemmas
Ancestors words arithmetic integer_word
Libs wordsLib

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

Theorem word_msb_xor:
  word_msb(a⊕b) = ¬(word_msb a ⇔ word_msb b)
Proof
  simp[word_msb_def,word_bit]
  >>`∃na nb. a = n2w na ∧ b = n2w nb` by metis_tac[n2w_w2n]
  >>gvs[word_xor_n2w,word_bit_n2w,bitTheory.BITWISE_THM]
QED

Theorem word_and_pow2m1_aux:
  n < dimindex(:'a) /\ 0<n ==>
  a:'a word && n2w(2**n-1) = (n-1><0) a
Proof
`2w:'a word = 1w<<1` by simp[addressTheory.word_LSL_n2w]
>>simp[word_extract_mask, n2w_sub, GSYM word_1_lsl]
QED

Theorem word_and_pow2m1:
  n < dimindex(:'a) /\
  a:'a word <+ n2w(2**n) ==>
  a && n2w(2**n-1) = a
Proof
`∃na. a = n2w na /\ na < dimword(:'a)` by metis_tac[n2w_w2n,w2n_lt]
>>Cases_on‘n’>-simp[word_lo_n2w]
>>rw[word_and_pow2m1_aux,word_extract_n2w,MIN_DEF,bitTheory.BITS_ZERO3,word_lo_n2w,dimword_def]
>>gvs[]
>>metis_tac[EXP_BASE_LT_MONO,LESS_TRANS,prove(“1n<2”,simp[])]
QED
