Theory word_lemmas
Ancestors words arithmetic integer_word
Libs wordsLib

Theorem a:
  a && m = a ==> a <=+ m
Proof
cheat
QED

Theorem c:
  n < dimindex(:'a) /\ 0<n ==>
  a:'a word && n2w(2**n-1) = (n-1><0) a
Proof
`2w:'a word = 1w<<1` by simp[addressTheory.word_LSL_n2w]
>>simp[word_extract_mask, n2w_sub, GSYM word_1_lsl]
QED

Theorem b:
  n < dimindex(:'a) /\
  a:'a word <+ n2w(2**n) ==>
  a && n2w(2**n-1) = a
Proof
`?na. a = n2w na /\ na < dimword(:'a)` by cheat(*metis_tac[n2w_w2n]*)
>>Cases_on‘n’>-simp[word_lo_n2w]
>>rw[c,word_extract_n2w,MIN_DEF,bitTheory.BITS_ZERO3,word_lo_n2w,dimword_def]
>>gvs[]
>>metis_tac[EXP_BASE_LT_MONO,LESS_TRANS,prove(``1n<2``,simp[])]
QED
