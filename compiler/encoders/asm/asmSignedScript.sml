(*
  Arithmetic facts shared by the signed ASM encoder proofs.
*)
Theory asmSigned
Ancestors
  asmProps integer_word
Libs
  preamble blastLib

Theorem signed_extend_i2w:
  dimindex (:'a) <= dimindex (:'b) ==>
  (sw2sw (w : 'a word) : 'b word) = i2w (w2i w)
Proof
  strip_tac
  \\ CONV_TAC (LAND_CONV (RAND_CONV
       (REWR_CONV (GSYM integer_wordTheory.i2w_w2i))))
  \\ simp [integer_wordTheory.sw2sw_i2w,
           integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le]
QED

Theorem signed_mul_wide_value:
  dimindex (:'a) <= dimindex (:'b) /\
  INT_MIN (:'b) <= w2i (a : 'a word) * w2i (b : 'a word) /\
  w2i a * w2i b <= INT_MAX (:'b) ==>
  w2i ((sw2sw a : 'b word) * sw2sw b) = w2i a * w2i b
Proof
  strip_tac
  \\ simp [signed_extend_i2w, integer_wordTheory.word_i2w_mul,
           integer_wordTheory.w2i_i2w]
QED

Theorem signed_product_64_bounds:
  INT_MIN (:128) <= w2i (a : word64) * w2i (b : word64) /\
  w2i a * w2i b <= INT_MAX (:128)
Proof
  map_every (mp_tac o Q.ISPEC `a : word64`)
    [integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le]
  \\ map_every (mp_tac o Q.ISPEC `b : word64`)
       [integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le]
  \\ simp [integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
           wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
           wordsTheory.dimword_def]
  \\ rpt strip_tac
  \\ `ABS (w2i a) < 9223372036854775809 /\
       ABS (w2i b) < 9223372036854775809` by (
    simp [integerTheory.INT_ABS_LT]
    \\ intLib.ARITH_TAC)
  \\ mp_tac (Q.SPECL
       [`ABS (w2i (a : word64))`, `9223372036854775809`,
        `ABS (w2i (b : word64))`, `9223372036854775809`]
       integerTheory.INT_LT_MUL2)
  \\ simp [integerTheory.INT_ABS_MUL, integerTheory.INT_ABS_LT]
  \\ intLib.ARITH_TAC
QED

Theorem signed_product_32_bounds:
  INT_MIN (:64) <= w2i (a : word32) * w2i (b : word32) /\
  w2i a * w2i b <= INT_MAX (:64)
Proof
  map_every (mp_tac o Q.ISPEC `a : word32`)
    [integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le]
  \\ map_every (mp_tac o Q.ISPEC `b : word32`)
       [integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le]
  \\ simp [integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
           wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
           wordsTheory.dimword_def]
  \\ rpt strip_tac
  \\ `ABS (w2i a) < 2147483649 /\
       ABS (w2i b) < 2147483649` by (
    simp [integerTheory.INT_ABS_LT]
    \\ intLib.ARITH_TAC)
  \\ mp_tac (Q.SPECL
       [`ABS (w2i (a : word32))`, `2147483649`,
        `ABS (w2i (b : word32))`, `2147483649`]
       integerTheory.INT_LT_MUL2)
  \\ simp [integerTheory.INT_ABS_MUL, integerTheory.INT_ABS_LT]
  \\ intLib.ARITH_TAC
QED

Theorem signed_low_64:
  (63 >< 0) (sw2sw (w : word64) : word128) = w
Proof
  blastLib.BBLAST_TAC
QED

Theorem signed_low_32:
  (31 >< 0) (sw2sw (w : word32) : word64) = w
Proof
  blastLib.BBLAST_TAC
QED

Theorem signed_high_fits_64:
  ((127 >< 64) (w : word128) = ((63 >< 0) w : word64) >> 63) <=>
  (w = sw2sw ((63 >< 0) w : word64))
Proof
  blastLib.BBLAST_TAC
QED

Theorem signed_high_fits_32:
  ((63 >< 32) (w : word64) = ((31 >< 0) w : word32) >> 31) <=>
  (w = sw2sw ((31 >< 0) w : word32))
Proof
  blastLib.BBLAST_TAC
QED

Theorem signed_mul_high_64:
  ((127 >< 64) ((sw2sw a : word128) * sw2sw b) =
     (a * b : word64) >> 63) <=>
  (w2i (a * b) = w2i a * w2i b)
Proof
  `(63 >< 0) ((sw2sw a : word128) * sw2sw b) = (a * b : word64)` by
    simp [wordsTheory.WORD_EXTRACT_OVER_MUL, signed_low_64]
  \\ `w2i ((sw2sw a : word128) * sw2sw b) = w2i a * w2i b` by (
    irule signed_mul_wide_value
    \\ simp [signed_product_64_bounds])
  \\ mp_tac (Q.ISPECL
       [`a * b : word64`,
        `(sw2sw (a : word64) : word128) * sw2sw (b : word64)`]
       (INST_TYPE [gamma |-> ``:128``] integer_wordTheory.w2i_11_lift))
  \\ mp_tac (Q.SPEC
       `(sw2sw (a : word64) : word128) * sw2sw (b : word64)`
       (GEN_ALL signed_high_fits_64))
  \\ simp [EQ_SYM_EQ]
QED

Theorem signed_mul_high_32:
  ((63 >< 32) ((sw2sw a : word64) * sw2sw b) =
     (a * b : word32) >> 31) <=>
  (w2i (a * b) = w2i a * w2i b)
Proof
  `(31 >< 0) ((sw2sw a : word64) * sw2sw b) = (a * b : word32)` by
    simp [wordsTheory.WORD_EXTRACT_OVER_MUL, signed_low_32]
  \\ `w2i ((sw2sw a : word64) * sw2sw b) = w2i a * w2i b` by (
    irule signed_mul_wide_value
    \\ simp [signed_product_32_bounds])
  \\ mp_tac (Q.ISPECL
       [`a * b : word32`,
        `(sw2sw (a : word32) : word64) * sw2sw (b : word32)`]
       (INST_TYPE [gamma |-> ``:64``] integer_wordTheory.w2i_11_lift))
  \\ mp_tac (Q.SPEC
       `(sw2sw (a : word32) : word64) * sw2sw (b : word32)`
       (GEN_ALL signed_high_fits_32))
  \\ simp [EQ_SYM_EQ]
QED

Theorem signed_dividend_64:
  w2i (((w >> 63) @@ (w : word64)) : word128) = w2i w
Proof
  `(((w >> 63) @@ (w : word64)) : word128) = sw2sw w` by
    blastLib.BBLAST_TAC
  \\ mp_tac (Q.ISPECL
       [`(((w >> 63) @@ (w : word64)) : word128)`, `w : word64`]
       (INST_TYPE [gamma |-> ``:128``] integer_wordTheory.w2i_11_lift))
  \\ simp []
QED

Theorem signed_dividend_parts_64:
  w2i ((w : word64) >> 63) * 18446744073709551616 + &w2n w = w2i w
Proof
  `(w : word64) >> 63 = if word_msb (w : word64) then -1w else 0w` by (
    Cases_on `word_msb (w : word64)`
    \\ fs [wordsTheory.word_msb_def]
    \\ blastLib.FULL_BBLAST_TAC)
  \\ Cases_on `word_msb (w : word64)`
  \\ fs [integer_wordTheory.w2i_eq_w2n, wordsTheory.WORD_MSB_INT_MIN_LS,
         wordsTheory.WORD_LS, wordsTheory.INT_MIN_def,
         wordsTheory.dimword_def]
  \\ intLib.ARITH_TAC
QED
