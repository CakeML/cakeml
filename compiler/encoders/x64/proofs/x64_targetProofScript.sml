(*
  Prove `encoder_correct` for x64
*)
open HolKernel Parse boolLib bossLib
open asmLib x64_stepLib x64_targetTheory;

val () = new_theory "x64_targetProof"

val () = wordsLib.guess_lengths()

val () = Parse.temp_overload_on ("reg", ``\r. Zr (total_num2Zreg r)``)

(* some lemmas ---------------------------------------------------------- *)

val Zreg2num_num2Zreg_imp =
   fst (Thm.EQ_IMP_RULE (SPEC_ALL x64Theory.Zreg2num_num2Zreg))

val const_lem1 =
   blastLib.BBLAST_PROVE
     ``!c: word64. ((63 >< 31) c = 0w: 33 word) ==>
                   0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw``

val const_lem2 = Q.prove(
   `!c: word64.
       [(7 >< 0) c; (15 >< 8) c; (23 >< 16) c; (31 >< 24) c]: word8 list =
       [( 7 ><  0) (w2w c : word32); (15 ><  8) (w2w c : word32);
        (23 >< 16) (w2w c : word32); (31 >< 24) (w2w c : word32)]`,
   simp [] \\ blastLib.BBLAST_TAC)

val const_lem3 =
   Drule.LIST_CONJ
      [blastLib.BBLAST_PROVE
         ``word_bit 3 (r: word4) \/ ((3 >< 3) r = 1w: word1) ==>
           ((1w: word1) @@ (v2w [r ' 2; r ' 1; r ' 0]: word3) = r)``,
       blastLib.BBLAST_PROVE
         ``~word_bit 3 (r: word4) \/ ((3 >< 3) r = 0w: word1) ==>
           ((0w: word1) @@ (v2w [r ' 2; r ' 1; r ' 0]: word3) = r)``,
       bitstringLib.v2w_n2w_CONV ``v2w [T] : word1``,
       bitstringLib.v2w_n2w_CONV ``v2w [F] : word1``]

val const_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          ((63 >< 31) c = 0w: 33 word) ==>
          ((31 >< 0) (0xFFFFFFFFw && sw2sw (w2w c: word32) : word64) = c)``

val jump_lem1 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFFBw /\
          c + 0xFFFFFFFFFFFFFFFBw <= 0x7FFFFFFFw``

val jump_lem2 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFFBw): word32) = c - 5w)``

val jump_lem3 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF7w /\
          c + 0xFFFFFFFFFFFFFFF7w <= 0x7FFFFFFFw``

val jump_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF6w /\
          c + 0xFFFFFFFFFFFFFFF6w <= 0x7FFFFFFFw``

val jump_lem5 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF4w /\
          c + 0xFFFFFFFFFFFFFFF4w <= 0x7FFFFFFFw``

val jump_lem6 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF3w /\
          c + 0xFFFFFFFFFFFFFFF3w <= 0x7FFFFFFFw``

val loc_lem1 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000007w <= c /\ c <= 0x80000006w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF9w /\
          c + 0xFFFFFFFFFFFFFFF9w <= 0x7FFFFFFFw``

val loc_lem2 = blastLib.BBLAST_PROVE ``(a || 8w) <> 0w: word4``

val loc_lem3 =
   blastLib.BBLAST_PROVE
      ``(v2w [r ' 3]: word1) @@ (v2w [r ' 2; r ' 1; r ' 0]: word3) = r: word4``

val loc_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000007w <= c /\ c <= 0x80000006w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF9w): word32) = c - 7w)``

val binop_lem1 = Q.prove(
   `((if b then [x] else []) <> []) = b`,
   rw [])

val binop_lem5 = Q.prove(
   `!c: word64. [(7 >< 0) c]: word8 list = [I (w2w c : word8)]`,
   simp [] \\ blastLib.BBLAST_TAC)

val binop_lem6 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
          (sw2sw (w2w c: word8) = c)``

val binop_lem7 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw ==>
          (sw2sw (w2w c: word32) = c)``

val binop_lem9b = Q.prove(
   `!n. n < 64 ==>
        (0xFFFFFFFFFFFFFF80w: word64) <= n2w n /\ n2w n <= (0x7Fw: word64)`,
   lrw [wordsTheory.word_le_n2w]
   \\ `n < 2 ** 63` by simp []
   \\ simp [bitTheory.NOT_BIT_GT_TWOEXP]
   )

val binop_lem9 = Q.prove(
   `!i: word64 n.
       n < 64 /\ Abbrev (i = n2w n) ==>
       0xFFFFFFFFFFFFFF80w <= i /\ i <= 0x7Fw /\ i <+ 64w /\
       (w2n (w2w i: word6) = n)`,
   Cases
   \\ lrw [wordsTheory.word_le_n2w, wordsTheory.word_lo_n2w,
           wordsTheory.w2w_n2w]
   \\ `n' < 18446744073709551616` by decide_tac
   \\ fs [markerTheory.Abbrev_def]
   \\ `n' < 2 ** 63` by simp []
   \\ simp [bitTheory.NOT_BIT_GT_TWOEXP]
   )

val binop_lem10 =
   blastLib.BBLAST_PROVE
      ``!i: word64.
          i <+ 64w ==>
          ((5 >< 0) (sw2sw (w2w i : word8): word64) = w2w i: word6)``

val binop_lem10b =
  binop_lem10
  |> Q.SPEC `n2w n`
  |> Q.DISCH `n < 64`
  |> SIMP_RULE (srw_ss()++ARITH_ss)
       [wordsTheory.word_lo_n2w, arithmeticTheory.LESS_MOD,
        blastLib.BBLAST_PROVE ``(w2w a : word8) = (7 >< 0) (a : word64)``]

val mem_lem1 = Q.prove(
   `!a n s state.
       target_state_rel x64_target s state /\ n < 16 /\ n <> 4 /\ n <> 5 /\
       s.regs n + a IN s.mem_domain ==>
       (state.MEM (state.REG (num2Zreg n) + a) = s.mem (s.regs n + a))`,
   rw [asmPropsTheory.target_state_rel_def, x64_target_def, x64_config_def]
   )

val mem_lem2 = Q.prove(
   `!a n s state.
    target_state_rel x64_target s state /\ n < 16 /\ n <> 4 /\ n <> 5 /\
    s.regs n + a IN s.mem_domain /\
    s.regs n + a + 1w IN s.mem_domain /\
    s.regs n + a + 2w IN s.mem_domain /\
    s.regs n + a + 3w IN s.mem_domain ==>
    (read_mem32 state.MEM (state.REG (num2Zreg n) + a) =
     s.mem (s.regs n + a + 3w) @@ s.mem (s.regs n + a + 2w) @@
     s.mem (s.regs n + a + 1w) @@ s.mem (s.regs n + a))`,
   rw [asmPropsTheory.target_state_rel_def, x64_target_def, x64_config_def,
       x64_stepTheory.read_mem32_def]
   )

val mem_lem3 = Q.prove(
   `!a n s state.
    target_state_rel x64_target s state /\ n < 16 /\ n <> 4 /\ n <> 5 /\
    s.regs n + a IN s.mem_domain /\
    s.regs n + a + 1w IN s.mem_domain /\
    s.regs n + a + 2w IN s.mem_domain /\
    s.regs n + a + 3w IN s.mem_domain /\
    s.regs n + a + 4w IN s.mem_domain /\
    s.regs n + a + 5w IN s.mem_domain /\
    s.regs n + a + 6w IN s.mem_domain /\
    s.regs n + a + 7w IN s.mem_domain ==>
    (read_mem64 state.MEM (state.REG (num2Zreg n) + a) =
     s.mem (s.regs n + a + 7w) @@ s.mem (s.regs n + a + 6w) @@
     s.mem (s.regs n + a + 5w) @@ s.mem (s.regs n + a + 4w) @@
     s.mem (s.regs n + a + 3w) @@ s.mem (s.regs n + a + 2w) @@
     s.mem (s.regs n + a + 1w) @@ s.mem (s.regs n + a))`,
   rw [asmPropsTheory.target_state_rel_def, x64_target_def, x64_config_def,
       x64_stepTheory.read_mem64_def]
   )

val mem_lem4 =
   blastLib.BBLAST_PROVE
      ``!r: word4. (v2w [r ' 3] : word1) @@ ((2 >< 0) r : word3) = r``

val mem_lem5 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
          (sw2sw (w2w c: word8) = c)``

val mem_lem6 = Q.prove(
   `!r. (2 >< 0) r <> (4w: word3) /\ (2 >< 0) r <> (5w: word3) ==>
        (r = RegNot4or5 r)`,
   rw [x64_stepTheory.RegNot4or5_def])

val mem_lem7 = Q.prove(
   `!r. (2 >< 0) r <> (4w: word3) ==> (r = RegNot4 r)`,
   rw [x64_stepTheory.RegNot4_def])

val mem_lem8 = Q.prove(
   `!r:word4 n.
       ~(3 < n) /\ Abbrev (r = n2w n) ==>
       num2Zreg (w2n r) <> RSP /\
       num2Zreg (w2n r) <> RBP /\
       num2Zreg (w2n r) <> RSI /\
       num2Zreg (w2n r) <> RDI`,
   wordsLib.Cases_word_value
   \\ rw [x64Theory.num2Zreg_thm]
   \\ Cases_on `3 < n`
   \\ simp [markerTheory.Abbrev_def]
   )

(*
val mem_lem9 = Q.prove(
   `!n r: word4.
      n < 16 /\ n <> 4 /\ Abbrev (r = n2w n) /\ ((2 >< 0) r = 4w: word3) ==>
      (zR12 = num2Zreg n)`,
   wordsLib.Cases_on_word_value `r`
   \\ rw []
   \\ rfs [markerTheory.Abbrev_def]
   \\ pop_assum (SUBST_ALL_TAC o SYM)
   \\ simp [x64Theory.num2Zreg_thm]
   )

val mem_lem10 = Q.prove(
   `!n r: word4.
      ~(n < 16 /\ n <> 4 /\ Abbrev (r = n2w n) /\ ((3 >< 3) r = (0w: word1)) /\
        ((2 >< 0) r = (4w: word3)))`,
   wordsLib.Cases_on_word_value `r`
   \\ rw [markerTheory.Abbrev_def]
   \\ Cases_on `n < 16`
   \\ simp []
   )
*)

val mem_lem11 =
   blastLib.BBLAST_PROVE
      ``!r: word4. ((3 >< 3) r = (1w: word1)) ==> r ' 3``

val mem_lem12 =
   blastLib.BBLAST_PROVE
      ``!r: word4. ((3 >< 3) r = (0w: word1)) ==> ~r ' 3``

val mem_lem13 =
   blastLib.BBLAST_PROVE
      ``!a: word4. v2w [a ' 2; a ' 1; a ' 0] = (2 >< 0) a : word3``

val mem_lem14 = Q.prove(
  `!w m :word64 -> word8.
   (w + 7w =+ b7)
     ((w + 6w =+ b6)
        ((w + 5w =+ b5)
           ((w + 4w =+ b4)
              ((w + 3w =+ b3)
                 ((w + 2w =+ b2)
                    ((w + 1w =+ b1)
                       ((w =+ b0) m))))))) =
   (w =+ b0)
     ((w + 1w =+ b1)
        ((w + 2w =+ b2)
           ((w + 3w =+ b3)
              ((w + 4w =+ b4)
                 ((w + 5w =+ b5)
                    ((w + 6w =+ b6)
                       ((w + 7w =+ b7) m)))))))`,
   rw [combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
   \\ rw []
   \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
   )

val mem_lem15 = Q.prove(
  `!w v:word64 m :word64 -> word8.
   (w + 3w =+ b3) ((w + 2w =+ b2) ((w + 1w =+ b1) ((w =+ b0) m))) =
   (w =+ b0) ((w + 1w =+ b1) ((w + 2w =+ b2) ((w + 3w =+ b3) m)))`,
   srw_tac [wordsLib.WORD_EXTRACT_ss]
      [combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM]
   \\ rw []
   \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
   )

val cmp_lem1 =
   blastLib.BBLAST_PROVE
      ``(!a b: word64. (a + -1w * b = 0w) = (a = b)) /\
        (!a b: word64. (-1w * b + a = 0w) = (a = b))``

val cmp_lem2 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFFBw): word32) = c - 5w)``

val cmp_lem3 = Thm.CONJ
  (blastLib.BBLAST_PROVE
    ``!a b: word64.
       ((-1w * b + a) ' 63 <=/=>
        (a ' 63 <=/=> b ' 63) /\ ((-1w * b + a) ' 63 <=/=> a ' 63)) <=> a < b``)
  (blastLib.BBLAST_PROVE
    ``!a b: word64.
       ((a + -1w * b) ' 63 <=/=>
        (a ' 63 <=/=> b ' 63) /\ ((a + -1w * b) ' 63 <=/=> a ' 63)) <=> a < b``)

val cmp_lem4 = Q.prove(
   `!w: word64 a b.
      (7 >< 0) w :: a :: b : word8 list = I (w2w w : word8) :: a :: b`,
   simp [] \\ blastLib.BBLAST_TAC)

val cmp_lem5 = Q.prove(
   `!c: word64.
       0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
       (((if (7 >< 7) c = 1w: word8 then 0xFFFFFFFFFFFFFF00w else 0w) ||
         ((7 >< 0) c)) = c)`,
   rw []
   \\ blastLib.FULL_BBLAST_TAC
   )

val cmp_lem6 = Q.prove(
   `!c: word64.
       0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw ==>
       (((if (31 >< 31) c = 1w: word32 then 0xFFFFFFFF00000000w else 0w) ||
         (31 >< 0) c) = c)`,
   rw []
   \\ blastLib.FULL_BBLAST_TAC
   )

val cmp_lem7 = Q.prove(
   `!rm. is_rax rm = (Zr RAX = rm)`,
   Cases \\ rw [x64Theory.is_rax_def]
   \\ CASE_TAC
   \\ simp []
   )

val cmp_lem8 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF7w) : word32) + 9w = c)``

val cmp_lem9 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF6w) : word32) + 10w = c)``

val cmp_lem10 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF4w) : word32) + 12w = c)``

val cmp_lem11 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF3w) : word32) + 13w = c)``

val cmp_lem12 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw
            (((31 >< 24) (c + 0xFFFFFFFFFFFFFFF4w) : word8) @@
             ((23 >< 16) (c + 0xFFFFFFFFFFFFFFF4w) : word8) @@
             ((15 >< 8) (c + 0xFFFFFFFFFFFFFFF4w) : word8) @@
             (w2w (c + 0xFFFFFFFFFFFFFFF4w) : word8)) + 12w = c)``

val cmp_lem13 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw ==>
          (sw2sw
            (((31 >< 24) c : word8) @@ ((23 >< 16) c : word8) @@
             ((15 >< 8) c : word8) @@ (w2w c : word8)) = c)``

val cmp_lem14 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw
            (((31 >< 24) (c + 0xFFFFFFFFFFFFFFF3w) : word8) @@
             ((23 >< 16) (c + 0xFFFFFFFFFFFFFFF3w) : word8) @@
             ((15 >< 8) (c + 0xFFFFFFFFFFFFFFF3w) : word8) @@
             (w2w (c + 0xFFFFFFFFFFFFFFF3w) : word8)) + 13w = c)``

val adc_lem1 =
  Thm.CONJ (bitstringLib.v2w_n2w_CONV ``v2w [F] : word64``)
           (bitstringLib.v2w_n2w_CONV ``v2w [T] : word64``)

val adc_lem2 = blastLib.BBLAST_PROVE ``a <+ 1w : word64 <=> (a = 0w)``

val overflow_lem =
  blastLib.BBLAST_PROVE ``!a: word64. word_bit 63 a = word_msb a``

val is_rax = Q.prove(
   `!n. n < 16 ==> ((RAX = num2Zreg n) = (n = 0))`,
   rw [] \\ fs [wordsTheory.NUMERAL_LESS_THM]
   )

val is_rdx = Q.prove(
   `!n. n < 16 ==> ((RDX = num2Zreg n) = (n = 2))`,
   rw [] \\ fs [wordsTheory.NUMERAL_LESS_THM]
   )

val xmm_reg = Q.prove(
  `(!n. n < 8 ==> ((3 >< 3) (n2w n : word4) = 0w : word1)) /\
   (!n. n < 8 ==> ((3 >< 3) (w2w (n2w n : word3) : word4) = 0w : word1)) /\
   (!n. n < 8 ==> ~word_bit 3 (n2w n : word4)) /\
   (!n. n < 16 /\ ~(n < 8) ==> ((3 >< 3) (n2w n : word4) = 1w : word1)) /\
   !n. n < 16 /\ ~(n < 8) ==> word_bit 3 (n2w n : word4)`,
  rpt strip_tac
  >- fs [wordsTheory.NUMERAL_LESS_THM]
  >- fs [wordsTheory.NUMERAL_LESS_THM]
  >- (fs [wordsTheory.NUMERAL_LESS_THM] \\ rfs [])
  \\ pop_assum mp_tac
  \\ fs [wordsTheory.NUMERAL_LESS_THM]
  )

val Zreg2num_num2Zreg_8 =
  x64Theory.Zreg2num_num2Zreg
  |> Drule.SPEC_ALL
  |> Q.DISCH `r < 8`
  |> SIMP_RULE arith_ss []
  |> Drule.GEN_ALL

val xmm_reg2 = Q.prove(
  `(!n r : word4.
      n < 8 /\ Abbrev (r = n2w n) ==>
      (RexReg (F, v2w [r ' 2; r ' 1; r ' 0]) = num2Zreg n)) /\
   (!n r : word4.
      ~(n < 8) /\ n < 16 /\ Abbrev (r = n2w n) ==>
      (RexReg (T, v2w [r ' 2; r ' 1; r ' 0]) = num2Zreg n))`,
   rpt strip_tac
   \\ full_simp_tac (srw_ss()++bitstringLib.v2w_n2w_ss)
        [Abbr `r`, wordsTheory.NUMERAL_LESS_THM, x64Theory.RexReg_def]
   \\ fs []
   )

val xmm_reg3 = Q.prove(
  `!n. n < 8 ==> (w2w (n2w n : word3) = n2w n : word4)`,
  rpt strip_tac \\ fs [wordsTheory.NUMERAL_LESS_THM]
  )

val extract_double =
  blastLib.BBLAST_PROVE
   ``(!w: word64 x: word128. (63 >< 0) (bit_field_insert 63 0 w x) = w) /\
     (!w1: word64 w2: word64. (63 >< 0) ((w1 @@ w2) : word128) = w2) /\
     (!w1: word32 w2: word32 x: word128.
       (63 >< 0)
         ((bit_field_insert 63 0 ((w1 @@ w2) : word64) x) << 96 >>> 96) =
       w2w w2 : word64) /\
     !w: word128. (31 >< 0) ((63 >< 0) w : word64) = (31 >< 0) w : word32``

val fp_abs = Q.prove(
  `!w. fp64_abs w = (0x7FFFFFFFFFFFFFFFw && w)`,
  simp [machine_ieeeTheory.fp64_abs_def, machine_ieeeTheory.fp64_to_float_def,
        binary_ieeeTheory.float_abs_def, machine_ieeeTheory.float_to_fp64_def]
  \\ blastLib.BBLAST_TAC
  )

val fp_neg = Q.prove(
  `!w. fp64_negate w = (0x8000000000000000w ?? w)`,
  simp [machine_ieeeTheory.fp64_negate_def,
        machine_ieeeTheory.fp64_to_float_def,
        binary_ieeeTheory.float_negate_def,
        machine_ieeeTheory.float_to_fp64_def]
  \\ blastLib.BBLAST_TAC
  )

val fp_compare = Q.prove(
  `(!a b. fp64_equal a b = (fp64_compare a b = EQ)) /\
   (!a b. fp64_lessThan a b = (fp64_compare a b = LT)) /\
   (!a b. fp64_lessEqual a b =
          ((fp64_compare a b = LT) \/ (fp64_compare a b = EQ)))`,
  simp [machine_ieeeTheory.fp64_equal_def,
        machine_ieeeTheory.fp64_lessEqual_def,
        machine_ieeeTheory.fp64_lessThan_def,
        machine_ieeeTheory.fp64_compare_def,
        binary_ieeeTheory.float_equal_def,
        binary_ieeeTheory.float_less_than_def,
        binary_ieeeTheory.float_less_equal_def]
  \\ rpt strip_tac
  \\ CASE_TAC
  )

val fp_to_int_lem = Q.prove(
  `!i w : word32.
      (w2i w = i) ==> -0x80000000 <= i /\ i <= 0x7FFFFFFF`,
  ntac 3 strip_tac
  \\ assume_tac
       (integer_wordTheory.w2i_le
        |> Q.ISPEC `w : word32`
        |> SIMP_RULE (srw_ss()) [])
  \\ assume_tac
       (integer_wordTheory.w2i_ge
        |> Q.ISPEC `w : word32`
        |> SIMP_RULE (srw_ss()) [])
  \\ rfs []
  )

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open x64Theory
   in
      [x64_enc_def, x64_ast_def, x64_bop_def, x64_cmp_def, x64_sh_def,
       x64_encode_def, encode_def, encode_sse_def, encode_sse_binop_def,
       xmm_mem_to_rm_def, e_gen_rm_reg_def,
       e_ModRM_def, e_opsize_def, rex_prefix_def, e_opc_def, e_rm_imm8_def,
       e_opsize_imm_def, not_byte_def, e_rax_imm_def, e_rm_imm_def,
       e_imm_8_32_def, e_imm_def, e_imm8_def, e_imm16_def, e_imm32_def,
       e_imm64_def, Zsize_width_def, Zbinop_name2num_thm,
       asmSemTheory.is_test_def, total_num2Zreg_def
       ]
   end;

val enc_rwts =
  [x64_config, Zreg2num_num2Zreg_imp, binop_lem1, loc_lem1, loc_lem2,
   const_lem1, const_lem2, binop_lem9b, jump_lem1, jump_lem3, jump_lem4,
   jump_lem5, jump_lem6, cmp_lem7, is_rax, x64_asm_ok, xmm_reg, xmm_reg3,
   utilsLib.mk_cond_rand_thms [``asmSem$asm_state_failed``]] @
  encode_rwts @ asmLib.asm_rwts;

val enc_ok_rwts =
  x64_asm_ok :: encode_rwts @ [asmPropsTheory.enc_ok_def, x64_config];

(* some custom tactics ---------------------------------------------------- *)

val rfs = rev_full_simp_tac (srw_ss());

local
   val rip = ``state.RIP``
   val pc = ``s.pc: word64``
   val w8 = ``:word8``
   fun add_offset x i =
     if i = 0 then x
     else wordsSyntax.mk_word_add (x, wordsSyntax.mk_wordii (i, 64))
   fun bytes_in_memory_thm (m, n) =
      let
         val offset_pc = add_offset (add_offset rip m)
         val (b, r) =
            List.tabulate
              (n, fn i =>
                    let
                      val b = Term.mk_var ("b" ^ Int.toString i, w8)
                      val rip' = offset_pc i
                    in
                      (b,
                       ``(state.MEM ^rip' = ^b) /\ ^rip' IN s.mem_domain``)
                    end) |> ListPair.unzip
          val l = listSyntax.mk_list (b, w8)
          val r = boolSyntax.list_mk_conj r
      in
         Q.prove(
            `!s state.
               target_state_rel x64_target s state /\
               bytes_in_memory ^(add_offset pc m) ^l s.mem s.mem_domain ==>
               (state.exception = NoException) /\
               (state.exception = NoException) /\
               ~state.MXCSR.FZ /\ state.MXCSR.PM /\ state.MXCSR.UM /\
                state.MXCSR.OM /\ state.MXCSR.ZM /\ state.MXCSR.DM /\
                state.MXCSR.IM /\ ~state.MXCSR.DAZ /\ (state.MXCSR.RC = 0w) /\
               ^r`,
            rw [asmPropsTheory.target_state_rel_def, x64_target_def, x64_ok_def,
                x64_config_def, miscTheory.bytes_in_memory_def]
            \\ rfs []
         ) |> Thm.GENL b
      end
   val bytes_in_memory_thm =
     utilsLib.cache 20 (Lib.pair_compare (Int.compare, Int.compare))
       bytes_in_memory_thm
   fun bytes_in_memory offset l =
      Drule.SPECL l
        (bytes_in_memory_thm (Option.getOpt (offset, 0), List.length l))
   fun P s = Lib.mem s ["v", "wv", "zflag", "cflag", "oflag", "sflag", "pflag"]
   fun gen_v thm =
      let
         val vars = Term.free_vars (Thm.concl thm)
         val l = List.filter (P o fst o Term.dest_var) vars
      in
         Thm.GENL l thm
      end
   fun step state =
      gen_v o Q.INST [`s` |-> state] o Drule.DISCH_ALL o x64_stepLib.x64_step
   val is_x64_decode = #4 (HolKernel.syntax_fns1 "x64" "x64_decode")
   val is_x64_next = #4 (HolKernel.syntax_fns1 "x64_target" "x64_next")
   val find_x64_decode = Lib.total (HolKernel.find_term is_x64_decode)
   val get_offset = Option.map (wordsSyntax.uint_of_word o snd) o
                    (Lib.total wordsSyntax.dest_word_add)
   val x64_next =
     Drule.GEN_ALL (Thm.AP_THM x64_targetTheory.x64_next_def ``s:x64_state``)
in
   val is_bytes_in_memory = Lib.can asmLib.dest_bytes_in_memory
   fun bytes_in_memory_tac (asl, g) =
      (case List.mapPartial asmLib.strip_bytes_in_memory asl of
          [l] => imp_res_tac (bytes_in_memory NONE l)
        | _ => NO_TAC) (asl, g)
   fun basic_next_state_tac (asl, g) =
      (case List.mapPartial asmLib.strip_bytes_in_memory asl of
          [] => NO_TAC
        | l => simp [x64_targetTheory.x64_next_def]
               \\ assume_tac (step `ms` (hd l))) (asl, g)
   fun next_state_tac (asl, g) =
     (let
         val x as (pc, l, _, _) =
            List.last
              (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
         val x_tm = asmLib.mk_bytes_in_memory x
         val l = fst (listSyntax.dest_list l)
         val th = bytes_in_memory (get_offset pc) l
         val (tac, the_state) =
            case asmLib.find_env is_x64_next g of
               SOME (t, tm) =>
                 let
                    val etm = ``env ^t ^tm : x64_state``
                 in
                    (`!a. a IN s1.mem_domain ==> ((^etm).MEM a = ms.MEM a)`
                     by (qpat_x_assum `!i:num s:x64_state. P`
                           (qspecl_then [`^t`, `^tm`]
                              (strip_assume_tac o SIMP_RULE (srw_ss())
                              [set_sepTheory.fun2set_eq]))
                            \\ simp []),
                     etm)
                 end
             | NONE => (all_tac, ``ms:x64_state``)
      in
         imp_res_tac th
         \\ tac
         \\ assume_tac (step `^the_state` l)
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss())
              [combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ Tactical.PAT_X_ASSUM x_tm kall_tac
         \\ SUBST1_TAC (Thm.SPEC the_state x64_next)
         \\ simp [Zreg2num_num2Zreg_8,
                  combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ TRY (Q.PAT_X_ASSUM `NextStateX64 qq = qqq` kall_tac)
      end
      handle List.Empty => FAIL_TAC "next_state_tac: empty") (asl, g)
end;

local
  fun is_n2w_var tm =
    case Lib.total wordsSyntax.dest_n2w tm of
       SOME (v, _) => Term.is_var v
     | NONE => false
  fun mk_abbrev t n =
    let
      val v = "r" ^ (if n = 0 then "" else Int.toString n)
    in
      boolSyntax.mk_eq (Term.mk_var (v, Term.type_of t), t)
    end
  fun abbreviate_n2w (asl, g) =
    (case List.mapPartial asmLib.strip_bytes_in_memory asl of
       [l] =>
         let
           val ts = List.map (HolKernel.find_terms is_n2w_var) l
                    |> List.concat |> Lib.op_mk_set aconv
           val ts =
             List.foldl
               (fn (t, (n, a)) => (n + 1, mk_abbrev t n :: a)) (0, []) ts
         in
           MAP_EVERY (fn tm => qabbrev_tac `^tm`) (snd ts)
         end
     | _ => NO_TAC) (asl, g)
  fun unabbrev_all_tac (asl, g) =
    MAP_EVERY
      (fn (v, tm) => Q.UNABBREV_TAC `^(Term.mk_var (v, Term.type_of tm))`)
      (List.mapPartial (Lib.total markerSyntax.dest_abbrev) asl) (asl, g)
  val sub_overflow = SIMP_RULE (srw_ss()) [] integer_wordTheory.sub_overflow
in
  fun next_tac l =
    let
      val i = List.length (List.filter (fn i => 0 < i) l)
      val n = numLib.term_of_int i
    in
      EXISTS_TAC n
      \\ SIMP_TAC std_ss [asmPropsTheory.asserts_eval, x64_proj_def,
                          asmPropsTheory.interference_ok_def,
                          asmPropsTheory.asserts2_eval]
      \\ NTAC 2 STRIP_TAC
      \\ Q.PAT_ABBREV_TAC `instr = x64_enc aa`
      \\ NO_STRIP_REV_FULL_SIMP_TAC
           (srw_ss()++ARITH_ss++boolSimps.LET_ss) enc_rwts
      \\ NO_STRIP_FULL_SIMP_TAC std_ss []
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()) []
      \\ qunabbrev_tac `instr`
      \\ abbreviate_n2w
      \\ imp_res_tac xmm_reg2
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()) []
      \\ MAP_EVERY asmLib.split_bytes_in_memory_tac (List.map Int.abs l)
      \\ NTAC (i + 1) next_state_tac
      \\ (if not (exists (fn i => i < 0) l) then all_tac else
          `s1.pc = ms.RIP` by
             (fs [asmPropsTheory.target_state_rel_def,x64_target_def])
          \\ full_simp_tac std_ss [miscTheory.bytes_in_memory_def,
               addressTheory.word_arith_lemma1])
      \\ fs [x64Theory.RexReg_def, asmPropsTheory.all_pcs, overflow_lem,
             asmPropsTheory.sym_target_state_rel, x64_target_def, sub_overflow,
             x64_config, set_sepTheory.fun2set_eq, integer_wordTheory.overflow,
             const_lem1, const_lem3, const_lem4, loc_lem3, loc_lem4,
             binop_lem6, binop_lem7, jump_lem2, cmp_lem1, cmp_lem3, x64_ok_def,
             x64_stepTheory.rounding_mode_def, fp_abs, fp_neg, fp_compare]
      \\ unabbrev_all_tac
      \\ rw [combinTheory.APPLY_UPDATE_THM, x64Theory.num2Zreg_11,
             binop_lem10b, adc_lem2, wordsTheory.w2w_n2w, extract_double,
             GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_def]
      \\ fs [is_rax, is_rdx, adc_lem1, wordsTheory.w2w_n2w]
      \\ rfs []
      \\ blastLib.FULL_BBLAST_TAC
    end
end;

local
   fun rule rwt thm =
      if is_bytes_in_memory (Thm.concl thm)
         then PURE_ONCE_REWRITE_RULE [rwt] thm
      else thm
   val not_reg_tac =
      pop_assum (fn th => rule_assum_tac (rule th) \\ assume_tac (SYM th))
   fun highreg v tm =
       case Lib.total boolSyntax.dest_eq tm of
          SOME (l, r) =>
             (case Lib.total wordsSyntax.dest_word_extract l of
                 SOME (h, l, x, _) =>
                    if x ~~ v andalso h ~~ ``3n`` andalso l ~~ ``3n``
                       then (case Lib.total wordsSyntax.uint_of_word r of
                                SOME 0 => SOME true
                              | SOME 1 => SOME false
                              | _ => NONE)
                    else NONE
               | NONE => NONE)
        | NONE => NONE
   fun high_low_reg v =
      fn asl =>
         case (Lib.mk_set o List.mapPartial (highreg v)) asl of
            [true] => (false, true)
          | [false] => (true, false)
          | _ => (false, false)
   val high_low_r1 = high_low_reg ``r1: word4``
   val high_low_r2 = high_low_reg ``r2: word4``
   fun ls_tac tac =
      basic_next_state_tac
      \\ bytes_in_memory_tac
      \\ fsrw_tac [] []
      \\ rfs [Abbr `r2`, mem_lem5, binop_lem7]
      \\ REPEAT (qpat_x_assum `NextStateX64 q = z` (K all_tac))
      \\ rfs [x64Theory.RexReg_def, asmPropsTheory.all_pcs,
              asmPropsTheory.sym_target_state_rel, x64_target_def,
              x64_config, x64_ok_def, set_sepTheory.fun2set_eq,
              REWRITE_RULE [mem_lem14] x64_stepTheory.write_mem64_def,
              REWRITE_RULE [mem_lem15] x64_stepTheory.write_mem32_def,
              const_lem1, const_lem3, const_lem4, loc_lem3, loc_lem4,
              mem_lem8]
      \\ Q.UNABBREV_TAC `r1`
      \\ rw [combinTheory.APPLY_UPDATE_THM, x64Theory.num2Zreg_11]
      \\ tac
      \\ blastLib.BBLAST_TAC
   fun load_store_tac load (asl, g) =
      let
         val (high_r1, low_r1) = high_low_r1 asl
         val (high_r2, low_r2) = high_low_r2 asl
         val tac =
            if load
               then ls_tac (qabbrev_tac `q = c + ms.REG (num2Zreg n')`)
            else ls_tac (full_simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) [])
         fun tac2 not5 =
           Cases_on `(2 >< 0) r2 = 4w: word3`
           \\ fsrw_tac [] enc_rwts
           >| [all_tac,
              (if not5
                  then `r2 = RegNot4or5 r2`
                       by (fsrw_tac [] [] \\ imp_res_tac mem_lem6)
               else `r2 = RegNot4 r2`
                    by (fsrw_tac [] [] \\ imp_res_tac mem_lem7))
              \\ not_reg_tac
           ]
           \\ rule_assum_tac (REWRITE_RULE [binop_lem5])
           \\ tac
      in
        (
         (if high_r1
             then `r1 ' 3` by imp_res_tac mem_lem11
          else if low_r1
             then `~r1 ' 3` by imp_res_tac mem_lem12
          else all_tac)
         \\ (if high_r2
                then `r2 ' 3` by imp_res_tac mem_lem11
             else if low_r2
                then `~r2 ' 3` by imp_res_tac mem_lem12
             else all_tac)
         \\ Cases_on `(c = 0w) /\ (2 >< 0) r2 <> 5w: word3`
         \\ asmLib.using_first 1 (fn thms => fsrw_tac [] (loc_lem2 :: thms))
         >- tac2 true
         \\ pop_assum (K all_tac)
         \\ Cases_on `0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw`
         \\ asmLib.using_first 1 (fn thms => fsrw_tac [] thms)
         >- tac2 false
         \\ pop_assum (K all_tac)
         \\ fsrw_tac [] [const_lem2]
         \\ tac2 false
        ) (asl, g)
      end
in
   val load_tac = load_store_tac true
   val store_tac = load_store_tac false
end;

val fp_cmp_tac =
  Cases_on `n < 8`
  \\ Cases_on
       `fp64_compare ((63 >< 0) (ms.XMM_REG (n2w n0)))
                     ((63 >< 0) (ms.XMM_REG (n2w n1))) = UN`
  >- next_tac [4, 5, ~2]
  >- next_tac [4, 5, 2]
  >- next_tac [4, 6, ~2]
  \\ next_tac [4, 6, 2];

(* -------------------------------------------------------------------------
   x64 target_ok
   ------------------------------------------------------------------------- *)

val x64_encoding = Q.prove (
   `!i. x64_enc i <> []`,
   strip_tac
   \\ Cases_on `LIST_BIND (x64_ast i) x64_encode`
   \\ simp [x64_enc_def, x64_dec_fail_def]
   );

val x64_cmp_neq_p = Q.prove(
  `!cmp. x64_cmp cmp <> Z_P`,
  Cases \\ simp [x64_cmp_def]
  );

val x64_target_ok = Q.prove (
   `target_ok x64_target`,
   rw [asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
       x64_proj_def, x64_target_def, x64_config, x64_encoding, x64_ok_def,
       set_sepTheory.fun2set_eq, asmPropsTheory.enc_ok_def]
   >| [simp encode_rwts,
       all_tac,
       Cases_on `ri`
       >| [all_tac,
           Cases_on `~is_test cmp /\ 0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7fw`
           >| [all_tac, Cases_on `r = 0`]
       ],
       all_tac,
       all_tac
   ]
   \\ full_simp_tac (srw_ss()++boolSimps.LET_ss)
        (asmPropsTheory.offset_monotonic_def :: x64_cmp_neq_p :: enc_ok_rwts)
   \\ rw [jump_lem1, jump_lem3, jump_lem4, jump_lem5, jump_lem6, loc_lem1]
   );

(* -------------------------------------------------------------------------
   x64 encoder_correct
   ------------------------------------------------------------------------- *)

val print_tac = asmLib.print_tac "";

Theorem x64_encoder_correct:
    encoder_correct x64_target
Proof
   simp [asmPropsTheory.encoder_correct_def, x64_target_ok]
   \\ qabbrev_tac `state_rel = target_state_rel x64_target`
   \\ rw [x64_target_def, x64_config, asmSemTheory.asm_step_def]
   \\ qunabbrev_tac `state_rel`
   \\ Cases_on `i`

   >- (
      (*--------------
          Inst
        --------------*)
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ next_tac []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `(63 >< 31) c = 0w : 33 word`
         >| [Cases_on `word_bit 3 (n2w n : word4)`, all_tac]
         \\ next_tac []
         )
      >- (
         (*--------------
             Arith
           --------------*)
         Cases_on `a`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            >- (
               (* Reg *)
               Cases_on `(b = Or) /\ (n0 = n')`
               >- next_tac []
               \\ Cases_on `b`
               \\ next_tac []
               )
               (* Imm *)
            \\ Cases_on `(b = Xor) /\ (c = -1w)`
            >- next_tac []
            \\ Cases_on `b`
            \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) []
            \\ (
                Cases_on `0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7fw`
                >- next_tac []
                \\ Cases_on `n0 = 0`
                \\ next_tac []
               )
            )
         >- (
            (*--------------
                Shift
              --------------*)
            print_tac "Shift"
            \\ Cases_on `s`
            \\ Cases_on `n1 = 1`
            \\ next_tac []
            )
         >- (
            (*--------------
                Div
              --------------*)
            print_tac "Div"
            \\ next_tac []
            )
         >- (
            (*--------------
                LongMul
              --------------*)
            print_tac "LongMul"
            \\ next_tac []
            )
         >- (
            (*--------------
                LongDiv
              --------------*)
            print_tac "LongDiv"
            \\ next_tac []
            )
         >- (
            (*--------------
                AddCarry
              --------------*)
            print_tac "AddCarry"
            \\ Cases_on `word_bit 3 (n2w n2 : word4)`
            >- (`(3 >< 3) (n2w n2 : word4) = 1w : word1`
                by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
                \\ next_tac [4,1,3,6])
            \\ `(3 >< 3) (n2w n2 : word4) = 0w : word1`
            by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ next_tac [4,1,3,5]
            )
         >- (
            (*--------------
                AddOverflow
              --------------*)
            print_tac "AddOverflow"
            \\ Cases_on `word_bit 3 (n2w n2 : word4)`
            >- (`(3 >< 3) (n2w n2 : word4) = 1w : word1`
                by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
                \\ next_tac [3, 6]
               )
            \\ `(3 >< 3) (n2w n2 : word4) = 0w : word1`
            by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ next_tac [3, 5]
            )
         >- (
            (*--------------
                SubOverflow
              --------------*)
            print_tac "SubOverflow"
            \\ Cases_on `word_bit 3 (n2w n2 : word4)`
            >- (`(3 >< 3) (n2w n2 : word4) = 1w : word1`
                by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
                \\ next_tac [3, 6]
               )
            \\ `(3 >< 3) (n2w n2 : word4) = 0w : word1`
            by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ next_tac [3, 5]
            )
         )
         >- (
            (*--------------
                Mem
              --------------*)
            qexists_tac `0`
            \\ simp [asmPropsTheory.asserts_eval,
                     asmPropsTheory.asserts2_eval,
                     asmPropsTheory.interference_ok_def,
                     x64_next_def, x64_proj_def]
            \\ NTAC 2 STRIP_TAC
            \\ Cases_on `a`
            \\ qabbrev_tac `r1 = n2w n : word4`
            \\ qabbrev_tac `r2 = n2w n' : word4`
            \\ `RexReg (r2 ' 3,(2 >< 0) r2) = num2Zreg n'`
            by (simp [mem_lem4, x64Theory.RexReg_def, Abbr `r2`]
                \\ fsrw_tac [] (x64_config :: asmLib.asm_ok_rwts))
            \\ Cases_on `m`
            \\ Q.PAT_ABBREV_TAC `instr = x64_enc aa`
            \\ NO_STRIP_REV_FULL_SIMP_TAC
                  (srw_ss()++ARITH_ss++boolSimps.LET_ss) enc_rwts
            \\ qunabbrev_tac `instr`
            \\ NO_STRIP_FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) []
            \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()) []
            >- (
               (*--------------
                   Load
                 --------------*)
               print_tac "Load"
               \\ `read_mem64 ms.MEM (ms.REG (num2Zreg n') + c) =
                   s1.mem (s1.regs n' + c + 7w) @@
                   s1.mem (s1.regs n' + c + 6w) @@
                   s1.mem (s1.regs n' + c + 5w) @@
                   s1.mem (s1.regs n' + c + 4w) @@
                   s1.mem (s1.regs n' + c + 3w) @@
                   s1.mem (s1.regs n' + c + 2w) @@
                   s1.mem (s1.regs n' + c + 1w) @@
                   s1.mem (s1.regs n' + c)`
               by (imp_res_tac (Q.SPECL [`c`, `n'`, `s1`, `ms`] mem_lem3)
                   \\ simp [])
               \\ load_tac
               )
            >- (
               (*--------------
                   Load8
                 --------------*)
               print_tac "Load8"
               \\ `ms.MEM (ms.REG (num2Zreg n') + c) = s1.mem (s1.regs n' + c)`
               by metis_tac [mem_lem1, wordsTheory.WORD_ADD_COMM]
               \\ load_tac
               )
            (*
            >- (
               (*--------------
                   Load32
                 --------------*)
               print_tac "Load32"
               \\ `read_mem32 ms.MEM (ms.REG (num2Zreg n') + c) =
                   s1.mem (s1.regs n' + c + 3w) @@
                   s1.mem (s1.regs n' + c + 2w) @@
                   s1.mem (s1.regs n' + c + 1w) @@
                   s1.mem (s1.regs n' + c)`
               by (imp_res_tac (Q.SPECL [`c`, `n'`, `s1`, `ms`] mem_lem2)
                   \\ simp [])
               \\ Cases_on
                    `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
               >- (fsrw_tac [] [] \\ load_tac)
               \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                          (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
               by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
               \\ qpat_x_assum `~(a /\ b)` (K all_tac)
               \\ load_tac
               )
            *)
            >- (
               (*--------------
                   Store
                 --------------*)
               print_tac "Store"
               \\ `?wv. read_mem64 ms.MEM (ms.REG (num2Zreg n') + c) = wv`
               by metis_tac [mem_lem3]
               \\ store_tac
               )
            >- (
               (*--------------
                   Store8
                 --------------*)
               print_tac "Store8"
               \\ `?wv. ms.MEM (ms.REG (num2Zreg n') + c) = wv`
               by metis_tac [mem_lem1, wordsTheory.WORD_ADD_COMM]
               \\ wordsLib.Cases_on_word_value `(3 >< 3) r1: word1`
               >| [
                  `3w <+ r1` by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
                  \\ `3 < n` by rfs [Abbr `r1`, wordsTheory.word_lo_n2w],
                  all_tac
               ]
               \\ wordsLib.Cases_on_word_value `(3 >< 3) r2: word1`
               >| [all_tac, all_tac, all_tac,
                   Cases_on `3 < n` >| [all_tac, imp_res_tac mem_lem8]
               ]
               \\ store_tac
               )
            (*
               (*--------------
                   Store32
                 --------------*)
            \\ print_tac "Store32"
            \\ `?wv. read_mem32 ms.MEM (ms.REG (num2Zreg n') + c) = wv`
            by metis_tac [mem_lem2]
            \\ Cases_on `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
            >- (fsrw_tac [] [] \\ store_tac)
            \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                       (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
            by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ qpat_x_assum `~(a /\ b)` (K all_tac)
            \\ store_tac
            *)
            )
         (*--------------
             FP
           --------------*)
         \\ print_tac "FP"
         \\ Cases_on `f`
         >- (print_tac "FPLess" \\ fp_cmp_tac)
         >- (print_tac "FPLessEqual" \\ fp_cmp_tac)
         >- (print_tac "FPEqual" \\ fp_cmp_tac)
         >- (print_tac "FPAbs" \\ next_tac [5, 5])
         >- (print_tac "FPNeg" \\ next_tac [5, 5])
         >- (print_tac "FPSqrt" \\ next_tac [])
         >- (print_tac "FPAdd" \\ next_tac [])
         >- (print_tac "FPSub" \\ next_tac [])
         >- (print_tac "FPMul" \\ next_tac [])
         >- (print_tac "FPDiv" \\ next_tac [])
         >- (print_tac "FPFma" \\ next_tac [])
         >- (print_tac "FPMov" \\ next_tac [])
         >- (print_tac "FPMovToReg" \\ next_tac [])
         >- (print_tac "FPMovFromReg" \\ next_tac [])
         >- (print_tac "FPToInt"
             \\ Cases_on `fp64_to_int roundTiesToEven (s1.fp_regs n0)`
             >- next_tac []
             \\ rename1 `fp64_to_int roundTiesToEven _ = SOME i`
             \\ Cases_on `w2i (i2w i : word32) = i`
             >- (
                 imp_res_tac fp_to_int_lem
                 \\ next_tac [4, 5]
                )
             \\ next_tac []
            )
         \\ (print_tac "FPFromInt" \\ next_tac [])
      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac []
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      >- (
         (* Reg *)
         Cases_on `c`
         \\ next_tac [3]
         )
      \\ Cases_on `c`
      >| [
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
        >- next_tac [4]
        \\ Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
        ,
        Cases_on `n = 0`
        >- next_tac [6]
        \\ next_tac [7]
      ]
      )
      (*--------------
          no Call
        --------------*)
   >- fsrw_tac [] enc_rwts
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ wordsLib.Cases_on_word_value `(3 >< 3) (n2w n : word4): word1`
      \\ next_tac []
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ next_tac []
      )
QED

val () = export_theory ()
