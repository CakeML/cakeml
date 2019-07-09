(*
  Prove `encoder_correct` for ARMv8
*)
open HolKernel Parse boolLib bossLib
open asmLib arm8_stepLib arm8_targetTheory;

val () = new_theory "arm8_targetProof"

val () = wordsLib.guess_lengths ()

val ERR = mk_HOL_ERR "arm8_targetProofTheory";

(* some lemmas ------------------------------------------------------------- *)

fun cases_on_DecodeBitMasks (g as (asl, _)) =
   let
      val (_, tm, _) = TypeBase.dest_case (lhs (List.nth (List.rev asl, 1)))
   in
      (Cases_on `^tm` \\ fs [] \\ Cases_on `x` \\ fs []) g
   end

Theorem Decode_EncodeBitMask:
    (!w: word32 n s r.
        (EncodeBitMask w = SOME (n, s, r)) ==>
        (?v. DecodeBitMasks (n, s, r, T) = SOME (w, v))) /\
    (!w: word64 n s r.
        (EncodeBitMask w = SOME (n, s, r)) ==>
        (?v. DecodeBitMasks (n, s, r, T) = SOME (w, v)))
Proof
   lrw [arm8Theory.EncodeBitMask_def, arm8Theory.EncodeBitMaskAux_def]
   \\ BasicProvers.FULL_CASE_TAC
   \\ fs []
   \\ cases_on_DecodeBitMasks
   \\ metis_tac []
QED

val word_log2_7 = Q.prove(
   `!s: word6. word_log2 (((1w: word1) @@ s) : word7) = 6w`,
   lrw [wordsTheory.word_concat_def, wordsTheory.word_join_def,
        wordsTheory.word_log2_def, wordsTheory.w2n_w2w]
   \\ `(w2w s || (64w: (unit + 6) word)) <> 0w` by blastLib.BBLAST_TAC
   \\ imp_res_tac wordsTheory.LOG2_w2n_lt
   \\ fs [arithmeticTheory.LESS_MOD, DECIDE ``a < 7n ==> a < 128``]
   \\ MATCH_MP_TAC bitTheory.LOG2_UNIQUE
   \\ simp [wordsTheory.w2w_def, wordsTheory.word_or_n2w, wordsTheory.w2n_n2w,
            (numLib.REDUCE_RULE o Q.SPEC `7`) bitTheory.BITWISE_LT_2EXP,
            arithmeticTheory.LESS_MOD]
   \\ simp [Once
              (CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV bitTheory.BITWISE_def)]
   )

val DecodeBitMasks_SOME = Q.prove(
   `!r s. ?wmask: word64 tmask.
          DecodeBitMasks (1w, s, r, F) = SOME (wmask,tmask)`,
   simp [arm8Theory.DecodeBitMasks_def, arm8Theory.HighestSetBit_def]
   \\ rw [word_log2_7]
   >- blastLib.FULL_BBLAST_TAC
   \\ EVAL_TAC
   )

val ShiftValue0 = Q.prove(
   `!x. ShiftValue (x, DecodeShift 0w, 0) = x`,
   rw [arm8Theory.ShiftValue_def, arm8Theory.DecodeShift_def,
       arm8Theory.num2ShiftType_thm]
   )

val valid_immediate_thm = Q.prove(
   `!b c.
        valid_immediate b c =
        if (b = INL Add) \/ (b = INL Sub) \/
           (b = INR Less) \/ (b = INR Lower) \/ (b = INR Equal) \/
           (b = INR NotLess) \/ (b = INR NotLower) \/ (b = INR NotEqual) then
           ((0xFFFFFFFFFFFFF000w && c) = 0w) \/
           ((0xFFFFFFFFFFFFF000w && c) <> 0w) /\
           ((0xFFFFFFFFFF000FFFw && c) = 0w)
        else
           ?N imms immr. EncodeBitMask c = SOME (N, imms, immr)`,
   Cases
   >| [ Cases_on `x`, Cases_on `y` ]
   \\ rw [valid_immediate_def]
   \\ TRY blastLib.BBLAST_PROVE_TAC
   \\ Cases_on `EncodeBitMask c`
   \\ simp []
   \\ METIS_TAC [pairTheory.ABS_PAIR_THM]
   )

val lem1 = asmLib.v2w_BIT_n2w 5

val lem2 =
   blastLib.BBLAST_PROVE
   ``(!n: word1. v2w [n ' 0] = n) /\
     (!w: word6. v2w [w ' 5; w ' 4; w ' 3; w ' 2; w ' 1; w ' 0] = w)``

val lem3 = bitstringLib.v2w_n2w_CONV ``v2w [T] : word1``

val lem5 = asmLib.v2w_BIT_n2w 6

val lem6 = bitstringLib.v2w_n2w_CONV ``v2w [T; T; T; T; T; T] : word6``

val lem7 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
        0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\ word_msb c  ==>
        (c = sw2sw ((8 >< 0) c : word9))``

val lem7b =
   blastLib.BBLAST_PROVE
     ``!c: word64.
        0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\
        c <> w2w ((11 >< 0) c : word12) ==>
        (c = sw2sw ((8 >< 0) c : word9))``

val lem8 = Q.prove(
   `!w: word64. aligned 2 w ==> ((1 >< 0) w = 0w: word2)`,
    simp [alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC
    )

val align_prove =
   Drule.EQT_ELIM o
   (SIMP_CONV std_ss [alignmentTheory.aligned_extract]
    THENC blastLib.BBLAST_CONV)

val lem9 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFF8000000w <= c /\ c <= 0x7FFFFFFw /\ aligned 2 c ==>
       (c = sw2sw ((((27 >< 2) c: 26 word) @@ (0w: word2)): word28))``

val lem10 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFFFF80000w <= c /\ c <= 0x7FFFFw /\ aligned 2 c ==>
       (c = sw2sw ((((20 >< 2) c: 19 word) @@ (0w: word2)): 21 word))``

val lem11 =
   align_prove
   ``!c: word64.
       0xFFFFFFFFFFF00004w <= c /\ c <= 0x100003w /\ aligned 2 c ==>
       (c + 0xFFFFFFFFFFFFFFFCw =
        sw2sw ((((20 >< 2) (c + 0xFFFFFFFFFFFFFFFCw): 19 word) @@
                (0w: word2)): 21 word))``

val lem13 = Q.prove(
   `!c: word64.
       (c = w2w ((11 >< 0) (c >>> 3) : word12) << 3) ==>
       (w2w (v2w [c ' 14; c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8;
                  c ' 7; c ' 6; c ' 5; c ' 4; c ' 3]: word12) << 3 = c)`,
   blastLib.BBLAST_TAC
   )

val lem14 = Q.prove(
   `!s state c: word64 n.
      target_state_rel arm8_target s state /\ n <> 26 /\ n <> 31 /\ n < 32 /\
      aligned 3 (c + s.regs n) ==> aligned 3 (c + state.REG (n2w n))`,
   rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
   )

(*
val lem14b = Q.prove(
   `!s state c: word64 n.
      target_state_rel arm8_target s state /\ n <> 26 /\ n <> 31 /\ n < 32 /\
      aligned 2 (c + s.regs n) ==> aligned 2 (c + state.REG (n2w n))`,
   rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
   )
*)

val lem16 =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\ word_msb c ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem16b =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       0xFFFFFFFFFFFFFF00w <= c /\ c <= 0xFFFw /\
       c <> w2w ((11 >< 0) c : word12) ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem16c =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       (c = sw2sw ((8 >< 0) c : word9)) ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem17 = Q.prove(
   `!c: word64.
      (c = w2w ((11 >< 0) c : word12)) ==>
      (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5; c ' 4;
                 c ' 3; c ' 2; c ' 1; c ' 0]: word12) = c)`,
   blastLib.BBLAST_TAC
   )

val lem18 = Q.prove(
   `!c: word64.
       (c = w2w ((11 >< 0) (c >>> 2) : word12) << 2) ==>
       (w2w (v2w [c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
                  c ' 6; c ' 5; c ' 4; c ' 3; c ' 2]: word12) << 2 = c)`,
   blastLib.BBLAST_TAC
   )

val lem20 = blastLib.BBLAST_PROVE ``a <> b ==> (a + -1w * b <> 0w: word64)``

val lem21 =
   blastLib.BBLAST_PROVE
     ``a < b: word64 ==>
       (word_msb (a + -1w * b) <=/=> (word_msb (a) <=/=> word_msb (b)) /\
       (word_msb (a + -1w * b) <=/=> word_msb (a)))``

val lem22 =
   blastLib.BBLAST_PROVE
     ``~(a < b: word64) ==>
       (word_msb (a + -1w * b) <=> (word_msb (a) <=/=> word_msb (b)) /\
       (word_msb (a + -1w * b) <=/=> word_msb (a)))``

val lem23 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFF000FFFw && c) = 0w) ==>
         ((-1w *
          w2w (v2w [c ' 23; c ' 22; c ' 21; c ' 20; c ' 19; c ' 18;
                    c ' 17; c ' 16; c ' 15; c ' 14; c ' 13; c ' 12] : word12))
           << 12 = -c)``

val lem24 =
   blastLib.BBLAST_PROVE ``!c: word64 n. n <> c ==> (-1w * c + n <> 0w)``

val lem25 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFFFFF000w && c) = 0w) ==>
         (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                    c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c)``

val lem26 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         ((0xFFFFFFFFFF000FFFw && c) = 0w) ==>
         (w2w (v2w [c ' 23; c ' 22; c ' 21; c ' 20; c ' 19; c ' 18;
                    c ' 17; c ' 16; c ' 15; c ' 14; c ' 13; c ' 12] : word12)
           << 12 = c)``

val lem27 = Q.prove(
   `!c: word64 q r.
     (arm8_enc_mov_imm c = SOME (q,r)) ==>
     (c =
      bit_field_insert
       (w2n (((v2w [r ' 1; r ' 0]: word2) @@ (0w: word4)) : word6) + 15)
       (w2n (((v2w [r ' 1; r ' 0]: word2) @@ (0w: word4)) : word6))
         (v2w [q ' 15; q ' 14; q ' 13; q ' 12; q ' 11; q ' 10; q ' 9; q ' 8;
               q ' 7; q ' 6; q ' 5; q ' 4; q ' 3; q ' 2; q ' 1; q ' 0] : word16)
       0w)`,
   lrw [arm8_enc_mov_imm_def]
   \\ simp []
   \\ CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   \\ simp []
   \\ blastLib.FULL_BBLAST_TAC
   )

val lem28 = metisLib.METIS_PROVE [wordsTheory.WORD_NOT_NOT]
               ``(~c = n) = (c = ~n:'a word)``

val lem29 = Q.prove( `!i. i < 31 ==> (i MOD 32 <> 31)`, rw [] )

val lem30 = DECIDE ``!a. a < 32n /\ a <> 31 <=> a < 31``

val lem31 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       0xFFFFFFFFFFFFEF01w <= c /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       word_msb c ==>
       ((0xFFFFFFFFFFFFF000w && (-1w * c + 0xFFFFFFFFFFFFFF00w)) = 0w)``

val lem32 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\ c <= 0x10FEw ==>
      (v2w [c ' 11 <=>
            c ' 10 /\ c ' 9 /\ c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 10 <=>
            c ' 9 /\ c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 9 <=>
            c ' 8 /\
            (c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
             c ' 1 \/ c ' 0);
            c ' 8 <=>
            c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3 \/ c ' 2 \/
            c ' 1 \/ c ' 0;
            c ' 7 <=>
            ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\
            ~c ' 1 /\ ~c ' 0;
            c ' 6 <=>
            ~c ' 5 /\ ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\
            ~c ' 0;
            c ' 5 <=>
            ~c ' 4 /\ ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 4 <=> ~c ' 3 /\ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 3 <=> ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
            c ' 2 <=> ~c ' 1 /\ ~c ' 0; ~c ' 1 <=> c ' 0; c ' 0] : word12 =
        (11 >< 0) (-1w * c - 0x100w))``

val lem33 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\
      c <> sw2sw ((8 >< 0) c : word9) /\ word_msb c ==>
      (-1w * w2w ((11 >< 0) (-1w * c + 0xFFFFFFFFFFFFFF00w) : word12) =
       c + 0x100w)``

val lem35 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       c <= 0x10FEw /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       ~word_msb c ==>
       ((0xFFFFFFFFFFFFF000w && (c + 0xFFFFFFFFFFFFFF01w)) = 0w)``

val lem36 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
      0xFFFFFFFFFFFFEF01w <= c /\ c <= 0x10FEw ==>
      (v2w [c ' 11 <=>
            c ' 10 \/ c ' 9 \/ c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 10 <=>
            c ' 9 \/ c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 9 <=>
            c ' 8 \/
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 8 <=>
            c ' 7 /\ c ' 6 /\ c ' 5 /\ c ' 4 /\ c ' 3 /\
            c ' 2 /\ c ' 1 /\ c ' 0;
            c ' 7 <=>
            ~c ' 6 \/ ~c ' 5 \/ ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/
            ~c ' 1 \/ ~c ' 0;
            c ' 6 <=>
            ~c ' 5 \/ ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/
            ~c ' 0;
            c ' 5 <=>
            ~c ' 4 \/ ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 4 <=> ~c ' 3 \/ ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 3 <=> ~c ' 2 \/ ~c ' 1 \/ ~c ' 0;
            c ' 2 <=> ~c ' 1 \/ ~c ' 0; c ' 1 <=> ~c ' 0;
            ~c ' 0] : word12 = (11 >< 0) (c - 0xFFw))``

val lem37 =
  blastLib.BBLAST_PROVE
    ``!c : word64.
       c <= 0x10FEw /\
       c <> sw2sw ((8 >< 0) c : word9) /\
       ~word_msb c ==>
       (w2w ((11 >< 0) (c + 0xFFFFFFFFFFFFFF01w) : word12) = c - 0xFFw)``

val ev = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV

val replicate1 = GEN_ALL (EVAL ``replicate v 1``)

fun and_max ty =
   wordsTheory.WORD_AND_CLAUSES
   |> Thm.INST_TYPE [Type.alpha |-> ty]
   |> REWRITE_RULE [EVAL (wordsSyntax.mk_word_T ty)]

val lsl_lem1 = Q.prove(
   `!w:word6.
      (if v2n (field 5 0 (w2v w)) + 1 < 64 then
          64
       else v2n (field 5 0 (w2v w)) + 1) = 64`,
   lrw []
   \\ Cases_on `v2n (field 5 0 (w2v w)) = 63`
   >- simp []
   \\ qspec_then `field 5 0 (w2v w)` assume_tac bitstringTheory.v2n_lt
   \\ fs []
   \\ decide_tac
   )

val lsl_lem2 = Q.prove(
   `!w:word6. (if w2n w + 1 < 64 then 64 else w2n w + 1) = 64`,
   lrw []
   \\ Cases_on `w2n w = 63`
   >- simp []
   \\ Q.ISPEC_THEN `w` assume_tac wordsTheory.w2n_lt
   \\ fs []
   \\ decide_tac
   )

val lsl_lem3 = ev
   ``v2w (PAD_LEFT F 64
            (PAD_LEFT T (v2n (field 5 0 (w2v (63w: word6))) + 1) [])): word64``

val lsl_lem4 = Q.prove(
   `!n. n < 64 ==> ((64 - n + 63) MOD 64 = 63 - n)`,
   lrw []
   \\ asm_simp_tac bool_ss
         [arithmeticTheory.ADD_MODULUS_RIGHT, DECIDE ``0n < 64``,
          DECIDE ``n < 64n ==> (127 - n = 64 + (63 - n)) /\ 63 - n < 64``,
          arithmeticTheory.LESS_MOD]
   )

val lsl_lem5 = Q.prove(
   `!n. n < 64 ==>
        (v2w (PAD_LEFT F 64 (PAD_LEFT T n [])) : word64 = (FCP i. i < n))`,
   srw_tac [fcpLib.FCP_ss] []
   \\ rewrite_tac [bitstringTheory.word_index_v2w]
   \\ simp [bitstringTheory.testbit, listTheory.PAD_LEFT]
   \\ Cases_on `63 - i < 64 - n`
   \\ simp [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
   )

val lsl_lem6 = DECIDE ``n < 64n ==> (63 - n + 1 = 64 - n)``

val lsl = Q.prove(
   `!r q n x wmask: word64 tmask.
       n < 64n /\
       Abbrev (r = n2w ((64 - n) MOD 64)) /\
       Abbrev (q = r + 63w) /\
       (DecodeBitMasks (1w, q, r, F) = SOME (wmask, tmask)) ==>
       (((tmask && wmask) && x #>> (w2n r)) = x << n)`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.Replicate_def,
        arm8Theory.Ones_def, arm8Theory.HighestSetBit_def, word_log2_7,
        EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ qunabbrev_tac `q`
   \\ qunabbrev_tac `r`
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1, lsl_lem2]
   \\ simp [and_max ``:64``, lsl_lem3]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ full_simp_tac (srw_ss())
         [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
          wordsTheory.word_add_n2w, lsl_lem4, lsl_lem6]
   \\ `PAD_LEFT F 64 (PAD_LEFT T (64 - n) []) =
       fixwidth (dimindex(:64)) (PAD_LEFT F 64 (PAD_LEFT T (64 - n) []))`
   by (match_mp_tac (GSYM bitstringTheory.fixwidth_id_imp)
       \\ simp [bitstringTheory.length_pad_left])
   \\ pop_assum SUBST1_TAC
   \\ rewrite_tac [GSYM bitstringTheory.word_ror_v2w]
   \\ simp [lsl_lem5]
   \\ simp_tac bool_ss [wordsTheory.ROR_BITWISE]
   \\ srw_tac [fcpLib.FCP_ss]
         [wordsTheory.word_lsl_def, wordsTheory.word_ror_def,
          wordsTheory.word_and_def]
   \\ Cases_on `n <= i`
   \\ simp []
   \\ `i + 64n - n = 64 + (i - n)` by decide_tac
   \\ pop_assum SUBST1_TAC
   \\ simp_tac std_ss [arithmeticTheory.ADD_MODULUS_RIGHT]
   \\ simp []
   )

val lsr_lem1 = Q.prove(
   `!n. v2n (field 5 0 (w2v (n2w n : word6))) = n MOD 64`,
   REPEAT strip_tac
   \\ strip_assume_tac
         (Q.ISPEC `n2w n: word6` bitstringTheory.ranged_bitstring_nchotomy)
   \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.word_extract_v2w,
            bitstringTheory.word_bits_v2w, bitstringTheory.w2w_v2w]
   \\ rfs [markerTheory.Abbrev_def, bitstringTheory.field_id_imp,
           GSYM bitstringTheory.n2w_v2n, arithmeticTheory.LESS_MOD]
   \\ metis_tac [bitstringTheory.v2n_lt, EVAL ``2n ** 6n``]
   )

val lsr_lem2 = Q.prove(
   `!n. v2w (rotate (PAD_LEFT F 64 (PAD_LEFT T 64 [])) n) = UINT_MAXw: word64`,
   strip_tac
   \\ `PAD_LEFT F 64 (PAD_LEFT T 64 []) =
       fixwidth (dimindex(:64)) (PAD_LEFT F 64 (PAD_LEFT T 64 []))`
   by EVAL_TAC
   \\ pop_assum SUBST1_TAC
   \\ rewrite_tac [GSYM bitstringTheory.word_ror_v2w]
   \\ simp [ev ``PAD_LEFT F 64 (PAD_LEFT T 64 [])``]
   \\ CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   \\ simp [wordsTheory.ROR_UINT_MAX
            |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
            |> CONV_RULE EVAL]
   )

val lsr = Q.prove(
   `!n x wmask: word64 tmask.
       n < 64n /\
       (DecodeBitMasks (1w, 63w, n2w n, F) = SOME (wmask, tmask)) ==>
       (((tmask && wmask) && x #>> n) = x >>> n)`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.Replicate_def,
        arm8Theory.Ones_def, arm8Theory.HighestSetBit_def,
        EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ full_simp_tac (srw_ss())
         [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
          wordsTheory.word_add_n2w, lsr_lem1, lsl_lem4, lsl_lem5, lsl_lem6,
          lsr_lem2]
   \\ srw_tac [fcpLib.FCP_ss]
         [wordsTheory.word_lsr_def, wordsTheory.word_ror_def,
          wordsTheory.word_and_def]
   \\ Cases_on `i + n < 64`
   \\ simp []
   )

val asr =
  wordsTheory.word_asr_n2w
  |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
  |> REWRITE_RULE
       [blastLib.BBLAST_PROVE ``word_msb (w:word64) = word_bit 63 w``]

val asr_lem1 = Q.prove(
   `!m. m < 64 ==> (MIN m 64 = m)`, rw [arithmeticTheory.MIN_DEF])

val asr2 = Q.prove(
   `!n x wmask: word64 tmask.
       n < 64n /\
       (DecodeBitMasks (1w, 63w, n2w n, F) = SOME (wmask, tmask)) ==>
       (n2w (0x10000000000000000 - 2 ** (64 - MIN n 64)) =
        (0xFFFFFFFFFFFFFFFFw && ~tmask))`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.Replicate_def,
        arm8Theory.Ones_def, arm8Theory.HighestSetBit_def,
        EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ full_simp_tac (srw_ss())
         [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
          wordsTheory.word_add_n2w, lsr_lem1, lsl_lem4, lsl_lem5, lsl_lem6,
          lsr_lem2, asr_lem1, and_max ``:64``]
   \\ `0x10000000000000000 - 2 ** (64 - n) = (2 ** n - 1) * 2 ** (64 - n)`
   by simp [arithmeticTheory.RIGHT_SUB_DISTRIB, GSYM arithmeticTheory.EXP_ADD]
   \\ pop_assum SUBST1_TAC
   \\ srw_tac [fcpLib.FCP_ss]
        [wordsTheory.word_and_def, wordsTheory.word_1comp_def,
         wordsTheory.word_index]
   \\ Cases_on `i < 64 - n`
   \\ lrw [bitTheory.BIT_SHIFT_THM2, bitTheory.BIT_SHIFT_THM3,
           bitTheory.BIT_EXP_SUB1]
   )

val ror = Q.prove(
  `!w : word64 n.
     n < 64 ==> (v2w (shiftr (w2v w ++ w2v w) n): word64 = w #>> n)`,
  rpt strip_tac
  \\ bitstringLib.Cases_on_v2w `w`
  \\ fs [markerTheory.Abbrev_def]
  \\ simp [bitstringTheory.word_ror_v2w, bitstringTheory.v2w_11,
           bitstringTheory.w2v_v2w]
  \\ match_mp_tac listTheory.LIST_EQ
  \\ rw [bitstringTheory.el_fixwidth, bitstringTheory.shiftr_def,
         bitstringTheory.rotate_def, rich_listTheory.EL_TAKE,
         rich_listTheory.EL_APPEND2]
  \\ Cases_on `x < n`
  \\ simp [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
           bitstringTheory.el_field, DECIDE ``n <> 0n ==> (SUC (n - 1) = n)``]
  )

val mul_long = Q.prove(
  `!a : word64 b : word64.
    n2w ((w2n a * w2n b) DIV 18446744073709551616) =
    (127 >< 64) (w2w a * w2w b : word128) : word64`,
  Cases
  \\ Cases
  \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_mul_n2w,
         wordsTheory.word_extract_n2w, bitTheory.BITS_THM]
  )

val ConditionTest_not_overflow =
  arm8_stepTheory.ConditionTest
  |> CONJUNCTS
  |> (fn l => List.nth (l, 7))
  |> Q.INST [`c` |-> `FST (SND (add_with_carry (a, b, F)))`,
             `v` |-> `SND (SND (add_with_carry (a, b, F)))`]
  |> REWRITE_RULE [pairTheory.PAIR]

(* some rewrites ----------------------------------------------------------- *)

val arm8_ast = REWRITE_RULE [bop_enc_def, astTheory.shift_distinct] arm8_ast_def
val arm8_enc =
  SIMP_RULE (srw_ss()) [listTheory.LIST_BIND_def] (Q.AP_THM arm8_enc_def `x`)

val encode_rwts =
   let
      open arm8Theory
   in
      [arm8_enc, arm8_ast, arm8_load_store_ast_def, arm8_encode_def, Encode_def,
       e_data_def, e_branch_def, e_load_store_def, e_sf_def,
       e_LoadStoreImmediate_def, EncodeLogicalOp_def, NoOperation_def,
       ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm,
       asmSemTheory.is_test_def
      ]
   end

val enc_rwts =
   [arm8_config, asmPropsTheory.offset_monotonic_def, cmp_cond_def,
    valid_immediate_thm, lem3, lem7, lem7b, lem8, lem9, lem10, lem11,
    arm8_asm_ok] @
   encode_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
   [asmPropsTheory.enc_ok_def, arm8_config, arm8_asm_ok] @ encode_rwts

(* some custom tactics ----------------------------------------------------- *)

val fs = full_simp_tac (srw_ss())
val rfs = rev_full_simp_tac (srw_ss())

val bytes_in_memory_thm = Q.prove(
   `!s state a b c d.
      target_state_rel arm8_target s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      (state.PSTATE.EL = 0w) /\
      ~state.SCTLR_EL1.E0E /\
      ~state.SCTLR_EL1.SA0 /\
      ~state.TCR_EL1.TBI1 /\
      ~state.TCR_EL1.TBI0 /\
      aligned 2 state.PC /\
      (state.MEM (state.PC + 3w) = d) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC) = a) /\
      state.PC + 3w IN s.mem_domain /\
      state.PC + 2w IN s.mem_domain /\
      state.PC + 1w IN s.mem_domain /\
      state.PC IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def,
       arm8_ok_def, miscTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
   \\ rfs []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      target_state_rel arm8_target s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.PC + w + 3w) = d) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w) = a) /\
      state.PC + w + 3w IN s.mem_domain /\
      state.PC + w + 2w IN s.mem_domain /\
      state.PC + w + 1w IN s.mem_domain /\
      state.PC + w IN s.mem_domain`,
   rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def,
       arm8_ok_def, miscTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
   \\ rfs []
   )

local
   fun is_reg_31 tm =
      case Lib.total ((bitstringSyntax.dest_v2w ## wordsSyntax.uint_of_word) o
                      boolSyntax.dest_eq) tm of
         SOME ((_, ty), 31) => ty = ``:5``
       | _ => false
   fun P s = Lib.mem s ["imm", "x"]
   fun gen_v thm =
      let
         val vars = Term.free_vars (Thm.concl thm)
         val l = List.filter (P o fst o Term.dest_var) vars
      in
         Thm.GENL l thm
      end
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.rev o List.map (boolify 8)
   fun step fltr state l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
      in
         case fltr (arm8_stepLib.arm8_step v) of
            [] => raise ERR "next_state_tac" "no step theorem"
          | [th] => (gen_v o Q.INST [`s` |-> state] o Drule.DISCH_ALL) th
          | thms => ( List.app print_thm thms
                    ; raise ERR "next_state_tac" "more than one step theorem"
                    )
      end
   val arm8_state_rule =
      REWRITE_RULE (utilsLib.datatype_rewrites true "arm8" ["arm8_state"])
in
   val filter_reg_31 = List.filter (not o List.exists is_reg_31 o Thm.hyp)
   val filter_vacuous =
     List.filter
       (not o utilsLib.vacuous o
        utilsLib.ALL_HYP_CONV_RULE
          (SIMP_CONV (srw_ss()++bitstringLib.v2w_n2w_ss) []))
   fun next_state_tac pick fltr q (asl, g) =
      (case List.mapPartial asmLib.strip_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step fltr q (pick l))) (asl, g)
end

val comm = ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]

fun next_state_tac0 imp_res pick fltr q =
   next_state_tac pick fltr q
   \\ (if imp_res then imp_res_tac bytes_in_memory_thm else all_tac)
   \\ rfs []
   \\ fs [lem1, lem2, lem3, lem5, lem6, GSYM wordsTheory.WORD_NOT_LOWER]
   \\ asmLib.byte_eq_tac
   \\ rfs [lem13, lem16, lem16b, lem16c, lem17, lem18, lem20, lem21, lem22,
           lem23, lem24, lem25, lem26, comm lem21, comm lem22, lem29, lem32,
           lem33, lem36, lem37,
           combinTheory.UPDATE_APPLY, ShiftValue0,
           alignmentTheory.aligned_numeric,
           arm8_stepTheory.ConditionTest, wordsTheory.ADD_WITH_CARRY_SUB,
           ConditionTest_not_overflow, wordsTheory.WORD_NOT_LOWER_EQUAL]

val next_state_tac01 = next_state_tac0 true List.last filter_reg_31 `ms`

fun next_state_tacN (w, x) fltr (asl, g) =
   let
      val (t, tm) = Option.valOf (asmLib.find_env optionSyntax.is_the g)
      val tac =
         qpat_x_assum `!i:num s:arm8_state. P`
            (qspecl_then [`^t`, `^tm`]
               (strip_assume_tac o SIMP_RULE (srw_ss())
                  [set_sepTheory.fun2set_eq]))
   in
      simp [arm8_ok_def, combinTheory.APPLY_UPDATE_THM,
            alignmentTheory.aligned_numeric]
      \\ imp_res_tac (Q.SPEC w bytes_in_memory_thm2)
      \\ sg `!a. a IN s1.mem_domain ==> ((env ^t ^tm).MEM a = ms.MEM a)`
      >| [tac, all_tac]
      \\ next_state_tac0 false (fn l => List.nth (l, x)) fltr `env ^t ^tm`
   end (asl, g)

val next_state_tac1 = next_state_tacN (`4w`, 0)

fun state_tac thms =
  fs ([asmPropsTheory.sym_target_state_rel, arm8_target_def,
       arm8_config, asmPropsTheory.all_pcs, arm8_ok_def, lem30,
       set_sepTheory.fun2set_eq] @ thms)
  \\ rw [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric]
  \\ rfs []

val shift_cases_tac =
   Cases_on `s`
   >| [Q.SPECL_THEN
         [`n2w ((64 - n1) MOD 64)`,
          `n2w ((64 - n1) MOD 64) + 63w`]
         STRIP_ASSUME_TAC DecodeBitMasks_SOME
       \\ qabbrev_tac `r: word6 = n2w ((64 - n1) MOD 64)`
       \\ qabbrev_tac `q = r + 63w`
       \\ `~((w2n q = 63) /\ r <> 0w)`
       by (Cases_on `r = 0w`
           \\ simp []
           \\ MATCH_MP_TAC
                (wordsLib.WORD_DECIDE ``a <> 63w ==> w2n (a: word6) <> 63``)
           \\ qunabbrev_tac `q`
           \\ blastLib.FULL_BBLAST_TAC),
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC DecodeBitMasks_SOME,
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC DecodeBitMasks_SOME,
       all_tac
   ]
   \\ qpat_x_assum `Abbrev (instr = arm8_enc xx)` assume_tac

fun cmp_case_tac q =
   Cases_on q
   >| [
        next_state_tac1 List.tl,
        next_state_tac1 (fn l => [hd l])
   ]
   \\ state_tac [alignmentTheory.aligned_numeric]
   \\ fs [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

fun next_tac n =
   qexists_tac n
   \\ simp_tac (srw_ss()++boolSimps.CONJ_ss)
        [arm8_next_def, asmPropsTheory.asserts_eval,
         asmPropsTheory.asserts2_eval,
         asmPropsTheory.interference_ok_def, arm8_proj_def]
   \\ NTAC 2 strip_tac
   \\ Q.PAT_ABBREV_TAC `instr = arm8_enc aa`

val enc_rwts_tac =
  NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss++boolSimps.LET_ss) enc_rwts
  \\ qunabbrev_tac `instr`
  \\ simp_tac (std_ss++listSimps.LIST_ss) []

(* -------------------------------------------------------------------------
   arm8 target_ok
   ------------------------------------------------------------------------- *)

val length_arm8_encode = Q.prove(
  `!i. LENGTH (arm8_encode i) = 4`,
  Cases
  \\ rw [arm8_encode_def]
  \\ CASE_TAC
  \\ simp []
  )

val length_arm8_enc = Q.prove(
  `!l. LENGTH (LIST_BIND l arm8_encode) = 4 * LENGTH l`,
  Induct \\ rw [length_arm8_encode]
  )

val arm8_encode_not_nil = Q.prove(
  `!i. arm8_encode i <> []`,
  simp_tac std_ss [GSYM listTheory.LENGTH_NIL, length_arm8_encode]
  )

val arm8_encoding = Q.prove (
  `!i. let l = arm8_enc i in (LENGTH l MOD 4 = 0) /\ l <> []`,
  strip_tac
  \\ asmLib.asm_cases_tac `i`
  \\ simp [arm8_enc_def, length_arm8_enc, length_arm8_encode,
           arm8_encode_fail_def, arm8_ast, arm8_load_store_ast_def]
  \\ REPEAT CASE_TAC
  \\ rw [length_arm8_encode, arm8_encode_not_nil]
  )
  |> SIMP_RULE (srw_ss()++boolSimps.LET_ss)
       [arm8_enc_def, listTheory.LIST_BIND_def]

val arm8_target_ok = Q.prove (
   `target_ok arm8_target`,
   rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        arm8_proj_def, arm8_target_def, arm8_config, arm8_ok_def,
        set_sepTheory.fun2set_eq, arm8_encoding] @ enc_ok_rwts)
   >| [all_tac, Cases_on `ri` \\ Cases_on `cmp`, all_tac, all_tac]
   \\ lfs enc_rwts
   \\ rw[]
   \\ lfs enc_rwts
   \\ blastLib.FULL_BBLAST_TAC
   )

(* -------------------------------------------------------------------------
   arm8 encoder_correct
   ------------------------------------------------------------------------- *)

val ext12 = ``(11 >< 0) : word64 -> word12``
val print_tac = asmLib.print_tac "correct"

Theorem arm8_encoder_correct:
    encoder_correct arm8_target
Proof
   simp [asmPropsTheory.encoder_correct_def, arm8_target_ok]
   \\ qabbrev_tac `state_rel = target_state_rel arm8_target`
   \\ rw [arm8_target_def, asmSemTheory.asm_step_def, arm8_config]
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
         \\ next_tac `0`
         \\ enc_rwts_tac
         \\ next_state_tac01
         \\ state_tac []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ REVERSE (Cases_on `arm8_enc_mov_imm c`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ enc_rwts_tac
             \\ next_state_tac01
             \\ imp_res_tac lem27
             \\ state_tac []
            )
         \\ REVERSE (Cases_on `arm8_enc_mov_imm ~c`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ enc_rwts_tac
             \\ next_state_tac01
             \\ imp_res_tac lem27
             \\ state_tac [lem28]
            )
         \\ REVERSE (Cases_on `EncodeBitMask c`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ Cases_on `r`
             \\ enc_rwts_tac
             \\ imp_res_tac Decode_EncodeBitMask
             \\ next_state_tac01
             \\ state_tac []
            )
         \\ next_tac `3`
         \\ enc_rwts_tac
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac01
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tacN (`4w`, 1) filter_reg_31
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tacN (`8w`, 1) filter_reg_31
         \\ next_state_tacN (`12w`, 0) filter_reg_31
         \\ state_tac []
         \\ blastLib.BBLAST_TAC
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
            \\ next_tac `0`
            \\ Cases_on `r`
            >| [Cases_on `b`,
                Cases_on `(b = Xor) /\ (c = -1w)`
                >| [all_tac,
                    Cases_on `b` \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) []
                   ]
               ]
            \\ enc_rwts_tac
            \\ fs []
            \\ imp_res_tac Decode_EncodeBitMask
            \\ fs []
            \\ next_state_tac01
            \\ state_tac []
            )
         >- (
            (*--------------
                Shift
              --------------*)
            print_tac "Shift"
            \\ next_tac `0`
            \\ shift_cases_tac
            \\ enc_rwts_tac
            \\ fs []
            \\ next_state_tac01
            \\ state_tac [lsr, asr, ror]
            >| [
                imp_res_tac lsl,
                imp_res_tac (lsl |> Q.SPEC `0w` |> SIMP_RULE (srw_ss()) []),
                imp_res_tac asr2
            ]
            \\ simp []
            )
         >- (
            (*--------------
                Div
              --------------*)
            print_tac "Div"
            \\ next_tac `0`
            \\ enc_rwts_tac
            \\ next_state_tac01
            \\ state_tac []
            )
         >- (
            (*--------------
                LongMul
              --------------*)
            print_tac "LongMul"
            \\ next_tac `1`
            \\ enc_rwts_tac
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tac01
            \\ next_state_tacN (`4w`, 0) filter_reg_31
            \\ state_tac [GSYM wordsTheory.word_mul_def, mul_long,
                          arm8Theory.ExtendWord_def]
            )
         >- (
            (*--------------
                LongDiv
              --------------*)
            print_tac "LongDiv"
            \\ enc_rwts_tac
            )
         >- (
            (*--------------
                AddCarry
              --------------*)
            print_tac "AddCarry"
            \\ next_tac `4`
            \\ enc_rwts_tac
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tac0 true List.last filter_vacuous `ms`
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tacN (`4w`, 1) filter_reg_31
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tacN (`8w`, 1) filter_reg_31
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tacN (`12w`, 1) filter_reg_31
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tacN (`16w`, 1) filter_reg_31
            \\ state_tac []
            \\ rw [wordsTheory.add_with_carry_def]
            \\ Cases_on `ms.REG (n2w i) = 0w`
            \\ full_simp_tac arith_ss []
            )
         >- (
            (*--------------
                AddOverflow
              --------------*)
            print_tac "AddOverflow"
            \\ next_tac `1`
            \\ enc_rwts_tac
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tac01
            \\ next_state_tacN (`4w`, 0) filter_reg_31
            \\ state_tac [integer_wordTheory.overflow_add]
            )
         >- (
            (*--------------
                SubOverflow
              --------------*)
            print_tac "SubOverflow"
            \\ next_tac `1`
            \\ enc_rwts_tac
            \\ asmLib.split_bytes_in_memory_tac 4
            \\ next_state_tac01
            \\ next_state_tacN (`4w`, 0) filter_reg_31
            \\ state_tac
                 [SIMP_RULE (srw_ss()) [] integer_wordTheory.sub_overflow]
            \\ fs []
            )
         )
         >- (
            (*--------------
                Mem
              --------------*)
            print_tac "Mem"
            \\ Cases_on `a`
            \\ Cases_on `m`
            >| [
               Cases_on `c = sw2sw ((8 >< 0) c : word9)`
               >| [next_tac `0`
                   \\ Cases_on
                        `~word_msb c /\ (c = w2w (^ext12 (c >>> 3)) << 3)`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on `c = w2w (^ext12 (c >>> 3)) << 3`
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
               ,
               next_tac `0`
               \\ Cases_on `~word_msb c /\ (c = w2w (^ext12 c))`
               ,
               Cases_on `c = sw2sw ((8 >< 0) c : word9)`
               >| [next_tac `0`
                   \\ Cases_on
                        `~word_msb c /\ (c = w2w (^ext12 (c >>> 3)) << 3)`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on `c = w2w (^ext12 (c >>> 3)) << 3`
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
               ,
               next_tac `0`
               \\ Cases_on `~word_msb c /\ (c = w2w (^ext12 c))`
            ]
            \\ enc_rwts_tac
            \\ rfs []
            \\ fs [lem7, lem7b, lem31, lem35]
            \\ TRY (`aligned 3 (c + ms.REG (n2w n'))`
                    by (imp_res_tac lem14 \\ NO_TAC))
            \\ split_bytes_in_memory_tac 4
            \\ next_state_tac01
            \\ TRY (asmLib.split_bytes_in_memory_tac 4
                    \\ next_state_tacN (`4w`, 1) filter_reg_31)
            \\ state_tac
                  [arm8_stepTheory.mem_dword_def, arm8_stepTheory.mem_word_def,
                   arm8Theory.ExtendWord_def, set_sepTheory.fun2set_eq]
            \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
            \\ NTAC 2 (lrw [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM])
            \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
            )
         (*--------------
             FP
           --------------*)
         \\ print_tac "FP"
         \\ Cases_on `f`
         \\ enc_rwts_tac

      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac `0`
      \\ enc_rwts_tac
      \\ next_state_tac01
      \\ state_tac [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ next_tac `1`
      \\ Cases_on `r`
      >| [
         Cases_on `c`
         \\ enc_rwts_tac
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac0 true List.last List.tl `ms`
         >| [
            cmp_case_tac `ms.REG (n2w n) = ms.REG (n2w n')`,
            cmp_case_tac `ms.REG (n2w n) <+ ms.REG (n2w n')`,
            cmp_case_tac `ms.REG (n2w n) < ms.REG (n2w n')`,
            cmp_case_tac `(ms.REG (n2w n) && ms.REG (n2w n')) = 0w`,
            cmp_case_tac `ms.REG (n2w n) <> ms.REG (n2w n')`,
            cmp_case_tac `~(ms.REG (n2w n) <+ ms.REG (n2w n'))`,
            cmp_case_tac `~(ms.REG (n2w n) < ms.REG (n2w n'))`,
            cmp_case_tac `(ms.REG (n2w n) && ms.REG (n2w n')) <> 0w`
         ],
         Cases_on `c`
         \\ enc_rwts_tac
         \\ fs []
         \\ fs []
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ imp_res_tac Decode_EncodeBitMask
         \\ next_state_tac0 true List.last List.tl `ms`
         >| [
            cmp_case_tac `ms.REG (n2w n) = c'`,
            cmp_case_tac `ms.REG (n2w n) = c'`,
            cmp_case_tac `ms.REG (n2w n) <+ c'`,
            cmp_case_tac `ms.REG (n2w n) <+ c'`,
            cmp_case_tac `ms.REG (n2w n) < c'`,
            cmp_case_tac `ms.REG (n2w n) < c'`,
            cmp_case_tac `(ms.REG (n2w n) && c') = 0w`,
            cmp_case_tac `ms.REG (n2w n) <> c'`,
            cmp_case_tac `ms.REG (n2w n) <> c'`,
            cmp_case_tac `~(ms.REG (n2w n) <+ c')`,
            cmp_case_tac `~(ms.REG (n2w n) <+ c')`,
            cmp_case_tac `~(ms.REG (n2w n) < c')`,
            cmp_case_tac `~(ms.REG (n2w n) < c')`,
            cmp_case_tac `(ms.REG (n2w n) && c') <> 0w`
         ]
      ]
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ next_tac `0`
      \\ enc_rwts_tac
      \\ next_state_tac01
      \\ state_tac [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac `0`
      \\ enc_rwts_tac
      \\ next_state_tac01
      \\ state_tac [alignmentTheory.aligned_extract]
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc">>
      Cases_on`sw2sw (INT_MINw: word20) ≤ c ∧ c ≤ sw2sw (INT_MAXw: word20)`
      >- (
        next_tac`0`
        \\ enc_rwts_tac
        \\ next_state_tac01
        \\ state_tac [alignmentTheory.aligned_extract]
        \\ blastLib.FULL_BBLAST_TAC)
      \\ next_tac `5`
      \\ enc_rwts_tac
      \\ qpat_x_assum`A ∨ B` kall_tac
      \\ `n2w n ≠ 26w:word5` by simp[lem1]
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tac01
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tacN (`4w`, 1) filter_reg_31
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tacN (`8w`, 1) filter_reg_31
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tacN (`12w`, 1) filter_reg_31
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tacN (`16w`, 1) filter_reg_31
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tacN (`20w`, 1) filter_reg_31
      \\ state_tac [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC)
QED

val () = export_theory ()
