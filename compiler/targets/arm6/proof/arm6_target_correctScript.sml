open HolKernel Parse boolLib bossLib
open asmLib arm6_targetTheory;

val () = new_theory "arm6_target_correct"

val () = wordsLib.guess_lengths ()

(* some lemmas ---------------------------------------------------------- *)

val n_tm = ``n < 16 /\ n <> 15n``

val arm6_asm_state = REWRITE_RULE [DECIDE ``n < 15 = ^n_tm``] arm6_asm_state_def

val lem1 = Q.prove(
   `!n m. ^n_tm ==> RName_PC <> R_mode m (n2w n)`,
   CONV_TAC (Conv.ONCE_DEPTH_CONV SYM_CONV)
   \\ simp [arm_stepTheory.R_x_pc]
   )

val lem2 = asmLib.v2w_BIT_n2w 4
val lem3 = asmLib.v2w_BIT_n2w 5

val lem4 =
   blastLib.BBLAST_PROVE ``0w <= c /\ c <= 4095w ==> c <=+ 4095w: word32``

val lem5 =
   blastLib.BBLAST_PROVE
      ``~(0w <= c) /\ 0xFFFFF001w <= c ==> -1w * c <=+ 4095w: word32``

val lem6 = Q.prove(
   `!s state c n.
      arm6_asm_state s state /\ ^n_tm /\ aligned 2 (c + s.regs n) ==>
      aligned 2 (c + state.REG (R_mode state.CPSR.M (n2w n)))`,
   rw [arm6_asm_state, alignmentTheory.aligned_extract]
   \\ pop_assum mp_tac
   \\ simp []
   )

val lem7 = Q.prove(
   `!a: word24. aligned 2 (sw2sw ((a @@ (0w: word2)): 26 word) : word32)`,
   srw_tac [wordsLib.WORD_EXTRACT_ss] [alignmentTheory.aligned_extract]
   )

fun bprove tm =
   Q.prove (tm, simp [markerTheory.Abbrev_def, alignmentTheory.aligned_extract]
                \\ blastLib.BBLAST_TAC)

val jmp_tm =
   ``0xFE00000Cw <= c /\ c <= 0x2000007w: word32 /\ aligned 2 (c: word32)``

val lem8 = bprove
   `^jmp_tm ==>
    0xFE000000w <= c + 0xFFFFFFF8w /\ 0xFE000000w <= c + 0xFFFFFFF4w /\
    c + 0xFFFFFFF8w <= 0x1FFFFFCw /\ c + 0xFFFFFFF4w <= 0x1FFFFFCw: word32`

val lem9 = bprove
  `Abbrev (a = (25 >< 2) (c + 0xFFFFFFF8w): word24) /\ a ' 23 /\ ^jmp_tm ==>
   (-1w *
   (v2w
      [~a ' 22; ~a ' 21; ~a ' 20; ~a ' 19; ~a ' 18; ~a ' 17; ~a ' 16;
       ~a ' 15; ~a ' 14; ~a ' 13; ~a ' 12; ~a ' 11; ~a ' 10; ~a ' 9;
       ~a ' 8; ~a ' 7; ~a ' 6; ~a ' 5; ~a ' 4; ~a ' 3; ~a ' 2; ~a ' 1;
       ~a ' 0; T; T] + 1w) = c - 8w)`

val lem10 = bprove
  `Abbrev (a = (25 >< 2) (c + 0xFFFFFFF8w): word24) /\ ~a ' 23 /\ ^jmp_tm ==>
   (v2w
      [a ' 22; a ' 21; a ' 20; a ' 19; a ' 18; a ' 17; a ' 16; a ' 15;
       a ' 14; a ' 13; a ' 12; a ' 11; a ' 10; a ' 9; a ' 8; a ' 7; a ' 6;
       a ' 5; a ' 4; a ' 3; a ' 2; a ' 1; a ' 0; F; F] = c - 8w)`

val lem11 =
   (REWRITE_RULE [wordsTheory.WORD_ADD_0] o  Q.INST [`c` |-> `0w`] o
    Drule.SPEC_ALL) lem6

val lem12 = Q.prove(
   `!x: word32. aligned 2 x ==> ~word_bit 1 x /\ ~word_bit 0 x`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

(*
val lem12 =
   Drule.GEN_ALL
      (Drule.IMP_TRANS lem11
         (Q.SPEC `state.REG (R_mode state.CPSR.M (n2w n))` lem12))
*)

val lem15 = bprove
  `Abbrev (a = (25 >< 2) (c + 0xFFFFFFF8w): word24) /\ ^jmp_tm ==>
     (sw2sw
        ((v2w
            [a ' 23; a ' 22; a ' 21; a ' 20; a ' 19; a ' 18; a ' 17; a ' 16;
             a ' 15; a ' 14; a ' 13; a ' 12; a ' 11; a ' 10; a ' 9; a ' 8;
             a ' 7; a ' 6; a ' 5; a ' 4; a ' 3; a ' 2; a ' 1; a ' 0]: word24
             @@ (0w: word2)) : 26 word) = c - 8w)`

val lem16 = bprove
   `!c r: word32.
       Abbrev (r = c + 0xFFFFFFF4w) /\ ^jmp_tm ==>
       (sw2sw
        ((v2w
          [r ' 25; r ' 24; r ' 23; r ' 22; r ' 21; r ' 20; r ' 19; r ' 18;
           r ' 17; r ' 16; r ' 15; r ' 14; r ' 13; r ' 12; r ' 11; r ' 10;
           r ' 9; r ' 8; r ' 7; r ' 6; r ' 5; r ' 4; r ' 3; r ' 2]: word24
          @@ (0w: word2)) : 26 word) = c - 12w)`

val lem18 =
   blastLib.BBLAST_PROVE
     ``((11 >< 8) (v2w [F; F; F; F; b7; b6; b5; b4; b3; b2; b1; b0] : word12) =
        0w: word4) /\
       ((11 >< 8) (v2w [T; T; F; F; b7; b6; b5; b4; b3; b2; b1; b0] : word12) =
        12w: word4)``

val lem19 =
   blastLib.BBLAST_PROVE
     ``!c: word32.
          c + 0xFFFFFFF8w <+ 256w ==>
          (w2w (v2w
                [c:word32 ' 7 = c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
                 c ' 6 = c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 = c ' 4 \/ c ' 3;
                 c ' 4 = c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0]: word8) =
           c - 8w: word32)``

fun tac n =
   simp [Ntimes armTheory.EncodeARMImmediate_aux_def n,
         wordsLib.WORD_DECIDE ``-1w = 15w: word4``]
   \\ strip_tac
   \\ qunabbrev_tac `i`
   \\ simp []
   \\ CONV_TAC
        (LAND_CONV (RAND_CONV (Conv.DEPTH_CONV blastLib.BBLAST_CONV)
                               THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV))
   \\ simp []
   \\ blastLib.FULL_BBLAST_TAC
   \\ blastLib.BBLAST_TAC

val decode_imm_thm = Q.prove(
   `!c.
      valid_immediate c ==>
      let imm12 = THE (EncodeARMImmediate c) in
         w2w (v2w [imm12 ' 7; imm12 ' 6; imm12 ' 5; imm12 ' 4;
                   imm12 ' 3; imm12 ' 2; imm12 ' 1; imm12 ' 0]: word8) #>>
         w2n (v2w [imm12 ' 11; imm12 ' 10; imm12 ' 9; imm12 ' 8; F] : word5) =
         c`,
   strip_tac
   \\ simp_tac std_ss [valid_immediate_def, armTheory.EncodeARMImmediate_def]
   \\ qabbrev_tac `i = EncodeARMImmediate_aux (15w,c)`
   \\ pop_assum mp_tac
   \\ Cases_on `(31 >< 8) c = 0w: word24` >- tac 1
   \\ Cases_on `(31 >< 8) (c #<< 2) = 0w: word24` >- tac 2
   \\ Cases_on `(31 >< 8) (c #<< 4) = 0w: word24` >- tac 3
   \\ Cases_on `(31 >< 8) (c #<< 6) = 0w: word24` >- tac 4
   \\ Cases_on `(31 >< 8) (c #<< 8) = 0w: word24` >- tac 5
   \\ Cases_on `(31 >< 8) (c #<< 10) = 0w: word24` >- tac 6
   \\ Cases_on `(31 >< 8) (c #<< 12) = 0w: word24` >- tac 7
   \\ Cases_on `(31 >< 8) (c #<< 14) = 0w: word24` >- tac 8
   \\ Cases_on `(31 >< 8) (c #<< 16) = 0w: word24` >- tac 9
   \\ Cases_on `(31 >< 8) (c #<< 18) = 0w: word24` >- tac 10
   \\ Cases_on `(31 >< 8) (c #<< 20) = 0w: word24` >- tac 11
   \\ Cases_on `(31 >< 8) (c #<< 22) = 0w: word24` >- tac 12
   \\ Cases_on `(31 >< 8) (c #<< 24) = 0w: word24` >- tac 13
   \\ Cases_on `(31 >< 8) (c #<< 26) = 0w: word24` >- tac 14
   \\ Cases_on `(31 >< 8) (c #<< 28) = 0w: word24` >- tac 15
   \\ Cases_on `(31 >< 8) (c #<< 30) = 0w: word24` >- tac 16
   \\ tac 17
   )

val decode_imm_thm = SIMP_RULE (bool_ss++boolSimps.LET_ss) [] decode_imm_thm

val decode_some_encode_immediate =
   decode_imm_thm
   |> Q.SPEC `c`
   |> Q.DISCH `EncodeARMImmediate c = SOME x`
   |> SIMP_RULE std_ss [valid_immediate_def]
   |> Drule.GEN_ALL

val decode_some_encode_neg_immediate =
   decode_imm_thm
   |> Q.SPEC `~c`
   |> Q.DISCH `EncodeARMImmediate (~c) = SOME x`
   |> SIMP_RULE std_ss [valid_immediate_def]
   |> Drule.GEN_ALL

val decode_imm12_thm =
   blastLib.BBLAST_PROVE
     ``!c: word32.
       c <=+ 4095w ==>
       (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6;
                  c ' 5; c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c)``

val decode_neg_imm12_thm = Q.prove(
   `!c: word32 d.
       0xFFFFF001w <= c /\ ~(0w <= c) /\ Abbrev (d = -1w * c) ==>
       (-1w *
        w2w (v2w [d ' 11; d ' 10; d ' 9; d ' 8; d ' 7; d ' 6;
                  d ' 5; d ' 4; d ' 3; d ' 2; d ' 1; d ' 0] : word12) = c)`,
   rw []
   \\ qunabbrev_tac `d`
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm1 = Q.prove(
   `!c: word32.
       8w <= c /\ c <= 263w ==>
       (EncodeARMImmediate (c + 0xFFFFFFF8w) =
        SOME ((7 >< 0) (c + 0xFFFFFFF8w)))`,
   rw [armTheory.EncodeARMImmediate_def,
       Once armTheory.EncodeARMImmediate_aux_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm2 =
   blastLib.BBLAST_PROVE
     ``!c: word32.
         8w <= c /\ c + 0xFFFFFFF8w <+ 256w ==>
         (w2w (v2w [c ' 7 <=> c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
                    c ' 6 <=> c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 <=> c ' 4 \/ c ' 3;
                    c ' 4 <=> c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0]: word8) =
         c - 8w)``

val decode_imm8_thm3 = Q.prove(
   `!c: word32.
       ~(8w <= c) /\ 0xFFFFFF09w <= c ==>
       (EncodeARMImmediate (-1w * c + 8w) = SOME ((7 >< 0) (-1w * c + 8w)))`,
   rw [armTheory.EncodeARMImmediate_def,
       Once armTheory.EncodeARMImmediate_aux_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm4 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         8w <= c /\ c <= 0x10007w /\ ~(c + 0xFFFFFFF8w <+ 256w) ==>
  (c + p =
   w2w
      (v2w
         [c ' 7 <=> c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 6 <=> c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 <=> c ' 4 \/ c ' 3;
          c ' 4 <=> c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0] : word8) +
    p +
    w2w
      (v2w
         [c ' 15 <=>
          c ' 14 \/ c ' 13 \/ c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/
          c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 14 <=>
          c ' 13 \/ c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/
          c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 13 <=>
          c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/
          c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 12 <=>
          c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/
          c ' 4 \/ c ' 3;
          c ' 11 <=>
          c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/
          c ' 3;
          c ' 10 <=>
          c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 9 <=> c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 8 <=> c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3] : word8) #>> 24 +
    8w)``

val decode_imm8_thm5 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         ~(8w <= c) /\ 0xFFFF0009w <= c /\ -1w * c + 8w <+ 256w ==>
  (c + p =
   -1w *
   w2w
     (v2w
        [c ' 7 <=>
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 6 <=>
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 5 <=> ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 4 <=> ~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
         c ' 3 <=> c ' 2 \/ c ' 1 \/ c ' 0; c ' 2 <=> ~c ' 1 /\ ~c ' 0;
         ~c ' 1 <=> c ' 0; c ' 0]: word8) + p + 8w)``

val decode_imm8_thm6 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         ~(8w <= c) /\ 0xFFFF0009w <= c /\ ~(-1w * c + 8w <+ 256w) ==>
  (c + p =
   -1w *
   w2w
     (v2w
        [c ' 7 <=>
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 6 <=>
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 5 <=> ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 4 <=> ~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
         c ' 3 <=> c ' 2 \/ c ' 1 \/ c ' 0; c ' 2 <=> ~c ' 1 /\ ~c ' 0;
         ~c ' 1 <=> c ' 0; c ' 0]: word8) + p +
   -1w *
   w2w
     (v2w
        [c ' 15 <=>
         ~c ' 14 /\ ~c ' 13 /\ ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\
         ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 14 <=>
         ~c ' 13 /\ ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\
         ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 13 <=>
         ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 12 <=>
         ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 11 <=>
         ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\
         ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 10 <=>
         ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 9 <=>
         ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 8 <=>
         ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0)]: word8) #>> 24 + 8w)``

val word_lo_not_carry = Q.prove(
   `!a b. a <+ b = ~CARRY_OUT a (~b) T`,
   simp [wordsTheory.ADD_WITH_CARRY_SUB, wordsTheory.WORD_NOT_LOWER_EQUAL]
   )

val word_lt_n_eq_v = Q.prove(
   `!a b: word32. a < b = (word_bit 31 (a + -1w * b) <> OVERFLOW a (~b) T)`,
   simp [wordsTheory.ADD_WITH_CARRY_SUB, GSYM wordsTheory.WORD_LO]
   \\ blastLib.BBLAST_TAC
   )

val SetPassCondition =
   utilsLib.map_conv
     (SIMP_CONV (srw_ss()++boolSimps.LET_ss) [armTheory.SetPassCondition_def])
     [``SetPassCondition 0w s``,
      ``SetPassCondition 1w s``,
      ``SetPassCondition 2w s``,
      ``SetPassCondition 3w s``,
      ``SetPassCondition 10w s``,
      ``SetPassCondition 11w s``,
      ``SetPassCondition 14w s``]

local
   open armTheory
   val () = utilsLib.setStepConv (Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV)
   val EV = utilsLib.STEP (K (utilsLib.datatype_rewrites true "arm" ["SRType"]),
                           ``s:arm_state``)
   val Shift_C_rwt =
      EV [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def]
         [] []
         ``Shift_C (value,typ,amount,carry_in)
           : arm_state -> ('a word # bool) # arm_state``
         |> hd
         |> SIMP_RULE std_ss []
   val arm_imm_lem = Q.prove(
      `((if n = 0 then ((w, c1), s) else ((w #>> n, c2), s)) =
        ((w #>> n, if n = 0 then c1 else c2), s)) /\
       (2 * w2n (v2w [a; b; c; d] : word4) =
        w2n (v2w [a; b; c; d; F] : word5))`,
      rw [] \\ wordsLib.n2w_INTRO_TAC 5 \\ blastLib.BBLAST_TAC
      )
in
   val ARMExpandImm_C_rwt =
      EV [armTheory.ARMExpandImm_C_def, Shift_C_rwt, arm_imm_lem] [] []
        ``ARMExpandImm_C (^(bitstringSyntax.mk_vec 12 0), c)``
        |> hd
        |> REWRITE_RULE [wordsTheory.w2n_eq_0]
end

val reg_mode_eq = Q.prove(
   `!m ms1 ms2.
       (ms1.REG o R_mode m = ms2.REG o R_mode m) =
       (!i. ms1.REG (R_mode m (n2w i)) = ms2.REG (R_mode m (n2w i))) /\
       (ms1.REG RName_PC = ms2.REG RName_PC)`,
   rw [FUN_EQ_THM]
   \\ eq_tac
   \\ strip_tac
   >- metis_tac [arm_stepTheory.R_mode]
   \\ Cases
   \\ simp []
   )

val aligned_add = Q.prove(
   `!p a b. aligned p a ==> (aligned p (a + b) = aligned p b)`,
   metis_tac [wordsTheory.WORD_ADD_COMM, alignmentTheory.aligned_add_sub]
   )


(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open armTheory
   in
      [arm6_enc_def, arm6_bop_def, arm6_sh_def, arm6_cmp_def, arm6_encode_def,
       encode_def, e_branch_def, e_data_def, e_load_def, e_store_def,
       EncodeImmShift_def
       ]
   end

val enc_rwts =
   [arm6_config_def, asmPropsTheory.offset_monotonic_def,
    arm_stepTheory.Aligned, alignmentTheory.aligned_0,
    alignmentTheory.aligned_numeric] @
   encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
   [asmPropsTheory.enc_ok_def, arm6_config_def] @
   encode_rwts @ asmLib.asm_ok_rwts

val dec_rwts =
   [arm6_dec_def, decode_word_def, SetPassCondition, fetch_word_def]

(* some custom tactics ---------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!s state a b c d.
      arm6_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      (state.Architecture = ARMv6) /\
      ~state.Extensions Extension_Security /\
      ~state.CPSR.T /\
      ~state.CPSR.J /\
      ~state.CPSR.E /\
      GoodMode state.CPSR.M /\
      ((1 >< 0) (state.REG RName_PC) = 0w: word32) /\
      aligned 2 (state.REG RName_PC) /\
      (state.MEM (state.REG RName_PC + 3w) = d) /\
      (state.MEM (state.REG RName_PC + 2w) = c) /\
      (state.MEM (state.REG RName_PC + 1w) = b) /\
      (state.MEM (state.REG RName_PC) = a) /\
      state.REG RName_PC + 3w IN s.mem_domain /\
      state.REG RName_PC + 2w IN s.mem_domain /\
      state.REG RName_PC + 1w IN s.mem_domain /\
      state.REG RName_PC IN s.mem_domain`,
   rw [arm6_asm_state_def, arm6_ok_def, asmSemTheory.bytes_in_memory_def,
       set_sepTheory.fun2set_eq]
   \\ rfs [alignmentTheory.aligned_extract]
   )

val bytes_in_memory_thm2 = Q.prove(
   `!s state w a b c d.
      arm6_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.REG RName_PC + w + 3w) = d) /\
      (state.MEM (state.REG RName_PC + w + 2w) = c) /\
      (state.MEM (state.REG RName_PC + w + 1w) = b) /\
      (state.MEM (state.REG RName_PC + w) = a) /\
      state.REG RName_PC + w + 3w IN s.mem_domain /\
      state.REG RName_PC + w + 2w IN s.mem_domain /\
      state.REG RName_PC + w + 1w IN s.mem_domain /\
      state.REG RName_PC + w IN s.mem_domain`,
   rw [arm6_asm_state_def, arm6_ok_def, asmSemTheory.bytes_in_memory_def,
       set_sepTheory.fun2set_eq]
   \\ rfs []
   )

val arm_op2 = HolKernel.syntax_fns2 "arm"

local
   fun gen_v P thm =
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
   val step6 = arm_stepLib.arm_eval "v6"
   fun step P state x l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
      in
         (gen_v P o Q.INST [`s` |-> state] o Drule.DISCH_ALL o step6) (x, v)
      end
   val dec6 = arm_stepLib.arm_decode (arm_configLib.mk_config_terms "v6")
   val arm_state_rule =
      REWRITE_RULE (utilsLib.datatype_rewrites true "arm" ["arm_state", "PSR"])
   fun dec x (tm,st) =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         (x, l) |> dec6 |> hd
                |> Drule.DISCH_ALL
                |> Thm.INST [``s: arm_state`` |-> st]
                |> arm_state_rule
                |> REWRITE_RULE [th1]
      end
   val (_, _, dest_DecodeARM, is_DecodeARM) = arm_op2 "DecodeARM"
   val find_DecodeARM =
      HolKernel.bvk_find_term (is_DecodeARM o snd) dest_DecodeARM
in
   fun decode_tac x (asl, g) =
      (case find_DecodeARM g of
          SOME tms =>
           let
              val dec_thm = dec x tms
           (*  val () = (print_thm dec_thm; print "\n") *)
           in
              asm_simp_tac (srw_ss())
                [dec_thm, lem2, lem3, arm6_dec_aux_def, decode_imm12_def,
                 ARMExpandImm_C_rwt, armTheory.DecodeImmShift_def]
              \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
              \\ lfs [lem2, lem3, lem4, decode_some_encode_immediate,
                      decode_imm_thm, decode_imm12_thm,
                      arm6_bop_dec_def, arm6_cmp_dec_def, arm6_sh_dec_def,
                      arm_stepTheory.Aligned]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac pick P state x (asl, g) =
      (case List.mapPartial asmLib.strip_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step P state x (pick l))) (asl, g)
end

fun next_state_tac0 f q l =
   next_state_tac f (K false) q l
   \\ imp_res_tac bytes_in_memory_thm
   \\ fs []
   \\ asmLib.byte_eq_tac
   \\ rfs [lem2, lem3, lem4, lem7, decode_imm12_thm, combinTheory.UPDATE_APPLY,
           decode_imm_thm, alignmentTheory.aligned_0,
           alignmentTheory.aligned_numeric]

val next_state_tac01 = next_state_tac0 List.last `ms` [true]

val enc_ok_tac = full_simp_tac (srw_ss()++boolSimps.LET_ss) enc_ok_rwts

fun next_tac n =
   qexists_tac n
   \\ simp_tac (srw_ss()++boolSimps.CONJ_ss)
         [arm6_next_def, asmPropsTheory.asserts_eval, reg_mode_eq,
          asmPropsTheory.interference_ok_def, arm6_proj_def]
   \\ NTAC 2 strip_tac

local
   val i_tm = ``R_mode ms.CPSR.M (n2w i)``
in
   val reg_tac =
      asmLib.env_tac
        (fn (t, s) =>
           let
              val r = utilsLib.rhsc (SIMP_CONV (srw_ss()) [] ``^s.REG``)
           in
              (``!i. (env ^t ^s).REG ^i_tm = ^r ^i_tm``,
               qpat_assum `!i:num s:arm_state. P`
                  (fn th =>
                     strip_assume_tac
                        (SIMP_RULE (srw_ss()) [] (Q.SPECL [`^t`, `^s`] th))
                     \\ assume_tac th)
               \\ fs [DISCH_ALL arm_stepTheory.R_x_not_pc,
                      combinTheory.UPDATE_APPLY]
              )
           end)
end

fun next_state_tac1 f l (asl, g) =
   let
      val (t, tm) = Option.valOf (asmLib.find_env g)
      val tac =
         qpat_assum `!i:num s:arm_state. P`
            (qspecl_then [`^t`, `^tm`]
               (strip_assume_tac o SIMP_RULE (srw_ss())
                  [set_sepTheory.fun2set_eq]))
   in
      simp [arm6_ok_def, combinTheory.APPLY_UPDATE_THM,
            alignmentTheory.aligned_numeric]
      \\ imp_res_tac bytes_in_memory_thm2
      \\ `!a. a IN s1.mem_domain ==> ((env ^t ^tm).MEM a = ms.MEM a)` by tac
      \\ next_state_tac0 f `env ^t ^tm` l
   end (asl, g)

fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

local
   val th = REWRITE_RULE [arm6_ok_def] arm6_asm_state
in
   fun state_tac thms =
      REPEAT (qpat_assum `NextStateARM q = z` (K all_tac))
      \\ fs ([th, decode_imm_thm, combinTheory.APPLY_UPDATE_THM,
              alignmentTheory.aligned_numeric] @ thms)
      \\ reg_tac
      \\ rw [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
             updateTheory.APPLY_UPDATE_ID, arm_stepTheory.R_mode_11, lem1]
end

local
   val th = REWRITE_RULE [arm6_ok_def] arm6_asm_state
in
   fun state_tac1 thms =
      REPEAT (qpat_assum `NextStateARM q = z` kall_tac)
      \\ REPEAT (qpat_assum `ms.MEM a = b` kall_tac)
      \\ REPEAT (qpat_assum `a IN s1.mem_domain` kall_tac)
      \\ REPEAT (qpat_assum `bytes_in_memory q0 q1 q2 q3` kall_tac)
      \\ pop_assum kall_tac
      \\ fs ([th, asmPropsTheory.all_pcs, combinTheory.APPLY_UPDATE_THM,
              alignmentTheory.aligned_numeric] @ thms)
      \\ REPEAT strip_tac
      \\ reg_tac
      \\ fs [DISCH_ALL arm_stepTheory.R_x_not_pc, combinTheory.UPDATE_APPLY]
      \\ reg_tac
      \\ rw [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
             updateTheory.APPLY_UPDATE_ID, arm_stepTheory.R_mode_11, lem1]
end

fun load_store_tac {neg, store} =
   (if neg then qabbrev_tac `d = -1w * c` \\ imp_res_tac decode_neg_imm12_thm
    else all_tac)
   \\ (if store
          then next_state_tac01
               \\ state_tac [FUN_EQ_THM, set_sepTheory.fun2set_eq]
               \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
               \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
       else next_state_tac0 List.last `ms` [true, false]
            \\ state_tac [set_sepTheory.fun2set_eq]
            \\ blastLib.BBLAST_TAC
            )

local
   val BLAST_BYTE_EQ_CONV =
      FORK_CONV
         (blastLib.BBLAST_CONV,
          FORK_CONV
             (blastLib.BBLAST_CONV,
              FORK_CONV
                 (blastLib.BBLAST_CONV,
                  LAND_CONV blastLib.BBLAST_CONV)))
      THENC REWRITE_CONV []
in
   val blast_byte_eq_tac =
      qpat_assum `(xx = yy) ==> pp`
         (assume_tac o (CONV_RULE BLAST_BYTE_EQ_CONV))
end

local
   fun tac b =
      blast_byte_eq_tac
      \\ qunabbrev_tac `p`
      \\ simp []
      \\ state_tac1 []
      \\ imp_res_tac lem16
      \\ fs [Q.SPEC `F` markerTheory.Abbrev_def,
             blastLib.BBLAST_PROVE ``a <> b ==> (0w <> a + -1w * b: word32)``,
             blastLib.BBLAST_PROVE ``a <> b ==> (0w <> -1w * b + a: word32)``,
             word_lo_not_carry, word_lt_n_eq_v]
      \\ fs ([Abbr `r`, lem7, alignmentTheory.aligned_numeric,
              alignmentTheory.aligned_add_sub, aligned_add] @
             (if b then [Abbr `q`] else []))
   fun tacs neg imm =
      let
         fun f l = List.map (next_state_tac1 hd) (if neg then List.rev l else l)
      in
        [
         (* Equal *)
         Cases_on `q = 0w`
         >| f [[false, true], [true, false]]
         \\ tac false,
         (* Lower *)
         Cases_on `FST (SND p)`
         >| f [[true, false], [false, true]]
         \\ tac false,
         (* Less *)
         Cases_on `word_bit 31 q = SND (SND p)`
         >| f [[true, false], [false, true]]
         \\ tac true,
         (* Test *)
         (if imm then Cases_on `ms.REG (R_mode ms.CPSR.M (n2w n)) && c' = 0w`
          else Cases_on `ms.REG (R_mode ms.CPSR.M (n2w n)) &&
                         ms.REG (R_mode ms.CPSR.M (n2w n')) = 0w`)
         >| f [[false, true], [true, false]]
         \\ tac true
        ]
      end
in
   fun cmp_tac imm =
      Cases_on `c`
      \\ lfs ([alignmentTheory.aligned_numeric,
               lem8] @ enc_rwts)
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tac01
      \\ qabbrev_tac `r = c0 + 0xFFFFFFF4w`
      \\ (if imm then
            qabbrev_tac
                 `p = add_with_carry (ms.REG (R_mode ms.CPSR.M (n2w n)), ~c',T)`
            \\ qabbrev_tac
                 `q = -1w * c' + ms.REG (R_mode ms.CPSR.M (n2w n))`
          else
            qabbrev_tac `p = add_with_carry
                               (ms.REG (R_mode ms.CPSR.M (n2w n)),
                                ~ms.REG (R_mode ms.CPSR.M (n2w n')),T)`
            \\ qabbrev_tac `q = ms.REG (R_mode ms.CPSR.M (n2w n)) +
                                -1w * ms.REG (R_mode ms.CPSR.M (n2w n'))`)
      >| (tacs false imm @ tacs true imm)
end

local
   val (_, _, _, is_SetPassCondition) = arm_op2 "SetPassCondition"
   val cnv =
      Conv.RATOR_CONV
         (Conv.RAND_CONV (SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []))
      THENC SIMP_CONV (srw_ss()) [SetPassCondition]
in
   fun SetPassCondition_CONV tm =
      if is_SetPassCondition tm
         then cnv tm
      else raise ERR "SetPassCondition_CONV" ""
   val SetPassCondition_tac =
      CONV_TAC (Conv.ONCE_DEPTH_CONV SetPassCondition_CONV)
      \\ simp_tac std_ss []
end

val decode_tac0 =
   simp ([lem4, lem5, lem8, decode_imm8_thm1, decode_imm8_thm3] @ enc_rwts)
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ SetPassCondition_tac
   \\ (decode_tac [true] ORELSE decode_tac [true, false])
   \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

(* -------------------------------------------------------------------------
   arm6_asm_deterministic
   arm6_backend_correct
   ------------------------------------------------------------------------- *)

val arm6_encoding = Count.apply Q.prove (
   `!i. asm_ok i arm6_config ==>
        let l = arm6_enc i in
        let n = LENGTH l in
           (!x. arm6_dec (l ++ x) = i) /\ (n MOD 4 = 0) /\ n <> 0`,
   Cases
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
         \\ decode_tac0
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ REVERSE (Cases_on `EncodeARMImmediate c`)
         >- decode_tac0
         \\ REVERSE (Cases_on `EncodeARMImmediate ~c`)
         >- (imp_res_tac decode_some_encode_neg_immediate \\ decode_tac0)
         \\ simp enc_rwts
         \\ REPEAT strip_tac
         \\ simp dec_rwts
         \\ SetPassCondition_tac
         \\ decode_tac [true]
         \\ simp dec_rwts
         \\ decode_tac [true]
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
            \\ Cases_on `r`
            \\ Cases_on `b`
            \\ decode_tac0
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ decode_tac0
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      \\ Cases_on `0w <= c`
      \\ decode_tac0
      )
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ decode_tac0
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ simp (lem8 :: enc_rwts)
      \\ REPEAT strip_tac
      \\ simp dec_rwts
      \\ SetPassCondition_tac
      \\ (decode_tac [true] ORELSE decode_tac [true, false])
      \\ simp dec_rwts
      \\ SetPassCondition_tac
      \\ decode_tac [false, true]
      \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) [arm6_cmp_dec_def]
      \\ rw []
      \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac0
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac0
      )
      (*--------------
          Loc
        --------------*)
   \\ print_tac "Loc"
   \\ lrw ([Q.ISPEC `LENGTH:'a list -> num` COND_RAND,
            (SIMP_RULE std_ss [] o Q.ISPEC `\x. x MOD 4`) COND_RAND] @ enc_rwts)
   \\ BasicProvers.CASE_TAC
   \\ simp dec_rwts
   \\ SetPassCondition_tac
   \\ (decode_tac [true] ORELSE decode_tac [true, false])
   \\ simp [lem18, lem19]
   \\ simp_tac (srw_ss()++boolSimps.LET_ss++wordsLib.WORD_EXTRACT_ss) dec_rwts
   \\ TRY (decode_tac [true] ORELSE decode_tac [true, false])
   \\ blastLib.FULL_BBLAST_TAC
   )

val arm6_asm_deterministic = Q.store_thm("arm6_asm_deterministic",
   `asm_deterministic arm6_enc arm6_config`,
   metis_tac [asmPropsTheory.decoder_asm_deterministic, arm6_encoding]
   )

val arm6_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [arm6_config_def] arm6_asm_deterministic

val enc_ok_rwts =
   SIMP_RULE (bool_ss++boolSimps.LET_ss) [arm6_config_def] arm6_encoding ::
   enc_ok_rwts

val tac1 =
   next_tac `0`
   \\ lfs enc_rwts
   \\ next_state_tac01
   \\ state_tac [alignmentTheory.align_aligned,
                 decode_imm8_thm2, decode_imm8_thm5]

val tac2 =
   next_tac `1`
   \\ lfs enc_rwts
   \\ asmLib.split_bytes_in_memory_tac 4
   \\ next_state_tac01
   \\ next_state_tac1 hd [true]
   \\ fs []
   \\ blast_byte_eq_tac
   \\ pop_assum SUBST1_TAC
   \\ state_tac1 [alignmentTheory.align_aligned]
   \\ asm_simp_tac std_ss [decode_imm8_thm4, decode_imm8_thm6]
   \\ reg_tac
   \\ rw [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric,
          updateTheory.APPLY_UPDATE_ID, arm_stepTheory.R_mode_11, lem1]

val arm6_backend_correct = Count.apply Q.store_thm ("arm6_backend_correct",
   `backend_correct arm6_target`,
   simp [asmPropsTheory.backend_correct_def, arm6_target_def]
   \\ REVERSE (REPEAT conj_tac)
   >| [
      rw [asmSemTheory.asm_step_def] \\ Cases_on `i`,
      srw_tac [] [arm6_asm_state_def, arm6_config_def, set_sepTheory.fun2set_eq]
      \\  `i < 15` by decide_tac
      \\ simp [],
      srw_tac [] [arm6_proj_def, arm6_asm_state_def, arm6_ok_def]
      \\ rfs [reg_mode_eq],
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
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
         \\ lfs enc_rwts
         \\ next_state_tac01
         \\ state_tac []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ REVERSE (Cases_on `EncodeARMImmediate c`)
         >- (
            next_tac `0`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            \\ simp [decode_some_encode_immediate]
            )
         \\ REVERSE (Cases_on `EncodeARMImmediate ~c`)
         >- (
            next_tac `0`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            \\ imp_res_tac decode_some_encode_neg_immediate
            \\ simp []
            )
         \\ next_tac `1`
         \\ lfs enc_rwts
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac01
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ fs []
         \\ next_state_tac1 (hd o tl) [true]
         \\ state_tac1 []
         \\ blastLib.BBLAST_TAC
         )
      >- (
         (*--------------
             Arith
           --------------*)
         next_tac `0`
         \\ Cases_on `a`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            \\ Cases_on `b`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
         )
         (*--------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ next_tac `0`
         \\ Cases_on `a`
         \\ Cases_on `m`
         \\ Cases_on `0w <= c`
         \\ lfs ([lem4, lem5] @ enc_rwts)
         >| [
             (* LDR + *)
             load_store_tac {neg = false, store = false},
             (* LDR - *)
             load_store_tac {neg = true, store = false},
             (* LDRB + *)
             load_store_tac {neg = false, store = false},
             (* LDRB - *)
             load_store_tac {neg = true, store = false},
             (* STR + *)
             load_store_tac {neg = false, store = true},
             (* STR - *)
             load_store_tac {neg = true, store = true},
             (* STRB + *)
             load_store_tac {neg = false, store = true},
             (* STRB - *)
             load_store_tac {neg = true, store = true}
         ]
      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac `0`
      \\ lfs (lem8 :: enc_rwts)
      \\ qabbrev_tac `a = (25 >< 2) (c + 0xFFFFFFF8w): word24`
      \\ next_state_tac01
      \\ state_tac []
      \\ imp_res_tac lem15
      \\ simp [lem7, alignmentTheory.aligned_add_sub, aligned_add]
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ next_tac `1`
      \\ Cases_on `r`
      >- cmp_tac false
      \\ cmp_tac true
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ next_tac `0`
      \\ lfs (lem8 :: enc_rwts)
      \\ qabbrev_tac `a = (25 >< 2) (c + 0xFFFFFFF8w): word24`
      \\ next_state_tac01
      \\ state_tac []
      \\ imp_res_tac lem9
      \\ imp_res_tac lem10
      \\ simp [alignmentTheory.aligned_numeric, alignmentTheory.aligned_add_sub,
               aligned_add]
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac `0`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ imp_res_tac lem11
      \\ imp_res_tac lem12
      \\ state_tac []
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ Cases_on `8w <= c`
      >| [
           Cases_on `c + 0xFFFFFFF8w <+ 256w`,
           Cases_on `-1w * c + 0x8w <+ 256w`
      ]
      >| [tac1, tac2, tac1, tac2]
      )
   >- (
      (*--------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ lfs (lem8 :: enc_rwts)
      )
   >- (
      (*--------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `ri`
      \\ Cases_on `cmp`
      \\ lfs (lem8 :: enc_rwts)
      )
   >- (
      (*--------------
          Call enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lfs (lem8 :: enc_rwts)
      )
   >- (
      (*--------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lrw enc_rwts
      \\ rw []
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*--------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [arm6_asm_deterministic_config]
   )

(*

val x64_enc_deterministic = proofManagerLib.top_thm ()

val x64_enc_deterministic = Theory.new_axiom ("x64_enc_deterministic",
   ``enc_deterministic x64_enc x64_config``)

   proofManagerLib.r
   set_trace "Goalstack.howmany_printed_subgoals" 60

*)

val () = export_theory ()
