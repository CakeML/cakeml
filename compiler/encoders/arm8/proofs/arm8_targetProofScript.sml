(*
  Prove `encoder_correct` for ARMv8
*)
Theory arm8_targetProof
Ancestors
  arm8_target
Libs
  asmLib arm8_stepLib arm8_targetProofLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val () = wordsLib.guess_lengths ()

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

val ev = EVAL THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV

val replicate1 = GEN_ALL (EVAL ``replicate v 1``)

fun and_max ty =
   wordsTheory.WORD_AND_CLAUSES
   |> Thm.INST_TYPE [Type.alpha |-> ty]
   |> REWRITE_RULE [EVAL (wordsSyntax.mk_word_T ty)]

Theorem lsl_lem1[local]:
  !w:word6.
      (if v2n (field 5 0 (w2v w)) + 1 < 64 then
          64
       else v2n (field 5 0 (w2v w)) + 1) = 64
Proof
  lrw []
   \\ Cases_on `v2n (field 5 0 (w2v w)) = 63`
   >- simp []
   \\ qspec_then `field 5 0 (w2v w)` assume_tac bitstringTheory.v2n_lt
   \\ fs []
   \\ decide_tac
QED

Theorem lsl_lem2[local]:
  !w:word6. (if w2n w + 1 < 64 then 64 else w2n w + 1) = 64
Proof
  lrw []
   \\ Cases_on `w2n w = 63`
   >- simp []
   \\ Q.ISPEC_THEN `w` assume_tac wordsTheory.w2n_lt
   \\ fs []
   \\ decide_tac
QED

val lsl_lem3 = ev
   ``v2w (PAD_LEFT F 64
            (PAD_LEFT T (v2n (field 5 0 (w2v (63w: word6))) + 1) [])): word64``

Theorem lsl_lem4[local]:
  !n. n < 64 ==> ((64 - n + 63) MOD 64 = 63 - n)
Proof
  lrw []
   \\ asm_simp_tac bool_ss
         [arithmeticTheory.ADD_MODULUS_RIGHT, DECIDE ``0n < 64``,
          DECIDE ``n < 64n ==> (127 - n = 64 + (63 - n)) /\ 63 - n < 64``,
          arithmeticTheory.LESS_MOD]
QED

Theorem lsl_lem5[local]:
  !n. n < 64 ==>
        (v2w (PAD_LEFT F 64 (PAD_LEFT T n [])) : word64 = (FCP i. i < n))
Proof
  srw_tac [fcpLib.FCP_ss] []
   \\ rewrite_tac [bitstringTheory.word_index_v2w]
   \\ simp [bitstringTheory.testbit, listTheory.PAD_LEFT]
   \\ Cases_on `63 - i < 64 - n`
   \\ simp [rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

val lsl_lem6 = DECIDE ``n < 64n ==> (63 - n + 1 = 64 - n)``

Theorem lsl:
   !r q n x wmask: word64 tmask.
       n < 64n /\
       Abbrev (r = n2w ((64 - n) MOD 64)) /\
       Abbrev (q = r + 63w) /\
       (DecodeBitMasks (1w, q, r, F) = SOME (wmask, tmask)) ==>
       (((tmask && wmask) && x #>> (w2n r)) = x << n)
Proof
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
   \\ simp [] \\ EVAL_TAC \\ wordsLib.WORD_DECIDE_TAC
QED

Theorem lsr_lem1[local]:
  !n. v2n (field 5 0 (w2v (n2w n : word6))) = n MOD 64
Proof
  REPEAT strip_tac
   \\ strip_assume_tac
         (Q.ISPEC `n2w n: word6` bitstringTheory.ranged_bitstring_nchotomy)
   \\ simp [bitstringTheory.w2v_v2w, bitstringTheory.word_extract_v2w,
            bitstringTheory.word_bits_v2w, bitstringTheory.w2w_v2w]
   \\ rfs [markerTheory.Abbrev_def, bitstringTheory.field_id_imp,
           GSYM bitstringTheory.n2w_v2n, arithmeticTheory.LESS_MOD]
   \\ metis_tac [bitstringTheory.v2n_lt, EVAL ``2n ** 6n``]
QED

Theorem lsr_lem2[local]:
  !n. v2w (rotate (PAD_LEFT F 64 (PAD_LEFT T 64 [])) n) = UINT_MAXw: word64
Proof
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
QED

Theorem lsr:
   !n x wmask: word64 tmask.
       n < 64n /\
       (DecodeBitMasks (1w, 63w, n2w n, F) = SOME (wmask, tmask)) ==>
       (((tmask && wmask) && x #>> n) = x >>> n)
Proof
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
QED

Theorem asr =
  wordsTheory.word_asr_n2w
  |> Thm.INST_TYPE [Type.alpha |-> ``:64``]
  |> REWRITE_RULE
       [blastLib.BBLAST_PROVE ``word_msb (w:word64) = word_bit 63 w``]

Theorem asr_lem1[local]:
  !m. m < 64 ==> (MIN m 64 = m)
Proof
  rw [arithmeticTheory.MIN_DEF]
QED

Theorem asr2:
   !n x wmask: word64 tmask.
       n < 64n /\
       (DecodeBitMasks (1w, 63w, n2w n, F) = SOME (wmask, tmask)) ==>
       (n2w (0x10000000000000000 - 2 ** (64 - MIN n 64)) =
        (0xFFFFFFFFFFFFFFFFw && ~tmask))
Proof
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
QED

Theorem ror:
  !w : word64 n.
     n < 64 ==> (v2w (shiftr (w2v w ++ w2v w) n): word64 = w #>> n)
Proof
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
QED

Theorem mul_long:
  !a : word64 b : word64.
    n2w ((w2n a * w2n b) DIV 18446744073709551616) =
    (127 >< 64) (w2w a * w2w b : word128) : word64
Proof
  Cases
  \\ Cases
  \\ fs [wordsTheory.w2w_n2w, wordsTheory.word_mul_n2w,
         wordsTheory.word_extract_n2w, bitTheory.BITS_THM]
QED

(* some custom tactics ----------------------------------------------------- *)

val fs = full_simp_tac (srw_ss())
val rfs = rev_full_simp_tac (srw_ss())


(* -------------------------------------------------------------------------
   arm8 target_ok
   ------------------------------------------------------------------------- *)

Theorem length_arm8_encode[local]:
  !i. LENGTH (arm8_encode i) = 4
Proof
  Cases
  \\ rw [arm8_encode_def]
  \\ CASE_TAC
  \\ simp []
QED

Theorem length_arm8_enc[local]:
  !l. LENGTH (LIST_BIND l arm8_encode) = 4 * LENGTH l
Proof
  Induct \\ rw [length_arm8_encode]
QED

Theorem arm8_encode_not_nil[local]:
  !i. arm8_encode i <> []
Proof
  simp_tac std_ss [GSYM listTheory.LENGTH_NIL, length_arm8_encode]
QED

Theorem arm8_encoding[local]:
  !i. let l = arm8_enc i in (LENGTH l MOD 4 = 0) /\ l <> []
Proof
  strip_tac
  \\ asmLib.asm_cases_tac `i`
  \\ simp [arm8_enc_def, length_arm8_enc, length_arm8_encode,
           arm8_encode_fail_def, arm8_ast, arm8_load_store_ast_def,
           arm8_load_store_ast16_def,arm8_load_store_ast32_def]
  \\ REPEAT CASE_TAC
  \\ rw [length_arm8_encode, arm8_encode_not_nil]
QED

Theorem arm8_encoding = arm8_encoding |>
    SIMP_RULE (srw_ss()++boolSimps.LET_ss)
       [arm8_enc_def, listTheory.LIST_BIND_def]

Theorem arm8_target_ok[local]:
  target_ok arm8_target
Proof
  rw ([asmPropsTheory.target_ok_def, asmPropsTheory.target_state_rel_def,
        arm8_proj_def, arm8_target_def, arm8_config, arm8_ok_def,
        set_sepTheory.fun2set_eq, arm8_encoding] @ enc_ok_rwts)
   >| [all_tac, Cases_on `ri` \\ Cases_on `cmp`, all_tac, all_tac]
   \\ lfs enc_rwts
   \\ rw[]
   \\ lfs enc_rwts
   \\ blastLib.FULL_BBLAST_TAC
QED

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
               Cases_on `c = sw2sw ((8 >< 0) c)`
               >| [next_tac `0`
                   \\ Cases_on
                      `¬word_msb c ∧ (c = w2w ((11 >< 0) (c ⋙ 1)) ≪ 1)`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on ‘c = w2w ((11 >< 0) (c ⋙ 1)) ≪ 1’
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
               ,
               Cases_on `c = sw2sw ((8 >< 0) c)`
               >| [next_tac `0`
                   \\ Cases_on `¬word_msb c ∧ c = w2w ((11 >< 0) (c ⋙ 2)) ≪ 2`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on ‘c = w2w ((11 >< 0) (c ⋙ 2)) ≪ 2’
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
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
               ,
               Cases_on `c = sw2sw ((8 >< 0) c)`
               >| [next_tac `0`
                   \\ Cases_on
                      `¬word_msb c ∧ (c = w2w ((11 >< 0) (c ⋙ 1)) ≪ 1)`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on ‘c = w2w ((11 >< 0) (c ⋙ 1)) ≪ 1’
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
               ,
               Cases_on `c = sw2sw ((8 >< 0) c)`
               >| [next_tac `0`
                   \\ Cases_on `¬word_msb c ∧ c = w2w ((11 >< 0) (c ⋙ 2)) ≪ 2`,
                   Cases_on `word_msb c`
                   >| [next_tac `1`,
                       Cases_on ‘c = w2w ((11 >< 0) (c ⋙ 2)) ≪ 2’
                       >| [next_tac `0`,
                           next_tac `1`
                       ]
                   ]
               ]
            ]
            \\ enc_rwts_tac
            \\ rfs []
            \\ fs [lem7, lem7b, lem31, lem35]
            \\ TRY (`aligned 3 (c + ms.REG (n2w n'))`
                    by (imp_res_tac lem14 \\ NO_TAC))
            \\ TRY (`aligned 2 (c + ms.REG (n2w n'))`
                    by (imp_res_tac lem14b \\ NO_TAC))
            \\ TRY (`aligned 1 (c + ms.REG (n2w n'))`
                    by (imp_res_tac lem14c \\ NO_TAC))
            \\ split_bytes_in_memory_tac 4
            \\ next_state_tac01
            \\ TRY (asmLib.split_bytes_in_memory_tac 4
                    \\ next_state_tacN (`4w`, 1) filter_reg_31)
            \\ state_tac
                  [arm8_stepTheory.mem_dword_def, arm8_stepTheory.mem_word_def,
                   arm8_stepTheory.mem_half_def,
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

