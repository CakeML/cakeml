(*
  Lemmas used by arm8_targetProofLib. They are proved here, in a theory,
  because proofs can no longer be run while a library is being loaded.
*)
Theory arm8_targetProofLemmas
Ancestors
  arm8_target
Libs
  asmLib arm8_stepLib

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = wordsLib.guess_lengths ()

Theorem lem1 = asmLib.v2w_BIT_n2w 5

Theorem lem5 = asmLib.v2w_BIT_n2w 6

Theorem word_log2_7:
  !s: word6. word_log2 (((1w: word1) @@ s) : word7) = 6w
Proof
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
QED

Theorem DecodeBitMasks_SOME:
  !r s. ?wmask: word64 tmask.
  DecodeBitMasks (1w, s, r, F) = SOME (wmask,tmask)
Proof
  simp [arm8Theory.DecodeBitMasks_def, arm8Theory.HighestSetBit_def]
  \\ rw [word_log2_7]
  >- blastLib.FULL_BBLAST_TAC
  \\ EVAL_TAC
QED

Theorem ShiftValue0:
  !x. ShiftValue (x, DecodeShift 0w, 0) = x
Proof
  rw [arm8Theory.ShiftValue_def, arm8Theory.DecodeShift_def,
  arm8Theory.num2ShiftType_thm]
QED

Theorem valid_immediate_thm:
  !b c.
  valid_immediate b c =
  if (b = INL Add) \/ (b = INL Sub) \/
     (b = INR Less) \/ (b = INR Lower) \/ (b = INR Equal) \/
     (b = INR NotLess) \/ (b = INR NotLower) \/ (b = INR NotEqual) then
     ((0xFFFFFFFFFFFFF000w && c) = 0w) \/
     ((0xFFFFFFFFFFFFF000w && c) <> 0w) /\
     ((0xFFFFFFFFFF000FFFw && c) = 0w)
  else
     ?N imms immr. EncodeBitMask c = SOME (N, imms, immr)
Proof
  Cases
  >| [ Cases_on `x`, Cases_on `y` ]
  \\ rw [valid_immediate_def]
  \\ TRY blastLib.BBLAST_PROVE_TAC
  \\ Cases_on `EncodeBitMask c`
  \\ simp []
  \\ METIS_TAC [pairTheory.ABS_PAIR_THM]
QED

Theorem lem8:
  !w: word64. aligned 2 w ==> ((1 >< 0) w = 0w: word2)
Proof
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
QED

Theorem lem13:
  !c: word64.
  (c = w2w ((11 >< 0) (c >>> 3) : word12) << 3) ==>
  (w2w (v2w [c ' 14; c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8;
             c ' 7; c ' 6; c ' 5; c ' 4; c ' 3]: word12) << 3 = c)
Proof
  blastLib.BBLAST_TAC
QED

Theorem lem14:
  !s state c: word64 n.
  target_state_rel arm8_target s state /\ n <> 18 /\ n <> 26 /\ n <> 31 /\
  n < 32 /\ aligned 3 (c + s.regs n) ==> aligned 3 (c + state.REG (n2w n))
Proof
  rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
QED

Theorem lem14b:
  !s state c: word64 n.
  target_state_rel arm8_target s state /\ n <> 18 /\ n <> 31 /\ n <> 26 /\ n < 32 /\
  aligned 2 (c + s.regs n) ==> aligned 2 (c + state.REG (n2w n))
Proof
  rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
QED

Theorem lem14c:
  !s state c: word64 n.
  target_state_rel arm8_target s state /\ n <> 18 /\ n <> 31 /\ n <> 26 /\ n < 32 /\
  aligned 1 (c + s.regs n) ==> aligned 1 (c + state.REG (n2w n))
Proof
  rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def]
QED

Theorem lem17:
  !c: word64.
  (c = w2w ((11 >< 0) c : word12)) ==>
  (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5; c ' 4;
             c ' 3; c ' 2; c ' 1; c ' 0]: word12) = c)
Proof
  blastLib.BBLAST_TAC
QED

Theorem lem18:
  !c: word64.
  (c = w2w ((11 >< 0) (c >>> 2) : word12) << 2) ==>
  (w2w (v2w [c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
             c ' 6; c ' 5; c ' 4; c ' 3; c ' 2]: word12) << 2 = c)
Proof
  blastLib.BBLAST_TAC
QED

Theorem lem18b:
  !c: word64.
  (c = w2w ((11 >< 0) (c >>> 1) : word12) << 1) ==>
  (w2w (v2w [c ' 12; c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
             c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1]: word12) << 1 = c)
Proof
  blastLib.BBLAST_TAC
QED

Theorem lem27:
  !c: word64 q r.
  (arm8_enc_mov_imm c = SOME (q,r)) ==>
  (c =
   bit_field_insert
    (w2n (((v2w [r ' 1; r ' 0]: word2) @@ (0w: word4)) : word6) + 15)
    (w2n (((v2w [r ' 1; r ' 0]: word2) @@ (0w: word4)) : word6))
      (v2w [q ' 15; q ' 14; q ' 13; q ' 12; q ' 11; q ' 10; q ' 9; q ' 8;
            q ' 7; q ' 6; q ' 5; q ' 4; q ' 3; q ' 2; q ' 1; q ' 0] : word16)
    0w)
Proof
  lrw [arm8_enc_mov_imm_def]
  \\ simp []
  \\ CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV)
  \\ simp []
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem lem29:
  !i. i < 31 ==> (i MOD 32 <> 31)
Proof
  rw []
QED

Theorem bytes_in_memory_thm:
  !s state a b c d.
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
  state.PC IN s.mem_domain
Proof
  rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def,
      arm8_ok_def, miscTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
  \\ rev_full_simp_tac (srw_ss()) []
QED

Theorem bytes_in_memory_thm2:
  !w s state a b c d.
  target_state_rel arm8_target s state /\
  bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
  (state.MEM (state.PC + w + 3w) = d) /\
  (state.MEM (state.PC + w + 2w) = c) /\
  (state.MEM (state.PC + w + 1w) = b) /\
  (state.MEM (state.PC + w) = a) /\
  state.PC + w + 3w IN s.mem_domain /\
  state.PC + w + 2w IN s.mem_domain /\
  state.PC + w + 1w IN s.mem_domain /\
  state.PC + w IN s.mem_domain
Proof
  rw [asmPropsTheory.target_state_rel_def, arm8_target_def, arm8_config_def,
      arm8_ok_def, miscTheory.bytes_in_memory_def, set_sepTheory.fun2set_eq]
  \\ rev_full_simp_tac (srw_ss()) []
QED

Theorem lem28:
  (~c = n) = (c = ~n:'a word)
Proof
  metis_tac [wordsTheory.WORD_NOT_NOT]
QED
