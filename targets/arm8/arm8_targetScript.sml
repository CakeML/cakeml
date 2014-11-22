open HolKernel Parse boolLib bossLib
open lcsymtacs sptreeLib asmTheory asmLib arm8_stepLib arm8_encodeTheory;

val () = new_theory "arm8_target"

val () = wordsLib.guess_lengths ()

(* --- Configuration for ARMv6 --- *)

val eval = rhs o concl o EVAL
val off_min = eval ``sw2sw (INT_MINw: word9) : word64``
val off_max = eval ``sw2sw (INT_MAXw: word9) : word64``
val loc_min = eval ``sw2sw (INT_MINw: word20) : word64``
val loc_max = eval ``sw2sw (INT_MAXw: word20) : word64``
val cjump_min = eval ``sw2sw (INT_MINw: 21 word) + 4w : word64``
val cjump_max = eval ``sw2sw (INT_MAXw: 21 word) + 4w : word64``
val jump_min = eval ``sw2sw (INT_MINw: word28) : word64``
val jump_max = eval ``sw2sw (INT_MAXw: word28) : word64``

val valid_immediate_def = Define`
   valid_immediate (c:binop+cmp) (i: word64) =
   if c IN {INL Add; INL Sub; INR Less; INR Lower; INR Equal} then
      (~0xFFFw && i = 0w) \/ (~0xFFF000w && i = 0w)
   else
      IS_SOME (EncodeBitMask (Imm64 i))`

val arm8_config_def = Define`
   arm8_config =
   <| ISA_name := "ARMv8"
    ; reg_count := 32
    ; avoid_regs := [31]
    ; link_reg := SOME 30
    ; has_delay_slot := F
    ; has_icache := F
    ; has_mem_32 := T
    ; two_reg_arith := F
    ; valid_imm := valid_immediate
    ; addr_offset_min := ^off_min
    ; addr_offset_max := ^off_max
    ; jump_offset_min := ^jump_min
    ; jump_offset_max := ^jump_max
    ; cjump_offset_min := ^cjump_min
    ; cjump_offset_max := ^cjump_max
    ; loc_offset_min := ^loc_min
    ; loc_offset_max := ^loc_max
    ; code_alignment := 4
    |>`

(* --- The next-state function --- *)

val arm8_next_def = Define `arm8_next = THE o NextStateARM8`

(* --- Relate ASM and ARMv6 states --- *)

val arm8_asm_state_def = Define`
   arm8_asm_state a s =
   (s.PSTATE.EL = 0w) /\
   ~s.SCTLR_EL1.E0E  /\ ~s.SCTLR_EL1.SA0 /\
   ~s.TCR_EL1.TBI1 /\ ~s.TCR_EL1.TBI0 /\
   (s.exception = NoException) /\
   (!i. i < 31 ==> (a.regs i = s.REG (n2w i))) /\
   (a.mem_domain = univ(:word64)) /\ (a.mem = s.MEM) /\
   (a.pc = s.PC) /\ Aligned (s.PC, 4)`

(* --- Encode ASM instructions to ARM bytes. --- *)

val arm8_encode_def = Define`
   arm8_encode i =
   case InstructionEncode i of
      ARM8 w => [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w]
    | _ => [] : word8 list`

val bop_enc_def = Define`
   (bop_enc And = LogicalOp_AND) /\
   (bop_enc Or  = LogicalOp_ORR) /\
   (bop_enc Xor = LogicalOp_EOR)`

val bop_dec_def = Define`
   (bop_dec LogicalOp_AND = And) /\
   (bop_dec LogicalOp_ORR = Or) /\
   (bop_dec LogicalOp_EOR = Xor)`

val cmp_cond_def = Define`
   (cmp_cond Less  = 0b1011w:word4) /\
   (cmp_cond Lower = 0b0011w) /\
   (cmp_cond Equal = 0w) /\
   (cmp_cond Test  = 0w)`

val arm8_enc_mov_imm_def = Define`
   arm8_enc_mov_imm (i: word64) =
   if i && 0xFFFFFFFFFFFF0000w = 0w then
      SOME ((15 >< 0) i, 0w: word2)
   else if i && 0xFFFFFFFF0000FFFFw = 0w then
      SOME ((31 >< 16) i, 1w)
   else if i && 0xFFFF0000FFFFFFFFw = 0w then
      SOME ((47 >< 32) i, 2w)
   else if i && 0x0000FFFFFFFFFFFFw = 0w then
      SOME ((63 >< 48) i, 3w)
   else
      NONE`

val arm8_enc_def = Define`
   (arm8_enc (Inst Skip) = arm8_encode NoOperation) /\
   (arm8_enc (Inst (Const r i)) =
      case arm8_enc_mov_imm i of
         SOME (imm16, hw) =>
            arm8_encode
               (Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, n2w r)))
       | NONE =>
          (case arm8_enc_mov_imm (~i) of
               SOME (imm16, hw) =>
                 arm8_encode
                    (Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, n2w r)))
            | NONE =>
                if IS_SOME (EncodeBitMask (Imm64 i)) then
                  arm8_encode
                     (Data (LogicalImmediate@64
                              (1w, LogicalOp_ORR, F, i, 0x1Fw, n2w r)))
                else
                  arm8_encode
                     (Data (MoveWide@64
                              (1w, MoveWideOp_K, 0w, (15 >< 0) i, n2w r))) ++
                  arm8_encode
                     (Data (MoveWide@64
                              (1w, MoveWideOp_K, 1w, (31 >< 16) i, n2w r))) ++
                  arm8_encode
                     (Data (MoveWide@64
                              (1w, MoveWideOp_K, 2w, (47 >< 32) i, n2w r))) ++
                  arm8_encode
                     (Data (MoveWide@64
                              (1w, MoveWideOp_K, 3w, (63 >< 48) i, n2w r))))) /\
   (arm8_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      arm8_encode (Data
        (case bop of
            Add => AddSubShiftedRegister@64
                     (1w, F, F, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1)
          | Sub => AddSubShiftedRegister@64
                     (1w, T, F, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1)
          | x => LogicalShiftedRegister@64
                     (1w, bop_enc x, F, F, ShiftType_LSL, 0,
                      n2w r3, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
      arm8_encode (Data
        (case bop of
            Add => AddSubImmediate@64 (1w, F, F, i, n2w r2, n2w r1)
          | Sub => AddSubImmediate@64 (1w, T, F, i, n2w r2, n2w r1)
          | x => LogicalImmediate@64 (1w, bop_enc x, F, i, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Arith (Shift sh r1 r2 n))) =
      case sh of
         Lsl => (let i = n2w n : word6 in
                 let r = -i and s = 63w - i in
                    case DecodeBitMasks (1w, s, r, F) of
                       SOME (wmask, tmask) =>
                         arm8_encode (Data
                            (BitfieldMove@64
                               (1w, T, F, wmask, tmask, w2n r, w2n s, n2w r2,
                                n2w r1)))
                     | NONE => [])
       | x => (case DecodeBitMasks (1w, 63w, n2w n, F) of
                  SOME (wmask, tmask) =>
                     arm8_encode (Data
                       (BitfieldMove@64
                         (1w, T, x = Asr, wmask, tmask, n, 63, n2w r2, n2w r1)))
                | NONE => [])) /\
   (arm8_enc (Inst (Mem Load r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@64
              (3w, F, MemOp_LOAD, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Mem Load32 r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@32
              (2w, T, MemOp_LOAD, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@8
              (0w, F, MemOp_LOAD, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Mem Store r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@64
              (3w, F, MemOp_STORE, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Mem Store32 r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@32
              (2w, T, MemOp_STORE, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
      arm8_encode
        (LoadStore
           (LoadStoreImmediate@8
              (0w, F, MemOp_STORE, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   (arm8_enc (Jump _ (SOME _)) = []) /\
   (arm8_enc (Jump a NONE) =
      arm8_encode (Branch (BranchImmediate (a, BranchType_JMP)))) /\
   (arm8_enc (JumpCmp _ _ _ _ (SOME _)) = []) /\
   (arm8_enc (JumpCmp cmp r1 (Reg r2) a NONE) =
      arm8_encode
         (Data (if cmp = Test then
                   LogicalShiftedRegister@64
                      (1w, LogicalOp_AND, F, T, ShiftType_LSL, 0,
                       n2w r2, n2w r1, 0x1Fw)
                else
                   AddSubShiftedRegister@64
                      (1w, T, T, ShiftType_LSL, n2w r2, 0w, n2w r1, 0x1Fw))) ++
      arm8_encode (Branch (BranchConditional (a - 4w, cmp_cond cmp)))) /\
   (arm8_enc (JumpCmp cmp r (Imm i) a NONE) =
      arm8_encode
         (Data (if cmp = Test then
                   LogicalImmediate@64
                      (1w, LogicalOp_AND, T, i, n2w r, 0x1Fw)
                else
                   AddSubImmediate@64 (1w, T, T, i, n2w r, 0x1Fw))) ++
      arm8_encode (Branch (BranchConditional (a - 4w, cmp_cond cmp)))) /\
   (arm8_enc (Call a) =
      arm8_encode (Branch (BranchImmediate (a, BranchType_CALL)))) /\
   (arm8_enc (JumpReg r) =
      arm8_encode (Branch (BranchRegister (n2w r, BranchType_JMP)))) /\
   (arm8_enc (Loc r i) = arm8_encode (Address (F, i, n2w r))) /\
   (arm8_enc Cache = [])`

val arm8_enc = REWRITE_RULE [bop_enc_def, asmTheory.shift_distinct] arm8_enc_def

val cond_cmp_def = Define`
   (cond_cmp (0b1011w:word4) = Less) /\
   (cond_cmp 0b0011w = Lower) /\
   (cond_cmp 0w = Equal)`;

val fetch_word_def = Define`
   fetch_word (b0 :: b1 :: b2 :: b3 :: (rest: word8 list)) =
     ((b3 @@ b2 @@ b1 @@ b0) : word32, rest)`

val decode_word_def = Define`
   decode_word l = let (w, rest) = fetch_word l in (Decode w, rest)`

val arm8_dec_aux_def = Define`
  arm8_dec_aux (ast, rest) =
  case ast of
     Hint SystemHintOp_NOP => Inst Skip
   | Data (MoveWide@64 (1w, MoveWideOp_K, 0w, imm16a, r)) =>
       (case decode_word rest of
           (Data (MoveWide@64 (1w, MoveWideOp_K, 1w, imm16b, r)), rest2) =>
             (case decode_word rest2 of
                 (Data (MoveWide@64 (1w, MoveWideOp_K, 2w, imm16c, r)),
                  rest3) =>
                   (case decode_word rest3 of
                       (Data (MoveWide@64 (1w, MoveWideOp_K, 3w, imm16d, r)),
                        rest4) =>
                          Inst (Const (w2n r)
                                  (imm16d @@ imm16c @@ imm16b @@ imm16a))
                     | _ => ARB)
               | _ => ARB)
         | _ => ARB)
   | Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, r)) =>
        Inst (Const (w2n r) (w2w imm16 << (w2n hw * 16)))
   | Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, r)) =>
        Inst (Const (w2n r) (~(w2w imm16 << (w2n hw * 16))))
   | Data (AddSubShiftedRegister@64
             (_, b, F, ShiftType_LSL, r3, 0w, r2, r1)) =>
        Inst (Arith (Binop (if b then Sub else Add)
                       (w2n r1) (w2n r2) (Reg (w2n r3))))
   | Data (LogicalShiftedRegister@64
             (_, opc, F, F, ShiftType_LSL, 0, r3, r2, r1)) =>
        Inst (Arith (Binop (bop_dec opc) (w2n r1) (w2n r2) (Reg (w2n r3))))
   | Data (AddSubImmediate@64 (_, b, F, i, r2, r1)) =>
        Inst (Arith (Binop (if b then Sub else Add) (w2n r1) (w2n r2) (Imm i)))
   | Data (LogicalImmediate@64 (_, LogicalOp_ORR, F, i, 0x1Fw, r)) =>
        Inst (Const (w2n r) i)
   | Data (LogicalImmediate@64 (_, opc, F, i, r2, r1)) =>
        Inst (Arith (Binop (bop_dec opc) (w2n r1) (w2n r2) (Imm i)))
   | Data (BitfieldMove@64 (_, T, b, _, _, r, s, r2, r1)) =>
        if (s = 63) /\ r <> 0 then
           Inst (Arith (Shift (if b then Asr else Lsr) (w2n r1) (w2n r2) r))
        else
           Inst (Arith (Shift Lsl (w2n r1) (w2n r2) (63 - s)))
   | Data (AddSubImmediate@64 (1w, T, T, i, r, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, c)) =>
              JumpCmp (cond_cmp c) (w2n r) (Imm i) (a + 4w) NONE
         | _ => ARB)
   | Data (LogicalImmediate@64 (1w, LogicalOp_AND, T, i, r, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, 0w)) =>
              JumpCmp Test (w2n r) (Imm i) (a + 4w) NONE
         | _ => ARB)
   | Data (AddSubShiftedRegister@64
             (1w, T, T, ShiftType_LSL, r2, 0w, r1, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, c)) =>
              JumpCmp (cond_cmp c) (w2n r1) (Reg (w2n r2)) (a + 4w) NONE
         | _ => ARB)
   | Data (LogicalShiftedRegister@64
              (1w, LogicalOp_AND, F, T, ShiftType_LSL, 0, r2, r1, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, 0w)) =>
              JumpCmp Test (w2n r1) (Reg (w2n r2)) (a + 4w) NONE
         | _ => ARB)
   | LoadStore
        (LoadStoreImmediate@64
           (3w, _, memop, AccType_NORMAL, F, _, _, F, F, _, a, r2, r1)) =>
        Inst (Mem (if memop = MemOp_LOAD then Load else Store) (w2n r1)
                  (Addr (w2n r2) a))
   | LoadStore
        (LoadStoreImmediate@32
           (2w, T, memop, AccType_NORMAL, F, _, _, F, F, _, a, r2, r1)) =>
        Inst (Mem (if memop = MemOp_LOAD then Load32 else Store32) (w2n r1)
                  (Addr (w2n r2) a))
   | LoadStore
        (LoadStoreImmediate@8
           (0w, _, memop, AccType_NORMAL, F, _, _, F, F, _, a, r2, r1)) =>
        Inst (Mem (if memop = MemOp_LOAD then Load8 else Store8) (w2n r1)
                  (Addr (w2n r2) a))
   | Branch (BranchImmediate (a, BranchType_JMP)) => Jump a NONE
   | Branch (BranchImmediate (a, BranchType_CALL)) => Call a
   | Branch (BranchRegister (r, BranchType_JMP)) => JumpReg (w2n r)
   | Address (F, i, r) => Loc (w2n r) i
   | _ => ARB`

val arm8_dec_def = Define `arm8_dec = arm8_dec_aux o decode_word`

(* ------------------------------------------------------------------------- *)

val lookup_CONV =
   RATOR_CONV (RAND_CONV wordsLib.WORD_EVAL_CONV)
   THENC RAND_CONV (fn t => if t = ``sptree_mask64`` then sptree_mask64_def
                            else sptree_mask32_def)
   THENC PURE_REWRITE_CONV [sptreeTheory.lookup_compute]

local
   val cmp = wordsLib.words_compset ()
   val () =
      ( utilsLib.add_base_datatypes cmp
      ; intReduce.add_int_compset cmp
      ; integer_wordLib.add_integer_word_compset cmp
      ; bitstringLib.add_bitstring_compset cmp
      ; utilsLib.add_theory ([], arm8Theory.inventory) cmp
      ; computeLib.add_conv
          (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV) cmp
      )
in
   val ARM8_CONV = computeLib.CBV_CONV cmp
end

fun dom_conv th = Count.apply (RAND_CONV (K th) THENC sptreeLib.domain_CONV)

val dom32 = dom_conv sptree_mask32_def ``domain sptree_mask32``
val dom64 = dom_conv sptree_mask64_def ``domain sptree_mask64``

(* some lemmas ------------------------------------------------------------- *)

val arm8_asm_state =
   REWRITE_RULE [DECIDE ``n < 31 = n < 32 /\ n <> 31``] arm8_asm_state_def

val Decode_EncodeBitMask = Count.apply Q.store_thm("Decode_EncodeBitMask",
   `(!w n s r.
        (EncodeBitMask (Imm32 w) = SOME (n, s, r)) ==>
        (?v. DecodeBitMasks (n, s, r, T) = SOME (w, v))) /\
    (!w n s r.
        (EncodeBitMask (Imm64 w) = SOME (n, s, r)) ==>
        (?v. DecodeBitMasks (n, s, r, T) = SOME (w, v)))`,
   strip_tac
   \\ Cases
   \\ rw [EncodeBitMask_def]
   >| [ `n IN domain sptree_mask32` by simp [sptreeTheory.domain_lookup],
        `n IN domain sptree_mask64` by simp [sptreeTheory.domain_lookup]
   ]
   \\ RULE_ASSUM_TAC (REWRITE_RULE [dom32, dom64, pred_setTheory.IN_INSERT])
   \\ fs []
   \\ pop_assum SUBST_ALL_TAC
   \\ RULE_ASSUM_TAC
         (CONV_RULE (TRY_CONV (LAND_CONV lookup_CONV
                               THENC REWRITE_CONV [optionTheory.SOME_11])))
   \\ pop_assum (assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ] o SYM)
   \\ asm_rewrite_tac []
   \\ CONV_TAC ARM8_CONV
   \\ simp []
   )

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

val aligned4 = Q.prove(
   `!w. (w2n (w: word32) MOD 4 = 0) = Aligned (w, 4)`,
   Cases
   \\ fs [arm8Theory.Aligned_def, arm8Theory.Align_def,
          arithmeticTheory.LESS_MOD,
          DECIDE ``a < b ==> (a - x < b:num)``,
          bitTheory.DIV_MULT_THM
          |> Q.SPEC `2`
          |> SIMP_RULE arith_ss []]
   \\ Cases_on `n < 4`
   \\ simp []
   )

val ShiftValue0 = Q.prove(
   `!x. ShiftValue (x, DecodeShift 0w, 0) = x`,
   rw [arm8Theory.ShiftValue_def, arm8Theory.DecodeShift_def,
       arm8Theory.num2ShiftType_thm, arm8Theory.LSL_def]
   )

val valid_immediate_thm = Q.prove(
   `!b c.
        valid_immediate b c =
        if (b = INL Add) \/ (b = INL Sub) \/
           (b = INR Less) \/ (b = INR Lower) \/ (b = INR Equal) then
           (0xFFFw && c = 0w) /\ (0xFFFFFFFFFF000000w && c = 0w) \/
           (0xFFFw && c) <> 0w /\ (0xFFFFFFFFFFFFF000w && c = 0w)
        else
           ?N imms immr. EncodeBitMask (Imm64 c) = SOME (N, imms, immr)`,
   Cases
   >| [ Cases_on `x`, Cases_on `y` ]
   \\ rw [valid_immediate_def]
   \\ TRY blastLib.BBLAST_PROVE_TAC
   \\ Cases_on `EncodeBitMask (Imm64 c)`
   \\ simp []
   \\ METIS_TAC [pairTheory.ABS_PAIR_THM]
   )

local
   fun bit_mod_thm n m =
      let
         val th = bitTheory.BITS_ZERO3 |> Q.SPEC n |> numLib.REDUCE_RULE
         val M = Term m
         val N = Term n
      in
         Tactical.prove (
             ``BIT ^M n = BIT ^M (n MOD 2 ** (^N + 1))``,
             simp [bitTheory.BIT_def, GSYM th, bitTheory.BITS_COMP_THM2])
         |> numLib.REDUCE_RULE
      end
   fun nq i = [QUOTE (Int.toString i ^ "n")]
   val th = GSYM wordsTheory.n2w_mod
in
   fun bit_mod_thms n =
      (th |> Thm.INST_TYPE [Type.alpha |-> fcpSyntax.mk_int_numeric_type n]
          |> CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV)) ::
      List.tabulate (n, fn j => bit_mod_thm (nq (n - 1)) (nq j))
end

val lem1 = Q.prove(
   `!n. v2w [BIT 4 n; BIT 3 n; BIT 2 n; BIT 1 n; BIT 0 n] = n2w n: word5`,
   strip_tac
   \\ once_rewrite_tac (bit_mod_thms 5)
   \\ qabbrev_tac `m = n MOD 32`
   \\ `m < 32` by simp [Abbr `m`]
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ EVAL_TAC
   )

val lem2 =
   blastLib.BBLAST_PROVE
   ``(!n: word1. v2w [n ' 0] = n) /\
     (!w: word6. v2w [w ' 5; w ' 4; w ' 3; w ' 2; w ' 1; w ' 0] = w)``

val lem3 = bitstringLib.v2w_n2w_CONV ``v2w [T] : word1``

val lem4 = Q.prove(
   `!n. n < 64 ==> (63 - w2n (n2w ((64 - n) MOD 64) + 63w: word6) = n)`,
   REPEAT strip_tac
   \\ asm_simp_tac bool_ss
          [(numLib.REDUCE_RULE o Q.SPECL [`64`, `1`, `n1`])
              wordsTheory.MOD_COMPLEMENT,
           (CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV) o
            Q.INST_TYPE [`:'a` |-> `:6`]) wordsTheory.n2w_mod]
   \\ simp [wordsTheory.word_add_n2w]
   \\ asm_simp_tac bool_ss
         [arithmeticTheory.ADD_MODULUS_RIGHT, DECIDE ``0n < 64``,
          DECIDE ``n < 64n ==> (127 - n = 64 + (63 - n)) /\ 63 - n < 64``,
          arithmeticTheory.LESS_MOD]
   \\ simp []
   )

val lem5 = Q.prove(
   `!n. v2w [BIT 5 n; BIT 4 n; BIT 3 n; BIT 2 n; BIT 1 n; BIT 0 n] =
        n2w n: word6`,
   strip_tac
   \\ once_rewrite_tac (bit_mod_thms 6)
   \\ qabbrev_tac `m = n MOD 64`
   \\ `m < 64` by simp [Abbr `m`]
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ EVAL_TAC
   )

val lem6 = bitstringLib.v2w_n2w_CONV ``v2w [T; T; T; T; T; T] : word6``

val lem7 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
        0xFFFFFFFFFFFFFF00w <= c /\ c <= 255w ==>
        (c = sw2sw ((8 >< 0) c : word9))``

val lem8 = Q.prove(
   `!w: word64. (w2n w MOD 4 = 0) = ((1 >< 0) w = 0w: word2)`,
   Cases
   \\ fs [arithmeticTheory.LESS_MOD, wordsTheory.word_extract_n2w,
          bitTheory.BITS_THM, DECIDE ``a < b ==> (a - x < b:num)``,
          bitTheory.DIV_MULT_THM
          |> Q.SPEC `2`
          |> SIMP_RULE arith_ss []]
   )

val lem9 =
   blastLib.BBLAST_PROVE
   ``!c: word64.
       0xFFFFFFFFF8000000w <= c /\ c <= 0x7FFFFFFw /\
       ((1 >< 0) c = 0w: word2) ==>
       (c = sw2sw ((((27 >< 2) c: 26 word) @@ (0w: word2)): word28))``

val lem10 =
   blastLib.BBLAST_PROVE
   ``!c: word64.
       0xFFFFFFFFFFF80000w <= c /\ c <= 0x7FFFFw /\
       ((1 >< 0) c = 0w: word2) ==>
       (c = sw2sw ((((20 >< 2) c: 19 word) @@ (0w: word2)): 21 word))``

val lem11 =
   blastLib.BBLAST_PROVE
   ``!c: word64.
       0xFFFFFFFFFFF00004w <= c /\ c <= 0x100003w /\
       ((1 >< 0) c = 0w: word2) ==>
       (c + 0xFFFFFFFFFFFFFFFCw =
        sw2sw ((((20 >< 2) (c + 0xFFFFFFFFFFFFFFFCw): 19 word) @@
                (0w: word2)): 21 word))``

val lem12 = Q.prove(
   `!c: word64 q r.
      (arm8_enc_mov_imm c = SOME (q,r)) ==>
      (w2w
        (v2w [q ' 15; q ' 14; q ' 13; q ' 12; q ' 11; q ' 10; q ' 9; q ' 8;
              q ' 7; q ' 6; q ' 5; q ' 4; q ' 3; q ' 2; q ' 1; q ' 0] : word16)
        << (16 * w2n (v2w [r ' 1; r ' 0]: word2)) = c)`,
   rw [arm8_enc_mov_imm_def]
   \\ simp []
   \\ CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   \\ simp []
   \\ blastLib.FULL_BBLAST_TAC
   )

val lem13 = Q.prove(
   `!c: word64.
       (c = w2w ((11 >< 0) (c >>> 3) : word12) << 3) ==>
       (LSL (w2w (v2w [c ' 14; c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8;
                       c ' 7; c ' 6; c ' 5; c ' 4; c ' 3]: word12),3) = c)`,
   simp [arm8Theory.LSL_def]
   \\ blastLib.BBLAST_TAC
   )

val lem14 = Q.prove(
   `!s state c: word64 n.
      arm8_asm_state s state /\ n < 32 /\ n <> 31 /\
      (7w && (c + s.regs n) = 0w) ==> Aligned (c + state.REG (n2w n), 8)`,
   rw [arm8_asm_state, arm8_stepTheory.Aligned]
   \\ pop_assum mp_tac
   \\ simp [blastLib.BBLAST_PROVE
               ``(7w && x = 0w: word64) = ((2 >< 0) x = 0w: word3)``]
   )

val lem16 =
   blastLib.BBLAST_PROVE
    ``!c: word64.
       0xFFFFFFFFFFFFFF00w <= c /\ c <= 255w ==>
       (sw2sw (v2w
               [c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1;
                c ' 0] : word9) = c)``

val lem17 = Q.prove(
   `!c: word64.
       (c = w2w ((11 >< 0) c : word12)) ==>
       (LSL (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
                       c ' 6; c ' 5; c ' 4; c ' 3; c ' 2;
                       c ' 1; c ' 0]: word12),0) = c)`,
   simp [arm8Theory.LSL_def]
   \\ blastLib.BBLAST_TAC
   )

val lem18 = Q.prove(
   `!c: word64.
       (c = w2w ((11 >< 0) (c >>> 2) : word12) << 2) ==>
       (LSL (w2w (v2w [c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
                       c ' 6; c ' 5; c ' 4; c ' 3; c ' 2]: word12),2) = c)`,
   simp [arm8Theory.LSL_def]
   \\ blastLib.BBLAST_TAC
   )

val lem19 = Q.prove(
   `!s state c: word64 n.
      arm8_asm_state s state /\ n < 32 /\ n <> 31 /\
      (3w && (c + s.regs n) = 0w) ==> Aligned (c + state.REG (n2w n), 4)`,
   rw [arm8_asm_state, arm8_stepTheory.Aligned]
   \\ pop_assum mp_tac
   \\ simp [blastLib.BBLAST_PROVE
               ``(3w && x = 0w: word64) = ((1 >< 0) x = 0w: word2)``]
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
       (word_msb (a + -1w * b) = (word_msb (a) <=/=> word_msb (b)) /\
       (word_msb (a + -1w * b) <=/=> word_msb (a)))``

val lem23 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         (4095w && c = 0w) /\ (0xFFFFFFFFFF000000w && c = 0w) ==>
          ((-1w *
           w2w (v2w [c ' 23; c ' 22; c ' 21; c ' 20; c ' 19; c ' 18;
                     c ' 17; c ' 16; c ' 15; c ' 14; c ' 13; c ' 12] : word12))
            << 12 = -c)``

val lem24 =
   blastLib.BBLAST_PROVE ``!c: word64 n. n <> c ==> (-1w * c + n <> 0w)``

val lem25 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         (0xFFFFFFFFFFFFF000w && c = 0w) ==>
         (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                    c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c)``

val lem26 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
         (4095w && c = 0w) /\ (0xFFFFFFFFFF000000w && c = 0w) ==>
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
       ((tmask && wmask) && ROR (x,w2n r) = x << n)`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.ROR_def,
        arm8Theory.Replicate_def, arm8Theory.Ones_def,
        arm8Theory.HighestSetBit_def, word_log2_7, EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ qunabbrev_tac `q`
   \\ qunabbrev_tac `r`
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1, lsl_lem2]
   \\ simp [and_max ``:64``, lsl_lem3]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ fs [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
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
       ((tmask && wmask) && ROR (x,n) = x >>> n)`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.ROR_def,
        arm8Theory.Replicate_def, arm8Theory.Ones_def,
        arm8Theory.HighestSetBit_def, EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ fs [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
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
        0xFFFFFFFFFFFFFFFFw && ~tmask)`,
   lrw [arm8Theory.DecodeBitMasks_def, arm8Theory.ROR_def,
        arm8Theory.Replicate_def, arm8Theory.Ones_def,
        arm8Theory.HighestSetBit_def, EVAL ``w2i (6w: word7)``,
        and_max ``:6``, ev ``v2w (PAD_LEFT T 6 []) : word6``]
   \\ simp [bitstringTheory.length_pad_left, replicate1, lsl_lem1]
   \\ Cases_on `n = 0`
   >- (fs [] \\ CONV_TAC ev \\ simp [and_max ``:64``])
   \\ fs [DECIDE ``n <> 0n ==> 64 - n < 64``, arithmeticTheory.LESS_MOD,
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

(* some rewrites ----------------------------------------------------------- *)

val encode_rwts =
   let
      open arm8Theory
   in
      [arm8_enc, arm8_encode_def, arm8_encodeTheory.InstructionEncode_def,
       Encode_def, e_data_def, e_branch_def, e_load_store_def, e_sf_def,
       e_LoadStoreImmediate_def, EncodeLogicalOp_def, NoOperation_def,
       ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm
      ]
   end

val enc_rwts =
   [arm8_config_def, offset_monotonic_def, cmp_cond_def, aligned4,
    valid_immediate_thm, lem7, lem8, lem9, lem10, lem11] @
   encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
   [enc_ok_def, arm8_config_def] @ encode_rwts @ asmLib.asm_ok_rwts

val dec_rwts = [arm8_dec_def, decode_word_def, fetch_word_def]

(* some custom tactics ----------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!s state a b c d.
      arm8_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.icache s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      (state.PSTATE.EL = 0w) /\
      ~state.SCTLR_EL1.E0E /\
      ~state.SCTLR_EL1.SA0 /\
      ~state.TCR_EL1.TBI1 /\
      ~state.TCR_EL1.TBI0 /\
      Aligned (state.PC,4) /\
      (state.MEM (state.PC + 3w) = d) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC) = a)`,
   rw [arm8_asm_state_def, bytes_in_memory_def]
   \\ simp []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      arm8_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.icache s.mem s.mem_domain ==>
      (state.MEM (state.PC + w + 3w) = d) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w) = a)`,
   rw [arm8_asm_state_def, bytes_in_memory_def]
   \\ simp []
   )

local
   fun is_reg_31 tm =
      case Lib.total ((bitstringSyntax.dest_v2w ## wordsSyntax.uint_of_word) o
                      boolSyntax.dest_eq) tm of
         SOME ((_, ty), 31) => ty = ``:5``
       | _ => false
   fun dest_bytes_in_memory tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("asm$bytes_in_memory", [_, l, _, _, _]) =>
            SOME (fst (listSyntax.dest_list l))
       | _ => NONE
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
   fun dec tm =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         l |> arm8_stepLib.arm8_decode
           |> Drule.DISCH_ALL
           |> arm8_state_rule
           |> REWRITE_RULE [th1, lem2, lem3, lem5, lem6]
      end
   val (_, _, dest_Decode, is_Decode) =
      HolKernel.syntax_fns "arm8" 1 HolKernel.dest_monop HolKernel.mk_monop
         "Decode"
   val find_Decode = HolKernel.bvk_find_term (is_Decode o snd) dest_Decode
in
   val filter_reg_31 = List.filter (not o List.exists is_reg_31 o Thm.hyp)
   fun decode_tac (asl, g) =
      (case find_Decode g of
          SOME tm =>
           let
              val dec_thm = dec tm
         (*   val () = (print_thm dec_thm; print "\n")  *)
           in
              imp_res_tac dec_thm
              \\ asm_simp_tac (srw_ss())
                   [dec_thm, arm8_dec_aux_def]
              \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
              \\ TRY (qunabbrev_tac `q` \\ qunabbrev_tac `r` \\ simp [lem4])
              \\ lfs [arm8_stepTheory.Aligned, arm8Theory.DecodeShift_def,
                      arm8Theory.num2ShiftType_thm, arm8Theory.LSL_def,
                      arm8Theory.LSR_def, bop_dec_def, lem1]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac pick fltr state (asl, g) =
      (case List.mapPartial dest_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step fltr state (pick l))) (asl, g)
end

local
   fun dest_v2w_or_n2w tm =
      bitstringSyntax.dest_v2w tm handle HOL_ERR _ => wordsSyntax.dest_n2w tm
   val is_byte_eq =
      Lib.can ((wordsSyntax.dest_word_extract ## dest_v2w_or_n2w) o
               boolSyntax.dest_eq)
in
   val byte_eq_tac =
      rule_assum_tac
        (Conv.CONV_RULE
           (Conv.DEPTH_CONV
              (fn tm => if is_byte_eq tm
                           then blastLib.BBLAST_CONV tm
                        else Conv.NO_CONV tm)
            THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV))
end

val comm = ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]

fun next_state_tac0 thm f fltr q =
   next_state_tac f fltr q
   \\ imp_res_tac thm
   \\ fs [lem1, lem2, lem3, lem5, lem6]
   \\ byte_eq_tac
   \\ rfs [lem13, lem16, lem17, lem18, lem20, lem21, lem22, lem23, lem24, lem25,
           lem26, comm lem21, comm lem22, combinTheory.UPDATE_APPLY,
           ShiftValue0, arm8_stepTheory.Aligned_numeric,
           CONJUNCT1 arm8_stepTheory.Aligned, arm8_stepTheory.ConditionTest,
           wordsTheory.ADD_WITH_CARRY_SUB, wordsTheory.WORD_NOT_LOWER_EQUAL]

val next_state_tac01 =
   next_state_tac0 bytes_in_memory_thm List.last filter_reg_31 `state`

fun next_state_tacN (n, w, x) fltr (asl, g) =
   let
      val tm = Lib.funpow n Term.rand g
   in
      next_state_tac0 (Q.SPEC w bytes_in_memory_thm2)
         (fn l => List.nth (l, x)) fltr `^tm` (asl, g)
   end

val next_state_tac1 = next_state_tacN (3, `4w`, 0)

fun state_tac thms =
   REPEAT (qpat_assum `NextStateARM8 q = z` (K all_tac))
   \\ fs ([arm8_asm_state] @ thms)
   \\ rw [combinTheory.APPLY_UPDATE_THM, arm8_stepTheory.Aligned_numeric]

val decode_tac0 =
   simp enc_rwts
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ imp_res_tac Decode_EncodeBitMask
   \\ decode_tac
   \\ blastLib.FULL_BBLAST_TAC

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
                  (wordsLib.WORD_DECIDE
                     ``a <> 63w ==> w2n (a: word6) <> 63``)
             \\ qunabbrev_tac `q`
             \\ blastLib.FULL_BBLAST_TAC),
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC
          DecodeBitMasks_SOME,
       Q.SPECL_THEN [`n2w n1`, `63w`] STRIP_ASSUME_TAC
          DecodeBitMasks_SOME
   ]

fun cmp_case_tac q =
   Cases_on q
   >| [
        next_state_tac1 List.tl,
        next_state_tac1 (fn l => [hd l])
   ]
   \\ state_tac [arm8_stepTheory.Aligned_numeric, arm8_stepTheory.Aligned]
   \\ blastLib.FULL_BBLAST_TAC

fun next_tac n =
   qexists_tac n \\ simp [arm8_next_def, numeralTheory.numeral_funpow]
fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

(* -------------------------------------------------------------------------
   arm8_asm_deterministic
   arm8_backend_correct
   ------------------------------------------------------------------------- *)

val ext12 = ``(11 >< 0) : word64 -> word12``

val arm8_encoding = Count.apply Q.prove (
   `!i. asm_ok i arm8_config ==>
        let l = arm8_enc i in
           (!x. arm8_dec (l ++ x) = i) /\ (LENGTH l MOD 4 = 0)`,
   Cases
   >- (
      (*
        --------------
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
         \\ Cases_on `arm8_enc_mov_imm c`
         >| [ Cases_on `arm8_enc_mov_imm (~c)`
              >| [ Cases_on `EncodeBitMask (Imm64 c)`
                   >| [
                        simp enc_rwts
                        \\ REPEAT (simp dec_rwts \\ decode_tac)
                        \\ blastLib.BBLAST_TAC,
                        Cases_on `x` \\ Cases_on `r`
                   ],
                   Cases_on `x`
              ],
              Cases_on `x`
         ]
         \\ simp enc_rwts
         \\ REPEAT strip_tac
         \\ simp dec_rwts
         \\ imp_res_tac Decode_EncodeBitMask
         \\ imp_res_tac lem12
         \\ decode_tac
         \\ simp dec_rwts
         \\ decode_tac
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
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ shift_cases_tac
            \\ decode_tac0
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      >| [
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,3))),3))`,
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,0))),0))`,
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,2))),2))`,
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,3))),3))`,
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,0))),0))`,
         Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,2))),2))`
      ]
      \\ decode_tac0
      )
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ Cases_on `o'`
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ REVERSE (Cases_on `o'`)
      >- fs enc_rwts
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ simp enc_rwts
      \\ REPEAT strip_tac
      \\ simp dec_rwts
      \\ imp_res_tac Decode_EncodeBitMask
      \\ decode_tac
      \\ simp dec_rwts
      \\ decode_tac
      \\ simp [cond_cmp_def]
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*
        --------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ decode_tac0
      )
      (*
        --------------
          no Cache
        --------------*)
   \\ fs enc_rwts
   )

val arm8_asm_deterministic = Q.store_thm("arm8_asm_deterministic",
   `asm_deterministic arm8_enc arm8_config`,
   metis_tac [decoder_asm_deterministic, has_decoder_def, arm8_encoding]
   )

val arm8_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [arm8_config_def] arm8_asm_deterministic

val arm8_backend_correct = Count.apply Q.store_thm ("arm8_backend_correct",
   `backend_correct arm8_enc arm8_config arm8_next arm8_asm_state`,
   simp [backend_correct_def]
   \\ REVERSE conj_tac
   >| [
      rw [asm_step_def] \\ Cases_on `i`,
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
   >- (
      (*
        --------------
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
         \\ REVERSE (Cases_on `arm8_enc_mov_imm c`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ lfs enc_rwts
             \\ next_state_tac01
             \\ imp_res_tac lem27
             \\ state_tac []
            )
         \\ REVERSE (Cases_on `arm8_enc_mov_imm ~c`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ lfs enc_rwts
             \\ next_state_tac01
             \\ imp_res_tac lem27
             \\ state_tac [lem28]
            )
         \\ REVERSE (Cases_on `EncodeBitMask (Imm64 c)`)
         >- (
             next_tac `0`
             \\ Cases_on `x`
             \\ Cases_on `r`
             \\ lfs enc_rwts
             \\ imp_res_tac Decode_EncodeBitMask
             \\ next_state_tac01
             \\ state_tac []
            )
         \\ next_tac `3`
         \\ lfs enc_rwts
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac01
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tacN (7, `4w`, 1) filter_reg_31
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tacN (5, `8w`, 1) filter_reg_31
         \\ next_state_tacN (3, `12w`, 0) filter_reg_31
         \\ state_tac []
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
            \\ fs []
            \\ imp_res_tac Decode_EncodeBitMask
            \\ next_state_tac01
            \\ state_tac []
            \\ blastLib.FULL_BBLAST_TAC
            )
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ shift_cases_tac
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac [lsr, asr]
            >| [
                imp_res_tac lsl,
                imp_res_tac (lsl |> Q.SPEC `0w` |> SIMP_RULE (srw_ss()) []),
                imp_res_tac asr2
            ]
            \\ simp []
         )
         (*
           --------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ next_tac `0`
         \\ Cases_on `a`
         \\ Cases_on `m`
         >| [
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,3))),3))`,
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,0))),0))`,
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,2))),2))`,
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,3))),3))`,
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,0))),0))`,
            Cases_on `~word_msb c /\ (c = LSL (w2w (^ext12 (LSR (c,2))),2))`
         ]
         \\ lfs enc_rwts
         \\ fs [arm8Theory.LSL_def, arm8Theory.LSR_def]
         \\ TRY (`Aligned (c + state.REG (n2w n'),8)`
                 by (imp_res_tac lem14 \\ NO_TAC)
                 ORELSE `Aligned (c + state.REG (n2w n'),4)`
                        by (imp_res_tac lem19 \\ NO_TAC))
         \\ next_state_tac01
         \\ state_tac
               [arm8_stepTheory.mem_dword_def, arm8_stepTheory.mem_word_def,
                arm8Theory.ExtendWord_def]
         \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
         \\ NTAC 2 (lrw [FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM])
         \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
      ) (* close Inst *)
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac `0`
      \\ Cases_on `o'`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ state_tac [arm8_stepTheory.Aligned]
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*
        --------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ next_tac `1`
      \\ REVERSE (Cases_on `o'`)
      >- fs enc_rwts
      \\ Cases_on `r`
      >| [
         Cases_on `c`
         \\ lfs enc_rwts
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac0 bytes_in_memory_thm List.last List.tl `state`
         >| [
            cmp_case_tac `state.REG (n2w n) = state.REG (n2w n')`,
            cmp_case_tac `state.REG (n2w n) <+ state.REG (n2w n')`,
            cmp_case_tac `state.REG (n2w n) < state.REG (n2w n')`,
            cmp_case_tac `state.REG (n2w n) && state.REG (n2w n') = 0w`
         ],
         Cases_on `c`
         \\ lfs enc_rwts
         \\ fs []
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ imp_res_tac Decode_EncodeBitMask
         \\ next_state_tac0 bytes_in_memory_thm List.last List.tl `state`
         >| [
            cmp_case_tac `state.REG (n2w n) = c'`,
            cmp_case_tac `state.REG (n2w n) = c'`,
            cmp_case_tac `state.REG (n2w n) <+ c'`,
            cmp_case_tac `state.REG (n2w n) <+ c'`,
            cmp_case_tac `state.REG (n2w n) < c'`,
            cmp_case_tac `state.REG (n2w n) < c'`,
            cmp_case_tac `state.REG (n2w n) && c' = 0w`
         ]
      ]
      )
      (*
        --------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ next_tac `0`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ state_tac [arm8_stepTheory.Aligned]
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac `0`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ state_tac [arm8_stepTheory.Aligned]
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ next_tac `0`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ state_tac []
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*
        --------------
          no Cache
        --------------*)
   >- fs enc_rwts
   >- (
      (*
        --------------
          enc MOD 4 enc_ok
        --------------*)
      simp
         [SIMP_RULE (bool_ss++boolSimps.LET_ss) [arm8_config_def] arm8_encoding]
      )
   >- (
      (*
        --------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ Cases_on `i`
      \\ lfs enc_rwts
      )
   >- (
      (*
        --------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `i`
      >| [Cases_on `ri` \\ Cases_on `cmp`, all_tac]
      \\ lfs enc_rwts
      )
   >- (
      (*
        --------------
          Call enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lfs enc_rwts
      )
   >- (
      (*
        --------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lfs enc_rwts
      )
      (*
        --------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [arm8_asm_deterministic_config]
   )

val () = export_theory ()
