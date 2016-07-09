open HolKernel Parse boolLib bossLib
open asmLib arm8Theory;

val () = new_theory "arm8_target"

val () = wordsLib.guess_lengths ()

(* --- Configuration for ARMv8 --- *)

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
   if c IN {INL Add; INL Sub;
            INR Less; INR Lower; INR Equal;
            INR NotLess; INR NotLower; INR NotEqual} then
      (~0xFFFw && i = 0w) \/ (~0xFFF000w && i = 0w)
   else
      IS_SOME (EncodeBitMask i)`

val arm8_config_def = Define`
   arm8_config =
   <| ISA := ARMv8
    ; reg_count := 32
    ; avoid_regs := [31]
    ; link_reg := SOME 30
    ; has_mem_32 := T
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := valid_immediate
    ; addr_offset_min := ^off_min
    ; addr_offset_max := ^off_max
    ; jump_offset_min := ^jump_min
    ; jump_offset_max := ^jump_max
    ; cjump_offset_min := ^cjump_min
    ; cjump_offset_max := ^cjump_max
    ; loc_offset_min := ^loc_min
    ; loc_offset_max := ^loc_max
    ; code_alignment := 2
    |>`

(* --- The next-state function --- *)

val arm8_next_def = Define `arm8_next = THE o NextStateARM8`

(* --- Relate ASM and ARMv8 states --- *)

val arm8_ok_def = Define`
   arm8_ok ms =
   (ms.PSTATE.EL = 0w) /\
   ~ms.SCTLR_EL1.E0E  /\ ~ms.SCTLR_EL1.SA0 /\
   ~ms.TCR_EL1.TBI1 /\ ~ms.TCR_EL1.TBI0 /\
   (ms.exception = NoException) /\ aligned 2 ms.PC`

val arm8_asm_state_def = Define`
   arm8_asm_state s ms =
   arm8_ok ms /\
   (!i. i < 31 ==> (s.regs i = ms.REG (n2w i))) /\
   (fun2set (s.mem, s.mem_domain) = fun2set (ms.MEM, s.mem_domain)) /\
   (s.pc = ms.PC)`

(* --- Encode ASM instructions to ARM bytes. --- *)

val arm8_encode_def = Define`
   arm8_encode i =
   case Encode i of
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
   (cmp_cond Less     = 0b1011w:word4) /\
   (cmp_cond Lower    = 0b0011w) /\
   (cmp_cond Equal    = 0b0000w) /\
   (cmp_cond Test     = 0b0000w) /\
   (cmp_cond NotLess  = 0b1010w) /\
   (cmp_cond NotLower = 0b0010w) /\
   (cmp_cond NotEqual = 0b0001w) /\
   (cmp_cond NotTest  = 0b0001w)`

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
                if IS_SOME (EncodeBitMask i) then
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
   (arm8_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      arm8_encode (Data (AddSubImmediate@64 (1w, T, T, 0w, n2w r4, 0x1Fw))) ++
      arm8_encode (Data (ConditionalCompareImmediate@64
                           (1w, F, 0w, 0w, (F, F, T, F), n2w r2))) ++
      arm8_encode (Data (AddSubCarry@64 (1w, F, T, n2w r3, n2w r2, n2w r1))) ++
      arm8_encode (Data (MoveWide@64 (1w, MoveWideOp_Z, 0w, 0w, n2w r4))) ++
      arm8_encode (Data (AddSubCarry@64 (1w, F, F, 31w, n2w r4, n2w r4)))) /\
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
   (arm8_enc (Jump a) =
      arm8_encode (Branch (BranchImmediate (a, BranchType_JMP)))) /\
   (arm8_enc (JumpCmp cmp r1 (Reg r2) a) =
      arm8_encode
         (Data (if is_test cmp then
                   LogicalShiftedRegister@64
                      (1w, LogicalOp_AND, F, T, ShiftType_LSL, 0,
                       n2w r2, n2w r1, 0x1Fw)
                else
                   AddSubShiftedRegister@64
                      (1w, T, T, ShiftType_LSL, n2w r2, 0w, n2w r1, 0x1Fw))) ++
      arm8_encode (Branch (BranchConditional (a - 4w, cmp_cond cmp)))) /\
   (arm8_enc (JumpCmp cmp r (Imm i) a) =
      arm8_encode
         (Data (if is_test cmp then
                   LogicalImmediate@64
                      (1w, LogicalOp_AND, T, i, n2w r, 0x1Fw)
                else
                   AddSubImmediate@64 (1w, T, T, i, n2w r, 0x1Fw))) ++
      arm8_encode (Branch (BranchConditional (a - 4w, cmp_cond cmp)))) /\
   (arm8_enc (Call a) =
      arm8_encode (Branch (BranchImmediate (a, BranchType_CALL)))) /\
   (arm8_enc (JumpReg r) =
      arm8_encode (Branch (BranchRegister (n2w r, BranchType_JMP)))) /\
   (arm8_enc (Loc r i) = arm8_encode (Address (F, i, n2w r)))`

val cond_cmp_def = Define`
   (cond_cmp (0b1011w:word4) = Less) /\
   (cond_cmp 0b0011w = Lower) /\
   (cond_cmp 0b0000w = Equal) /\
   (cond_cmp 0b1010w = NotLess) /\
   (cond_cmp 0b0010w = NotLower) /\
   (cond_cmp 0b0001w = NotEqual)`

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
   | Data (AddSubImmediate@64 (1w, T, T, i, r1, 0x1Fw)) =>
       (case decode_word rest of
           (Branch (BranchConditional (a, c)), _) =>
              JumpCmp (cond_cmp c) (w2n r1) (Imm i) (a + 4w)
         | (Data (ConditionalCompareImmediate@64
                    (1w, F, 0w, 0w, (F, F, T, F), r2)), rest2) =>
             (case decode_word rest2 of
                 (Data (AddSubCarry@64 (1w, F, T, r3, r4, r5)), rest3) =>
                   (case decode_word rest3 of
                       (Data (MoveWide@64 (1w, MoveWideOp_Z, 0w, 0w, r6)),
                        rest4) =>
                          (case FST (decode_word rest4) of
                              Data (AddSubCarry@64 (1w, F, F, 31w, r7, r8)) =>
                                 if
                 (* 4: 1,6,7,8 *)   (r1 = r6) /\ (r6 = r7) /\ (r7 = r8) /\
                 (* 2: 2,4 *)       (r2 = r4) then
                 (* 1: 5 *)
                 (* 3: 3 *)
                                   Inst (Arith (AddCarry
                                      (w2n r5) (w2n r2) (w2n r3) (w2n r1)))
                                 else ARB
                            | _ => ARB)
                     | _ => ARB)
               | _ => ARB)
         | _ => ARB)
   | Data (LogicalImmediate@64 (1w, LogicalOp_AND, T, i, r, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, 0w)) =>
              JumpCmp Test (w2n r) (Imm i) (a + 4w)
         | Branch (BranchConditional (a, 1w)) =>
              JumpCmp NotTest (w2n r) (Imm i) (a + 4w)
         | _ => ARB)
   | Data (AddSubShiftedRegister@64
             (1w, T, T, ShiftType_LSL, r2, 0w, r1, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, c)) =>
              JumpCmp (cond_cmp c) (w2n r1) (Reg (w2n r2)) (a + 4w)
         | _ => ARB)
   | Data (LogicalShiftedRegister@64
              (1w, LogicalOp_AND, F, T, ShiftType_LSL, 0, r2, r1, 0x1Fw)) =>
       (case FST (decode_word rest) of
           Branch (BranchConditional (a, 0w)) =>
              JumpCmp Test (w2n r1) (Reg (w2n r2)) (a + 4w)
         | Branch (BranchConditional (a, 1w)) =>
              JumpCmp NotTest (w2n r1) (Reg (w2n r2)) (a + 4w)
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
   | Branch (BranchImmediate (a, BranchType_JMP)) => Jump a
   | Branch (BranchImmediate (a, BranchType_CALL)) => Call a
   | Branch (BranchRegister (r, BranchType_JMP)) => JumpReg (w2n r)
   | Address (F, i, r) => Loc (w2n r) i
   | _ => ARB`

val arm8_dec_def = Define `arm8_dec = arm8_dec_aux o decode_word`

val arm8_proj_def = Define`
   arm8_proj d s =
   (s.PSTATE, s.SCTLR_EL1, s.TCR_EL1, s.exception, s.REG, fun2set (s.MEM,d),
    s.PC)`

val arm8_target_def = Define`
   arm8_target =
   <| encode := arm8_enc
    ; get_pc := arm8_state_PC
    ; get_reg := (\s. arm8_state_REG s o n2w)
    ; get_byte := arm8_state_MEM
    ; state_ok := arm8_ok
    ; state_rel := arm8_asm_state
    ; proj := arm8_proj
    ; next := arm8_next
    ; config := arm8_config
    |>`

val () = export_theory ()
