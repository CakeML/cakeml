(*
  Define the target compiler configuration for ARMv8.
*)
open HolKernel Parse boolLib bossLib
open asmLib arm8_stepTheory;

val () = new_theory "arm8_target"

val () = wordsLib.guess_lengths ()

(* --- The next-state function --- *)

val arm8_next_def = Define `arm8_next = THE o NextStateARM8`

(* --- Valid ARMv8 states --- *)

val arm8_ok_def = Define`
   arm8_ok ms <=>
   (ms.PSTATE.EL = 0w) /\
   ~ms.SCTLR_EL1.E0E  /\ ~ms.SCTLR_EL1.SA0 /\
   ~ms.TCR_EL1.TBI1 /\ ~ms.TCR_EL1.TBI0 /\
   (ms.exception = NoException) /\ aligned 2 ms.PC`

(* --- Encode ASM instructions to ARM bytes. --- *)

val arm8_encode_fail_def = zDefine`
  arm8_encode_fail = [NoOperation]`

val arm8_encode_def = Define`
   arm8_encode i =
   case arm8$Encode i of
      ARM8 w => [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w]
    | _ => [0w; 0w; 0w; 0w]`

val bop_enc_def = Define`
   (bop_enc And = LogicalOp_AND) /\
   (bop_enc Or  = LogicalOp_ORR) /\
   (bop_enc Xor = LogicalOp_EOR)`

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
   if (i && 0xFFFFFFFFFFFF0000w) = 0w then
      SOME ((15 >< 0) i, 0w: word2)
   else if (i && 0xFFFFFFFF0000FFFFw) = 0w then
      SOME ((31 >< 16) i, 1w)
   else if (i && 0xFFFF0000FFFFFFFFw) = 0w then
      SOME ((47 >< 32) i, 2w)
   else if (i && 0x0000FFFFFFFFFFFFw) = 0w then
      SOME ((63 >< 48) i, 3w)
   else
      NONE`

val temp = ``26w : word5``

val arm8_load_store_ast_def = Define`
  arm8_load_store_ast ls r1 r2 a =
  let unsigned = ~word_msb a in
  if a <> sw2sw ((8 >< 0) a : word9) /\
     (unsigned ==> a <> w2w ((11 >< 0) (a >>> 3) : word12) << 3) then
    let (b, c) = if unsigned then (a - 0xFFw, 0xFFw) else (-a - 0x100w, -0x100w)
    in
      [Data (AddSubImmediate@64 (1w, ~unsigned, F, b, n2w r2, ^temp));
       LoadStore
         (LoadStoreImmediate@64
            (3w, F, ls, AccType_NORMAL, F, F, F, F, F, unsigned, c,
             ^temp, n2w r1))]
  else
    [LoadStore
       (LoadStoreImmediate@64
          (3w, F, ls, AccType_NORMAL, F, F, F, F, F, unsigned, a,
           n2w r2, n2w r1))]`

val arm8_ast_def = Define`
   (arm8_ast (Inst Skip) = [NoOperation]) /\
   (arm8_ast (Inst (Const r i)) =
      case arm8_enc_mov_imm i of
         SOME (imm16, hw) =>
           [Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, n2w r))]
       | NONE =>
          (case arm8_enc_mov_imm (~i) of
               SOME (imm16, hw) =>
                  [Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, n2w r))]
            | NONE =>
                if IS_SOME (EncodeBitMask i) then
                  [Data (LogicalImmediate@64
                           (1w, LogicalOp_ORR, F, i, 0x1Fw, n2w r))]
                else
                  [Data (MoveWide@64
                           (1w, MoveWideOp_K, 0w, (15 >< 0) i, n2w r));
                   Data (MoveWide@64
                           (1w, MoveWideOp_K, 1w, (31 >< 16) i, n2w r));
                   Data (MoveWide@64
                           (1w, MoveWideOp_K, 2w, (47 >< 32) i, n2w r));
                   Data (MoveWide@64
                           (1w, MoveWideOp_K, 3w, (63 >< 48) i, n2w r))])) /\
   (arm8_ast (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      [Data
        (case bop of
            Add => AddSubShiftedRegister@64
                     (1w, F, F, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1)
          | Sub => AddSubShiftedRegister@64
                     (1w, T, F, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1)
          | x => LogicalShiftedRegister@64
                     (1w, bop_enc x, F, F, ShiftType_LSL, 0,
                      n2w r3, n2w r2, n2w r1))]) /\
   (arm8_ast (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
      [Data
        (case bop of
            Add => AddSubImmediate@64 (1w, F, F, i, n2w r2, n2w r1)
          | Sub => AddSubImmediate@64 (1w, T, F, i, n2w r2, n2w r1)
          | Xor => if i = -1w then
                     LogicalShiftedRegister@64
                       (1w, LogicalOp_ORR, T, F, ShiftType_LSL, 0, n2w r2, 31w,
                        n2w r1)
                   else
                     LogicalImmediate@64
                       (1w, LogicalOp_EOR, F, i, n2w r2, n2w r1)
          | x => LogicalImmediate@64 (1w, bop_enc x, F, i, n2w r2, n2w r1))]) /\
   (arm8_ast (Inst (Arith (Shift sh r1 r2 n))) =
      case sh of
         Lsl => (let i = n2w n : word6 in
                 let r = -i and s = 63w - i in
                    case DecodeBitMasks (1w, s, r, F) of
                       SOME (wmask, tmask) =>
                         [Data
                            (BitfieldMove@64
                               (1w, T, F, wmask, tmask, w2n r, w2n s, n2w r2,
                                n2w r1))]
                     | NONE => arm8_encode_fail)
       | Ror => [Data (ExtractRegister@64 (1w, n2w n, n2w r2, n2w r2, n2w r1))]
       | x => (case DecodeBitMasks (1w, 63w, n2w n, F) of
                  SOME (wmask, tmask) =>
                     [Data
                       (BitfieldMove@64
                         (1w, T, x = Asr, wmask, tmask, n, 63, n2w r2, n2w r1))]
                | NONE => arm8_encode_fail)) /\
   (arm8_ast (Inst (Arith (Div r1 r2 r3))) =
      [Data (Division@64 (1w, F, n2w r3, n2w r2, n2w r1))]) /\
   (arm8_ast (Inst (Arith (LongMul r1 r2 r3 r4))) =
      [Data (MultiplyHigh (F, n2w r4, n2w r3, n2w r1));
       Data (MultiplyAddSub@64 (1w, F, n2w r4, 31w, n2w r3, n2w r2))]) /\
   (arm8_ast (Inst (Arith (LongDiv _ _ _ _ _))) = arm8_encode_fail) /\
   (arm8_ast (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      [Data (AddSubImmediate@64 (1w, T, T, 0w, n2w r4, 0x1Fw));
       Data (ConditionalCompareImmediate@64
               (1w, F, 0w, 0w, (F, F, T, F), n2w r2));
       Data (AddSubCarry@64 (1w, F, T, n2w r3, n2w r2, n2w r1));
       Data (MoveWide@64 (1w, MoveWideOp_Z, 0w, 0w, n2w r4));
       Data (AddSubCarry@64 (1w, F, F, 31w, n2w r4, n2w r4))]) /\
   (arm8_ast (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
      [Data (AddSubShiftedRegister@64
               (1w, F, T, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1));
       Data (ConditionalSelect@64 (1w, F, T, 7w, 31w, 31w, n2w r4))]) /\
   (arm8_ast (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
      [Data (AddSubShiftedRegister@64
               (1w, T, T, ShiftType_LSL, n2w r3, 0w, n2w r2, n2w r1));
       Data (ConditionalSelect@64 (1w, F, T, 7w, 31w, 31w, n2w r4))]) /\
   (arm8_ast (Inst (Mem Load r1 (Addr r2 a))) =
      arm8_load_store_ast MemOp_LOAD r1 r2 a) /\
   (*
   (arm8_ast (Inst (Mem Load32 r1 (Addr r2 a))) =
        (LoadStore
           (LoadStoreImmediate@32
              (2w, T, MemOp_LOAD, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   *)
   (arm8_ast (Inst (Mem Load8 r1 (Addr r2 a))) =
      [LoadStore
         (LoadStoreImmediate@8
            (0w, F, MemOp_LOAD, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
             a, n2w r2, n2w r1))]) /\
   (arm8_ast (Inst (Mem Store r1 (Addr r2 a))) =
      arm8_load_store_ast MemOp_STORE r1 r2 a) /\
   (*
   (arm8_ast (Inst (Mem Store32 r1 (Addr r2 a))) =
        (LoadStore
           (LoadStoreImmediate@32
              (2w, T, MemOp_STORE, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
               a, n2w r2, n2w r1)))) /\
   *)
   (arm8_ast (Inst (Mem Store8 r1 (Addr r2 a))) =
      [LoadStore
         (LoadStoreImmediate@8
            (0w, F, MemOp_STORE, AccType_NORMAL, F, F, F, F, F, ~word_msb a,
             a, n2w r2, n2w r1))]) /\
   (arm8_ast (Inst (FP _)) = arm8_encode_fail) /\
   (arm8_ast (Jump a) =
      [Branch (BranchImmediate (a, BranchType_JMP))]) /\
   (arm8_ast (JumpCmp cmp r1 (Reg r2) a) =
      [Data (if is_test cmp then
                LogicalShiftedRegister@64
                   (1w, LogicalOp_AND, F, T, ShiftType_LSL, 0,
                    n2w r2, n2w r1, 0x1Fw)
             else
                AddSubShiftedRegister@64
                   (1w, T, T, ShiftType_LSL, n2w r2, 0w, n2w r1, 0x1Fw));
       Branch (BranchConditional (a - 4w, cmp_cond cmp))]) /\
   (arm8_ast (JumpCmp cmp r (Imm i) a) =
      [Data (if is_test cmp then
                LogicalImmediate@64
                   (1w, LogicalOp_AND, T, i, n2w r, 0x1Fw)
             else
                AddSubImmediate@64 (1w, T, T, i, n2w r, 0x1Fw));
       Branch (BranchConditional (a - 4w, cmp_cond cmp))]) /\
   (arm8_ast (Call a) =
      [Branch (BranchImmediate (a, BranchType_CALL))]) /\
   (arm8_ast (JumpReg r) =
      [Branch (BranchRegister (n2w r, BranchType_JMP))]) /\
   (arm8_ast (Loc r i) =
      if sw2sw (INT_MINw: word20) ≤ i ∧ i ≤ sw2sw (INT_MAXw: word20)
      then
        [Address (F, i, n2w r)]
      else
        [
        Address (F, 0w, n2w r);
        Data (MoveWide@64
                (1w, MoveWideOp_K, 0w, (15 >< 0) i, ^temp));
        Data (MoveWide@64
                (1w, MoveWideOp_K, 1w, (31 >< 16) i, ^temp));
        Data (MoveWide@64
                (1w, MoveWideOp_K, 2w, (47 >< 32) i, ^temp));
        Data (MoveWide@64
                (1w, MoveWideOp_K, 3w, (63 >< 48) i, ^temp));
        Data (AddSubShiftedRegister@64
                (1w, F, F, ShiftType_LSL, ^temp, 0w, n2w r, n2w r))
        ])`

val arm8_enc_def = zDefine
  `arm8_enc = combin$C LIST_BIND arm8_encode o arm8_ast`

(* --- Configuration for ARMv8 --- *)

val eval = rhs o concl o EVAL
val off_min9 = eval ``sw2sw (INT_MINw: word9) : word64``
val off_max9 = eval ``sw2sw (INT_MAXw: word9) : word64``
val off_max12 = eval ``w2w (UINT_MAXw: word12) : word64``
val off_min = eval ``-^off_max12 + ^off_min9``
val off_max = eval ``^off_max12 + ^off_max9``

val loc_min = eval ``sw2sw (INT_MINw: word32) : word64``
val loc_max = eval ``sw2sw (INT_MAXw: word32) : word64``
val cjump_min = eval ``sw2sw (INT_MINw: 21 word) + 4w : word64``
val cjump_max = eval ``sw2sw (INT_MAXw: 21 word) + 4w : word64``
val jump_min = eval ``sw2sw (INT_MINw: word28) : word64``
val jump_max = eval ``sw2sw (INT_MAXw: word28) : word64``

val valid_immediate_def = Define`
   valid_immediate (c:binop+cmp) (i: word64) =
   if c IN {INL Add; INL Sub;
            INR Less; INR Lower; INR Equal;
            INR NotLess; INR NotLower; INR NotEqual} then
      ((~0xFFFw && i) = 0w) \/ ((~0xFFF000w && i) = 0w)
   else
      IS_SOME (EncodeBitMask i)`

val arm8_config_def = Define`
   arm8_config =
   <| ISA := ARMv8
    ; encode := arm8_enc
    ; reg_count := 32
    ; fp_reg_count := 0
    ; avoid_regs := [26; 31]
    ; link_reg := SOME 30
    ; two_reg_arith := F
    ; big_endian := F
    ; code_alignment := 2
    ; valid_imm := valid_immediate
    ; addr_offset := (^off_min, ^off_max)
    ; byte_offset := (^off_min9, ^off_max12)
    ; jump_offset := (^jump_min, ^jump_max)
    ; cjump_offset := (^cjump_min, ^cjump_max)
    ; loc_offset := (^loc_min, ^loc_max)
    |>`

val arm8_proj_def = Define`
   arm8_proj d s =
   (s.PSTATE, s.SCTLR_EL1, s.TCR_EL1, s.exception, s.REG, fun2set (s.MEM,d),
    s.PC)`

val arm8_target_def = Define`
   arm8_target =
   <| next := arm8_next
    ; config := arm8_config
    ; get_pc := arm8_state_PC
    ; get_reg := (\s. arm8_state_REG s o n2w)
    ; get_byte := arm8_state_MEM
    ; state_ok := arm8_ok
    ; proj := arm8_proj
    |>`

val (arm8_config, arm8_asm_ok) =
  asmLib.target_asm_rwts
    [DECIDE ``a < 32 /\ a <> 26 /\ a <> 31n <=> a <> 26 /\ a < 31``]
    ``arm8_config``

val arm8_config = save_thm("arm8_config", arm8_config)
val arm8_asm_ok = save_thm("arm8_asm_ok", arm8_asm_ok)

val () = export_theory ()
