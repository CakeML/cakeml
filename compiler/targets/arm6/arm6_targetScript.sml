open HolKernel Parse boolLib bossLib
open asmLib arm_stepLib;

val () = new_theory "arm6_target"

val () = wordsLib.guess_lengths ()

(* --- The next-state function --- *)

val arm6_next_def = Define `arm6_next = THE o NextStateARM`

(* --- Relate ASM and ARMv6 states --- *)

val arm6_ok_def = Define`
   arm6_ok ms =
   GoodMode ms.CPSR.M /\ ~ms.CPSR.E /\ ~ms.CPSR.J /\ ~ms.CPSR.T /\
   (ms.Architecture = ARMv6) /\ ~ms.Extensions Extension_Security /\
   (ms.exception = NoException) /\ aligned 2 (ms.REG RName_PC)`

val arm6_asm_state_def = Define`
   arm6_asm_state s ms =
   arm6_ok ms /\
   (!i. i < 15 ==> (s.regs i = ms.REG (R_mode ms.CPSR.M (n2w i)))) /\
   (fun2set (s.mem, s.mem_domain) = fun2set (ms.MEM, s.mem_domain)) /\
   (s.pc = ms.REG RName_PC)`

(* --- Encode ASM instructions to ARM bytes. --- *)

val arm6_encode_fail_def = zDefine`
  arm6_encode_fail = [0w; 0w; 0w; 0w] : word8 list`

val arm6_encode_def = Define`
   arm6_encode c i =
   case encode (c, i) of
      ARM w =>
        [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list
    | _ => arm6_encode_fail`

val () = Parse.temp_overload_on ("enc", ``arm6_encode 14w``)

val arm6_bop_def = Define`
   (arm6_bop Add = 0b0100w: word4) /\
   (arm6_bop Sub = 0b0010w) /\
   (arm6_bop And = 0b0000w) /\
   (arm6_bop Or  = 0b1100w) /\
   (arm6_bop Xor = 0b0001w)`

val arm6_sh_def = Define`
   (arm6_sh Lsl = SRType_LSL) /\
   (arm6_sh Lsr = SRType_LSR) /\
   (arm6_sh Asr = SRType_ASR)`

val arm6_cmp_def = Define`
   (arm6_cmp Less     = (2w, 0b1011w) : word2 # word4) /\
   (arm6_cmp Lower    = (2w, 0b0011w)) /\
   (arm6_cmp Equal    = (2w, 0b0000w)) /\
   (arm6_cmp Test     = (0w, 0b0000w)) /\
   (arm6_cmp NotLess  = (2w, 0b1010w)) /\
   (arm6_cmp NotLower = (2w, 0b0010w)) /\
   (arm6_cmp NotEqual = (2w, 0b0001w)) /\
   (arm6_cmp NotTest  = (0w, 0b0001w))`

val arm6_enc_def = Define`
   (arm6_enc (Inst Skip) =
       (* NoOperation instruction is for >= ARMv6T2 and so isn't available.
          Using BIC r0, r0, #0 instead.
        *)
       enc (Data (ArithLogicImmediate (14w, F, 0w, 0w, 0w)))) /\
   (arm6_enc (Inst (Const r i)) =
      case EncodeARMImmediate i of
         SOME imm12 => enc (Data (Move (F, F, n2w r, imm12)))
       | NONE =>
           (case EncodeARMImmediate (~i) of
               SOME imm12 => enc (Data (Move (F, T, n2w r, imm12)))
             | NONE =>
                 enc (Load (LoadLiteral (T, n2w r, 0w))) ++
                 enc (Branch (BranchTarget (0w))) ++
                 [(7 >< 0) i; (15 >< 8) i; (23 >< 16) i; (31 >< 24) i])) /\
   (arm6_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
       enc (Data
              (Register
                 (arm6_bop bop, F, n2w r1, n2w r2, n2w r3, SRType_LSL, 0)))) /\
   (arm6_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       enc (Data (ArithLogicImmediate
                     (arm6_bop bop, F, n2w r1, n2w r2,
                      THE (EncodeARMImmediate i))))) /\
   (arm6_enc (Inst (Arith (Shift sh r1 r2 n))) =
       enc (Data (ShiftImmediate (F, F, n2w r1, n2w r2, arm6_sh sh, n)))) /\
   (arm6_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
       enc (Data (TestCompareImmediate (2w, n2w r4, 0w))) ++
       arm6_encode 0w (Data (TestCompareImmediate (3w, n2w r4, 0w))) ++
       enc (Data (Register (5w, T, n2w r1, n2w r2, n2w r3, SRType_LSL, 0))) ++
       arm6_encode 3w (Data (Move (F, F, n2w r4, 0w))) ++
       arm6_encode 2w (Data (Move (F, F, n2w r4, 1w)))) /\
   (arm6_enc (Inst (Mem Load r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Load
              (LoadWord (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Load32 _ _)) = arm6_encode_fail) /\
   (arm6_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Load
              (LoadByte
                 (T, add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Store r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Store
              (StoreWord
                 (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Store32 r1 (Addr r2 a))) = arm6_encode_fail) /\
   (arm6_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Store
              (StoreByte
                 (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Jump a) = enc (Branch (BranchTarget (a - 8w)))) /\
   (arm6_enc (JumpCmp cmp r1 (Reg r2) a) =
       let (opc, c) = arm6_cmp cmp in
          enc
            (Data (TestCompareRegister (opc, n2w r1, n2w r2, SRType_LSL, 0))) ++
          arm6_encode c (Branch (BranchTarget (a - 12w)))) /\
   (arm6_enc (JumpCmp cmp r (Imm i) a) =
       let (opc, c) = arm6_cmp cmp
       and imm12 = THE (EncodeARMImmediate i)
       in
          enc (Data (TestCompareImmediate (opc, n2w r, imm12))) ++
          arm6_encode c (Branch (BranchTarget (a - 12w)))) /\
   (arm6_enc (Call a) =
      enc (Branch (BranchLinkExchangeImmediate (InstrSet_ARM, a - 8w)))) /\
   (arm6_enc (JumpReg r) = enc (Branch (BranchExchange (n2w r)))) /\
   (arm6_enc (Loc r i) =
       let (opc, imm32) = if 8w <= i then (4w, i - 8w) else (2w, 8w - i) in
         if imm32 <+ 256w then
            enc
              (Data (ArithLogicImmediate (opc, F, n2w r, 15w, (7 >< 0) imm32)))
         else
            let imm12t = (12w:word4) @@ (15 >< 8) imm32
            and imm12b = (7 >< 0) imm32
            in
               enc (Data (ArithLogicImmediate (opc, F, n2w r, 15w, imm12t))) ++
               enc (Data (ArithLogicImmediate (opc, F, n2w r, n2w r, imm12b))))`

(* --- Configuration for ARMv6 --- *)

val eval = rhs o concl o EVAL
val min12 = eval ``-(w2w (UINT_MAXw: word12)) : word32``
val max12 = eval ``w2w (UINT_MAXw: word12) : word32``
val min16 = eval ``-(w2w (UINT_MAXw: word16)) + 8w : word32``
val max16 = eval ``w2w (UINT_MAXw: word16) + 8w : word32``
val min26 = eval ``sw2sw (INT_MINw: 26 word) + 12w : word32``
val max26 = eval ``sw2sw (INT_MAXw: 26 word) + 8w : word32``

val valid_immediate_def = Define`
   valid_immediate = IS_SOME o EncodeARMImmediate`

val arm6_config_def = Define`
   arm6_config =
   <| ISA := ARMv6
    ; encode := arm6_enc
    ; reg_count := 16
    ; avoid_regs := [15]
    ; link_reg := SOME 14
    ; has_mem_32 := F
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := \c i. valid_immediate i
    ; addr_offset_min := ^min12
    ; addr_offset_max := ^max12
    ; jump_offset_min := ^min26
    ; jump_offset_max := ^max26
    ; cjump_offset_min := ^min26
    ; cjump_offset_max := ^max26
    ; loc_offset_min := ^min16
    ; loc_offset_max := ^max16
    ; code_alignment := 2
    |>`

val arm6_proj_def = Define`
   arm6_proj d s =
   (s.CPSR, s.Architecture, s.Extensions, s.exception,
    s.REG o R_mode s.CPSR.M, fun2set (s.MEM,d))`

val arm6_target_def = Define`
   arm6_target =
   <| get_pc := (\s. s.REG RName_PC)
    ; get_reg := (\s. s.REG o R_mode s.CPSR.M o n2w)
    ; get_byte := arm_state_MEM
    ; state_ok := arm6_ok
    ; state_rel := arm6_asm_state
    ; proj := arm6_proj
    ; next := arm6_next
    ; config := arm6_config
    |>`

val () = export_theory ()
