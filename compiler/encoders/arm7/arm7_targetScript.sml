(*
  Define the target compiler configuration for ARMv7.
*)
open HolKernel Parse boolLib bossLib
open asmLib arm_stepTheory;

val () = new_theory "arm7_target";

val () = wordsLib.guess_lengths ();

(* --- The next-state function --- *)

val arm7_next_def = Define `arm7_next = THE o NextStateARM`;

(* --- Valid ARMv7 states --- *)

(* NOTE: The underlying model of ARM VFP does not cover all possible
         details, e.g. floating-point exceptions, treatement of NaNs and
         flushing to zero (non-IEEE operation). However, the model should
         adequately capture CakeML use cases, provided arm7_ok below holds.
*)


val arm7_ok_def = Define`
   arm7_ok ms <=>
   GoodMode ms.CPSR.M /\ ~ms.CPSR.E /\ ~ms.CPSR.J /\ ~ms.CPSR.T /\
   (ms.FP.FPSCR.RMode = 0w) /\ (* Rounding mode is TiesToEven *)
   ~ms.FP.FPSCR.FZ /\  (* Disable flush to zero *)
   ~ms.FP.FPSCR.IXE /\ ~ms.FP.FPSCR.UFE /\ ~ms.FP.FPSCR.OFE /\
   ~ms.FP.FPSCR.DZE /\ ~ms.FP.FPSCR.IOE /\ (* Disable FP exception traps *)
  (* TODO: Potentially change to ARMv7_A *)
   (ms.Architecture = ARMv7_R) /\ ~ms.Extensions Extension_Security /\
   (ms.VFPExtension = VFPv4) /\ (ms.exception = NoException) /\
   aligned 2 (ms.REG RName_PC)`

(* --- Encode ASM instructions to ARM bytes. --- *)

val () = List.app Parse.temp_overload_on
  (ListPair.zip
     (["EQ", "NE", "CS", "CC", "MI", "PL", "VS", "VC",
       "HI", "LS", "GE", "LT", "GT", "LE", "AL"],
      List.tabulate (15, fn i => wordsSyntax.mk_wordii (i, 4))))

val arm7_encode_fail_def = zDefine`
  arm7_encode_fail = [0w; 0w; 0w; 0w] : word8 list`

val arm7_encode1_def = Define`
  arm7_encode1 c i =
  case arm$encode (c, i) of
     ARM w =>
       [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list
   | _ => arm7_encode_fail`

val arm7_encode_def = Define`
   arm7_encode = combin$C LIST_BIND (UNCURRY arm7_encode1)`

val () = Parse.temp_overload_on ("enc", ``arm7_encode1 AL``)

val arm7_bop_def = Define`
   (arm7_bop Add = 0b0100w: word4) /\
   (arm7_bop Sub = 0b0010w) /\
   (arm7_bop And = 0b0000w) /\
   (arm7_bop Or  = 0b1100w) /\
   (arm7_bop Xor = 0b0001w)`

val arm7_sh_def = Define`
   (arm7_sh Lsl = SRType_LSL) /\
   (arm7_sh Lsr = SRType_LSR) /\
   (arm7_sh Asr = SRType_ASR) /\
   (arm7_sh Ror = SRType_ROR)`

val arm7_cmp_def = Define`
   (arm7_cmp Less     = (2w, 0b1011w) : word2 # word4) /\
   (arm7_cmp Lower    = (2w, 0b0011w)) /\
   (arm7_cmp Equal    = (2w, 0b0000w)) /\
   (arm7_cmp Test     = (0w, 0b0000w)) /\
   (arm7_cmp NotLess  = (2w, 0b1010w)) /\
   (arm7_cmp NotLower = (2w, 0b0010w)) /\
   (arm7_cmp NotEqual = (2w, 0b0001w)) /\
   (arm7_cmp NotTest  = (0w, 0b0001w))`

val arm7_vfp_cmp_def = Define`
  arm7_vfp_cmp c n d1 d2 =
  arm7_encode
    [(AL, VFP (vcmp (T, n2w d1, SOME (n2w d2))));
     (AL, VFP (vmrs 15w)); (* move FPSCR flags to CPSR flags *)
     (AL, Data (Move (F, F, n2w n, 0w)));
     (c,  Data (Move (F, F, n2w n, 1w)));
     (VS, Data (Move (F, F, n2w n, 0w))) (* unordered (d1 or d2 is a NaN) *)
    ]`

val arm7_enc_def = Define`
   (arm7_enc (Inst Skip) =
      (* >= ARMv6T2 has dedicated NOP but using MOV r0, r0 instead. *)
      enc (Data (ShiftImmediate (F, F, 0w, 0w, SRType_LSL, 0)))) /\
   (arm7_enc (Inst (Const r i)) =
      case EncodeARMImmediate i of
         SOME imm12 => enc (Data (Move (F, F, n2w r, imm12)))
       | NONE =>
           (case EncodeARMImmediate (~i) of
               SOME imm12 => enc (Data (Move (F, T, n2w r, imm12)))
             | NONE =>
                 arm7_encode [(AL, Load (LoadLiteral (T, n2w r, 0w)));
                              (AL, Branch (BranchTarget (0w)))] ++
                 [(7 >< 0) i; (15 >< 8) i; (23 >< 16) i; (31 >< 24) i])) /\
   (arm7_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      enc (Data (Register (arm7_bop bop, F, n2w r1, n2w r2, n2w r3,
                           SRType_LSL, 0)))) /\
   (arm7_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
      if (bop = Xor) /\ (i = -1w) then
        enc (Data (ShiftImmediate (T, F, n2w r1, n2w r2, SRType_LSL, 0)))
      else
        case EncodeARMImmediate i of
           SOME imm12 =>
             enc (Data (ArithLogicImmediate
                           (arm7_bop bop, F, n2w r1, n2w r2, imm12)))
         | NONE => arm7_encode_fail) /\
   (arm7_enc (Inst (Arith (Shift sh r1 r2 n))) =
      enc (Data (ShiftImmediate (F, F, n2w r1, n2w r2, arm7_sh sh, n)))) /\
   (arm7_enc (Inst (Arith (Div _ _ _))) = arm7_encode_fail) /\
   (arm7_enc (Inst (Arith (LongMul r1 r2 r3 r4))) =
      enc (Multiply
             (MultiplyLong (F, F, F, n2w r1, n2w r2, n2w r3, n2w r4)))) /\
   (arm7_enc (Inst (Arith (LongDiv _ _ _ _ _))) = arm7_encode_fail) /\
   (arm7_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      arm7_encode
        [(AL, Data (TestCompareImmediate (2w, n2w r4, 0w)));
         (EQ, Data (TestCompareImmediate (3w, n2w r4, 0w)));
         (AL, Data (Register (5w, T, n2w r1, n2w r2, n2w r3, SRType_LSL, 0)));
         (CC, Data (Move (F, F, n2w r4, 0w)));
         (CS, Data (Move (F, F, n2w r4, 1w)))]) /\
   (arm7_enc (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
      arm7_encode
        [(AL, Data (Register (4w, T, n2w r1, n2w r2, n2w r3, SRType_LSL, 0)));
         (VC, Data (Move (F, F, n2w r4, 0w)));
         (VS, Data (Move (F, F, n2w r4, 1w)))]) /\
   (arm7_enc (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
      arm7_encode
        [(AL, Data (Register (2w, T, n2w r1, n2w r2, n2w r3, SRType_LSL, 0)));
         (VC, Data (Move (F, F, n2w r4, 0w)));
         (VS, Data (Move (F, F, n2w r4, 1w)))]) /\
   (arm7_enc (Inst (Mem Load r1 (Addr r2 a))) =
      let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
      enc (Load (LoadWord (add, T, F, n2w r1, n2w r2,
                           immediate_form1 imm12)))) /\
   (* (arm7_enc (Inst (Mem Load32 _ _)) = arm7_encode_fail) /\ *)
   (arm7_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
      let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
      enc (Load (LoadByte (T, add, T, F, n2w r1, n2w r2,
                           immediate_form1 imm12)))) /\
   (arm7_enc (Inst (Mem Store r1 (Addr r2 a))) =
      let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
      enc (Store (StoreWord (add, T, F, n2w r1, n2w r2,
                             immediate_form1 imm12)))) /\
   (* (arm7_enc (Inst (Mem Store32 r1 (Addr r2 a))) = arm7_encode_fail) /\ *)
   (arm7_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
      let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
      enc (Store (StoreByte (add, T, F, n2w r1, n2w r2,
                             immediate_form1 imm12)))) /\
   (arm7_enc (Inst (FP (FPLess n d1 d2))) = arm7_vfp_cmp LT n d1 d2) /\
   (arm7_enc (Inst (FP (FPLessEqual n d1 d2))) = arm7_vfp_cmp LE n d1 d2) /\
   (arm7_enc (Inst (FP (FPEqual n d1 d2))) = arm7_vfp_cmp EQ n d1 d2) /\
   (arm7_enc (Inst (FP (FPMov d1 d2))) =
      enc (VFP (vmov (F, n2w d1, n2w d2)))) /\
   (arm7_enc (Inst (FP (FPAbs d1 d2))) =
      enc (VFP (vabs (T, n2w d1, n2w d2)))) /\
   (arm7_enc (Inst (FP (FPNeg d1 d2))) =
      enc (VFP (vneg (T, n2w d1, n2w d2)))) /\
   (arm7_enc (Inst (FP (FPSqrt d1 d2))) =
      enc (VFP (vsqrt (T, n2w d1, n2w d2)))) /\
   (arm7_enc (Inst (FP (FPAdd d1 d2 d3))) =
      enc (VFP (vadd (T, n2w d1, n2w d2, n2w d3)))) /\
   (arm7_enc (Inst (FP (FPSub d1 d2 d3))) =
      enc (VFP (vsub (T, n2w d1, n2w d2, n2w d3)))) /\
   (arm7_enc (Inst (FP (FPMul d1 d2 d3))) =
      enc (VFP (vmul (T, n2w d1, n2w d2, n2w d3)))) /\
   (arm7_enc (Inst (FP (FPDiv d1 d2 d3))) =
      enc (VFP (vdiv (T, n2w d1, n2w d2, n2w d3)))) /\
   (arm7_enc (Inst (FP (FPFma d1 d2 d3))) =
      (* FIXME: T or F for flags?? *)
      enc (VFP (vfma_vfms (T, T, n2w d1, n2w d2, n2w d3)))) /\
   (arm7_enc (Inst (FP (FPMovToReg r1 r2 d))) =
      enc (VFP (vmov_double (T, n2w r1, n2w r2, n2w d)))) /\
   (arm7_enc (Inst (FP (FPMovFromReg d r1 r2))) =
      enc (VFP (vmov_double (F, n2w r1, n2w r2, n2w d)))) /\
   (arm7_enc (Inst (FP (FPToInt d1 d2))) =
      enc (VFP (vcvt_to_integer (T, F, F, n2w d1, n2w d2)))) /\
   (arm7_enc (Inst (FP (FPFromInt d1 d2))) =
      enc (VFP (vcvt_from_integer (T, F, n2w d1, n2w d2)))) /\
   (arm7_enc (Jump a) = enc (Branch (BranchTarget (a - 8w)))) /\
   (arm7_enc (JumpCmp cmp r1 (Reg r2) a) =
      let (opc, c) = arm7_cmp cmp in
      arm7_encode
        [(AL, Data (TestCompareRegister (opc, n2w r1, n2w r2, SRType_LSL, 0)));
         (c, Branch (BranchTarget (a - 12w)))]) /\
   (arm7_enc (JumpCmp cmp r (Imm i) a) =
      let (opc, c) = arm7_cmp cmp
      in
        case EncodeARMImmediate i of
           SOME imm12 =>
              arm7_encode
                [(AL, Data (TestCompareImmediate (opc, n2w r, imm12)));
                 (c, Branch (BranchTarget (a - 12w)))]
         | NONE => arm7_encode_fail) /\
   (arm7_enc (Call a) =
      enc (Branch (BranchLinkExchangeImmediate (InstrSet_ARM, a - 8w)))) /\
   (arm7_enc (JumpReg r) = enc (Branch (BranchExchange (n2w r)))) /\
   (arm7_enc (Loc r i) =
      let (opc, imm32) = if 8w <= i then (4w, i - 8w) else (2w, 8w - i) in
      let imm32b3 = (31 >< 24) imm32 : word8
      and imm32b2 = (23 >< 16) imm32 : word8
      and imm32b1 = (15 >< 8) imm32 : word8
      and imm32b0 = (7 >< 0) imm32 : word12
      in
        combin$C LIST_BIND
         (\x. enc (Data (ArithLogicImmediate (opc, F, n2w r, x))))
         (if imm32b3 <> 0w then
            [(15w, (4w : word4) @@ imm32b3);
             (n2w r, (8w : word4) @@ imm32b2);
             (n2w r, (12w : word4) @@ imm32b1);
             (n2w r, imm32b0)]
          else if imm32b2 <> 0w then
            [(15w, (8w : word4) @@ imm32b2);
             (n2w r, (12w : word4) @@ imm32b1);
             (n2w r, imm32b0)]
          else if imm32b1 <> 0w then
            [(15w, (12w : word4) @@ imm32b1);
             (n2w r, imm32b0)]
          else
            [(15w, imm32b0)]))`

(* --- Configuration for ARMv7 --- *)

val eval = rhs o concl o EVAL
val min12 = eval ``-(w2w (UINT_MAXw: word12)) : word32``
val max12 = eval ``w2w (UINT_MAXw: word12) : word32``
val min26 = eval ``sw2sw (INT_MINw: 26 word) : word32``
val max26 = eval ``sw2sw (INT_MAXw: 26 word) : word32``

val valid_immediate_def = Define`
   valid_immediate = IS_SOME o EncodeARMImmediate`

val arm7_config_def = Define`
   arm7_config =
   <| ISA := ARMv7
    ; encode := arm7_enc
    ; code_alignment := 2
    ; reg_count := 16
    ; fp_reg_count := 32
    ; avoid_regs := [13; 15]
    ; link_reg := SOME 14
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := \c i. valid_immediate i
    ; addr_offset := (^min12, ^max12)
    ; byte_offset := (^min12, ^max12)
    ; jump_offset := (^min26 + 8w, ^max26 + 8w)
    ; cjump_offset := (^min26 + 12w, ^max26 + 12w)
    ; loc_offset := (INT_MINw, INT_MAXw)
    |>`

val arm7_proj_def = Define`
   arm7_proj d s =
   (s.CPSR, s.FP.FPSCR, s.Architecture, s.Extensions, s.VFPExtension,
    s.exception, s.REG o R_mode s.CPSR.M, s.FP.REG, fun2set (s.MEM,d))`

val arm7_target_def = Define`
   arm7_target =
   <| next := arm7_next
    ; config := arm7_config
    ; get_pc := (\s. s.REG RName_PC)
    ; get_reg := (\s. s.REG o R_mode s.CPSR.M o n2w)
    ; get_fp_reg := (\s. s.FP.REG o n2w)
    ; get_byte := arm_state_MEM
    ; state_ok := arm7_ok
    ; proj := arm7_proj
    |>`

val (arm7_config, arm7_asm_ok) = asmLib.target_asm_rwts [] ``arm7_config``

val arm7_config = save_thm("arm7_config", arm7_config)
val arm7_asm_ok = save_thm("arm7_asm_ok", arm7_asm_ok)

val () = export_theory ()
