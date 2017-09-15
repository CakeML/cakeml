open HolKernel Parse boolLib bossLib
open asmLib tinyTheory;

val () = new_theory "tiny_target"

(* --- Valid Tiny states --- *)

val tiny_ok_def = Define`
  tiny_ok ms <=> ~ms.Reset /\ (ms.lastMemAddr = UINT_MAXw) /\ aligned 2 ms.PC`

(* --- Encode ASM instructions to Tiny bytes. --- *)

val tiny_encode1_def = Define`
  tiny_encode1 i =
  let w = tiny$Encode i in
  [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list`

val tiny_encode_def = Define `tiny_encode = combin$C LIST_BIND tiny_encode1`

val tiny_bop_def = Define`
   (tiny_bop Add = fAdd) /\
   (tiny_bop Sub = fSub) /\
   (tiny_bop And = fAnd) /\
   (tiny_bop Or  = fOr) /\
   (tiny_bop Xor = fXor)`

val tiny_sh_def = Define`
   (tiny_sh Lsl = shiftLL) /\
   (tiny_sh Lsr = shiftLR) /\
   (tiny_sh Asr = shiftAR) /\
   (tiny_sh Ror = shiftRor)`

val tiny_cmp_def = Define`
   (tiny_cmp Equal = fEqual) /\
   (tiny_cmp Less = fLess) /\
   (tiny_cmp Lower = fLower) /\
   (tiny_cmp Test = fAnd) /\
   (tiny_cmp NotEqual = fEqual) /\
   (tiny_cmp NotLess = fLess) /\
   (tiny_cmp NotLower = fLower) /\
   (tiny_cmp NotTest = fAnd)`

val tiny_constant_def = Define`
  tiny_constant (r, v : word32) =
  let (b, n) = if 0w <= v then (F, v) else (T, -v) in
  LoadConstant (r, b, w2w n)`

val () = Parse.temp_overload_on ("enc", ``tiny_encode1``)
val () = Parse.temp_overload_on ("temp_reg", ``63w : word6``)

val tiny_enc_def = Define`
   (tiny_enc (Inst Skip) =
      enc (Normal (fOr, 0w, Reg 0w, Imm 0w))) /\
   (tiny_enc (Inst (Const r i)) =
      if word_abs i <+ 0x800000w : word32 then
        enc (tiny_constant (n2w r, i))
      else
        tiny_encode
          [LoadConstant (n2w r, F, (22 >< 0) i);
           LoadUpperConstant (n2w r, (31 >< 23) i)]) /\
   (tiny_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      enc (Normal (tiny_bop bop, n2w r1, Reg (n2w r2), Reg (n2w r3)))) /\
   (tiny_enc (Inst (Arith (Binop bop r1 r2 (asm$Imm i)))) =
      enc (Normal (tiny_bop bop, n2w r1, Reg (n2w r2), Imm (w2w i)))) /\
   (tiny_enc (Inst (Arith (asm$Shift sh r1 r2 n))) =
      enc (Shift (tiny_sh sh, n2w r1, Reg (n2w r2), Imm (n2w n)))) /\
   (tiny_enc (Inst (Arith (Div _ _ _))) = enc ReservedInstr) /\
   (tiny_enc (Inst (Arith (LongMul r1 r2 r3 r4))) =
      tiny_encode
        [Normal (fMulHU, n2w r1, Reg (n2w r3), Reg (n2w r4));
         Normal (fMul, n2w r2, Reg (n2w r3), Reg (n2w r4))]) /\
   (tiny_enc (Inst (Arith (LongDiv _ _ _ _ _))) = enc ReservedInstr) /\
   (tiny_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      tiny_encode
        [Normal (fAdd, temp_reg, Imm (-1w), Reg (n2w r4));
         Normal (fAddWithCarry, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fCarry, n2w r4, Imm 0w, Imm 0w)]) /\
   (tiny_enc (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
      tiny_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fOverflow, n2w r4, Imm 0w, Imm 0w)]) /\
   (tiny_enc (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
      tiny_encode
        [Normal (fSub, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fOverflow, n2w r4, Imm 0w, Imm 0w)]) /\
   (tiny_enc (Inst (Mem Load r1 (Addr r2 a))) =
      tiny_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Imm (w2w a));
         LoadMEM (n2w r1, Reg (n2w r1))]) /\
   (tiny_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
      tiny_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Imm (w2w a));
         LoadMEMByte (n2w r1, Reg (n2w r1))]) /\
   (tiny_enc (Inst (Mem Store r1 (Addr r2 a))) =
      tiny_encode
        [Normal (fAdd, temp_reg, Reg (n2w r2), Imm (w2w a));
         StoreMEM (fSnd, temp_reg, Reg (n2w r1), Reg temp_reg)]) /\
   (tiny_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
      tiny_encode
        [Normal (fAdd, temp_reg, Reg (n2w r2), Imm (w2w a));
         StoreMEMByte (fSnd, temp_reg, Reg (n2w r1), Reg temp_reg)]) /\
   (tiny_enc (Inst (FP _)) = enc ReservedInstr) /\
   (tiny_enc (Jump a) =
      if -32w <= a /\ a < 32w then
        enc (Jump (fAdd, temp_reg, Imm (w2w a)))
      else
        tiny_encode
          [tiny_constant (temp_reg, a - 4w);
           Jump (fAdd, temp_reg, Reg temp_reg)]) /\
   (tiny_enc (Call a) =
      if -32w <= a /\ a < 32w then
        enc (Jump (fAdd, 62w, Imm (w2w a)))
      else
        tiny_encode
          [tiny_constant (temp_reg, a - 4w);
           Jump (fAdd, 62w, Reg temp_reg)]) /\
   (tiny_enc (JumpReg r) =
      enc (Jump (fSnd, temp_reg, Reg (n2w r)))) /\
   (tiny_enc (Loc r i) =
      let j = i - 4w in
      tiny_encode
        (Jump (fAdd, n2w r, Imm 4w) ::
         (if -32w <= j /\ j < 32w then
            [Normal (fAdd, n2w r, Reg (n2w r), Imm (w2w j))]
          else
            [tiny_constant (temp_reg, j);
             Normal (fAdd, n2w r, Reg (n2w r), Reg temp_reg)]))) /\
   (tiny_enc (JumpCmp cmp r1 (Reg r2) a) =
      let arg = (tiny_cmp cmp, Reg temp_reg, Reg (n2w r1), Reg (n2w r2)) in
      tiny_encode
        [tiny_constant (temp_reg, a - 4w);
         if cmp IN {Test; NotEqual; NotLess; NotLower} then
           JumpIfZero arg
         else
           JumpIfNotZero arg]) /\
   (tiny_enc (JumpCmp cmp r (asm$Imm i) a) =
      let arg = (tiny_cmp cmp, Reg temp_reg, Reg (n2w r), Imm (w2w i)) in
      tiny_encode
        [tiny_constant (temp_reg, a - 4w);
         if cmp IN {Test; NotEqual; NotLess; NotLower} then
           JumpIfZero arg
         else
           JumpIfNotZero arg])`

(* --- Configuration for Tiny --- *)

val tiny_config_def = Define`
   tiny_config =
   <| ISA := Tiny
    ; encode := tiny_enc
    ; code_alignment := 2
    ; reg_count := 64
    ; fp_reg_count := 0
    ; avoid_regs := [63]
    ; link_reg := SOME 62
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := \_ i. -32w <= i /\ i < 32w
    ; addr_offset := (-32w, 31w)
    ; byte_offset := (-32w, 31w)
    ; jump_offset := (-0x7FFFFFw + 4w, 0x7FFFFFw + 4w)
    ; cjump_offset := (-0x7FFFFFw + 4w, 0x7FFFFFw + 4w)
    ; loc_offset := (-0x7FFFFFw + 4w, 0x7FFFFFw + 4w)
    |>`

val tiny_proj_def = Define`
   tiny_proj d s =
   (s.PC, s.R, fun2set (s.MEM, d), s.CarryFlag, s.OverflowFlag, s.Reset,
    s.lastMemAddr)`

val tiny_target_def = Define`
   tiny_target =
   <| next := tiny$Next
    ; config := tiny_config
    ; get_pc := tiny_state_PC
    ; get_reg := (\s. s.R o n2w)
    ; get_byte := tiny_state_MEM
    ; state_ok := tiny_ok
    ; proj := tiny_proj
    |>`

val (tiny_config, tiny_asm_ok) = asmLib.target_asm_rwts [] ``tiny_config``

val tiny_config = save_thm("tiny_config", tiny_config)
val tiny_asm_ok = save_thm("tiny_asm_ok", tiny_asm_ok)

val () = export_theory ()
