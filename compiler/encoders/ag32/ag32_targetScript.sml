open HolKernel Parse boolLib bossLib
open asmLib ag32Theory;

val () = new_theory "ag32_target"

(* --- Valid Ag32 states --- *)

val ag32_ok_def = Define`
  ag32_ok ms <=> aligned 2 ms.PC`

(* Possible initial states for Ag32, not placed in the L3 ISA because it was
   difficult to express this concisely there *)

val ag32_init_regs_def = Define `
 ag32_init_regs mem_start k = if k = 0n then mem_start else 0w`

val is_ag32_init_state_def = Define `
 is_ag32_init_state mem mem_start s <=>
  s.PC = mem_start /\
  s.MEM = mem /\
  s.R = ag32_init_regs mem_start o w2n /\
  s.io_events = []`;

(* --- Encode ASM instructions to Ag32 bytes. --- *)

val ag32_encode1_def = Define`
  ag32_encode1 i =
  let w = ag32$Encode i in
  [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list`

val ag32_encode_def = Define `ag32_encode = combin$C LIST_BIND ag32_encode1`

val ag32_bop_def = Define`
   (ag32_bop Add = fAdd) /\
   (ag32_bop Sub = fSub) /\
   (ag32_bop And = fAnd) /\
   (ag32_bop Or  = fOr) /\
   (ag32_bop Xor = fXor)`

val ag32_sh_def = Define`
   (ag32_sh Lsl = shiftLL) /\
   (ag32_sh Lsr = shiftLR) /\
   (ag32_sh Asr = shiftAR) /\
   (ag32_sh Ror = shiftRor)`

val ag32_cmp_def = Define`
   (ag32_cmp Equal = fEqual) /\
   (ag32_cmp Less = fLess) /\
   (ag32_cmp Lower = fLower) /\
   (ag32_cmp Test = fAnd) /\
   (ag32_cmp NotEqual = fEqual) /\
   (ag32_cmp NotLess = fLess) /\
   (ag32_cmp NotLower = fLower) /\
   (ag32_cmp NotTest = fAnd)`

val ag32_constant_def = Define`
  ag32_constant (r, v : word32, jmp) =
  if -0x7FFFFFw <= v /\ v < 0x7FFFFFw then
   let v = if jmp then v - 4w else v;
       (b, n) = if 0w <= v then (F, v) else (T, -v) in
    [LoadConstant (r, b, w2w n)]
  else
   let v = if jmp then v - 8w else v in
    [LoadConstant (r, F, (22 >< 0) v); LoadUpperConstant (r, (31 >< 23) v)]`;

val () = Parse.temp_overload_on ("enc", ``ag32_encode1``)
val () = Parse.temp_overload_on ("temp_reg", ``63w : word6``)

val ag32_enc_def = Define`
   (ag32_enc (Inst Skip) =
      enc (Normal (fOr, 0w, Reg 0w, Imm 0w))) /\
   (ag32_enc (Inst (Const r i)) =
      ag32_encode (ag32_constant (n2w r, i, F))) /\
   (ag32_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      enc (Normal (ag32_bop bop, n2w r1, Reg (n2w r2), Reg (n2w r3)))) /\
   (ag32_enc (Inst (Arith (Binop bop r1 r2 (asm$Imm i)))) =
    if -32w <= i /\ i < 32w then
      enc (Normal (ag32_bop bop, n2w r1, Reg (n2w r2), Imm (w2w i)))
    else
      ag32_encode
        (ag32_constant (temp_reg, i, F) ++
        [Normal (ag32_bop bop, n2w r1, Reg (n2w r2), Reg temp_reg)])) /\
   (ag32_enc (Inst (Arith (asm$Shift sh r1 r2 n))) =
      enc (Shift (ag32_sh sh, n2w r1, Reg (n2w r2), Imm (n2w n)))) /\
   (ag32_enc (Inst (Arith (Div _ _ _))) = enc ReservedInstr) /\
   (ag32_enc (Inst (Arith (LongMul r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fMulHU, n2w r1, Reg (n2w r3), Reg (n2w r4));
         Normal (fMul, n2w r2, Reg (n2w r3), Reg (n2w r4))]) /\
   (ag32_enc (Inst (Arith (LongDiv _ _ _ _ _))) = enc ReservedInstr) /\
   (ag32_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fAdd, temp_reg, Imm (-1w), Reg (n2w r4));
         Normal (fAddWithCarry, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fCarry, n2w r4, Imm 0w, Imm 0w)]) /\
   (ag32_enc (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fOverflow, n2w r4, Imm 0w, Imm 0w)]) /\
   (ag32_enc (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
      ag32_encode
        [Normal (fSub, n2w r1, Reg (n2w r2), Reg (n2w r3));
         Normal (fOverflow, n2w r4, Imm 0w, Imm 0w)]) /\
   (ag32_enc (Inst (Mem Load r1 (Addr r2 a))) =
    if -32w <= a /\ a < 32w then
      ag32_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Imm (w2w a));
         LoadMEM (n2w r1, Reg (n2w r1))]
    else
      ag32_encode
        (ag32_constant (temp_reg, a, F) ++
         [Normal (fAdd, n2w r1, Reg (n2w r2), Reg temp_reg);
         LoadMEM (n2w r1, Reg (n2w r1))])) /\
   (ag32_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
    if -32w <= a /\ a < 32w then
      ag32_encode
        [Normal (fAdd, n2w r1, Reg (n2w r2), Imm (w2w a));
         LoadMEMByte (n2w r1, Reg (n2w r1))]
    else
      ag32_encode
        (ag32_constant (temp_reg, a, F) ++
         [Normal (fAdd, n2w r1, Reg (n2w r2), Reg temp_reg);
         LoadMEMByte (n2w r1, Reg (n2w r1))])) /\
   (ag32_enc (Inst (Mem Store r1 (Addr r2 a))) =
    if -32w <= a /\ a < 32w then
      ag32_encode
        [Normal (fAdd, temp_reg, Reg (n2w r2), Imm (w2w a));
         StoreMEM (Reg (n2w r1), Reg temp_reg)]
    else
      ag32_encode
        (ag32_constant (temp_reg, a, F) ++
         [Normal (fAdd, temp_reg, Reg (n2w r2), Reg temp_reg);
         StoreMEM (Reg (n2w r1), Reg temp_reg)])) /\
   (ag32_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
    if -32w <= a /\ a < 32w then
      ag32_encode
        [Normal (fAdd, temp_reg, Reg (n2w r2), Imm (w2w a));
         StoreMEMByte (Reg (n2w r1), Reg temp_reg)]
    else
      ag32_encode
        (ag32_constant (temp_reg, a, F) ++
         [Normal (fAdd, temp_reg, Reg (n2w r2), Reg temp_reg);
         StoreMEMByte (Reg (n2w r1), Reg temp_reg)])) /\
   (ag32_enc (Inst (FP _)) = enc ReservedInstr) /\
   (ag32_enc (Jump a) =
      if -32w <= a /\ a < 32w then
        enc (Jump (fAdd, temp_reg, Imm (w2w a)))
      else
        ag32_encode
          (ag32_constant (temp_reg, a, T) ++
           [Jump (fAdd, temp_reg, Reg temp_reg)])) /\
   (ag32_enc (Call a) =
      if -32w <= a /\ a < 32w then
        enc (Jump (fAdd, 0w, Imm (w2w a)))
      else
        ag32_encode
          (ag32_constant (temp_reg, a, T) ++
           [Jump (fAdd, 0w, Reg temp_reg)])) /\
   (ag32_enc (JumpReg r) =
      enc (Jump (fSnd, temp_reg, Reg (n2w r)))) /\
   (ag32_enc (Loc r i) =
      let j = i - 4w in
      ag32_encode
        (Jump (fAdd, n2w r, Imm 4w) ::
         (if -32w <= j /\ j < 32w then
            [Normal (fAdd, n2w r, Reg (n2w r), Imm (w2w j))]
          else
            (ag32_constant (temp_reg, j, F) ++
             [Normal (fAdd, n2w r, Reg (n2w r), Reg temp_reg)])))) /\
   (* TODO: a can sometimes fit as an imm here! *)
   (ag32_enc (JumpCmp cmp r1 (Reg r2) a) =
      let arg = (ag32_cmp cmp, Reg temp_reg, Reg (n2w r1), Reg (n2w r2)) in
      ag32_encode
        (ag32_constant (temp_reg, a, T) ++
         [if cmp IN {Test; NotEqual; NotLess; NotLower} then
           JumpIfZero arg
         else
           JumpIfNotZero arg])) /\
   (* TODO: a can sometimes fit as an imm here! *)
   (ag32_enc (JumpCmp cmp r (asm$Imm i) a) =
      let arg = (ag32_cmp cmp, Reg temp_reg, Reg (n2w r), Imm (w2w i)) in
      ag32_encode
        (ag32_constant (temp_reg, a, T) ++
         [if cmp IN {Test; NotEqual; NotLess; NotLower} then
           JumpIfZero arg
         else
           JumpIfNotZero arg]))`

(* --- Configuration for Ag32 --- *)

(* Note that some bounds here might not be tight *)
val ag32_config_def = Define`
   ag32_config =
   <| ISA := Ag32
    ; encode := ag32_enc
    ; code_alignment := 2
    ; reg_count := 64
    ; fp_reg_count := 0
    ; avoid_regs := [63]
    ; link_reg := SOME 0
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := \i n. if ISL i then
                           -0x7FFFFFw <= n /\ n < 0x7FFFFFw
                         else
                           -32w <= n /\ n < 32w
    ; addr_offset := (-0x7FFFFFw, 0x7FFFFFw)
    ; byte_offset := (-32w, 31w)
    ; jump_offset := (-0x7FFFFFFFw + 4w, 0x7FFFFFFFw + 4w)
    ; cjump_offset := (-0x7FFFFFFFw + 4w, 0x7FFFFFFFw + 4w)
    ; loc_offset := (-0x7FFFFFFFw + 4w, 0x7FFFFFFFw + 4w)
    |>`

val ag32_proj_def = Define`
   ag32_proj d s =
   (s.PC, s.R, fun2set (s.MEM, d), s.CarryFlag, s.OverflowFlag)`

val ag32_target_def = Define`
   ag32_target =
   <| next := ag32$Next
    ; config := ag32_config
    ; get_pc := ag32_state_PC
    ; get_reg := (\s. s.R o n2w)
    ; get_byte := ag32_state_MEM
    ; state_ok := ag32_ok
    ; proj := ag32_proj
    |>`

val (ag32_config, ag32_asm_ok) = asmLib.target_asm_rwts [] ``ag32_config``

val ag32_config = save_thm("ag32_config", ag32_config)
val ag32_asm_ok = save_thm("ag32_asm_ok", ag32_asm_ok)

val () = export_theory ()
