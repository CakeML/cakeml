open HolKernel Parse boolLib bossLib
open asmLib riscv_stepLib;

val () = new_theory "riscv_target"

val () = wordsLib.guess_lengths()

val riscv_next_def = Define `riscv_next s = THE (NextRISCV s)`

(* --- Relate ASM and RISC-V states --- *)

(* We assume virtual memory is turned off and a 64-bit architecture (RV64I) *)
val riscv_ok_def = Define`
   riscv_ok ms =
   ((ms.c_MCSR ms.procID).mstatus.VM = 0w) /\
   ((ms.c_MCSR ms.procID).mcpuid.ArchBase = 2w) /\
   (ms.c_NextFetch ms.procID = NONE) /\
   (ms.exception = NoException) /\ aligned 2 (ms.c_PC ms.procID)`

val riscv_asm_state_def = Define`
   riscv_asm_state s ms =
   riscv_ok ms /\
   (!i. 1 < i /\ i < 32 ==> (s.regs i = ms.c_gpr ms.procID (n2w i))) /\
   (fun2set (s.mem, s.mem_domain) = fun2set (ms.MEM8, s.mem_domain)) /\
   (s.pc = ms.c_PC ms.procID)`

(* --- Encode ASM instructions to RISC-V bytes. --- *)

val riscv_encode_def = Define`
   riscv_encode i =
   let w = riscv$Encode i in
      [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list`

val riscv_bop_r_def = Define`
   (riscv_bop_r Add = ADD) /\
   (riscv_bop_r Sub = SUB) /\
   (riscv_bop_r And = AND) /\
   (riscv_bop_r Or  = OR) /\
   (riscv_bop_r Xor = XOR)`

val riscv_bop_i_def = Define`
   (riscv_bop_i Add = ADDI) /\
   (riscv_bop_i And = ANDI) /\
   (riscv_bop_i Or  = ORI) /\
   (riscv_bop_i Xor = XORI)`

val riscv_sh_def = Define`
   (riscv_sh Lsl = SLLI) /\
   (riscv_sh Lsr = SRLI) /\
   (riscv_sh Asr = SRAI)`

val riscv_memop_def = Define`
   (riscv_memop Load    = INL LD) /\
   (riscv_memop Load32  = INL LWU) /\
   (riscv_memop Load8   = INL LBU) /\
   (riscv_memop Store   = INR SD) /\
   (riscv_memop Store32 = INR SW) /\
   (riscv_memop Store8  = INR SB)`

val riscv_const32_def = Define`
  riscv_const32 r (i: word32) =
  if i ' 11 then
    riscv_encode (ArithI (LUI (r, ~((31 >< 12) i)))) ++
    riscv_encode (ArithI (XORI (r, r, (11 >< 0) i)))
  else
    riscv_encode (ArithI (LUI (r, (31 >< 12) i))) ++
    riscv_encode (ArithI (ADDI (r, r, (11 >< 0) i)))`

val riscv_enc_def = Define`
   (riscv_enc (Inst Skip) = riscv_encode (ArithI (ADDI (0w, 0w, 0w)))) /\
   (riscv_enc (Inst (Const r (i: word64))) =
      let imm12 = (11 >< 0) i in
      if i = sw2sw imm12 then
        riscv_encode (ArithI (ORI (n2w r, 0w, imm12)))
      else if ((63 >< 32) i = 0w: word32) /\ ~i ' 31 \/
              ((63 >< 32) i = -1w: word32) /\ i ' 31 then
        riscv_const32 (n2w r) ((31 >< 0) i)
      else if i ' 31 then
        riscv_const32 1w ((31 >< 0) i) ++
        riscv_const32 (n2w r) (~((63 >< 32) i)) ++
        riscv_encode (Shift (SLLI (n2w r, n2w r, 32w))) ++
        riscv_encode (ArithR (XOR (n2w r, n2w r, 1w)))
      else
        riscv_const32 1w ((31 >< 0) i) ++
        riscv_const32 (n2w r) ((63 >< 32) i) ++
        riscv_encode (Shift (SLLI (n2w r, n2w r, 32w))) ++
        riscv_encode (ArithR (OR (n2w r, n2w r, 1w)))) /\
   (riscv_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
     riscv_encode (ArithR (riscv_bop_r bop (n2w r1, n2w r2, n2w r3)))) /\
   (riscv_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
     riscv_encode (ArithI (riscv_bop_i bop (n2w r1, n2w r2, w2w i)))) /\
   (riscv_enc (Inst (Arith (Shift sh r1 r2 n))) =
     riscv_encode (Shift (riscv_sh sh (n2w r1, n2w r2, n2w n)))) /\
   (riscv_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
     riscv_encode (ArithR (SLTU (1w, 0w, n2w r4))) ++
     riscv_encode (ArithR (ADD (n2w r1, n2w r2, n2w r3))) ++
     riscv_encode (ArithR (SLTU (n2w r4, n2w r1, n2w r3))) ++
     riscv_encode (ArithR (ADD (n2w r1, n2w r1, 1w))) ++
     riscv_encode (ArithR (SLTU (1w, n2w r1, 1w))) ++
     riscv_encode (ArithR (OR (n2w r4, n2w r4, 1w)))) /\
   (riscv_enc (Inst (Mem mop r1 (Addr r2 a))) =
      case riscv_memop mop of
         INL f => riscv_encode (Load (f (n2w r1, n2w r2, w2w a)))
       | INR f => riscv_encode (Store (f (n2w r2, n2w r1, w2w a)))) /\
   (riscv_enc (Jump a) = riscv_encode (Branch (JAL (0w, w2w (a >>> 1))))) /\
   (riscv_enc (JumpCmp c r1 (Reg r2) a) =
      let off = w2w (a >>> 1) in
      case c of
         Equal => riscv_encode (Branch (BEQ (n2w r1, n2w r2, off)))
       | Less  => riscv_encode (Branch (BLT (n2w r1, n2w r2, off)))
       | Lower => riscv_encode (Branch (BLTU (n2w r1, n2w r2, off)))
       | Test  => riscv_encode (ArithR (AND (1w, n2w r1, n2w r2))) ++
                  riscv_encode (Branch (BEQ (1w, 0w, off - 2w)))
       | NotEqual => riscv_encode (Branch (BNE (n2w r1, n2w r2, off)))
       | NotLess  => riscv_encode (Branch (BGE (n2w r1, n2w r2, off)))
       | NotLower => riscv_encode (Branch (BGEU (n2w r1, n2w r2, off)))
       | NotTest  => riscv_encode (ArithR (AND (1w, n2w r1, n2w r2))) ++
                     riscv_encode (Branch (BNE (1w, 0w, off - 2w)))) /\
   (riscv_enc (JumpCmp c r (Imm i) a) =
      let off = w2w (a >>> 1) - 2w in
      case c of
         Equal => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                  riscv_encode (Branch (BEQ (n2w r, 1w, off)))
       | Less  => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                  riscv_encode (Branch (BLT (n2w r, 1w, off)))
       | Lower => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                  riscv_encode (Branch (BLTU (n2w r, 1w, off)))
       | Test  => riscv_encode (ArithI (ANDI (1w, n2w r, w2w i))) ++
                  riscv_encode (Branch (BEQ (1w, 0w, off)))
       | NotEqual => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                     riscv_encode (Branch (BNE (n2w r, 1w, off)))
       | NotLess  => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                     riscv_encode (Branch (BGE (n2w r, 1w, off)))
       | NotLower => riscv_encode (ArithI (ORI (1w, 0w, w2w i))) ++
                     riscv_encode (Branch (BGEU (n2w r, 1w, off)))
       | NotTest  => riscv_encode (ArithI (ANDI (1w, n2w r, w2w i))) ++
                     riscv_encode (Branch (BNE (1w, 0w, off)))) /\
   (riscv_enc (Call a) = riscv_encode (Branch (JAL (31w, w2w (a >>> 1))))) /\
   (riscv_enc (JumpReg r) = riscv_encode (Branch (JALR (0w, n2w r, 0w)))) /\
   (riscv_enc (Loc r i) =
      let imm12 = (11 >< 0) i in
      riscv_encode (ArithI (AUIPC (n2w r, (31 >< 12) (i - sw2sw imm12)))) ++
      riscv_encode (ArithI (ADDI (n2w r, n2w r, imm12))))`

val fetch_decode_def = Define`
   fetch_decode (b0 :: b1 :: b2 :: b3 :: (rest: word8 list)) =
   (Decode (b3 @@ b2 @@ b1 @@ b0), rest)`

val riscv_dec_const32_def = Define`
  riscv_dec_const32 r1 (imm20: 20 word) l =
  case fetch_decode l of
     (ArithI (XORI (r2, r3, imm12)), rest) =>
        if (r1 = r2) /\ (r2 = r3) then
           (Inst (Const (w2n r1) (sw2sw imm20 << 12 ?? sw2sw imm12)), rest)
        else (ARB, rest)
   | (ArithI (ADDI (r2, r3, imm12)), rest) =>
        if (r1 = r2) /\ (r2 = r3) then
           (Inst (Const (w2n r1) (sw2sw imm20 << 12 + sw2sw imm12)), rest)
        else (ARB, rest)
   | _ => (ARB : 64 asm, l)`

val riscv_dec_def = Lib.with_flag (Globals.priming, SOME "_") Define`
   riscv_dec l =
   case fetch_decode l of
    (* Skip *)
      (ArithI (ADDI (0w, 0w, 0w)), _) => Inst Skip
    (* JumpCmp *)
    | (Branch (BEQ (r1, r2, a)), _) =>
       JumpCmp Equal (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (Branch (BLT (r1, r2, a)), _) =>
       JumpCmp Less (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (Branch (BLTU (r1, r2, a)), _) =>
       JumpCmp Lower (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (ArithR (AND (1w, r1, r2)), rest) =>
       (case FST (fetch_decode rest) of
           Branch (BEQ (1w, 0w, a)) =>
             JumpCmp Test (w2n r1) (Reg (w2n r2)) (sw2sw (a + 2w) << 1)
         | Branch (BNE (1w, 0w, a)) =>
             JumpCmp NotTest (w2n r1) (Reg (w2n r2)) (sw2sw (a + 2w) << 1)
         | _ => ARB)
    | (Branch (BNE (r1, r2, a)), _) =>
       JumpCmp NotEqual (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (Branch (BGE (r1, r2, a)), _) =>
       JumpCmp NotLess (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (Branch (BGEU (r1, r2, a)), _) =>
       JumpCmp NotLower (w2n r1) (Reg (w2n r2)) (sw2sw a << 1)
    | (ArithI (ORI (1w, 0w, i)), rest) =>
       (case FST (fetch_decode rest) of
           Branch (BEQ (r, 1w, a)) =>
             JumpCmp Equal (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BLT (r, 1w, a)) =>
             JumpCmp Less (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BLTU (r, 1w, a)) =>
             JumpCmp Lower (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BNE (r, 1w, a)) =>
             JumpCmp NotEqual (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BGE (r, 1w, a)) =>
             JumpCmp NotLess (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BGEU (r, 1w, a)) =>
             JumpCmp NotLower (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | _ => ARB)
    | (ArithI (ANDI (1w, r, i)), rest) =>
       (case FST (fetch_decode rest) of
           Branch (BEQ (1w, 0w, a)) =>
             JumpCmp Test (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | Branch (BNE (1w, 0w, a)) =>
             JumpCmp NotTest (w2n r) (Imm (sw2sw i)) (sw2sw (a + 2w) << 1)
         | _ => ARB)
    (* Const *)
    | (ArithI (ORI (r, 0w, imm12)), _) =>
       Inst (Const (w2n r) (sw2sw imm12 : word64))
    | (ArithI (LUI (r, imm20)), rest) =>
       (case riscv_dec_const32 r imm20 rest of
           (Inst (Const 1 imm32), rest2) =>
              (case fetch_decode rest2 of
                  (ArithI (LUI (r1, imm20b)), rest3) =>
                    (case riscv_dec_const32 r1 imm20b rest3 of
                       (Inst (Const rn imm32b), rest4) =>
                          (case fetch_decode rest4 of
                              (Shift (SLLI (r2, r3, 32w)), rest5) =>
                                 (case FST (fetch_decode rest5) of
                                     ArithR (XOR (r4, r5, 1w)) =>
                                       if (r1 = r2) /\ (r2 = r3) /\ (r3 = r4) /\
                                          (r4 = r5) then
                                         Inst (Const rn (imm32b << 32 ?? imm32))
                                       else ARB
                                   | ArithR (OR (r4, r5, 1w)) =>
                                       if (r1 = r2) /\ (r2 = r3) /\ (r3 = r4) /\
                                          (r4 = r5) then
                                         Inst (Const rn (imm32b << 32 || imm32))
                                       else ARB
                                   | _ => ARB)
                            | _ => ARB)
                     | _ => ARB)
                | _ => ARB)
         | (i, _) => i)
    (* Binop reg *)
    | (ArithR (ADD (r1, r2, r3)), _) =>
       Inst (Arith (Binop Add (w2n r1) (w2n r2) (Reg (w2n r3))))
    | (ArithR (SUB (r1, r2, r3)), _) =>
       Inst (Arith (Binop Sub (w2n r1) (w2n r2) (Reg (w2n r3))))
    | (ArithR (AND (r1, r2, r3)), _) =>
       Inst (Arith (Binop And (w2n r1) (w2n r2) (Reg (w2n r3))))
    | (ArithR (OR (r1, r2, r3)), _) =>
       Inst (Arith (Binop Or (w2n r1) (w2n r2) (Reg (w2n r3))))
    | (ArithR (XOR (r1, r2, r3)), _) =>
       Inst (Arith (Binop Xor (w2n r1) (w2n r2) (Reg (w2n r3))))
    (* Binop imm *)
    | (ArithI (ADDI (r1, r2, imm12)), _) =>
       Inst (Arith (Binop Add (w2n r1) (w2n r2) (Imm (sw2sw imm12))))
    | (ArithI (ANDI (r1, r2, imm12)), _) =>
       Inst (Arith (Binop And (w2n r1) (w2n r2) (Imm (sw2sw imm12))))
    | (ArithI (ORI (r1, r2, imm12)), _) =>
       Inst (Arith (Binop Or (w2n r1) (w2n r2) (Imm (sw2sw imm12))))
    | (ArithI (XORI (r1, r2, imm12)), _) =>
       Inst (Arith (Binop Xor (w2n r1) (w2n r2) (Imm (sw2sw imm12))))
    (* Shift *)
    | (Shift (SLLI (r1, r2, n)), _) =>
       Inst (Arith (Shift Lsl (w2n r1) (w2n r2) (w2n n)))
    | (Shift (SRLI (r1, r2, n)), _) =>
       Inst (Arith (Shift Lsr (w2n r1) (w2n r2) (w2n n)))
    | (Shift (SRAI (r1, r2, n)), _) =>
       Inst (Arith (Shift Asr (w2n r1) (w2n r2) (w2n n)))
    (* AddCarry *)
    | (ArithR (SLTU (1w, 0w, r1)), rest) =>
       (case fetch_decode rest of
           (ArithR (ADD (r2, r3, r4)), rest2) =>
              (case fetch_decode rest2 of
                  (ArithR (SLTU (r5, r6, r7)), rest3) =>
                    (case fetch_decode rest3 of
                       (ArithR (ADD (r8, r9, 1w)), rest4) =>
                          (case fetch_decode rest4 of
                              (ArithR (SLTU (1w, r10, 1w)), rest5) =>
                                 (case FST (fetch_decode rest5) of
                                     ArithR (OR (r11, r12, 1w)) =>
                                       if (r1 = r5) /\ (r5 = r11) /\
                                          (r11 = r12) /\
                                          (r2 = r6) /\ (r6 = r8) /\ (r8 = r9) /\
                                          (r9 = r10) /\ (r4 = r7) then
                                         Inst (Arith (AddCarry
                                           (w2n r2) (w2n r3) (w2n r4) (w2n r1)))
                                       else ARB
                                   | _ => ARB)
                            | _ => ARB)
                     | _ => ARB)
                | _ => ARB)
         |  _ => ARB)
    (* Load *)
    | (Load (LD (r1, r2, a)), _) =>
       Inst (Mem Load (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Load (LWU (r1, r2, a)), _) =>
       Inst (Mem Load32 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Load (LBU (r1, r2, a)), _) =>
       Inst (Mem Load8 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    (* Store *)
    | (Store (SD (r1, r2, a)), _) =>
       Inst (Mem Store (w2n r2) (Addr (w2n r1) (sw2sw a)))
    | (Store (SW (r1, r2, a)), _) =>
       Inst (Mem Store32 (w2n r2) (Addr (w2n r1) (sw2sw a)))
    | (Store (SB (r1, r2, a)), _) =>
       Inst (Mem Store8 (w2n r2) (Addr (w2n r1) (sw2sw a)))
    (* Jump *)
    | (Branch (JAL (0w, a)), _) => Jump (sw2sw a << 1)
    (* Call *)
    | (Branch (JAL (31w, a)), _) => Call (sw2sw a << 1)
    (* JumpReg *)
    | (Branch (JALR (0w, r, 0w)), _) => JumpReg (w2n r)
    (* Loc *)
    | (ArithI (AUIPC (r1, imm20)), rest) =>
        (case FST (fetch_decode rest) of
            ArithI (ADDI (r2, r3, imm12)) =>
              if (r1 = r2) /\ (r2 = r3) then
                Loc (w2n r1) (sw2sw imm20 << 12 + sw2sw imm12) else ARB
          | _ => ARB)
    | _ => ARB`

(* --- Configuration for RISC-V --- *)

val eval = rhs o concl o EVAL
val min12 = eval ``sw2sw (INT_MINw: word12) : word64``
val max12 = eval ``sw2sw (INT_MAXw: word12) : word64``
val min13 = eval ``sw2sw (INT_MINw: 13 word) : word64``
val max13 = eval ``sw2sw (INT_MAXw: 13 word) : word64``
val min21 = eval ``sw2sw (INT_MINw: 21 word) : word64``
val max21 = eval ``sw2sw (INT_MAXw: 21 word) : word64``
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``

val riscv_config_def = Define`
   riscv_config =
   <| ISA := RISC_V
    ; encode := riscv_enc
    ; reg_count := 32
    ; avoid_regs := [0; 1]
    ; link_reg := SOME 31
    ; has_mem_32 := T
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := (\b i. b <> INL Sub /\ ^min12 <= i /\ i <= ^max12)
    ; addr_offset_min := ^min12
    ; addr_offset_max := ^max12
    ; jump_offset_min := ^min21
    ; jump_offset_max := ^max21
    ; cjump_offset_min := ^min13 + 4w
    ; cjump_offset_max := ^max13
    ; loc_offset_min := ^min32
    ; loc_offset_max := 0x7FFFF7FFw
    ; code_alignment := 2
    |>`

val riscv_proj_def = Define`
   riscv_proj d s =
   ((s.c_MCSR s.procID).mstatus.VM,
    (s.c_MCSR s.procID).mcpuid.ArchBase,
    s.c_NextFetch s.procID,
    s.exception,
    s.c_gpr s.procID,
    fun2set (s.MEM8,d),
    s.c_PC s.procID)`

val riscv_target_def = Define`
   riscv_target =
   <| get_pc := (\s. s.c_PC s.procID)
    ; get_reg := (\s. s.c_gpr s.procID o n2w)
    ; get_byte := riscv_state_MEM8
    ; state_ok := riscv_ok
    ; state_rel := riscv_asm_state
    ; proj := riscv_proj
    ; next := riscv_next
    ; config := riscv_config
    |>`

val () = export_theory ()
