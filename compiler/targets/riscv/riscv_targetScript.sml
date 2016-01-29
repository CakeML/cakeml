open HolKernel Parse boolLib bossLib
open asmLib riscv_stepLib;

val () = new_theory "riscv_target"

val () = wordsLib.guess_lengths()

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
   <| ISA_name := "riscv"
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
   <| encode := riscv_enc
    ; get_pc := (\s. s.c_PC s.procID)
    ; get_reg := (\s. s.c_gpr s.procID o n2w)
    ; get_byte := riscv_state_MEM8
    ; state_ok := riscv_ok
    ; state_rel := riscv_asm_state
    ; proj := riscv_proj
    ; next := riscv_next
    ; config := riscv_config
    |>`

(* ------------------------------------------------------------------------- *)

(* some lemmas ---------------------------------------------------------- *)

val riscv_asm_state =
   REWRITE_RULE [DECIDE ``1 < i = i <> 0n /\ i <> 1``] riscv_asm_state_def

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      riscv_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      ((state.c_MCSR state.procID).mstatus.VM = 0w) /\
      ((state.c_MCSR state.procID).mcpuid.ArchBase = 2w) /\
      (state.c_NextFetch state.procID = NONE) /\
      aligned 2 (state.c_PC state.procID) /\
      (state.MEM8 (state.c_PC state.procID) = a) /\
      (state.MEM8 (state.c_PC state.procID + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + 3w) = d) /\
      state.c_PC state.procID + 3w IN s.mem_domain /\
      state.c_PC state.procID + 2w IN s.mem_domain /\
      state.c_PC state.procID + 1w IN s.mem_domain /\
      state.c_PC state.procID IN s.mem_domain`,
   rw [riscv_asm_state_def, riscv_ok_def, asmSemTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract, set_sepTheory.fun2set_eq]
   \\ rfs []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      riscv_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM8 (state.c_PC state.procID + w) = a) /\
      (state.MEM8 (state.c_PC state.procID + w + 1w) = b) /\
      (state.MEM8 (state.c_PC state.procID + w + 2w) = c) /\
      (state.MEM8 (state.c_PC state.procID + w + 3w) = d) /\
      state.c_PC state.procID + w + 3w IN s.mem_domain /\
      state.c_PC state.procID + w + 2w IN s.mem_domain /\
      state.c_PC state.procID + w + 1w IN s.mem_domain /\
      state.c_PC state.procID + w IN s.mem_domain`,
   rw [riscv_asm_state_def, riscv_ok_def, asmSemTheory.bytes_in_memory_def,
       set_sepTheory.fun2set_eq]
   \\ rfs []
   )

val lem1 = asmLib.v2w_BIT_n2w 5
val lem2 = asmLib.v2w_BIT_n2w 6

val lem3 = Q.prove(
   `!n s state.
     n <> 0 /\ n <> 1 /\ n < 32 /\ riscv_asm_state s state ==>
     (s.regs n = state.c_gpr state.procID (n2w n))`,
   lrw [riscv_asm_state]
   )

val lem4 = blastLib.BBLAST_PROVE
  ``0xFFFFFFFFFFFFF800w <= c /\ c <= 0x7FFw ==>
    (sw2sw
      (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
            c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c : word64)``


val lem5 = Q.prove(
  `aligned 2 (c: word64) ==>
   ~word_lsb (v2w [c ' 20; c ' 19; c ' 18; c ' 17; c ' 16; c ' 15; c ' 14;
                   c ' 13; c ' 12; c ' 11; c ' 10; c ' 9; c ' 8; c ' 7;
                   c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1] : 20 word)`,
  simp [alignmentTheory.aligned_extract]
  \\ blastLib.BBLAST_TAC
  )

val lem6 = blastLib.BBLAST_PROVE
  ``(((31 >< 0) (c: word64) : word32) ' 11 = c ' 11) /\
    (((63 >< 32) c : word32) ' 11 = c ' 43) /\
    (~(63 >< 32) c : word32 ' 11 = ~c ' 43) ``

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open riscvTheory
   in
      [riscv_enc_def, riscv_encode_def, riscv_const32_def, riscv_bop_r_def,
       riscv_bop_i_def, riscv_sh_def, riscv_memop_def, Encode_def, opc_def,
       Itype_def, Rtype_def, Stype_def, SBtype_def, Utype_def, UJtype_def]
   end

val enc_rwts =
  [riscv_config_def, lem6] @ encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, riscv_config_def] @
  encode_rwts @ asmLib.asm_ok_rwts

val dec_rwts = [riscv_dec_def, fetch_decode_def, riscv_dec_const32_def]

(* some custom tactics ---------------------------------------------------- *)

local
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.map (boolify 8)
   val v2w_n2w_rule =
     Conv.RIGHT_CONV_RULE (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   fun dec tm =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         l |> riscv_stepLib.riscv_decode
           |> v2w_n2w_rule
           |> Conv.CONV_RULE (Conv.LHS_CONV (REWRITE_CONV [th1]))
      end
   val s1 = HolKernel.syntax_fns1 "riscv"
   val (_, _, dest_Decode, is_Decode) = s1 "Decode"
   val find_Decode = HolKernel.bvk_find_term (is_Decode o snd) dest_Decode
   fun is_riscv_next tm =
     Lib.total (fst o Term.dest_const o fst o Term.dest_comb) tm =
     SOME "riscv_next"
   fun dest_env tm =
      case Lib.total boolSyntax.strip_comb tm of
         SOME (env, [n, ms]) =>
            if Lib.total (fst o Term.dest_var) env = SOME "env" andalso
               not (is_riscv_next ms) andalso numSyntax.is_numeral n
               then (numSyntax.int_of_term n, ms)
            else raise ERR "dest_env" ""
       | _ => raise ERR "dest_env" ""
   fun find_env g =
      g |> boolSyntax.strip_conj |> List.last
        |> HolKernel.find_terms (Lib.can dest_env)
        |> Lib.mk_set
        |> mlibUseful.sort_map (HolKernel.term_size) Int.compare
        |> Lib.total List.last
        |> Option.map ((numSyntax.term_of_int ## Lib.I) o dest_env)
   val (_, _, dest_NextRISCV, is_NextRISCV) =
      HolKernel.syntax_fns1 "riscv_step" "NextRISCV"
   val find_NextRISCV =
      dest_NextRISCV o List.hd o HolKernel.find_terms is_NextRISCV
   val s = ``s: riscv_state``
   fun step the_state l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
         val thm = Thm.INST [s |-> the_state] (riscv_stepLib.riscv_step v)
      in
         (Drule.DISCH_ALL thm,
          optionSyntax.dest_some (boolSyntax.rand (Thm.concl thm)))
      end
   val ms = ``ms: riscv_state``
   fun new_state_var l =
     Lib.with_flag (Globals.priming, SOME "_")
       (Term.variant (List.concat (List.map Term.free_vars l))) ms
   fun env (t, tm) =
     let
       (*
       val (t, tm) = Option.valOf (find_env g)
       *)
       val etm = ``env ^t ^tm : riscv_state``
     in
       (fn (asl, g) =>
         let
           val pc = fst (pred_setSyntax.dest_in (hd asl))
         in
           `(!a. a IN s1.mem_domain ==> ((^etm).MEM8 a = ms.MEM8 a)) /\
            ((^etm).exception = ms.exception) /\
            ((^etm).c_NextFetch (^etm).procID = ms.c_NextFetch ms.procID) /\
            (((^etm).c_MCSR (^etm).procID).mstatus.VM =
             (ms.c_MCSR ms.procID).mstatus.VM) /\
            (((^etm).c_MCSR (^etm).procID).mcpuid.ArchBase =
             (ms.c_MCSR ms.procID).mcpuid.ArchBase) /\
            ((^etm).c_PC (^etm).procID = ^pc)`
            by asm_simp_tac (srw_ss())
                 [combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ, Abbr `^tm`]
         end (asl, g)
       , etm
       )
     end
in
   fun decode_tac' (asl, g) =
      (case find_Decode g of
          SOME tm =>
           let
              val dec_thm = dec tm
           (* val () = (print_thm dec_thm; print "\n") *)
           in
              simp [dec_thm, lem1, lem2]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac (asl, g) =
     (let
         val x as (pc, l, _, _) =
            List.last
              (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
         val x_tm = asmLib.mk_bytes_in_memory x
         val l = List.rev (fst (listSyntax.dest_list l))
         val th = case Lib.total wordsSyntax.dest_word_add pc of
                     SOME (_, w) => Thm.SPEC w bytes_in_memory_thm2
                   | NONE => bytes_in_memory_thm
         val (tac, the_state) =
           case find_env g of SOME x => env x | NONE => (all_tac, ms)
         val (step_thm, next_state) = step the_state l
         val next_state_var = new_state_var (g::asl)
      in
         imp_res_tac th
         \\ tac
         \\ assume_tac step_thm
         \\ qabbrev_tac `^next_state_var = ^next_state`
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss())
              [lem1, lem4, lem5, alignmentTheory.aligned_numeric]
         \\ Tactical.PAT_ASSUM x_tm kall_tac
         \\ SUBST1_TAC (Thm.SPEC the_state riscv_next_def)
         \\ byte_eq_tac
         \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [lem1]
      end
      handle List.Empty => FAIL_TAC "next_state_tac: empty") (asl, g)
end

local
  val thm = DECIDE ``~(n < 32n) ==> (n - 32 + 32 = n)``
in
fun state_tac (gs as (asl, _)) =
  let
    val l = List.mapPartial (Lib.total (fst o markerSyntax.dest_abbrev)) asl
    val (l, x) = Lib.front_last l
  in
    (
     NO_STRIP_FULL_SIMP_TAC (srw_ss())
       [riscv_ok_def, riscv_asm_state, asmPropsTheory.all_pcs, lem2,
        alignmentTheory.aligned_numeric, set_sepTheory.fun2set_eq]
     \\ MAP_EVERY (fn s =>
          qunabbrev_tac [QUOTE s]
          \\ asm_simp_tac (srw_ss())
               [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric]
          \\ NTAC 10 (POP_ASSUM kall_tac)
          ) l
     \\ qunabbrev_tac [QUOTE x]
     \\ asm_simp_tac (srw_ss())
          [combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric]
     \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
     \\ simp []
     \\ rw [combinTheory.APPLY_UPDATE_THM, thm]
    ) gs
  end
end

val decode_tac =
   simp enc_rwts
   \\ REPEAT strip_tac
   \\ REPEAT (simp dec_rwts \\ decode_tac')
   \\ NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (hd asl) of
         SOME l => List.length l div 4
       | NONE => raise ERR "number_of_instructions" ""
   fun next_tac' gs =
      let
         val j = number_of_instructions (fst gs)
         val i = j - 1
         val n = numLib.term_of_int i
      in
         exists_tac n
         \\ simp [asmPropsTheory.asserts_eval, set_sepTheory.fun2set_eq,
                  asmPropsTheory.interference_ok_def, riscv_proj_def]
         \\ NTAC 2 strip_tac
         \\ NTAC i (split_bytes_in_memory_tac 4)
         \\ NTAC j next_state_tac
         \\ REPEAT (Q.PAT_ASSUM `ms.MEM8 qq = bn` kall_tac)
         \\ REPEAT (Q.PAT_ASSUM `NextRISCV qq = qqq` kall_tac)
         \\ state_tac
      end gs
in
   val next_tac =
      qpat_assum `bytes_in_memory aa bb cc dd` mp_tac
      \\ simp enc_rwts
      \\ NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) enc_rwts
      \\ imp_res_tac lem3
      \\ NO_STRIP_FULL_SIMP_TAC std_ss []
      \\ strip_tac
      \\ next_tac'
   val bnext_tac =
      next_tac
      \\ NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC
end

val enc_ok_tac =
   full_simp_tac (srw_ss()++boolSimps.LET_ss)
      (asmPropsTheory.offset_monotonic_def :: enc_ok_rwts)

(* -------------------------------------------------------------------------
   riscv_asm_deterministic
   riscv_backend_correct
   ------------------------------------------------------------------------- *)

val riscv_encoding = Count.apply Q.prove (
   `!i. asm_ok i riscv_config ==>
        let l = riscv_enc i in
        let n = LENGTH l in
           (!x. riscv_dec (l ++ x) = i) /\ (n MOD 4 = 0) /\ n <> 0`,
   Cases
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
         \\ decode_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `c = sw2sw ((11 >< 0) c : word12)`
         >- decode_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\ ~c ' 31 \/
                      ((63 >< 32) c = -1w: word32) /\ c ' 31`
         >- (Cases_on `c ' 11` \\ decode_tac)
         \\ Cases_on `c ' 31`
         \\ Cases_on `c ' 43`
         \\ Cases_on `c ' 11`
         \\ decode_tac
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
            \\ decode_tac
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ decode_tac
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      \\ decode_tac
      )
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ decode_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac
      )
      (*--------------
          Loc
        --------------*)
   \\ print_tac "Loc"
   \\ decode_tac
   )

val riscv_asm_deterministic = Q.store_thm("riscv_asm_deterministic",
   `asm_deterministic riscv_enc riscv_config`,
   metis_tac [asmPropsTheory.decoder_asm_deterministic, riscv_encoding]
   )

val riscv_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [riscv_config_def] riscv_asm_deterministic

val enc_ok_rwts =
   SIMP_RULE (bool_ss++boolSimps.LET_ss) [riscv_config_def] riscv_encoding ::
   enc_ok_rwts

val riscv_backend_correct = Count.apply Q.store_thm ("riscv_backend_correct",
   `backend_correct riscv_target`,
   simp [asmPropsTheory.backend_correct_def, riscv_target_def]
   \\ REVERSE (REPEAT conj_tac)
   >| [
      rw [asmSemTheory.asm_step_def] \\ Cases_on `i`,
      srw_tac []
        [riscv_asm_state_def, riscv_config_def, set_sepTheory.fun2set_eq]
      \\  `1 < i` by decide_tac
      \\ simp [],
      srw_tac [] [riscv_proj_def, riscv_asm_state_def, riscv_ok_def],
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
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
         \\ next_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `c = sw2sw ((11 >< 0) c : word12)`
         >- bnext_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\ ~c ' 31 \/
                      ((63 >< 32) c = -1w: word32) /\ c ' 31`
         >- (Cases_on `c ' 11` \\ bnext_tac)
         \\ Cases_on `c ' 31`
         \\ Cases_on `c ' 43`
         \\ Cases_on `c ' 11`
         \\ bnext_tac
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
            \\ bnext_tac
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ next_tac
         )
         (*--------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ Cases_on `a`
         \\ Cases_on `m`
         \\ next_tac
         \\ full_simp_tac
              (srw_ss()++wordsLib.WORD_EXTRACT_ss++wordsLib.WORD_CANCEL_ss) []
      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ bnext_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      >| [
         Cases_on `ms.c_gpr ms.procID (n2w n) = ms.c_gpr ms.procID (n2w n')`,
         Cases_on `ms.c_gpr ms.procID (n2w n) <+ ms.c_gpr ms.procID (n2w n')`,
         Cases_on `ms.c_gpr ms.procID (n2w n) < ms.c_gpr ms.procID (n2w n')`,
         Cases_on `ms.c_gpr ms.procID (n2w n) &&
                   ms.c_gpr ms.procID (n2w n') = 0w`,
         Cases_on `ms.c_gpr ms.procID (n2w n) <> ms.c_gpr ms.procID (n2w n')`,
         Cases_on `~(ms.c_gpr ms.procID (n2w n) <+
                     ms.c_gpr ms.procID (n2w n'))`,
         Cases_on `~(ms.c_gpr ms.procID (n2w n) < ms.c_gpr ms.procID (n2w n'))`,
         Cases_on `(ms.c_gpr ms.procID (n2w n) &&
                    ms.c_gpr ms.procID (n2w n')) <> 0w`,
         Cases_on `ms.c_gpr ms.procID (n2w n) = c'`,
         Cases_on `ms.c_gpr ms.procID (n2w n) <+ c'`,
         Cases_on `ms.c_gpr ms.procID (n2w n) < c'`,
         Cases_on `ms.c_gpr ms.procID (n2w n) && c' = 0w`,
         Cases_on `ms.c_gpr ms.procID (n2w n) <> c'`,
         Cases_on `~(ms.c_gpr ms.procID (n2w n) <+ c')`,
         Cases_on `~(ms.c_gpr ms.procID (n2w n) < c')`,
         Cases_on `(ms.c_gpr ms.procID (n2w n) && c') <> 0w`
      ]
      \\ bnext_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ bnext_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ bnext_tac
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ bnext_tac
      )
   >- (
      (*--------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `ri`
      \\ Cases_on `cmp`
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          Call enc_ok
        --------------*)
      enc_ok_tac
      )
   >- (
      (*--------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ enc_ok_tac
      )
      (*--------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [riscv_asm_deterministic_config]
   )

val () = export_theory ()
