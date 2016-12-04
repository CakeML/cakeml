open HolKernel Parse boolLib bossLib
open asmLib riscv_stepTheory;

val () = new_theory "riscv_target"

val () = wordsLib.guess_lengths()

val riscv_next_def = Define `riscv_next s = THE (NextRISCV s)`

(* --- Valid RISC-V states --- *)

(* We assume virtual memory is turned off and a 64-bit architecture (RV64I) *)
val riscv_ok_def = Define`
   riscv_ok ms <=>
   ((ms.c_MCSR ms.procID).mstatus.VM = 0w) /\
   ((ms.c_MCSR ms.procID).mcpuid.ArchBase = 2w) /\
   (ms.c_NextFetch ms.procID = NONE) /\
   (ms.exception = NoException) /\ aligned 2 (ms.c_PC ms.procID)`

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
(* (riscv_memop Load32  = INL LWU) /\ *)
   (riscv_memop Load8   = INL LBU) /\
   (riscv_memop Store   = INR SD) /\
(* (riscv_memop Store32 = INR SW) /\ *)
   (riscv_memop Store8  = INR SB)`

val riscv_const32_def = Define`
  riscv_const32 r (i: word32) =
  if i ' 11 then
    riscv_encode (ArithI (LUI (r, ~((31 >< 12) i)))) ++
    riscv_encode (ArithI (XORI (r, r, (11 >< 0) i)))
  else
    riscv_encode (ArithI (LUI (r, (31 >< 12) i))) ++
    riscv_encode (ArithI (ADDI (r, r, (11 >< 0) i)))`

val riscv_encode_fail_def = Define`
  riscv_encode_fail = [0w; 0w; 0w; 0w] : word8 list`

val () = Parse.temp_overload_on ("temp_reg", ``31w : word5``)

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
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) (~((63 >< 32) i)) ++
        riscv_encode (Shift (SLLI (n2w r, n2w r, 32w))) ++
        riscv_encode (ArithR (XOR (n2w r, n2w r, temp_reg)))
      else
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) ((63 >< 32) i) ++
        riscv_encode (Shift (SLLI (n2w r, n2w r, 32w))) ++
        riscv_encode (ArithR (OR (n2w r, n2w r, temp_reg)))) /\
   (riscv_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
     riscv_encode (ArithR (riscv_bop_r bop (n2w r1, n2w r2, n2w r3)))) /\
   (riscv_enc (Inst (Arith (Binop Sub r1 r2 (Imm i)))) =
     riscv_encode (ArithI (ADDI (n2w r1, n2w r2, -(w2w i))))) /\
   (riscv_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
     riscv_encode (ArithI (riscv_bop_i bop (n2w r1, n2w r2, w2w i)))) /\
   (riscv_enc (Inst (Arith (Shift sh r1 r2 n))) =
     riscv_encode (Shift (riscv_sh sh (n2w r1, n2w r2, n2w n)))) /\
   (riscv_enc (Inst (Arith (Div r1 r2 r3))) =
     riscv_encode (MulDiv (riscv$DIV (n2w r1, n2w r2, n2w r3)))) /\
   (riscv_enc (Inst (Arith (LongMul r1 r2 r3 r4))) =
     riscv_encode (MulDiv (MULHU (n2w r1, n2w r3, n2w r4))) ++
     riscv_encode (MulDiv (MUL (n2w r2, n2w r3, n2w r4)))) /\
   (riscv_enc (Inst (Arith (LongDiv _ _ _ _ _))) = riscv_encode_fail) /\
   (riscv_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
     riscv_encode (ArithR (SLTU (temp_reg, 0w, n2w r4))) ++
     riscv_encode (ArithR (ADD (n2w r1, n2w r2, n2w r3))) ++
     riscv_encode (ArithR (SLTU (n2w r4, n2w r1, n2w r3))) ++
     riscv_encode (ArithR (ADD (n2w r1, n2w r1, temp_reg))) ++
     riscv_encode (ArithR (SLTU (temp_reg, n2w r1, temp_reg))) ++
     riscv_encode (ArithR (OR (n2w r4, n2w r4, temp_reg)))) /\
   (riscv_enc (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
     riscv_encode (ArithR (ADD (n2w r1, n2w r2, n2w r3))) ++
     riscv_encode (ArithR (XOR (temp_reg, n2w r2, n2w r3))) ++
     riscv_encode (ArithI (XORI (temp_reg, temp_reg, -1w))) ++
     riscv_encode (ArithR (XOR (n2w r4, n2w r2, n2w r1))) ++
     riscv_encode (ArithR (AND (n2w r4, temp_reg, n2w r4))) ++
     riscv_encode (Shift (SRLI (n2w r4, n2w r4, 63w)))) /\
   (riscv_enc (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
     riscv_encode (ArithR (SUB (n2w r1, n2w r2, n2w r3))) ++
     riscv_encode (ArithR (XOR (temp_reg, n2w r2, n2w r3))) ++
     riscv_encode (ArithR (XOR (n2w r4, n2w r2, n2w r1))) ++
     riscv_encode (ArithR (AND (n2w r4, temp_reg, n2w r4))) ++
     riscv_encode (Shift (SRLI (n2w r4, n2w r4, 63w)))) /\
   (riscv_enc (Inst (Mem mop r1 (Addr r2 a))) =
      case riscv_memop mop of
         INL f => riscv_encode (Load (f (n2w r1, n2w r2, w2w a)))
       | INR f => riscv_encode (Store (f (n2w r2, n2w r1, w2w a)))) /\
   (riscv_enc (Jump a) = riscv_encode (Branch (JAL (0w, w2w (a >>> 1))))) /\
   (riscv_enc (JumpCmp c r1 (Reg r2) a) =
      if -0xFFCw <= a /\ a <= 0xFFFw then
        let off12 = w2w (a >>> 1) in
        case c of
           Equal => riscv_encode (Branch (BEQ (n2w r1, n2w r2, off12)))
         | Less  => riscv_encode (Branch (BLT (n2w r1, n2w r2, off12)))
         | Lower => riscv_encode (Branch (BLTU (n2w r1, n2w r2, off12)))
         | Test  => riscv_encode (ArithR (AND (temp_reg, n2w r1, n2w r2))) ++
                    riscv_encode (Branch (BEQ (temp_reg, 0w, off12 - 2w)))
         | NotEqual => riscv_encode (Branch (BNE (n2w r1, n2w r2, off12)))
         | NotLess  => riscv_encode (Branch (BGE (n2w r1, n2w r2, off12)))
         | NotLower => riscv_encode (Branch (BGEU (n2w r1, n2w r2, off12)))
         | NotTest  => riscv_encode (ArithR (AND (temp_reg, n2w r1, n2w r2))) ++
                       riscv_encode (Branch (BNE (temp_reg, 0w, off12 - 2w)))
      else
        let off20 = w2w (a >>> 1) - 2w in
        case c of
           Equal => riscv_encode (Branch (BNE (n2w r1, n2w r2, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Less  => riscv_encode (Branch (BGE (n2w r1, n2w r2, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Lower => riscv_encode (Branch (BGEU (n2w r1, n2w r2, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Test  => riscv_encode (ArithR (AND (temp_reg, n2w r1, n2w r2))) ++
                    riscv_encode (Branch (BNE (temp_reg, 0w, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20 - 2w)))
         | NotEqual => riscv_encode (Branch (BEQ (n2w r1, n2w r2, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotLess  => riscv_encode (Branch (BLT (n2w r1, n2w r2, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotLower => riscv_encode (Branch (BLTU (n2w r1, n2w r2, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotTest  => riscv_encode (ArithR (AND (temp_reg, n2w r1, n2w r2))) ++
                       riscv_encode (Branch (BEQ (temp_reg, 0w, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20 - 2w)))) /\
   (riscv_enc (JumpCmp c r (Imm i) a) =
      if -0xFFCw <= a /\ a <= 0xFFFw then
        let off12 = w2w (a >>> 1) - 2w in
        case c of
           Equal => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BEQ (n2w r, temp_reg, off12)))
         | Less  => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BLT (n2w r, temp_reg, off12)))
         | Lower => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BLTU (n2w r, temp_reg, off12)))
         | Test  => riscv_encode (ArithI (ANDI (temp_reg, n2w r, w2w i))) ++
                    riscv_encode (Branch (BEQ (temp_reg, 0w, off12)))
         | NotEqual => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BNE (n2w r, temp_reg, off12)))
         | NotLess  => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BGE (n2w r, temp_reg, off12)))
         | NotLower => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BGEU (n2w r, temp_reg, off12)))
         | NotTest  => riscv_encode (ArithI (ANDI (temp_reg, n2w r, w2w i))) ++
                       riscv_encode (Branch (BNE (temp_reg, 0w, off12)))
      else
        let off20 = w2w (a >>> 1) - 4w in
        case c of
           Equal => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BNE (n2w r, temp_reg, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Less  => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BGE (n2w r, temp_reg, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Lower => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                    riscv_encode (Branch (BGEU (n2w r, temp_reg, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | Test  => riscv_encode (ArithI (ANDI (temp_reg, n2w r, w2w i))) ++
                    riscv_encode (Branch (BNE (temp_reg, 0w, 4w))) ++
                    riscv_encode (Branch (JAL (0w, off20)))
         | NotEqual => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BEQ (n2w r, temp_reg, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotLess  => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BLT (n2w r, temp_reg, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotLower => riscv_encode (ArithI (ORI (temp_reg, 0w, w2w i))) ++
                       riscv_encode (Branch (BLTU (n2w r, temp_reg, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))
         | NotTest  => riscv_encode (ArithI (ANDI (temp_reg, n2w r, w2w i))) ++
                       riscv_encode (Branch (BEQ (temp_reg, 0w, 4w))) ++
                       riscv_encode (Branch (JAL (0w, off20)))) /\
   (riscv_enc (Call a) = riscv_encode (Branch (JAL (1w, w2w (a >>> 1))))) /\
   (riscv_enc (JumpReg r) = riscv_encode (Branch (JALR (0w, n2w r, 0w)))) /\
   (riscv_enc (Loc r i) =
      let imm12 = (11 >< 0) i in
      riscv_encode (ArithI (AUIPC (n2w r, (31 >< 12) (i - sw2sw imm12)))) ++
      riscv_encode (ArithI (ADDI (n2w r, n2w r, imm12))))`

(* --- Configuration for RISC-V --- *)

val eval = rhs o concl o EVAL
val min12 = eval ``sw2sw (INT_MINw: word12) : word64``
val max12 = eval ``sw2sw (INT_MAXw: word12) : word64``
val min21 = eval ``sw2sw (INT_MINw: 21 word) : word64``
val max21 = eval ``sw2sw (INT_MAXw: 21 word) : word64``
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``

val riscv_config_def = Define`
   riscv_config =
   <| ISA := RISC_V
    ; encode := riscv_enc
    ; reg_count := 32
    (* calling conventions: https://riscv.org/specifications/, p109
       0 - hardwired zero
       2 - stack pointer
       3 - global pointer
       31 - used by encoder above
    *)
    ; avoid_regs := [0; 2; 3; 31]
    ; link_reg := SOME 1
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := (\b i. (if b = INL Sub then ^min12 < i else ^min12 <= i) /\
                          i <= ^max12)
    ; addr_offset := (^min12, ^max12)
    ; jump_offset := (^min21, ^max21)
    ; cjump_offset := (^min21 + 8w, ^max21 + 4w)
    ; loc_offset := (^min32, 0x7FFFF7FFw)
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
   <| next := riscv_next
    ; config := riscv_config
    ; get_pc := (\s. s.c_PC s.procID)
    ; get_reg := (\s. s.c_gpr s.procID o n2w)
    ; get_byte := riscv_state_MEM8
    ; state_ok := riscv_ok
    ; proj := riscv_proj
    |>`

val (riscv_config, riscv_asm_ok) = asmLib.target_asm_rwts [] ``riscv_config``

val riscv_config = save_thm("riscv_config", riscv_config)
val riscv_asm_ok = save_thm("riscv_asm_ok", riscv_asm_ok)

val () = export_theory ()
