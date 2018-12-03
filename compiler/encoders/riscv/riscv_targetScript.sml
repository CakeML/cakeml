(*
  Define the target compiler configuration for RISC-V.
*)
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

val riscv_encode_fail_def = Define`
  riscv_encode_fail = [ArithI (ADDI (0w, 0w, 0w))]`

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
    [ArithI (LUI (r, ~((31 >< 12) i)));
     ArithI (XORI (r, r, (11 >< 0) i))]
  else
    [ArithI (LUI (r, (31 >< 12) i));
     ArithI (ADDI (r, r, (11 >< 0) i))]`

val eval = rhs o concl o EVAL
val min12 = eval ``sw2sw (INT_MINw: word12) : word64``
val max12 = eval ``sw2sw (INT_MAXw: word12) : word64``
val min21 = eval ``sw2sw (INT_MINw: 21 word) : word64``
val max21 = eval ``sw2sw (INT_MAXw: 21 word) : word64``
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``

val () = Parse.temp_overload_on ("temp_reg", ``31w : word5``)

val riscv_ast_def = Define`
   (riscv_ast (Inst Skip) = [ArithI (ADDI (0w, 0w, 0w))]) /\
   (riscv_ast (Inst (Const r (i: word64))) =
      let imm12 = (11 >< 0) i in
      if i = sw2sw imm12 then
        [ArithI (ORI (n2w r, 0w, imm12))]
      else if ((63 >< 32) i = 0w: word32) /\ ~i ' 31 \/
              ((63 >< 32) i = -1w: word32) /\ i ' 31 then
        riscv_const32 (n2w r) ((31 >< 0) i)
      else if i ' 31 then
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) (~((63 >< 32) i)) ++
        [Shift (SLLI (n2w r, n2w r, 32w));
         ArithR (XOR (n2w r, n2w r, temp_reg))]
      else
        riscv_const32 temp_reg ((31 >< 0) i) ++
        riscv_const32 (n2w r) ((63 >< 32) i) ++
        [Shift (SLLI (n2w r, n2w r, 32w));
         ArithR (OR (n2w r, n2w r, temp_reg))]) /\
   (riscv_ast (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
     [ArithR (riscv_bop_r bop (n2w r1, n2w r2, n2w r3))]) /\
   (riscv_ast (Inst (Arith (Binop Sub r1 r2 (Imm i)))) =
     [ArithI (ADDI (n2w r1, n2w r2, -(w2w i)))]) /\
   (riscv_ast (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
     [ArithI (riscv_bop_i bop (n2w r1, n2w r2, w2w i))]) /\
   (riscv_ast (Inst (Arith (Shift sh r1 r2 n))) =
     if sh = Ror then
       [Shift (SRLI (temp_reg, n2w r2, n2w n));
        Shift (SLLI (n2w r1, n2w r2, n2w (64 - n)));
        ArithR (OR (n2w r1, n2w r1, temp_reg))]
     else
       [Shift (riscv_sh sh (n2w r1, n2w r2, n2w n))]) /\
   (riscv_ast (Inst (Arith (Div r1 r2 r3))) =
     [MulDiv (riscv$DIV (n2w r1, n2w r2, n2w r3))]) /\
   (riscv_ast (Inst (Arith (LongMul r1 r2 r3 r4))) =
     [MulDiv (MULHU (n2w r1, n2w r3, n2w r4));
      MulDiv (MUL (n2w r2, n2w r3, n2w r4))]) /\
   (riscv_ast (Inst (Arith (LongDiv _ _ _ _ _))) = riscv_encode_fail) /\
   (riscv_ast (Inst (Arith (AddCarry r1 r2 r3 r4))) =
     [ArithR (SLTU (temp_reg, 0w, n2w r4));
      ArithR (ADD (n2w r1, n2w r2, n2w r3));
      ArithR (SLTU (n2w r4, n2w r1, n2w r3));
      ArithR (ADD (n2w r1, n2w r1, temp_reg));
      ArithR (SLTU (temp_reg, n2w r1, temp_reg));
      ArithR (OR (n2w r4, n2w r4, temp_reg))]) /\
   (riscv_ast (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
     [ArithR (XOR (temp_reg, n2w r2, n2w r3));
      ArithI (XORI (temp_reg, temp_reg, -1w));
      ArithR (ADD (n2w r1, n2w r2, n2w r3));
      ArithR (XOR (n2w r4, n2w r3, n2w r1));
      ArithR (AND (n2w r4, temp_reg, n2w r4));
      Shift (SRLI (n2w r4, n2w r4, 63w))]) /\
   (riscv_ast (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
     [ArithR (XOR (temp_reg, n2w r2, n2w r3));
      ArithR (SUB (n2w r1, n2w r2, n2w r3));
      ArithR (XOR (n2w r4, n2w r3, n2w r1));
      ArithI (XORI (n2w r4, n2w r4, -1w));
      ArithR (AND (n2w r4, temp_reg, n2w r4));
      Shift (SRLI (n2w r4, n2w r4, 63w))]) /\
   (riscv_ast (Inst (Mem mop r1 (Addr r2 a))) =
      case riscv_memop mop of
         INL f => [Load (f (n2w r1, n2w r2, w2w a))]
       | INR f => [Store (f (n2w r2, n2w r1, w2w a))]) /\
   (riscv_ast (Inst (FP _)) = riscv_encode_fail) /\
   (riscv_ast (Jump a) =
      if ^min21 <= a /\ a <= ^max21 then
         [Branch (JAL (0w, w2w (a >>> 1)))]
      else let imm12 = (11 >< 0) a in
         [ArithI (AUIPC (temp_reg, (31 >< 12) (a - sw2sw imm12)));
          Branch (JALR (0w, temp_reg, (11 >< 0) a))]) /\
   (riscv_ast (JumpCmp c r1 (Reg r2) a) =
      if -0xFFCw <= a /\ a <= 0xFFFw then
        let off12 = w2w (a >>> 1) in
        case c of
           Equal => [Branch (BEQ (n2w r1, n2w r2, off12))]
         | Less  => [Branch (BLT (n2w r1, n2w r2, off12))]
         | Lower => [Branch (BLTU (n2w r1, n2w r2, off12))]
         | Test  => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                     Branch (BEQ (temp_reg, 0w, off12 - 2w))]
         | NotEqual => [Branch (BNE (n2w r1, n2w r2, off12))]
         | NotLess  => [Branch (BGE (n2w r1, n2w r2, off12))]
         | NotLower => [Branch (BGEU (n2w r1, n2w r2, off12))]
         | NotTest  => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                        Branch (BNE (temp_reg, 0w, off12 - 2w))]
      else
        let off20 = w2w (a >>> 1) - 2w in
        case c of
           Equal => [Branch (BNE (n2w r1, n2w r2, 4w));
                     Branch (JAL (0w, off20))]
         | Less  => [Branch (BGE (n2w r1, n2w r2, 4w));
                     Branch (JAL (0w, off20))]
         | Lower => [Branch (BGEU (n2w r1, n2w r2, 4w));
                     Branch (JAL (0w, off20))]
         | Test  => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                     Branch (BNE (temp_reg, 0w, 4w));
                     Branch (JAL (0w, off20 - 2w))]
         | NotEqual => [Branch (BEQ (n2w r1, n2w r2, 4w));
                        Branch (JAL (0w, off20))]
         | NotLess  => [Branch (BLT (n2w r1, n2w r2, 4w));
                        Branch (JAL (0w, off20))]
         | NotLower => [Branch (BLTU (n2w r1, n2w r2, 4w));
                        Branch (JAL (0w, off20))]
         | NotTest  => [ArithR (AND (temp_reg, n2w r1, n2w r2));
                        Branch (BEQ (temp_reg, 0w, 4w));
                        Branch (JAL (0w, off20 - 2w))]) /\
   (riscv_ast (JumpCmp c r (Imm i) a) =
      if -0xFFCw <= a /\ a <= 0xFFFw then
        let off12 = w2w (a >>> 1) - 2w in
        case c of
           Equal => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BEQ (n2w r, temp_reg, off12))]
         | Less  => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BLT (n2w r, temp_reg, off12))]
         | Lower => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BLTU (n2w r, temp_reg, off12))]
         | Test  => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                     Branch (BEQ (temp_reg, 0w, off12))]
         | NotEqual => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BNE (n2w r, temp_reg, off12))]
         | NotLess  => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BGE (n2w r, temp_reg, off12))]
         | NotLower => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BGEU (n2w r, temp_reg, off12))]
         | NotTest  => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                        Branch (BNE (temp_reg, 0w, off12))]
      else
        let off20 = w2w (a >>> 1) - 4w in
        case c of
           Equal => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BNE (n2w r, temp_reg, 4w));
                     Branch (JAL (0w, off20))]
         | Less  => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BGE (n2w r, temp_reg, 4w));
                     Branch (JAL (0w, off20))]
         | Lower => [ArithI (ORI (temp_reg, 0w, w2w i));
                     Branch (BGEU (n2w r, temp_reg, 4w));
                     Branch (JAL (0w, off20))]
         | Test  => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                     Branch (BNE (temp_reg, 0w, 4w));
                     Branch (JAL (0w, off20))]
         | NotEqual => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BEQ (n2w r, temp_reg, 4w));
                        Branch (JAL (0w, off20))]
         | NotLess  => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BLT (n2w r, temp_reg, 4w));
                        Branch (JAL (0w, off20))]
         | NotLower => [ArithI (ORI (temp_reg, 0w, w2w i));
                        Branch (BLTU (n2w r, temp_reg, 4w));
                        Branch (JAL (0w, off20))]
         | NotTest  => [ArithI (ANDI (temp_reg, n2w r, w2w i));
                        Branch (BEQ (temp_reg, 0w, 4w));
                        Branch (JAL (0w, off20))]) /\
   (riscv_ast (Call a) =
      if ^min21 <= a /\ a <= ^max21 then
         [Branch (JAL (1w, w2w (a >>> 1)))]
      else let imm12 = (11 >< 0) a in
         [ArithI (AUIPC (1w, (31 >< 12) (a - sw2sw imm12)));
          Branch (JALR (1w, 1w, (11 >< 0) a))]) /\
   (riscv_ast (JumpReg r) = [Branch (JALR (0w, n2w r, 0w))]) /\
   (riscv_ast (Loc r i) =
      let imm12 = (11 >< 0) i in
      [ArithI (AUIPC (n2w r, (31 >< 12) (i - sw2sw imm12)));
       ArithI (ADDI (n2w r, n2w r, imm12))])`

val riscv_enc_def = zDefine`
  riscv_enc = combin$C LIST_BIND riscv_encode o riscv_ast`

(* --- Configuration for RISC-V --- *)

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
    ; fp_reg_count := 0
    ; link_reg := SOME 1
    ; two_reg_arith := F
    ; big_endian := F
    ; valid_imm := (\b i. (if b = INL Sub then ^min12 < i else ^min12 <= i) /\
                          i <= ^max12)
    ; addr_offset := (^min12, ^max12)
    ; byte_offset := (^min12, ^max12)
    ; jump_offset := (^min32, 0x7FFFF7FFw)
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
