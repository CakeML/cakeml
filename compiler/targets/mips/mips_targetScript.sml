open HolKernel Parse boolLib bossLib
open asmLib mips_stepTheory;

val () = new_theory "mips_target"

val () = wordsLib.guess_lengths()

(* --- The next-state function --- *)

(* --------------------------------------------------------------------------
   Simplifying Assumption for MIPS Branch-Delay Slot
   -------------------------------------------------
   NOTE: The next-state function defined below merges branches with their
   following instruction. This temporal abstraction artificially prevents us
   from considering side-effect events (exceptions) occurring between these two
   instructions. As such, we are assuming that this case is handled correctly
   and we don't attempt to model or verify this behaviour.
   -------------------------------------------------------------------------- *)

val mips_next_def = Define`
   mips_next s =
   let s' = THE (NextStateMIPS s) in
     if IS_SOME s'.BranchDelay then THE (NextStateMIPS s') else s'`

(* --- Valid MIPS states --- *)

val mips_ok_def = Define`
   mips_ok ms =
   ms.CP0.Config.BE /\ ~ms.CP0.Status.RE /\ ~ms.exceptionSignalled /\
   (ms.BranchDelay = NONE) /\ (ms.BranchTo = NONE) /\
   (ms.exception = NoException) /\ aligned 2 ms.PC`

(* --- Encode ASM instructions to MIPS bytes. --- *)

val mips_encode_def = Define`
   mips_encode i =
   let w = mips$Encode i in
      [(31 >< 24) w; (23 >< 16) w; (15 >< 8) w; (7 >< 0) w] : word8 list`

val encs_def = Define `encs l = FLAT (MAP mips_encode l)`

val mips_bop_r_def = Define`
   (mips_bop_r Add = DADDU) /\
   (mips_bop_r Sub = DSUBU) /\
   (mips_bop_r And = AND) /\
   (mips_bop_r Or  = OR) /\
   (mips_bop_r Xor = XOR)`

val mips_bop_i_def = Define`
   (mips_bop_i Add = DADDIU) /\
   (mips_bop_i And = ANDI) /\
   (mips_bop_i Or  = ORI) /\
   (mips_bop_i Xor = XORI)`

val mips_sh_def = Define`
   (mips_sh Lsl = DSLL) /\
   (mips_sh Lsr = DSRL) /\
   (mips_sh Asr = DSRA)`

val mips_sh32_def = Define`
   (mips_sh32 Lsl = DSLL32) /\
   (mips_sh32 Lsr = DSRL32) /\
   (mips_sh32 Asr = DSRA32)`

val mips_memop_def = Define`
   (mips_memop Load    = INL LD) /\
(* (mips_memop Load32  = INL LWU) /\ *)
   (mips_memop Load8   = INL LBU) /\
   (mips_memop Store   = INR SD) /\
(* (mips_memop Store32 = INR SW) /\ *)
   (mips_memop Store8  = INR SB)`

val mips_cmp_def = Define`
   (mips_cmp Equal    = (NONE, BEQ)) /\
   (mips_cmp Less     = (SOME (SLT, SLTI), BNE)) /\
   (mips_cmp Lower    = (SOME (SLTU, SLTIU), BNE)) /\
   (mips_cmp Test     = (SOME (AND, ANDI), BEQ)) /\
   (mips_cmp NotEqual = (NONE, BNE)) /\
   (mips_cmp NotLess  = (SOME (SLT, SLTI), BEQ)) /\
   (mips_cmp NotLower = (SOME (SLTU, SLTIU), BEQ)) /\
   (mips_cmp NotTest  = (SOME (AND, ANDI), BNE))`

val nop = ``Shift (SLL (0w, 0w, 0w))``

val mips_encode_fail_def = Define`
  mips_encode_fail = [0w; 0w; 0w; 0w] : word8 list`

val mips_enc_def = Define`
   (mips_enc (Inst Skip) = mips_encode ^nop) /\
   (mips_enc (Inst (Const r (i: word64))) =
      let top    = (63 >< 32) i : word32
      and middle = (31 >< 16) i : word16
      and bottom = (15 ><  0) i : word16
      in
         if (top = 0w) /\ (middle = 0w) then
            mips_encode (ArithI (ORI (0w, n2w r, bottom)))
         else if (top = -1w) /\ (middle = -1w) /\ bottom ' 15 then
            mips_encode (ArithI (ADDIU (0w, n2w r, bottom)))
         else if (top = 0w) /\ ~middle ' 15 \/ (top = -1w) /\ middle ' 15 then
            encs [ArithI (LUI (n2w r, middle));
                  ArithI (XORI (n2w r, n2w r, bottom))]
         else
            encs [ArithI (LUI (n2w r, (31 >< 16) top));
                  ArithI (ORI (n2w r, n2w r, (15 >< 0) top));
                  Shift (DSLL (n2w r, n2w r, 16w));
                  ArithI (ORI (n2w r, n2w r, middle));
                  Shift (DSLL (n2w r, n2w r, 16w));
                  ArithI (ORI (n2w r, n2w r, bottom))]) /\
   (mips_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
       mips_encode (ArithR (mips_bop_r bop (n2w r2, n2w r3, n2w r1)))) /\
   (mips_enc (Inst (Arith (Binop Sub r1 r2 (Imm i)))) =
       mips_encode (ArithI (DADDIU (n2w r2, n2w r1, -(w2w i))))) /\
   (mips_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       mips_encode (ArithI (mips_bop_i bop (n2w r2, n2w r1, w2w i)))) /\
   (mips_enc (Inst (Arith (Shift sh r1 r2 n))) =
       let (f, n) = if n < 32 then (mips_sh, n) else (mips_sh32, n - 32) in
         mips_encode (Shift (f sh (n2w r2, n2w r1, n2w n)))) /\
   (mips_enc (Inst (Arith (Div r1 r2 r3))) =
       encs [MultDiv (DDIVU (n2w r2, n2w r3));
             MultDiv (MFLO (n2w r1))]) /\
   (mips_enc (Inst (Arith (LongMul r1 r2 r3 r4))) =
       encs [MultDiv (DMULTU (n2w r3, n2w r4));
             MultDiv (MFHI (n2w r1));
             MultDiv (MFLO (n2w r2))]) /\
   (mips_enc (Inst (Arith (LongDiv _ _ _ _ _))) = mips_encode_fail) /\
   (mips_enc (Inst (Arith (AddCarry r1 r2 r3 r4))) =
       encs [ArithR (SLTU (0w, n2w r4, 1w));
             ArithR (DADDU (n2w r2, n2w r3, n2w r1));
             ArithR (SLTU (n2w r1, n2w r3, n2w r4));
             ArithR (DADDU (n2w r1, 1w, n2w r1));
             ArithR (SLTU (n2w r1, 1w, 1w));
             ArithR (OR (n2w r4, 1w, n2w r4))]) /\
   (mips_enc (Inst (Mem mop r1 (Addr r2 a))) =
       case mips_memop mop of
          INL f => mips_encode (Load (f (n2w r2, n2w r1, w2w a)))
        | INR f => mips_encode (Store (f (n2w r2, n2w r1, w2w a)))) /\
   (mips_enc (Jump a) =
       encs [Branch (BEQ (0w, 0w, w2w (a >>> 2) - 1w)); ^nop]) /\
   (mips_enc (JumpCmp c r1 (Reg r2) a) =
       let (f1, f2) = mips_cmp c and b = w2w (a >>> 2) - 2w in
       let l = case f1 of
                  SOME (f, _) =>
                   [ArithR (f (n2w r1, n2w r2, 1w)); Branch (f2 (1w, 0w, b))]
                | NONE =>
                   [Branch (f2 (n2w r1, n2w r2, b + 1w))]
       in
         encs (l ++ [^nop])) /\
   (mips_enc (JumpCmp c r (Imm i) a) =
       let (f1, f2) = mips_cmp c and b = w2w (a >>> 2) - 2w in
       let l = case f1 of
                  SOME (_, f) =>
                   [ArithI (f (n2w r, 1w, w2w i)); Branch (f2 (1w, 0w, b))]
                | NONE =>
                   [ArithI (DADDIU (0w, 1w, w2w i)); Branch (f2 (n2w r, 1w, b))]
       in
         encs (l ++ [^nop])) /\
   (mips_enc (Call a) =
       encs [Branch (BGEZAL (0w, w2w (a >>> 2) - 1w)); ^nop]) /\
   (mips_enc (JumpReg r) = encs [Branch (JR (n2w r)); ^nop]) /\
   (mips_enc (Loc r i) =
       encs
       (if r = 31 then
           [Branch (BLTZAL (0w, 0w));                    (* LR := pc + 8     *)
            ArithI (DADDIU (31w, n2w r, w2w (i - 8w)))]  (* r := LR - 8 + i  *)
        else
           [ArithI (ORI (31w, 1w, 0w));                  (* $1 := LR         *)
            Branch (BLTZAL (0w, 0w));                    (* LR := pc + 12    *)
            ArithI (DADDIU (31w, n2w r, w2w (i - 12w))); (* r := LR - 12 + i *)
            ArithI (ORI (1w, 31w, 0w))]))`               (* LR := $1         *)

(* --- Configuration for MIPS --- *)

val eval = rhs o concl o EVAL
val min16 = eval ``sw2sw (INT_MINw: word16) : word64``
val max16 = eval ``sw2sw (INT_MAXw: word16) : word64``
val umax16 = eval ``w2w (UINT_MAXw: word16) : word64``

val mips_config_def = Define`
   mips_config =
   <| ISA := MIPS
    ; encode := mips_enc
    ; reg_count := 32
    ; avoid_regs := [0; 1; 25; 26; 27; 28; 29]
    ; link_reg := SOME 31
    ; two_reg_arith := F
    ; big_endian := T
    ; valid_imm :=
       (\b i. if b IN {INL And; INL Or; INL Xor; INR Test; INR NotTest} then
                0w <= i /\ i <= ^umax16
              else (if b = INL Sub then ^min16 < i else ^min16 <= i) /\
                   i <= ^max16)
    ; addr_offset := (^min16, ^max16)
    ; jump_offset := (^min16, ^max16)
    ; cjump_offset := (^min16, ^max16)
    ; loc_offset := (^min16 + 12w, ^max16 + 8w)
    ; code_alignment := 2
    |>`

val mips_proj_def = Define`
   mips_proj d s =
   (s.CP0.Config, s.CP0.Status.RE, s.exceptionSignalled,
    s.BranchDelay, s.BranchTo, s.exception, s.gpr, s.lo, s.hi,
    fun2set (s.MEM,d), s.PC)`

val mips_target_def = Define`
   mips_target =
   <| next := mips_next
    ; config := mips_config
    ; get_pc := mips_state_PC
    ; get_reg := (\s. mips_state_gpr s o n2w)
    ; get_byte := mips_state_MEM
    ; state_ok := mips_ok
    ; proj := mips_proj
    |>`

val mips_reg_ok_def = Define`
  mips_reg_ok n = ~MEM n mips_config.avoid_regs`

val mips_reg_ok = save_thm("mips_reg_ok",
  GSYM (SIMP_RULE (srw_ss()) [mips_config_def] mips_reg_ok_def))

val (mips_config, mips_asm_ok) =
  asmLib.target_asm_rwts [mips_reg_ok] ``mips_config``

val mips_config = save_thm("mips_config", mips_config)
val mips_asm_ok = save_thm("mips_asm_ok", mips_asm_ok)

val () = export_theory ()
