(*
  Define the target compiler configuration for MIPS.
*)
open HolKernel Parse boolLib bossLib
open asmLib mips_stepTheory;

val () = new_theory "mips_target"

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
   mips_ok ms <=>
   ms.CP0.Config.BE /\ ~ms.CP0.Status.RE /\
   ms.CP0.Status.CU1 /\ ms.fcsr.ABS2008 /\ ~ms.fcsr.FS /\ (ms.fcsr.RM = 0w) /\
   (ms.BranchDelay = NONE) /\ (ms.BranchTo = NONE) /\
   ~ms.exceptionSignalled /\ (ms.exception = NoException) /\ aligned 2 ms.PC`

(* --- Encode ASM instructions to MIPS bytes. --- *)

val nop = ``Shift (SLL (0w, 0w, 0w))``

val mips_encode_fail_def = Define `mips_encode_fail = [^nop]`

val mips_encode_def = Define`
   mips_encode i =
   let w = mips$Encode i in
     [(31 >< 24) w; (23 >< 16) w; (15 >< 8) w; (7 >< 0) w] : word8 list`

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
   (mips_sh Asr = DSRA) /\
   (mips_sh _   = DSRA)`

val mips_sh32_def = Define`
   (mips_sh32 Lsl = DSLL32) /\
   (mips_sh32 Lsr = DSRL32) /\
   (mips_sh32 Asr = DSRA32) /\
   (mips_sh32 _   = DSRA32)`

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

val mips_fp_cmp_def = Define`
   mips_fp_cmp c n d1 d2 =
     [COP1 (C_cond_D (n2w d1, n2w d2, c, 0w));
      ArithI (ORI (0w, n2w n, 1w));
      COP1 (MOVF (n2w n, 0w, 0w))]`

val eval = rhs o concl o EVAL
val min16 = eval ``sw2sw (INT_MINw: word16) : word64``
val max16 = eval ``sw2sw (INT_MAXw: word16) : word64``
val min18 = eval ``sw2sw (INT_MINw: 18 word) : word64``
val max18 = eval ``sw2sw (INT_MAXw: 18 word) : word64``
val min32 = eval ``sw2sw (INT_MINw: 32 word) : word64``
val max32 = eval ``sw2sw (INT_MAXw: 32 word) : word64``
val umax16 = eval ``w2w (UINT_MAXw: word16) : word64``

val () = Parse.temp_overload_on ("temp_reg", ``1w : word5``)
val () = Parse.temp_overload_on ("temp_reg2", ``30w : word5``)

val mips_ast_def = Define`
   (mips_ast (Inst Skip) = [^nop]) /\
   (mips_ast (Inst (Const r (i: word64))) =
      let top    = (63 >< 32) i : word32
      and middle = (31 >< 16) i : word16
      and bottom = (15 ><  0) i : word16
      in
         if (top = 0w) /\ (middle = 0w) then
            [ArithI (ORI (0w, n2w r, bottom))]
         else if (top = -1w) /\ (middle = -1w) /\ bottom ' 15 then
            [ArithI (ADDIU (0w, n2w r, bottom))]
         else if (top = 0w) /\ ~middle ' 15 \/ (top = -1w) /\ middle ' 15 then
            [ArithI (LUI (n2w r, middle));
             ArithI (XORI (n2w r, n2w r, bottom))]
         else
            [ArithI (LUI (n2w r, (31 >< 16) top));
             ArithI (ORI (n2w r, n2w r, (15 >< 0) top));
             Shift (DSLL (n2w r, n2w r, 16w));
             ArithI (ORI (n2w r, n2w r, middle));
             Shift (DSLL (n2w r, n2w r, 16w));
             ArithI (ORI (n2w r, n2w r, bottom))]) /\
   (mips_ast (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
       [ArithR (mips_bop_r bop (n2w r2, n2w r3, n2w r1))]) /\
   (mips_ast (Inst (Arith (Binop Sub r1 r2 (Imm i)))) =
       [ArithI (DADDIU (n2w r2, n2w r1, -(w2w i)))]) /\
   (mips_ast (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       if (bop = Xor) /\ (i = -1w) then
         [ArithR (NOR (n2w r2, 0w, n2w r1))]
       else
         [ArithI (mips_bop_i bop (n2w r2, n2w r1, w2w i))]) /\
   (mips_ast (Inst (Arith (Shift sh r1 r2 n))) =
       if sh = Ror then
         if n < 32 then
           [Shift (DSRL (n2w r2, temp_reg, n2w n));
            Shift (DSLL32 (n2w r2, n2w r1, n2w (32 - n)));
            ArithR (OR (n2w r1, temp_reg, n2w r1))]
         else if n = 32 then
           [Shift (DSRL32 (n2w r2, temp_reg, 0w));
            Shift (DSLL32 (n2w r2, n2w r1, 0w));
            ArithR (OR (n2w r1, temp_reg, n2w r1))]
         else
           [Shift (DSRL32 (n2w r2, temp_reg, n2w (n - 32)));
            Shift (DSLL (n2w r2, n2w r1, n2w (64 - n)));
            ArithR (OR (n2w r1, temp_reg, n2w r1))]
       else
         let (f, n) = if n < 32 then (mips_sh, n) else (mips_sh32, n - 32) in
           [Shift (f sh (n2w r2, n2w r1, n2w n))]) /\
   (mips_ast (Inst (Arith (Div r1 r2 r3))) =
       [MultDiv (DDIV (n2w r2, n2w r3));
        MultDiv (MFLO (n2w r1))]) /\
   (mips_ast (Inst (Arith (LongMul r1 r2 r3 r4))) =
       [MultDiv (DMULTU (n2w r3, n2w r4));
        MultDiv (MFHI (n2w r1));
        MultDiv (MFLO (n2w r2))]) /\
   (mips_ast (Inst (Arith (LongDiv _ _ _ _ _))) = mips_encode_fail) /\
   (mips_ast (Inst (Arith (AddCarry r1 r2 r3 r4))) =
       [ArithR (SLTU (0w, n2w r4, temp_reg));
        ArithR (DADDU (n2w r2, n2w r3, n2w r1));
        ArithR (SLTU (n2w r1, n2w r3, n2w r4));
        ArithR (DADDU (n2w r1, temp_reg, n2w r1));
        ArithR (SLTU (n2w r1, temp_reg, temp_reg));
        ArithR (OR (n2w r4, temp_reg, n2w r4))]) /\
   (mips_ast (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
       [ArithR (XOR (n2w r2, n2w r3, temp_reg));
        ArithR (NOR (temp_reg, 0w, temp_reg));
        ArithR (DADDU (n2w r2, n2w r3, n2w r1));
        ArithR (XOR (n2w r3, n2w r1, n2w r4));
        ArithR (AND (temp_reg, n2w r4, n2w r4));
        Shift (DSRL32 (n2w r4, n2w r4, 31w))]) /\
   (mips_ast (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
       [ArithR (XOR (n2w r2, n2w r3, temp_reg));
        ArithR (DSUBU (n2w r2, n2w r3, n2w r1));
        ArithR (XOR (n2w r3, n2w r1, n2w r4));
        ArithR (NOR (n2w r4, 0w, n2w r4));
        ArithR (AND (temp_reg, n2w r4, n2w r4));
        Shift (DSRL32 (n2w r4, n2w r4, 31w))]) /\
   (mips_ast (Inst (Mem mop r1 (Addr r2 a))) =
       case mips_memop mop of
          INL f => [Load (f (n2w r2, n2w r1, w2w a))]
        | INR f => [Store (f (n2w r2, n2w r1, w2w a))]) /\
   (mips_ast (Inst (FP (FPLess n d1 d2))) = mips_fp_cmp 4w n d1 d2) /\
   (mips_ast (Inst (FP (FPLessEqual n d1 d2))) = mips_fp_cmp 6w n d1 d2) /\
   (mips_ast (Inst (FP (FPEqual n d1 d2))) = mips_fp_cmp 2w n d1 d2) /\
   (mips_ast (Inst (FP (FPMov d1 d2))) = [COP1 (MOV_D (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP (FPAbs d1 d2))) = [COP1 (ABS_D (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP (FPNeg d1 d2))) = [COP1 (NEG_D (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP (FPSqrt d1 d2))) = [COP1 (SQRT_D (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP (FPAdd d1 d2 d3))) =
       [COP1 (ADD_D (n2w d1, n2w d2, n2w d3))]) /\
   (mips_ast (Inst (FP (FPSub d1 d2 d3))) =
       [COP1 (SUB_D (n2w d1, n2w d2, n2w d3))]) /\
   (mips_ast (Inst (FP (FPMul d1 d2 d3))) =
       [COP1 (MUL_D (n2w d1, n2w d2, n2w d3))]) /\
   (mips_ast (Inst (FP (FPDiv d1 d2 d3))) =
       [COP1 (DIV_D (n2w d1, n2w d2, n2w d3))]) /\
   (mips_ast (Inst (FP (FPFma d1 d2 d3))) = [^nop]) /\
   (mips_ast (Inst (FP (FPMovToReg r _ d))) = [COP1 (DMFC1 (n2w r, n2w d))]) /\
   (mips_ast (Inst (FP (FPMovFromReg d r _))) =
       [COP1 (DMTC1 (n2w r, n2w d))]) /\
   (mips_ast (Inst (FP (FPToInt d1 d2))) =
       [COP1 (CVT_L_D (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP (FPFromInt d1 d2))) =
       [COP1 (CVT_D_L (n2w d1, n2w d2))]) /\
   (mips_ast (Inst (FP _ )) = mips_encode_fail) /\
   (mips_ast (Jump a) =
       if ^min18 + 4w <= a /\ a <= ^max18 + 4w then
         [Branch (BEQ (0w, 0w, w2w (a >>> 2) - 1w)); ^nop]
       else let b = a - 12w in
         [ArithI (ORI (31w, temp_reg2, 0w));              (* tmp2 := LR    *)
          Branch (BLTZAL (0w, 0w));                       (* LR := pc + 12 *)
          ArithI (LUI (temp_reg, (31 >< 16) b));
          ArithI (ORI (temp_reg, temp_reg, (15 >< 0) b)); (* tmp := a - 12 *)
          ArithR (DADDU (31w, temp_reg, temp_reg));       (* tmp := pc + a *)
          Branch (JR temp_reg);                           (* pc := tmp     *)
          ArithI (ORI (temp_reg2, 31w, 0w))]) /\          (* LR := tmp2    *)
   (mips_ast (JumpCmp c r1 (Reg r2) a) =
       let b = w2w (a >>> 2) - 2w in
         case mips_cmp c of
            (SOME (f1, _), f2) =>
               [ArithR (f1 (n2w r1, n2w r2, temp_reg));
                Branch (f2 (temp_reg, 0w, b));
                ^nop]
          | (NONE, f) => [Branch (f (n2w r1, n2w r2, b + 1w)); ^nop]) /\
   (mips_ast (JumpCmp c r (Imm i) a) =
       let b = w2w (a >>> 2) - 2w in
         case mips_cmp c of
            (SOME (_, f1), f2) =>
               [ArithI (f1 (n2w r, temp_reg, w2w i));
                Branch (f2 (temp_reg, 0w, b));
                ^nop]
          | (NONE, f) =>
               [ArithI (DADDIU (0w, temp_reg, w2w i));
                Branch (f (n2w r, temp_reg, b));
                ^nop]) /\
   (mips_ast (Call a) =
       if ^min18 + 4w <= a /\ a <= ^max18 + 4w then
         [Branch (BGEZAL (0w, w2w (a >>> 2) - 1w)); ^nop]
       else let b = a - 8w in
         [Branch (BLTZAL (0w, 0w));                       (* LR := pc + 8  *)
          ArithI (LUI (temp_reg, (31 >< 16) b));
          ArithI (ORI (temp_reg, temp_reg, (15 >< 0) b)); (* tmp := a - 8  *)
          ArithR (DADDU (31w, temp_reg, temp_reg));       (* tmp := pc + a *)
          Branch (JALR (temp_reg, 31w));                  (* pc := tmp     *)
          ^nop]) /\                                       (* LR := pc      *)
   (mips_ast (JumpReg r) = [Branch (JR (n2w r)); ^nop]) /\
   (mips_ast (Loc r i) =
       if r = 31 then
          if ^min16 + 8w <= i /\ i <= ^max16 + 8w then
            [Branch (BLTZAL (0w, 0w));                    (* LR := pc + 8    *)
             ArithI (DADDIU (31w, n2w r, w2w (i - 8w)))]  (* r := LR - 8 + i *)
          else let b = i - 8w in
            [Branch (BLTZAL (0w, 0w));                       (* LR := pc + 8  *)
             ArithI (LUI (temp_reg, (31 >< 16) b));
             ArithI (ORI (temp_reg, temp_reg, (15 >< 0) b)); (* tmp := i - 8  *)
             ArithR (DADDU (temp_reg, 31w, n2w r))]          (* r := tmp + LR *)
       else if ^min16 + 12w <= i /\ i <= ^max16 + 12w then
          [ArithI (ORI (31w, temp_reg, 0w));            (* tmp := LR        *)
           Branch (BLTZAL (0w, 0w));                    (* LR := pc + 12    *)
           ArithI (DADDIU (31w, n2w r, w2w (i - 12w))); (* r := LR - 12 + i *)
           ArithI (ORI (temp_reg, 31w, 0w))]            (* LR := tmp        *)
       else let b = i - 12w in
          [ArithI (ORI (31w, temp_reg, 0w));          (* tmp := LR    *)
           Branch (BLTZAL (0w, 0w));                  (* LR := pc + 12 *)
           ArithI (LUI (n2w r, (31 >< 16) b));
           ArithI (ORI (n2w r, n2w r, (15 >< 0) b));  (* r := i - 12  *)
           ArithR (DADDU (n2w r, 31w, n2w r));        (* r := pc + i  *)
           ArithI (ORI (temp_reg, 31w, 0w))])`        (* LR := tmp    *)

val mips_enc_def = zDefine`
  mips_enc = combin$C LIST_BIND mips_encode o mips_ast`

(* --- Configuration for MIPS --- *)

val mips_config_def = Define`
   mips_config =
   <| ISA := MIPS
    ; encode := mips_enc
    ; reg_count := 32
    ; fp_reg_count := 0 (* 32 *)
    ; avoid_regs := [0; 1; 25; 26; 27; 28; 29; 30]
    ; link_reg := SOME 31
    ; two_reg_arith := F
    ; big_endian := T
    ; valid_imm :=
       (\b i. if b IN {INL And; INL Or; INL Xor; INR Test; INR NotTest} then
                0w <= i /\ i <= ^umax16
              else (if b = INL Sub then ^min16 < i else ^min16 <= i) /\
                   i <= ^max16)
    ; addr_offset := (^min16, ^max16)
    ; byte_offset := (^min16, ^max16)
    ; jump_offset := (^min32 + 12w, ^max32 + 8w)
    ; cjump_offset := (^min18 + 8w, ^max18 + 4w)
    ; loc_offset := (^min32 + 12w, ^max32 + 8w)
    ; code_alignment := 2
    |>`

val mips_proj_def = Define`
   mips_proj d s =
   (s.CP0.Config, s.CP0.Status.RE,
    s.CP0.Status.CU1, s.fcsr.ABS2008, s.fcsr.FS, s.fcsr.RM, s.fcsr.FCC,
    s.exceptionSignalled, s.BranchDelay, s.BranchTo, s.exception, s.gpr,
    s.lo, s.hi, s.FGR, fun2set (s.MEM,d), s.PC)`

val mips_target_def = Define`
   mips_target =
   <| next := mips_next
    ; config := mips_config
    ; get_pc := mips_state_PC
    ; get_reg := (\s. mips_state_gpr s o n2w)
    ; get_fp_reg := (\s. s.FGR o n2w)
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
