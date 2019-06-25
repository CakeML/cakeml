(*
  Define the target compiler configuration for x64.
*)
open HolKernel Parse boolLib bossLib
open asmLib x64_stepTheory;

val () = new_theory "x64_target"

val () = wordsLib.guess_lengths()

(* --- The next-state function --- *)

val x64_next_def = Define `x64_next = THE o NextStateX64`

(* --- Valid x64 states --- *)

(* All floating-point exceptions are masked; don't flush to zero and denormals
   are not treated as zero. Rounding mode is TiesToEven *)

val x64_ok_def = Define`
  x64_ok ms = (~ms.MXCSR.FZ /\ ms.MXCSR.PM /\ ms.MXCSR.UM /\ ms.MXCSR.OM /\
                ms.MXCSR.ZM /\ ms.MXCSR.DM /\ ms.MXCSR.IM /\ ~ms.MXCSR.DAZ /\
                (ms.MXCSR.RC = 0w) /\ (ms.exception = NoException))`

(* --- Encode ASM instructions to x86-64 bytes. --- *)

val total_num2Zreg_def = Define`
  total_num2Zreg n = if n < 16 then num2Zreg n else RAX`

val () = Parse.temp_overload_on ("reg", ``\r. Zr (total_num2Zreg r)``)
val () = Parse.temp_overload_on ("xr", ``\r. xmm_reg (n2w r)``)

val () = Parse.temp_overload_on
   ("ld",
    ``\r1 r2 a.
       Zr_rm (total_num2Zreg r1, Zm (NONE, ZregBase (total_num2Zreg r2), a))``)

val () = Parse.temp_overload_on
   ("st",
    ``\r1 r2 a.
       Zrm_r (Zm (NONE, ZregBase (total_num2Zreg r2), a), total_num2Zreg r1)``)

val x64_bop_def = Define`
   (x64_bop Add = Zadd) /\
   (x64_bop Sub = Zsub) /\
   (x64_bop And = Zand) /\
   (x64_bop Or  = Zor) /\
   (x64_bop Xor = Zxor)`

val x64_sh_def = Define`
   (x64_sh Lsl = Zshl) /\
   (x64_sh Lsr = Zshr) /\
   (x64_sh Asr = Zsar) /\
   (x64_sh Ror = Zror)`

val x64_cmp_def = Define`
   (x64_cmp Less  = Z_L) /\
   (x64_cmp Lower = Z_B) /\
   (x64_cmp Equal = Z_E) /\
   (x64_cmp Test  = Z_E) /\
   (x64_cmp NotLess  = Z_NL) /\
   (x64_cmp NotLower = Z_NB) /\
   (x64_cmp NotEqual = Z_NE) /\
   (x64_cmp NotTest  = Z_NE)`

val x64_ast_def = Define`
   (x64_ast (Inst Skip) = [Znop(1)]) /\
   (x64_ast (Inst (Const r i)) =
      let sz = if (63 >< 31) i = 0w: 33 word then Z32 else Z64
      in
        [Zmov (Z_ALWAYS, sz, Zrm_i (reg r, i))]) /\
   (x64_ast (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      let a = (Z64, Zrm_r (reg r1, total_num2Zreg r3))
      in
        [if (bop = Or) /\ (r2 = r3) then
           Zmov (Z_ALWAYS, a)
         else
           Zbinop (x64_bop bop, a)]) /\
   (x64_ast (Inst (Arith (Binop bop r _ (Imm i)))) =
      [if (bop = Xor) /\ (i = -1w) then
         Zmonop (Znot, Z64, reg r)
       else
         Zbinop (x64_bop bop, Z64, Zrm_i (reg r, i))]) /\
   (x64_ast (Inst (Arith (Shift sh r _ n))) =
      [Zbinop (x64_sh sh, Z64, Zrm_i (reg r, n2w n))]) /\
   (x64_ast (Inst (Arith (Div _ _ _))) = []) /\
   (x64_ast (Inst (Arith (LongMul _ _ _ r))) = [Zmul (Z64, reg r)]) /\
   (x64_ast (Inst (Arith (LongDiv _ _ _ _ r))) = [Zdiv (Z64, reg r)]) /\
   (x64_ast (Inst (Arith (AddCarry r1 r2 r3 r4))) =
      [Zbinop (Zcmp, Z64, Zrm_i (reg r4, 1w));
       Zcmc;
       Zbinop (Zadc, Z64, Zrm_r (reg r1, total_num2Zreg r3));
       Zmov (Z_ALWAYS, Z32, Zrm_i (reg r4, 0w));
       Zset (Z_B, T, reg r4)]) /\
   (x64_ast (Inst (Arith (AddOverflow r1 _ r2 r3))) =
      [Zbinop (Zadd, Z64, Zrm_r (reg r1, total_num2Zreg r2));
       Zmov (Z_ALWAYS, Z32, Zrm_i (reg r3, 0w));
       Zset (Z_O, T, reg r3)]) /\
   (x64_ast (Inst (Arith (SubOverflow r1 _ r2 r3))) =
      [Zbinop (Zsub, Z64, Zrm_r (reg r1, total_num2Zreg r2));
       Zmov (Z_ALWAYS, Z32, Zrm_i (reg r3, 0w));
       Zset (Z_O, T, reg r3)]) /\
   (x64_ast (Inst (Mem Load r1 (Addr r2 a))) =
      [Zmov (Z_ALWAYS, Z64, ld r1 r2 a)]) /\
   (*
   (x64_ast (Inst (Mem Load32 r1 (Addr r2 a))) =
      [Zmov (Z_ALWAYS, Z32, ld r1 r2 a)]) /\
   *)
   (x64_ast (Inst (Mem Load8 r1 (Addr r2 a))) =
      [Zmovzx (Z8 T, ld r1 r2 a, Z64)]) /\
   (x64_ast (Inst (Mem Store r1 (Addr r2 a))) =
      [Zmov (Z_ALWAYS, Z64, st r1 r2 a)]) /\
   (*
   (x64_ast (Inst (Mem Store32 r1 (Addr r2 a))) =
      [Zmov (Z_ALWAYS, Z32, st r1 r2 a)]) /\
   *)
   (x64_ast (Inst (Mem Store8 r1 (Addr r2 a))) =
      [Zmov (Z_ALWAYS, Z8 (3 < r1), st r1 r2 a)]) /\
(**)
   (x64_ast (Inst (FP (FPLess n d1 d2))) =
     [SSE (COMISD (n2w d1, xr d2));
      Zmov (Z_ALWAYS, Z32, Zrm_i (reg n, 0w));
      Zjcc (Z_P, 4w);
      Zset (Z_B, T, reg n)]) /\
   (x64_ast (Inst (FP (FPLessEqual n d1 d2))) =
     [SSE (COMISD (n2w d1, xr d2));
      Zmov (Z_ALWAYS, Z32, Zrm_i (reg n, 0w));
      Zjcc (Z_P, 4w);
      Zset (Z_NA, T, reg n)]) /\
   (x64_ast (Inst (FP (FPEqual n d1 d2))) =
     [SSE (COMISD (n2w d1, xr d2));
      Zmov (Z_ALWAYS, Z32, Zrm_i (reg n, 0w));
      Zjcc (Z_P, 4w);
      Zset (Z_E, T, reg n)]) /\
   (x64_ast (Inst (FP (FPMov d1 d2))) = [SSE (MOVSD (xr d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPAbs d1 d2))) =
     [SSE (PCMPEQQ (n2w d1, xr d1));
      SSE (PSRLQ_imm (n2w d1, 1w));
      SSE (logic_PD (sse_and, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPNeg d1 d2))) =
     [SSE (PCMPEQQ (n2w d1, xr d1));
      SSE (PSLLQ_imm (n2w d1, 63w));
      SSE (logic_PD (sse_xor, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPSqrt d1 d2))) = [SSE (SQRTSD (n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPAdd d1 _ d2))) =
     [SSE (bin_SD (sse_add, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPSub d1 _ d2))) =
     [SSE (bin_SD (sse_sub, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPMul d1 _ d2))) =
     [SSE (bin_SD (sse_mul, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPDiv d1 _ d2))) =
     [SSE (bin_SD (sse_div, n2w d1, xr d2))]) /\
   (x64_ast (Inst (FP (FPFma _ _ _))) =
    [Znop(1)]) /\
   (x64_ast (Inst (FP (FPMovToReg r1 r2 d))) =
     [SSE (MOV_D_Q (F, T, n2w d, reg r1))]) /\
   (x64_ast (Inst (FP (FPMovFromReg d r1 r2))) =
     [SSE (MOV_D_Q (T, T, n2w d, reg r1))]) /\
   (x64_ast (Inst (FP (FPToInt d1 d2))) =
     [SSE (CVTPD2DQ (F, n2w d1, xr d2));
      SSE (PSLLDQ (n2w d1, 12w));
      SSE (PSRLDQ (n2w d1, 12w))]) /\
   (x64_ast (Inst (FP (FPFromInt d1 d2))) =
     [SSE (CVTDQ2PD (n2w d1, xr d2))]) /\
(**)
   (x64_ast (Jump a) = [Zjcc (Z_ALWAYS, a - 5w)]) /\
   (x64_ast (JumpCmp cmp r1 (Reg r2) a) =
      [Zbinop (if is_test cmp then Ztest else Zcmp, Z64,
               Zrm_r (reg r1, total_num2Zreg r2));
       Zjcc (x64_cmp cmp, a - 9w)]) /\
   (x64_ast (JumpCmp cmp r (Imm i) a) =
      let width =
        if ~is_test cmp /\ 0xFFFFFFFFFFFFFF80w <= i /\ i <= 0x7Fw then
           10w
        else if r = 0 then
           12w
        else
           13w
      in
        [Zbinop (if is_test cmp then Ztest else Zcmp, Z64, Zrm_i (reg r, i));
         Zjcc (x64_cmp cmp, a - width)]) /\
   (x64_ast (Call _) = []) /\
   (x64_ast (JumpReg r) = [Zjmp (reg r)]) /\
   (x64_ast (Loc r i) =
      [Zlea (Z64, Zr_rm (total_num2Zreg r, Zm (NONE, (ZripBase, i - 7w))))])`

(* Avoid x64$encode when encoding jcc because it can produce short jumps. *)
val x64_encode_def = Define`
  (x64_encode (Zjcc (cond, imm)) =
     if cond = Z_ALWAYS then
        0xE9w :: e_imm32 imm
     else if cond = Z_P then (* short branch for floating-point compares *)
        x64$encode (Zjcc (cond, imm))
     else
        [0x0Fw; 0x80w || n2w (Zcond2num cond)] ++ e_imm32 imm) /\
  (x64_encode i = x64$encode i)`;

val x64_dec_fail_def = zDefine `x64_dec_fail = [0w] : word8 list`

val x64_enc_def = Define`
  x64_enc i =
  case LIST_BIND (x64_ast i) x64_encode of
     [] => x64_dec_fail
   | l => l`

(* --- Configuration for x86-64 --- *)

val eval = rhs o concl o EVAL
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``
val max32 = eval ``sw2sw (INT_MAXw: word32) : word64``

val x64_config_def = Define`
   x64_config =
   <| ISA := x86_64
    ; encode := x64_enc
    ; reg_count := 16
    ; fp_reg_count := 8
    ; avoid_regs := [4;5]
    ; link_reg := NONE
    ; two_reg_arith := T
    ; big_endian := F
    ; valid_imm := \b i. ^min32 <= i /\ i <= ^max32
    ; addr_offset := (^min32, ^max32)
    ; byte_offset := (^min32, ^max32)
    ; jump_offset := (^min32 + 13w, ^max32 + 5w)
    ; cjump_offset := (^min32 + 13w, ^max32 + 5w)
    ; loc_offset := (^min32 + 7w, ^max32 + 7w)
    ; code_alignment := 0
    |>`

val x64_proj_def = Define`
   x64_proj d s =
   (s.RIP, s.REG, s.XMM_REG, fun2set (s.MEM, d), s.EFLAGS, s.MXCSR,
    s.exception)`

val x64_target_def = Define`
   x64_target =
   <| next := x64_next
    ; config := x64_config
    ; get_pc := x64_state_RIP
    ; get_reg := (\s. s.REG o num2Zreg)
    ; get_fp_reg := (\s n. (63 >< 0) (s.XMM_REG (n2w n)))
    ; get_byte := x64_state_MEM
    ; state_ok := x64_ok
    ; proj := x64_proj
    |>`

val (x64_config, x64_asm_ok) =
  asmLib.target_asm_rwts [alignmentTheory.aligned_0] ``x64_config``

val x64_config = save_thm("x64_config", x64_config)
val x64_asm_ok = save_thm("x64_asm_ok", x64_asm_ok)

val () = export_theory ()
