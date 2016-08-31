open HolKernel Parse boolLib bossLib
open asmLib x64Theory;

val () = new_theory "x64_target"

val () = wordsLib.guess_lengths()

(* --- The next-state function --- *)

val x64_next_def = Define `x64_next = THE o NextStateX64`

(* --- Relate ASM and x86-64 states --- *)

val x64_asm_state_def = Define`
   x64_asm_state s ms =
   (ms.exception = NoException) /\
   (!i. i < 16 ==> (s.regs i = ms.REG (num2Zreg i))) /\
   (fun2set (s.mem, s.mem_domain) = fun2set (ms.MEM, s.mem_domain)) /\
   (s.pc = ms.RIP)`

(* --- Encode ASM instructions to x86-64 bytes. --- *)

val total_num2Zreg_def = Define`
  total_num2Zreg n = if n < 16 then num2Zreg n else RAX`

val () = Parse.temp_overload_on ("reg", ``\r. Zr (total_num2Zreg r)``)

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
   (x64_sh Asr = Zsar)`

val x64_cmp_def = Define`
   (x64_cmp Less  = Z_L) /\
   (x64_cmp Lower = Z_B) /\
   (x64_cmp Equal = Z_E) /\
   (x64_cmp Test  = Z_E) /\
   (x64_cmp NotLess  = Z_NL) /\
   (x64_cmp NotLower = Z_NB) /\
   (x64_cmp NotEqual = Z_NE) /\
   (x64_cmp NotTest  = Z_NE)`

(* Avoid x64$encode when encoding jcc because it can produce short jumps. *)

val x64_encode_jcc_def = Define`
   x64_encode_jcc cond a =
     if cond = Z_ALWAYS then
        0xE9w :: e_imm32 a
     else
        [0x0Fw; 0x80w || n2w (Zcond2num cond)] ++ e_imm32 a`;

val x64_enc_def = Define`
   (x64_enc0 (Inst Skip) = x64$encode Znop) /\
   (x64_enc0 (Inst (Const r i)) =
      let sz = if (63 >< 31) i = 0w: 33 word then Z32 else Z64 in
      x64$encode (Zmov (Z_ALWAYS, sz, Zrm_i (reg r, i)))) /\
   (x64_enc0 (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      let a = (Z64, Zrm_r (reg r1, total_num2Zreg r3)) in
        x64$encode
          (if (bop = Or) /\ (r2 = r3) then Zmov (Z_ALWAYS, a)
           else Zbinop (x64_bop bop, a))) /\
   (x64_enc0 (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       x64$encode (Zbinop (x64_bop bop, Z64, Zrm_i (reg r1, i)))) /\
   (x64_enc0 (Inst (Arith (Shift sh r1 r2 n))) =
       x64$encode (Zbinop (x64_sh sh, Z64, Zrm_i (reg r1, n2w n)))) /\
   (x64_enc0 (Inst (Arith (LongMul _ _ _ r))) =
       x64$encode (Zmul (Z64, reg r))) /\
   (x64_enc0 (Inst (Arith (LongDiv _ _ _ _ r))) =
       x64$encode (Zdiv (Z64, reg r))) /\
   (x64_enc0 (Inst (Arith (AddCarry r1 r2 r3 r4))) =
       x64$encode (Zbinop (Zcmp, Z64, Zrm_i (reg r4, 1w))) ++
       x64$encode Zcmc ++
       x64$encode (Zbinop (Zadc, Z64, Zrm_r (reg r1, total_num2Zreg r3))) ++
       x64$encode (Zmov (Z_ALWAYS, Z32, Zrm_i (reg r4, 0w))) ++
       x64$encode (Zbinop (Zadc, Z64, Zrm_i (reg r4, 0w)))) /\
   (x64_enc0 (Inst (Mem Load r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z64, ld r1 r2 a))) /\
   (x64_enc0 (Inst (Mem Load32 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z32, ld r1 r2 a))) /\
   (x64_enc0 (Inst (Mem Load8 r1 (Addr r2 a))) =
       x64$encode (Zmovzx (Z8 T, ld r1 r2 a, Z64))) /\
   (x64_enc0 (Inst (Mem Store r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z64, st r1 r2 a))) /\
   (x64_enc0 (Inst (Mem Store32 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z32, st r1 r2 a))) /\
   (x64_enc0 (Inst (Mem Store8 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z8 (3 < r1), st r1 r2 a))) /\
   (x64_enc0 (Jump a) = x64_encode_jcc Z_ALWAYS (a - 5w)) /\
   (x64_enc0 (JumpCmp cmp r1 (Reg r2) a) =
       x64$encode (Zbinop (if is_test cmp then Ztest else Zcmp, Z64,
                           Zrm_r (reg r1, total_num2Zreg r2))) ++
       x64_encode_jcc (x64_cmp cmp) (a - 9w)) /\
   (x64_enc0 (JumpCmp cmp r (Imm i) a) =
       let width =
          if ~is_test cmp /\ 0xFFFFFFFFFFFFFF80w <= i /\ i <= 0x7Fw then
             10w
          else if r = 0 then
             12w
          else
             13w
       in
          x64$encode (Zbinop (if is_test cmp then Ztest else Zcmp, Z64,
                              Zrm_i (reg r, i))) ++
          x64_encode_jcc (x64_cmp cmp) (a - width)) /\
   (x64_enc0 (Call _) = []) /\
   (x64_enc0 (JumpReg r) = x64$encode (Zjmp (reg r))) /\
   (x64_enc0 (Loc r i) =
      x64$encode
        (Zlea (Z64, Zr_rm (total_num2Zreg r, Zm (NONE, (ZripBase, i - 7w))))))`

val x64_dec_fail_def = zDefine `x64_dec_fail = [0w: word8]`

val x64_enc_def = Define`
  x64_enc i = case x64_enc0 i of [] => x64_dec_fail | l => l`

(* --- Configuration for x86-64 --- *)

val eval = rhs o concl o EVAL
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``
val max32 = eval ``sw2sw (INT_MAXw: word32) : word64``

val x64_config_def = Define`
   x64_config =
   <| ISA := x86_64
    ; encode := x64_enc
    ; reg_count := 16
    ; avoid_regs := [4;5]
    ; link_reg := NONE
    ; has_mem_32 := T
    ; two_reg_arith := T
    ; big_endian := F
    ; valid_imm := \b i. ^min32 <= i /\ i <= ^max32
    ; addr_offset_min := ^min32
    ; addr_offset_max := ^max32
    ; jump_offset_min := ^min32 + 13w
    ; jump_offset_max := ^max32 + 5w
    ; cjump_offset_min := ^min32 + 13w
    ; cjump_offset_max := ^max32 + 5w
    ; loc_offset_min := ^min32 + 7w
    ; loc_offset_max := ^max32 + 7w
    ; code_alignment := 0
    |>`

val x64_proj_def = Define`
   x64_proj d s = (s.RIP, s.REG, fun2set (s.MEM, d), s.EFLAGS, s.exception)`

val x64_target_def = Define`
   x64_target =
   <| get_pc := x64_state_RIP
    ; get_reg := (\s. s.REG o num2Zreg)
    ; get_byte := x64_state_MEM
    ; state_ok := (\s. s.exception = NoException)
    ; state_rel := x64_asm_state
    ; proj := x64_proj
    ; next := x64_next
    ; config := x64_config
    |>`

val () = export_theory ()
