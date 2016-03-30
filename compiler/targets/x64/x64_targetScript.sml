open HolKernel Parse boolLib bossLib
open asmLib x64Theory;

val () = new_theory "x64_target"

val () = wordsLib.guess_lengths()

(* --- Configuration for x86-64 --- *)

val eval = rhs o concl o EVAL
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``
val max32 = eval ``sw2sw (INT_MAXw: word32) : word64``

val x64_config_def = Define`
   x64_config =
   <| ISA_name := "x64"
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

val () = Parse.temp_overload_on ("reg", ``\r. Zr (num2Zreg r)``)

val () = Parse.temp_overload_on
   ("ld",
    ``\r1 r2 a. Zr_rm (num2Zreg r1, Zm (NONE, ZregBase (num2Zreg r2), a))``)

val () = Parse.temp_overload_on
   ("st",
    ``\r1 r2 a. Zrm_r (Zm (NONE, ZregBase (num2Zreg r2), a), num2Zreg r1)``)

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
   (x64_enc (Inst Skip) = x64$encode Znop) /\
   (x64_enc (Inst (Const r i)) =
      let sz = if 0w <= i /\ i <= 0x7FFFFFFFw then Z32 else Z64
      in
         x64$encode (Zmov (Z_ALWAYS, sz, Zrm_i (reg r, i)))) /\
   (x64_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
      let a = (Z64, Zrm_r (reg r1, num2Zreg r3)) in
        x64$encode
          (if (bop = Or) /\ (r2 = r3) then Zmov (Z_ALWAYS, a)
           else Zbinop (x64_bop bop, a))) /\
   (x64_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       x64$encode (Zbinop (x64_bop bop, Z64, Zrm_i (reg r1, i)))) /\
   (x64_enc (Inst (Arith (Shift sh r1 r2 n))) =
       x64$encode (Zbinop (x64_sh sh, Z64, Zrm_i (reg r1, n2w n)))) /\
   (x64_enc (Inst (Mem Load r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z64, ld r1 r2 a))) /\
   (x64_enc (Inst (Mem Load32 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z32, ld r1 r2 a))) /\
   (x64_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
       x64$encode (Zmovzx (Z8 T, ld r1 r2 a, Z64))) /\
   (x64_enc (Inst (Mem Store r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z64, st r1 r2 a))) /\
   (x64_enc (Inst (Mem Store32 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z32, st r1 r2 a))) /\
   (x64_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
       x64$encode (Zmov (Z_ALWAYS, Z8 (3 < r1), st r1 r2 a))) /\
   (x64_enc (Jump a) = x64_encode_jcc Z_ALWAYS (a - 5w)) /\
   (x64_enc (JumpCmp cmp r1 (Reg r2) a) =
       x64$encode (Zbinop (if is_test cmp then Ztest else Zcmp, Z64,
                           Zrm_r (reg r1, num2Zreg r2))) ++
       x64_encode_jcc (x64_cmp cmp) (a - 9w)) /\
   (x64_enc (JumpCmp cmp r (Imm i) a) =
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
   (x64_enc (Call _) = []) /\
   (x64_enc (JumpReg r) = x64$encode (Zjmp (reg r))) /\
   (x64_enc (Loc r i) =
      x64$encode
        (Zlea (Z64, Zr_rm (num2Zreg r, Zm (NONE, (ZripBase, i - 7w))))))`

val x64_bop_dec_def = Define`
   (x64_bop_dec Zadd = INL Add) /\
   (x64_bop_dec Zsub = INL Sub) /\
   (x64_bop_dec Zand = INL And) /\
   (x64_bop_dec Zor  = INL Or) /\
   (x64_bop_dec Zxor = INL Xor) /\
   (x64_bop_dec Zshl = INR Lsl) /\
   (x64_bop_dec Zshr = INR Lsr) /\
   (x64_bop_dec Zsar = INR Asr)`

val x64_cmp_dec_def = Define`
   (x64_cmp_dec (Ztest, Z_E) = Test) /\
   (x64_cmp_dec (Zcmp,  Z_L) = Less) /\
   (x64_cmp_dec (Zcmp,  Z_B) = Lower) /\
   (x64_cmp_dec (Zcmp,  Z_E) = Equal) /\
   (x64_cmp_dec (Ztest, Z_NE) = NotTest) /\
   (x64_cmp_dec (Zcmp,  Z_NL) = NotLess) /\
   (x64_cmp_dec (Zcmp,  Z_NB) = NotLower) /\
   (x64_cmp_dec (Zcmp,  Z_NE) = NotEqual)`

val fetch_decode_def = Define`
   fetch_decode l =
   case x64_decode (TAKE 20 l) of
      Zfull_inst (_, i, SOME r) => (i, r ++ DROP 20 l)
    | _ => ARB`

val x64_dec_def = Define`
   x64_dec l =
   case fetch_decode l of
      (Znop, _) => Inst Skip
    | (Zmov (Z_ALWAYS, _, Zrm_i (Zr r, i)), _) => Inst (Const (Zreg2num r) i)
    | (Zmov (Z_ALWAYS, Z64, Zrm_r (Zr r1, r2)), _) =>
         let r2 = Zreg2num r2 in
            Inst (Arith (Binop Or (Zreg2num r1) r2 (Reg r2)))
    | (Zmov (Z_ALWAYS, sz, Zr_rm (r1, Zm (NONE, ZregBase r2, a))), _) =>
         Inst (Mem (if sz = Z64 then Load else Load32) (Zreg2num r1)
                   (Addr (Zreg2num r2) a))
    | (Zmovzx (Z8 T, Zr_rm (r1, Zm (NONE, ZregBase r2, a)), Z64), _) =>
         Inst (Mem Load8 (Zreg2num r1) (Addr (Zreg2num r2) a))
    | (Zmov (Z_ALWAYS, sz, Zrm_r (Zm (NONE, ZregBase r2, a), r1)), _) =>
         Inst (Mem (case sz of Z64 => Store | Z32 => Store32 | _ => Store8)
                   (Zreg2num r1) (Addr (Zreg2num r2) a))
    | (Zbinop (bop, Z64, Zrm_r (Zr r1, r2)), rest) =>
         let r1 = Zreg2num r1 and r2 = Zreg2num r2 in
            if (bop = Ztest) \/ (bop = Zcmp) then
               (case fetch_decode rest of
                   (Zjcc (c, a), _) =>
                       JumpCmp (x64_cmp_dec (bop, c)) r1 (Reg r2) (a + 9w)
                 | _ => ARB)
            else
               (case x64_bop_dec bop of
                   INL b => Inst (Arith (Binop b r1 r1 (Reg r2)))
                 | _ => ARB)
    | (Zbinop (bop, Z64, Zrm_i (Zr r1, n)), rest) =>
         let r1 = Zreg2num r1 in
            if (bop = Ztest) \/ (bop = Zcmp) then
               (case fetch_decode rest of
                   (Zjcc (c, a), _) =>
                      let cmp = x64_cmp_dec (bop, c) in
                      let w = if ~is_test cmp /\
                                 0xFFFFFFFFFFFFFF80w <= n /\ n <= 0x7Fw then
                                 10w
                              else if r1 = 0 then 12w else 13w
                      in
                         JumpCmp cmp r1 (Imm n) (a + w)
                 | _ => ARB)
            else
               (case x64_bop_dec bop of
                   INL b => Inst (Arith (Binop b r1 r1 (Imm n)))
                 | INR b => Inst (Arith (Shift b r1 r1 (w2n n))))
    | (Zjcc (Z_ALWAYS, a), _) => Jump (a + 5w)
    | (Zjmp (Zr r), _) => JumpReg (Zreg2num r)
    | (Zlea (Z64, Zr_rm (r, Zm (NONE, (ZripBase, i)))), _) =>
         Loc (Zreg2num r) (i + 7w)
    | _ => ARB`

val x64_proj_def = Define`
   x64_proj d s = (s.RIP, s.REG, fun2set (s.MEM, d), s.EFLAGS, s.exception)`

val x64_target_def = Define`
   x64_target =
   <| encode := x64_enc
    ; get_pc := x64_state_RIP
    ; get_reg := (\s. s.REG o num2Zreg)
    ; get_byte := x64_state_MEM
    ; state_ok := (\s. s.exception = NoException)
    ; state_rel := x64_asm_state
    ; proj := x64_proj
    ; next := x64_next
    ; config := x64_config
    |>`

val () = export_theory ()
