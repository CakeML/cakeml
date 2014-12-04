open HolKernel Parse boolLib bossLib
open lcsymtacs asmTheory asmLib x64_stepLib;

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
    ; avoid_regs := [4]
    ; link_reg := NONE
    ; has_delay_slot := F
    ; has_icache := T
    ; has_mem_32 := T
    ; two_reg_arith := T
    ; valid_imm := \b i. ^min32 <= i /\ i <= ^max32
    ; addr_offset_min := ^min32
    ; addr_offset_max := ^max32
    ; jump_offset_min := ^min32 + 13w
    ; jump_offset_max := ^max32 + 5w
    ; cjump_offset_min := ^min32 + 13w
    ; cjump_offset_max := ^max32 + 5w
    ; loc_offset_min := ^min32 + 7w
    ; loc_offset_max := ^max32 + 7w
    ; code_alignment := 1
    |>`

(* --- The next-state function --- *)

val x64_next_def = Define `x64_next = THE o NextStateX64`

(* --- Relate ASM and x86-64 states --- *)

val x64_asm_state_def = Define`
   x64_asm_state a x =
   (x.exception = NoException) /\
   (!i. i < 16 ==> (a.regs i = x.REG (num2Zreg i))) /\
   (!i. case x.MEM i of
           SOME b => i IN a.mem_domain /\ (a.mem i = b)
         | NONE => i NOTIN a.mem_domain) /\
   IS_SOME a.icache /\
   (!i. case x.ICACHE i of
           SOME b => i IN a.mem_domain /\ (THE a.icache i = b)
         | NONE => i NOTIN a.mem_domain) /\
   (a.pc = x.RIP)`

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
   (x64_cmp _     = Z_E)`

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
       x64$encode (Zbinop (x64_bop bop, Z64, Zrm_r (reg r1, num2Zreg r3)))) /\
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
   (x64_enc (Jump _ (SOME _)) = []) /\
   (x64_enc (Jump a NONE) = x64_encode_jcc Z_ALWAYS (a - 5w)) /\
   (x64_enc (JumpCmp _ _ _ _ (SOME _)) = []) /\
   (x64_enc (JumpCmp cmp r1 (Reg r2) a NONE) =
       x64$encode (Zbinop (if cmp = Test then Ztest else Zcmp, Z64,
                           Zrm_r (reg r1, num2Zreg r2))) ++
       x64_encode_jcc (x64_cmp cmp) (a - 9w)) /\
   (x64_enc (JumpCmp cmp r (Imm i) a NONE) =
       let width = if cmp <> Test /\ 0xFFFFFFFFFFFFFF80w <= i /\ i <= 0x7Fw then
                      10w
                   else if r = 0 then
                      12w
                   else
                      13w
       in
          x64$encode (Zbinop (if cmp = Test then Ztest else Zcmp, Z64,
                              Zrm_i (reg r, i))) ++
          x64_encode_jcc (x64_cmp cmp) (a - width)) /\
   (x64_enc (Call _) = []) /\
   (x64_enc (JumpReg r) = x64$encode (Zjmp (reg r))) /\
   (x64_enc (Loc r i) =
      x64$encode
        (Zlea (Z64, Zr_rm (num2Zreg r, Zm (NONE, (ZripBase, i - 7w)))))) /\
   (x64_enc Cache = x64$encode Zcpuid)`

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
   (x64_cmp_dec (Zcmp,  Z_E) = Equal)`

val fetch_decode_def = Define`
   fetch_decode l =
   case x64_decode (TAKE 20 l) of
      Zfull_inst (_, i, r) => (i, r ++ DROP 20 l)
    | _ => ARB`

val x64_dec_def = Define`
   x64_dec l =
   case fetch_decode l of
      (Zcpuid, _) => Cache
    | (Znop, _) => Inst Skip
    | (Zmov (Z_ALWAYS, _, Zrm_i (Zr r, i)), _) => Inst (Const (Zreg2num r) i)
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
                       JumpCmp (x64_cmp_dec (bop, c)) r1 (Reg r2) (a + 9w) NONE
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
                      let w = if cmp <> Test /\
                                 0xFFFFFFFFFFFFFF80w <= n /\ n <= 0x7Fw then
                                 10w
                              else if r1 = 0 then 12w else 13w
                      in
                         JumpCmp cmp r1 (Imm n) (a + w) NONE
                 | _ => ARB)
            else
               (case x64_bop_dec bop of
                   INL b => Inst (Arith (Binop b r1 r1 (Imm n)))
                 | INR b => Inst (Arith (Shift b r1 r1 (w2n n))))
    | (Zjcc (Z_ALWAYS, a), _) => Jump (a + 5w) NONE
    | (Zjmp (Zr r), _) => JumpReg (Zreg2num r)
    | (Zlea (Z64, Zr_rm (r, Zm (NONE, (ZripBase, i)))), _) =>
         Loc (Zreg2num r) (i + 7w)
    | _ => ARB`

(* ------------------------------------------------------------------------- *)

(* some lemmas ---------------------------------------------------------- *)

val Zreg2num_num2Zreg_imp =
   fst (Thm.EQ_IMP_RULE (SPEC_ALL x64Theory.Zreg2num_num2Zreg))

val const_lem1 =
   blastLib.BBLAST_PROVE ``!c: word64. 0w <= c ==> 0xFFFFFFFF80000000w <= c``

val const_lem2 = Q.prove(
   `!c: word64.
       [(7 >< 0) c; (15 >< 8) c; (23 >< 16) c; (31 >< 24) c]: word8 list =
       [( 7 ><  0) (w2w c : word32); (15 ><  8) (w2w c : word32);
        (23 >< 16) (w2w c : word32); (31 >< 24) (w2w c : word32)]`,
   simp [] \\ blastLib.BBLAST_TAC)

val const_lem3 =
   Thm.CONJ
      (blastLib.BBLAST_PROVE
         ``word_bit 3 (r: word4) \/ ((3 >< 3) r = 1w: word1) ==>
           ((1w: word1) @@ (v2w [r ' 2; r ' 1; r ' 0]: word3) = r)``)
      (blastLib.BBLAST_PROVE
         ``~word_bit 3 (r: word4) \/ ((3 >< 3) r = 0w: word1) ==>
           ((0w: word1) @@ (v2w [r ' 2; r ' 1; r ' 0]: word3) = r)``)

val const_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0w <= c /\ c <= 0x7FFFFFFFw ==>
          ((31 >< 0) (0xFFFFFFFFw && sw2sw (w2w c: word32) : word64) = c)``

val jump_lem1 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFFBw /\
          c + 0xFFFFFFFFFFFFFFFBw <= 0x7FFFFFFFw``

val jump_lem2 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFFBw): word32) = c - 5w)``

val jump_lem3 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF7w /\
          c + 0xFFFFFFFFFFFFFFF7w <= 0x7FFFFFFFw``

val jump_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF6w /\
          c + 0xFFFFFFFFFFFFFFF6w <= 0x7FFFFFFFw``

val jump_lem5 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF4w /\
          c + 0xFFFFFFFFFFFFFFF4w <= 0x7FFFFFFFw``

val jump_lem6 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF3w /\
          c + 0xFFFFFFFFFFFFFFF3w <= 0x7FFFFFFFw``

val loc_lem1 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000007w <= c /\ c <= 0x80000006w ==>
          0xFFFFFFFF80000000w <= c + 0xFFFFFFFFFFFFFFF9w /\
          c + 0xFFFFFFFFFFFFFFF9w <= 0x7FFFFFFFw``

val loc_lem2 = blastLib.BBLAST_PROVE ``(a || 8w) <> 0w: word4``

val loc_lem3 =
   blastLib.BBLAST_PROVE
      ``(if r ' 3 then (1w: word1) else 0w) @@
        (v2w [r ' 2; r ' 1; r ' 0]: word3) = r: word4``

val loc_lem4 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000007w <= c /\ c <= 0x80000006w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFF9w): word32) = c - 7w)``

val binop_lem1 = Q.prove(
   `((if b then [x] else []) <> []) = b`,
   rw [])

val binop_lem5 = Q.prove(
   `!c: word64. [(7 >< 0) c]: word8 list = [I (w2w c : word8)]`,
   simp [] \\ blastLib.BBLAST_TAC)

val binop_lem6 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
          (sw2sw (w2w c: word8) = c)``

val binop_lem7 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw ==>
          (sw2sw (w2w c: word32) = c)``

val binop_lem8 = Q.prove(
   `!i. is_rax (reg i) = (RAX = num2Zreg i)`,
   strip_tac
   \\ wordsLib.Cases_on_word_value `num2Zreg i`
   \\ rw [x64Theory.is_rax_def])

val binop_lem9b = Q.prove(
   `!n. n < 64 ==>
        (0xFFFFFFFFFFFFFF80w: word64) <= n2w n /\ n2w n <= (0x7Fw: word64)`,
   lrw [wordsTheory.word_le_n2w]
   \\ `n < 2 ** 63` by simp []
   \\ simp [bitTheory.NOT_BIT_GT_TWOEXP]
   )

val binop_lem9 = Q.prove(
   `!i: word64 n.
       n < 64 /\ Abbrev (i = n2w n) ==>
       0xFFFFFFFFFFFFFF80w <= i /\ i <= 0x7Fw /\ i <+ 64w /\
       (w2n (w2w i: word6) = n)`,
   Cases
   \\ lrw [wordsTheory.word_le_n2w, wordsTheory.word_lo_n2w,
           wordsTheory.w2w_n2w]
   \\ `n' < 18446744073709551616` by decide_tac
   \\ fs [markerTheory.Abbrev_def]
   \\ `n' < 2 ** 63` by simp []
   \\ simp [bitTheory.NOT_BIT_GT_TWOEXP]
   )

val binop_lem10 =
   blastLib.BBLAST_PROVE
      ``!i: word64.
          i <+ 64w ==>
          ((5 >< 0) (sw2sw (w2w i : word8): word64) = w2w i: word6)``

val binop_lem11 = Q.prove(
   `!b x: word8. ((if b then [x] else []) <> []) = b`,
   rw []
   )

val case_mem_tm = ``!i. case state.MEM i of NONE => q | SOME b => r``
val case_icache_tm = ``!i. case state.ICACHE i of NONE => q | SOME b => r``

fun tac i =
   let
      val v = wordsSyntax.mk_wordii (i, 64)
      val tm = ``a + s.regs n + ^v: word64``
   in
      `state.MEM (a + state.REG (num2Zreg n) + ^v) = SOME (s.mem ^tm)`
      by (qpat_assum `^case_mem_tm` (qspec_then `^tm` assume_tac)
          \\ Cases_on `state.MEM ^tm` \\ fs[] \\ metis_tac [])
      \\ pop_assum (SUBST1_TAC o REWRITE_RULE [wordsTheory.WORD_ADD_0])
   end

val mem_lem1 = Q.prove(
   `!a n s state.
       x64_asm_state s state /\ n < 16 /\
       s.regs n + a IN s.mem_domain ==>
       (state.MEM (state.REG (num2Zreg n) + a) = SOME (s.mem (s.regs n + a)))`,
   rw [x64_asm_state_def]
   \\ qpat_assum `^case_mem_tm`
         (qspec_then `a + state.REG (num2Zreg n)` assume_tac)
   \\ Cases_on `state.MEM (a + state.REG (num2Zreg n))`
   \\ rfs []
   )

val mem_lem2 = Q.prove(
   `!a n s state.
    x64_asm_state s state /\ n < 16 /\
    a + s.regs n IN s.mem_domain /\
    a + s.regs n + 1w IN s.mem_domain /\
    a + s.regs n + 2w IN s.mem_domain /\
    a + s.regs n + 3w IN s.mem_domain ==>
    (read_mem32 state.MEM (state.REG (num2Zreg n) + a) =
     SOME (s.mem (s.regs n + a + 3w) @@
           s.mem (s.regs n + a + 2w) @@
           s.mem (s.regs n + a + 1w) @@
           s.mem (s.regs n + a)))`,
   rw [x64_asm_state_def, x64_stepTheory.read_mem32_def]
   \\ EVERY (List.tabulate (4, tac))
   \\ fs [])

val mem_lem3 = Q.prove(
   `!a n s state.
    x64_asm_state s state /\ n < 16 /\
    a + s.regs n IN s.mem_domain /\
    a + s.regs n + 1w IN s.mem_domain /\
    a + s.regs n + 2w IN s.mem_domain /\
    a + s.regs n + 3w IN s.mem_domain /\
    a + s.regs n + 4w IN s.mem_domain /\
    a + s.regs n + 5w IN s.mem_domain /\
    a + s.regs n + 6w IN s.mem_domain /\
    a + s.regs n + 7w IN s.mem_domain ==>
    (read_mem64 state.MEM (state.REG (num2Zreg n) + a) =
     SOME (s.mem (s.regs n + a + 7w) @@
           s.mem (s.regs n + a + 6w) @@
           s.mem (s.regs n + a + 5w) @@
           s.mem (s.regs n + a + 4w) @@
           s.mem (s.regs n + a + 3w) @@
           s.mem (s.regs n + a + 2w) @@
           s.mem (s.regs n + a + 1w) @@
           s.mem (s.regs n + a)))`,
   rw [x64_asm_state_def, x64_stepTheory.read_mem64_def]
   \\ EVERY (List.tabulate (8, tac))
   \\ fs [])

val mem_lem4 =
   blastLib.BBLAST_PROVE
      ``!r: word4.
          (if r ' 3 then 1w else 0w: word1) @@ ((2 >< 0) r : word3) = r``

val mem_lem5 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
          (sw2sw (w2w c: word8) = c)``

val mem_lem6 = Q.prove(
   `!r. (2 >< 0) r <> (4w: word3) /\ (2 >< 0) r <> (5w: word3) ==>
        (r = RegNot4or5 r)`,
   rw [x64_stepTheory.RegNot4or5_def])

val mem_lem7 = Q.prove(
   `!r. (2 >< 0) r <> (4w: word3) ==> (r = RegNot4 r)`,
   rw [x64_stepTheory.RegNot4_def])

val mem_lem8 = Q.prove(
   `!r:word4 n.
       ~(3 < n) /\ Abbrev (r = n2w n) ==>
       num2Zreg (w2n r) <> RSP /\
       num2Zreg (w2n r) <> RBP /\
       num2Zreg (w2n r) <> RSI /\
       num2Zreg (w2n r) <> RDI`,
   wordsLib.Cases_word_value
   \\ rw [x64Theory.num2Zreg_thm]
   \\ Cases_on `3 < n`
   \\ simp [markerTheory.Abbrev_def]
   )

val mem_lem9 = Q.prove(
   `!n r: word4.
      n < 16 /\ n <> 4 /\ Abbrev (r = n2w n) /\ ((2 >< 0) r = 4w: word3) ==>
      (zR12 = num2Zreg n)`,
   wordsLib.Cases_on_word_value `r`
   \\ rw []
   \\ rfs [markerTheory.Abbrev_def]
   \\ pop_assum (SUBST_ALL_TAC o SYM)
   \\ simp [x64Theory.num2Zreg_thm]
   )

val mem_lem10 = Q.prove(
   `!n r: word4.
      ~(n < 16 /\ n <> 4 /\ Abbrev (r = n2w n) /\ ((3 >< 3) r = (0w: word1)) /\
        ((2 >< 0) r = (4w: word3)))`,
   wordsLib.Cases_on_word_value `r`
   \\ rw [markerTheory.Abbrev_def]
   \\ Cases_on `n < 16`
   \\ simp []
   )

val mem_lem11 =
   blastLib.BBLAST_PROVE
      ``!r: word4. ((3 >< 3) r = (1w: word1)) ==> r ' 3``

val mem_lem12 =
   blastLib.BBLAST_PROVE
      ``!r: word4. ((3 >< 3) r = (0w: word1)) ==> ~r ' 3``

val mem_lem13 =
   blastLib.BBLAST_PROVE
      ``!a: word4. v2w [a ' 2; a ' 1; a ' 0] = (2 >< 0) a : word3``

val cmp_lem1 =
   blastLib.BBLAST_PROVE ``!a b: word64. (a + -1w * b = 0w) = (a = b)``

val cmp_lem2 =
   blastLib.BBLAST_PROVE
      ``!c: word64.
          0xFFFFFFFF8000000Dw <= c /\ c <= 0x80000004w ==>
          (sw2sw (w2w (c + 0xFFFFFFFFFFFFFFFBw): word32) = c - 5w)``

val cmp_lem3 =
   blastLib.BBLAST_PROVE
      ``!a b: word64.
          ((a + -1w * b) ' 63 <=/=>
           (a ' 63 <=/=> b ' 63) /\ ((a + -1w * b) ' 63 <=/=> a ' 63)) = a < b``

val cmp_lem4 = Q.prove(
   `!w: word64 a b.
      (7 >< 0) w :: a :: b : word8 list = I (w2w w : word8) :: a :: b`,
   simp [] \\ blastLib.BBLAST_TAC)

val cmp_lem5 = Q.prove(
   `!c: word64.
       0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw ==>
       ((if (7 >< 7) c = 1w: word8 then 0xFFFFFFFFFFFFFF00w else 0w) ||
         (7 >< 0) c = c)`,
   rw []
   \\ blastLib.FULL_BBLAST_TAC
   )

val cmp_lem6 = Q.prove(
   `!c: word64.
       0xFFFFFFFF80000000w <= c /\ c <= 0x7FFFFFFFw ==>
       ((if (31 >< 31) c = 1w: word32 then 0xFFFFFFFF00000000w else 0w) ||
         (31 >< 0) c = c)`,
   rw []
   \\ blastLib.FULL_BBLAST_TAC
   )

val cmp_lem7 = Q.prove(
   `!n. n < 16 ==> (is_rax (reg n) = (n = 0))`,
   rw [x64Theory.is_rax_def]
   \\ fs [wordsTheory.NUMERAL_LESS_THM, x64Theory.num2Zreg_thm]
   )

val dec_neq0 = blastLib.BBLAST_PROVE ``!x: word4. (x || 8w) <> 0w``

val is_rax_Zreg2num = Q.prove(
   `!n. n < 16 /\ is_rax (reg n) ==> (Zreg2num RAX = n)`,
   rw [x64Theory.is_rax_def]
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ rfs [x64Theory.num2Zreg_thm, x64Theory.Zreg2num_thm]
   )

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open x64Theory
   in
      [x64_enc_def, x64_bop_def, x64_cmp_def, x64_sh_def, x64_encode_jcc_def,
       encode_def, e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def, e_opsize_def,
       rex_prefix_def, e_opc_def, e_rm_imm8_def, e_opsize_imm_def,
       not_byte_def, e_rax_imm_def, e_rm_imm_def, e_imm_8_32_def, e_imm_def,
       e_imm8_def, e_imm16_def, e_imm32_def, e_imm64_def, Zsize_width_def,
       Zbinop_name2num_thm
       ]
   end

val enc_rwts =
  [x64_config_def, Zreg2num_num2Zreg_imp] @ encode_rwts @ asmLib.asm_ok_rwts @
  asmLib.asm_rwts

val enc_ok_rwts =
  encode_rwts @ asmLib.asm_ok_rwts @ [enc_ok_def, x64_config_def]

val dec_rwts =
   [x64_dec_def, fetch_decode_def, const_lem1, const_lem3, const_lem4,
    loc_lem3, loc_lem4, binop_lem6, binop_lem7, binop_lem8, binop_lem10,
    dec_neq0]

(* some custom tactics ---------------------------------------------------- *)

local
   val rip = ``state.RIP``
   val pc = ``s.pc: word64``
   fun mem_tac i =
      let
         val tm =
            if i = 0 then pc
            else wordsSyntax.mk_word_add (pc, wordsSyntax.mk_wordii (i, 64))
      in
         [qpat_assum `^case_mem_tm` (qspec_then `^tm` assume_tac)
          \\ Cases_on `state.MEM ^tm`,
          qpat_assum `^case_icache_tm` (qspec_then `^tm` assume_tac)
          \\ Cases_on `state.ICACHE ^tm`]
      end
   val w8 = ``:word8``
   fun bytes_in_memory_thm n =
      let
         val (b, r) =
            List.tabulate
               (n, fn i => let
                              val b = Term.mk_var ("b" ^ Int.toString i, w8)
                              val pc =
                                 if i = 0 then rip
                                 else wordsSyntax.mk_word_add
                                        (rip, wordsSyntax.mk_wordii (i, 64))
                           in
                              (b, ``(state.MEM ^pc = SOME ^b) /\
                                    (state.ICACHE ^pc = SOME ^b)``)
                           end) |> ListPair.unzip
          val l = listSyntax.mk_list (b, w8)
          val r = boolSyntax.list_mk_conj r
          val tacs = List.concat (List.tabulate (n, mem_tac))
      in
         Q.prove(
            `!s state.
               x64_asm_state s state /\
               bytes_in_memory s.pc ^l s.icache s.mem s.mem_domain ==>
               (state.exception = NoException) /\
               ^r`,
            rw [x64_asm_state_def, bytes_in_memory_def]
            \\ Cases_on `s.icache`
            \\ fs []
            >| tacs
            \\ fs []
            \\ rfs []
         ) |> Thm.GENL b
      end
   val bytes_in_memory_thm = utilsLib.cache 20 Int.compare bytes_in_memory_thm
   fun bytes_in_memory l = Drule.SPECL l (bytes_in_memory_thm (List.length l))
   fun dest_bytes_in_memory tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("asm$bytes_in_memory", [_, l, _, _, _]) =>
            SOME (fst (listSyntax.dest_list l))
       | _ => NONE
   fun gen_v P thm =
      let
         val vars = Term.free_vars (Thm.concl thm)
         val l = List.filter (P o fst o Term.dest_var) vars
      in
         Thm.GENL l thm
      end
   fun step P state =
      gen_v P o Q.INST [`s` |-> state] o Drule.DISCH_ALL o x64_stepLib.x64_step
   val (_, _, _, is_x64_decode) =
      HolKernel.syntax_fns "x64" 1 HolKernel.dest_monop HolKernel.mk_monop
                  "x64_decode"
   val find_x64_decode = Lib.total (HolKernel.find_term is_x64_decode)
in
   fun is_bytes_in_memory tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("asm$bytes_in_memory", [_, _, _, _, _]) => true
       | _ => false
   fun bytes_in_memory_tac (asl, g) =
      (case List.mapPartial dest_bytes_in_memory asl of
          [l] => imp_res_tac (bytes_in_memory l)
        | _ => NO_TAC) (asl, g)
   fun decode_tac thms (asl, g) =
      (case find_x64_decode g of
          SOME tm =>
           let
          (*  val () = (print_term tm; print "\n")  *)
              val dec_thm = x64_stepLib.x64_CONV tm
          (*  val () = (print_thm dec_thm; print "\n")  *)
           in
              imp_res_tac dec_thm
              \\ asm_simp_tac (srw_ss())
                   ([dec_thm, x64_bop_dec_def, is_rax_Zreg2num,
                     x64Theory.immediate32_def, x64Theory.immediate8_def,
                     const_lem1, const_lem3, const_lem4, loc_lem3, loc_lem4,
                     binop_lem6, binop_lem7, binop_lem8, binop_lem10,
                     blastLib.BBLAST_PROVE
                        ``(7 >< 0) (w:word64) = w2w w : word8``] @ thms)
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac pick P state (asl, g) =
      (case List.mapPartial dest_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step P state (pick l))) (asl, g)
end

val next_state_tac0 =
   next_state_tac hd (fn s => s = "v" orelse s = "wv") `state`
   \\ bytes_in_memory_tac
   \\ fs []

fun next_state_tac_cmp n =
   bytes_in_memory_tac
   \\ asmLib.split_bytes_in_memory_tac n
   \\ next_state_tac List.last (K false) `state`
   \\ rfs [const_lem2]
   \\ (fn (asl, g) =>
         let
            val tm = g |> rand |> rand |> rand
         in
            next_state_tac hd
              (fn s => Lib.mem s ["zflag", "cflag", "oflag", "sflag"])
              `^tm` (asl, g)
         end
      )
   \\ rev_full_simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss)
         [combinTheory.APPLY_UPDATE_THM]

val enc_ok_tac =
   full_simp_tac (srw_ss()++boolSimps.LET_ss)
      (offset_monotonic_def :: enc_ok_rwts)

fun next_tac n =
   qexists_tac n \\ simp [x64_next_def, numeralTheory.numeral_funpow]
fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

fun state_tac thms l =
   REPEAT (qpat_assum `NextStateX64 q = z` (K all_tac))
   \\ fs ([x64_asm_state_def, x64Theory.RexReg_def,
           x64_stepTheory.write_mem64_def, x64_stepTheory.write_mem32_def,
           const_lem1, const_lem3, const_lem4, loc_lem3, loc_lem4, binop_lem6,
           binop_lem7, binop_lem8, binop_lem10] @ thms)
   \\ map_every Q.UNABBREV_TAC l
   \\ rw [combinTheory.APPLY_UPDATE_THM, x64Theory.num2Zreg_11]

local
   fun rule rwt thm =
      if is_bytes_in_memory (Thm.concl thm)
         then PURE_ONCE_REWRITE_RULE [rwt] thm
      else thm
   val not_reg_tac =
      pop_assum (fn th => rule_assum_tac (rule th) \\ assume_tac (SYM th))
   fun highreg v tm =
       case Lib.total boolSyntax.dest_eq tm of
          SOME (l, r) =>
             (case Lib.total wordsSyntax.dest_word_extract l of
                 SOME (h, l, x, _) =>
                    if x = v andalso h = ``3n`` andalso l = ``3n``
                       then (case Lib.total wordsSyntax.uint_of_word r of
                                SOME 0 => SOME true
                              | SOME 1 => SOME false
                              | _ => NONE)
                    else NONE
               | NONE => NONE)
        | NONE => NONE
   fun high_low_reg v =
      fn asl =>
         case (Lib.mk_set o List.mapPartial (highreg v)) asl of
            [true] => (false, true)
          | [false] => (true, false)
          | _ => (false, false)
   val high_low_r1 = high_low_reg ``r1: word4``
   val high_low_r2 = high_low_reg ``r2: word4``
   fun ls_tac tac =
      next_state_tac0
      \\ rfs [Abbr `r2`, mem_lem5, binop_lem7]
      \\ state_tac [mem_lem8] [`r1`]
      \\ tac
      \\ blastLib.BBLAST_TAC
   fun load_store_tac decode load (asl, g) =
      let
         val (high_r1, low_r1) = high_low_r1 asl
         val (high_r2, low_r2) = high_low_r2 asl
         val tac =
            if decode
               then decode_tac []
                    \\ rfs [Abbr `r2`, mem_lem5, binop_lem7]
                    \\ lfs [Abbr `r1`, mem_lem8, mem_lem13,
                            Zreg2num_num2Zreg_imp]
                    \\ blastLib.FULL_BBLAST_TAC
            else if load
               then ls_tac (qabbrev_tac `q = c + state.REG (num2Zreg n')`)
            else ls_tac (full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) [])
         fun tac2 not5 =
           Cases_on `(2 >< 0) r2 = 4w: word3`
           \\ fs enc_rwts
           >| [
              (if low_r2
                  then assume_tac (Q.SPECL [`n'`, `r2`] mem_lem10)
                       \\ rfs [Q.SPEC `T` markerTheory.Abbrev_def]
               else all_tac)
              \\ `zR12 = num2Zreg n'` by imp_res_tac mem_lem9
              \\ (if decode then simp dec_rwts else all_tac),
              (if not5
                  then `r2 = RegNot4or5 r2` by (fs [] \\ imp_res_tac mem_lem6)
               else `r2 = RegNot4 r2` by (fs [] \\ imp_res_tac mem_lem7))
              \\ (if decode
                     then pop_assum (fn th => SUBST1_TAC th
                                              \\ simp dec_rwts
                                              \\ ASSUME_TAC (SYM th))
                  else not_reg_tac)
           ]
           \\ rule_assum_tac (REWRITE_RULE [binop_lem5])
           \\ tac
      in
        (
         (if high_r1
             then `r1 ' 3` by imp_res_tac mem_lem11
          else if low_r1
             then `~r1 ' 3` by imp_res_tac mem_lem12
          else all_tac)
         \\ (if high_r2
                then `r2 ' 3` by imp_res_tac mem_lem11
             else if low_r2
                then `~r2 ' 3` by imp_res_tac mem_lem12
             else all_tac)
         \\ Cases_on `(c = 0w) /\ (2 >< 0) r2 <> 5w: word3`
         \\ asmLib.using_first 1 (fn thms => fs (loc_lem2 :: thms))
         >- tac2 true
         \\ pop_assum (K all_tac)
         \\ Cases_on `0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7Fw`
         \\ asmLib.using_first 1 (fn thms => fs thms)
         >- tac2 false
         \\ pop_assum (K all_tac)
         \\ fs [const_lem2]
         \\ tac2 false
        ) (asl, g)
      end
in
   val load_tac = load_store_tac false true
   val store_tac = load_store_tac false false
   val load_store_tac = load_store_tac true false
end

val cmp_tac =
   Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
   \\ asmLib.using_first 1
        (fn thms => fs ([const_lem2, jump_lem1, jump_lem4] @ thms))
   >- (
      rule_assum_tac (REWRITE_RULE [cmp_lem4])
      \\ next_state_tac_cmp 4
      \\ state_tac [cmp_lem1, cmp_lem3, cmp_lem5] [`r1`]
      \\ fs []
      \\ blastLib.FULL_BBLAST_TAC
      )
   \\ pop_assum (K all_tac)

fun decode_tac0 l =
   simp enc_rwts
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ decode_tac [x64Theory.RexReg_def]
   \\ map_every Q.UNABBREV_TAC l
   \\ lfs [Zreg2num_num2Zreg_imp]
   \\ blastLib.FULL_BBLAST_TAC

fun decode_tac1 l =
   simp ([jump_lem5, jump_lem6, cmp_lem7] @ dec_rwts)
   \\ decode_tac []
   \\ decode_tac []
   \\ map_every Q.UNABBREV_TAC l
   \\ lfs [Zreg2num_num2Zreg_imp, x64_cmp_dec_def, x64Theory.Zreg2num_thm]
   \\ blastLib.FULL_BBLAST_TAC

val decode_cmp_tac =
   Cases_on `0xFFFFFFFFFFFFFF80w <= c' /\ c' <= 0x7fw`
   \\ asmLib.using_first 1
        (fn thms => fs ([const_lem2, jump_lem1, jump_lem4] @ thms))
   >- (
      rule_assum_tac (REWRITE_RULE [cmp_lem4])
      \\ decode_tac1 [`r1`]
      )

(* -------------------------------------------------------------------------
   x64_asm_deterministic
   x64_backend_correct
   ------------------------------------------------------------------------- *)

val x64_encoding = Count.apply Q.prove (
   `!i. asm_ok i x64_config ==> !x. x64_dec (x64_enc i ++ x) = i`,
   Cases
   >- (
      (*
        --------------
          Inst
        --------------*)
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ decode_tac0 []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ qabbrev_tac `r = n2w n : word4`
         \\ Cases_on `0w <= c /\ c <= 0x7FFFFFFFw`
         \\ Cases_on `word_bit 3 r`
         \\ decode_tac0 [`r`]
         )
      >- (
         (*--------------
             Arith
           --------------*)
         Cases_on `a`
         \\ qabbrev_tac `r1 = n2w n : word4`
         \\ qabbrev_tac `r2 = n2w n0 : word4`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            >| [
               (* Reg *)
               qabbrev_tac `r3 = n2w n' : word4`
               \\ Cases_on `b`
               \\ decode_tac0 [`r2`, `r3`],
               (* Imm *)
               Cases_on `b`
               \\ (Cases_on `0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7fw`
                   \\ lfs ([loc_lem2, binop_lem1] @ enc_rwts)
                   >- decode_tac0 [`r1`, `r2`]
                   \\ Cases_on `is_rax (reg n0)`
                   >- decode_tac0 []
                   \\ decode_tac0 [`r1`, `r2`]
                  )
            ]
            )
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ qabbrev_tac `i = n2w n1 : word64`
            \\ Cases_on `s`
            \\ lfs ([loc_lem2] @ enc_rwts)
            \\ imp_res_tac binop_lem9
            \\ fs []
            \\ Cases_on `n1 = 1`
            \\ fs []
            \\ decode_tac0 [`i`, `r2`]
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ qabbrev_tac `r1 = n2w n : word4`
      \\ qabbrev_tac `r2 = n2w n' : word4`
      \\ strip_tac
      \\ `RexReg (r2 ' 3,(2 >< 0) r2) = num2Zreg n'`
      by (simp [mem_lem4, x64Theory.RexReg_def, Abbr `r2`] \\ fs enc_rwts)
      \\ `RexReg (r1 ' 3,(2 >< 0) r1) = num2Zreg n`
      by (simp [mem_lem4, x64Theory.RexReg_def, Abbr `r1`] \\ fs enc_rwts)
      \\ Cases_on `m`
      \\ lfs enc_rwts
      >- (
         (*
           --------------
             Load
           --------------*)
         print_tac "Load"
         \\ load_store_tac
         )
      >- (
         (*
           --------------
             Load8
           --------------*)
         print_tac "Load8"
         \\ load_store_tac
         )
      >- (
         (*
           --------------
             Load32
           --------------*)
         print_tac "Load32"
         \\ Cases_on `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
         >- (fs [] \\ load_store_tac)
         \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                    (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
         by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
         \\ qpat_assum `~(a /\ b)` (K all_tac)
         \\ load_store_tac
         )
      >- (
         (*
           --------------
             Store
           --------------*)
         print_tac "Store"
         \\ load_store_tac
         )
      >- (
         (*
           --------------
             Store8
           --------------*)
         print_tac "Store8"
         \\ wordsLib.Cases_on_word_value `(3 >< 3) r1: word1`
         >| [
            `3w <+ r1` by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ `3 < n` by rfs [Abbr `r1`, wordsTheory.word_lo_n2w],
            all_tac
         ]
         \\ wordsLib.Cases_on_word_value `(3 >< 3) r2: word1`
         >| [all_tac, all_tac, all_tac,
             Cases_on `3 < n` >| [all_tac, imp_res_tac mem_lem8]
         ]
         \\ load_store_tac
         )
         (*
           --------------
             Store32
           --------------*)
      \\ print_tac "Store32"
      \\ Cases_on `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
      >- (fs [] \\ load_store_tac)
      \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                 (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
      by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
      \\ qpat_assum `~(a /\ b)` (K all_tac)
      \\ load_store_tac
      )
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ Cases_on `o'`
      \\ lfs ([jump_lem1, const_lem2] @ enc_rwts)
      \\ decode_tac0 []
      )
   >- (
      (*
        --------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ REVERSE (Cases_on `o'`)
      >- fs enc_rwts
      \\ qabbrev_tac `r1 = n2w n : word4`
      \\ Cases_on `r`
      >- (
         (* Reg *)
         qabbrev_tac `r2 = n2w n' : word4`
         \\ Cases_on `c`
         \\ lfs ([jump_lem3, loc_lem2, x64Theory.Zcond2num_thm] @ enc_rwts)
         \\ REPEAT strip_tac
         \\ `RexReg (r1 ' 3,v2w [r1 ' 2; r1 ' 1; r1 ' 0]) = num2Zreg n`
         by (simp [mem_lem4, loc_lem3, x64Theory.RexReg_def, Abbr `r1`]
          \\ fs enc_rwts)
         \\ `RexReg (r2 ' 3,v2w [r2 ' 2; r2 ' 1; r2 ' 0]) = num2Zreg n'`
         by (simp [mem_lem4, loc_lem3, x64Theory.RexReg_def, Abbr `r2`]
             \\ fs enc_rwts)
         \\ decode_tac1 [`r1`, `r2`]
         )
         (* Imm *)
      \\ Cases_on `c`
      \\ lfs ([jump_lem3, loc_lem2, x64Theory.Zcond2num_thm] @ enc_rwts)
      \\ REPEAT strip_tac
      \\ `RexReg (r1 ' 3,v2w [r1 ' 2; r1 ' 1; r1 ' 0]) = num2Zreg n`
      by (simp [mem_lem4, loc_lem3, x64Theory.RexReg_def, Abbr `r1`]
          \\ fs enc_rwts)
      >| [decode_cmp_tac, decode_cmp_tac, decode_cmp_tac, all_tac]
      \\ (
         Cases_on `n = 0`
         \\ decode_tac1 [`r1`]
         )
      )
      (*
        --------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ fs enc_rwts
      )
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ qabbrev_tac `r = n2w n : word4`
      \\ lfs enc_rwts
      \\ wordsLib.Cases_on_word_value `(3 >< 3) r: word1`
      \\ lfs []
      \\ decode_tac0 [`r`]
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ qabbrev_tac `r = n2w n : word4`
      \\ lfs ([loc_lem1, loc_lem2, const_lem2] @ enc_rwts)
      \\ decode_tac0 [`r`]
      )
      (*
        --------------
          Cache
        --------------*)
   \\ print_tac "Cache"
   \\ simp (enc_rwts @ dec_rwts)
   \\ decode_tac []
   \\ rw []
   )

val x64_asm_deterministic = Q.store_thm("x64_asm_deterministic",
   `asm_deterministic x64_enc x64_config`,
   metis_tac [decoder_asm_deterministic, has_decoder_def, x64_encoding]
   )

val x64_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [x64_config_def] x64_asm_deterministic

val x64_backend_correct = Count.apply Q.store_thm ("x64_backend_correct",
   `backend_correct x64_enc x64_config x64_next x64_asm_state`,
   simp [backend_correct_def]
   \\ REVERSE conj_tac
   >| [
      rw [asm_step_def] \\ Cases_on `i`,
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
   >- (
      (*
        --------------
          Inst
        --------------*)
      next_tac `0`
      \\ Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ fs enc_rwts
         \\ next_state_tac0
         \\ state_tac [] []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ qabbrev_tac `r = n2w n : word4`
         \\ Cases_on `0w <= c /\ c <= 0x7FFFFFFFw`
         \\ Cases_on `word_bit 3 r`
         \\ asmLib.using_first 2
              (fn thms =>
                 lfs ([const_lem1, const_lem2] @ thms @ enc_rwts)
                 \\ next_state_tac0
                 \\ state_tac thms [`r`])
         )
      >- (
         (*--------------
             Arith
           --------------*)
         Cases_on `a`
         \\ qabbrev_tac `r1 = n2w n : word4`
         \\ qabbrev_tac `r2 = n2w n0 : word4`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            >| [
               (* Reg *)
               qabbrev_tac `r3 = n2w n' : word4`
               \\ Cases_on `b`
               \\ lfs ([loc_lem2] @ enc_rwts)
               \\ next_state_tac0
               \\ state_tac [] [`r1`, `r2`, `r3`],
               (* Imm *)
               Cases_on `b`
               \\ lfs ([loc_lem2, binop_lem1] @ enc_rwts)
               \\ (
                   Cases_on `0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7fw`
                   \\ asmLib.using_first 1 fs
                   >- (rule_assum_tac (REWRITE_RULE [binop_lem5])
                       \\ next_state_tac0
                       \\ state_tac [] [`r1`, `r2`])
                   \\ Cases_on `is_rax (reg n0)`
                   \\ fs [const_lem2]
                   \\ next_state_tac0
                   \\ state_tac [] [`r1`, `r2`]
                   )
            ]
            )
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ qabbrev_tac `i = n2w n1 : word64`
            \\ Cases_on `s`
            \\ lfs ([loc_lem2] @ enc_rwts)
            \\ imp_res_tac binop_lem9
            \\ fs []
            \\ Cases_on `n1 = 1`
            \\ fs []
            \\ rule_assum_tac (REWRITE_RULE [binop_lem5])
            \\ next_state_tac0
            \\ state_tac [] [`r1`, `r2`]
         )
         (*
           --------------
             Mem
           --------------*)
         \\ Cases_on `a`
         \\ qabbrev_tac `r1 = n2w n : word4`
         \\ qabbrev_tac `r2 = n2w n' : word4`
         \\ `RexReg (r2 ' 3,(2 >< 0) r2) = num2Zreg n'`
         by (simp [mem_lem4, x64Theory.RexReg_def, Abbr `r2`] \\ fs enc_rwts)
         \\ Cases_on `m`
         \\ lfs enc_rwts
         >- (
            (*
              --------------
                Load
              --------------*)
            print_tac "Load"
            \\ `read_mem64 state.MEM (state.REG (num2Zreg n') + c) =
                 SOME (s1.mem (s1.regs n' + c + 7w) @@
                       s1.mem (s1.regs n' + c + 6w) @@
                       s1.mem (s1.regs n' + c + 5w) @@
                       s1.mem (s1.regs n' + c + 4w) @@
                       s1.mem (s1.regs n' + c + 3w) @@
                       s1.mem (s1.regs n' + c + 2w) @@
                       s1.mem (s1.regs n' + c + 1w) @@
                       s1.mem (s1.regs n' + c))`
            by imp_res_tac (Q.SPECL [`c`, `n'`, `s1`, `state`] mem_lem3)
            \\ load_tac
            )
         >- (
            (*
              --------------
                Load8
              --------------*)
            print_tac "Load8"
            \\ `state.MEM (state.REG (num2Zreg n') + c) =
                SOME (s1.mem (s1.regs n' + c))`
            by metis_tac [mem_lem1, wordsTheory.WORD_ADD_COMM]
            \\ load_tac
            )
         >- (
            (*
              --------------
                Load32
              --------------*)
            print_tac "Load32"
            \\ `read_mem32 state.MEM (state.REG (num2Zreg n') + c) =
                 SOME (s1.mem (s1.regs n' + c + 3w) @@
                       s1.mem (s1.regs n' + c + 2w) @@
                       s1.mem (s1.regs n' + c + 1w) @@
                       s1.mem (s1.regs n' + c))`
            by imp_res_tac (Q.SPECL [`c`, `n'`, `s1`, `state`] mem_lem2)
            \\ Cases_on `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
            >- (fs [] \\ load_tac)
            \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                       (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
            by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
            \\ qpat_assum `~(a /\ b)` (K all_tac)
            \\ load_tac
            )
         >- (
            (*
              --------------
                Store
              --------------*)
            print_tac "Store"
            \\ `?wv. read_mem64 state.MEM (state.REG (num2Zreg n') + c) =
                     SOME wv`
            by metis_tac [mem_lem3]
            \\ store_tac
            )
         >- (
            (*
              --------------
                Store8
              --------------*)
            print_tac "Store8"
            \\ `?wv. state.MEM (state.REG (num2Zreg n') + c) = SOME wv`
            by metis_tac [mem_lem1, wordsTheory.WORD_ADD_COMM]
            \\ wordsLib.Cases_on_word_value `(3 >< 3) r1: word1`
            >| [
               `3w <+ r1` by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
               \\ `3 < n` by rfs [Abbr `r1`, wordsTheory.word_lo_n2w],
               all_tac
            ]
            \\ wordsLib.Cases_on_word_value `(3 >< 3) r2: word1`
            >| [all_tac, all_tac, all_tac,
                Cases_on `3 < n` >| [all_tac, imp_res_tac mem_lem8]
            ]
            \\ store_tac
            )
            (*
              --------------
                Store32
              --------------*)
         \\ print_tac "Store32"
         \\ `?wv. read_mem32 state.MEM (state.REG (num2Zreg n') + c) =
                  SOME wv`
         by metis_tac [mem_lem2]
         \\ Cases_on `((3 >< 3) r1 = 0w: word1) /\ ((3 >< 3) r2 = 0w: word1)`
         >- (fs [] \\ store_tac)
         \\ `(7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
                    (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)`
         by (pop_assum mp_tac \\ blastLib.BBLAST_TAC)
         \\ qpat_assum `~(a /\ b)` (K all_tac)
         \\ store_tac
      ) (* close Inst *)
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac `0`
      \\ Cases_on `o'`
      \\ lfs ([jump_lem1, const_lem2] @ enc_rwts)
      \\ next_state_tac0
      \\ state_tac [jump_lem2] []
      )
   >- (
      (*
        --------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ next_tac `1`
      \\ REVERSE (Cases_on `o'`)
      >- fs enc_rwts
      \\ qabbrev_tac `r1 = n2w n : word4`
      \\ Cases_on `r`
      >- (
         (* Reg *)
         qabbrev_tac `r2 = n2w n' : word4`
         \\ Cases_on `c`
         \\ lfs ([jump_lem3, loc_lem2, x64Theory.Zcond2num_thm] @ enc_rwts)
         \\ next_state_tac_cmp 3
         \\ state_tac [jump_lem2, cmp_lem1, cmp_lem3] [`r1`, `r2`]
         \\ blastLib.FULL_BBLAST_TAC
         )
         (* Imm *)
      \\ Cases_on `c`
      \\ lfs ([jump_lem3, loc_lem2, x64Theory.Zcond2num_thm] @ enc_rwts)
      >| [cmp_tac, cmp_tac, cmp_tac, all_tac]
      \\ (
         Cases_on `n = 0`
         \\ fs [const_lem2, jump_lem5, jump_lem6, cmp_lem7]
         >| [next_state_tac_cmp 6, next_state_tac_cmp 7]
         \\ state_tac [cmp_lem1, cmp_lem3, cmp_lem6, x64Theory.num2Zreg_thm]
                 [`r1`]
         \\ fs []
         \\ blastLib.FULL_BBLAST_TAC
         )
      )
      (*
        --------------
          no Call
        --------------*)
   >- fs enc_rwts
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac `0`
      \\ qabbrev_tac `r = n2w n : word4`
      \\ lfs enc_rwts
      \\ wordsLib.Cases_on_word_value `(3 >< 3) r: word1`
      \\ lfs []
      \\ next_state_tac0
      \\ state_tac [] [`r`]
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ next_tac `0`
      \\ qabbrev_tac `r = n2w n : word4`
      \\ lfs ([loc_lem1, loc_lem2, const_lem2] @ enc_rwts)
      \\ next_state_tac0
      \\ state_tac [] [`r`]
      )
   >- (
      (*
        --------------
          Cache
        --------------*)
      print_tac "Cache"
      \\ next_tac `0`
      \\ fs enc_rwts
      \\ next_state_tac0
      \\ state_tac [] []
      \\ fs [x64Theory.num2Zreg_thm, x64Theory.Zreg2num_thm,
             x64Theory.Zreg_EQ_Zreg, x64Theory.Zreg2num_num2Zreg]
      )
   >- (
      (*
        --------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ Cases_on `i`
      \\ enc_ok_tac
      \\ rw []
      \\ blastLib.FULL_BBLAST_TAC
      )
   >- (
      (*
        --------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ REVERSE (Cases_on `i`)
      >- enc_ok_tac
      \\ Cases_on `ri`
      >| [all_tac,
          Cases_on `cmp <> Test /\ 0xFFFFFFFFFFFFFF80w <= c /\ c <= 0x7fw`
          >| [all_tac, Cases_on `r = 0`]
      ]
      \\ enc_ok_tac
      \\ rw [jump_lem1, jump_lem3, jump_lem4, jump_lem5, jump_lem6]
      )
   >- (
      (*
        --------------
          no Call enc_ok
        --------------*)
      enc_ok_tac
      )
   >- (
      (*
        --------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ enc_ok_tac
      \\ rw [loc_lem1]
      )
      (*
        --------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [x64_asm_deterministic_config]
   )

val () = export_theory ()
