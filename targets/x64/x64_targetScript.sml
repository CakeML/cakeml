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

val tac =
   rewrite_tac [DECIDE ``~(3n < n) = n < 4``]
   \\ NTAC 3 strip_tac
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ rfs []

val sh_neq_lem = Q.prove(
   `!n1 n2.
      n1 < 64 /\ n2 < 64 /\ n1 <> n2 ==>
      ~((BIT 6 n1 = BIT 6 n2) /\ (BIT 5 n1 = BIT 5 n2) /\
        (BIT 4 n1 = BIT 4 n2) /\ (BIT 3 n1 = BIT 3 n2) /\
        (BIT 2 n1 = BIT 2 n2) /\ (BIT 1 n1 = BIT 1 n2) /\
        (BIT 0 n1 = BIT 0 n2))`,
   tac
   )

val reg_neq_lem = Q.prove(
   `!n1 n2.
      n1 < 16 /\ n2 < 16 /\ n1 <> n2 ==>
      ~((BIT 3 n1 = BIT 3 n2) /\ (BIT 2 n1 = BIT 2 n2) /\
        (BIT 1 n1 = BIT 1 n2) /\ (BIT 0 n1 = BIT 0 n2))`,
   tac
   )

val reg4_neq_lem = Q.prove(
   `!n1 n2.
      ~(3 < n1) /\ ~(3 < n2) /\ n1 <> n2 ==>
      ~((BIT 1 n1 = BIT 1 n2) /\ (BIT 0 n1 = BIT 0 n2))`,
   tac
   )

val reg4_neq_lem2 = Q.prove(
   `!n1 n2.
      ~(3 < n1) /\ 3 < n2 /\ n2 < 16 /\
      ((3 >< 3) (n2w n2: word4) = (0w: word1)) /\
      n1 <> n2 ==>
      ~((BIT 2 n1 = BIT 2 n2) /\ (BIT 1 n1 = BIT 1 n2) /\
        (BIT 0 n1 = BIT 0 n2))`,
   tac
   )

val bop_enc_lem = Q.prove(
   `!b. x64_bop b <> Ztest /\
        ~word_bit 3 (n2w (Zbinop_name2num (x64_bop b)) : word4)`,
   Cases
   \\ rw [x64_bop_def, x64Theory.Zbinop_name2num_thm]
   \\ EVAL_TAC
   )

val sh_enc_lem = Q.prove(
   `!s. x64_sh s <> Ztest /\
        word_bit 3 (n2w (Zbinop_name2num (x64_sh s)) : word4)`,
   Cases
   \\ rw [x64_sh_def, x64Theory.Zbinop_name2num_thm]
   \\ EVAL_TAC
   )

val sh_enc_lem2 = Q.prove(
   `!n. n < 64n /\ (n2w n = 1w: word64) ==> (n = 1)`,
   simp []
   \\ metis_tac [arithmeticTheory.LESS_MOD, arithmeticTheory.LESS_TRANS,
                 DECIDE ``64 < 18446744073709551616``]
   )

val cmp_enc_lem = Q.prove(
   `!c. x64_cmp c <> Z_ALWAYS`,
   Cases
   \\ rw [x64_cmp_def]
   )

val mem_enc_lem = Q.prove(
   `(case 0 of 0 => 0w | 1 => 1w | v => 2w: word2) = 0w`,
   simp []
   )

val mem_enc_lem2 = Q.prove(
   `!b. (if b then 1 else 4) IN {0; 1; 4}`,
   rw []
   )

val mem_enc_lem3 =
   blastLib.BBLAST_PROVE
     ``!r1 r2.
          ~(((3 >< 3) r1 = 0w) /\ ((3 >< 3) r2 = 0w)) ==>
          (7w && (0w: word1) @@ (3 >< 3) (r1: word4) @@
           (0w: word1) @@ (3 >< 3) (r2: word4)) <> (0w: word4)``

val mem_enc_lem4 = Q.prove(
   `!b l1 x.
      (case if b then [x] else [] of [] => (4, l1) | l2 => (1, l2)) =
      (if b then 1 else 4, if b then [x] else l1)`,
   rw []
   )

val mem_enc_lem5 = Q.prove(
   `!b x.
      (case (if b then 1 else 4) of 0 => x | 1 => 1w | _ => 2w) =
      if b then 1w else 2w`,
   rw []
   \\ fs []
   )

val concat_lems =
   blastLib.BBLAST_PROVE
      ``(!a b c. ((a: word4) @@ (b: word4) = ((a @@ c): word8)) = (b = c)) /\
        (!a b c. ((a: word2) @@ (b: word6) = ((a @@ c): word8)) = (b = c)) /\
        (!a b c. ((a: word3) @@ (b: word3) = ((c @@ b): word6)) = (a = c)) /\
        (!a b c. ((a: word1) @@ (b: word3) = ((a @@ c): word4)) = (b = c))``

val byte_neq =
   blastLib.BBLAST_PROVE
      ``!c1 c2: word64.
          c1 <> c2 /\
          0xFFFFFFFFFFFFFF80w <= c1 /\ c1 <= 0x7Fw /\
          0xFFFFFFFFFFFFFF80w <= c2 /\ c2 <= 0x7Fw ==>
          (7 >< 0) c1 <> (7 >< 0) c2: word8``

val byte_neq2 =
   blastLib.BBLAST_PROVE
      ``!c1 c2: word64.
          c1 <> c2 /\
          0xFFFFFFFF80000000w <= c1 /\ c1 <= 0x7FFFFFFFw /\
          0xFFFFFFFF80000000w <= c2 /\ c2 <= 0x7FFFFFFFw ==>
          (7 >< 0) c1 <> (7 >< 0) c2: word8 \/
          (15 >< 8) c1 <> (15 >< 8) c2: word8 \/
          (23 >< 16) c1 <> (23 >< 16) c2: word8 \/
          (31 >< 24) c1 <> (31 >< 24) c2: word8``

val byte_neq3 =
   blastLib.BBLAST_PROVE
      ``!c1 c2: word64.
          c1 <> c2 /\
          0w <= c1 /\ c1 <= 0x7FFFFFFFw /\
          0w <= c2 /\ c2 <= 0x7FFFFFFFw ==>
          (7 >< 0) c1 <> (7 >< 0) c2: word8 \/
          (15 >< 8) c1 <> (15 >< 8) c2: word8 \/
          (23 >< 16) c1 <> (23 >< 16) c2: word8 \/
          (31 >< 24) c1 <> (31 >< 24) c2: word8``

val byte_neq4 =
   blastLib.BBLAST_PROVE
      ``!c1 c2: word64.
          c1 <> c2  ==>
          (7 >< 0) c1 <> (7 >< 0) c2: word8 \/
          (15 >< 8) c1 <> (15 >< 8) c2: word8 \/
          (23 >< 16) c1 <> (23 >< 16) c2: word8 \/
          (31 >< 24) c1 <> (31 >< 24) c2: word8 \/
          (39 >< 32) c1 <> (39 >< 32) c2: word8 \/
          (47 >< 40) c1 <> (47 >< 40) c2: word8 \/
          (55 >< 48) c1 <> (55 >< 48) c2: word8 \/
          (63 >< 56) c1 <> (63 >< 56) c2: word8``

val byte_neq5 = Q.prove(
   `!b. (7w && (if b then 1w else 0w) = (0w: word4)) = ~b`,
   rw []
   )

val byte_neq6 = Q.prove(
   `!n1 n2.
      n1 < 16 /\ n2 < 16 /\
      (word_bit 3 (n2w n1: word4) = word_bit 3 (n2w n2: word4)) /\
      n1 <> n2 ==>
      (2 >< 0) (n2w n1: word4) <> (2 >< 0) (n2w n2: word4) : word3`,
   NTAC 3 strip_tac
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ rfs []
   )

val byte_neq7 =
   blastLib.BBLAST_PROVE
    ``((0w: word1) @@ (a: word1) @@ (0w: word1) @@ (b: word1) || (8w: word4) =
       (0w: word1) @@ (c: word1) @@ (0w: word1) @@ (d: word1) || (8w: word4)) =
      (a = c) /\ (b = d)``

val byte_neq8 = Q.prove(
   `!n. ~(3 < n) ==> ((3 >< 3) (n2w n : word4) = 0w: word1)`,
   REPEAT strip_tac
   \\ fs [wordsTheory.NUMERAL_LESS_THM, DECIDE ``~(3n < n) = n < 4``]
   )

val cmp_neq = Q.prove(
   `!b1 b2. b1 <> b2 /\ b1 <> Test /\ b2 <> Test ==>
            ~word_bit 7 (n2w (Zcond2num (x64_cmp b1)): word8) /\
            ~word_bit 7 (n2w (Zcond2num (x64_cmp b2)): word8) /\
            (n2w (Zcond2num (x64_cmp b1)): word8) <>
            (n2w (Zcond2num (x64_cmp b2)))`,
   Cases
   \\ Cases
   \\ simp [x64_cmp_def, x64Theory.Zcond2num_thm]
   )

val sh_neq = Q.prove(
   `!b1 b2. b1 <> b2 ==>
            word_bit 3 (n2w (Zbinop_name2num (x64_sh b1)) : word4) /\
            word_bit 3 (n2w (Zbinop_name2num (x64_sh b2)) : word4) /\
            (n2w (Zbinop_name2num (x64_sh b1)): word4) <>
            (n2w (Zbinop_name2num (x64_sh b2)))`,
   Cases
   \\ Cases
   \\ simp [x64_sh_def, x64Theory.Zbinop_name2num_thm]
   )

val bop_neq = Q.prove(
   `!b1 b2. b1 <> b2 ==>
            ~word_bit 3 (n2w (Zbinop_name2num (x64_bop b1)) : word4) /\
            ~word_bit 3 (n2w (Zbinop_name2num (x64_bop b2)) : word4) /\
            (n2w (Zbinop_name2num (x64_bop b1)): word4) <>
            (n2w (Zbinop_name2num (x64_bop b2)))`,
   Cases
   \\ Cases
   \\ simp [x64_bop_def, x64Theory.Zbinop_name2num_thm]
   )

val bop_neq2 = Q.prove(
   `!b. ~(BIT 0 (Zbinop_name2num (x64_bop b)) /\
          BIT 1 (Zbinop_name2num (x64_bop b)) /\
          BIT 2 (Zbinop_name2num (x64_bop b)))`,
   Cases
   \\ simp [x64_bop_def, x64Theory.Zbinop_name2num_thm]
   )

val bop_neq2 =
   CONJ bop_neq2 (REWRITE_RULE [boolTheory.DE_MORGAN_THM] bop_neq2)

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
in
   fun is_bytes_in_memory tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("asm$bytes_in_memory", [_, _, _, _, _]) => true
       | _ => false
   fun bytes_in_memory_tac (asl, g) =
      (case List.mapPartial dest_bytes_in_memory asl of
          [l] => imp_res_tac (bytes_in_memory l)
        | _ => NO_TAC) (asl, g)
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
in
   val not_reg_tac =
      pop_assum (fn th => rule_assum_tac (rule th) \\ assume_tac (SYM th))
end

local
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
in
   val high_low_r1 = high_low_reg ``r1: word4``
   val high_low_r2 = high_low_reg ``r2: word4``
end

fun load_store_tac tac (asl, g) =
   let
      val (high_r1, low_r1) = high_low_r1 asl
      val (high_r2, low_r2) = high_low_r2 asl
      fun tac2 not5 =
        Cases_on `(2 >< 0) r2 = 4w: word3`
        \\ fs enc_rwts
        >| [
           (if low_r2
               then assume_tac (Q.SPECL [`n'`, `r2`] mem_lem10)
                    \\ rfs [Q.SPEC `T` markerTheory.Abbrev_def]
            else all_tac)
           \\ `zR12 = num2Zreg n'` by imp_res_tac mem_lem9,
           (if not5
               then `r2 = RegNot4or5 r2` by (fs [] \\ imp_res_tac mem_lem6)
            else `r2 = RegNot4 r2` by (fs [] \\ imp_res_tac mem_lem7))
           \\ not_reg_tac
        ]
        \\ rule_assum_tac (REWRITE_RULE [binop_lem5])
        \\ next_state_tac0
        \\ rfs [Abbr `r2`, mem_lem5, binop_lem7]
        \\ state_tac [mem_lem8] [`r1`]
        \\ tac
        \\ blastLib.BBLAST_TAC
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

(*
val tac = qabbrev_tac `q = c + state.REG (num2Zreg n')`
val tac = full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
*)

val load_tac = load_store_tac (qabbrev_tac `q = c + state.REG (num2Zreg n')`)
val store_tac =
   load_store_tac (full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) [])

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


val total_strip = Lib.total boolSyntax.dest_strip_comb

fun pos_neg_term q =
   let
      val tm = Parse.Term q
   in
      (q, (tm, boolSyntax.mk_neg tm))
   end

fun explode_x64_enc_tac left (asl, g) =
   let
      val tm = g |> boolSyntax.dest_neg
                 |> listSyntax.dest_isprefix
                 |> (if left then fst else snd)
                 |> rand
      fun contains l = List.exists (fn t => Lib.mem t l) asl
      fun qcase q =
         let
            val (tm, ntm) = snd (pos_neg_term q)
         in
            if contains [tm, ntm] then Tactical.NO_TAC else Cases_on q
         end
   in
     (case total_strip tm of
         SOME ("asm$Call", [_, _]) => fs enc_rwts
       | SOME ("asm$Inst", [i]) =>
            (case total_strip i of
                SOME ("asm$Skip", []) => Tactical.NO_TAC
              | SOME ("asm$Arith", [a]) =>
                   (case total_strip a of
                       SOME ("asm$Shift", [_, _, _, n]) =>
                          qcase `n2w ^n = 1w: word64`
                     | SOME ("asm$Binop", [_, _, _, r]) =>
                          if Term.is_var r
                             then Cases_on `^r`
                          else Tactical.NO_TAC
                     | SOME _ => Tactical.NO_TAC
                     | NONE => Cases_on `^a`)
              | SOME ("asm$Mem", [m, n1, a]) =>
                  (case total_strip a of
                      SOME ("asm$Addr", [n2, c]) =>
                       let
                          val c0_n5 =
                             qcase `(^c = 0w) /\
                                    (2 >< 0) (n2w ^n2: word4) <> (5w: word3)`
                       in
                        if m = ``Store8``
                           then
                             let
                                val q1 = `(3 >< 3) (n2w ^n1 : word4) : word1`
                                val q2 = `(3 >< 3) (n2w ^n2 : word4) : word1`
                                val tm = Parse.Term q1
                             in
                                if contains [``^tm = 0w``, ``^tm = 1w``]
                                   then Tactical.NO_TAC
                                else wordsLib.Cases_on_word_value q1
                                     \\ wordsLib.Cases_on_word_value q2
                                     \\ Cases_on `3 < ^n1`
                                     \\ c0_n5
                             end
                        else if Lib.mem m [``Load32``, ``Store32``]
                           then qcase
                                  `((3 >< 3) (n2w ^n1 : word4) = (0w: word1)) /\
                                   ((3 >< 3) (n2w ^n2 : word4) = (0w: word1))`
                                \\ c0_n5
                        else c0_n5
                       end
                    | SOME _ => Tactical.NO_TAC
                    | NONE => Cases_on `^a` \\ Cases_on `^m`)
              | SOME ("asm$Const", [_, c]) =>
                   qcase `0w <= ^c /\ ^c <= 0x7FFFFFFFw`
              | SOME _ => Tactical.NO_TAC
              | NONE => Cases_on `^i`
            )
       | SOME ("asm$Jump", [_, i]) =>
           if Term.is_var i
              then REVERSE (Cases_on `^i`) >- fs enc_rwts
           else Tactical.NO_TAC
       | SOME ("asm$JumpCmp", [c, n, r, _, i]) =>
          (if Term.is_var i
              then REVERSE (Cases_on `^i`) >- fs enc_rwts
                   \\ Cases_on `^r`
                   \\ Cases_on `^c = Test`
           else case total_strip r of
                   SOME ("asm$Imm", [v]) =>
                      let
                         val (q1, (tm1, ntm1)) = pos_neg_term `^n = 0`
                         val (q2, (tm2, ntm2)) =
                            pos_neg_term
                              `0xFFFFFFFFFFFFFF80w <= ^v /\ ^v <= 0x7fw`
                      in
                         if contains [tm1, ntm1, tm2, ntm2]
                            then Tactical.NO_TAC
                         else if contains [``^c = Test``]
                            then Cases_on q1
                         else Cases_on q2
                              >| [all_tac, Cases_on q1]
                      end
                 | _ => Tactical.NO_TAC)
       | SOME ("asm$JumpReg", [n]) =>
           let
              val q = `(3 >< 3) (n2w ^n : word4) : word1`
              val tm = Parse.Term q
           in
              if contains [``^tm = 0w``, ``^tm = 1w``]
                 then Tactical.NO_TAC
              else wordsLib.Cases_on_word_value q
           end
       | SOME _ => Tactical.NO_TAC
       | NONE => Cases_on `^tm`) (asl, g)
   end

local
   fun is_n tm =
      case Lib.total (snd o Term.dest_var) tm of
         SOME ty => ty = numSyntax.num
       | NONE => false
   fun reg_neq tm =
      case Lib.total (boolSyntax.dest_eq o boolSyntax.dest_neg) tm of
         SOME (l, r) => if is_n l andalso is_n r then SOME (l, r) else NONE
       | NONE => NONE
   fun try_thm (l, r) th =
      let
         val tm = th |> Drule.SPECL [l, r] |> Thm.concl |> Term.rand
      in
         `^tm` by (match_mp_tac th
                   \\ asm_rewrite_tac []
                   \\ simp []
                   \\ Tactical.NO_TAC)
         \\ pop_assum mp_tac
      end
   fun try_both_thm (l, r) th = try_thm (l, r) th ORELSE try_thm (r, l) th
in
   fun val_neq_tac (asl, g) =
     (case List.mapPartial reg_neq asl of
         [lr] => Tactical.MAP_FIRST (try_both_thm lr)
                    [reg4_neq_lem2, reg4_neq_lem, reg_neq_lem, sh_neq_lem]
       | _ => all_tac) (asl, g)
end

local
   val enc_rwts' =
      [const_lem1, loc_lem1, loc_lem2, jump_lem1, jump_lem3, jump_lem4,
       jump_lem5, jump_lem6, cmp_lem7, binop_lem9b, binop_lem11,
       x64Theory.Zcond2num_thm] @ enc_rwts
   fun simpfrag_to_ssfrag name ({convs, rewrs}: simpfrag.simpfrag) =
      simpLib.SSFRAG
         {name = SOME name, convs = convs, rewrs = rewrs, ac = [],
          filter = NONE, dprocs = [], congs = []}
   fun type_frag name ty = simpfrag_to_ssfrag name (TypeBase.simpls_of ty)
   val enc_ss =
      pureSimps.pure_ss ++
      boolSimps.LET_ss ++
      pairSimps.PAIR_ss ++
      pairSimps.gen_beta_ss ++
      optionSimps.OPTION_ss ++
      listSimps.LIST_ss ++
      wordsLib.WORD_ss ++
      type_frag "asm_config" ``:64 asm_config`` ++
      type_frag "asm" ``:64 asm`` ++
      type_frag "asm" ``:cmp`` ++
      type_frag "asm" ``:mem_op`` ++
      type_frag "instruction" ``:instruction`` ++
      type_frag "instruction" ``:Zcond`` ++
      type_frag "instruction" ``:Zdest_src`` ++
      type_frag "instruction" ``:Zrm`` ++
      type_frag "instruction" ``:Zsize`` ++
      type_frag "instruction" ``:Zbase`` ++
      type_frag "instruction" ``:Zbinop_name`` ++ (* remove later? *)
      simpLib.conv_ss
        {name = "BETA_CONV (beta reduction)",
         trace = 2,
         key = SOME ([],``(\x:'a. y:'b) z``),
         conv = K (K Thm.BETA_CONV)} ++
      simpLib.rewrites
        ([combinTheory.K_THM, boolTheory.AND_CLAUSES, boolTheory.IMP_CLAUSES,
          boolTheory.NOT_CLAUSES, boolTheory.COND_CLAUSES,
          boolTheory.OR_CLAUSES, pairTheory.pair_case_thm, boolTheory.EQ_REFL,
          pred_setTheory.COMPONENT, DECIDE ``8n < 64``,
          bop_enc_lem, sh_enc_lem, cmp_enc_lem,
          mem_enc_lem, mem_enc_lem2, mem_enc_lem3, mem_enc_lem4, mem_enc_lem5
          (*, utilsLib.mk_cond_rand_thms [pairSyntax.fst_tm] *)] @
         enc_rwts')
in
   val enc_simp_tac = full_simp_tac enc_ss []
end

local
   fun not_le th =
      let
         val tm = Thm.concl th
      in
         not (wordsSyntax.is_word_le tm orelse
              Lib.can (wordsSyntax.dest_word_le o boolSyntax.dest_neg) tm)
      end
   val CACHE_BBLAST_CONV = utilsLib.cache 200 Term.compare blastLib.BBLAST_CONV
   fun loop jump [] = (* Tactical.NO_TAC for testing *)
      imp_res_tac sh_enc_lem2
      \\ fs [concat_lems, byte_neq, byte_neq2, byte_neq3, byte_neq4,
             byte_neq5, byte_neq6, byte_neq7, byte_neq8]
      \\ map_every imp_res_tac [bop_neq, cmp_neq, sh_neq]
      \\ val_neq_tac
      \\ (if jump
             then all_tac
          else POP_ASSUM_LIST
                (fn ths =>
                    MAP_EVERY ASSUME_TAC (List.filter not_le (List.rev ths))))
      \\ blastLib.FULL_BBLAST_TAC
      \\ REWRITE_TAC [bop_neq2]
     | loop jump (h :: t) =
        let
           val thm = CACHE_BBLAST_CONV h
        in
           if boolSyntax.rhs (Thm.concl thm) = boolSyntax.T
              then REWRITE_TAC [thm]
           else loop jump t
        end
in
   fun byte_blast_tac jump (asl, g) =
      loop jump (boolSyntax.strip_disj g) (asl, g)
end

local
   val i = ref 0
   fun tac jump =
      enc_simp_tac
      \\ rw []
      \\ byte_blast_tac jump
   val asm64_ty = ``:64 asm``
   fun is_asm_neq tm =
      case Lib.total (Term.type_of o rhs o boolSyntax.dest_neg) tm of
         SOME ty => ty = asm64_ty
       | NONE => false
   fun is_jump tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("asm$Loc", [_, _]) => true
       | SOME ("asm$Jump", [_, _]) => true
       | SOME ("asm$JumpCmp", [_, _, _, _, _]) => true
       | _ => false
in
   (* fun reset_i_tac x = (i := 0; all_tac x) *)
   fun enc_tac (asl, g) =
      let
         val tm = Option.valOf (List.find is_asm_neq asl)
         val (l, r) = boolSyntax.dest_eq (boolSyntax.dest_neg tm)
         val jump = is_jump l andalso is_jump r
      in
         i := (!i) + 1
       ; print (Int.toString (!i) ^ "\n")
       ; print_term tm
       ; print "\n\n"
       ; (tac jump \\ goalStack.print_tac "" \\ Tactical.NO_TAC) (asl, g)
     end
end

(* -------------------------------------------------------------------------
   x64_asm_deterministic
   x64_backend_correct
   ------------------------------------------------------------------------- *)

val x64_asm_deterministic = Count.apply Q.store_thm ("x64_asm_deterministic",
   `asm_deterministic x64_enc x64_config`,
   match_mp_tac asmTheory.simple_enc_deterministic
   \\ NTAC 3 strip_tac
   \\ REPEAT (explode_x64_enc_tac false)
   \\ enc_simp_tac
   \\ REPEAT (explode_x64_enc_tac true)
   \\ enc_tac
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

(*

val th = proofManagerLib.top_thm ()

val x64_asm_deterministic = Theory.new_axiom ("x64_asm_deterministic",
   ``asm_deterministic x64_enc x64_config``)

   proofManagerLib.r
   set_trace "Goalstack.howmany_printed_subgoals" 60

*)

val () = export_theory ()
