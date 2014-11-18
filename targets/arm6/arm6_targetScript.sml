open HolKernel Parse boolLib bossLib
open lcsymtacs asmTheory asmLib arm_stepLib;

val () = new_theory "arm6_target"

val () = wordsLib.guess_lengths ()

(* --- Configuration for ARMv6 --- *)

val eval = rhs o concl o EVAL
val min12 = eval ``-(w2w (UINT_MAXw: word12)) : word32``
val max12 = eval ``w2w (UINT_MAXw: word12) : word32``
val min16 = eval ``-(w2w (UINT_MAXw: word16)) + 8w : word32``
val max16 = eval ``w2w (UINT_MAXw: word16) + 8w : word32``
val min26 = eval ``sw2sw (INT_MINw: 26 word) + 12w : word32``
val max26 = eval ``sw2sw (INT_MAXw: 26 word) + 8w : word32``

val valid_immediate_def = Define`
   valid_immediate = IS_SOME o EncodeARMImmediate`

val arm6_config_def = Define`
   arm6_config =
   <| ISA_name := "ARMv6"
    ; reg_count := 16
    ; avoid_regs := [15]
    ; link_reg := SOME 14
    ; has_delay_slot := F
    ; has_icache := F
    ; has_mem_32 := F
    ; two_reg_arith := F
    ; valid_imm := \c i. valid_immediate i
    ; addr_offset_min := ^min12
    ; addr_offset_max := ^max12
    ; jump_offset_min := ^min26
    ; jump_offset_max := ^max26
    ; cjump_offset_min := ^min26
    ; cjump_offset_max := ^max26
    ; loc_offset_min := ^min16
    ; loc_offset_max := ^max16
    ; code_alignment := 4
    |>`

(* --- The next-state function --- *)

val arm6_next_def = Define `arm6_next = THE o NextStateARM`

(* --- Relate ASM and ARMv6 states --- *)

val arm6_asm_state_def = Define`
   arm6_asm_state a s =
   GoodMode s.CPSR.M /\ ~s.CPSR.E /\ ~s.CPSR.J /\ ~s.CPSR.T /\
   (s.Architecture = ARMv6) /\ ~s.Extensions Extension_Security /\
   (s.exception = NoException) /\
   (!i. i < 15 ==> (a.regs i = s.REG (R_mode s.CPSR.M (n2w i)))) /\
   (a.mem_domain = univ(:word32)) /\ (a.mem = s.MEM) /\
   (a.pc = s.REG RName_PC) /\ Aligned (s.REG RName_PC, 4)`

(* --- Encode ASM instructions to ARM bytes. --- *)

val arm6_encode_def = Define`
   arm6_encode c i =
      case encode (c, i) of
         ARM w =>
           [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] : word8 list
       | _ => ARB`

val () = Parse.temp_overload_on ("enc", ``arm6_encode 14w``)

val arm6_bop_def = Define`
   (arm6_bop Add = 0b0100w: word4) /\
   (arm6_bop Sub = 0b0010w) /\
   (arm6_bop And = 0b0000w) /\
   (arm6_bop Or  = 0b1100w) /\
   (arm6_bop Xor = 0b0001w)`

val arm6_sh_def = Define`
   (arm6_sh Lsl = SRType_LSL) /\
   (arm6_sh Lsr = SRType_LSR) /\
   (arm6_sh Asr = SRType_ASR)`

val arm6_cmp_def = Define`
   (arm6_cmp Less  = (2w:word2, 0b1011w:word4)) /\
   (arm6_cmp Lower = (2w, 0b0011w)) /\
   (arm6_cmp Equal = (2w, 0w)) /\
   (arm6_cmp Test  = (0w, 0w))`

val arm6_enc_def = Define`
   (arm6_enc (Inst Skip) =
       (* NoOperation instruction is for >= ARMv6T2 and so isn't available.
          Using BIC r0, r0, #0 instead.
        *)
       enc (Data (ArithLogicImmediate (14w, F, 0w, 0w, 0w)))) /\
   (arm6_enc (Inst (Const r i)) =
      case EncodeARMImmediate i of
         SOME imm12 => enc (Data (Move (F, F, n2w r, imm12)))
       | NONE =>
           (case EncodeARMImmediate (~i) of
               SOME imm12 => enc (Data (Move (F, T, n2w r, imm12)))
             | NONE =>
                 enc (Load (LoadLiteral (T, n2w r, 0w))) ++
                 enc (Branch (BranchTarget (0w))) ++
                 [(7 >< 0) i; (15 >< 8) i; (23 >< 16) i; (31 >< 24) i])) /\
   (arm6_enc (Inst (Arith (Binop bop r1 r2 (Reg r3)))) =
       enc (Data
              (Register
                 (arm6_bop bop, F, n2w r1, n2w r2, n2w r3, SRType_LSL, 0)))) /\
   (arm6_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       enc (Data (ArithLogicImmediate
                     (arm6_bop bop, F, n2w r1, n2w r2,
                      THE (EncodeARMImmediate i))))) /\
   (arm6_enc (Inst (Arith (Shift sh r1 r2 n))) =
       enc (Data (ShiftImmediate (F, F, n2w r1, n2w r2, arm6_sh sh, n)))) /\
   (arm6_enc (Inst (Mem Load r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Load
              (LoadWord (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Load32 _ _)) = []) /\
   (arm6_enc (Inst (Mem Load8 r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Load
              (LoadByte
                 (T, add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Store r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Store
              (StoreWord
                 (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Inst (Mem Store32 r1 (Addr r2 a))) = []) /\
   (arm6_enc (Inst (Mem Store8 r1 (Addr r2 a))) =
       let (add, imm12) = if 0w <= a then (T, a) else (F, -a) in
         enc
           (Store
              (StoreByte
                 (add, T, F, n2w r1, n2w r2, immediate_form1 imm12)))) /\
   (arm6_enc (Jump _ (SOME _)) = []) /\
   (arm6_enc (Jump a NONE) = enc (Branch (BranchTarget (a - 8w)))) /\
   (arm6_enc (JumpCmp _ _ _ _ (SOME _)) = []) /\
   (arm6_enc (JumpCmp cmp r1 (Reg r2) a NONE) =
       let (opc, c) = arm6_cmp cmp in
          enc
            (Data (TestCompareRegister (opc, n2w r1, n2w r2, SRType_LSL, 0))) ++
          arm6_encode c (Branch (BranchTarget (a - 12w)))) /\
   (arm6_enc (JumpCmp cmp r (Imm i) a NONE) =
       let (opc, c) = arm6_cmp cmp
       and imm12 = THE (EncodeARMImmediate i)
       in
          enc (Data (TestCompareImmediate (opc, n2w r, imm12))) ++
          arm6_encode c (Branch (BranchTarget (a - 12w)))) /\
   (arm6_enc (Call a) =
      enc (Branch (BranchLinkExchangeImmediate (InstrSet_ARM, a - 8w)))) /\
   (arm6_enc (JumpReg r) = enc (Branch (BranchExchange (n2w r)))) /\
   (arm6_enc (Loc r i) =
       let (opc, imm32) = if 8w <= i then (4w, i - 8w) else (2w, 8w - i) in
         if imm32 <+ 256w then
            enc
              (Data (ArithLogicImmediate (opc, F, n2w r, 15w, (7 >< 0) imm32)))
         else
            let imm12t = (12w:word4) @@ (15 >< 8) imm32
            and imm12b = (7 >< 0) imm32
            in
               enc (Data (ArithLogicImmediate (opc, F, n2w r, 15w, imm12t))) ++
               enc (Data (ArithLogicImmediate (opc, F, n2w r, n2w r, imm12b))))
        /\
   (arm6_enc Cache = [])`

val arm6_bop_dec_def = Define`
   (arm6_bop_dec (0b0100w: word4) = Add) /\
   (arm6_bop_dec 0b0010w = Sub) /\
   (arm6_bop_dec 0b0000w = And) /\
   (arm6_bop_dec 0b1100w = Or ) /\
   (arm6_bop_dec 0b0001w = Xor)`

val arm6_sh_dec_def = Define`
   (arm6_sh_dec SRType_LSL = Lsl) /\
   (arm6_sh_dec SRType_LSR = Lsr) /\
   (arm6_sh_dec SRType_ASR = Asr)`

val arm6_cmp_dec_def = Define`
   (arm6_cmp_dec (2w:word2, 0b1011w:word4) = Less) /\
   (arm6_cmp_dec (2w, 0b0011w) = Lower) /\
   (arm6_cmp_dec (2w, 0b0000w) = Equal)/\
   (arm6_cmp_dec (0w, 0b0000w) = Test)`

val decode_imm12_def = Define`
   decode_imm12 imm12 = FST (FST (ARMExpandImm_C (imm12, F) ARB))`

val fetch_word_def = Define`
   fetch_word (b0 :: b1 :: b2 :: b3 :: (rest: word8 list)) =
     ((b3 @@ b2 @@ b1 @@ b0) : word32, rest)`

val dec_state_tm = ``<| Architecture := ARMv6; Encoding := Encoding_ARM |>``

val decode_word_def = Define`
   decode_word l =
   let (w, rest) = fetch_word l in
   let cond = (31 >< 28) w : word4 in
   let s = SND (SetPassCondition cond ^dec_state_tm) in
      (cond, FST (DecodeARM w s), rest)`

val arm6_dec_aux_def = Define`
  arm6_dec_aux (ast, rest) =
  case ast of
     Data (ArithLogicImmediate (opc, F, r1, r2, imm12)) =>
      if opc = 14w then Inst Skip
      else if r2 = 15w then
         let imm32 = decode_imm12 imm12 in
            if (11 >< 8) imm12 = 0w then
               Loc (w2n r1) (if opc = 2w then 8w - imm32 else imm32 + 8w)
            else
              (case decode_word rest of
                  (14w, Data (ArithLogicImmediate (opc2, F, r3, r4, imm12b)),
                   rest2) =>
                     let imm32b = decode_imm12 imm12b in
                        Loc (w2n r1)
                            (if opc = 2w then 8w - imm32 - imm32b
                             else imm32 + imm32b + 8w)
                | _ => ARB)
      else Inst (Arith (Binop (arm6_bop_dec opc) (w2n r1) (w2n r2)
                              (Imm (decode_imm12 imm12))))
   | Data (Move (F, neg, r, imm12)) =>
      let c = decode_imm12 imm12 in Inst (Const (w2n r) (if neg then ~c else c))
   | Data (Register (opc, F, r1, r2, r3, SRType_LSL, 0)) =>
      Inst (Arith (Binop (arm6_bop_dec opc) (w2n r1) (w2n r2) (Reg (w2n r3))))
   | Data (ShiftImmediate (F, F, r1, r2, sh, n)) =>
      Inst (Arith (Shift (arm6_sh_dec sh) (w2n r1) (w2n r2) n))
   | Load (LoadLiteral (T, r, 0w)) =>
        (case decode_word rest of
            (14w, Branch (BranchTarget 0w), rest2) =>
               Inst (Const (w2n r) (FST (fetch_word rest2)))
          | _ => ARB)
   | Load (LoadWord (plus, T, F, r1, r2, immediate_form1 imm12)) =>
      Inst (Mem Load (w2n r1) (Addr (w2n r2) (if plus then imm12 else -imm12)))
   | Load (LoadByte (T, plus, T, F, r1, r2, immediate_form1 imm12)) =>
      Inst (Mem Load8 (w2n r1) (Addr (w2n r2) (if plus then imm12 else -imm12)))
   | Store (StoreWord (plus, T, F, r1, r2, immediate_form1 imm12)) =>
      Inst (Mem Store (w2n r1) (Addr (w2n r2) (if plus then imm12 else -imm12)))
   | Store (StoreByte (plus, T, F, r1, r2, immediate_form1 imm12)) =>
      Inst (Mem Store8 (w2n r1) (Addr (w2n r2)
                (if plus then imm12 else -imm12)))
   | Branch (BranchTarget imm32) => Jump (imm32 + 8w) NONE
   | Branch (BranchLinkExchangeImmediate (InstrSet_ARM, imm32)) =>
      Call (imm32 + 8w)
   | Branch (BranchExchange r) => JumpReg (w2n r)
   | Data (TestCompareImmediate (opc, r, imm12)) =>
        (case decode_word rest of
            (cond2, Branch (BranchTarget imm32), _) =>
               JumpCmp (arm6_cmp_dec (opc, cond2)) (w2n r)
                       (Imm (decode_imm12 imm12)) (imm32 + 12w) NONE
          | _ => ARB)
   | Data (TestCompareRegister (opc, r1, r2, SRType_LSL, 0)) =>
        (case decode_word rest of
            (cond2, Branch (BranchTarget imm32), _) =>
               JumpCmp (arm6_cmp_dec (opc, cond2)) (w2n r1) (Reg (w2n r2))
                       (imm32 + 12w) NONE
          | _ => ARB)
   | _ => ARB`

val arm6_dec_def = Define `arm6_dec = arm6_dec_aux o SND o decode_word`

(* ------------------------------------------------------------------------- *)

(* some lemmas ---------------------------------------------------------- *)

val n_tm = ``n < 16 /\ n <> 15n``

val arm6_asm_state = REWRITE_RULE [DECIDE ``n < 15 = ^n_tm``] arm6_asm_state_def

val lem1 = Q.prove(
   `!n m. ^n_tm ==> RName_PC <> R_mode m (n2w n)`,
   CONV_TAC (Conv.ONCE_DEPTH_CONV SYM_CONV)
   \\ simp [arm_stepTheory.R_x_pc]
   )

val lem2 = Q.prove(
   `!n. n < 16 ==> (v2w [BIT 3 n; BIT 2 n; BIT 1 n; BIT 0 n] = n2w n: word4)`,
   NTAC 2 strip_tac
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ EVAL_TAC
   )

val lem3 = Q.prove(
   `!n. n < 32 ==>
        (v2w [BIT 4 n; BIT 3 n; BIT 2 n; BIT 1 n; BIT 0 n] = n2w n: word5)`,
   NTAC 2 strip_tac
   \\ fs [wordsTheory.NUMERAL_LESS_THM]
   \\ EVAL_TAC
   )

val lem4 =
   blastLib.BBLAST_PROVE ``0w <= c /\ c <= 4095w ==> c <=+ 4095w: word32``

val lem5 =
   blastLib.BBLAST_PROVE
      ``~(0w <= c) /\ 0xFFFFF001w <= c ==> -1w * c <=+ 4095w: word32``

val lem6 = Q.prove(
   `!s state c n.
      arm6_asm_state s state /\ ^n_tm /\ (3w && (c + s.regs n) = 0w) ==>
      Aligned (c + state.REG (R_mode state.CPSR.M (n2w n)), 4)`,
   rw [arm6_asm_state, arm_stepTheory.Aligned]
   \\ pop_assum mp_tac
   \\ simp [blastLib.BBLAST_PROVE
               ``(3w && x = 0w: word32) = ((1 >< 0) x = 0w: word2)``]
   )

val lem7 = Q.prove(
   `!w. (w2n (w: word32) MOD 4 = 0) = Aligned (w, 4)`,
   Cases
   \\ fs [armTheory.Aligned_def, armTheory.Align_def, arithmeticTheory.LESS_MOD,
          DECIDE ``a < b ==> (a - x < b:num)``,
          bitTheory.DIV_MULT_THM
          |> Q.SPEC `2`
          |> SIMP_RULE arith_ss []]
   \\ Cases_on `n < 4`
   \\ simp []
   )

val jmp_tm =
   ``0xFE00000Cw <= c /\ c <= 0x2000007w: word32 /\ ((1 >< 0) c = 0w: word2)``

val lem8 =
   blastLib.BBLAST_PROVE
      ``^jmp_tm ==>
        0xFE000000w <= c + 0xFFFFFFF8w /\ 0xFE000000w <= c + 0xFFFFFFF4w /\
        c + 0xFFFFFFF8w <= 0x1FFFFFCw /\ c + 0xFFFFFFF4w <= 0x1FFFFFCw: word32``

val rule = REWRITE_RULE [GSYM arm_stepTheory.Aligned]
val lem8 = rule lem8

val lem9 =
   blastLib.BBLAST_PROVE
     ``(a = (25 >< 2) (c + 0xFFFFFFF8w): word24) /\ a ' 23 /\ ^jmp_tm ==>
       (-1w *
       (v2w
          [~a ' 22; ~a ' 21; ~a ' 20; ~a ' 19; ~a ' 18; ~a ' 17; ~a ' 16;
           ~a ' 15; ~a ' 14; ~a ' 13; ~a ' 12; ~a ' 11; ~a ' 10; ~a ' 9;
           ~a ' 8; ~a ' 7; ~a ' 6; ~a ' 5; ~a ' 4; ~a ' 3; ~a ' 2; ~a ' 1;
           ~a ' 0; T; T] + 1w) = c - 8w)``

val rule =
   CONV_RULE
      (LAND_CONV
         (LAND_CONV (ONCE_REWRITE_CONV [GSYM markerTheory.Abbrev_def]))) o rule

val lem9 = rule lem9

val lem10 =
   blastLib.BBLAST_PROVE
     ``(a = (25 >< 2) (c + 0xFFFFFFF8w): word24) /\ ~a ' 23 /\ ^jmp_tm ==>
       (v2w
          [a ' 22; a ' 21; a ' 20; a ' 19; a ' 18; a ' 17; a ' 16; a ' 15;
           a ' 14; a ' 13; a ' 12; a ' 11; a ' 10; a ' 9; a ' 8; a ' 7; a ' 6;
           a ' 5; a ' 4; a ' 3; a ' 2; a ' 1; a ' 0; F; F] = c - 8w)``

val lem10 = rule lem10

val lem11 =
   (REWRITE_RULE [wordsTheory.WORD_ADD_0] o  Q.INST [`c` |-> `0w`] o
    Drule.SPEC_ALL) lem6

val lem12 = Q.prove(
   `!x: word32. Aligned (x, 4) ==> ~word_bit 1 x /\ ~word_bit 0 x`,
   simp [arm_stepTheory.Aligned]
   \\ blastLib.BBLAST_TAC
   )

(*
val lem12 =
   Drule.GEN_ALL
      (Drule.IMP_TRANS lem11
         (Q.SPEC `state.REG (R_mode state.CPSR.M (n2w n))` lem12))
*)

val lem14 =
   arm_stepTheory.Align4_base_pc_plus
   |> Q.INST [`t` |-> `F`, `x` |-> `0w`]
   |> Drule.DISCH_ALL
   |> SIMP_RULE (srw_ss()) []

val lem15 = Q.prove(
   `!c r: word32.
       Abbrev (r = c + 0xFFFFFFF4w) /\ r ' 25 /\ ^jmp_tm ==>
       (-1w *
        (v2w
          [~r ' 24; ~r ' 23; ~r ' 22; ~r ' 21; ~r ' 20; ~r ' 19; ~r ' 18;
           ~r ' 17; ~r ' 16; ~r ' 15; ~r ' 14; ~r ' 13; ~r ' 12; ~r ' 11;
           ~r ' 10; ~r ' 9; ~r ' 8; ~r ' 7; ~r ' 6; ~r ' 5; ~r ' 4; ~r ' 3;
           ~r ' 2; T; T] + 1w) = c - 12w)`,
   rw []
   \\ qunabbrev_tac `r`
   \\ blastLib.FULL_BBLAST_TAC
   )

val lem16 = Q.prove(
   `!c r: word32.
       Abbrev (r = c + 0xFFFFFFF4w) /\ ~r ' 25 /\ ^jmp_tm ==>
       (v2w
          [r ' 24; r ' 23; r ' 22; r ' 21; r ' 20; r ' 19; r ' 18; r ' 17;
           r ' 16; r ' 15; r ' 14; r ' 13; r ' 12; r ' 11; r ' 10; r ' 9; r ' 8;
           r ' 7; r ' 6; r ' 5; r ' 4; r ' 3; r ' 2; F; F] = c - 12w)`,
   rw []
   \\ qunabbrev_tac `r`
   \\ blastLib.FULL_BBLAST_TAC
   )

val lem18 =
   blastLib.BBLAST_PROVE
     ``((11 >< 8) (v2w [F; F; F; F; b7; b6; b5; b4; b3; b2; b1; b0] : word12) =
        0w: word4) /\
       ((11 >< 8) (v2w [T; T; F; F; b7; b6; b5; b4; b3; b2; b1; b0] : word12) =
        12w: word4)``

val lem19 =
   blastLib.BBLAST_PROVE
     ``!c: word32.
          c + 0xFFFFFFF8w <+ 256w ==>
          (w2w (v2w
                [c:word32 ' 7 = c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
                 c ' 6 = c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 = c ' 4 \/ c ' 3;
                 c ' 4 = c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0]: word8) =
           c - 8w: word32)``

val rule = REWRITE_RULE [GSYM arm_stepTheory.Aligned]
val lem15 = rule lem15
val lem16 = rule lem16

val aligned_sum = Q.prove(
   `!a b: word32. Aligned (a, 4) /\ Aligned (b, 4) ==> Aligned (a + b, 4)`,
   simp [arm_stepTheory.Aligned]
   \\ blastLib.BBLAST_TAC
   )

fun tac n =
   simp [Ntimes armTheory.EncodeARMImmediate_aux_def n,
         wordsLib.WORD_DECIDE ``-1w = 15w: word4``]
   \\ strip_tac
   \\ qunabbrev_tac `i`
   \\ simp []
   \\ CONV_TAC
        (LAND_CONV (RAND_CONV (Conv.DEPTH_CONV blastLib.BBLAST_CONV)
                               THENC DEPTH_CONV bitstringLib.v2w_n2w_CONV))
   \\ simp []
   \\ blastLib.FULL_BBLAST_TAC
   \\ blastLib.BBLAST_TAC

val decode_imm_thm = Q.prove(
   `!c.
      valid_immediate c ==>
      let imm12 = THE (EncodeARMImmediate c) in
         w2w (v2w [imm12 ' 7; imm12 ' 6; imm12 ' 5; imm12 ' 4;
                   imm12 ' 3; imm12 ' 2; imm12 ' 1; imm12 ' 0]: word8) #>>
         w2n (v2w [imm12 ' 11; imm12 ' 10; imm12 ' 9; imm12 ' 8; F] : word5) =
         c`,
   strip_tac
   \\ simp_tac std_ss [valid_immediate_def, armTheory.EncodeARMImmediate_def]
   \\ qabbrev_tac `i = EncodeARMImmediate_aux (15w,c)`
   \\ pop_assum mp_tac
   \\ Cases_on `(31 >< 8) c = 0w: word24` >- tac 1
   \\ Cases_on `(31 >< 8) (c #<< 2) = 0w: word24` >- tac 2
   \\ Cases_on `(31 >< 8) (c #<< 4) = 0w: word24` >- tac 3
   \\ Cases_on `(31 >< 8) (c #<< 6) = 0w: word24` >- tac 4
   \\ Cases_on `(31 >< 8) (c #<< 8) = 0w: word24` >- tac 5
   \\ Cases_on `(31 >< 8) (c #<< 10) = 0w: word24` >- tac 6
   \\ Cases_on `(31 >< 8) (c #<< 12) = 0w: word24` >- tac 7
   \\ Cases_on `(31 >< 8) (c #<< 14) = 0w: word24` >- tac 8
   \\ Cases_on `(31 >< 8) (c #<< 16) = 0w: word24` >- tac 9
   \\ Cases_on `(31 >< 8) (c #<< 18) = 0w: word24` >- tac 10
   \\ Cases_on `(31 >< 8) (c #<< 20) = 0w: word24` >- tac 11
   \\ Cases_on `(31 >< 8) (c #<< 22) = 0w: word24` >- tac 12
   \\ Cases_on `(31 >< 8) (c #<< 24) = 0w: word24` >- tac 13
   \\ Cases_on `(31 >< 8) (c #<< 26) = 0w: word24` >- tac 14
   \\ Cases_on `(31 >< 8) (c #<< 28) = 0w: word24` >- tac 15
   \\ Cases_on `(31 >< 8) (c #<< 30) = 0w: word24` >- tac 16
   \\ tac 17
   )

val decode_imm_thm = SIMP_RULE (bool_ss++boolSimps.LET_ss) [] decode_imm_thm

val decode_some_encode_immediate =
   decode_imm_thm
   |> Q.SPEC `c`
   |> Q.DISCH `EncodeARMImmediate c = SOME x`
   |> SIMP_RULE std_ss [valid_immediate_def]
   |> Drule.GEN_ALL

val decode_some_encode_neg_immediate =
   decode_imm_thm
   |> Q.SPEC `~c`
   |> Q.DISCH `EncodeARMImmediate (~c) = SOME x`
   |> SIMP_RULE std_ss [valid_immediate_def]
   |> Drule.GEN_ALL

val decode_imm12_thm =
   blastLib.BBLAST_PROVE
     ``!c: word32.
       c <=+ 4095w ==>
       (w2w (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6;
                  c ' 5; c ' 4; c ' 3; c ' 2; c ' 1; c ' 0] : word12) = c)``

val decode_neg_imm12_thm = Q.prove(
   `!c: word32 d.
       0xFFFFF001w <= c /\ ~(0w <= c) /\ Abbrev (d = -1w * c) ==>
       (-1w *
        w2w (v2w [d ' 11; d ' 10; d ' 9; d ' 8; d ' 7; d ' 6;
                  d ' 5; d ' 4; d ' 3; d ' 2; d ' 1; d ' 0] : word12) = c)`,
   rw []
   \\ qunabbrev_tac `d`
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm1 = Q.prove(
   `!c: word32.
       8w <= c /\ c <= 263w ==>
       (EncodeARMImmediate (c + 0xFFFFFFF8w) =
        SOME ((7 >< 0) (c + 0xFFFFFFF8w)))`,
   rw [armTheory.EncodeARMImmediate_def,
       Once armTheory.EncodeARMImmediate_aux_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm2 =
   blastLib.BBLAST_PROVE
     ``!c: word32.
         8w <= c /\ c + 0xFFFFFFF8w <+ 256w ==>
         (w2w (v2w [c ' 7 <=> c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
                    c ' 6 <=> c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 <=> c ' 4 \/ c ' 3;
                    c ' 4 <=> c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0]: word8) =
         c - 8w)``

val decode_imm8_thm3 = Q.prove(
   `!c: word32.
       ~(8w <= c) /\ 0xFFFFFF09w <= c ==>
       (EncodeARMImmediate (-1w * c + 8w) = SOME ((7 >< 0) (-1w * c + 8w)))`,
   rw [armTheory.EncodeARMImmediate_def,
       Once armTheory.EncodeARMImmediate_aux_def]
   \\ blastLib.FULL_BBLAST_TAC
   )

val decode_imm8_thm4 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         8w <= c /\ c <= 0x10007w /\ ~(c + 0xFFFFFFF8w <+ 256w) ==>
  (c + p =
   w2w
      (v2w
         [c ' 7 <=> c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 6 <=> c ' 5 \/ c ' 4 \/ c ' 3; c ' 5 <=> c ' 4 \/ c ' 3;
          c ' 4 <=> c ' 3; ~c ' 3; c ' 2; c ' 1; c ' 0] : word8) +
    p +
    w2w
      (v2w
         [c ' 15 <=>
          c ' 14 \/ c ' 13 \/ c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/
          c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 14 <=>
          c ' 13 \/ c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/
          c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 13 <=>
          c ' 12 \/ c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/
          c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 12 <=>
          c ' 11 \/ c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/
          c ' 4 \/ c ' 3;
          c ' 11 <=>
          c ' 10 \/ c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/
          c ' 3;
          c ' 10 <=>
          c ' 9 \/ c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 9 <=> c ' 8 \/ c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3;
          c ' 8 <=> c ' 7 \/ c ' 6 \/ c ' 5 \/ c ' 4 \/ c ' 3] : word8) #>> 24 +
    8w)``

val decode_imm8_thm5 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         ~(8w <= c) /\ 0xFFFF0009w <= c /\ -1w * c + 8w <+ 256w ==>
  (c + p =
   -1w *
   w2w
     (v2w
        [c ' 7 <=>
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 6 <=>
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 5 <=> ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 4 <=> ~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
         c ' 3 <=> c ' 2 \/ c ' 1 \/ c ' 0; c ' 2 <=> ~c ' 1 /\ ~c ' 0;
         ~c ' 1 <=> c ' 0; c ' 0]: word8) + p + 8w)``

val decode_imm8_thm6 =
   blastLib.BBLAST_PROVE
     ``!c: word32 p.
         ~(8w <= c) /\ 0xFFFF0009w <= c /\ ~(-1w * c + 8w <+ 256w) ==>
  (c + p =
   -1w *
   w2w
     (v2w
        [c ' 7 <=>
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 6 <=>
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 5 <=> ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 4 <=> ~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0;
         c ' 3 <=> c ' 2 \/ c ' 1 \/ c ' 0; c ' 2 <=> ~c ' 1 /\ ~c ' 0;
         ~c ' 1 <=> c ' 0; c ' 0]: word8) + p +
   -1w *
   w2w
     (v2w
        [c ' 15 <=>
         ~c ' 14 /\ ~c ' 13 /\ ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\
         ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 14 <=>
         ~c ' 13 /\ ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\
         ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 13 <=>
         ~c ' 12 /\ ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\
         ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 12 <=>
         ~c ' 11 /\ ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\
         ~c ' 5 /\ ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 11 <=>
         ~c ' 10 /\ ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\
         ~c ' 4 /\ (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 10 <=>
         ~c ' 9 /\ ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 9 <=>
         ~c ' 8 /\ ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0);
         c ' 8 <=>
         ~c ' 7 /\ ~c ' 6 /\ ~c ' 5 /\ ~c ' 4 /\
         (~c ' 3 \/ ~c ' 2 /\ ~c ' 1 /\ ~c ' 0)]: word8) #>> 24 + 8w)``

val word_lo_not_carry = Q.prove(
   `!a b. a <+ b = ~CARRY_OUT a (~b) T`,
   simp [wordsTheory.ADD_WITH_CARRY_SUB, wordsTheory.WORD_NOT_LOWER_EQUAL]
   )

val word_lt_n_eq_v = Q.prove(
   `!a b: word32. a < b = (word_bit 31 (a + -1w * b) <> OVERFLOW a (~b) T)`,
   simp [wordsTheory.ADD_WITH_CARRY_SUB, GSYM wordsTheory.WORD_LO]
   \\ blastLib.BBLAST_TAC
   )

val SetPassCondition =
   utilsLib.map_conv
     (SIMP_CONV (srw_ss()++boolSimps.LET_ss) [armTheory.SetPassCondition_def])
     [``SetPassCondition 0w s``,
      ``SetPassCondition 3w s``,
      ``SetPassCondition 11w s``,
      ``SetPassCondition 14w s``]

local
   open armTheory
   val () = utilsLib.setStepConv (Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV)
   val EV = utilsLib.STEP (K (utilsLib.datatype_rewrites true "arm" ["SRType"]),
                           ``s:arm_state``)
   val Shift_C_rwt =
      EV [Shift_C_def, LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def, RRX_C_def]
         [] []
         ``Shift_C (value,typ,amount,carry_in)
           : arm_state -> ('a word # bool) # arm_state``
         |> hd
         |> SIMP_RULE std_ss []
   val arm_imm_lem = Q.prove(
      `((if n = 0 then ((w, c1), s) else ((w #>> n, c2), s)) =
        ((w #>> n, if n = 0 then c1 else c2), s)) /\
       (2 * w2n (v2w [a; b; c; d] : word4) =
        w2n (v2w [a; b; c; d; F] : word5))`,
      rw [] \\ wordsLib.n2w_INTRO_TAC 5 \\ blastLib.BBLAST_TAC
      )
in
   val ARMExpandImm_C_rwt =
      EV [armTheory.ARMExpandImm_C_def, Shift_C_rwt, arm_imm_lem] [] []
        ``ARMExpandImm_C (^(bitstringSyntax.mk_vec 12 0), c)``
        |> hd
        |> REWRITE_RULE [wordsTheory.w2n_eq_0]
end

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open armTheory
   in
      [arm6_enc_def, arm6_bop_def, arm6_sh_def, arm6_cmp_def, arm6_encode_def,
       encode_def, e_branch_def, e_data_def, e_load_def, e_store_def,
       EncodeImmShift_def
       ]
   end

val enc_rwts =
   [arm6_config_def, offset_monotonic_def, lem7] @
   encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
   encode_rwts @ asmLib.asm_ok_rwts @ [enc_ok_def, arm6_config_def]

val dec_rwts =
   [arm6_dec_def, decode_word_def, SetPassCondition, fetch_word_def]

(* some custom tactics ---------------------------------------------------- *)

val bytes_in_memory_thm = Q.prove(
   `!s state a b c d.
      arm6_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.icache s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      (state.Architecture = ARMv6) /\
      ~state.Extensions Extension_Security /\
      ~state.CPSR.T /\
      ~state.CPSR.J /\
      ~state.CPSR.E /\
      GoodMode state.CPSR.M /\
      Aligned (state.REG RName_PC,4) /\
      (state.MEM (state.REG RName_PC + 3w) = d) /\
      (state.MEM (state.REG RName_PC + 2w) = c) /\
      (state.MEM (state.REG RName_PC + 1w) = b) /\
      (state.MEM (state.REG RName_PC) = a)`,
   rw [arm6_asm_state_def, bytes_in_memory_def]
   \\ simp []
   )

val bytes_in_memory_thm2 = Q.prove(
   `!s state w a b c d.
      arm6_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.icache s.mem s.mem_domain ==>
      (state.MEM (state.REG RName_PC + w + 3w) = d) /\
      (state.MEM (state.REG RName_PC + w + 2w) = c) /\
      (state.MEM (state.REG RName_PC + w + 1w) = b) /\
      (state.MEM (state.REG RName_PC + w) = a)`,
   rw [arm6_asm_state_def, bytes_in_memory_def]
   \\ simp []
   )

val arm_op2 =
   HolKernel.syntax_fns "arm" 2 HolKernel.dest_binop HolKernel.mk_binop

local
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
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.rev o List.map (boolify 8)
   val step6 = arm_stepLib.arm_eval "v6"
   fun step P state x l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
      in
         (gen_v P o Q.INST [`s` |-> state] o Drule.DISCH_ALL o step6) (x, v)
      end
   val dec6 = arm_stepLib.arm_decode (arm_configLib.mk_config_terms "v6")
   val arm_state_rule =
      REWRITE_RULE (utilsLib.datatype_rewrites true "arm" ["arm_state", "PSR"])
   fun dec x (tm,st) =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         (x, l) |> dec6 |> hd
                |> Drule.DISCH_ALL
                |> Thm.INST [``s: arm_state`` |-> st]
                |> arm_state_rule
                |> REWRITE_RULE [th1]
      end
   val (_, _, dest_DecodeARM, is_DecodeARM) = arm_op2 "DecodeARM"
   val find_DecodeARM =
      HolKernel.bvk_find_term (is_DecodeARM o snd) dest_DecodeARM
in
   fun decode_tac x (asl, g) =
      (case find_DecodeARM g of
          SOME tms =>
           let
              val dec_thm = dec x tms
           (*  val () = (print_thm dec_thm; print "\n") *)
           in
              asm_simp_tac (srw_ss())
                [dec_thm, lem2, lem3, arm6_dec_aux_def, decode_imm12_def,
                 ARMExpandImm_C_rwt, armTheory.DecodeImmShift_def]
              \\ CONV_TAC (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
              \\ lfs [lem2, lem3, lem4, decode_some_encode_immediate,
                      decode_imm_thm, decode_imm12_thm,
                      arm6_bop_dec_def, arm6_cmp_dec_def, arm6_sh_dec_def,
                      arm_stepTheory.Aligned]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac pick P state x (asl, g) =
      (case List.mapPartial dest_bytes_in_memory asl of
          [] => NO_TAC
        | l => assume_tac (step P state x (pick l))) (asl, g)
end

local
   val is_byte_eq =
      Lib.can ((wordsSyntax.dest_word_extract ## bitstringSyntax.dest_v2w) o
               boolSyntax.dest_eq)
in
   val byte_eq_tac =
      rule_assum_tac
        (Conv.CONV_RULE
           (Conv.DEPTH_CONV
              (fn tm => if is_byte_eq tm
                           then blastLib.BBLAST_CONV tm
                        else Conv.NO_CONV tm)
            THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV))
end

fun next_state_tac0 f q l =
   next_state_tac f (K false) q l
   \\ imp_res_tac bytes_in_memory_thm
   \\ fs []
   \\ byte_eq_tac
   \\ rfs [lem2, lem3, lem4, lem6, decode_imm12_thm, combinTheory.UPDATE_APPLY,
           decode_imm_thm, arm_stepTheory.Aligned_numeric]

val next_state_tac01 = next_state_tac0 List.last `state` [true]

fun next_state_tac1 f l (asl, g) =
   let
      val tm = g |> rand |> rand |> rand
   in
      next_state_tac0 f `^tm` l (asl, g)
   end

val enc_ok_tac = full_simp_tac (srw_ss()++boolSimps.LET_ss) enc_ok_rwts
fun next_tac n =
   qexists_tac n \\ simp [arm6_next_def, numeralTheory.numeral_funpow]
fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

fun state_tac thms =
   REPEAT (qpat_assum `NextStateARM q = z` (K all_tac))
   \\ fs ([arm6_asm_state, decode_imm_thm] @ thms)
   \\ rw [combinTheory.APPLY_UPDATE_THM, arm_stepTheory.Aligned_numeric,
          arm_stepTheory.R_mode_11, lem1]

fun load_store_tac {word, neg, store} =
   (if neg then qabbrev_tac `d = -1w * c` \\ imp_res_tac decode_neg_imm12_thm
    else all_tac)
   \\ (if word then imp_res_tac lem6 else all_tac)
   \\ (if store
          then next_state_tac01
               \\ state_tac [FUN_EQ_THM]
               \\ srw_tac [wordsLib.WORD_EXTRACT_ss] []
               \\ full_simp_tac (srw_ss()++wordsLib.WORD_CANCEL_ss) []
       else next_state_tac0 List.last `state` [true, false]
            \\ state_tac []
            \\ blastLib.BBLAST_TAC)

local
   val BLAST_BYTE_EQ_CONV =
      FORK_CONV
         (blastLib.BBLAST_CONV,
          FORK_CONV
             (blastLib.BBLAST_CONV,
              FORK_CONV
                 (blastLib.BBLAST_CONV,
                  LAND_CONV blastLib.BBLAST_CONV)))
      THENC REWRITE_CONV []
in
   val blast_byte_eq_tac =
      qpat_assum `(xx = yy) ==> pp`
         (assume_tac o (CONV_RULE BLAST_BYTE_EQ_CONV))
end

local
   fun tac b =
      imp_res_tac bytes_in_memory_thm2
      \\ fs []
      \\ blast_byte_eq_tac
      \\ qunabbrev_tac `p`
      \\ state_tac []
      \\ imp_res_tac lem15
      \\ imp_res_tac lem16
      \\ fs [Q.SPEC `F` markerTheory.Abbrev_def,
             blastLib.BBLAST_PROVE ``a <> b ==> (0w <> a + -1w * b: word32)``,
             blastLib.BBLAST_PROVE ``a <> b ==> (0w <> -1w * b + a: word32)``,
             word_lo_not_carry, word_lt_n_eq_v]
      \\ fs ([Abbr `r`, arm_stepTheory.Aligned_numeric, aligned_sum] @
             (if b then [Abbr `q`] else []))
in
   fun cmp_tac imm =
      Cases_on `c`
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      \\ asmLib.split_bytes_in_memory_tac 4
      \\ next_state_tac01
      \\ qabbrev_tac `r = c0 + 0xFFFFFFF4w`
      \\ (if imm then
            qabbrev_tac
                 `p = add_with_carry
                         (state.REG (R_mode state.CPSR.M (n2w n)), ~c',T)`
            \\ qabbrev_tac
                 `q = -1w * c' + state.REG (R_mode state.CPSR.M (n2w n))`
          else
            qabbrev_tac `p = add_with_carry
                               (state.REG (R_mode state.CPSR.M (n2w n)),
                                ~state.REG (R_mode state.CPSR.M (n2w n')),T)`
            \\ qabbrev_tac `q = state.REG (R_mode state.CPSR.M (n2w n)) +
                                -1w * state.REG (R_mode state.CPSR.M (n2w n'))`)
      >| [
         (* Equal *)
         Cases_on `q = 0w`
         >| [
            next_state_tac1 hd [false, true],
            next_state_tac1 hd [true, false]
         ]
         \\ tac false,
         (* Lower *)
         Cases_on `FST (SND p)`
         >| [
            next_state_tac1 hd [true, false],
            next_state_tac1 hd [false, true]
         ]
         \\ tac false,
         (* Less *)
         Cases_on `word_bit 31 q = SND (SND p)`
         >| [
            next_state_tac1 hd [true, false],
            next_state_tac1 hd [false, true]
         ]
         \\ tac true,
         (* Test *)
         (if imm
             then Cases_on `state.REG (R_mode state.CPSR.M (n2w n)) && c' = 0w`
          else Cases_on `state.REG (R_mode state.CPSR.M (n2w n)) &&
                         state.REG (R_mode state.CPSR.M (n2w n')) = 0w`)
         >| [
            next_state_tac1 hd [false, true],
            next_state_tac1 hd [true, false]
         ]
         \\ tac true
      ]
end

local
   val (_, _, _, is_SetPassCondition) = arm_op2 "SetPassCondition"
   val cnv =
      Conv.RATOR_CONV
         (Conv.RAND_CONV (SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []))
      THENC SIMP_CONV (srw_ss()) [SetPassCondition]
in
   fun SetPassCondition_CONV tm =
      if is_SetPassCondition tm
         then cnv tm
      else raise ERR "SetPassCondition_CONV" ""
   val SetPassCondition_tac =
      CONV_TAC (Conv.ONCE_DEPTH_CONV SetPassCondition_CONV)
      \\ simp_tac std_ss []
end

val decode_tac0 =
   simp ([lem4, lem5, lem8, decode_imm8_thm1, decode_imm8_thm3,
          GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric] @
         enc_rwts)
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ SetPassCondition_tac
   \\ (decode_tac [true] ORELSE decode_tac [true, false])
   \\ blastLib.FULL_BBLAST_TAC

(* -------------------------------------------------------------------------
   arm6_asm_deterministic
   arm6_backend_correct
   ------------------------------------------------------------------------- *)

val arm6_encoding = Count.apply Q.prove (
   `!i. asm_ok i arm6_config ==>
        let l = arm6_enc i in
           (!x. arm6_dec (l ++ x) = i) /\ (LENGTH l MOD 4 = 0)`,
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
         \\ decode_tac0
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ REVERSE (Cases_on `EncodeARMImmediate c`)
         >- decode_tac0
         \\ REVERSE (Cases_on `EncodeARMImmediate ~c`)
         >- (imp_res_tac decode_some_encode_neg_immediate \\ decode_tac0)
         \\ simp enc_rwts
         \\ REPEAT strip_tac
         \\ simp dec_rwts
         \\ SetPassCondition_tac
         \\ decode_tac [true]
         \\ simp dec_rwts
         \\ decode_tac [true]
         \\ blastLib.BBLAST_TAC
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
            \\ decode_tac0
            )
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ decode_tac0
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      \\ Cases_on `0w <= c`
      \\ decode_tac0
      )
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ Cases_on `o'`
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ REVERSE (Cases_on `o'`)
      >- fs enc_rwts
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ simp ([lem8, GSYM arm_stepTheory.Aligned,
                arm_stepTheory.Aligned_numeric] @ enc_rwts)
      \\ REPEAT strip_tac
      \\ simp dec_rwts
      \\ SetPassCondition_tac
      \\ (decode_tac [true] ORELSE decode_tac [true, false])
      \\ simp dec_rwts
      \\ SetPassCondition_tac
      \\ decode_tac [false, true]
      \\ simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) [arm6_cmp_dec_def]
      \\ rw []
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*
        --------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac0
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ lrw ([Q.ISPEC `LENGTH:'a list -> num` COND_RAND,
               (SIMP_RULE std_ss [] o Q.ISPEC `\x. x MOD 4`) COND_RAND] @
              enc_rwts)
      \\ BasicProvers.CASE_TAC
      \\ simp dec_rwts
      \\ SetPassCondition_tac
      \\ (decode_tac [true] ORELSE decode_tac [true, false])
      \\ simp [lem18, lem19]
      \\ simp_tac (srw_ss()++boolSimps.LET_ss++wordsLib.WORD_EXTRACT_ss)
           dec_rwts
      \\ TRY (decode_tac [true] ORELSE decode_tac [true, false])
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*
        --------------
          no Cache
        --------------*)
   \\ fs enc_rwts
   )

val arm6_asm_deterministic = Q.store_thm("arm6_asm_deterministic",
   `asm_deterministic arm6_enc arm6_config`,
   metis_tac [decoder_asm_deterministic, has_decoder_def, arm6_encoding]
   )

val arm6_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [arm6_config_def] arm6_asm_deterministic

val arm6_backend_correct = Count.apply Q.store_thm ("arm6_backend_correct",
   `backend_correct arm6_enc arm6_config arm6_next arm6_asm_state`,
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
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ next_tac `0`
         \\ lfs enc_rwts
         \\ next_state_tac01
         \\ state_tac []
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ REVERSE (Cases_on `EncodeARMImmediate c`)
         >- (
            next_tac `0`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            \\ simp [decode_some_encode_immediate]
            )
         \\ REVERSE (Cases_on `EncodeARMImmediate ~c`)
         >- (
            next_tac `0`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            \\ imp_res_tac decode_some_encode_neg_immediate
            \\ simp []
            )
         \\ next_tac `1`
         \\ lfs enc_rwts
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ next_state_tac01
         \\ asmLib.split_bytes_in_memory_tac 4
         \\ fs []
         \\ imp_res_tac bytes_in_memory_thm2
         \\ next_state_tac1 (hd o tl) [true]
         \\ state_tac []
         \\ blastLib.BBLAST_TAC
         )
      >- (
         (*--------------
             Arith
           --------------*)
         next_tac `0`
         \\ Cases_on `a`
         >- (
            (*--------------
                Binop
              --------------*)
            print_tac "Binop"
            \\ Cases_on `r`
            \\ Cases_on `b`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
            )
            (*
              --------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ lfs enc_rwts
            \\ next_state_tac01
            \\ state_tac []
         )
         (*
           --------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ next_tac `0`
         \\ Cases_on `a`
         \\ Cases_on `m`
         \\ Cases_on `0w <= c`
         \\ lfs ([lem4, lem5] @ enc_rwts)
         >| [
             (* LDR + *)
             load_store_tac {word = true, neg = false, store = false},
             (* LDR - *)
             load_store_tac {word = true, neg = true, store = false},
             (* LDRB + *)
             load_store_tac {word = false, neg = false, store = false},
             (* LDRB - *)
             load_store_tac {word = false, neg = true, store = false},
             (* STR + *)
             load_store_tac {word = true, neg = false, store = true},
             (* STR - *)
             load_store_tac {word = true, neg = true, store = true},
             (* STRB + *)
             load_store_tac {word = false, neg = false, store = true},
             (* STRB - *)
             load_store_tac {word = false, neg = true, store = true}
         ]
      ) (* close Inst *)
      (*
        --------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ next_tac `0`
      \\ Cases_on `o'`
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      \\ qabbrev_tac `a = (25 >< 2) (c + 0xFFFFFFF8w): word24`
      \\ next_state_tac01
      \\ state_tac []
      \\ imp_res_tac lem9
      \\ imp_res_tac lem10
      \\ simp [arm_stepTheory.Aligned_numeric, aligned_sum]
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
      \\ Cases_on `r`
      >- cmp_tac false
      \\ cmp_tac true
      )
      (*
        --------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ next_tac `0`
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      \\ qabbrev_tac `a = (25 >< 2) (c + 0xFFFFFFF8w): word24`
      \\ next_state_tac01
      \\ state_tac []
      \\ imp_res_tac lem9
      \\ imp_res_tac lem10
      \\ simp [arm_stepTheory.Aligned_numeric, aligned_sum]
      )
   >- (
      (*
        --------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac `0`
      \\ lfs enc_rwts
      \\ next_state_tac01
      \\ imp_res_tac lem11
      \\ imp_res_tac lem12
      \\ state_tac []
      )
   >- (
      (*
        --------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ Cases_on `8w <= c`
      >| [
           Cases_on `c + 0xFFFFFFF8w <+ 256w`,
           Cases_on `-1w * c + 0x8w <+ 256w`
      ]
      >| let
            val tac1 =
               next_tac `0`
               \\ lfs enc_rwts
               \\ next_state_tac01
               \\ state_tac [lem14, decode_imm8_thm2, decode_imm8_thm5]
            val tac2 =
               next_tac `1`
               \\ lfs enc_rwts
               \\ asmLib.split_bytes_in_memory_tac 4
               \\ next_state_tac01
               \\ next_state_tac1 hd [true]
               \\ imp_res_tac bytes_in_memory_thm2
               \\ fs []
               \\ blast_byte_eq_tac
               \\ pop_assum SUBST1_TAC
               \\ state_tac [lem14]
               \\ asm_simp_tac std_ss [decode_imm8_thm4, decode_imm8_thm6]
         in
            [tac1, tac2, tac1, tac2]
         end
      )
      (*
        --------------
          no Cache
        --------------*)
   >- fs enc_rwts
   >- (
      (*
        --------------
          enc MOD 4 enc_ok
        --------------*)
      simp
         [SIMP_RULE (bool_ss++boolSimps.LET_ss) [arm6_config_def] arm6_encoding]
      )
   >- (
      (*
        --------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ Cases_on `i`
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      )
   >- (
      (*
        --------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `i`
      >| [Cases_on `ri` \\ Cases_on `cmp`, all_tac]
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      )
   >- (
      (*
        --------------
          Call enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lfs ([GSYM arm_stepTheory.Aligned, arm_stepTheory.Aligned_numeric,
               lem8] @ enc_rwts)
      )
   >- (
      (*
        --------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ lrw enc_rwts
      \\ rw []
      \\ blastLib.FULL_BBLAST_TAC
      )
      (*
        --------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [arm6_asm_deterministic_config]
   )

(*

val x64_enc_deterministic = proofManagerLib.top_thm ()

val x64_enc_deterministic = Theory.new_axiom ("x64_enc_deterministic",
   ``enc_deterministic x64_enc x64_config``)

   proofManagerLib.r
   set_trace "Goalstack.howmany_printed_subgoals" 60

*)

val () = export_theory ()
