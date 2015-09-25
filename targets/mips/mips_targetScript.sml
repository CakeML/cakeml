open HolKernel Parse boolLib bossLib
open lcsymtacs asmLib mips_stepLib;

val () = new_theory "mips_target"

val () = wordsLib.guess_lengths()

(* --- Configuration for MIPS --- *)

val eval = rhs o concl o EVAL
val min16 = eval ``sw2sw (INT_MINw: word16) : word64``
val max16 = eval ``sw2sw (INT_MAXw: word16) : word64``
val umax16 = eval ``w2w (UINT_MAXw: word16) : word64``

val mips_config_def = Define`
   mips_config =
   <| ISA_name := "mips"
    ; reg_count := 32
    ; avoid_regs := [0; 1]
    ; link_reg := SOME 31
    ; has_mem_32 := T
    ; two_reg_arith := F
    ; big_endian := T
    ; valid_imm := (\b i. case b of
                             INL Sub  => F
                           | INL And  => 0w <= i /\ i <= ^umax16
                           | INL Or   => 0w <= i /\ i <= ^umax16
                           | INL Xor  => 0w <= i /\ i <= ^umax16
                           | INR Test => 0w <= i /\ i <= ^umax16
                           | _ =>    ^min16 <= i /\ i <= ^max16)
    ; addr_offset_min := ^min16
    ; addr_offset_max := ^max16
    ; jump_offset_min := ^min16
    ; jump_offset_max := ^max16
    ; cjump_offset_min := ^min16
    ; cjump_offset_max := ^max16
    ; loc_offset_min := ^min16 + 12w
    ; loc_offset_max := ^max16 + 8w
    ; code_alignment := 2
    |>`

(* --- The next-state function --- *)

val mips_next_def = Define `mips_next = THE o NextStateMIPS`

(* --- Relate ASM and MIPS states --- *)

val mips_asm_state_def = Define`
   mips_asm_state a s =
   (s.exception = NoException) /\
   s.CP0.Config.BE /\ ~s.CP0.Status.RE /\ ~s.exceptionSignalled /\
   (s.BranchDelay = NONE) /\ (s.BranchTo = NONE) /\
   (a.pc = s.PC) /\ aligned 2 s.PC /\
   (!i. 1 < i /\ i < 32 ==> (a.regs i = s.gpr (n2w i))) /\
   (a.mem = s.MEM)`

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
   (mips_memop Load32  = INL LWU) /\
   (mips_memop Load8   = INL LBU) /\
   (mips_memop Store   = INR SD) /\
   (mips_memop Store32 = INR SW) /\
   (mips_memop Store8  = INR SB)`

val nop = ``Shift (SLL (0w, 0w, 0w))``

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
   (mips_enc (Inst (Arith (Binop Sub r1 r2 (Imm i)))) = []) /\
   (mips_enc (Inst (Arith (Binop bop r1 r2 (Imm i)))) =
       mips_encode (ArithI (mips_bop_i bop (n2w r2, n2w r1, w2w i)))) /\
   (mips_enc (Inst (Arith (Shift sh r1 r2 n))) =
       let (f, n) = if n < 32 then (mips_sh, n) else (mips_sh32, n - 32) in
         mips_encode (Shift (f sh (n2w r2, n2w r1, n2w n)))) /\
   (mips_enc (Inst (Mem mop r1 (Addr r2 a))) =
       case mips_memop mop of
          INL f => mips_encode (Load (f (n2w r2, n2w r1, w2w a)))
        | INR f => mips_encode (Store (f (n2w r2, n2w r1, w2w a)))) /\
   (mips_enc (Jump a) =
       encs [Branch (BEQ (0w, 0w, w2w (a >>> 2) - 1w)); ^nop]) /\
   (mips_enc (JumpCmp Equal r1 (Reg r2) a) =
       encs [Branch (BEQ (n2w r1, n2w r2, w2w (a >>> 2) - 1w)); ^nop]) /\
   (mips_enc (JumpCmp Less r1 (Reg r2) a) =
       encs [ArithR (SLT (n2w r1, n2w r2, 1w));
             Branch (BNE (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Lower r1 (Reg r2) a) =
       encs [ArithR (SLTU (n2w r1, n2w r2, 1w));
             Branch (BNE (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Test r1 (Reg r2) a) =
       encs [ArithR (AND (n2w r1, n2w r2, 1w));
             Branch (BEQ (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Equal r (Imm i) a) =
       encs [ArithI (DADDIU (0w, 1w, w2w i));
             Branch (BEQ (n2w r, 1w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Less r (Imm i) a) =
       encs [ArithI (SLTI (n2w r, 1w, w2w i));
             Branch (BNE (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Lower r (Imm i) a) =
       encs [ArithI (SLTIU (n2w r, 1w, w2w i));
             Branch (BNE (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
   (mips_enc (JumpCmp Test r (Imm i) a) =
       encs [ArithI (ANDI (n2w r, 1w, w2w i));
             Branch (BEQ (1w, 0w, w2w (a >>> 2) - 2w));
             ^nop]) /\
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

val fetch_decode_def = Define`
   fetch_decode (b0 :: b1 :: b2 :: b3 :: (rest: word8 list)) =
   (Decode (b0 @@ b1 @@ b2 @@ b3), rest)`

val all_same_def = Define`
   (all_same (h::t) = EVERY ((=) h) t)`

val when_nop_def = Define`
   when_nop l (r: 64 asm) = case fetch_decode l of (^nop, _) => r`

val mips_dec_def = Lib.with_flag (Globals.priming, SOME "_") Define`
   mips_dec l =
   case fetch_decode l of
      (ArithR (SLT (r1, r2, 1w)), rest) =>
        (case fetch_decode rest of
            (Branch (BNE (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Less (w2n r1) (Reg (w2n r2)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithR (SLTU (r1, r2, 1w)), rest) =>
        (case fetch_decode rest of
            (Branch (BNE (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Lower (w2n r1) (Reg (w2n r2)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithR (AND (r1, r2, 1w)), rest) =>
        (case fetch_decode rest of
            (Branch (BEQ (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Test (w2n r1) (Reg (w2n r2)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithI (DADDIU (0w, 1w, i)), rest) =>
        (case fetch_decode rest of
            (Branch (BEQ (r, 1w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Equal (w2n r) (Imm (sw2sw i)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithI (ORI (0w, r, i)), _) =>
        Inst (Const (w2n r) (w2w i : word64))
    | (ArithI (ADDIU (0w, r, i)), _) =>
        Inst (Const (w2n r) (sw2sw i : word64))
    | (ArithI (SLTI (r, 1w, i)), rest) =>
        (case fetch_decode rest of
            (Branch (BNE (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Less (w2n r) (Imm (sw2sw i)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithI (SLTIU (r, 1w, i)), rest) =>
        (case fetch_decode rest of
            (Branch (BNE (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Lower (w2n r) (Imm (sw2sw i)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithI (ANDI (r1, 1w, i)), rest) =>
        (case fetch_decode rest of
            (Branch (BEQ (1w, 0w, a)), rest1) =>
               when_nop rest1
                 (JumpCmp Test (w2n r1) (Imm (w2w i)) (sw2sw ((a + 2w) << 2)))
          | _ => ARB)
    | (ArithI (ORI (31w, 1w, 0w)), rest0) =>
        (case fetch_decode rest0 of
            (Branch (BLTZAL (0w, 0w)), rest1) =>
              (case fetch_decode rest1 of
                  (ArithI (DADDIU (31w, rr, i)), rest2) =>
                    (case fetch_decode rest2 of
                        (ArithI (ORI (1w, 31w, 0w)), _) =>
                           Loc (w2n rr) (sw2sw i + 12w)
                      | _ => ARB)
                | _ => ARB)
          | _ => ARB)
    | (ArithI (LUI (r0, i0)), rest0) =>
        (case fetch_decode rest0 of
            (ArithI (XORI (r1, r2, i1)), _) =>
                if all_same [r0; r1; r2] then
                   Inst (Const (w2n r0) (sw2sw ((i0 @@ i1) : word32)))
                else
                   ARB
          | (ArithI (ORI (r1, r2, i1)), rest1) =>
              (case fetch_decode rest1 of
                  (Shift (DSLL (r3, r4, 16w)), rest2) =>
                    (case fetch_decode rest2 of
                        (ArithI (ORI (r5, r6, i2)), rest3) =>
                             (case fetch_decode rest3 of
                                 (Shift (DSLL (r7, r8, 16w)), rest4) =>
                                   (case fetch_decode rest4 of
                                       (ArithI (ORI (r9, r10, i3)), _) =>
                                          if all_same [r0; r1; r2; r3; r4; r5;
                                                       r6; r7; r8; r9; r10]
                                             then Inst (Const (w2n r0)
                                                         (i0 @@ i1 @@ i2 @@ i3))
                                          else ARB
                                     | _ => ARB)
                               | _ => ARB)
                      | _ => ARB)
                | _ => ARB)
          | _ => ARB)
    | (ArithR (DADDU (r1, r2, r3)), _) =>
        Inst (Arith (Binop Add (w2n r3) (w2n r1) (Reg (w2n r2))))
    | (ArithR (DSUBU (r1, r2, r3)), _) =>
        Inst (Arith (Binop Sub (w2n r3) (w2n r1) (Reg (w2n r2))))
    | (ArithR (AND (r1, r2, r3)), _) =>
        Inst (Arith (Binop And (w2n r3) (w2n r1) (Reg (w2n r2))))
    | (ArithR (OR (r1, r2, r3)), _) =>
        Inst (Arith (Binop Or (w2n r3) (w2n r1) (Reg (w2n r2))))
    | (ArithR (XOR (r1, r2, r3)), _) =>
        Inst (Arith (Binop Xor (w2n r3) (w2n r1) (Reg (w2n r2))))
    | (ArithI (DADDIU (r1, r2, i)), _) =>
        Inst (Arith (Binop Add (w2n r2) (w2n r1) (Imm (sw2sw i))))
    | (ArithI (ANDI (r1, r2, i)), _) =>
        Inst (Arith (Binop And (w2n r2) (w2n r1) (Imm (w2w i))))
    | (ArithI (ORI (r1, r2, i)), _) =>
        Inst (Arith (Binop Or (w2n r2) (w2n r1) (Imm (w2w i))))
    | (ArithI (XORI (r1, r2, i)), _) =>
        Inst (Arith (Binop Xor (w2n r2) (w2n r1) (Imm (w2w i))))
    | (Shift (SLL (0w, 0w, 0w)), _) =>
        Inst Skip
    | (Shift (DSLL (r1, r2, n)), _) =>
        Inst (Arith (Shift Lsl (w2n r2) (w2n r1) (w2n n)))
    | (Shift (DSRL (r1, r2, n)), _) =>
        Inst (Arith (Shift Lsr (w2n r2) (w2n r1) (w2n n)))
    | (Shift (DSRA (r1, r2, n)), _) =>
        Inst (Arith (Shift Asr (w2n r2) (w2n r1) (w2n n)))
    | (Shift (DSLL32 (r1, r2, n)), _) =>
        Inst (Arith (Shift Lsl (w2n r2) (w2n r1) (w2n n + 32)))
    | (Shift (DSRL32 (r1, r2, n)), _) =>
        Inst (Arith (Shift Lsr (w2n r2) (w2n r1) (w2n n + 32)))
    | (Shift (DSRA32 (r1, r2, n)), _) =>
        Inst (Arith (Shift Asr (w2n r2) (w2n r1) (w2n n + 32)))
    | (Load (LD (r2, r1, a)), _) =>
        Inst (Mem Load (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Load (LWU (r2, r1, a)), _) =>
        Inst (Mem Load32 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Load (LBU (r2, r1, a)), _) =>
        Inst (Mem Load8 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Store (SD (r2, r1, a)), _) =>
        Inst (Mem Store (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Store (SW (r2, r1, a)), _) =>
        Inst (Mem Store32 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Store (SB (r2, r1, a)), _) =>
        Inst (Mem Store8 (w2n r1) (Addr (w2n r2) (sw2sw a)))
    | (Branch (BEQ (r1, r2, a)), rest) =>
        when_nop rest
           (let aa = sw2sw ((a + 1w) << 2) in
               if (r1 = 0w) /\ (r1 = r2) then
                  Jump aa
               else
                  JumpCmp Equal (w2n r1) (Reg (w2n r2)) aa)
    | (Branch (BGEZAL (0w, a)), rest) =>
        when_nop rest (Call (sw2sw ((a + 1w) << 2)))
    | (Branch (BLTZAL (0w, 0w)), rest) =>
        (case fetch_decode rest of
             (ArithI (DADDIU (31w, 31w, i)), rest2) =>
            Loc 31 (sw2sw i + 8w)
          | _ => ARB)
    | (Branch (JR r), rest) =>
        when_nop rest (JumpReg (w2n r))
    | _ => ARB`

(* ------------------------------------------------------------------------- *)

(* some lemmas ---------------------------------------------------------- *)

val mips_asm_state =
   REWRITE_RULE [DECIDE ``1 < i = i <> 0n /\ i <> 1n``] mips_asm_state_def

val bytes_in_memory_thm = Q.prove(
   `!w s state a b c d.
      mips_asm_state s state /\
      bytes_in_memory s.pc [a; b; c; d] s.mem s.mem_domain ==>
      (state.exception = NoException) /\
      state.CP0.Config.BE /\
      ~state.CP0.Status.RE /\
      ~state.exceptionSignalled /\
      (state.BranchDelay = NONE) /\
      (state.BranchTo = NONE) /\
      ((1 >< 0) state.PC = 0w: word2) /\
      aligned 2 state.PC /\
      (state.MEM state.PC = a) /\
      (state.MEM (state.PC + 1w) = b) /\
      (state.MEM (state.PC + 2w) = c) /\
      (state.MEM (state.PC + 3w) = d)`,
   rw [mips_asm_state_def, asmSemTheory.bytes_in_memory_def,
       alignmentTheory.aligned_extract]
   \\ simp []
   \\ blastLib.FULL_BBLAST_TAC
   )

val bytes_in_memory_thm2 = Q.prove(
   `!w s state a b c d.
      mips_asm_state s state /\
      bytes_in_memory (s.pc + w) [a; b; c; d] s.mem s.mem_domain ==>
      (state.MEM (state.PC + w) = a) /\
      (state.MEM (state.PC + w + 1w) = b) /\
      (state.MEM (state.PC + w + 2w) = c) /\
      (state.MEM (state.PC + w + 3w) = d)`,
   rw [mips_asm_state_def, asmSemTheory.bytes_in_memory_def]
   \\ simp []
   )

val lem1 = asmLib.v2w_BIT_n2w 5

val lem4 =
   blastLib.BBLAST_CONV ``(1 >< 0) (x: word64) = 0w: word2``
   |> Thm.EQ_IMP_RULE |> fst

val lem5 = Q.prove(
   `!n s state.
     n <> 0 /\ n <> 1 /\ n < 32 /\ mips_asm_state s state ==>
     (s.regs n = state.gpr (n2w n))`,
   lrw [mips_asm_state]
   )

val lem6 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
       0xFFFFFFFFFFFF8000w <= c /\ c <= 32767w ==>
       (sw2sw
          (v2w [c ' 15; c ' 14; c ' 13; c ' 12; c ' 11;
                c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                c ' 4; c ' 3; c ' 2; c ' 1; c ' 0]: word16) = c)``

val lem7 = Q.prove(
   `(!c: word64. aligned 3 c ==> ((2 >< 0) c = 0w: word3)) /\
    (!c: word64. aligned 2 c ==> ((1 >< 0) c = 0w: word2))`,
   simp [alignmentTheory.aligned_extract]
   \\ blastLib.BBLAST_TAC
   )

val lem8 =
   blastLib.BBLAST_PROVE
     ``w2w (b7: word8) ||
       w2w (b0: word8) << 56 ||
       w2w (b1: word8) << 48 ||
       w2w (b3: word8) << 32 ||
       w2w (b5: word8) << 16 ||
       w2w (b2: word8) << 40 ||
       w2w (b4: word8) << 24 ||
       w2w (b6: word8) << 8 =
       b0 @@ b1 @@ b2 @@ b3 @@ b4 @@ b5 @@ b6 @@ b7``

val lem9 =
   blastLib.BBLAST_PROVE
     ``w2w (b3: word8) ||
       w2w (b0: word8) << 24 ||
       w2w (b1: word8) << 16 ||
       w2w (b2: word8) << 8 =
       w2w (b0 @@ b1 @@ b2 @@ b3) : word64``

val lem10 =
   blastLib.BBLAST_PROVE
     ``!c: word64.
       0x0w <= c /\ c <= 65535w ==>
       (w2w
          (v2w [c ' 15; c ' 14; c ' 13; c ' 12; c ' 11;
                c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5;
                c ' 4; c ' 3; c ' 2; c ' 1; c ' 0]: word16) = c)``

(* some rewrites ---------------------------------------------------------- *)

val encode_rwts =
   let
      open mipsTheory
   in
      [mips_enc_def, encs_def, mips_encode_def, mips_bop_r_def, mips_bop_i_def,
       mips_sh_def, mips_sh32_def, mips_memop_def,
       Encode_def, form1_def, form2_def, form3_def, form4_def, form5_def]
   end

val enc_rwts =
  [mips_config_def] @ encode_rwts @ asmLib.asm_ok_rwts @ asmLib.asm_rwts

val enc_ok_rwts =
  [asmPropsTheory.enc_ok_def, mips_config_def] @
  encode_rwts @ asmLib.asm_ok_rwts

val dec_rwts =
   [mips_dec_def, fetch_decode_def, all_same_def, when_nop_def]

(* some custom tactics ---------------------------------------------------- *)

local
   val bool1 = utilsLib.rhsc o blastLib.BBLAST_CONV o fcpSyntax.mk_fcp_index
   fun boolify n tm =
      List.tabulate (n, fn i => bool1 (tm, numLib.term_of_int (n - 1 - i)))
   val bytes = List.concat o List.map (boolify 8)
   val v2w_n2w_rule = CONV_RULE (Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV)
   fun dec tm =
      let
         val l = listSyntax.mk_list (boolify 32 tm, Type.bool)
         val w = bitstringSyntax.mk_v2w (l, fcpSyntax.mk_int_numeric_type 32)
         val th1 = blastLib.BBLAST_PROVE (boolSyntax.mk_eq (w, tm))
      in
         l |> mips_stepLib.mips_decode
           |> Drule.DISCH_ALL
           |> v2w_n2w_rule
           |> REWRITE_RULE [th1, lem1]
      end
   val s1 = HolKernel.syntax_fns1 "mips"
   val (_, _, dest_Decode, is_Decode) = s1 "Decode"
   val (_, mk_mips_state_BranchDelay, _, _) = s1 "mips_state_BranchDelay"
   val (_, _, dest_NextStateMIPS, is_NextStateMIPS) =
      HolKernel.syntax_fns1 "mips_step" "NextStateMIPS"
   val get_BranchDelay =
      (utilsLib.rhsc o Conv.QCONV (SIMP_CONV (srw_ss()) []) o
       mk_mips_state_BranchDelay)
   val find_Decode = HolKernel.bvk_find_term (is_Decode o snd) dest_Decode
   val find_NextStateMIPS =
      dest_NextStateMIPS o List.hd o HolKernel.find_terms is_NextStateMIPS
   val ev = mips_stepLib.mips_eval true
   val s = ``s: mips_state``
   val d = ``d: word64 option``
   fun step the_state bd l =
      let
         val v = listSyntax.mk_list (bytes l, Type.bool)
         val thms = ev v
         val _ = Lib.mem (List.length thms) [1, 2] orelse
                 ( List.app print_thm thms
                 ; raise ERR "next_state_tac" "expecting one or two theorems"
                 )
         val f = if optionSyntax.is_some bd
                    then Thm.INST [d |-> Term.rand bd] o List.last
                 else List.hd
      in
         (Thm.INST [s |-> the_state] o Drule.DISCH_ALL o f) thms
      end
in
   fun decode_tac' (asl, g) =
      (case find_Decode g of
          SOME tm =>
           let
              val dec_thm = dec tm
           (* val () = (print_thm dec_thm; print "\n") *)
           in
              simp [dec_thm]
           end
        | NONE => NO_TAC) (asl, g)
   fun next_state_tac (asl, g) =
     (let
         val x as (pc, l, _, _) =
            List.last
              (List.mapPartial (Lib.total asmLib.dest_bytes_in_memory) asl)
         val tm = asmLib.mk_bytes_in_memory x
         val the_state = find_NextStateMIPS g
         val bd = get_BranchDelay the_state
         val l = fst (listSyntax.dest_list l)
         val th = case Lib.total wordsSyntax.dest_word_add pc of
                     SOME (_, w) => Thm.SPEC w bytes_in_memory_thm2
                   | NONE => bytes_in_memory_thm
      in
         imp_res_tac th
         \\ assume_tac (step the_state bd l)
         \\ rfs [lem1, lem6, lem7, lem10,
                 combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ Tactical.PAT_ASSUM tm kall_tac
         \\ asmLib.byte_eq_tac
         \\ rfs [lem1, lem4, combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
         \\ TRY (Q.PAT_ASSUM `NextStateMIPS qq = qqq` kall_tac)
      end
      handle List.Empty => FAIL_TAC "next_state_tac: empty") (asl, g)
end

val state_tac =
   fs [mips_asm_state, alignmentTheory.aligned_numeric, lem8, lem9]
   \\ rw [combinTheory.APPLY_UPDATE_THM,
          DECIDE ``~(n < 32n) ==> (n - 32 + 32 = n)``]

val decode_tac =
   simp enc_rwts
   \\ REPEAT strip_tac
   \\ simp dec_rwts
   \\ REPEAT decode_tac'
   \\ NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
   \\ blastLib.FULL_BBLAST_TAC

fun print_tac s gs = (print (s ^ "\n"); ALL_TAC gs)

local
   fun number_of_instructions asl =
      case asmLib.strip_bytes_in_memory (List.last asl) of
         SOME l => List.length l div 4
       | NONE => raise ERR "number_of_instructions" ""
   fun next_tac' gs =
      let
         val j = number_of_instructions (fst gs)
         val i = j - 1
         val n = numLib.term_of_int i
      in
         exists_tac n
         \\ simp [mips_next_def, numeralTheory.numeral_funpow]
         \\ NTAC i (split_bytes_in_memory_tac 4)
         \\ NTAC j next_state_tac
         \\ REPEAT (Q.PAT_ASSUM `state.MEM qq = bn` kall_tac)
         \\ state_tac
      end gs
in
   val next_tac =
      lfs enc_rwts
      \\ imp_res_tac lem5
      \\ fs []
      \\ next_tac'
   val bnext_tac =
      next_tac
      \\ NO_STRIP_FULL_SIMP_TAC std_ss [alignmentTheory.aligned_extract]
      \\ blastLib.FULL_BBLAST_TAC
end

val enc_ok_tac =
   full_simp_tac (srw_ss()++boolSimps.LET_ss)
      (asmPropsTheory.offset_monotonic_def :: enc_ok_rwts)

(* -------------------------------------------------------------------------
   mips_asm_deterministic
   mips_backend_correct
   ------------------------------------------------------------------------- *)

val mips_encoding = Count.apply Q.prove (
   `!i. asm_ok i mips_config ==>
        let l = mips_enc i in
        let n = LENGTH l in
           (!x. mips_dec (l ++ x) = i) /\ (n MOD 4 = 0) /\ n <> 0`,
   Cases
   >- (
      (*--------------
          Inst
        --------------*)
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ decode_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ((31 >< 16) c = 0w: word16)`
         >- decode_tac
         \\ Cases_on `((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c = -1w: word16) /\
                      ((15 >< 0) c : word16) ' 15`
         >- decode_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ~((31 >< 16) c : word16) ' 15 \/
                      ((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c : word16) ' 15`
         \\ decode_tac
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
            \\ decode_tac
            \\ Cases_on `n0 = 31`
            \\ rw []
            \\ blastLib.FULL_BBLAST_TAC
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ Cases_on `n1 < 32`
            \\ decode_tac
         )
      \\ print_tac "Mem"
      \\ Cases_on `a`
      \\ Cases_on `m`
      \\ decode_tac
      )
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      \\ decode_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ decode_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ decode_tac
      )
      (*--------------
          Loc
        --------------*)
   \\ print_tac "Loc"
   \\ Cases_on `n = 31`
   \\ decode_tac
   )

val mips_asm_deterministic = Q.store_thm("mips_asm_deterministic",
   `asm_deterministic mips_enc mips_config`,
   metis_tac [asmPropsTheory.decoder_asm_deterministic,
              asmPropsTheory.has_decoder_def, mips_encoding]
   )

val mips_asm_deterministic_config =
   SIMP_RULE (srw_ss()) [mips_config_def] mips_asm_deterministic

val enc_ok_rwts =
   SIMP_RULE (bool_ss++boolSimps.LET_ss) [mips_config_def] mips_encoding ::
   enc_ok_rwts

val mips_backend_correct = Count.apply Q.store_thm ("mips_backend_correct",
   `backend_correct mips_enc mips_config mips_next mips_asm_state`,
   simp [asmPropsTheory.backend_correct_def]
   \\ REVERSE conj_tac
   >| [
      rw [asmSemTheory.asm_step_def] \\ Cases_on `i`,
      srw_tac [boolSimps.LET_ss] enc_ok_rwts
   ]
   >- (
      (*--------------
          Inst
        --------------*)
      Cases_on `i'`
      >- (
         (*--------------
             Skip
           --------------*)
         print_tac "Skip"
         \\ next_tac
         )
      >- (
         (*--------------
             Const
           --------------*)
         print_tac "Const"
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ((31 >< 16) c = 0w: word16)`
         >- bnext_tac
         \\ Cases_on `((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c = -1w: word16) /\
                      ((15 >< 0) c : word16) ' 15`
         >- bnext_tac
         \\ Cases_on `((63 >< 32) c = 0w: word32) /\
                      ~((31 >< 16) c : word16) ' 15 \/
                      ((63 >< 32) c = -1w: word32) /\
                      ((31 >< 16) c : word16) ' 15`
         \\ bnext_tac
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
            \\ bnext_tac
            )
            (*--------------
                Shift
              --------------*)
            \\ print_tac "Shift"
            \\ Cases_on `s`
            \\ Cases_on `n1 < 32`
            \\ next_tac
         )
         (*--------------
             Mem
           --------------*)
         \\ print_tac "Mem"
         \\ Cases_on `a`
         \\ Cases_on `m`
         \\ next_tac
         \\ rw [boolTheory.FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM]
         \\ full_simp_tac
              (srw_ss()++wordsLib.WORD_EXTRACT_ss++wordsLib.WORD_CANCEL_ss) []
      ) (* close Inst *)
      (*--------------
          Jump
        --------------*)
   >- (
      print_tac "Jump"
      \\ bnext_tac
      )
   >- (
      (*--------------
          JumpCmp
        --------------*)
      print_tac "JumpCmp"
      \\ Cases_on `r`
      \\ Cases_on `c`
      >| [
         Cases_on `state.gpr (n2w n) = state.gpr (n2w n')`,
         Cases_on `state.gpr (n2w n) <+ state.gpr (n2w n')`,
         Cases_on `state.gpr (n2w n) < state.gpr (n2w n')`,
         Cases_on `state.gpr (n2w n) && state.gpr (n2w n') = 0w`,
         Cases_on `state.gpr (n2w n) = c'`,
         Cases_on `state.gpr (n2w n) <+ c'`,
         Cases_on `state.gpr (n2w n) < c'`,
         Cases_on `state.gpr (n2w n) && c' = 0w`
      ]
      \\ bnext_tac
      )
      (*--------------
          Call
        --------------*)
   >- (
      print_tac "Call"
      \\ bnext_tac
      )
   >- (
      (*--------------
          JumpReg
        --------------*)
      print_tac "JumpReg"
      \\ next_tac
      )
   >- (
      (*--------------
          Loc
        --------------*)
      print_tac "Loc"
      \\ Cases_on `n = 31`
      \\ bnext_tac
      )
   >- (
      (*--------------
          Jump enc_ok
        --------------*)
      print_tac "enc_ok: Jump"
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          JumpCmp enc_ok
        --------------*)
      print_tac "enc_ok: JumpCmp"
      \\ Cases_on `ri`
      \\ Cases_on `cmp`
      \\ enc_ok_tac
      )
   >- (
      (*--------------
          Call enc_ok
        --------------*)
      enc_ok_tac
      )
   >- (
      (*--------------
          Loc enc_ok
        --------------*)
      print_tac "enc_ok: Loc"
      \\ Cases_on `r = 31`
      \\ enc_ok_tac
      )
      (*--------------
          asm_deterministic
        --------------*)
   \\ print_tac "asm_deterministic"
   \\ rewrite_tac [mips_asm_deterministic_config]
   )

val () = export_theory ()
