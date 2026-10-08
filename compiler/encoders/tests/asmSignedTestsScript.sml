(*
  Executable regression checks for signed ASM operations and encodings.
*)
Theory asmSignedTests
Ancestors
  x64_target arm7_target arm8_target mips_target riscv_target ag32_target
Libs
  preamble x64_targetLib arm7_targetLib arm8_targetLib mips_targetLib
  riscv_targetLib

(* Add `0 quot -1 = 0` and `0 rem -1 = 0`, which the integer numeral
   conversions leave unevaluated. *)
val signed_compset = computeLib.add_thms
  (map (fn th => MP (Q.SPEC `-1` th)
     (EQT_ELIM (EVAL ``(-1:int) <> 0``)))
    [integerTheory.INT_QUOT_0, integerTheory.INT_REM0])
  (List.foldl (fn (tm, cs) => computeLib.scrub_const cs tm)
    (computeLib.the_compset ())
    [``x64_enc``, ``arm7_enc``, ``arm8_enc``, ``mips_enc``, ``riscv_enc``]);
val signed_eval = computeLib.CBV_CONV
  (List.foldl (fn (extend, cs) => extend cs) signed_compset
    [x64_targetLib.add_x64_encode_compset,
     arm7_targetLib.add_arm7_encode_compset,
     arm8_targetLib.add_arm8_encode_compset,
     mips_targetLib.add_mips_encode_compset,
     riscv_targetLib.add_riscv_encode_compset]);

fun check tm =
  let val result = rhs (concl (signed_eval tm)) in
    if aconv result T then ()
    else raise Fail ("Signed ASM regression: " ^ term_to_string tm ^
                     "\nEvaluated result: " ^ term_to_string result)
  end;

(* Byte registers SIL/DIL and R8B--R15B require a REX prefix; AL--BL do not. *)
val () = List.app (fn (rd, rb, ro) =>
  let
    val d = numSyntax.term_of_int rd
    val b = numSyntax.term_of_int rb
    val oreg = numSyntax.term_of_int ro
  in
    check ``asm_ok (Inst (Arith (IMul ^d ^d ^b ^oreg))) x64_config``;
    check ``LENGTH (x64_ast (Inst (Arith (IMul ^d ^d ^b ^oreg)))) = 3``;
    check ``LENGTH (x64_enc (Inst (Arith (IMul ^d ^d ^b ^oreg)))) =
             (if ^oreg < 4 then 10 else 12)``
  end)
  [(0, 1, 2), (8, 9, 10), (0, 6, 6), (0, 7, 7), (6, 7, 0)];

val () = List.app (fn divisor =>
  let val b = numSyntax.term_of_int divisor in
    check ``asm_ok (Inst (Arith (IDiv 0 2 0 ^b))) x64_config``;
    check ``LENGTH (x64_ast (Inst (Arith (IDiv 0 2 0 ^b)))) = 3``;
    check ``LENGTH (x64_enc (Inst (Arith (IDiv 0 2 0 ^b)))) = 10``
  end) [0, 1, 6, 7, 8, 15];

val () = check ``~asm_ok (Inst (Arith (IDiv 0 2 0 2))) x64_config``;
val () = check ``~asm_ok (Inst (Arith (IMul 0 0 1 0))) x64_config``;

(* GNU as reference bytes, including the compact 32-bit zero extension. *)
val () = check ``x64_enc (Inst (Arith (IMul 0 0 1 2))) =
                  [72w; 15w; 175w; 193w; 15w; 144w; 194w; 15w; 182w; 210w]``;
val () = check ``x64_enc (Inst (Arith (IMul 8 8 9 10))) =
  [0x4Dw; 0x0Fw; 0xAFw; 0xC1w; 0x41w; 0x0Fw; 0x90w; 0xC2w;
   0x4Dw; 0x0Fw; 0xB6w; 0xD2w]``;
val () = check ``x64_enc (Inst (Arith (IMul 0 0 6 6))) =
  [0x48w; 0x0Fw; 0xAFw; 0xC6w; 0x40w; 0x0Fw; 0x90w; 0xC6w;
   0x48w; 0x0Fw; 0xB6w; 0xF6w]``;
val () = check ``x64_enc (Inst (Arith (IMul 0 0 7 7))) =
  [0x48w; 0x0Fw; 0xAFw; 0xC7w; 0x40w; 0x0Fw; 0x90w; 0xC7w;
   0x48w; 0x0Fw; 0xB6w; 0xFFw]``;
val () = check ``x64_enc (Inst (Arith (IDiv 0 2 0 1))) =
                  [72w; 137w; 194w; 72w; 193w; 250w; 63w; 72w; 247w; 249w]``;

val () = check ``LENGTH (arm7_enc (Inst (Arith (IMul 0 0 1 2)))) = 16``;
val () = check ``LENGTH (arm8_ast (Inst (Arith (IMul 0 0 1 2)))) = 4``;
val () = check ``LENGTH (riscv_ast (Inst (Arith (IMul 5 5 6 7)))) = 5``;
val () = check ``LENGTH (mips_ast (Inst (Arith (IMul 2 2 3 4)))) = 6``;
val () = check ``LENGTH (arm8_enc (Inst (Arith (IMul 0 0 1 2)))) = 16``;
val () = check ``LENGTH (riscv_enc (Inst (Arith (IMul 5 5 6 7)))) = 20``;
val () = check ``LENGTH (mips_enc (Inst (Arith (IMul 2 2 3 4)))) = 24``;

(* GNU as reference bytes for the ARMv7 and ARMv8 sequences. *)
val () = check ``arm7_enc (Inst (Arith (IMul 0 0 1 2))) =
  [0x90w; 0x01w; 0xC2w; 0xE0w; 0xC0w; 0x0Fw; 0x52w; 0xE1w;
   0x00w; 0x20w; 0xA0w; 0x03w; 0x01w; 0x20w; 0xA0w; 0x13w]``;
val () = check ``arm8_enc (Inst (Arith (IMul 0 0 1 2))) =
  [0x1Aw; 0x7Cw; 0x41w; 0x9Bw; 0x00w; 0x7Cw; 0x01w; 0x9Bw;
   0x5Fw; 0xFFw; 0x80w; 0xEBw; 0xE2w; 0x07w; 0x9Fw; 0x9Aw]``;
val () = check ``arm8_enc (Inst (Arith (IDiv 0 1 2 3))) =
  [0x40w; 0x0Cw; 0xC3w; 0x9Aw; 0x01w; 0x88w; 0x03w; 0x9Bw]``;
val () = check ``arm8_enc (Inst (Arith (IDiv 0 1 0 3))) =
  [0x1Aw; 0x0Cw; 0xC3w; 0x9Aw; 0x41w; 0x83w; 0x03w; 0x9Bw;
   0xE0w; 0x03w; 0x1Aw; 0xAAw]``;

(* GNU as reference bytes for MIPS, in the target's big-endian order. *)
val () = check ``mips_enc (Inst (Arith (IMul 2 2 3 4))) =
  [0x00w; 0x43w; 0x00w; 0x1Cw; 0x00w; 0x00w; 0x10w; 0x12w;
   0x00w; 0x00w; 0x20w; 0x10w; 0x00w; 0x02w; 0x0Fw; 0xFFw;
   0x00w; 0x81w; 0x20w; 0x26w; 0x00w; 0x04w; 0x20w; 0x2Bw]``;
val () = check ``mips_enc (Inst (Arith (IDiv 2 3 2 3))) =
  [0x00w; 0x43w; 0x00w; 0x1Ew; 0x00w; 0x00w; 0x10w; 0x12w;
   0x00w; 0x00w; 0x18w; 0x10w]``;

(* Quotient aliases need one scratch result and a final register move. *)
val () = check ``LENGTH (arm8_ast (Inst (Arith (IDiv 0 1 2 3)))) = 2``;
val () = check ``LENGTH (arm8_ast (Inst (Arith (IDiv 0 1 0 3)))) = 3``;
val () = check ``LENGTH (arm8_ast (Inst (Arith (IDiv 0 1 2 0)))) = 3``;
val () = check ``LENGTH (riscv_ast (Inst (Arith (IDiv 5 6 7 8)))) = 2``;
val () = check ``LENGTH (riscv_ast (Inst (Arith (IDiv 5 6 5 8)))) = 3``;
val () = check ``LENGTH (riscv_ast (Inst (Arith (IDiv 5 6 7 5)))) = 3``;
val () = check ``LENGTH (mips_ast (Inst (Arith (IDiv 2 3 2 3)))) = 3``;
val () = check ``LENGTH (arm8_enc (Inst (Arith (IDiv 0 1 2 3)))) = 8``;
val () = check ``LENGTH (arm8_enc (Inst (Arith (IDiv 0 1 0 3)))) = 12``;
val () = check ``LENGTH (riscv_enc (Inst (Arith (IDiv 5 6 7 8)))) = 8``;
val () = check ``LENGTH (riscv_enc (Inst (Arith (IDiv 5 6 5 8)))) = 12``;
val () = check ``LENGTH (mips_enc (Inst (Arith (IDiv 2 3 2 3)))) = 12``;

val () = check ``~asm_ok (Inst (Arith (IDiv 0 1 2 3))) arm7_config``;
val () = check ``~asm_ok (Inst (Arith (IMul 0 1 2 3))) ag32_config``;
val () = check ``~asm_ok (Inst (Arith (IDiv 0 1 2 3))) ag32_config``;

(* Signed division differs from floor division for opposite-sign inputs. *)
val () = List.app (fn (a, b, q, r) =>
  let
    val dividend = intSyntax.term_of_int (Arbint.fromInt a)
    val divisor = intSyntax.term_of_int (Arbint.fromInt b)
    val quotient = intSyntax.term_of_int (Arbint.fromInt q)
    val remainder = intSyntax.term_of_int (Arbint.fromInt r)
  in
    check ``let s = (ARB : 64 asm_state) with
              <|regs := (\reg. if reg = 0 then i2w ^dividend
                              else if reg = 1 then i2w ^divisor else 0w);
                failed := F|>;
                result = arith_upd (IDiv 0 1 0 1) s
            in ~result.failed /\ w2i (result.regs 0) = ^quotient /\
               w2i (result.regs 1) = ^remainder``
  end)
  [(7, 3, 2, 1), (~7, 3, ~2, ~1), (7, ~3, ~2, 1),
   (~7, ~3, 2, ~1), (~6, 3, ~2, 0), (0, ~1, 0, 0)];

val () = check ``let s = (ARB : 64 asm_state) with
                  <|regs := (\reg. if reg = 0 then INT_MINw else -1w);
                    failed := F|>
                in (arith_upd (IDiv 0 1 0 1) s).failed``;
val () = check ``let s = (ARB : 32 asm_state) with
                  <|regs := (\reg. if reg = 0 then INT_MINw else -1w);
                    failed := F|>
                in (arith_upd (IDiv 0 1 0 1) s).failed``;
val () = check ``let s = (ARB : 64 asm_state) with
                  <|regs := (\reg. 0w); failed := F|>
                in (arith_upd (IDiv 0 1 0 1) s).failed``;

val () = List.app (fn (a, b, product, overflow) =>
  let
    val left = intSyntax.term_of_int (Arbint.fromInt a)
    val right = intSyntax.term_of_int (Arbint.fromInt b)
    val expected = intSyntax.term_of_int (Arbint.fromInt product)
    val flag = numSyntax.term_of_int overflow
  in
    check ``let s = (ARB : 32 asm_state) with
              <|regs := (\reg. if reg = 0 then i2w ^left
                              else if reg = 1 then i2w ^right else 0w);
                failed := F|>;
                result = arith_upd (IMul 0 0 1 1) s
            in ~result.failed /\ result.regs 0 = i2w ^expected /\
               result.regs 1 = n2w ^flag``
  end)
  [(~7, 3, ~21, 0), (~7, ~3, 21, 0), (0, ~1, 0, 0),
   (2147483647, 1, 2147483647, 0), (~2147483648, 1, ~2147483648, 0),
   (2147483647, 2, ~2, 1), (~2147483648, ~1, ~2147483648, 1)];
