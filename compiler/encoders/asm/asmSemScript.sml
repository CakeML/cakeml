(*
  The semantics of the asm instruction description.
*)
open HolKernel Parse boolLib bossLib
open asmTheory machine_ieeeTheory
open miscTheory (* for bytes_in_memory *)

val () = new_theory "asmSem"

(* -- semantics of ASM program -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)
val () = Parse.temp_type_abbrev ("fp_reg", ``:num``)

val () = Datatype `
  asm_state =
    <| regs       : num -> 'a word
     ; fp_regs    : num -> word64
     ; mem        : 'a word -> word8
     ; mem_domain : 'a word set
     ; pc         : 'a word
     ; lr         : reg
     ; align      : num
     ; be         : bool
     ; failed     : bool
     |>`

val upd_pc_def      = Define `upd_pc pc s = s with pc := pc`
val upd_reg_def     = Define `upd_reg r v s = s with regs := (r =+ v) s.regs`
val upd_fp_reg_def  = Define `upd_fp_reg r v s = s with fp_regs := (r =+ v) s.fp_regs`
val upd_mem_def     = Define `upd_mem a b s = s with mem := (a =+ b) s.mem`
val read_reg_def    = Define `read_reg r s = s.regs r`
val read_fp_reg_def = Define `read_fp_reg r s = s.fp_regs r`
val read_mem_def    = Define `read_mem a s = s.mem a`

val assert_def = Define `assert b s = s with failed := (~b \/ s.failed)`

val reg_imm_def = Define `
  (reg_imm (Reg r) s = read_reg r s) /\
  (reg_imm (Imm w) s = w)`

val binop_upd_def = Define `
  (binop_upd r Add w1 w2 = upd_reg r (w1 + w2)) /\
  (binop_upd r Sub w1 w2 = upd_reg r (w1 - w2)) /\
  (binop_upd r And w1 w2 = upd_reg r (word_and w1 w2)) /\
  (binop_upd r Or w1 w2  = upd_reg r (word_or w1 w2)) /\
  (binop_upd r Xor w1 w2 = upd_reg r (word_xor w1 w2))`

val is_test_def = Define `is_test c <=> (c = Test) \/ (c = NotTest)`

val word_shift_def = Define `
  (word_shift Lsl w n = w << n) /\
  (word_shift Lsr w n = w >>> n) /\
  (word_shift Asr w n = w >> n) /\
  (word_shift Ror w n = word_ror w n)`;

val arith_upd_def = Define `
  (arith_upd (Binop b r1 r2 (ri:'a reg_imm)) s =
     binop_upd r1 b (read_reg r2 s) (reg_imm ri s) s) /\
  (arith_upd (Shift l r1 r2 n) s =
     upd_reg r1 (word_shift l (read_reg r2 s) n) s) /\
  (arith_upd (Div r1 r2 r3) s =
     let q = read_reg r3 s in
       assert (q <> 0w) (upd_reg r1 (read_reg r2 s / q) s)) /\
  (arith_upd (LongMul r1 r2 r3 r4) (s : 'a asm_state) =
     let r = w2n (read_reg r3 s) * w2n (read_reg r4 s)
     in
       upd_reg r2 (n2w r) (upd_reg r1 (n2w (r DIV dimword (:'a))) s)) /\
  (arith_upd (LongDiv r1 r2 r3 r4 r5) (s : 'a asm_state) =
     let n = w2n (read_reg r3 s) * dimword (:'a) + w2n (read_reg r4 s) in
     let d = w2n (read_reg r5 s) in
     let q = n DIV d
     in
       assert (d <> 0 /\ q < dimword (:'a))
         (upd_reg r1 (n2w q) (upd_reg r2 (n2w (n MOD d)) s))) /\
  (arith_upd (AddCarry r1 r2 r3 r4) (s : 'a asm_state) =
     let r = w2n (read_reg r2 s) + w2n (read_reg r3 s) +
             (if read_reg r4 s = 0w then 0 else 1)
     in
       upd_reg r4 (if dimword (:'a) <= r then 1w else 0w)
         (upd_reg r1 (n2w r) s)) /\
  (arith_upd (AddOverflow r1 r2 r3 r4) (s : 'a asm_state) =
     let w2 = read_reg r2 s in
     let w3 = read_reg r3 s
     in
       upd_reg r4 (if w2i (w2 + w3) <> w2i w2 + w2i w3 then 1w else 0w)
         (upd_reg r1 (w2 + w3) s)) /\
  (arith_upd (SubOverflow r1 r2 r3 r4) (s : 'a asm_state) =
     let w2 = read_reg r2 s in
     let w3 = read_reg r3 s
     in
       upd_reg r4 (if w2i (w2 - w3) <> w2i w2 - w2i w3 then 1w else 0w)
         (upd_reg r1 (w2 - w3) s))`

val fp_upd_def = Define `
  (fp_upd (FPLess r d1 d2) s =
     upd_reg r (if fp64_lessThan (read_fp_reg d1 s) (read_fp_reg d2 s)
                  then 1w
                else 0w) s) /\
  (fp_upd (FPLessEqual r d1 d2) s =
     upd_reg r (if fp64_lessEqual (read_fp_reg d1 s) (read_fp_reg d2 s)
                  then 1w
                else 0w) s) /\
  (fp_upd (FPEqual r d1 d2) s =
     upd_reg r (if fp64_equal (read_fp_reg d1 s) (read_fp_reg d2 s)
                  then 1w
                else 0w) s) /\
  (fp_upd (FPMov d1 d2) s = upd_fp_reg d1 (read_fp_reg d2 s) s) /\
  (fp_upd (FPAbs d1 d2) s = upd_fp_reg d1 (fp64_abs (read_fp_reg d2 s)) s) /\
  (fp_upd (FPNeg d1 d2) s = upd_fp_reg d1 (fp64_negate (read_fp_reg d2 s)) s) /\
  (fp_upd (FPSqrt d1 d2) s =
     upd_fp_reg d1 (fp64_sqrt roundTiesToEven (read_fp_reg d2 s)) s) /\
  (fp_upd (FPAdd d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPSub d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_sub roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPMul d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_mul roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPDiv d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_div roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPFma d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_mul_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s) (read_fp_reg d1 s)) s) /\
  (fp_upd (FPMovToReg r1 r2 d) (s : 'a asm_state) =
     if dimindex(:'a) = 64 then
       upd_reg r1 (w2w (read_fp_reg d s)) s
     else let v = read_fp_reg d s in
       upd_reg r2 ((63 >< 32) v) (upd_reg r1 ((31 >< 0) v) s)) /\
  (fp_upd (FPMovFromReg d r1 r2) (s : 'a asm_state) =
     upd_fp_reg d
       (if dimindex(:'a) = 64 then
          w2w (read_reg r1 s)
        else
          read_reg r2 s @@ read_reg r1 s) s) /\
  (fp_upd (FPToInt d1 d2) (s : 'a asm_state) =
     case fp64_to_int roundTiesToEven (read_fp_reg d2 s) of
         SOME i =>
           let w = i2w i : word32 in
             (if dimindex(:'a) = 64 then
                upd_fp_reg d1 (w2w w)
              else let (h, l) = if ODD d1 then (63, 32) else (31, 0) in
                     upd_fp_reg (d1 DIV 2)
                       (bit_field_insert h l w (read_fp_reg (d1 DIV 2) s)))
                (assert (w2i w = i) s)
      | _ => assert F s) /\
  (fp_upd (FPFromInt d1 d2) (s : 'a asm_state) =
     let i = if dimindex(:'a) = 64 then
               w2i ((31 >< 0) (read_fp_reg d2 s) : word32)
             else let v = read_fp_reg (d2 DIV 2) s in
               w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : 'a word)
     in
       upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s)`

val addr_def = Define `addr (Addr r offset) s = read_reg r s + offset`

val read_mem_word_def = Define `
  (read_mem_word a 0 s = (0w:'a word,s)) /\
  (read_mem_word a (SUC n) s =
     let (w,s1) = read_mem_word (if s.be then a - 1w else a + 1w) n s in
       (word_or (w << 8) (w2w (read_mem a s1)),
          assert (a IN s1.mem_domain) s1))`

val mem_load_def = Define `
  mem_load n r a s =
    let a = addr a s in
    let (w,s) = read_mem_word (if s.be then a + n2w (n - 1) else a) n s in
    let s = upd_reg r w s in
      assert (aligned (LOG2 n) a) s`

val write_mem_word_def = Define `
  (write_mem_word a 0 w s = s) /\
  (write_mem_word a (SUC n) w s =
     let s1 = write_mem_word (if s.be then a - 1w else a + 1w) n (w >>> 8) s in
       assert (a IN s1.mem_domain) (upd_mem a (w2w w) s1))`

val mem_store_def = Define `
  mem_store n r a s =
    let a = addr a s in
    let w = read_reg r s in
    let s = write_mem_word (if s.be then a + n2w (n - 1) else a) n w s in
      assert (aligned (LOG2 n) a) s`

val mem_op_def = Define `
  (mem_op Load r a = mem_load (dimindex (:'a) DIV 8) r a) /\
  (mem_op Store r a = mem_store (dimindex (:'a) DIV 8) r a) /\
  (mem_op Load8 r a = mem_load 1 r a) /\
  (mem_op Store8 r a = mem_store 1 r a) /\
  (mem_op Load32 r (a:'a addr) = mem_load 4 r a) /\
  (mem_op Store32 r (a:'a addr) = mem_store 4 r a)`

val inst_def = Define `
  (inst Skip s = s) /\
  (inst (Const r imm) s = upd_reg r imm s) /\
  (inst (Arith x) s = arith_upd x s) /\
  (inst (Mem m r a) s = mem_op m r a s) /\
  (inst (FP fp) s = fp_upd fp s)`

val jump_to_offset_def = Define `jump_to_offset w s = upd_pc (s.pc + w) s`

val asm_def = Define `
  (asm (Inst i) pc s = upd_pc pc (inst i s)) /\
  (asm (Jump l) pc s = jump_to_offset l s) /\
  (asm (JumpCmp cmp r ri l) pc s =
     if word_cmp cmp (read_reg r s) (reg_imm ri s)
     then jump_to_offset l s
     else upd_pc pc s) /\
  (asm (Call l) pc s = jump_to_offset l (upd_reg s.lr pc s)) /\
  (asm (JumpReg r) pc s =
     let a = read_reg r s in upd_pc a (assert (aligned s.align a) s)) /\
  (asm (Loc r l) pc s = upd_pc pc (upd_reg r (s.pc + l) s))`

val asm_step_def = Define `
  asm_step c s1 i s2 <=>
    bytes_in_memory s1.pc (c.encode i) s1.mem s1.mem_domain /\
    (case c.link_reg of SOME r => s1.lr = r | NONE => T) /\
    (s1.be = c.big_endian) /\
    (s1.align = c.code_alignment) /\
    (asm i (s1.pc + n2w (LENGTH (c.encode i))) s1 = s2) /\
    ~s2.failed /\ asm_ok i c`

val () = export_theory ()
