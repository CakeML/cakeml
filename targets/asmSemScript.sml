open HolKernel Parse boolLib bossLib
open asmTheory

val () = new_theory "asmSem"

(* -- semantics of ASM program -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)

val () = Datatype `
  asm_state =
    <| regs       : num -> 'a word
     ; mem        : 'a word -> word8
     ; mem_domain : 'a word set
     ; pc         : 'a word
     ; lr         : reg
     ; align      : num
     ; be         : bool
     ; failed     : bool
     |>`

val upd_pc_def   = Define `upd_pc pc s = s with pc := pc`
val upd_reg_def  = Define `upd_reg r v s = s with regs := (r =+ v) s.regs`
val upd_mem_def  = Define `upd_mem a b s = s with mem := (a =+ b) s.mem`
val read_reg_def = Define `read_reg r s = s.regs r`
val read_mem_def = Define `read_mem a s = s.mem a`

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

val word_cmp_def = Define `
  (word_cmp Equal w1 w2 = (w1 = w2)) /\
  (word_cmp Less w1 w2  = (w1 < w2)) /\
  (word_cmp Lower w1 w2 = (w1 <+ w2)) /\
  (word_cmp Test w1 w2  = (w1 && w2 = 0w))`

val word_shift_def = Define `
  (word_shift Lsl w n = w << n) /\
  (word_shift Lsr w n = w >>> n) /\
  (word_shift Asr w n = w >> n)`

val arith_upd_def = Define `
  (arith_upd (Binop b r1 r2 (ri:'a reg_imm)) s =
     binop_upd r1 b (read_reg r2 s) (reg_imm ri s) s) /\
  (arith_upd (Shift l r1 r2 n) s =
     upd_reg r1 (word_shift l (read_reg r2 s) n) s)`

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
  (inst (Mem m r a) s = mem_op m r a s)`

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

val bytes_in_memory_def = Define `
  (bytes_in_memory a [] m dm = T) /\
  (bytes_in_memory a ((x:word8)::xs) m dm =
     (m a = x) /\ a IN dm /\ bytes_in_memory (a + 1w) xs m dm)`

val asm_step_def = Define `
  asm_step enc c s1 s2 =
    ?i. bytes_in_memory s1.pc (enc i) s1.mem s1.mem_domain /\
        (case c.link_reg of SOME r => s1.lr = r | NONE => T) /\
        (s1.be = c.big_endian) /\
        (s1.align = c.code_alignment) /\
        (asm i (s1.pc + n2w (LENGTH (enc i))) s1 = s2) /\
        ~s2.failed /\ asm_ok i c`

val asm_step_alt_def = Define `
  asm_step_alt enc c s1 i s2 =
    bytes_in_memory s1.pc (enc i) s1.mem s1.mem_domain /\
    (case c.link_reg of SOME r => s1.lr = r | NONE => T) /\
    (s1.be = c.big_endian) /\
    (s1.align = c.code_alignment) /\
    (asm i (s1.pc + n2w (LENGTH (enc i))) s1 = s2) /\
    ~s2.failed /\ asm_ok i c`

val () = export_theory ()
