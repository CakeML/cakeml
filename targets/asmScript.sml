open HolKernel Parse boolLib bossLib
open wordsTheory;

val () = new_theory "asm"

(* -------------------------------------------------------------------------

   This script defines the syntax and semantics of a small general-
   purpose assembly language (without labels).

   The intention is that each instruction in this assembly language
   can be translated (i.e. encoded) into one instruction in real
   machine languages such as 32-bit ARM, 64-bit x86, MIPS etc.

 * A clean, simple and reusable assembly language

   The language is full of compromises as it attempts to be both a
   clean target language for compiler backends and, at the same time,
   translate as naturally as possible into several different real
   machine languages.

   The language attempts to be clean and simple by having:
    - register names be natural numbers,
    - the machine word size be a variable throughout,
    - the memory be flat word -> byte mapping,
    - compare-and-jump instead of status flags, and
    - immediate constants fit a full machine word.

 * Target specific configuration

   In order to be able to map the abstract assembly instructions into
   real assembly, we also provide a target-specific configuration
   which can prune (from the syntax of assembly language) instructions
   which cannot be supported by the specific target machine
   language. The target-specific configuration can e.g.
    - disallow certain instructions,
    - limit the number of registers,
    - exclude special registers,
    - limit the size of immediate constants, offsets etc.
    - force arithmetic to only use two registers (e.g. xor r8,r9,r10
        cannot be translated to a single instruction in x86-64)

   This configuration is used by the compiler implementations to
   guide code generation into the appropriate target-specific subset
   of the assembly language.

 * Encode function, decode function or both?

   We had to decide how to define the semantics of an instruction
   execution. Normally, machine languages semantics are defined using
   decode functions. In our setting, the assembler/compiler needs an
   encode function. If the assembly language semantics was defined
   using a decode function, then we'd need a theorem roughly:

     !i. asm_ok i config ==> (decode (encode i) = i)

   But that's not generally true: the encode function might encode
   instructions to the same machine instruction, e.g. some
   architectures map "mov r0,r1" and "or r0,r1,r1" to the same
   instruction.  In order to keep things as simple as possible, we
   defined the semantics just in terms of an encode function.

 * Determinism

   The assembly language must be deterministic. The current definition
   of the semantics is relational and, as a result, can allow for a
   non-deterministic behaviour. It is up to the target provider to
   prove that the supplied encode function provides deterministic
   behaviour in the assembly language, i.e. instruction encodings only
   overlap if the assembly semantics also matches precisely.

   ------------------------------------------------------------------------- *)

(* -- syntax of ASM instruction -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)
val () = Parse.temp_type_abbrev ("imm", ``:'a word``)

val () = Datatype `
  reg_imm = Reg reg | Imm ('a imm)`

val () = Datatype `
  binop = Add | Sub | And | Or | Xor`

val () = Datatype `
  cmp = Equal | Lower | Less | Test`

val () = Datatype `
  shift = Lsl | Lsr | Asr`

val () = Datatype `
  arith = Binop binop reg reg ('a reg_imm)
        | Shift shift reg reg num`

val () = Datatype `
  addr = Addr reg ('a word)`

val () = Datatype `
  mem_op = Load  | Load8  | Load32
         | Store | Store8 | Store32`

val () = Datatype `
  inst = Const reg ('a word)
       | Arith ('a arith)
       | Mem mem_op reg ('a addr)`

val () = Datatype `
  asm = Skip
      | Inst ('a inst)
      | Jump ('a word) ('a inst option) (* delay slot *)
      | JumpCmp cmp reg ('a reg_imm) ('a word) ('a inst option)
      | Call ('a word) reg
      | JumpReg reg
      | Loc reg ('a word)`

(* -- ASM target-specific configuration -- *)

val () = Datatype `
  asm_config =
    <| ISA_name        : string
     ; reg_count       : num
     ; avoid_regs      : num set
     ; link_reg        : num
     ; allow_call      : bool
     ; has_delay_slot  : bool
     ; two_reg_arith   : bool
     ; imm_min         : 'a word
     ; imm_max         : 'a word
     ; addr_offset_min : 'a word
     ; addr_offset_max : 'a word
     ; jump_offset_min : 'a word
     ; jump_offset_max : 'a word
     ; code_alignment  : num
     |>`

val reg_ok_def = Define `
  reg_ok r c = r < c.reg_count /\ r NOTIN c.avoid_regs`

val imm_ok_def = Define `
  imm_ok w c = c.imm_min <= w /\ w <= c.imm_max`

val reg_imm_ok_def = Define `
  (reg_imm_ok (Reg r) c = reg_ok r c) /\
  (reg_imm_ok (Imm w) c = imm_ok w c)`

val arith_ok_def = Define `
  (arith_ok (Binop b r1 r2 ri) c =
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_imm_ok ri c) /\
  (arith_ok (Shift l r1 r2 n) c =
     reg_ok r1 c /\ reg_ok r2 c)`

val cmp_ok_def = Define `
  cmp_ok (cmp: cmp) r ri c = reg_ok r c /\ reg_imm_ok ri c`

val addr_offset_ok_def = Define `
  addr_offset_ok w c = c.addr_offset_min <= w /\ w <= c.addr_offset_max`

val jump_offset_ok_def = Define `
  jump_offset_ok w c = c.jump_offset_min <= w /\ w <= c.jump_offset_max /\
                       (w2n w MOD c.code_alignment = 0)`

val addr_ok_def = Define `
  addr_ok (Addr r w) c = reg_ok r c /\ addr_offset_ok w c`

val inst_ok_def = Define `
  (inst_ok (Const r w) c = reg_ok r c) /\
  (inst_ok (Arith x) c = arith_ok x c) /\
  (inst_ok (Mem m r a) c = reg_ok r c /\ addr_ok a c)`

val asm_ok_def = Define `
  (asm_ok (Skip) c = T) /\
  (asm_ok (Inst i) c = inst_ok i c) /\
  (asm_ok (Jump w i) c =
     jump_offset_ok w c /\
     case i of NONE => ~c.has_delay_slot
             | SOME x => inst_ok x c /\ c.has_delay_slot) /\
  (asm_ok (JumpCmp cmp r ri w i) c =
     jump_offset_ok w c /\ cmp_ok cmp r ri c /\
     case i of NONE => ~c.has_delay_slot
             | SOME x => inst_ok x c /\ c.has_delay_slot) /\
  (asm_ok (Call w r) c =
     reg_ok r c /\ c.allow_call /\
     (c.link_reg = r) /\ jump_offset_ok w c) /\
  (asm_ok (JumpReg r) c = reg_ok r c) /\
  (asm_ok (Loc r w) c = reg_ok r c /\ jump_offset_ok w c)`

(* -- semantics of ASM program -- *)

val () = Datatype `
  asm_state =
    <| regs       : num -> 'a word
     ; mem        : 'a word -> word8
     ; mem_domain : 'a word set
     ; pc         : 'a word
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
     assert (n < dimindex (:'a))
       (upd_reg r1 (word_shift l (read_reg r2 s) n) s))`

val addr_def = Define `
  addr (Addr r offset) s = read_reg r s + offset`

val read_mem_word_def = Define `
  (read_mem_word a 0 s = (0w:'a word,s)) /\
  (read_mem_word a (SUC n) s =
     let (w,s1) = read_mem_word (a + 1w) n s in
       (word_or (w << 8) (w2w (read_mem a s1)),
          assert (a IN s1.mem_domain) s1))`

val mem_load_def = Define `
  mem_load n r a s =
    let a = addr a s in
    let (w,s) = read_mem_word a n s in
    let s = upd_reg r w s in
      assert (a && n2w (n - 1) = 0w) s`

val write_mem_word_def = Define `
  (write_mem_word a 0 w s = s) /\
  (write_mem_word a (SUC n) w s =
     let s1 = write_mem_word (a + 1w) n (w >>> 8) s in
       assert (a IN s1.mem_domain) (upd_mem a (w2w w) s1))`

val mem_store_def = Define `
  mem_store n r a s =
    let a = addr a s in
    let w = read_reg r s in
    let s = write_mem_word a n w s in
      assert (a && n2w (n - 1) = 0w) s`

val mem_op_upd_def = Define `
  (mem_op Load r a = mem_load (dimindex (:'a) DIV 8) r a) /\
  (mem_op Store r a = mem_store (dimindex (:'a) DIV 8) r a) /\
  (mem_op Load8 r a = mem_load 1 r a) /\
  (mem_op Store8 r a = mem_store 1 r a) /\
  (mem_op Load32 r (a:'a addr) = mem_load 4 r a) /\
  (mem_op Store32 r (a:'a addr) = mem_store 4 r a)`

val inst_def = Define `
  (inst (Const r imm) s = upd_reg r imm s) /\
  (inst (Arith x) s = arith_upd x s) /\
  (inst (Mem m r a) s = mem_op m r a s)`

val inst_opt_def = Define `
  (inst_opt NONE s = s) /\
  (inst_opt (SOME i) s = inst i s)`

val jump_to_offset_def = Define `
  jump_to_offset w s = upd_pc (s.pc + w) s`

val asm_def = Define `
  (asm Skip pc s = upd_pc pc s) /\
  (asm (Inst i) pc s = upd_pc pc (inst i s)) /\
  (asm (Jump l i) pc s = inst_opt i (jump_to_offset l s)) /\
  (asm (JumpCmp cmp r ri l i) pc s =
     if word_cmp cmp (read_reg r s) (reg_imm ri s)
     then inst_opt i (jump_to_offset l s)
     else inst_opt i (upd_pc pc s)) /\
  (asm (Call l r) pc s = jump_to_offset l (upd_reg r pc s)) /\
  (asm (JumpReg r) pc s = upd_pc (read_reg r s) s) /\
  (asm (Loc r l) pc s = upd_pc pc (upd_reg r (s.pc + l) s))`

val bytes_in_memory_def = Define `
  (bytes_in_memory a [] m dm = T) /\
  (bytes_in_memory a ((x:word8)::xs) m dm =
     (m a = x) /\ a IN dm /\ bytes_in_memory (a + 1w) xs m dm)`

val asm_step_def = Define `
  asm_step enc c s1 s2 =
    ?i. ~s2.failed /\ asm_ok i c /\
        bytes_in_memory s1.pc (enc i) s1.mem s1.mem_domain /\
        (asm i (s1.pc + n2w (LENGTH (enc i))) s1 = s2)`

(* -- semantics is deterministic if encoding is deterministic enough -- *)

val enc_deterministic_def = Define `
  enc_deterministic enc c =
    !i j s1.
      asm_ok i c /\ asm_ok j c /\ isPREFIX (enc i) (enc j) ==>
        (asm i (s1.pc + n2w (LENGTH (enc i))) s1 =
         asm j (s1.pc + n2w (LENGTH (enc j))) s1)`

val bytes_in_memory_IMP = prove(
  ``!xs ys a m dm.
      bytes_in_memory a xs m dm /\ bytes_in_memory a ys m dm ==>
      isPREFIX xs ys \/ isPREFIX ys xs``,
  Induct
  THEN Cases_on `ys`
  THEN SRW_TAC [] []
  THEN METIS_TAC [bytes_in_memory_def])

val asm_deterministic = store_thm("asm_deterministic",
  ``enc_deterministic enc config ==>
    !s1 s2 s3.
      asm_step enc config s1 s2 /\ asm_step enc config s1 s3 ==> (s2 = s3)``,
  SRW_TAC [] [asm_step_def]
  THEN METIS_TAC [enc_deterministic_def, bytes_in_memory_IMP])

(* -- well-formedness of encoding -- *)

val enc_ok_def = Define `
  enc_ok (enc: 'a asm -> word8 list) c =
    (* code alignment *)
    1 <= c.code_alignment /\
    ((c.code_alignment = 1) ==> ODD (LENGTH (enc Skip))) /\
    (!w. LENGTH (enc w) MOD c.code_alignment = 0) /\
    (* label instantiation does not affect length of code *)
    (!w i. LENGTH (enc (Jump w i)) = LENGTH (enc (Jump 0w i))) /\
    (!c r ri w i. LENGTH (enc (JumpCmp c r ri w i)) =
                  LENGTH (enc (JumpCmp c r ri 0w i))) /\
    (!w r. LENGTH (enc (Call w r)) = LENGTH (enc (Call 0w r))) /\
    (!w r. LENGTH (enc (Loc r w)) = LENGTH (enc (Loc r 0w))) /\
    (* no overlap between instructions with different behaviour *)
    enc_deterministic enc c`

(* -- correctness property to be proved for each backend -- *)

val backend_correct_def = Define `
  backend_correct enc (config:'a asm_config) (next:'b -> 'b) R =
    enc_ok enc config /\
    !s1 s2.
      asm_step enc config s1 s2 ==>
      !state. R s1 state ==> ?n. R s2 (FUNPOW next (n + 1) state)`

val () = export_theory ()
