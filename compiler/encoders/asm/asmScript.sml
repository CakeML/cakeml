(* -------------------------------------------------------------------------

   This script defines the syntax of a small general-purpose machine
   instruction description (without labels).

   The intention is that each instruction can be translated
   (i.e. encoded) into one instruction in real machine languages such
   as 32-bit ARM, 64-bit x86, MIPS etc.

 * A clean, simple and reusable instruction description language

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
   of the semantics is relational but it only allows deterministic behaviour.

   ------------------------------------------------------------------------- *)
open HolKernel Parse boolLib bossLib
open wordsTheory alignmentTheory astTheory

val () = new_theory "asm"

(* -- syntax of ASM instruction -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)
val () = Parse.temp_type_abbrev ("fp_reg", ``:num``)
val () = Parse.temp_type_abbrev ("imm", ``:'a word``)

val () = Datatype `
  reg_imm = Reg reg | Imm ('a imm)`

val () = Datatype `
  binop = Add | Sub | And | Or | Xor`

val () = Datatype `
  cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest`

val () = Datatype `
  arith = Binop binop reg reg ('a reg_imm)
        | Shift shift reg reg num
        | Div reg reg reg
        | LongMul reg reg reg reg
        | LongDiv reg reg reg reg reg
        | AddCarry reg reg reg reg
        | AddOverflow reg reg reg reg
        | SubOverflow reg reg reg reg`

val () = Datatype `
  fp = (* orderings *)
       FPLess reg fp_reg fp_reg
     | FPLessEqual reg fp_reg fp_reg
     | FPEqual reg fp_reg fp_reg
       (* unary ops *)
     | FPAbs fp_reg fp_reg (* IEEE754:2008 *)
     | FPNeg fp_reg fp_reg (* IEEE754:2008 *)
     | FPSqrt fp_reg fp_reg
       (* binary ops *)
     | FPAdd fp_reg fp_reg fp_reg
     | FPSub fp_reg fp_reg fp_reg
     | FPMul fp_reg fp_reg fp_reg
     | FPDiv fp_reg fp_reg fp_reg
       (* Ternary ops *)
     | FPFma fp_reg fp_reg fp_reg
       (* moves and converts *)
     | FPMov fp_reg fp_reg
     | FPMovToReg reg reg fp_reg
     | FPMovFromReg fp_reg reg reg
     | FPToInt fp_reg fp_reg
     | FPFromInt fp_reg fp_reg`

val () = Datatype `
  addr = Addr reg ('a word)`

(* old version
val () = Datatype `
  mem_op = Load  | Load8  | Load32
         | Store | Store8 | Store32`
*)

val () = Datatype `
  memop = Load  | Load8 | Store | Store8`

val () = Datatype `
  inst = Skip
       | Const reg ('a word)
       | Arith ('a arith)
       | Mem memop reg ('a addr)
       | FP fp`

val () = Datatype `
  asm = Inst ('a inst)
      | Jump ('a word)
      | JumpCmp cmp reg ('a reg_imm) ('a word)
      | Call ('a word)
      | JumpReg reg
      | Loc reg ('a word)`

(* -- ASM target-specific configuration -- *)

val () = Datatype `
  architecture = ARMv7 | ARMv8 | MIPS | RISC_V | Ag32 | x86_64`

val () = Datatype `
  asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; fp_reg_count   : num  (* set to 0 if float not available *)
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>`

val reg_ok_def = Define `
  reg_ok r c <=> r < c.reg_count /\ ~MEM r c.avoid_regs`

val fp_reg_ok_def = Define `
  fp_reg_ok d c <=> d < c.fp_reg_count`

val reg_imm_ok_def = Define `
  (reg_imm_ok b (Reg r) c = reg_ok r c) /\
  (reg_imm_ok b (Imm w) c =
     (* Always permit Xor by -1 in order to provide 1's complement *)
     ((b = INL Xor) /\ (w = -1w) \/ c.valid_imm b w))`


(* Requires register inequality for some architectures *)
val arith_ok_def = Define `
  (arith_ok (Binop b r1 r2 ri) c <=>
     (* note: register to register moves can be implmented with
              "Or" on "two_reg_arith" architectures. *)
     (c.two_reg_arith ==> (r1 = r2) \/ (b = Or) /\ (ri = Reg r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_imm_ok (INL b) ri c) /\
  (arith_ok (Shift l r1 r2 n) (c: 'a asm_config) <=>
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\
     ((n = 0) ==> (l = Lsl)) /\ n < dimindex(:'a)) /\
  (arith_ok (Div r1 r2 r3) c <=>
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\
     c.ISA IN {ARMv8; MIPS; RISC_V}) /\
  (arith_ok (LongMul r1 r2 r3 r4) c <=>
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     ((c.ISA = x86_64) ==> (r1 = 2) /\ (r2 = 0) /\ (r3 = 0)) /\
     ((c.ISA = ARMv7) ==> r1 <> r2) /\
     (c.ISA IN {ARMv8; RISC_V; Ag32} ==> r1 <> r3 /\ r1 <> r4)) /\
  (arith_ok (LongDiv r1 r2 r3 r4 r5) c <=>
     (c.ISA = x86_64) /\ (r1 = 0) /\ (r2 = 2) /\ (r3 = 2) /\ (r4 = 0) /\
     reg_ok r5 c) /\
  (arith_ok (AddCarry r1 r2 r3 r4) c <=>
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 <> r3 /\ r1 <> r4)) /\
  (arith_ok (AddOverflow r1 r2 r3 r4) c <=>
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 <> r3)) /\
  (arith_ok (SubOverflow r1 r2 r3 r4) c <=>
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 <> r3))`

val fp_ok_def = Define `
  (fp_ok (FPLess r d1 d2) c <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPLessEqual r d1 d2) c <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPEqual r d1 d2) c <=>
      reg_ok r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPAbs d1 d2) c <=>
      (c.two_reg_arith ==> (d1 <> d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPNeg d1 d2) c <=>
      (c.two_reg_arith ==> (d1 <> d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPSqrt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPAdd d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_ok (FPSub d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_ok (FPMul d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_ok (FPDiv d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_ok (FPFma d1 d2 d3) c <=>
      (c.ISA = ARMv7) /\
      2 < c.fp_reg_count /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_ok (FPMov d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_ok (FPMovToReg r1 r2 d) (c : 'a asm_config) <=>
      reg_ok r1 c /\ ((dimindex(:'a) = 32) ==> r1 <> r2 /\ reg_ok r2 c) /\
      fp_reg_ok d c) /\
  (fp_ok (FPMovFromReg d r1 r2) (c : 'a asm_config) <=>
      reg_ok r1 c /\ ((dimindex(:'a) = 32) ==> r1 <> r2 /\ reg_ok r2 c) /\
      fp_reg_ok d c) /\
  (fp_ok (FPToInt r d) c <=> fp_reg_ok r c /\ fp_reg_ok d c) /\
  (fp_ok (FPFromInt d r) c <=> fp_reg_ok r c /\ fp_reg_ok d c)`

val cmp_ok_def = Define `
  cmp_ok (cmp: cmp) r ri c <=> reg_ok r c /\ reg_imm_ok (INR cmp) ri c`

val offset_ok_def = Define`
  offset_ok a offset w =
  let (min, max) = offset in min <= w /\ w <= max /\ aligned a w`

val () = List.app overload_on
  [("addr_offset_ok",  ``\c. offset_ok 0 c.addr_offset``),
   ("byte_offset_ok",  ``\c. offset_ok 0 c.byte_offset``),
   ("jump_offset_ok",  ``\c. offset_ok c.code_alignment c.jump_offset``),
   ("cjump_offset_ok", ``\c. offset_ok c.code_alignment c.cjump_offset``),
   ("loc_offset_ok",   ``\c. offset_ok c.code_alignment c.loc_offset``)]

val inst_ok_def = Define `
  (inst_ok Skip c = T) /\
  (inst_ok (Const r w) c = reg_ok r c) /\
  (inst_ok (Arith x) c = arith_ok x c) /\
  (inst_ok (FP x) c = fp_ok x c) /\
  (inst_ok (Mem m r1 (Addr r2 w) : 'a inst) c <=>
     reg_ok r1 c /\ reg_ok r2 c /\
     (if m IN {Load; Store} then
        addr_offset_ok c w
      else
        byte_offset_ok c w))`

val asm_ok_def = Define `
  (asm_ok (Inst i) c <=> inst_ok i c) /\
  (asm_ok (Jump w) c <=> jump_offset_ok c w) /\
  (asm_ok (JumpCmp cmp r ri w) c <=>
     cjump_offset_ok c w /\ cmp_ok cmp r ri c) /\
  (asm_ok (Call w) c <=>
     (case c.link_reg of SOME r => reg_ok r c | NONE => F) /\
     jump_offset_ok c w) /\
  (asm_ok (JumpReg r) c <=> reg_ok r c) /\
  (asm_ok (Loc r w) c <=> reg_ok r c /\ loc_offset_ok c w)`

val word_cmp_def = Define `
  (word_cmp Equal w1 w2 = (w1 = w2)) /\
  (word_cmp Less w1 w2  = (w1 < w2)) /\
  (word_cmp Lower w1 w2 = (w1 <+ w2)) /\
  (word_cmp Test w1 w2  = ((w1 && w2) = 0w)) /\
  (word_cmp NotEqual w1 w2 = (w1 <> w2)) /\
  (word_cmp NotLess w1 w2  = ~(w1 < w2)) /\
  (word_cmp NotLower w1 w2 = ~(w1 <+ w2)) /\
  (word_cmp NotTest w1 w2  = ((w1 && w2) <> 0w))`

val () = export_theory ()
