open HolKernel Parse boolLib bossLib
open wordsTheory alignmentTheory

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
   of the semantics is relational but it only allows deterministic behaviour.

   ------------------------------------------------------------------------- *)

(* -- syntax of ASM instruction -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)
val () = Parse.temp_type_abbrev ("imm", ``:'a word``)

val () = Datatype `
  reg_imm = Reg reg | Imm ('a imm)`

val () = Datatype `
  binop = Add | Sub | And | Or | Xor`

val () = Datatype `
  cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest`

val () = Datatype `
  shift = Lsl | Lsr | Asr`

val () = Datatype `
  arith = Binop binop reg reg ('a reg_imm)
        | Shift shift reg reg num
        | Div reg reg reg
        | LongMul reg reg reg reg
        | LongDiv reg reg reg reg reg
        | AddCarry reg reg reg reg`

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
       | Mem memop reg ('a addr)`

val () = Datatype `
  asm = Inst ('a inst)
      | Jump ('a word)
      | JumpCmp cmp reg ('a reg_imm) ('a word)
      | Call ('a word)
      | JumpReg reg
      | Loc reg ('a word)`

(* -- ASM target-specific configuration -- *)

val () = Datatype `
  architecture = ARMv6 | ARMv8 | MIPS | RISC_V | x86_64`

val () = Datatype `
  asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>`

val reg_ok_def = Define `
  reg_ok r c = r < c.reg_count /\ ~MEM r c.avoid_regs`

val reg_imm_ok_def = Define `
  (reg_imm_ok b (Reg r) c = reg_ok r c) /\
  (reg_imm_ok b (Imm w) c = c.valid_imm b w)`

(* Requires register inequality for some architectures *)
val arith_ok_def = Define `
  (arith_ok (Binop b r1 r2 ri) c =
     (* note: register to register moves can be implmented with
              "Or" on "two_reg_arith" architectures. *)
     (c.two_reg_arith ==> (r1 = r2) \/ (b = Or) /\ (ri = Reg r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_imm_ok (INL b) ri c) /\
  (arith_ok (Shift l r1 r2 n) (c: 'a asm_config) =
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\
     ((n = 0) ==> (l = Lsl)) /\ n < dimindex(:'a)) /\
  (arith_ok (Div r1 r2 r3) c =
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\
     c.ISA IN {ARMv8; MIPS; RISC_V}) /\
  (arith_ok (LongMul r1 r2 r3 r4) c =
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     ((c.ISA = x86_64) ==> (r1 = 2) /\ (r2 = 0) /\ (r3 = 0)) /\
     ((c.ISA = ARMv6) ==> r1 <> r2) /\
     (((c.ISA = ARMv8) \/ (c.ISA = RISC_V)) ==> r1 <> r3 /\ r1 <> r4)) /\
  (arith_ok (LongDiv r1 r2 r3 r4 r5) c =
     (c.ISA = x86_64) /\ (r1 = 0) /\ (r2 = 2) /\ (r3 = 0) /\ (r4 = 2) /\
     reg_ok r5 c) /\
  (arith_ok (AddCarry r1 r2 r3 r4) c =
     (c.two_reg_arith ==> (r1 = r2)) /\
     reg_ok r1 c /\ reg_ok r2 c /\ reg_ok r3 c /\ reg_ok r4 c /\
     (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 <> r3 /\ r1 <> r4))`

val cmp_ok_def = Define `
  cmp_ok (cmp: cmp) r ri c = reg_ok r c /\ reg_imm_ok (INR cmp) ri c`

val offset_ok_def = Define`
  offset_ok a offset w =
  let (min, max) = offset in min <= w /\ w <= max /\ aligned a w`

val () =
   List.app overload_on
    [("addr_offset_ok",  ``\w c. offset_ok 0 c.addr_offset w``),
     ("jump_offset_ok",  ``\w c. offset_ok c.code_alignment c.jump_offset w``),
     ("cjump_offset_ok", ``\w c. offset_ok c.code_alignment c.cjump_offset w``),
     ("loc_offset_ok",   ``\w c. offset_ok c.code_alignment c.loc_offset w``)]

val addr_ok_def = Define `
  addr_ok (Addr r w) c = reg_ok r c /\ addr_offset_ok w c`

val inst_ok_def = Define `
  (inst_ok Skip c = T) /\
  (inst_ok (Const r w) c = reg_ok r c) /\
  (inst_ok (Arith x) c = arith_ok x c) /\
  (inst_ok (Mem m r a : 'a inst) c =
     (* (((m = Load32) \/ (m = Store32)) ==> (dimindex(:'a) = 64)) /\ *)
     reg_ok r c /\ addr_ok a c)`

val asm_ok_def = Define `
  (asm_ok (Inst i) c = inst_ok i c) /\
  (asm_ok (Jump w) c = jump_offset_ok w c) /\
  (asm_ok (JumpCmp cmp r ri w) c = cjump_offset_ok w c /\ cmp_ok cmp r ri c) /\
  (asm_ok (Call w) c =
     (case c.link_reg of SOME r => reg_ok r c | NONE => F) /\
     jump_offset_ok w c) /\
  (asm_ok (JumpReg r) c = reg_ok r c) /\
  (asm_ok (Loc r w) c = reg_ok r c /\ loc_offset_ok w c)`

val () = export_theory ()
