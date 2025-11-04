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
Theory asm
Ancestors
  words alignment ast

(* -- syntax of ASM instruction -- *)

Type reg = ``:num``
Type fp_reg = ``:num``
Type imm = ``:'a word``

Datatype:
  reg_imm = Reg reg | Imm ('a imm)
End

Datatype:
  binop = Add | Sub | And | Or | Xor
End

Datatype:
  cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest
End

Datatype:
  arith = Binop binop reg reg ('a reg_imm)
        | Shift shift reg reg num
        | Div reg reg reg
        | LongMul reg reg reg reg
        | LongDiv reg reg reg reg reg
        | AddCarry reg reg reg reg
        | AddOverflow reg reg reg reg
        | SubOverflow reg reg reg reg
End

Datatype:
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
     | FPFromInt fp_reg fp_reg
End

Datatype:
  addr = Addr reg ('a word)
End

Datatype:
  memop = Load  | Load8  | Load16  | Load32
        | Store | Store8 | Store16 | Store32
End

Datatype:
  inst = Skip
       | Const reg ('a word)
       | Arith ('a arith)
       | Mem memop reg ('a addr)
       | FP fp
End

Datatype:
  asm = Inst ('a inst)
      | Jump ('a word)
      | JumpCmp cmp reg ('a reg_imm) ('a word)
      | Call ('a word)
      | JumpReg reg
      | Loc reg ('a word)
End

(* -- ASM target-specific configuration -- *)

Datatype:
  architecture = ARMv7 | ARMv8 | MIPS | RISC_V | Ag32 | x86_64 | Wasm
End

Datatype:
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
     ; hw_offset      : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>
End

Definition reg_ok_def:
  reg_ok r c <=> r < c.reg_count /\ ~MEM r c.avoid_regs
End

Definition fp_reg_ok_def:
  fp_reg_ok d c <=> d < c.fp_reg_count
End

Definition reg_imm_ok_def:
  (reg_imm_ok b (Reg r) c = reg_ok r c) /\
  (reg_imm_ok b (Imm w) c =
     (* Always permit Xor by -1 in order to provide 1's complement *)
     ((b = INL Xor) /\ (w = -1w) \/ c.valid_imm b w))
End


(* Requires register inequality for some architectures *)
Definition arith_ok_def:
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
     c.ISA IN {ARMv8; MIPS; RISC_V; Wasm}) /\
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
     (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 <> r3))
End

Definition fp_ok_def:
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
  (fp_ok (FPFromInt d r) c <=> fp_reg_ok r c /\ fp_reg_ok d c)
End

Definition cmp_ok_def:
  cmp_ok (cmp: cmp) r ri c <=> reg_ok r c /\ reg_imm_ok (INR cmp) ri c
End

Definition offset_ok_def:
  offset_ok a offset w =
  let (min, max) = offset in min <= w /\ w <= max /\ aligned a w
End

Overload addr_offset_ok = “λc. offset_ok 0 c.addr_offset”
Overload hw_offset_ok = “λc. offset_ok 0 c.hw_offset”
Overload byte_offset_ok = “λc. offset_ok 0 c.byte_offset”
Overload jump_offset_ok = “λc. offset_ok c.code_alignment c.jump_offset”
Overload cjump_offset_ok = “λc. offset_ok c.code_alignment c.cjump_offset”
Overload loc_offset_ok = “λc. offset_ok c.code_alignment c.loc_offset”

Definition inst_ok_def:
  (inst_ok Skip c = T) /\
  (inst_ok (Const r w) c = reg_ok r c) /\
  (inst_ok (Arith x) c = arith_ok x c) /\
  (inst_ok (FP x) c = fp_ok x c) /\
  (inst_ok (Mem m r1 (Addr r2 w) : 'a inst) c <=>
     reg_ok r1 c /\ reg_ok r2 c /\
     (if m IN {Load; Store; Load32; Store32} then
        addr_offset_ok c w
      else if m IN {Load16; Store16} then
        hw_offset_ok c w ∧ c.ISA ≠ Ag32
      else
        byte_offset_ok c w))
End

Definition asm_ok_def:
  (asm_ok (Inst i) c <=> inst_ok i c) /\
  (asm_ok (Jump w) c <=> jump_offset_ok c w) /\
  (asm_ok (JumpCmp cmp r ri w) c <=>
     cjump_offset_ok c w /\ cmp_ok cmp r ri c) /\
  (asm_ok (Call w) c <=>
     (case c.link_reg of SOME r => reg_ok r c | NONE => F) /\
     jump_offset_ok c w) /\
  (asm_ok (JumpReg r) c <=> reg_ok r c) /\
  (asm_ok (Loc r w) c <=> reg_ok r c /\ loc_offset_ok c w)
End

Definition word_cmp_def:
  (word_cmp Equal w1 w2 = (w1 = w2)) /\
  (word_cmp Less w1 w2  = (w1 < w2)) /\
  (word_cmp Lower w1 w2 = (w1 <+ w2)) /\
  (word_cmp Test w1 w2  = ((w1 && w2) = 0w)) /\
  (word_cmp NotEqual w1 w2 = (w1 <> w2)) /\
  (word_cmp NotLess w1 w2  = ~(w1 < w2)) /\
  (word_cmp NotLower w1 w2 = ~(w1 <+ w2)) /\
  (word_cmp NotTest w1 w2  = ((w1 && w2) <> 0w))
End

Definition is_load_def[simp]:
  (is_load Load = T) ∧
  (is_load Load8 = T) ∧
  (is_load Load16 = T) ∧
  (is_load Load32 = T) ∧
  (is_load _ = F)
End
