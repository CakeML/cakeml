open preamble stackLangTheory;

val _ = new_theory "stack_names";

(* Rename the registers to fit with the target architecture *)

val find_name_def = Define `
  find_name f n =
    case lookup n f of
    | NONE => n
    | SOME k => k`

val ri_find_name_def = Define `
  (ri_find_name f (Reg r) = Reg (find_name f r)) /\
  (ri_find_name f (Imm w) = Imm w)`

val inst_find_name_def = Define `
  inst_find_name f i =
    case i of
    | Skip => Skip
    | Const r w => Const (find_name f r) w
    | Arith (Binop bop d r ri) =>
        Arith (Binop bop (find_name f d) (find_name f r) (ri_find_name f ri))
    | Arith (Shift sop d r i) =>
        Arith (Shift sop (find_name f d) (find_name f r) i)
    | Arith (AddCarry r1 r2 r3 r4) =>
        Arith (AddCarry (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (LongMul r1 r2 r3 r4) =>
        Arith (LongMul (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (LongDiv r1 r2 r3 r4 r5) =>
        Arith (LongDiv (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4) (find_name f r5))
    | Mem mop r (Addr a w) => Mem mop (find_name f r) (Addr (find_name f a) w)`

val dest_find_name_def = Define`
  dest_find_name f (INR r) = INR (find_name f r) ∧
  dest_find_name f x = x`;

val comp_def = Define `
  comp f p =
    case p of
    | Halt r => Halt (find_name f r)
    | Raise r => Raise (find_name f r)
    | Return r1 r2 => Return (find_name f r1) (find_name f r2)
    | Inst i => Inst (inst_find_name f i)
    | LocValue i l1 l2 => LocValue (find_name f i) l1 l2
    | Seq p1 p2 => Seq (comp f p1) (comp f p2)
    | If c r ri p1 p2 =>
        If c (find_name f r) (ri_find_name f ri) (comp f p1) (comp f p2)
    | While c r ri p1 =>
        While c (find_name f r) (ri_find_name f ri) (comp f p1)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp f p1,find_name f lr,l1,l2))
             (dest_find_name f dest)
             (case exc of
              | NONE => NONE
              | SOME (p2,l1,l2) => SOME (comp f p2,l1,l2))
    | FFI i r1 r2 r3 => FFI i (find_name f r1) (find_name f r2) (find_name f r3)
    | JumpLower r1 r2 dest => JumpLower (find_name f r1) (find_name f r2) dest
    | p => p`

val prog_comp_def = Define `
  prog_comp f (n,p) = (n,comp f p)`

val compile_def = Define `
  compile f prog = MAP (prog_comp f) prog`;

(* some defaults *)

val names_ok_def = Define `
  names_ok names reg_count avoid_regs =
    let xs = GENLIST (find_name names) (reg_count - LENGTH avoid_regs) in
      ALL_DISTINCT xs /\
      EVERY (\x. x < reg_count /\ ~(MEM x avoid_regs)) xs`

val x64_names_def = Define `
  x64_names =
    (* 16 regs, must avoid 4 and 5, names:
         r0=rax, r1=rbx, r2=rcx, r3=rdx, r4=rbp, r5=rsp, r6=rsi,
         r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
       The first six arguments are passed in registers. The first
       argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
       the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
       in r8 and the sixth in r9.
       Callee-saved regs: r12-r15, rbx
     *)
    (insert 1 7 o  (* arg 1 *)
     insert 2 6 o  (* arg 2 *)
  (* insert 3 3 o *)
     insert 4 2 o
     insert 5 8 o
     insert 6 9 o
     insert 11 12 o
     insert 12 13 o
     insert 13 14 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 7 1 o
     insert 8 15 o
     insert 9 11 o
     insert 14 4 o
     insert 15 5) LN:num num_map`

val x64_names_def = save_thm("x64_names_def",
  CONV_RULE (RAND_CONV EVAL) x64_names_def);

val arm_names_def = Define `
  arm_names =
    (* source can use 14 regs,
       target's r15 must be avoided (pc),
       target's r13 must be avoided (stack pointer),
       source 0 must represent r14 (link register),
       source 1-2 must be r0 and r1 (1st 2 arguments)
       the top three (source 11-13) must be callee-saved
       (callee-saved include: r4-r8, r10-11) *)
    (insert 0 14 o
     insert 1 0 o
     insert 2 1 o
     insert 12 8 o
     insert 13 10 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 8 2 o
     insert 10 12 o
     insert 14 13) LN:num num_map`

val arm_names_def = save_thm("arm_names_def",
  CONV_RULE (RAND_CONV EVAL) arm_names_def);

val arm8_names_def = Define `
  arm8_names =
    (* source can use 31 regs (0-30),
       target's r31 must be avoided (stack pointer),
       source 0 must represent r30 (link register),
       source 1-2 must be r0,r1 (1st 2 args),
       top three (28-30) must be callee-saved (in r19-r29) *)
    (insert 0 30 o
     insert 1 0 o
     insert 2 1 o
     insert 30 27 o
     insert 27 2) LN:num num_map`

val arm8_names_def = save_thm("arm8_names_def",
  CONV_RULE (RAND_CONV EVAL) arm8_names_def);

val mips_names_def = Define `
  mips_names =
    (* source can use 25 regs (r2-r24,r30-r31),
       target's r0 must be avoided (hardcoded to 0),
       target's r1 must be avoided (used by encoder in asm),
       target's r25 and r28 are used to set up PIC
       target's r29 must be avoided (stack pointer),
       target's r26-r27 avoided (reserved for OS kernel),
       source 0 must represent r31 (link register),
       source 1 2 must be r4, r5 (1st 2 args),
       top 3 (22-24) must be callee-saved (in 16-23, 28, 30) *)
    (insert 0 31 o
     insert 1 4 o
     insert 2 5 o
     insert 22 21 o
     insert 23 22 o
     insert 24 23 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 4 2 o
     insert 21 24 o
     insert 5 30 o
     insert 31 0 o
     insert 30 1) LN:num num_map`

val mips_names_def = save_thm("mips_names_def",
  CONV_RULE (RAND_CONV EVAL) mips_names_def);

val riscv_names_def = Define `
  riscv_names =
  (* arguments: 10-17
       including return values: 10-11
     temporaries: 5-7, 28-31
     return address: 1
     saved regs: 8-9, 18-27
     3 = global pointer, 4 = thread pointer (not sure if they need to be avoided)
     0 avoided (hardwired zero)
     2 avoided (stack pointer)
     3 avoided (global pointer)
     31 avoided (used by encoder)
     4 avoid regs means 28 regs available for CakeML
     constraints:
       the last 3 of these (25, 26, 27) must be mapped to callee saved regs
       0 1 and 2 must be mapped to link reg (1), 1st arg (10), 2nd arg (11)
  *)
  (insert 0 1 o
   insert 1 10 o
   insert 2 11 o
   insert 3 28 o
   (* the rest to make the mapping well-formed *)
   insert 10 29 o
   insert 11 30 o
   insert 28 0 o
   insert 29 2 o
   insert 30 3) LN:num num_map`;

val riscv_names_def = save_thm("riscv_names_def",
  CONV_RULE (RAND_CONV EVAL) riscv_names_def);

val _ = export_theory();
