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
        Arith (Shift sop (find_name f d) (find_name f r) (find_name f i))
    | Mem mop r (Addr a w) => Mem mop (find_name f r) (Addr (find_name f a) w)`

val comp_def = Define `
  comp f p =
    case p of
    | Halt r => Halt (find_name f r)
    | Raise r => Raise (find_name f r)
    | Return r1 r2 => Return (find_name f r1) (find_name f r2)
    | Inst i => Inst (inst_find_name f i)
    | Seq p1 p2 => Seq (comp f p1) (comp f p2)
    | If c r ri p1 p2 =>
        If c (find_name f r) (ri_find_name f ri) (comp f p1) (comp f p2)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp f p1,find_name f lr,l1,l2))
          dest (case exc of
                | NONE => NONE
                | SOME (p2,l1,l2) => SOME (comp f p2,l1,l2))
    | FFI i r1 r2 r3 => FFI i (find_name f r1) (find_name f r2) (find_name f r3)
    | p => p`

val prog_comp_def = Define `
  prog_comp f (n,p) = (n,comp f p)`

val compile_def = Define `
  compile f prog = MAP (prog_comp f) prog`;

(* some defaults *)

val x64_names_def = Define `
  x64_names =
    (* 16 regs, must avoid 4 and 5, names:
         r0=rax, r1=rbx, r2=rcx, r3=rdx, r4=rbp, r5=rsp, r6=rsi,
         r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
       The first six arguments are passed in registers. The first
       argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
       the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
       in r8 and the sixth in r9.
     *)
    (insert 1 7 o
     insert 2 6 o
  (* insert 3 3 o *)
     insert 4 2 o
     insert 5 8 o
     insert 6 9 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 7 1 o
     insert 8 14 o
     insert 9 15) LN:num num_map`

val x64_names_def = save_thm("x64_names_def",
  CONV_RULE (RAND_CONV EVAL) x64_names_def);

val _ = export_theory();
