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
    | p => p`

val prog_comp_def = Define `
  prog_comp f (n,p) = (n,comp f p)`

val compile_def = Define `
  compile f prog = MAP (prog_comp f) prog`;

val _ = export_theory();
