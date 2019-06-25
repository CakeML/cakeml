(*
  This compiler phase renames the registers to fit with the target
  architecture.
*)

open preamble stackLangTheory

val _ = new_theory "stack_names";

val _ = set_grammar_ancestry["stackLang"];

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = overload_on("find_name",``tlookup``);

val ri_find_name_def = Define `
  (ri_find_name f (Reg r) = Reg (find_name f r)) /\
  (ri_find_name f (Imm w) = Imm w)`

val inst_find_name_def = Define `
  inst_find_name f i =
    dtcase i of
    | Skip => Skip
    | Const r w => Const (find_name f r) w
    | Arith (Binop bop d r ri) =>
        Arith (Binop bop (find_name f d) (find_name f r) (ri_find_name f ri))
    | Arith (Shift sop d r i) =>
        Arith (Shift sop (find_name f d) (find_name f r) i)
    | Arith (Div r1 r2 r3) =>
        Arith (Div (find_name f r1) (find_name f r2) (find_name f r3))
    | Arith (AddCarry r1 r2 r3 r4) =>
        Arith (AddCarry (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (AddOverflow r1 r2 r3 r4) =>
        Arith (AddOverflow (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (SubOverflow r1 r2 r3 r4) =>
        Arith (SubOverflow (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (LongMul r1 r2 r3 r4) =>
        Arith (LongMul (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4))
    | Arith (LongDiv r1 r2 r3 r4 r5) =>
        Arith (LongDiv (find_name f r1) (find_name f r2) (find_name f r3) (find_name f r4) (find_name f r5))
    | Mem mop r (Addr a w) => Mem mop (find_name f r) (Addr (find_name f a) w)
    | FP (FPLess r f1 f2) => FP (FPLess (find_name f r) f1 f2)
    | FP (FPLessEqual r f1 f2) => FP (FPLessEqual (find_name f r) f1 f2)
    | FP (FPEqual r f1 f2) => FP (FPEqual (find_name f r) f1 f2)
    | FP (FPMovToReg r1 r2 d) => FP (FPMovToReg (find_name f r1) (find_name f r2) d)
    | FP (FPMovFromReg d r1 r2) => FP (FPMovFromReg d (find_name f r1) (find_name f r2))
    | i => i`

val dest_find_name_def = Define`
  dest_find_name f (INR r) = INR (find_name f r) ∧
  dest_find_name f x = x`;

local val comp_quotation = `
  comp f p =
    dtcase p of
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
        Call (dtcase ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp f p1,find_name f lr,l1,l2))
             (dest_find_name f dest)
             (dtcase exc of
              | NONE => NONE
              | SOME (p2,l1,l2) => SOME (comp f p2,l1,l2))
    | Install r1 r2 r3 r4 r5 => Install (find_name f r1) (find_name f r2)
      (find_name f r3) (find_name f r4) (find_name f r5)
    | CodeBufferWrite r1 r2 => CodeBufferWrite (find_name f r1) (find_name f r2)
    | FFI i r1 r2 r3 r4 r5 => FFI i (find_name f r1) (find_name f r2) (find_name f r3)
                                    (find_name f r4) (find_name f r5)
    | JumpLower r1 r2 dest => JumpLower (find_name f r1) (find_name f r2) dest
    | p => p`
in
val comp_def = Define comp_quotation

Theorem comp_pmatch = Q.prove(
  `∀f p.` @
    (comp_quotation |>
     map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq)),
   rpt(
    rpt strip_tac
    >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
    >> every_case_tac
    >> fs[Once comp_def]));
end

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

val _ = export_theory();
