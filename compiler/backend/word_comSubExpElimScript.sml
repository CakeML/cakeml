(*
This file is a Work in Progress.
It gives some functions and verification proofs about a Common Sub-Expression Elimination occuring right atfer the SSA-like renaming.
*)

(*
Mind map / TODO:
- the register equivalence form
    -> num list list
    -> Grouping equivalent registers together, keeping the first register added to a group in the head.
    -> Adding a r2 -> r1 to the existing mapping consits of looking if ∃group∈map. r1∈group.
         If so, we look if ∃group'∈map. r2∈group'.
           If so, we merge group and group'.
           Else, we add r2 to group in the second place.
         Else, we look if ∃group'∈map. r2∈group'.
           If so, we add r1 to group' in the second place.
           Else, we create a group=[r1;r2] that we add to map.
    -> !!! Case of function call we context conservation !!!
       One solution could be 
*)        
        
open preamble wordLangTheory boolTheory mlmapTheory

val _ = new_theory "comSubExpElim";
                             
(*
  Can not figure out how to make `NotGE` work, HOL keep raising:
  > The following variables are free in the right hand side of the proposed definition: "NotGE"
  So I replaced it with `Greater`.
*)
Definition listCmp_def:
  (listCmp ( (hd1:num) :: tl1) ( (hd2:num) :: tl2) = if hd1=hd2 then listCmp tl1 tl2 else if hd1>hd2 then Greater else Greater) ∧
  (listCmp [] [] = Equal) ∧
  (listCmp (hd1::tl1) [] = Greater) ∧
  (listCmp [] (hd2::tl2) = Greater)
End

Theorem listCmp_correct:
  ∀L1 L2. (listCmp L1 L2 = Equal) ⇔ L1 = L2
Proof
  strip_tac >>
  Induct_on ‘L1’
  >- (Cases_on ‘L2’
      \\ rw[listCmp_def])
  >- (Cases_on ‘L2’
      >- rw[listCmp_def]
      >- (strip_tac >>
          Cases_on ‘h=h'’
          \\ rw[listCmp_def]))
QED
        
(*
Principle:
  We keep track of a map containing all instructions already dealt with, and we explore the program to find instuctions matching one in the map.
  If we find one, we change the instruction by a simple move and we keep track of the registers equivalence.
  If we don't find any, depending on the instruction, we store it into the map under the shape of an num list.
Signification of the terms:
    r -> registers or imm_registers
    i -> instructions
    e -> expressions
    x -> "store_name"
    p -> programs
    c -> comparisons
    m -> num_set
    b -> binop
    s -> string
*)
Definition comSubExpElim_def:
  instrToList regs instrs (Skip) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Move r1 r2) = ((r1,r2)::regs, instrs, Move r1 r2) ∧
  instrToList regs instrs (Inst i) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Assign r e) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Get r x) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Set x r) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Store e r) = (regs, instrs, Skip) ∧
  instrToList regs instrs (MustTerminate p) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Call arg1 arg2 arg3 arg4) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Seq p1 p2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (If c r1 r2 p1 p2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Alloc r m) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Raise r) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Return r1 r2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Tick) = (regs, instrs, Skip) ∧
  instrToList regs instrs (OpCurrHeap b r1 r2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (LocValue r1 r2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (Install r1 r2 r3 r4 m) = (regs, instrs, Skip) ∧
  instrToList regs instrs (CodeBufferWrite r1 r2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (DataBufferWrite r1 r2) = (regs, instrs, Skip) ∧
  instrToList regs instrs (FFI s r1 r2 r3 r4 m) = (regs, instrs, Skip)
End

        
