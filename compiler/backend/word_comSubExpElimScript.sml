(*
This file is a Work in Progress.
It gives some functions and verification proofs about a Common Sub-Expression
Elimination occuring right atfer the SSA-like renaming.
*)

(*
Mind map / TODO:
- the register equivalence form
    -> num list list
    -> Grouping equivalent registers together, keeping the first register
         added to a group in the head.
    -> Adding a r2 -> r1 to the existing mapping consits of looking if
         ∃group∈map. r1∈group.
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

Type regsT = ``:num list list``

(* LIST COMPARISON *)

Definition listCmp_def:
  (listCmp ((hd1:num) :: tl1) ((hd2:num) :: tl2) =
   if hd1=hd2
     then listCmp tl1 tl2
     else if hd1>hd2 then Greater else Less) ∧
  (listCmp [] [] = Equal) ∧
  (listCmp (hd1::tl1) [] = Greater) ∧
  (listCmp [] (hd2::tl2) = Less)
End

Theorem listCmpEq_correct:
  ∀L1 L2. listCmp L1 L2 = Equal ⇔ L1 = L2
Proof
  strip_tac
  \\Induct_on ‘L1’
    >- (Cases_on ‘L2’
        \\ rw[listCmp_def])
    >- (Cases_on ‘L2’
        >- rw[listCmp_def]
        >- (strip_tac >>
            Cases_on ‘h=h'’
            \\ rw[listCmp_def]))
QED

(* REGISTERS EQUIVALENCE MEMORY *)

Definition listLookup_def:
  listLookup x [] = F ∧
  listLookup x (y::tl) = if x=y then T else listLookup x tl
End

Definition regsLookup_def:
  regsLookup r [] = F ∧
  regsLookup r (hd::tl) = if listLookup r hd then T else regsLookup r tl
End

Definition regsUpdate1Aux_def:
  regsUpdate1Aux r l (hd::tl) =
    if listLookup r hd
      then (l ++ hd)::tl
      else hd::(regsUpdate1Aux r l tl)
End

Definition regsUpdate1_def:
  regsUpdate1 r1 r2 (hd::tl) =
    if listLookup r1 hd
      then if listLookup r2 hd
        then (hd::tl)
        else regsUpdate1Aux r2 hd tl
      else if listLookup r2 hd
        then regsUpdate1Aux r1 hd tl
        else hd::(regsUpdate1 r1 r2 tl)
End

Definition regsUpdate2_def:
  regsUpdate2 r1 r2 ((hd::tl)::tl') =
    if listLookup r1 (hd::tl)
      then (hd::r2::tl)::tl'
      else (hd::tl)::(regsUpdate2 r1 r2 tl')
End

Definition regsUpdate_def:
  regsUpdate r1 r2 [] = [[r1;r2]] ∧
  regsUpdate r1 r2 (hd::tl) =
    if regsLookup r1 (hd::tl)
      then if regsLookup r2 (hd::tl)
        then regsUpdate1 r1 r2 (hd::tl)
        else regsUpdate2 r1 r2 (hd::tl)
      else if regsLookup r2 (hd::tl)
        then regsUpdate2 r2 r1 (hd::tl)
        else [r1;r2]::hd::tl
End

Theorem regsUpdate_test_merge1:
  regsUpdate 1 6 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3;4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_merge2:
  regsUpdate 1 7 [[1;2;3];[4;5;6];[7;8;9]] = [[4;5;6];[1;2;3;7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_merge3:
  regsUpdate 5 7 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3]; [4;5;6;7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_merge4:
  regsUpdate 6 1 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3;4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_merge5:
  regsUpdate 7 1 [[1;2;3];[4;5;6];[7;8;9]] = [[4;5;6];[1;2;3;7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_merge6:
  regsUpdate 7 5 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3]; [4;5;6;7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_eq1:
  regsUpdate 1 2 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_eq2:
  regsUpdate 4 5 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_eq3:
  regsUpdate 8 9 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add1:
  regsUpdate 2 10 [[1;2;3];[4;5;6];[7;8;9]] = [[1;10;2;3];[4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add2:
  regsUpdate 6 10 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;10;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add3:
  regsUpdate 9 10 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;10;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add4:
  regsUpdate 10 2 [[1;2;3];[4;5;6];[7;8;9]] = [[1;10;2;3];[4;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add5:
  regsUpdate 10 6 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;10;5;6];[7;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

Theorem regsUpdate_test_add6:
  regsUpdate 10 9 [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;10;8;9]]
Proof
  rw[regsUpdate_def,regsUpdate1_def,regsUpdate1Aux_def,
     regsUpdate2_def,regsLookup_def,listLookup_def]
QED

(* REGISTER TRANSFORMATIONS *)

Definition canonicalRegs_def:
  canonicalRegs (r:num) [] = r ∧
  canonicalRegs r (hd::tl) =
  if listLookup r hd
    then HD hd
    else canonicalRegs r tl
End

Definition canonicalExp_def:
  canonicalExp e regs = e
End

Definition canonicalMultExp_def:
  canonicalMultExp [] regs = [] ∧
  canonicalMultExp (hd::tl) regs = (canonicalExp hd regs)::(canonicalMultExp tl regs)
End

Definition canonicalMoveRegs_def:
  canonicalMoveRegs [] regs = ([], regs) ∧
  canonicalMoveRegs ((r1,r2)::tl) regs =
    let r2' = canonicalRegs r2 regs in
    let regs' = regsUpdate r1 r2' regs in
    let (tl', regs'') = canonicalMoveRegs tl regs' in
    (r1,r2')::tl', regs''
End

Definition canonicalExp_def:
  canonicalExp (Const w) regs = Const w ∧
  canonicalExp (Var r) regs = Var (canonicalRegs r regs) ∧
  canonicalExp (Lookup s) regs = Lookup s ∧
  canonicalExp (Load e) regs = Load (canonicalExp e regs) ∧
  canonicalExp (Op op nl) regs = Op op (canonicalMultExp nl regs) ∧
  canonicalExp (Shift s e n) regs = Shift s (canonicalExp e regs) n
End

(* SEEN INSTRUCTIONS MEMORY *)

(* TODO *)
Definition wordToNum_def:
  wordToNum w = (0:num)
End

Definition shiftToNum_def:
  shiftToNum Lsl = (69:num) ∧
  shiftToNum Lsr = 70 ∧
  shiftToNum Asr = 71 ∧
  shiftToNum Ror = 72
End

Theorem shiftToNum_unique:
  ∀s1 s2. s1 = s2 ⇔ shiftToNum s1 = shiftToNum s2
Proof
  rpt strip_tac >>
  Cases_on ‘s1’ \\
  (Cases_on ‘s2’ \\
  rw[shiftToNum_def])
QED

Definition storeNameToNumList_def:
  storeNameToNumList NextFree = [(51:num)] ∧
  storeNameToNumList EndOfHeap = [52] ∧
  storeNameToNumList TriggerGC = [53] ∧
  storeNameToNumList HeapLength = [54] ∧
  storeNameToNumList ProgStart = [55] ∧
  storeNameToNumList BitmapBase = [56] ∧
  storeNameToNumList CurrHeap = [57] ∧
  storeNameToNumList OtherHeap = [58] ∧
  storeNameToNumList AllocSize = [59] ∧
  storeNameToNumList Globals = [60] ∧
  storeNameToNumList GlobReal = [61] ∧
  storeNameToNumList Handler = [62] ∧
  storeNameToNumList GenStart = [63] ∧
  storeNameToNumList CodeBuffer = [64] ∧
  storeNameToNumList CodeBufferEnd = [65] ∧
  storeNameToNumList BitmapBuffer = [66] ∧
  storeNameToNumList BitmapBufferEnd = [67] ∧
  storeNameToNumList (Temp w) = [68; wordToNum w]
End

Definition arithOpToNum_def:
  arithOpToNum Add = (46:num) ∧
  arithOpToNum Sub = 47 ∧
  arithOpToNum And = 48 ∧
  arithOpToNum Or = 49 ∧
  arithOpToNum Xor = 50
End

Theorem arithOpToNum_unique:
  ∀op1 op2. op1 = op2 ⇔ arithOpToNum op1 = arithOpToNum op2
Proof
  rpt strip_tac >>
  Cases_on ‘op1’ \\
  (Cases_on ‘op2’ \\
  rw[arithOpToNum_def])
QED
        

Definition expListToNumList_def:
  expListToNumList el = []
End

Definition expToNumList_def:
  expToNumList (Const w) = [40; wordToNum w] ∧
  expToNumList (Var r) = [41; r+100] ∧
  expToNumList (Lookup n) = 42::(storeNameToNumList n) ∧
  expToNumList (Load e) = 43::(expToNumList e) ∧
  expToNumList (Op op el) = [44; arithOpToNum op] ++ (expListToNumList el) ∧
  expToNumList (Shift s e r) = [45; shiftToNum s] ++ (expToNumList e) ++ [r+100]
End
        
(* !!!! Op has exp list, need to end list by unique id too !!!! *)
Definition expListToNumList_def:
  expListToNumList [] = [(38:num)] ∧
  expListToNumList (hd::tl) = (expToNumList hd) ++ 39::(expListToNumList tl)
End

Definition regImmToNumList_def:
  regImmToNumList (Reg r) = [36; r+100] ∧
  regImmToNumList (Imm w) = [37; wordToNum w]
End

Definition arithToNumList_def:
  arithToNumList (Binop op r1 r2 ri) = [28; arithOpToNum op; r1+100; r2+100] ++ regImmToNumList ri ∧
  arithToNumList (LongMul r1 r2 r3 r4) = [29; r1+100; r2+100; r3+100; r4+100] ∧
  arithToNumList (LongDiv r1 r2 r3 r4 r5) = [30; r1+100; r2+100; r3+100; r4+100; r5+100] ∧
  arithToNumList (Shift s r1 r2 n) = [31; shiftToNum s; r1+100; r2+100; n] ∧
  arithToNumList (Div r1 r2 r3) = [32; r1+100; r2+100; r3+100] ∧
  arithToNumList (AddCarry r1 r2 r3 r4) = [33; r1+100; r2+100; r3+100; r4+100] ∧
  arithToNumList (AddOverflow r1 r2 r3 r4) = [34; r1+100; r2+100; r3+100; r4+100] ∧
  arithToNumList (SubOverflow r1 r2 r3 r4) = [35; r1+100; r2+100; r2+100; r4+100]
End

Definition memOpToNum_def:
  memOpToNum Load = (24:num) ∧
  memOpToNum Load8 = 25 ∧
  memOpToNum Store = 26 ∧
  memOpToNum Store8 = 27
End

Theorem memOpToNum_def:
  ∀op1 op2. op1 = op2 ⇔ memOpToNum op1 = memOpToNum op2
Proof
  rpt strip_tac >>
  Cases_on ‘op1’ \\
  (Cases_on ‘op2’ \\
  rw[memOpToNum_def])
QED

Definition fpToNumList_def:
  fpToNumList (FPLess r1 r2 r3) = [8; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPLessEqual r1 r2 r3) = [9; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPEqual r1 r2 r3) = [10; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPAbs r1 r2) = [11; r1+100; r2+100] ∧
  fpToNumList (FPNeg r1 r2) = [12; r1+100; r2+100] ∧
  fpToNumList (FPSqrt r1 r2) = [13; r1+100; r2+100] ∧
  fpToNumList (FPAdd r1 r2 r3) = [14; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPSub r1 r2 r3) = [15; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPMul r1 r2 r3) = [16; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPDiv r1 r2 r3) = [17; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPFma r1 r2 r3) = [18; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPMov r1 r2) = [19; r1+100; r2+100] ∧
  fpToNumList (FPMovToReg r1 r2 r3) = [20; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPMovFromReg r1 r2 r3) = [21; r1+100; r2+100; r3+100] ∧
  fpToNumList (FPToInt r1 r2) = [22; r1+100; r2+100] ∧
  fpToNumList (FPFromInt r1 r2) = [23; r1+100; r2+100]
End

Theorem fpToNumList_def:
  ∀fp1 fp2. fp1 = fp2 ⇔ fpToNumList fp1 = fpToNumList fp2
Proof
  rpt strip_tac >>
  Cases_on ‘fp1’ \\
  (Cases_on ‘fp2’ \\
  rw[fpToNumList_def])
QED


Definition instToNumList_def:
  instToNumList (Skip) = [3] ∧
  instToNumList (Const r w) = [4;r+100; wordToNum w] ∧
  instToNumList (Arith a) = 5::(arithToNumList a) ∧
  instToNumList (Mem op r (Addr r' w)) = [6; memOpToNum op; r+100; r'+100; wordToNum w] ∧
  instToNumList (FP fp) = 7::(fpToNumList fp)
End

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an instruction.
Numbers above 99 corresponds to a register or a word value.
*)
(* TODO : rename instruction numbers such that each is unique *)
Definition progToNumList_def:
  progToNumList (Assign r e) = 0::(expToNumList e) ∧
  progToNumList (LocValue r1 r2) = [1; r1 + 100; r2 + 100] ∧
  progToNumList (Inst i) = 2::(instToNumList i) ∧
  progToNumList (Skip) = [3] ∧
  progToNumList (Move _ _) = [4] ∧
  progToNumList (Get _ _) = [5] ∧
  progToNumList (Set _ _) = [6] ∧
  progToNumList (Store _ _) = [7] ∧
  progToNumList (MustTerminate _) = [8] ∧
  progToNumList (Call _ _ _ _) = [9] ∧
  progToNumList (Seq _ _) = [10] ∧
  progToNumList (If _ _ _ _ _) = [11] ∧
  progToNumList (Alloc _ _) = [12] ∧
  progToNumList (Raise _) = [13] ∧
  progToNumList (Return _ _) = [14] ∧
  progToNumList (Tick) = [15] ∧
  progToNumList (OpCurrHeap _ _ _) = [16] ∧
  progToNumList (Install _ _ _ _ _) = [17] ∧
  progToNumList (CodeBufferWrite _ _) = [18] ∧
  progToNumList (DataBufferWrite _ _) = [19] ∧
  progToNumList (FFI _ _ _ _ _ _) = [20]
End

(*
Theorem progToNumList_unique:
  ∀p1 p2. (p1 = p2) ⇔ (progToNumList p1 = progToNumList p2)
Proof
  
strip_tac
Induct_on ‘p1’
  \\(strip_tac >>
     eq_tac >>
       rw[] >>
       Cases_on ‘p2’ \\ rw[progToNumList_def])

        
  >- Induct_on ‘p1’
  \\Cases_on ‘progToNumList p2’
  \\rw[wordToNum_def, shiftToNum_def, storeNameToNumList_def, arithOpToNum_def, expListToNumList_def, expToNumList_def, expListToNumList_def, regImmToNumList_def, arithToNumList_def, memOpToNum_def, fpToNumList_def, instToNumList_def, progToNumList_def]

QED

wordToNum_def, shiftToNum_def, storeNameToNumList_def, arithOpToNum_def, expListToNumList_def, expToNumList_def, expListToNumList_def, regImmToNumList_def, arithToNumList_def, memOpToNum_def, fpToNumList_def, instToNumList_def, progToNumList_def
*)

               
(* TODO *)
Definition comSubExpElimInst_def:
  comSubExpElimInst regs instrs Skip = (regs, instrs, Inst Skip) ∧
  comSubExpElimInst regs instrs (Const r w) = (regs, instrs, Inst Skip) ∧
  comSubExpElimInst regs instrs (Arith a) = (regs, instrs, Inst Skip) ∧
  comSubExpElimInst regs instrs (Mem op r addr) = (regs, instrs, Inst Skip) ∧
  comSubExpElimInst regs instrs (FP f) = (regs, instrs, Inst Skip)
End

(*
Principle:
  We keep track of a map containing all instructions already dealt with,
    and we explore the program to find instuctions matching one in the map.
  If we find one, we change the instruction by a simple move and we keep track
    of the registers equivalence.
  If we don't find any, depending on the instruction, we store it into the map
    under the shape of an num list.
Signification of the terms:
    r -> registers or imm_registers
    rs-> multiple registers associations ((num # num) list) (For the Move)
    i -> instructions
    e -> expressions
    x -> "store_name"
    p -> programs
    c -> comparisons
    m -> num_set
    b -> binop
    s -> string
*)
(* TODO *)
Definition comSubExpElim_def:
  (comSubExpElim (regs:regsT) (instrs:(num list,num)map) (Skip) =
                (regs, instrs, Skip)) ∧
  (comSubExpElim regs instrs (Move r rs) =
            let (rs', regs') = canonicalMoveRegs rs regs in
                (regs', instrs, Move r rs')) ∧
  (comSubExpElim regs instrs (Inst i) =
            let (regs', instrs', p) = comSubExpElimInst regs instrs i in
                (regs', instrs', p)) ∧
  (comSubExpElim regs instrs (Assign r e) =
            let e' = canonicalExp e regs in
            let i = progToNumList (Assign r e') in
            case lookup instrs i of
              |NONE => (regs, insert instrs i r, Assign r e')
              |SOME r' => (regsUpdate r r' regs, instrs, Move 0 [(r,r')])) ∧
  (comSubExpElim regs instrs (Get r x) =
                (regs, instrs, Get r x)) ∧
  (comSubExpElim regs instrs (Set x e) =
            let e' = canonicalExp e regs in
                (regs, instrs, Set x e')) ∧
  (comSubExpElim regs instrs (Store e r) =
                (regs, instrs, Store e r)) ∧
  (comSubExpElim regs instrs (MustTerminate p) =
            let (regs', instrs', p') = comSubExpElim regs instrs p in
                (regs', instrs', MustTerminate p')) ∧
  (comSubExpElim regs instrs (Call arg1 arg2 arg3 arg4) =
                (regs, instrs, Call arg1 arg2 arg3 arg4)) ∧

  (comSubExpElim regs instrs (Seq p1 p2) =
            let (regs1, instrs1, p1') = comSubExpElim regs instrs p1 in
            let (regs2, instrs2, p2') = comSubExpElim regs1 instrs1 p2 in
                (regs2, instrs2, Seq p1' p2')) ∧
  (comSubExpElim regs instrs (If c r1 r2 p1 p2) =
                (regs, instrs, If c r1 r2 p1 p2)) ∧

  (comSubExpElim regs instrs (Alloc r m) =
                (regs, instrs, Alloc r m)) ∧
  (comSubExpElim regs instrs (Raise r) =
            let r' = canonicalRegs r regs in
                (regs, instrs, Raise r')) ∧
  (comSubExpElim regs instrs (Return r1 r2) =
            let r1' = canonicalRegs r1 regs in
            let r2' = canonicalRegs r2 regs in
                (regs, instrs, Return r1' r2')) ∧
  (comSubExpElim regs instrs (Tick) = (regs, instrs, Tick)) ∧
  (comSubExpElim regs instrs (OpCurrHeap b r1 r2) =
            let r2' = canonicalRegs r2 regs in
                (regs, instrs, OpCurrHeap b r1 r2')) ∧
  (comSubExpElim regs instrs (LocValue r1 r2) =
                (regs, instrs, LocValue r1 r2)) ∧
  (comSubExpElim regs instrs (Install r1 r2 r3 r4 m) =
                (regs, instrs, Install r1 r2 r3 r4 m)) ∧
  (comSubExpElim regs instrs (CodeBufferWrite r1 r2) =
                (regs, instrs, CodeBufferWrite r1 r2)) ∧
  (comSubExpElim regs instrs (DataBufferWrite r1 r2) =
                (regs, instrs, DataBufferWrite r1 r2)) ∧
  (comSubExpElim regs instrs (FFI s r1 r2 r3 r4 m) =
                (regs, instrs, FFI s r1 r2 r3 r4 m))
End

val _ = export_theory ();
