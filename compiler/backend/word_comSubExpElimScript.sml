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
*)

open preamble wordLangTheory wordsTheory boolTheory mlmapTheory sptreeTheory

val _ = new_theory "word_comSubExpElim";

Type regsE = ``:num list list``
Type regsM = ``:num num_map``
Type instrsM = ``:(num list,num)map``

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
  canonicalRegs (instMap:regsM) (ochMap:regsM) (r:num) =
  case sptree$lookup r instMap of
  | SOME r' => r'
  | NONE => case sptree$lookup r ochMap of
            | NONE => r
            | SOME r' => r'
End

Definition canonicalImmReg_def:
  canonicalImmReg instMap ochMap (Reg r) = Reg (canonicalRegs instMap ochMap r) ∧
  canonicalImmReg instMap ochMap (Imm w) = Imm w
End

Definition canonicalMultRegs_def:
  canonicalMultRegs instMap ochMap[] = [] ∧
  canonicalMultRegs instMap ochMap (hd::tl) =
    (canonicalRegs instMap ochMap hd)::(canonicalMultRegs instMap ochMap tl)
End

Definition canonicalMoveRegs_def:
  canonicalMoveRegs instEq instMap ochMap [] = (instEq, instMap, ochMap, []) ∧
  canonicalMoveRegs instEq instMap ochMap ((r1,r2)::tl) =
    case sptree$lookup r2 ochMap of
    | SOME r2' => let ochMap' = sptree$insert r1 r2' ochMap in
                  let (instEq', instMap', ochMap'', tl') = canonicalMoveRegs instEq instMap ochMap' tl in
                    (instEq', instMap', ochMap'', (r1,r2')::tl')
    | NONE     => let r2' = (case sptree$lookup r2 instMap of SOME r => r | NONE => r2) in
                  let instEq' = regsUpdate r2' r1 instEq in
                  let instMap' = sptree$insert r1 r2' instMap in
                  let (instEq'', instMap'', ochMap', tl') = canonicalMoveRegs instEq' instMap' ochMap tl in
                    (instEq'', instMap'', ochMap', (r1,r2')::tl')
End

Definition canonicalExp_def:
  canonicalExp instMap ochMap e = e
End

Definition canonicalMultExp_def:
  canonicalMultExp instMap ochMap [] = [] ∧
  canonicalMultExp instMap ochMap (hd::tl) =
    (canonicalExp instMap ochMap hd)::(canonicalMultExp instMap ochMap tl)
End

Definition canonicalExp_def:
  canonicalExp instMap ochMap (Const w) = Const w ∧
  canonicalExp instMap ochMap (Var r) = Var (canonicalRegs instMap ochMap r) ∧
  canonicalExp instMap ochMap (Lookup s) = Lookup s ∧
  canonicalExp instMap ochMap (Load e) = Load (canonicalExp instMap ochMap e) ∧
  canonicalExp instMap ochMap (Op op nl) = Op op (canonicalMultExp instMap ochMap nl) ∧
  canonicalExp instMap ochMap (Shift s e n) = Shift s (canonicalExp instMap ochMap e) n
End

Definition canonicalArith_def:
  canonicalArith instMap ochMap (Binop op r1 r2 r3) =
    Binop op r1 (canonicalRegs instMap ochMap r2) (canonicalImmReg instMap ochMap r3) ∧
  canonicalArith instMap ochMap (Shift s r1 r2 n) =
    Shift s (canonicalRegs instMap ochMap r1) (canonicalRegs instMap ochMap r2) n ∧
  canonicalArith instMap ochMap (Div r1 r2 r3) =
    Div r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalArith instMap ochMap (LongMul r1 r2 r3 r4) =
    LongMul r1 r2 (canonicalRegs instMap ochMap r3) (canonicalRegs instMap ochMap r4) ∧
  canonicalArith instMap ochMap (LongDiv r1 r2 r3 r4 r5) =
    LongDiv r1 r2 (canonicalRegs instMap ochMap r3) (canonicalRegs instMap ochMap r4) (canonicalRegs instMap ochMap r5) ∧
  canonicalArith instMap ochMap (AddCarry r1 r2 r3 r4) =
    AddCarry r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) r4 ∧
  canonicalArith instMap ochMap (AddOverflow r1 r2 r3 r4) =
    AddOverflow r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) r4 ∧
  canonicalArith instMap ochMap (SubOverflow r1 r2 r3 r4) =
    SubOverflow r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) r4
End

Definition canonicalFp_def:
  canonicalFp instMap ochMap (FPLess r1 r2 r3) =
    FPLess r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPLessEqual r1 r2 r3) =
    FPLessEqual r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPEqual r1 r2 r3) =
    FPEqual r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPAbs r1 r2) =
    FPAbs r1 (canonicalRegs instMap ochMap r2) ∧
  canonicalFp instMap ochMap (FPNeg r1 r2) =
    FPNeg r1 (canonicalRegs instMap ochMap r2) ∧
  canonicalFp instMap ochMap (FPSqrt r1 r2) =
    FPSqrt r1 (canonicalRegs instMap ochMap r2) ∧
  canonicalFp instMap ochMap (FPAdd r1 r2 r3) =
    FPAdd r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPSub r1 r2 r3) =
    FPSub r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPMul r1 r2 r3) =
    FPMul r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPDiv r1 r2 r3) =
    FPDiv r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPFma r1 r2 r3) =
    FPFma r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPMov r1 r2) =
    FPMov r1 (canonicalRegs instMap ochMap r2) ∧
  canonicalFp instMap ochMap (FPMovToReg r1 r2 r3) =
    FPMovToReg r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPMovFromReg r1 r2 r3) =
    FPMovFromReg r1 (canonicalRegs instMap ochMap r2) (canonicalRegs instMap ochMap r3) ∧
  canonicalFp instMap ochMap (FPToInt r1 r2) =
    FPToInt r1 (canonicalRegs instMap ochMap r2) ∧
  canonicalFp instMap ochMap (FPFromInt r1 r2) =
    FPFromInt r1 (canonicalRegs instMap ochMap r2)
End

(* SEEN INSTRUCTIONS MEMORY *)

Definition wordToNum_def:
  wordToNum w = w2n w
End

Theorem wordToNum_unique:
  ∀w1 w2. w1 = w2 ⇔ wordToNum w1 = wordToNum w2
Proof
  rw[wordToNum_def]
QED


Definition shiftToNum_def:
  shiftToNum Lsl = (38:num) ∧
  shiftToNum Lsr = 39 ∧
  shiftToNum Asr = 40 ∧
  shiftToNum Ror = 41
End

Theorem shiftToNum_unique:
  ∀s1 s2. s1 = s2 ⇔ shiftToNum s1 = shiftToNum s2
Proof
  rpt strip_tac >>
  Cases_on ‘s1’ \\
  (Cases_on ‘s2’ \\
  rw[shiftToNum_def])
QED


Definition arithOpToNum_def:
  arithOpToNum Add = (33:num) ∧
  arithOpToNum Sub = 34 ∧
  arithOpToNum And = 35 ∧
  arithOpToNum Or = 36 ∧
  arithOpToNum Xor = 37
End

Theorem arithOpToNum_unique:
  ∀op1 op2. op1 = op2 ⇔ arithOpToNum op1 = arithOpToNum op2
Proof
  rpt strip_tac >>
  Cases_on ‘op1’ \\
  (Cases_on ‘op2’ \\
  rw[arithOpToNum_def])
QED


(*
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
Theorem storeNameToNumList_unique:
  ∀n1 n2. n1 = n2 ⇔ storeNameToNumList n1 = storeNameToNumList n2
Proof
  rpt strip_tac >>
  Cases_on ‘n1’ \\
  (Cases_on ‘n2’ \\
  rw[storeNameToNumList_def, wordToNum_unique])
QED
Definition expListToNumList_def:
  expListToNumList [] = [(38:num)] ∧
  expListToNumList ((Const w)::tl) = 40::(wordToNum w)::(expListToNumList tl) ∧
  expListToNumList ((Var r)::tl) = 41::(r+100)::(expListToNumList tl) ∧
  expListToNumList ((Lookup n)::tl) = 42::(storeNameToNumList n) ++ expListToNumList tl ∧
  expListToNumList ((Load e)::tl) = 43::(expListToNumList [e]) ++ expListToNumList tl ∧
  expListToNumList ((Op op el)::tl) = [44; arithOpToNum op] ++ (expListToNumList el) ++ expListToNumList tl ∧
  expListToNumList ((Shift s e r)::tl) = 45::(shiftToNum s)::(expListToNumList [e]) ++ [r+100] ++ expListToNumList tl
End
Definition expToNumList_def:
  expToNumList e = expListToNumList [e]
End
Definition expListToNumList_def:
  expListToNumList (hd::tl) = (expToNumList hd) ++ 39::(expListToNumList tl)
End
Definition expToNumList_def:
  expToNumList (Const w) = [40; wordToNum w] ∧
  expToNumList (Var r) = [41; r+100] ∧
  expToNumList (Lookup n) = 42::(storeNameToNumList n) ∧
  expToNumList (Load e) = 43::(expToNumList e) ∧
  expToNumList (Op op []) = [38] ∧
  expToNumList (Op op (hd::tl)) = [arithOpToNum op] ++ (expToNumList hd) ++ (expToNumList (Op op tl)) ∧
  expToNumList (Shift s e r) = [45; shiftToNum s] ++ (expToNumList e) ++ [r+100]
End
Theorem expToNumList_unique:
  ∀e1 e2. e1 = e2 ⇔ expToNumList e1 = expToNumList e2
Proof ho_match_mp_tac expToNumList_ind
  strip_tac >>
  Induct_on ‘e1’ \\
  (Cases_on ‘e2’ \\
   rw[expToNumList_def, wordToNum_unique, storeNameToNumList_unique, arithOpToNum_unique, shiftToNum_unique])
   decide_tac
   Cases_on ‘l’
QED
*)

Definition regImmToNumList_def:
  regImmToNumList (Reg r) = [31; r+100] ∧
  regImmToNumList (Imm w) = [32; wordToNum w]
End

Theorem regImmToNumList_unique:
  ∀ri1 ri2. ri1 = ri2 ⇔ regImmToNumList ri1 = regImmToNumList ri2
Proof
  rpt strip_tac >>
  Cases_on ‘ri1’ \\
  (Cases_on ‘ri2’ \\
  rw[regImmToNumList_def, wordToNum_unique])
QED


Definition arithToNumList_def:
  arithToNumList (Binop op r1 r2 ri) = [23; arithOpToNum op; r2+100] ++ regImmToNumList ri ∧
  arithToNumList (LongMul r1 r2 r3 r4) = [24; r3+100; r4+100] ∧
  arithToNumList (LongDiv r1 r2 r3 r4 r5) = [25; r3+100; r4+100; r5+100] ∧
  arithToNumList (Shift s r1 r2 n) = [26; shiftToNum s; r2+100; n] ∧
  arithToNumList (Div r1 r2 r3) = [27; r2+100; r3+100] ∧
  arithToNumList (AddCarry r1 r2 r3 r4) = [28; r2+100; r3+100] ∧
  arithToNumList (AddOverflow r1 r2 r3 r4) = [29; r2+100; r3+100] ∧
  arithToNumList (SubOverflow r1 r2 r3 r4) = [30; r2+100; r3+100]
End
(*
Theorem arithToNumList_unique:
  ∀a1 a2. a1 = a2 ⇔ arithToNumList a1 = arithToNumList a2
Proof
  rpt strip_tac >>
  Cases_on ‘a1’ \\
  (Cases_on ‘a2’ \\
  rw[arithToNumList_def, regImmToNumList_unique, shiftToNum_unique, arithOpToNum_unique])
QED
*)

Definition memOpToNum_def:
  memOpToNum Load = (19:num) ∧
  memOpToNum Load8 = 20 ∧
  memOpToNum Store = 21 ∧
  memOpToNum Store8 = 22
End

Theorem memOpToNum_unique:
  ∀op1 op2. op1 = op2 ⇔ memOpToNum op1 = memOpToNum op2
Proof
  rpt strip_tac >>
  Cases_on ‘op1’ \\
  (Cases_on ‘op2’ \\
  rw[memOpToNum_def])
QED


Definition fpToNumList_def:
  fpToNumList (FPLess r1 r2 r3) = [3; r2+100; r3+100] ∧
  fpToNumList (FPLessEqual r1 r2 r3) = [4; r2+100; r3+100] ∧
  fpToNumList (FPEqual r1 r2 r3) = [5; r2+100; r3+100] ∧
  fpToNumList (FPAbs r1 r2) = [6; r2+100] ∧
  fpToNumList (FPNeg r1 r2) = [7; r2+100] ∧
  fpToNumList (FPSqrt r1 r2) = [8; r2+100] ∧
  fpToNumList (FPAdd r1 r2 r3) = [9; r2+100; r3+100] ∧
  fpToNumList (FPSub r1 r2 r3) = [10; r2+100; r3+100] ∧
  fpToNumList (FPMul r1 r2 r3) = [11; r2+100; r3+100] ∧
  fpToNumList (FPDiv r1 r2 r3) = [12; r2+100; r3+100] ∧
  fpToNumList (FPFma r1 r2 r3) = [13; r1+100; r2+100; r3+100] ∧ (* List never matched again *)
  fpToNumList (FPMov r1 r2) = [14; r2+100] ∧
  fpToNumList (FPMovToReg r1 r2 r3) = [15; r2+100; r3+100] ∧
  fpToNumList (FPMovFromReg r1 r2 r3) = [16; r2+100; r3+100] ∧
  fpToNumList (FPToInt r1 r2) = [17; r2+100] ∧
  fpToNumList (FPFromInt r1 r2) = [18; r2+100]
End
(*
Theorem fpToNumList_unique:
  ∀fp1 fp2. fpToNumList fp1 = fpToNumList fp2 ⇒ ∃r r'
Proof
  rpt strip_tac >>
  Cases_on ‘fp1’ \\
  (Cases_on ‘fp2’ \\
  rw[fpToNumList_def])
QED
*)

(*
Definition addrToNumList_def:
  addrToNumList (Addr r w) = [r+100; wordToNum w]
End
Theorem addrToNumList_unique:
  ∀a1 a2. a1 = a2 ⇔ addrToNumList a1 = addrToNumList a2
Proof
  rpt strip_tac >>
  Cases_on ‘a1’ \\
  (Cases_on ‘a2’ \\
  rw[addrToNumList_def, wordToNum_unique])
QED
*)

Definition instToNumList_def:
  instToNumList (Skip) = [1] ∧
  instToNumList (Const r w) = [2;wordToNum w] ∧
  instToNumList (Arith a) = arithToNumList a ∧
  instToNumList (FP fp) = fpToNumList fp
End
(*
Theorem instToNumList_unique:
  ∀i1 i2. i1 = i2 ⇔ instToNumList i1 = instToNumList i2
Proof
  rpt strip_tac >>
  Cases_on ‘i1’ \\
  (Cases_on ‘i2’ \\
   rw[instToNumList_def, wordToNum_unique, arithToNumList_unique,
      memOpToNum_unique, addrToNumList_unique, fpToNumList_unique])
QED
*)

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an instruction.
Numbers above 99 corresponds to a register or a word value.
*)
(* TODO : redo the rename of instruction numbers such that each is unique *)
Definition progToNumList_def:
  progToNumList (Inst i) = 0::(instToNumList i) ∧
  progToNumList (OpCurrHeap op r1 r2) = [1; arithOpToNum op; r2+100]
End
(*
Theorem progToNumList_unique:
  ∀p1 p2. (∃i. p1 = Inst i)∧(∃i. p2 = Inst i) ⇒
              (p1 = p2 ⇔ progToNumList p1 = progToNumList p2)
Proof
  rw[progToNumList_def, instToNumList_unique]
QED
*)

Definition firstRegOfArith_def:
  firstRegOfArith (Binop _ r _ _) = r ∧
  firstRegOfArith (Shift _ r _ _) = r ∧
  firstRegOfArith (Div r _ _) = r ∧
  firstRegOfArith (LongMul r _ _ _) = r ∧
  firstRegOfArith (LongDiv r _ _ _ _) = r ∧
  firstRegOfArith (AddCarry r _ _ _) = r ∧
  firstRegOfArith (AddOverflow r _ _ _) = r ∧
  firstRegOfArith (SubOverflow r _ _ _) = r
End

Definition firstRegOfFp_def:
  firstRegOfFp (FPLess r _ _) = r ∧
  firstRegOfFp (FPLessEqual r _ _) = r ∧
  firstRegOfFp (FPEqual r _ _) = r ∧
  firstRegOfFp (FPAbs r _) = r ∧
  firstRegOfFp (FPNeg r _) = r ∧
  firstRegOfFp (FPSqrt r _) = r ∧
  firstRegOfFp (FPAdd r _ _) = r ∧
  firstRegOfFp (FPSub r _ _) = r ∧
  firstRegOfFp (FPMul r _ _) = r ∧
  firstRegOfFp (FPDiv r _ _) = r ∧
  firstRegOfFp (FPFma r _ _) = r ∧
  firstRegOfFp (FPMov r _) = r ∧
  firstRegOfFp (FPMovToReg r _ _) = r ∧
  firstRegOfFp (FPMovFromReg r _ _) = r ∧
  firstRegOfFp (FPToInt r _) = r ∧
  firstRegOfFp (FPFromInt r _) = r
End

Definition comSubExpElimInst_def:
  (comSubExpElimInst (n:num) (instEq:regsE) (instMap:regsM) (instInstrs:instrsM) (ochMap:regsM) Skip = (n, instEq, instMap, instInstrs, Inst Skip)) ∧
  (comSubExpElimInst n instEq instMap instInstrs ochMap (Const r w) =
            let i = instToNumList (Const r w) in
            case mlmap$lookup instInstrs i of
            | SOME r' => (n+1, regsUpdate r' r instEq, insert r r' instMap, instInstrs, Move 0 [(r,r')])
            | NONE    => (n, instEq, instMap, insert instInstrs i r, Inst (Const r w))) ∧
  (comSubExpElimInst n instEq instMap instInstrs ochMap (Arith a) =
            let a' = canonicalArith instMap ochMap a in
            let r = firstRegOfArith a' in
            let i = instToNumList (Arith a') in
            case mlmap$lookup instInstrs i of
            | SOME r' => (n+1, regsUpdate r' r instEq, insert r r' instMap, instInstrs, Move 0 [(r,r')])
            | NONE    => (n, instEq, instMap, insert instInstrs i r, Inst (Arith a'))) ∧
  (comSubExpElimInst n instEq instMap instInstrs ochMap (Mem op r (Addr r' w)) =
            (n, instEq, instMap, instInstrs, Inst (Mem op (canonicalRegs instMap ochMap r) (Addr (canonicalRegs instMap ochMap r') w)))) ∧
  (comSubExpElimInst n instEq instMap instInstrs ochMap ((FP f):'a inst) =
            let f' = canonicalFp instMap ochMap f in
            let r = firstRegOfFp f' in
            let i = instToNumList ((FP f'):'a inst) in
            case mlmap$lookup instInstrs i of
            | SOME r' => (n+1, regsUpdate r' r instEq, insert r r' instMap, instInstrs, Move 0 [(r,r')])
            | NONE    => (n, instEq, instMap, insert instInstrs i r, Inst (FP f')))
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
Definition comSubExpElim_def:
  (comSubExpElim (n:num) (instEq:regsE) (instMap:regsM) (instInstrs:instrsM) (ochMap:regsM) (ochInstrs:instrsM) (Skip) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Skip)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Move r rs) =
            let (instEq', instMap', ochMap', rs') = canonicalMoveRegs instEq instMap ochMap rs in
                (n, instEq', instMap', instInstrs, ochMap', ochInstrs, Move r rs')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Inst i) =
            let (n', instEq', instMap', instInstrs', p) = comSubExpElimInst n instEq instMap instInstrs ochMap i in
                (n', instEq', instMap', instInstrs', ochMap, ochInstrs, p)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Assign r e) =
            let e' = canonicalExp instMap ochMap e in
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Assign r e')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Get r x) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Get r x)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Set x e) =
            let e' = canonicalExp instMap ochMap e in
                (n, instEq, instMap, instInstrs, LN, empty listCmp, Set x e')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Store e r) =
            let r' = canonicalRegs instMap ochMap r in
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Store e r')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (MustTerminate p) =
            let (n', instEq', instMap', instInstrs', ochMap', ochInstrs', p') = comSubExpElim n instEq instMap instInstrs ochMap ochInstrs p in
                (n', instEq', instMap', instInstrs', ochMap', ochInstrs', MustTerminate p')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Call ret dest args handler) =
                (n, [], LN, empty listCmp, LN, empty listCmp, Call ret dest args handler)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Seq p1 p2) =
            let (n1, regsEq1, regsMap1, instrs1, ochMap1, ochInstrs1, p1') = comSubExpElim n instEq instMap instInstrs ochMap ochInstrs p1 in
            let (n2, regsEq2, regsMap2, instrs2, ochMap2, ochInstrs2, p2') = comSubExpElim n1 regsEq1 regsMap1 instrs1 ochMap1 ochInstrs1 p2 in
                (n2, regsEq2, regsMap2, instrs2, ochMap2, ochInstrs2, Seq p1' p2')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (If c r1 r2 p1 p2) =
            let r1' = canonicalRegs instMap ochMap r1 in
            let r2' = canonicalImmReg instMap ochMap r2 in
            let (n1, instEq1, instMap1, instInstrs1, ochMap1, ochInstrs1, p1') = comSubExpElim n instEq instMap instInstrs ochMap ochInstrs p1 in
            let (n2, instEq2, instMap2, instInstrs2, ochMap2, ochInstrs2, p2') = comSubExpElim n1 instEq instMap instInstrs ochMap ochInstrs p2 in
                (n2, [], LN, empty listCmp, LN, empty listCmp, If c r1' r2' p1' p2')) ∧
                (* We don't know what happen in the IF. Intersection would be the best. *)
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Alloc r m) =
                (n, instEq, instMap, instInstrs, LN, empty listCmp, Alloc r m)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Raise r) =
            let r' = canonicalRegs instMap ochMap r in
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Raise r')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Return r1 r2) =
            let r1' = canonicalRegs instMap ochMap r1 in
            let r2' = canonicalRegs instMap ochMap r2 in
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Return r1' r2')) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Tick) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Tick)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs ((OpCurrHeap b r1 r2):'a prog) =
            let r2' = canonicalRegs instMap ochMap r2 in
            let pL = progToNumList ((OpCurrHeap b r1 r2'):'a prog) in
            case lookup ochInstrs pL of
            | NONE => (n, instEq, instMap, instInstrs, ochMap, insert ochInstrs pL r1, OpCurrHeap b r1 r2')
            | SOME r1' => (n+1, instEq, instMap, instInstrs, insert r1 r1' ochMap, ochInstrs, Move 0 [(r1, r1')])) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (LocValue r1 l) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, LocValue r1 l)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (Install p l dp dl m) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, Install p l dp dl m)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (CodeBufferWrite r1 r2) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, CodeBufferWrite r1 r2)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (DataBufferWrite r1 r2) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, DataBufferWrite r1 r2)) ∧
  (comSubExpElim n instEq instMap instInstrs ochMap ochInstrs (FFI s p1 l1 p2 l2 m) =
                (n, instEq, instMap, instInstrs, ochMap, ochInstrs, FFI s p1 l1 p2 l2 m))
End

Definition word_cse_def:
  word_cse p = let (_,_,_,_,_,_,p') = comSubExpElim 0 [] LN (empty listCmp) LN (empty listCmp) p in p'
End

(*
EVAL “word_cse (Seq (Inst (Arith (Binop Add 3 1 (Reg 2)))) (Inst (Arith (Binop Add 4 1 (Reg 2)))))”

EVAL “word_cse
    (Seq
      (Inst (Arith (Binop Add 3 1 (Reg 2))))
    (Seq
      (Inst (Arith (Binop Add 4 1 (Reg 2))))
    (Seq
      (Inst (Arith (Binop Sub 5 1 (Reg 3))))
      (Inst (Arith (Binop Sub 6 1 (Reg 4))))
    )))
”
*)

val _ = export_theory ();
