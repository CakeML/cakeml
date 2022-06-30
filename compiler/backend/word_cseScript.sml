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

val _ = new_theory "word_cse";

Type regsE = ``:num list list``
Type regsM = ``:num num_map``
Type instrsM = ``:(num list,num)map``

val _ = Datatype `knowledge = <| n:num;
                                 inst_eq:regsE;
                                 inst_map:regsM;
                                 inst_instrs:instrsM;
                                 och_map:regsM;
                                 och_instrs:instrsM;
                                 all_names:num_set |>`;

(* add a (all_names:num_set) ⇒ when seeing a new register, add it in all_names
if a register is affected and is in all_names, throw everything

!!! even registers !!!
*)

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

Definition empty_data_def:
  empty_data = <| n:=0;
                  inst_eq:=[];
                  inst_map:=LN;
                  inst_instrs:=empty listCmp;
                  och_map:=LN;
                  och_instrs:=empty listCmp;
                  all_names:=LN |>
End

Definition is_seen_def:
  is_seen r data = case sptree$lookup r data.all_names of SOME _ => T | NONE => F
End


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

(* REGISTER TRANSFORMATIONS *)

Definition canonicalRegs_def:
  canonicalRegs (data:knowledge) (r:num) =
  lookup_any r data.inst_map (lookup_any r data.och_map r)
(*
  case sptree$lookup r data.inst_map of
  | SOME r' => r'
  | NONE => case sptree$lookup r data.och_map of
            | NONE => r
            | SOME r' => r'
*)
End

Definition canonicalImmReg_def:
  canonicalImmReg data (Reg r) = Reg (canonicalRegs data r) ∧
  canonicalImmReg data (Imm w) = Imm w
End

Definition canonicalMultRegs_def:
  canonicalMultRegs (data:knowledge) (regs:num list) = MAP (canonicalRegs data) regs
End

Definition canonicalMoveRegs_def:
  canonicalMoveRegs data [] = (data, []) ∧
  canonicalMoveRegs data ((r1,r2)::tl) =
  if is_seen r1 data then empty_data, ((r1,r2)::tl) else
        case sptree$lookup r2 data.och_map of
        | SOME r2' => let och_map' = sptree$insert r1 r2' data.och_map in
                      let (data', tl') = canonicalMoveRegs (data with och_map:=och_map') tl in
                        (data', (r1,r2')::tl')
        | NONE     => let r2' = (case sptree$lookup r2 data.inst_map of SOME r => r | NONE => r2) in
                      let inst_eq' = regsUpdate r2' r1 data.inst_eq in
                      let inst_map' = sptree$insert r1 r2' data.inst_map in
                      let (data', tl') = canonicalMoveRegs (data with <| inst_eq:=inst_eq'; inst_map:=inst_map' |>) tl in
                        (data', (r1,r2')::tl')
End

(* make a lookup_data to wrap case matching
lookup_any x sp d = lookup x sp otherwise return d
To discuss*)

Definition canonicalMoveRegs2_def:
  canonicalMoveRegs2 data [] = (data, []) ∧
  canonicalMoveRegs2 data ((r1,r2)::tl) =
    if is_seen r1 data then empty_data, ((r1,r2)::tl) else
    if (EVEN r1 ∨ EVEN r2)
      then let (data', tl') = canonicalMoveRegs2 data tl in
               (data', (r1, canonicalRegs data r2)::tl')
      else
        case sptree$lookup r2 data.och_map of
        | SOME r2' => let och_map' = sptree$insert r1 r2' data.och_map in
                      let (data', tl') = canonicalMoveRegs2 (data with och_map:=och_map') tl in
                        (data', (r1,r2')::tl')
        | NONE     => let r2' = (case sptree$lookup r2 data.inst_map of SOME r => r | NONE => r2) in
                      let inst_eq' = regsUpdate r2' r1 data.inst_eq in
                      let inst_map' = sptree$insert r1 r2' data.inst_map in
                      let (data', tl') = canonicalMoveRegs2 (data with <| inst_eq:=inst_eq'; inst_map:=inst_map' |>) tl in
                        (data', (r1,r2')::tl')
End

(*
Move [(1,2);(2,3);(3,1)]
Move [(1,can 2);(2,can 3);(3,can 1)]
Knowledge : 1 ⇔ can 2 / 2 ⇔ can 3 / 3 ⇔ can 1
*)

Definition canonicalMoveRegs_aux_def:
  canonicalMoveRegs_aux data [] = data ∧
  canonicalMoveRegs_aux data ((r1,r2)::tl) =
    if EVEN r1 then canonicalMoveRegs_aux data tl
    else let och_map' = sptree$insert r1 r2 data.och_map in
         let all_names' = sptree$insert r1 () data.all_names in
         let data' = data with <| och_map := och_map'; all_names := all_names' |> in
           canonicalMoveRegs_aux data' tl
End

Definition canonicalMoveRegs3_def:
  canonicalMoveRegs3 data moves =
  let moves' = MAP (λ(a,b). (a, canonicalRegs data b)) moves in
    if EXISTS (λ(a,b). is_seen a data) moves then (empty_data, moves')
    else (canonicalMoveRegs_aux data moves', moves')
End

Definition canonicalExp_def:
  canonicalExp data (Var r) = Var (canonicalRegs data r) ∧
  canonicalExp data exp = exp
End

Definition canonicalArith_def:
  canonicalArith data (Binop op r1 r2 r3) =
    Binop op r1 (canonicalRegs data r2) (canonicalImmReg data r3) ∧
  canonicalArith data (Shift s r1 r2 n) =
    Shift s r1 (canonicalRegs data r2) n ∧
  canonicalArith data (Div r1 r2 r3) =
    Div r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalArith data (LongMul r1 r2 r3 r4) =
    LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs data r4) ∧
  canonicalArith data (LongDiv r1 r2 r3 r4 r5) =
    LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs data r4) (canonicalRegs data r5) ∧
  canonicalArith data (AddCarry r1 r2 r3 r4) =
    AddCarry r1 (canonicalRegs data r2) (canonicalRegs data r3) r4 ∧
  canonicalArith data (AddOverflow r1 r2 r3 r4) =
    AddOverflow r1 (canonicalRegs data r2) (canonicalRegs data r3) r4 ∧
  canonicalArith data (SubOverflow r1 r2 r3 r4) =
    SubOverflow r1 (canonicalRegs data r2) (canonicalRegs data r3) r4
End

Definition canonicalFp_def:
  canonicalFp data (FPLess r1 r2 r3) =
    FPLess r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPLessEqual r1 r2 r3) =
    FPLessEqual r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPEqual r1 r2 r3) =
    FPEqual r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPAbs r1 r2) =
    FPAbs r1 (canonicalRegs data r2) ∧
  canonicalFp data (FPNeg r1 r2) =
    FPNeg r1 (canonicalRegs data r2) ∧
  canonicalFp data (FPSqrt r1 r2) =
    FPSqrt r1 (canonicalRegs data r2) ∧
  canonicalFp data (FPAdd r1 r2 r3) =
    FPAdd r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPSub r1 r2 r3) =
    FPSub r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPMul r1 r2 r3) =
    FPMul r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPDiv r1 r2 r3) =
    FPDiv r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPFma r1 r2 r3) =
    FPFma r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPMov r1 r2) =
    FPMov r1 (canonicalRegs data r2) ∧
  canonicalFp data (FPMovToReg r1 r2 r3) =
    FPMovToReg r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPMovFromReg r1 r2 r3) =
    FPMovFromReg r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalFp data (FPToInt r1 r2) =
    FPToInt r1 (canonicalRegs data r2) ∧
  canonicalFp data (FPFromInt r1 r2) =
    FPFromInt r1 (canonicalRegs data r2)
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
  instToNumList (Arith a) = 3::(arithToNumList a) ∧
  instToNumList (FP fp) = 4::(fpToNumList fp)
End
(*
Theorem instToNumList_unique:
  ∀i1 i2. instToNumList i1 = instToNumList i2 ⇒ ∀n. setDest i1 n = setDest i2 n
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
(*
Theorem progToNumList_:
  ∀p1 p2. (
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

Definition word_cseInst_def:
  (word_cseInst (data:knowledge) Skip = (data, Inst Skip)) ∧
  (word_cseInst data (Const r w) =
   if is_seen r data then (empty_data, Inst (Const r w)) else
            let data = data with <| all_names:=insert r () data.all_names |> in
            let i = instToNumList (Const r w) in
            case mlmap$lookup data.inst_instrs i of
            | SOME r' => (data with <| inst_eq:=regsUpdate r' r data.inst_eq; inst_map:=insert r r' data.inst_map |>, Move 0 [(r,r')])
            | NONE    => (data with inst_instrs:=insert data.inst_instrs i r, Inst (Const r w))) ∧
  (word_cseInst data (Arith a) =
            let r = firstRegOfArith a in
            if is_seen r data then (empty_data, Inst (Arith a)) else
            let a' = canonicalArith data a in
            let i = instToNumList (Arith a') in
            case mlmap$lookup data.inst_instrs i of
            | SOME r' => (data with <| inst_eq:=regsUpdate r' r data.inst_eq; inst_map:=insert r r' data.inst_map; all_names:=insert r () data.all_names |>, Move 0 [(r,r')])
            | NONE    => (data with <| inst_instrs:=insert data.inst_instrs i r; all_names:=insert r () data.all_names |>, Inst (Arith a'))) ∧
  (word_cseInst data (Mem op r (Addr r' w)) =
                (empty_data, Inst (Mem op r (Addr r' w)))
   (* !!! meaning difference of r between Load and Store
    if sptree$lookup r data.all_names ≠ NONE then (empty_data, Inst (Mem op r (Addr r' w))) else
            (data, Inst (Mem op (canonicalRegs data r) (Addr (canonicalRegs data r') w)))
   *) ) ∧
  (word_cseInst data ((FP f):'a inst) =
            (empty_data, Inst (FP f)))
  (* Not relevant: issue with fp regs having same id as regs, possible confusion
            let f' = canonicalFp inst_map och_map f in
            let r = firstRegOfFp f' in
            let i = instToNumList ((FP f'):'a inst) in
            case mlmap$lookup inst_instrs i of
            | SOME r' => (n+1, regsUpdate r' r inst_eq, insert r r' inst_map, inst_instrs, Move 0 [(r,r')])
            | NONE    => (n, inst_eq, inst_map, insert inst_instrs i r, Inst (FP f')))
  *)
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
Definition word_cse_def:
  (word_cse (data:knowledge) (Skip) =
                (data, Skip)) ∧
  (word_cse data (Move r rs) =
            let (data', rs') = canonicalMoveRegs3 data rs in
                (data', Move r rs')) ∧
  (word_cse data (Inst i) =
            let (data', p) = word_cseInst data i in
                (data', p)) ∧
  (word_cse data (Assign r e) =
                (data, Assign r e)) ∧
  (word_cse data (Get r x) =
            if is_seen r data then (empty_data, Get r x) else (data, Get r x)) ∧
  (word_cse data (Set x e) =
            let e' = canonicalExp data e in
            if x = CurrHeap then
                (empty_data, Set x e')
            else
                (data, Set x e'))∧
  (word_cse data (Store e r) =
                (data, Store e r)) ∧
  (word_cse data (MustTerminate p) =
            let (data', p') = word_cse data p in
                (data', MustTerminate p')) ∧
  (word_cse data (Call ret dest args handler) =
                (empty_data, Call ret dest args handler)) ∧
  (word_cse data (Seq p1 p2) =
            let (data1, p1') = word_cse data p1 in
            let (data2, p2') = word_cse data1 p2 in
                (data2, Seq p1' p2')) ∧
  (word_cse data (If c r1 r2 p1 p2) =
            let r1' = canonicalRegs data r1 in
            let r2' = canonicalImmReg data r2 in
            let (data1, p1') = word_cse data p1 in
            let (data2, p2') = word_cse data p2 in
                (empty_data, If c r1' r2' p1' p2')) ∧
                (* We don't know what happen in the IF. Intersection would be the best. *)
  (word_cse data (Alloc r m) =
                (empty_data, Alloc r m)) ∧
  (word_cse data (Raise r) =
                (data, Raise r)) ∧
  (word_cse data (Return r1 r2) =
                (data, Return r1 r2)) ∧
  (word_cse data (Tick) =
                (data, Tick)) ∧
  (word_cse data ((OpCurrHeap b r1 r2):'a prog) =
    if sptree$lookup r1 data.all_names ≠ NONE then (empty_data, OpCurrHeap b r1 r2) else
            let r2' = canonicalRegs data r2 in
            let pL = progToNumList ((OpCurrHeap b r1 r2'):'a prog) in
            case lookup data.och_instrs pL of
            | NONE => (data with och_instrs:=(insert data.och_instrs pL r1), OpCurrHeap b r1 r2')
            | SOME r1' => (data with <| n:=data.n+1; och_map:=(insert r1 r1' data.och_map) |>, Move 0 [(r1, r1')])) ∧
  (word_cse data (LocValue r l) =
                if is_seen r data then (empty_data, LocValue r l) else (data, LocValue r l)) ∧
  (word_cse data (Install p l dp dl m) =
                (empty_data, Install p l dp dl m)) ∧
  (word_cse data (CodeBufferWrite r1 r2) =
                (empty_data, CodeBufferWrite r1 r2)) ∧
  (word_cse data (DataBufferWrite r1 r2) =
                (empty_data, DataBufferWrite r1 r2)) ∧
  (word_cse data (FFI s p1 l1 p2 l2 m) =
                (empty_data, FFI s p1 l1 p2 l2 m))
End


(*
EVAL “word_cse empty_data (Seq (Inst (Arith (Binop Add 3 1 (Reg 2)))) (Inst (Arith (Binop Add 4 1 (Reg 2)))))”

EVAL “word_cse empty_data
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
