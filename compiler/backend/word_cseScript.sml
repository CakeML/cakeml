(*
  Defines a common sub-expression elimination pass on a wordLang program.
  This pass is to run immeidately atfer the SSA-like renaming.
*)

open preamble wordLangTheory wordsTheory boolTheory mlmapTheory sptreeTheory

val _ = new_theory "word_cse";

Type regsE = ``:num list list``
Type regsM = ``:num num_map``
Type instrsM = ``:(num list,num)map``

val _ = Datatype `knowledge = <| eq:regsE;
                                 map:regsM;
                                 instrs:instrsM;
                                 all_names:num_set |>`;

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
  empty_data = <| eq:=[];
                  map:=LN;
                  instrs:=empty listCmp;
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
   (if listLookup r hd
      then (l ++ hd)::tl
      else hd::(regsUpdate1Aux r l tl)) ∧
  regsUpdate1Aux r l _ = []
End

Definition regsUpdate1_def:
  regsUpdate1 r1 r2 (hd::tl) =
   (if listLookup r1 hd
      then if listLookup r2 hd
        then (hd::tl)
        else regsUpdate1Aux r2 hd tl
      else if listLookup r2 hd
        then regsUpdate1Aux r1 hd tl
        else hd::(regsUpdate1 r1 r2 tl)) ∧
  regsUpdate1 r1 r2 _ = []
End

Definition regsUpdate2_def:
  regsUpdate2 r1 r2 ((hd::tl)::tl') =
   (if listLookup r1 (hd::tl)
      then (hd::r2::tl)::tl'
      else (hd::tl)::(regsUpdate2 r1 r2 tl')) ∧
  regsUpdate2 r1 r2 _ = []
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
  lookup_any r data.map r
End

Definition canonicalRegs'_def:
  canonicalRegs' avoid (data:knowledge) (r:num) =
    let n = canonicalRegs (data:knowledge) (r:num) in
      if n = avoid then r else n
End

Definition canonicalImmReg_def:
  canonicalImmReg data (Reg r) = Reg (canonicalRegs data r) ∧
  canonicalImmReg data (Imm w) = Imm w
End

Definition canonicalImmReg'_def:
  canonicalImmReg' avoid data (Reg r) = Reg (canonicalRegs' avoid data r) ∧
  canonicalImmReg' avoid data (Imm w) = Imm w
End

Definition canonicalMultRegs_def:
  canonicalMultRegs (data:knowledge) (regs:num list) = MAP (canonicalRegs data) regs
End

Definition map_insert_def:
  map_insert [] m = m ∧
  map_insert ((x,y)::xs) m =
    insert x y (map_insert xs m)
End

Definition canonicalMoveRegs3_def:
  canonicalMoveRegs3 data moves =
  let moves' = MAP (λ(a,b). (a, canonicalRegs data b)) moves in
    if EXISTS (λ(a,b). is_seen a data) moves ∨
       ¬EVERY (λ(a,b). EVEN b ∨ is_seen b data) moves
    then (empty_data, moves')
    else
      let xs = FILTER (λ(a,b).  ¬EVEN a ∧ ¬EVEN b) moves' in
      let a_n = list_insert (FILTER ODD (MAP FST moves)) data.all_names in
      let m = map_insert xs data.map in
        (data with <| all_names := a_n; map := m |>, moves')
End

Definition canonicalExp_def:
  canonicalExp data (Var r) = Var (canonicalRegs data r) ∧
  canonicalExp data exp = exp
End

Definition canonicalArith_def:
  canonicalArith data (Binop op r1 r2 r3) =
    Binop op r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data r3) ∧
  canonicalArith data (Shift s r1 r2 n) =
    Shift s r1 (canonicalRegs' r1 data r2) n ∧
  canonicalArith data (Div r1 r2 r3) =
    Div r1 (canonicalRegs data r2) (canonicalRegs data r3) ∧
  canonicalArith data (LongMul r1 r2 r3 r4) =
    LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs data r4) ∧
  canonicalArith data (LongDiv r1 r2 r3 r4 r5) =
    LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs data r4) (canonicalRegs data r5) ∧
  canonicalArith data (AddCarry r1 r2 r3 r4) =
    AddCarry r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4 ∧
  canonicalArith data (AddOverflow r1 r2 r3 r4) =
    AddOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4 ∧
  canonicalArith data (SubOverflow r1 r2 r3 r4) =
    SubOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4
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

Definition shiftToNum_def:
  shiftToNum Lsl = (40:num) ∧
  shiftToNum Lsr = 41 ∧
  shiftToNum Asr = 42 ∧
  shiftToNum Ror = 43
End

Definition arithOpToNum_def:
  arithOpToNum Add = (35:num) ∧
  arithOpToNum Sub = 36 ∧
  arithOpToNum And = 37 ∧
  arithOpToNum Or = 38 ∧
  arithOpToNum Xor = 39
End

Definition regImmToNumList_def:
  regImmToNumList (Reg r) = [33; r+100] ∧
  regImmToNumList (Imm w) = [34; wordToNum w]
End

Definition arithToNumList_def:
  arithToNumList (Binop op r1 r2 ri) = [25; arithOpToNum op; r2+100] ++ regImmToNumList ri ∧
  arithToNumList (LongMul r1 r2 r3 r4) = [26; r3+100; r4+100] ∧
  arithToNumList (LongDiv r1 r2 r3 r4 r5) = [27; r3+100; r4+100; r5+100] ∧
  arithToNumList (Shift s r1 r2 n) = [28; shiftToNum s; r2+100; n] ∧
  arithToNumList (Div r1 r2 r3) = [29; r2+100; r3+100] ∧
  arithToNumList (AddCarry r1 r2 r3 r4) = [30; r2+100; r3+100] ∧
  arithToNumList (AddOverflow r1 r2 r3 r4) = [31; r2+100; r3+100] ∧
  arithToNumList (SubOverflow r1 r2 r3 r4) = [32; r2+100; r3+100]
End

Definition memOpToNum_def:
  memOpToNum Load = (21:num) ∧
  memOpToNum Load8 = 22 ∧
  memOpToNum Store = 23 ∧
  memOpToNum Store8 = 24
End

Definition fpToNumList_def:
  fpToNumList (FPLess r1 r2 r3) = [5; r2+100; r3+100] ∧
  fpToNumList (FPLessEqual r1 r2 r3) = [6; r2+100; r3+100] ∧
  fpToNumList (FPEqual r1 r2 r3) = [7; r2+100; r3+100] ∧
  fpToNumList (FPAbs r1 r2) = [8; r2+100] ∧
  fpToNumList (FPNeg r1 r2) = [9; r2+100] ∧
  fpToNumList (FPSqrt r1 r2) = [10; r2+100] ∧
  fpToNumList (FPAdd r1 r2 r3) = [11; r2+100; r3+100] ∧
  fpToNumList (FPSub r1 r2 r3) = [12; r2+100; r3+100] ∧
  fpToNumList (FPMul r1 r2 r3) = [13; r2+100; r3+100] ∧
  fpToNumList (FPDiv r1 r2 r3) = [14; r2+100; r3+100] ∧
  fpToNumList (FPFma r1 r2 r3) = [15; r1+100; r2+100; r3+100] ∧ (* List never matched again *)
  fpToNumList (FPMov r1 r2) = [16; r2+100] ∧
  fpToNumList (FPMovToReg r1 r2 r3) = [17; r2+100; r3+100] ∧
  fpToNumList (FPMovFromReg r1 r2 r3) = [18; r2+100; r3+100] ∧
  fpToNumList (FPToInt r1 r2) = [19; r2+100] ∧
  fpToNumList (FPFromInt r1 r2) = [20; r2+100]
End

Definition instToNumList_def:
  instToNumList (Const r w) = [2;wordToNum w] ∧
  instToNumList (Arith a) = 3::(arithToNumList a) ∧
  instToNumList (FP fp) = 4::(fpToNumList fp) ∧
  instToNumList _ = [1]
End

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an instruction.
Numbers above 99 corresponds to a register or a word value.
*)
Definition OpCurrHeapToNumList_def:
  OpCurrHeapToNumList op r2 = [0; arithOpToNum op; r2+100]
End

(* WORD CSE FUNCTIONS *)

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

Definition are_reads_seen_def:
  are_reads_seen (Binop _ _ r1 (Reg r2)) data = (is_seen r1 data ∧ is_seen r2 data) ∧
  are_reads_seen (Binop _ _ r1 (Imm _)) data = (is_seen r1 data) ∧
  are_reads_seen (Div _ r1 r2) data = (is_seen r1 data ∧ is_seen r2 data) ∧
  are_reads_seen (Shift _ _ r _) data = is_seen r data ∧
  are_reads_seen _ data = T
End

Definition add_to_data_aux_def:
  add_to_data_aux data r i x =
    case mlmap$lookup data.instrs i of
    | SOME r' => if EVEN r then
                   (data, Move 0 [(r,r')])
                 else
                   (data with <| eq:=regsUpdate r' r data.eq; map:=insert r r' data.map; all_names:=insert r () data.all_names |>, Move 0 [(r,r')])
    | NONE    => if EVEN r then
                   (data, x)
                 else
                   (data with <| instrs:=insert data.instrs i r; all_names:=insert r () data.all_names |>, x)
End

Definition add_to_data_def:
  add_to_data data r x =
  let i = instToNumList x in
    add_to_data_aux data r i (Inst x)
End

Definition is_store_def:
  is_store Load = F ∧
  is_store Load8 = F ∧
  is_store Store = T ∧
  is_store Store8 = T
End

Definition is_complex_def:
  is_complex (Binop _ _ _ _) = F ∧
  is_complex (Div _ _ _) = F ∧
  is_complex (Shift _ _ _ _) = F ∧
  is_complex _ = T
End

Definition word_cseInst_def:
  (word_cseInst (data:knowledge) Skip = (data, Inst Skip)) ∧
  (word_cseInst data (Const r w) =
   if is_seen r data then (empty_data with all_names:=data.all_names, Inst (Const r w)) else
       add_to_data data r (Const r w)) ∧
  (word_cseInst data (Arith a) =
   let r = firstRegOfArith a in
     let a' = canonicalArith data a in
       if is_seen r data ∨ is_complex a' ∨ ¬are_reads_seen a' data then
         (empty_data with all_names:=data.all_names, Inst (Arith a))
       else
         add_to_data data r (Arith a')) ∧
  (word_cseInst data (Mem op r (Addr r' w)) =
   if is_store op then
     (data, Inst (Mem op (canonicalRegs data r) (Addr (canonicalRegs data r') w)))
   else
     if is_seen r data then
       (empty_data with all_names:=data.all_names, Inst (Mem op r (Addr (canonicalRegs data r') w)))
     else
       (data, Inst (Mem op r (Addr (canonicalRegs data r') w))) ) ∧
  (word_cseInst data (x:'a inst) =
     (empty_data with all_names:=data.all_names, Inst x))
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
            if is_seen r data then (empty_data with all_names:=data.all_names, Get r x) else (data, Get r x)) ∧
  (word_cse data (Set x e) =
            let e' = canonicalExp data e in
            if x = CurrHeap then
                (empty_data with all_names:=data.all_names, Set x e')
            else
                (data, Set x e'))∧
  (word_cse data (Store e r) =
                (data, Store e r)) ∧
  (word_cse data (MustTerminate p) =
            let (data', p') = word_cse data p in
                (data', MustTerminate p')) ∧
  (word_cse data (Call ret dest args handler) =
            case ret of
            | NONE => (empty_data, Call ret dest args handler)
            | SOME (ret_reg, cut_set, p, l1, k) =>
                      (empty_data with all_names:=inter data.all_names cut_set, Call ret dest args handler)) ∧
  (word_cse data (Seq p1 p2) =
            let (data1, p1') = word_cse data p1 in
            let (data2, p2') = word_cse data1 p2 in
                (data2, Seq p1' p2')) ∧
  (word_cse data (If c r1 r2 p1 p2) =
            let r1' = canonicalRegs data r1 in
            let r2' = canonicalImmReg data r2 in
            let (data1, p1') = word_cse data p1 in
            let (data2, p2') = word_cse data p2 in
                (empty_data with all_names:=inter data1.all_names data2.all_names, If c r1' r2' p1' p2')) ∧
                (* We don't know what happen in the IF. Intersection would be the best. *)
  (word_cse data (Alloc r m) =
                (empty_data with all_names:=data.all_names, Alloc r m)) ∧
  (word_cse data (Raise r) =
                (data, Raise r)) ∧
  (word_cse data (Return r1 r2) =
                (data, Return r1 r2)) ∧
  (word_cse data (Tick) =
                (data, Tick)) ∧
  (word_cse data ((OpCurrHeap b r1 r2):'a prog) =
    if is_seen r1 data ∨ ¬is_seen r2 data then (empty_data with all_names:=data.all_names, OpCurrHeap b r1 r2) else
      let r2' = canonicalRegs' r1 data r2 in
        let pL = OpCurrHeapToNumList b r2' in
          add_to_data_aux data r1 pL (OpCurrHeap b r1 r2')) ∧
  (word_cse data (LocValue r l) =
                if is_seen r data then (empty_data with all_names:=data.all_names, LocValue r l) else (data, LocValue r l)) ∧
  (word_cse data (Install p l dp dl m) =
                (empty_data with all_names:=data.all_names, Install p l dp dl m)) ∧
  (word_cse data (CodeBufferWrite r1 r2) =
                (empty_data with all_names:=data.all_names, CodeBufferWrite r1 r2)) ∧
  (word_cse data (DataBufferWrite r1 r2) =
                (empty_data with all_names:=data.all_names, DataBufferWrite r1 r2)) ∧
  (word_cse data (FFI s p1 l1 p2 l2 m) =
                (empty_data with all_names:=data.all_names, FFI s p1 l1 p2 l2 m)) ∧
  (word_cse data (StoreConsts r1 r2 r3 r4 payload) =
                (empty_data with all_names:=data.all_names,
                 StoreConsts r1 r2 r3 r4 payload))
End

Definition word_common_subexp_elim_def:
  word_common_subexp_elim prog =
    let (_,new_prog) = word_cse empty_data prog in
      new_prog
End

val _ = export_theory ();
