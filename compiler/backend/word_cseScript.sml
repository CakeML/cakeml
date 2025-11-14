(*
  Defines a common sub-expression elimination pass on a wordLang program.
  This pass is to run immediately after the SSA-like renaming.
*)
Theory word_cse
Ancestors
  wordLang words bool balanced_map sptree
Libs
  preamble



(* DATA

  The to_canonical field maps register name r to a canonical name c
  such that registers r and c hold the same value.

  The to_latest field maps canonical name to latest register name
  that has that value. The latest name should always be emitted to
  generate code with as short live ranges as possible (helps register
  allocation).

  The gets_mem field maps store names to canonical registers.

  The instrs_mem field maps instructions to canonical register holding
  the value of that this instruction produces. Note that instructions
  are stored with canonical names only.

  Conventions:

   - The domain of to_canonical include all names that are mentioned
     anywhere in the data state.

   - The data must be reset to empty, in case we encounter an
     assignment to a name that's in the main of to_canonical, because
     such assignments can make the optimisers state out-of-date.

   - All names in the domain and range of to_canonical must be ODD, so
     that pre-register-allocated registers aren't touched.

*)

Datatype:
  knowledge =
  <|
    to_canonical : num num_map ;
    to_latest    : num num_map ;
    gets_mem     : (store_name, num) alist ;
    instrs_mem   : (num list, num) balanced_map
  |>
End

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
  empty_data = <| to_canonical := LN ;
                  to_latest    := LN ;
                  gets_mem     := [] ;
                  instrs_mem   := empty |>
End

(* Whether we're allowed to keep the data
  after writing to this register *)
Definition keep_data_def:
  keep_data canon (write_to_reg:num) =
    IS_NONE (lookup write_to_reg canon)
End

Definition invalidate_data_def:
  invalidate_data data (write_to_reg:num) =
  if keep_data data.to_canonical write_to_reg
  then data
  else empty_data
End

(* REGISTER TRANSFORMATIONS *)

Definition canonicalRegs_def:
  canonicalRegs (data:knowledge) (r:num) =
  lookup_any r data.to_canonical r
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

Definition canonicalMoveRegs_def:
  canonicalMoveRegs data moves =
  if EVERY (keep_data data.to_canonical) (MAP FST moves)
  then
    let xs = FILTER (λ(a,b). ¬EVEN a ∧ ¬EVEN b) moves in
    let ys = MAP (λ(a,b). (a, canonicalRegs data b)) xs in
    let to_c = map_insert ys data.to_canonical in
    let zs = MAP (λ(a,b). (b,a)) ys in
    let to_l = map_insert ys data.to_latest in
      data with <| to_canonical := to_c ; to_latest := to_l |>
  else empty_data
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
  memOpToNum Load32 = 44 ∧
  memOpToNum Store = 23 ∧
  memOpToNum Store8 = 24 ∧
  memOpToNum Store34 = 45
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

Definition add_to_data_aux_def:
  add_to_data_aux data r i x =
    case balanced_map$lookup listCmp i data.instrs_mem of
    | SOME r' => let k = lookup_any r' data.to_latest r' in
                   if EVEN r then
                     (data, Move 0 [(r,k)])
                   else
                     (data with <| to_canonical := insert r r' data.to_canonical;
                                   to_latest := insert r' r data.to_latest |>, Move 0 [(r,k)])
    | NONE    => if EVEN r then
                   (data, x)
                 else
                   (data with <| instrs_mem := insert listCmp i r data.instrs_mem;
                                 to_canonical := insert r r data.to_canonical;
                                 to_latest := insert r r data.to_latest |>, x)
End

Definition add_to_data_def:
  add_to_data data r adjusted x =
    let i = instToNumList adjusted in
      add_to_data_aux data r i (Inst x)
End

Definition is_store_def:
  is_store Load = F ∧
  is_store Load8 = F ∧
  is_store Load32 = F ∧
  is_store Store = T ∧
  is_store Store8 = T ∧
  is_store Store32 = T
End

Definition is_store_def:
  (is_store Load = F) ∧
  (is_store Load8 = F) ∧
  (is_store Load32 = F) ∧
  (is_store Store = T) ∧
  (is_store Store8 = T) ∧
  (is_store Store32 = T)
End

Definition word_cseInst_def:
  (word_cseInst (data:knowledge) Skip = (data, Inst Skip)) ∧
  (word_cseInst data (Const r w) =
     let data = invalidate_data data r in
       if EVEN r then (data,Inst (Const r w)) else
         add_to_data data r (Const r w) (Const r w)) ∧
  (word_cseInst data (Arith a) =
     let r = firstRegOfArith a in
     let data = invalidate_data data r in
     let a' = canonicalArith data a in
       if can_mem_arith a' then
         add_to_data data r (Arith a') (Arith a)
       else
         (data, Inst (Arith a))) ∧
  (word_cseInst data (Mem op r ad) =
     let data = (if is_store op then data else invalidate_data data r) in
       (data, Inst (Mem op r ad))) ∧
  (word_cseInst data (FP fp :'a inst) =
     (invalidate_data data (firstRegOfFp fp), Inst (FP fp)))
End

Definition dest_Var_def:
  dest_Var (Var v :'a wordLang$exp) = SOME v ∧
  dest_Var _ = NONE
End

(*
Principle:
  We keep track of a map containing all instructions already dealt with,
    and we explore the program to find instructions matching one in the map.
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
  (word_cse data (Move r rs) =
    let data' = canonicalMoveRegs data rs in
      (data', Move r rs)) ∧
  (word_cse data (Inst i) =
    let (data', p) = word_cseInst data i in
      (data', p)) ∧
  (word_cse data (Get r x) =
    let data = invalidate_data data r in
      case ALOOKUP data.gets_mem x of
      | NONE => if EVEN r then (data,Get r x) else
                  (data with <| gets_mem := ((x,r)::data.gets_mem);
                                to_canonical := insert r r data.to_canonical;
                                to_latest := insert r r data.to_latest|>,
                   Get r x)
      | SOME k => (data with <| to_latest := insert k r data.to_latest |>,
                   Move 1 [(r,lookup_any k data.to_latest k)])) ∧
  (word_cse data (Set x e) =
    if x = CurrHeap then
      (empty_data, Set x e)
    else
      let new_gets_mem = FILTER (λ(m,n). m ≠ x) data.gets_mem in
        case dest_Var e of
        | NONE => (data with gets_mem := new_gets_mem, Set x e)
        | SOME v => (data with
                          <| gets_mem := (x,v)::new_gets_mem ;
                             to_canonical := insert v (lookup_any v data.to_canonical v)
                                                    data.to_canonical |>,
                     Set x e)) ∧
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
    let (data1, p1') = word_cse data p1 in
    let (data2, p2') = word_cse data p2 in
      (empty_data, If c r1 r2 p1' p2')) ∧
  (word_cse data ((OpCurrHeap b r1 r2):'a prog) =
    let data = invalidate_data data r1 in
      if EVEN r2 then (data,OpCurrHeap b r1 r2) else
        let r2' = canonicalRegs' r1 data r2 in
        let pL = OpCurrHeapToNumList b r2' in
          add_to_data_aux data r1 pL (OpCurrHeap b r1 r2)) ∧
  (word_cse data (LocValue r l) = (invalidate_data data r, LocValue r l)) ∧
  (word_cse data (Skip) = (data, Skip)) ∧
  (word_cse data (Store e r) = (data, Store e r)) ∧
  (word_cse data (Assign r e) = (data, Assign r e)) ∧
  (word_cse data (Raise r) = (data, Raise r)) ∧
  (word_cse data (Return r1 r2) = (data, Return r1 r2)) ∧
  (word_cse data (Tick) = (data, Tick)) ∧
  (word_cse data other = (empty_data, other))
End

Definition word_common_subexp_elim_def:
  word_common_subexp_elim prog =
    let (_,new_prog) = word_cse empty_data prog in
      new_prog
End

(* tests *)

Definition Seqs_def:
  (Seqs [] = wordLang$Skip) /\
  (Seqs [x] = x) /\
  (Seqs (x::y::xs) = Seq x (Seqs (y::xs)))
End

Triviality test_latest_name_used:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (Binop Add 11 1 (Reg 1)));
          Inst (Arith (Binop Add 13 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Move 0 [(9,7)];
          Move 0 [(11,9)];
          Move 0 [(13,11)]]
Proof
  EVAL_TAC
QED

Triviality test_get_set:
  word_common_subexp_elim $
    Seqs [Get 1 NextFree;
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Set NextFree (Var 7);
          Get 9 NextFree;
          Inst (Arith (Binop Add 11 1 (Reg 1)));
          Get 33 NextFree;
          Get 35 NextFree;
          Get 37 NextFree]
  =
    Seqs [Get 1 NextFree;
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Set NextFree (Var 7);
          Move 1 [(9,7)];
          Move 0 [(11,9)];
          Move 1 [(33,11)];
          Move 1 [(35,33)];
          Move 1 [(37,35)]]
Proof
  EVAL_TAC
QED

Triviality test_pattern_match_and_cons:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Shift Lsr 301 297 9));
          OpCurrHeap Add 305 301;
          Inst (Mem Load 309 (Addr 305 8w));
          Move 0 [(313,297)];
          Inst (Arith (Shift Lsr 317 313 9));
          OpCurrHeap Add 321 317;
          Inst (Mem Load 325 (Addr 321 16w));
          Move 0 [(329,313)];
          Inst (Arith (Shift Lsr 333 329 9));
          OpCurrHeap Add 337 333;
          Inst (Mem Load 341 (Addr 337 24w));
          Get 345 NextFree;
          Inst (Const 349 0x200000003w);
          Move 0 [(353,345)];
          Inst (Mem Store 349 (Addr 353 0w));
          Move 0 [(357,353)];
          Inst (Mem Store 325 (Addr 357 8w));
          Move 0 [(361,357)];
          Inst (Mem Store 341 (Addr 361 16w));
          Move 0 [(365,361)];
          OpCurrHeap Sub 369 365;
          Inst (Arith (Shift Lsl 373 369 9));
          Inst (Arith (Binop Or 377 373 (Imm 5w)));
          Move 0 [(381,365)];
          Inst (Arith (Binop Add 385 381 (Imm 24w)));
          Set NextFree (Var 385);
          Get 389 NextFree;
          Inst (Const 393 0x200000003w);
          Move 0 [(397,389)];
          Inst (Mem Store 393 (Addr 397 0w));
          Move 0 [(401,397)];
          Inst (Mem Store 309 (Addr 401 8w));
          Move 0 [(405,401)];
          Inst (Mem Store 377 (Addr 405 16w));
          Move 0 [(409,405)];
          OpCurrHeap Sub 413 409;
          Inst (Arith (Shift Lsl 417 413 9));
          Inst (Arith (Binop Or 421 417 (Imm 5w)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24w)));
          Set NextFree (Var 429);
          Move 0 [(2,421)]; Return 273 2]
  =
    Seqs [Inst (Arith (Shift Lsr 301 297 9));
          OpCurrHeap Add 305 301;
          Inst (Mem Load 309 (Addr 305 8w));
          Move 0 [(313,297)];
          Move 0 [(317,301)];
          Move 0 [(321,305)];
          Inst (Mem Load 325 (Addr 321 16w));
          Move 0 [(329,313)];
          Move 0 [(333,317)];
          Move 0 [(337,321)];
          Inst (Mem Load 341 (Addr 337 24w));
          Get 345 NextFree;
          Inst (Const 349 0x200000003w);
          Move 0 [(353,345)];
          Inst (Mem Store 349 (Addr 353 0w));
          Move 0 [(357,353)];
          Inst (Mem Store 325 (Addr 357 8w));
          Move 0 [(361,357)];
          Inst (Mem Store 341 (Addr 361 16w));
          Move 0 [(365,361)];
          OpCurrHeap Sub 369 365;
          Inst (Arith (Shift Lsl 373 369 9));
          Inst (Arith (Binop Or 377 373 (Imm 5w)));
          Move 0 [(381,365)];
          Inst (Arith (Binop Add 385 381 (Imm 24w)));
          Set NextFree (Var 385);
          Move 1 [(389,385)];
          Move 0 [(393,349)];
          Move 0 [(397,389)];
          Inst (Mem Store 393 (Addr 397 0w));
          Move 0 [(401,397)];
          Inst (Mem Store 309 (Addr 401 8w));
          Move 0 [(405,401)];
          Inst (Mem Store 377 (Addr 405 16w));
          Move 0 [(409,405)];
          OpCurrHeap Sub 413 409;
          Inst (Arith (Shift Lsl 417 413 9));
          Inst (Arith (Binop Or 421 417 (Imm 5w)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24w)));
          Set NextFree (Var 429);
          Move 0 [(2,421)];
          Return 273 2]
Proof
  EVAL_TAC
QED

val _ = Theory.delete_const "Seqs";
