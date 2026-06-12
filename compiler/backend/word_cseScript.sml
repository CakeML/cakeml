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

  The loads_mem field maps load instructions (keyed by width, canonical
  address register and offset) to the canonical register holding the
  value last loaded from that address. It is kept separate from
  instrs_mem because memory writes must invalidate exactly the load
  facts: a store clears loads_mem and leaves all register-only facts
  intact.

  Conventions:

   - The domain of to_canonical include all names that are mentioned
     anywhere in the data state.

   - The data must be reset to empty, in case we encounter an
     assignment to a name that's in the main of to_canonical, because
     such assignments can make the optimisers state out-of-date.

   - All names in the domain and range of to_canonical must be ODD, so
     that pre-register-allocated registers aren't touched.

   - Every register mentioned by a stored fact — including registers an
     instruction only reads — must be in the domain of to_canonical, so
     that a later write to it resets the data. Reads are entered as
     self-mappings (registered) when a fact is stored.

*)

Datatype:
  knowledge =
  <|
    to_canonical : num num_map ;
    to_latest    : num num_map ;
    gets_mem     : (store_name, num) alist ;
    instrs_mem   : (num list, num) balanced_map ;
    loads_mem    : (num list, num) balanced_map
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
                  instrs_mem   := empty ;
                  loads_mem    := empty |>
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

(* Invalidate after writing each register in a list (e.g. multi-output
  instructions); empties the data if any of them is tracked. *)
Definition invalidate_regs_def:
  invalidate_regs data [] = data ∧
  invalidate_regs data (r::rs) = invalidate_regs (invalidate_data data r) rs
End

(* Enter an odd register that a stored fact reads into the tracked set as a
  self-mapping, so that a later write to it resets the data. Registers
  already tracked, and pre-allocated (EVEN) registers, are left alone. *)
Definition register_read_def:
  register_read data (r:num) =
    if ¬EVEN r ∧ keep_data data.to_canonical r
    then data with to_canonical := insert r r data.to_canonical
    else data
End

Definition register_reads_def:
  register_reads data [] = data ∧
  register_reads data (r::rs) = register_reads (register_read data r) rs
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
  (* Register the sources first: a register that is both a source and a
     destination is then tracked and fails the keep_data check below, so
     no equivalence is recorded across a self-interfering parallel move. *)
  let data = register_reads data (MAP SND moves) in
  if EVERY (keep_data data.to_canonical) (MAP FST moves)
  then
    let xs = FILTER (λ(a,b). ¬EVEN a ∧ ¬EVEN b) moves in
    let ys = MAP (λ(a,b). (a, canonicalRegs data b)) xs in
    let to_c = map_insert ys data.to_canonical in
    let zs = MAP (λ(a,b). (b,a)) ys in
    let to_l = map_insert zs data.to_latest in
      data with <| to_canonical := to_c ; to_latest := to_l |>
  else empty_data
End

Definition canonicalArith_def:
  canonicalArith data (Binop op r1 r2 r3) =
    Binop op r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data r3) ∧
  canonicalArith data (Shift s r1 r2 ri) =
    Shift s r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data ri) ∧
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
  arithToNumList (Shift s r1 r2 ri) = [28; shiftToNum s; r2+100] ++ regImmToNumList ri ∧
  arithToNumList (Div r1 r2 r3) = [29; r2+100; r3+100] ∧
  arithToNumList (AddCarry r1 r2 r3 r4) = [30; r2+100; r3+100] ∧
  arithToNumList (AddOverflow r1 r2 r3 r4) = [31; r2+100; r3+100] ∧
  arithToNumList (SubOverflow r1 r2 r3 r4) = [32; r2+100; r3+100]
End

Definition memOpToNum_def:
  memOpToNum Load = (21:num) ∧
  memOpToNum Load8 = 22 ∧
  memOpToNum Load16 = 46 ∧
  memOpToNum Load32 = 44 ∧
  memOpToNum Store = 23 ∧
  memOpToNum Store8 = 47 ∧
  memOpToNum Store16 = 24 ∧
  memOpToNum Store32 = 45
End

(* Key for a load fact (kept in the separate loads_mem map): the memop head
   distinguishes the load widths; the address register is stored
   canonically. *)
Definition loadToNumList_def:
  loadToNumList op (a:num) ofs = [memOpToNum op; a+100; wordToNum ofs]
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

(* All registers an arith instruction writes (multi-output ops write two), so
  that every written register is invalidated. *)
Definition arithWrites_def:
  arithWrites (Binop _ r _ _) = [r] ∧
  arithWrites (Shift _ r _ _) = [r] ∧
  arithWrites (Div r _ _) = [r] ∧
  arithWrites (LongMul r1 r2 _ _) = [r1; r2] ∧
  arithWrites (LongDiv r1 r2 _ _ _) = [r1; r2] ∧
  arithWrites (AddCarry r1 _ _ r4) = [r1; r4] ∧
  arithWrites (AddOverflow r1 _ _ r4) = [r1; r4] ∧
  arithWrites (SubOverflow r1 _ _ r4) = [r1; r4]
End

(* All registers an arith instruction reads (AddCarry also reads the
  carry-flag register r4). *)
Definition arithReads_def:
  arithReads (Binop _ _ r2 (Reg r3)) = [r2; r3] ∧
  arithReads (Binop _ _ r2 (Imm _)) = [r2] ∧
  arithReads (Shift _ _ r2 (Reg r3)) = [r2; r3] ∧
  arithReads (Shift _ _ r2 (Imm _)) = [r2] ∧
  arithReads (Div _ r2 r3) = [r2; r3] ∧
  arithReads (LongMul _ _ r3 r4) = [r3; r4] ∧
  arithReads (LongDiv _ _ r3 r4 r5) = [r3; r4; r5] ∧
  arithReads (AddCarry _ r2 r3 r4) = [r2; r3; r4] ∧
  arithReads (AddOverflow _ r2 r3 _) = [r2; r3] ∧
  arithReads (SubOverflow _ r2 r3 _) = [r2; r3]
End

(* The general-purpose registers an fp instruction writes. Most write only
  fp-registers (disjoint from the tracked state), hence []. *)
Definition fpWrites_def:
  fpWrites (FPLess r _ _) = [r] ∧
  fpWrites (FPLessEqual r _ _) = [r] ∧
  fpWrites (FPEqual r _ _) = [r] ∧
  fpWrites (FPMovToReg r1 r2 _) = [r1; r2] ∧
  fpWrites _ = []
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

(* As add_to_data_aux, but for the load-fact map. *)
Definition add_to_load_aux_def:
  add_to_load_aux data r i x =
    case balanced_map$lookup listCmp i data.loads_mem of
    | SOME r' => let k = lookup_any r' data.to_latest r' in
                   if EVEN r then
                     (data, Move 0 [(r,k)])
                   else
                     (data with <| to_canonical := insert r r' data.to_canonical;
                                   to_latest := insert r' r data.to_latest |>, Move 0 [(r,k)])
    | NONE    => if EVEN r then
                   (data, x)
                 else
                   (data with <| loads_mem := insert listCmp i r data.loads_mem;
                                 to_canonical := insert r r data.to_canonical;
                                 to_latest := insert r r data.to_latest |>, x)
End

Definition can_mem_arith_def:
  can_mem_arith (Binop _ _ r1 (Reg r2)) = (ODD r1 ∧ ODD r2) ∧
  can_mem_arith (Binop _ _ r1 (Imm _)) = ODD r1 ∧
  can_mem_arith (Div _ r1 r2) = (ODD r1 ∧ ODD r2) ∧
  can_mem_arith (Shift _ _ r (Imm _)) = ODD r ∧
  can_mem_arith _ = F
End

Definition is_store_def:
  (is_store Load = F) ∧
  (is_store Load8 = F) ∧
  (is_store Load16 = F) ∧
  (is_store Load32 = F) ∧
  (is_store Store = T) ∧
  (is_store Store8 = T) ∧
  (is_store Store16 = T) ∧
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
     let data = invalidate_regs data (arithWrites a) in
     let a' = canonicalArith data a in
     let rds = arithReads a' in
       (* A fact whose reads include the written register would not describe
          the post-state, so it is not stored. *)
       if can_mem_arith a' ∧ ¬MEM r rds then
         add_to_data (register_reads data rds) r (Arith a') (Arith a)
       else
         (data, Inst (Arith a))) ∧
  (word_cseInst data (Mem op r (Addr a ofs)) =
     if is_store op then
       (* A store writes no register, but it writes memory: all load facts
          are invalidated. Register-only facts survive. *)
       (data with loads_mem := empty, Inst (Mem op r (Addr a ofs)))
     else
       let data = invalidate_data data r in
         (* A load fact whose address is the written register (a = r) would
            not describe the post-state; EVEN names are never tracked. *)
         if EVEN r ∨ EVEN a ∨ a = r then (data, Inst (Mem op r (Addr a ofs)))
         else
           let a' = canonicalRegs' r data a in
             add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
                             (Inst (Mem op r (Addr a ofs)))) ∧
  (word_cseInst data (FP fp :'a inst) =
     (invalidate_regs data (fpWrites fp), Inst (FP fp)))
End

Definition dest_Var_def:
  dest_Var (Var v :'a wordLang$exp) = SOME v ∧
  dest_Var _ = NONE
End

(* IF-JOIN MERGE

  Knowledge valid after an If is the set of facts that hold after either
  branch: exactly the entries present with equal value on both sides. *)

(* First-order equality-intersection for the instruction map (written
  without higher-order functions so it can be translated by cv_trans). *)
Definition bm_inter_eq_acc_def:
  bm_inter_eq_acc m2 Tip acc = acc ∧
  bm_inter_eq_acc m2 (Bin n k v l r) acc =
    bm_inter_eq_acc m2 l
      (bm_inter_eq_acc m2 r
        (if balanced_map$lookup listCmp k m2 = SOME v
         then balanced_map$insert listCmp k v acc
         else acc))
End

Definition bm_inter_eq_def:
  bm_inter_eq m1 m2 = bm_inter_eq_acc m2 m1 empty
End

(* to_latest is reset: its entries must stay within the domain of the merged
  to_canonical, and they regenerate as soon as new facts are stored. *)
Definition merge_data_def:
  merge_data d1 d2 =
    <| to_canonical := inter_eq d1.to_canonical d2.to_canonical ;
       to_latest    := LN ;
       gets_mem     := FILTER (λ(x,v). ALOOKUP d2.gets_mem x = SOME v) d1.gets_mem ;
       instrs_mem   := bm_inter_eq d1.instrs_mem d2.instrs_mem ;
       loads_mem    := bm_inter_eq d1.loads_mem d2.loads_mem |>
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
      | SOME k => if EVEN r then (data, Move 1 [(r,lookup_any k data.to_latest k)]) else
                  (data with <| to_canonical := insert r k data.to_canonical;
                                to_latest := insert k r data.to_latest |>,
                   Move 1 [(r,lookup_any k data.to_latest k)])) ∧
  (word_cse data (Set x e) =
    if x = CurrHeap then
      (empty_data, Set x e)
    else
      let new_gets_mem = FILTER (λ(m,n). m ≠ x) data.gets_mem in
        case dest_Var e of
        | NONE => (data with gets_mem := new_gets_mem, Set x e)
        (* Only ODD source registers are tracked; storing a fact about a
           pre-allocated (EVEN) register would later reset all knowledge on
           any write to it, for a fact of little value. *)
        | SOME v => if EVEN v then (data with gets_mem := new_gets_mem, Set x e)
                    else
                      (data with
                          <| gets_mem := (x, canonicalRegs data v)::new_gets_mem ;
                             to_canonical := insert v (lookup_any v data.to_canonical v)
                                                    data.to_canonical |>,
                       Set x e)) ∧
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
    let (data1, p1') = word_cse data p1 in
    let (data2, p2') = word_cse data p2 in
      (merge_data data1 data2, If c r1 r2 p1' p2')) ∧
  (word_cse data ((OpCurrHeap b r1 r2):'a prog) =
    let data = invalidate_data data r1 in
      (* r2 = r1 reads the register the instruction overwrites; such a fact
         would not describe the post-state, so it is not stored. *)
      if EVEN r2 ∨ r2 = r1 then (data,OpCurrHeap b r1 r2) else
        let r2' = canonicalRegs' r1 data r2 in
        let pL = OpCurrHeapToNumList b r2' in
          add_to_data_aux (register_read data r2') r1 pL (OpCurrHeap b r1 r2)) ∧
  (word_cse data (LocValue r l) =
    (* Loc l 0 is a constant determined by l, so CSE it like an immediate.
       Tag 48 is distinct from every other stored hash head (0, 2, 3). *)
    let data = invalidate_data data r in
      add_to_data_aux data r [48; l] (LocValue r l)) ∧
  (word_cse data (Skip) = (data, Skip)) ∧
  (* Store cannot occur in flat code, but it writes memory, so be sound:
     drop the load facts, keep the register-only facts. *)
  (word_cse data (Store e r) = (data with loads_mem := empty, Store e r)) ∧
  (word_cse data (Assign r e) = (data, Assign r e)) ∧
  (word_cse data (Raise r) = (data, Raise r)) ∧
  (word_cse data (Return r1 r2) = (data, Return r1 r2)) ∧
  (word_cse data (Tick) = (data, Tick)) ∧
  (word_cse data (Alloc r m) = (empty_data, Alloc r m)) ∧
  (word_cse data (Install p l dp dl m) = (empty_data, Install p l dp dl m)) ∧
  (* Buffer writes touch only the code/data buffers, nothing we track. *)
  (word_cse data (CodeBufferWrite r1 r2) = (data, CodeBufferWrite r1 r2)) ∧
  (word_cse data (DataBufferWrite r1 r2) = (data, DataBufferWrite r1 r2)) ∧
  (* FFI cuts the local environment, so all knowledge is stale. *)
  (word_cse data (FFI s p1 l1 p2 l2 m) = (empty_data, FFI s p1 l1 p2 l2 m)) ∧
  (* StoreConsts writes (or unsets) only its four register args and memory;
     the memory writes invalidate the load facts. *)
  (word_cse data (StoreConsts r1 r2 r3 r4 payload) =
     (let data = invalidate_regs data [r1; r2; r3; r4] in
        (data with loads_mem := empty, StoreConsts r1 r2 r3 r4 payload))) ∧
  (* Shared-memory op: a load writes its var; a store writes no register.
     Shared memory (sh_mdomain) is disjoint from the heap memory that load
     facts describe, so loads_mem survives both. *)
  (word_cse data (ShareInst op r exp) =
     let data = (if is_store op then data else invalidate_data data r) in
       (data, ShareInst op r exp)) ∧
  (* Conservative: optimise the loop body from empty state. *)
  (word_cse data (Loop names c exit_names) =
     let (_, c') = word_cse empty_data c in
       (empty_data, Loop names c' exit_names)) ∧
  (word_cse data (Break k) = (data, Break k)) ∧
  (word_cse data (Continue k) = (data, Continue k))
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

(* Concrete word type: the load-fact keys compare distinct offsets, which is
   only decidable at a fixed word width. *)
Triviality test_pattern_match_and_cons:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Shift Lsr 301 297 (Imm (9w:word64))));
          OpCurrHeap Add 305 301;
          Inst (Mem Load 309 (Addr 305 8w));
          Move 0 [(313,297)];
          Inst (Arith (Shift Lsr 317 313 (Imm 9w)));
          OpCurrHeap Add 321 317;
          Inst (Mem Load 325 (Addr 321 16w));
          Move 0 [(329,313)];
          Inst (Arith (Shift Lsr 333 329 (Imm 9w)));
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
          Inst (Arith (Shift Lsl 373 369 (Imm 9w)));
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
          Inst (Arith (Shift Lsl 417 413 (Imm 9w)));
          Inst (Arith (Binop Or 421 417 (Imm 5w)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24w)));
          Set NextFree (Var 429);
          Move 0 [(2,421)]; Return 273 [2]]
  =
    Seqs [Inst (Arith (Shift Lsr 301 297 (Imm 9w)));
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
          Inst (Arith (Shift Lsl 373 369 (Imm 9w)));
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
          Inst (Arith (Shift Lsl 417 413 (Imm 9w)));
          Inst (Arith (Binop Or 421 417 (Imm 5w)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24w)));
          Set NextFree (Var 429);
          Move 0 [(2,421)];
          Return 273 [2]]
Proof
  EVAL_TAC
QED

(* Loads from the same canonical address at the same width are CSE'd (and a
   chain hanging off the loaded value then CSEs too); a different width is a
   different fact; any store invalidates all load facts but no register
   facts. *)
Triviality test_load_cse:
  word_common_subexp_elim $
    Seqs [Inst (Mem Load 9 (Addr 7 (0w:word64)));
          Inst (Arith (Shift Lsr 11 9 (Imm 29w)));
          Inst (Mem Load 13 (Addr 7 0w));
          Inst (Arith (Shift Lsr 15 13 (Imm 29w)));
          Inst (Mem Load8 17 (Addr 7 0w));
          Inst (Mem Store 15 (Addr 7 0w));
          Inst (Mem Load 19 (Addr 7 0w))]
  =
    Seqs [Inst (Mem Load 9 (Addr 7 0w));
          Inst (Arith (Shift Lsr 11 9 (Imm 29w)));
          Move 0 [(13,9)];
          Move 0 [(15,11)];
          Inst (Mem Load8 17 (Addr 7 0w));
          Inst (Mem Store 15 (Addr 7 0w));
          Inst (Mem Load 19 (Addr 7 0w))]
Proof
  EVAL_TAC
QED

(* Set CurrHeap conservatively resets all knowledge (it is not emitted by
   data_to_word, so a finer treatment is not worth its proof cost): nothing
   after it is CSE'd. *)
Triviality test_set_currheap:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          OpCurrHeap Add 3 1;
          Set CurrHeap (Var 7);
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          OpCurrHeap Add 5 1]
  =
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          OpCurrHeap Add 3 1;
          Set CurrHeap (Var 7);
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          OpCurrHeap Add 5 1]
Proof
  EVAL_TAC
QED

(* A repeated LocValue of the same label is CSE'd to a Move. *)
Triviality test_locvalue:
  word_common_subexp_elim $
    Seqs [LocValue 7 100; LocValue 9 100]
  =
    Seqs [LocValue 7 100; Move 0 [(9,7)]]
Proof
  EVAL_TAC
QED

(* LongMul clobbers both outputs (7 and 9), so the value previously stored in
   9 is invalidated and the later Add is NOT replaced by a Move from 9. *)
Triviality test_multi_output_invalidation:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (LongMul 7 9 3 5));
          Inst (Arith (Binop Add 11 1 (Reg 1)))]
  =
    Seqs [Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (LongMul 7 9 3 5));
          Inst (Arith (Binop Add 11 1 (Reg 1)))]
Proof
  EVAL_TAC
QED

(* An instruction that reads the register it writes is not stored as a fact,
   so the second Add (reading the NEW 7) is not replaced by a Move. *)
Triviality test_self_read_not_cse:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Binop Add 7 7 (Imm 1w)));
          Inst (Arith (Binop Add 9 7 (Imm 1w)))]
  =
    Seqs [Inst (Arith (Binop Add 7 7 (Imm 1w)));
          Inst (Arith (Binop Add 9 7 (Imm 1w)))]
Proof
  EVAL_TAC
QED

(* Facts valid after both arms of an If survive the join: the Add fact
   (holder 7) is used both inside the first arm and after the join. *)
Triviality test_if_merge:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0w)
             (Inst (Arith (Binop Add 9 1 (Reg 1))))
             (Move 0 [(11,7)]);
          Inst (Arith (Binop Add 13 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0w) (Move 0 [(9,7)]) (Move 0 [(11,7)]);
          Move 0 [(13,7)]]
Proof
  EVAL_TAC
QED

(* An arm that clobbers a tracked register resets its branch knowledge, so
   nothing survives the join and the trailing Add is not CSE'd. *)
Triviality test_if_merge_clobber:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0w)
             (Move 0 [(7,3)])
             Skip;
          Inst (Arith (Binop Add 9 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0w);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0w) (Move 0 [(7,3)]) Skip;
          Inst (Arith (Binop Add 9 1 (Reg 1)))]
Proof
  EVAL_TAC
QED

val _ = Theory.delete_const "Seqs";
