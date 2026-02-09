(*
  This is the compiler's register allocator. It supports different modes:
      0) simple allocator, no spill heuristics;
      1) simple allocator + spill heuristics;
      2) IRC allocator, no spill heuristics (default);
      3) IRC allocator + spill heuristics;
      4) linear scan register allocator.
*)
Theory word_alloc
Libs
  preamble
Ancestors
  mllist
  asm[qualified] (* for arity-2 Const *)
  reg_alloc misc[qualified] wordLang linear_scan

val _ = patternMatchesSyntax.temp_enable_pmatch();

Overload Move0[inferior] = ``Move 0n``;
Overload Move1[inferior] = ``Move 1n``;

(*SSA form*)
Definition apply_nummap_key_def[simp]:
  apply_nummap_key f names =
  fromAList (MAP (λx,y.f x,y) (toAList names))
End

Definition apply_nummaps_key_def:
  apply_nummaps_key f names =
  (fromAList (MAP (λx,y.f x,y) (toAList (FST names))),
   fromAList (MAP (λx,y.f x,y) (toAList (SND names))))
End

Definition option_lookup_def:
  option_lookup t v = case lookup v t of NONE => 0n | SOME x => x
End

Definition even_list_def:
  (even_list = GENLIST (\x.2*x))
End

(*Consistently sets up the next alloc variable rename for v*)
Definition next_var_rename_def:
  next_var_rename v ssa (na:num) = (na,insert v na ssa,na+4)
End

Definition list_next_var_rename_def:
  (list_next_var_rename [] ssa (na:num) = ([],ssa,na)) ∧
  (list_next_var_rename (x::xs) ssa na =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ssa',na') = next_var_rename x ssa na in
    let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
      (y::ys,ssa'',na''))
End

Definition fake_move_def:
  fake_move v : α wordLang$prog = Inst (Const v 0w)
End

(*Do the merging moves only*)
Definition merge_moves_def:
  (merge_moves [] ssa_L ssa_R (na:num) = ([],[],na,ssa_L,ssa_R)) ∧
  (merge_moves (x::xs) ssa_L ssa_R na =
    let (seqL,seqR,na',ssa_L',ssa_R') =
      merge_moves xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    case (optLx,optLy) of
      (SOME Lx,SOME Ly) =>
      if Lx = Ly then
        (seqL,seqR,na',ssa_L',ssa_R')
      else
        let Lmove = (na',Lx) in
        let Rmove = (na',Ly) in
        (Lmove::seqL, Rmove::seqR,na'+4, insert x na' ssa_L'
                                       , insert x na' ssa_R')
    | _ => (seqL,seqR,na',ssa_L',ssa_R'))
End

(* tracking priority of moves
  0 = unprioritized
  1 = base "high" priority
  2 = higher priority than base

  T, INL <- left side
  F, INR <- right side
*)
Definition priority_def:
  (priority NONE b = 1n) ∧
  (priority (SOME (INL())) b =
    if b then 2 else 1) ∧
  (priority (SOME (INR())) b =
    if b then 1 else 2)
End

(*Separately do the fake moves*)
Definition fake_moves_def:
  (fake_moves prio [] ssa_L ssa_R (na:num) = (Skip:'a wordLang$prog,Skip:'a wordLang$prog,na,ssa_L,ssa_R)) ∧
  (fake_moves prio (x::xs) ssa_L ssa_R na =
    let (seqL,seqR,na',ssa_L',ssa_R') =
      fake_moves prio xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    case (optLx,optLy) of
      (NONE,SOME Ly) =>
        let Lmove = Seq seqL (fake_move na') in
        let Rmove = Seq seqR (Move (priority prio F) [(na',Ly)]) in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | (SOME Lx,NONE) =>
        let Lmove = Seq seqL (Move (priority prio T) [(na',Lx)]) in
        let Rmove = Seq seqR (fake_move na') in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | _ => (seqL,seqR,na',ssa_L',ssa_R'))
End

Definition fix_inconsistencies_def:
  fix_inconsistencies prio ssa_L ssa_R na =
  let var_union = MAP FST (toAList (union ssa_L ssa_R)) in
  let (Lmov,Rmov,na',ssa_L',ssa_R') =
    merge_moves var_union ssa_L ssa_R na in
  let (Lseq,Rseq,na'',ssa_L'',ssa_R'') =
    fake_moves prio var_union ssa_L' ssa_R' na' in
    (Seq (Move (priority prio T) Lmov) Lseq,Seq (Move (priority prio F) Rmov) Rseq,na'',ssa_L'')
End

(*ssa_cc_trans_inst does not need to interact with stack*)
(* Note: this needs to return a prog to support specific registers for AddCarry and other special insts
*)
Definition ssa_cc_trans_inst_def:
  (ssa_cc_trans_inst Skip ssa na = (Skip,ssa,na)) ∧
  (ssa_cc_trans_inst (Const reg w) ssa na =
    let (reg',ssa',na') = next_var_rename reg ssa na in
      (Inst (Const reg' w),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Binop bop r1 r2 ri)) ssa na =
    case ri of
      Reg r3 =>
      let r3' = option_lookup ssa r3 in
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Inst (Arith (Binop bop r1' r2' (Reg r3'))),ssa',na')
    | _ =>
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Inst (Arith (Binop bop r1' r2' ri)),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Shift shift r1 r2 n)) ssa na =
    let r2' = option_lookup ssa r2 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
      (Inst (Arith (Shift shift r1' r2' n)),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Div r1 r2 r3)) ssa na =
    let r2' = option_lookup ssa r2 in
    let r3' = option_lookup ssa r3 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    (Inst (Arith (Div r1' r2' r3')),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (AddCarry r1 r2 r3 r4)) ssa na =
    let r2' = option_lookup ssa r2 in
    let r3' = option_lookup ssa r3 in
    let r4' = option_lookup ssa r4 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let mov_in = Move1 [(0,r4')] in
    let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
    let mov_out = Move1 [(r4'',0)] in
      (Seq mov_in (Seq (Inst (Arith (AddCarry r1' r2' r3' 0))) mov_out), ssa'',na'')) ∧
  (* Note: for AddOverflow and SubOverflow, setting r4 to 0 is not necessary
     However, this helps with word_to_stack which currently only spills
     one register on writes
  *)
  (ssa_cc_trans_inst (Arith (AddOverflow r1 r2 r3 r4)) ssa na =
    let r2' = option_lookup ssa r2 in
    let r3' = option_lookup ssa r3 in
    (* TODO: This might need to be made a strong preference *)
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
    let mov_out = Move1 [(r4'',0)] in
      (Seq (Inst (Arith (AddOverflow r1' r2' r3' 0))) mov_out, ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (SubOverflow r1 r2 r3 r4)) ssa na =
    let r2' = option_lookup ssa r2 in
    let r3' = option_lookup ssa r3 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
    let mov_out = Move1 [(r4'',0)] in
      (Seq (Inst (Arith (SubOverflow r1' r2' r3' 0))) mov_out, ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (LongMul r1 r2 r3 r4)) ssa na =
    let r3' = option_lookup ssa r3 in
    let r4' = option_lookup ssa r4 in
    let mov_in = Move1 [(0,r3');(4,r4')] in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
    let mov_out = Move1 [(r2',0);(r1',6)] in
      (Seq mov_in  (Seq (Inst (Arith (LongMul 6 0 0 4))) mov_out),ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (LongDiv r1 r2 r3 r4 r5)) ssa na =
    let r3' = option_lookup ssa r3 in
    let r4' = option_lookup ssa r4 in
    let r5' = option_lookup ssa r5 in
    let mov_in = Move1 [(6,r3');(0,r4')] in
    let (r2',ssa',na') = next_var_rename r2 ssa na in
    let (r1',ssa'',na'') = next_var_rename r1 ssa' na' in
    let mov_out = Move1 [(r2',6);(r1',0)] in
      (Seq mov_in  (Seq (Inst (Arith (LongDiv 0 6 6 0 r5'))) mov_out),ssa'',na'')) ∧
  (ssa_cc_trans_inst (Mem Load r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (Mem Load r' (Addr a' w)),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Store r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Inst (Mem Store r' (Addr a' w)),ssa,na)) ∧
  (ssa_cc_trans_inst (Mem Load32 r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (Mem Load32 r' (Addr a' w)),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Store32 r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Inst (Mem Store32 r' (Addr a' w)),ssa,na)) ∧
  (ssa_cc_trans_inst (Mem Load8 r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (Mem Load8 r' (Addr a' w)),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Store8 r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Inst (Mem Store8 r' (Addr a' w)),ssa,na)) ∧
  (ssa_cc_trans_inst (FP (FPLess r f1 f2)) ssa na =
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (FP (FPLess r' f1 f2)),ssa',na')) ∧
  (ssa_cc_trans_inst (FP (FPLessEqual r f1 f2)) ssa na =
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (FP (FPLessEqual r' f1 f2)),ssa',na')) ∧
  (ssa_cc_trans_inst (FP (FPEqual r f1 f2)) ssa na =
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (FP (FPEqual r' f1 f2)),ssa',na')) ∧
  (ssa_cc_trans_inst (FP (FPMovToReg r1 r2 d):'a inst) ssa na =
    if dimindex(:'a) = 64 then
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Inst (FP (FPMovToReg r1' r2 d)),ssa',na')
    else
      let (r1',ssa',na') = next_var_rename r1 ssa na in
      let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
        (Inst (FP (FPMovToReg r1' r2' d)),ssa'',na'')) ∧
  (ssa_cc_trans_inst (FP (FPMovFromReg d r1 r2)) ssa na =
    if dimindex(:'a) = 64 then
      let r1' = option_lookup ssa r1 in
        (Inst (FP (FPMovFromReg d r1' 0)),ssa,na)
    else
      let r1' = option_lookup ssa r1 in
      let r2' = option_lookup ssa r2 in
      if r1' = r2'
      then
        (* force distinct with an extra Move *)
        let (r2'',ssa',na') = next_var_rename r2 ssa na in
        let mov_in = Move0 [(r2'',r2')] in
        (Seq mov_in (Inst (FP (FPMovFromReg d r1' r2''))),
        ssa',na')
      else
        (Inst (FP (FPMovFromReg d r1' r2')),ssa,na)) ∧
        (*Catchall -- for future instructions to be added, and all other FP *)
  (ssa_cc_trans_inst x ssa na = (Inst x,ssa,na))
End

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
Definition ssa_cc_trans_exp_def:
  (ssa_cc_trans_exp t (Var num) =
    Var (option_lookup t num)) ∧
  (ssa_cc_trans_exp t (Load exp) = Load (ssa_cc_trans_exp t exp)) ∧
  (ssa_cc_trans_exp t (Op wop ls) =
    Op wop (MAP (ssa_cc_trans_exp t) ls)) ∧
  (ssa_cc_trans_exp t (Shift sh exp nexp) =
    Shift sh (ssa_cc_trans_exp t exp) nexp) ∧
  (ssa_cc_trans_exp t expr = expr)
End

(*Attempt to pull out "renaming" moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
Definition list_next_var_rename_move_def:
  list_next_var_rename_move ssa n ls =
    let cur_ls = MAP (option_lookup ssa) ls in
    let (new_ls,ssa',n') = list_next_var_rename ls ssa n in
    (Move0 (ZIP(new_ls,cur_ls)),ssa',n')
End

(* force the renaming map to send x -> y unless
  x is already remapped *)
Definition force_rename_def:
  (force_rename [] ssa = ssa) ∧
  (force_rename ((x,y)::xs) ssa =
    force_rename xs (insert x y ssa))
End

Definition mk_prio_def:
  mk_prio el er =
  if el = Skip then SOME (INL())
  else if er = Skip then SOME (INR())
  else NONE
End

Definition ssa_cc_trans_def:
  (ssa_cc_trans Skip ssa na = (Skip,ssa,na)) ∧
  (ssa_cc_trans (Move pri ls) ssa na =
    let ls_1 = MAP FST ls in
    let ls_2 = MAP SND ls in
    let ren_ls2 = MAP (option_lookup ssa) ls_2 in
    let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
    let force =
      FILTER (λ(x,y). ¬ MEM x ls_1) (ZIP(ls_2,ren_ls1)) in
      (Move pri (ZIP(ren_ls1,ren_ls2)),force_rename force ssa',na')) ∧
  (ssa_cc_trans (StoreConsts a b c d ws) ssa na =
    let c1 = option_lookup ssa c in
    let d1 = option_lookup ssa d in
    let (d2,ssa',na') = next_var_rename d ssa na in
    let (c2,ssa'',na'') = next_var_rename c ssa' na' in
    let prog = Seq (Move1 [(4,c1);(6,d1)])
      (Seq (StoreConsts 0 2 4 6 ws)
           (Move1 [(c2,4);(d2,6)])) in
    (prog, ssa'',na'')
  ) ∧
  (ssa_cc_trans (Inst i) ssa na =
    let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
      (i',ssa',na')) ∧
  (ssa_cc_trans (Assign num exp) ssa na=
    let exp' = ssa_cc_trans_exp ssa exp in
    let (num',ssa',na') = next_var_rename num ssa na in
      (Assign num' exp',ssa',na')) ∧
  (ssa_cc_trans (Get num store) ssa na=
    let (num',ssa',na') = next_var_rename num ssa na in
      (Get num' store,ssa',na')) ∧
  (ssa_cc_trans (Store exp num) ssa na=
    let exp' = ssa_cc_trans_exp ssa exp in
    let num' = option_lookup ssa num in
      (Store exp' num',ssa,na)) ∧
  (ssa_cc_trans (Seq s1 s2) ssa na=
    let (s1',ssa',na') = ssa_cc_trans s1 ssa na in
    let (s2',ssa'',na'') = ssa_cc_trans s2 ssa' na' in
      (Seq s1' s2',ssa'',na'')) ∧
  (ssa_cc_trans (MustTerminate s1) ssa na =
    let (s1',ssa',na') = ssa_cc_trans s1 ssa na in
      (MustTerminate s1',ssa',na')) ∧
  (*Tricky pmatch 1: we need to merge the ssa results from both branches by
    unSSA-ing the phi functions
  *)
  (ssa_cc_trans (If cmp r1 ri e2 e3) ssa na =
    let r1' = option_lookup ssa r1 in
    let ri' = case ri of Reg r => Reg (option_lookup ssa r)
                      |  Imm v => Imm v in
    (*ssa is the copy for both branches,
      however, we can use new na2 and ns2*)
    let (e2',ssa2,na2) = ssa_cc_trans e2 ssa na in
    (*ssa2 is the ssa map for the first branch*)
    let (e3',ssa3,na3) = ssa_cc_trans e3 ssa na2 in
    (*ssa3 is the ssa map for the second branch, notice we
      continued using na2 here though!*)
    (* prioritizing original skips *)
    let prio = mk_prio e2' e3' in
    let (e2_cons,e3_cons,na_fin,ssa_fin) =
      fix_inconsistencies prio ssa2 ssa3 na3 in
    (If cmp r1' ri' (Seq e2' e2_cons) (Seq e3' e3_cons),ssa_fin,na_fin)) ∧
  (*For cutsets, we must restart the ssa mapping to maintain consistency*)
  (ssa_cc_trans (Alloc num numset) ssa na =
    let all_names = union (FST numset) (SND numset) in
    let ls = MAP FST (toAList all_names) in
    (*This trick allows us to not keep the "next stack" variable by
      simply starting from the next available stack location
      Assuming na is an alloc var of course..*)
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let num' = option_lookup ssa' num in
    let stack_set = apply_nummaps_key (option_lookup ssa') numset in
    (*Restart the ssa map*)
    let ssa_cut = inter ssa' all_names in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    let prog = (Seq (stack_mov)
               (Seq (Move1 [(2,num')])
               (Seq (Alloc 2 stack_set) (ret_mov)))) in
    (prog,ssa'',na'')) ∧
  (ssa_cc_trans (Raise num) ssa na =
    let num' = option_lookup ssa num in
    let mov = Move1 [(2,num')] in
    (Seq mov (Raise 2),ssa,na)) ∧
  (ssa_cc_trans (OpCurrHeap b dst src) ssa na=
    let src' = option_lookup ssa src in
    let (dst',ssa',na') = next_var_rename dst ssa na in
      (OpCurrHeap b dst' src',ssa',na')) ∧
  (ssa_cc_trans (Return num nums) ssa na=
    let num' = option_lookup ssa num in
    let nums' = MAP (option_lookup ssa) nums in
    let rets = GENLIST (\x.2*(x+1)) (LENGTH nums') in
    let mov = Move 0 (ZIP (rets,nums')) in
    (Seq mov (Return num' rets),ssa,na)) ∧
  (ssa_cc_trans Tick ssa na = (Tick,ssa,na)) ∧
  (ssa_cc_trans (Set n exp) ssa na =
    let exp' = ssa_cc_trans_exp ssa exp in
    (Set n exp',ssa,na)) ∧
  (ssa_cc_trans (LocValue r l1) ssa na =
    let (r',ssa',na') = next_var_rename r ssa na in
      (LocValue r' l1,ssa',na')) ∧
  (ssa_cc_trans (Install ptr len dptr dlen numset) ssa na =
    let all_names = union (FST numset) (SND numset) in
    let ls = MAP FST (toAList all_names) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummaps_key (option_lookup ssa') numset in
    let ptr' = option_lookup ssa' ptr in
    let len' = option_lookup ssa' len in
    let dptr' = option_lookup ssa' dptr in
    let dlen' = option_lookup ssa' dlen in
    let ssa_cut = inter ssa' all_names in
    let (ptr'',ssa'',na'') = next_var_rename ptr ssa_cut (na'+2) in
    let (ret_mov,ssa''',na''') =
      list_next_var_rename_move ssa'' na'' ls in
    let prog = (Seq (stack_mov)
               (Seq (Move1 [(2,ptr');(4,len')])
               (Seq (Install 2 4 dptr' dlen' stack_set)
               (Seq (Move1 [(ptr'',2)]) ret_mov)))) in
    (prog,ssa''',na''')) ∧
  (ssa_cc_trans (CodeBufferWrite r1 r2) ssa na =
    let r1' = option_lookup ssa r1 in
    let r2' = option_lookup ssa r2 in
    (CodeBufferWrite r1' r2',ssa,na)) ∧
  (ssa_cc_trans (DataBufferWrite r1 r2) ssa na =
    let r1' = option_lookup ssa r1 in
    let r2' = option_lookup ssa r2 in
    (DataBufferWrite r1' r2',ssa,na)) ∧
  (ssa_cc_trans (FFI ffi_index ptr1 len1 ptr2 len2 numset) ssa na =
    let all_names = union (FST numset) (SND numset) in
    let ls = MAP FST (toAList all_names) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummaps_key (option_lookup ssa') numset in
    let cptr1 = option_lookup ssa' ptr1 in
    let clen1 = option_lookup ssa' len1 in
    let cptr2 = option_lookup ssa' ptr2 in
    let clen2 = option_lookup ssa' len2 in
    let ssa_cut = inter ssa' all_names in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    let prog = (Seq (stack_mov)
               (Seq (Move1 [(2,cptr1);(4,clen1);(6,cptr2);(8,clen2)])
               (Seq (FFI ffi_index 2 4 6 8 stack_set) (ret_mov)))) in
    (prog,ssa'',na'')) ∧
  (ssa_cc_trans (Call NONE dest args h) ssa na =
    let names = MAP (option_lookup ssa) args in
    let conv_args = GENLIST (\x.2*x) (LENGTH names) in
    let move_args = (Move1 (ZIP (conv_args,names))) in
    let prog = Seq move_args (Call NONE dest conv_args h) in
      (prog,ssa,na)) ∧
  (ssa_cc_trans (Call (SOME(ret,numset,ret_handler,l1,l2)) dest args h) ssa na =
    let all_names = union (FST numset) (SND numset) in
    let ls = MAP FST (toAList all_names) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummaps_key (option_lookup ssa') numset in
    let names = MAP (option_lookup ssa) args in
    let conv_args = GENLIST (\x.2*(x+1)) (LENGTH names) in
    let move_args = (Move1 (ZIP (conv_args,names))) in
    let ssa_cut = inter ssa' all_names in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    (*ret_mov restores the cutset*)
    (*This recurses on the returning handler*)
    let (ret',ssa_2_p,na_2_p) = list_next_var_rename ret ssa'' na'' in
    let (ren_ret_handler,ssa_2,na_2) =
      ssa_cc_trans ret_handler ssa_2_p na_2_p in
    let regs = GENLIST (\x.2*(x+1)) (LENGTH ret) in
    let mov_ret_handler =
        (Seq ret_mov (Seq (Move1 (ZIP (ret',regs))) (ren_ret_handler))) in
    (case h of
      NONE =>
        let prog =
          (Seq stack_mov (Seq move_args
          (Call (SOME(regs,stack_set,mov_ret_handler,l1,l2))
                dest conv_args NONE))) in
        (prog,ssa_2,na_2)
    | SOME(n,h,l1',l2') =>
        let (n',ssa_3_p,na_3_p) = next_var_rename n ssa'' na_2 in
        let (ren_exc_handler,ssa_3,na_3) =
            (ssa_cc_trans h ssa_3_p na_3_p) in
        let mov_exc_handler =
            (Seq ret_mov (Seq(Move1 [n',2]) (ren_exc_handler))) in
        let prio = mk_prio mov_ret_handler mov_exc_handler in
        let (ret_cons,exc_cons,na_fin,ssa_fin) =
            fix_inconsistencies prio ssa_2 ssa_3 na_3 in
        let cons_ret_handler = Seq mov_ret_handler ret_cons in
        let cons_exc_handler = Seq mov_exc_handler exc_cons in
        let prog =
            (Seq stack_mov (Seq move_args
            (Call (SOME(regs,stack_set,cons_ret_handler,l1,l2))
               dest conv_args (SOME(2,cons_exc_handler,l1',l2'))))) in
        (prog,ssa_fin,na_fin))) /\
  (ssa_cc_trans (ShareInst op v exp) ssa na =
    let exp' = ssa_cc_trans_exp ssa exp in
      if op = Store ∨ op = Store8 ∨ op = Store16 ∨ op = Store32
      then
        (ShareInst op (option_lookup ssa v) exp',ssa,na)
      else
        let (v',ssa',na') = next_var_rename v ssa na in
          (ShareInst op v' exp',ssa',na'))
End

(*Recursively applying colours to a program*)

Definition apply_colour_exp_def[simp]:
  (apply_colour_exp f (Var num) = Var (f num)) /\
  (apply_colour_exp f (Load exp) = Load (apply_colour_exp f exp)) /\
  (apply_colour_exp f (Op wop ls) = Op wop (MAP (apply_colour_exp f) ls)) /\
  (apply_colour_exp f (Shift sh exp nexp) = Shift sh (apply_colour_exp f exp) nexp) /\
  (apply_colour_exp f expr = expr)
End

Definition apply_colour_imm_def[simp]:
  (apply_colour_imm f (Reg n) = Reg (f n)) ∧
  (apply_colour_imm f x = x)
End

Definition apply_colour_inst_def[simp]:
  (apply_colour_inst f Skip = Skip) ∧
  (apply_colour_inst f (Const reg w) = Const (f reg) w) ∧
  (apply_colour_inst f (Arith (Binop bop r1 r2 ri)) =
    Arith (Binop bop (f r1) (f r2) (apply_colour_imm f ri))) ∧
  (apply_colour_inst f (Arith (Shift shift r1 r2 n)) =
    Arith (Shift shift (f r1) (f r2) n)) ∧
  (apply_colour_inst f (Arith (Div r1 r2 r3)) =
    Arith (Div (f r1) (f r2) (f r3))) ∧
  (apply_colour_inst f (Arith (AddCarry r1 r2 r3 r4)) =
    Arith (AddCarry (f r1) (f r2) (f r3) (f r4))) ∧
  (apply_colour_inst f (Arith (AddOverflow r1 r2 r3 r4)) =
    Arith (AddOverflow (f r1) (f r2) (f r3) (f r4))) ∧
  (apply_colour_inst f (Arith (SubOverflow r1 r2 r3 r4)) =
    Arith (SubOverflow (f r1) (f r2) (f r3) (f r4))) ∧
  (apply_colour_inst f (Arith (LongMul r1 r2 r3 r4)) =
    Arith (LongMul (f r1) (f r2) (f r3) (f r4))) ∧
  (apply_colour_inst f (Arith (LongDiv r1 r2 r3 r4 r5)) =
    Arith (LongDiv (f r1) (f r2) (f r3) (f r4) (f r5))) ∧
  (apply_colour_inst f (Mem Load r (Addr a w)) =
    Mem Load (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Store r (Addr a w)) =
    Mem Store (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Load32 r (Addr a w)) =
    Mem Load32 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Store32 r (Addr a w)) =
    Mem Store32 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Load8 r (Addr a w)) =
    Mem Load8 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Store8 r (Addr a w)) =
    Mem Store8 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (FP (FPLess r f1 f2)) = FP (FPLess (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPLessEqual r f1 f2)) = FP (FPLessEqual (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPEqual r f1 f2)) = FP (FPEqual (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPMovToReg r1 r2 d)) = FP (FPMovToReg (f r1) (f r2) d)) ∧
  (apply_colour_inst f (FP (FPMovFromReg d r1 r2)) = FP (FPMovFromReg d (f r1) (f r2))) ∧
  (apply_colour_inst f x = x)
End (*Catchall -- for future instructions to be added*)

Definition apply_colour_def[simp]:
  (apply_colour f Skip = Skip) ∧
  (apply_colour f (Move pri ls) =
    Move pri (ZIP (MAP (f o FST) ls, MAP (f o SND) ls))) ∧
  (apply_colour f (Inst i) = Inst (apply_colour_inst f i)) ∧
  (apply_colour f (Assign num exp) = Assign (f num) (apply_colour_exp f exp)) ∧
  (apply_colour f (Get num store) = Get (f num) store) ∧
  (apply_colour f (Store exp num) = Store (apply_colour_exp f exp) (f num)) ∧
  (apply_colour f (Call ret dest args h) =
    let ret = case ret of NONE => NONE
                        | SOME (vs,cutset,ret_handler,l1,l2) =>
                          SOME (MAP f vs,apply_nummaps_key f cutset,apply_colour f ret_handler,l1,l2) in
    let args = MAP f args in
    let h = case h of NONE => NONE
                     | SOME (v,prog,l1,l2) => SOME (f v, apply_colour f prog,l1,l2) in
      Call ret dest args h) ∧
  (apply_colour f (Seq s1 s2) = Seq (apply_colour f s1) (apply_colour f s2)) ∧
  (apply_colour f (MustTerminate s1) = MustTerminate (apply_colour f s1)) ∧
  (apply_colour f (If cmp r1 ri e2 e3) =
    If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)) ∧
  (apply_colour f (Install r1 r2 r3 r4 numset) =
    Install (f r1) (f r2) (f r3) (f r4) (apply_nummaps_key f numset)) ∧
  (apply_colour f (CodeBufferWrite r1 r2) =
    CodeBufferWrite (f r1) (f r2)) ∧
  (apply_colour f (DataBufferWrite r1 r2) =
    DataBufferWrite (f r1) (f r2)) ∧
  (apply_colour f (FFI ffi_index ptr1 len1 ptr2 len2 numset) =
    FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2) (apply_nummaps_key f numset)) ∧
  (apply_colour f (LocValue r l1) =
    LocValue (f r) l1) ∧
  (apply_colour f (Alloc num numset) =
    Alloc (f num) (apply_nummaps_key f numset)) ∧
  (apply_colour f (StoreConsts a b c d ws) =
    StoreConsts (f a) (f b) (f c) (f d) ws) ∧
  (apply_colour f (Raise num) = Raise (f num)) ∧
  (apply_colour f (Return num1 nums) = Return (f num1) (MAP f nums)) ∧
  (apply_colour f Tick = Tick) ∧
  (apply_colour f (Set n exp) = Set n (apply_colour_exp f exp)) ∧
  (apply_colour f (OpCurrHeap b n1 n2) = OpCurrHeap b (f n1) (f n2)) ∧
  (apply_colour f (ShareInst op v exp) = ShareInst op (f v) (apply_colour_exp f exp)) ∧
  (apply_colour f p = p )
End


(* Liveness Analysis*)

(*Writes made by any inst as a sptree*)
Definition get_writes_inst_def:
  (get_writes_inst (Const reg w) = insert reg () LN) ∧
  (get_writes_inst (Arith (Binop bop r1 r2 ri)) = insert r1 () LN) ∧
  (get_writes_inst (Arith (Shift shift r1 r2 n)) = insert r1 () LN) ∧
  (get_writes_inst (Arith (Div r1 r2 r3)) = insert r1 () LN) ∧
  (get_writes_inst (Arith (AddCarry r1 r2 r3 r4)) = insert r4 () (insert r1 () LN)) ∧
  (get_writes_inst (Arith (AddOverflow r1 r2 r3 r4)) = insert r4 () (insert r1 () LN)) ∧
  (get_writes_inst (Arith (SubOverflow r1 r2 r3 r4)) = insert r4 () (insert r1 () LN)) ∧
  (get_writes_inst (Arith (LongMul r1 r2 r3 r4)) = insert r2 () (insert r1 () LN)) ∧
  (get_writes_inst (Arith (LongDiv r1 r2 r3 r4 r5)) = insert r2 () (insert r1 () LN)) ∧
  (get_writes_inst (Mem Load r (Addr a w)) = insert r () LN) ∧
  (get_writes_inst (Mem Load32 r (Addr a w)) = insert r () LN) ∧
  (get_writes_inst (Mem Load8 r (Addr a w)) = insert r () LN) ∧
  (get_writes_inst (FP (FPLess r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPLessEqual r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPEqual r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPMovToReg r1 r2 d) :'a inst) =
    if dimindex(:'a) = 64
      then insert r1 () LN
      else insert r2 () (insert r1 () LN)) ∧
  (get_writes_inst inst = LN)
End

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
Definition get_live_inst_def:
  (get_live_inst Skip live:num_set = live) ∧
  (get_live_inst (Const reg w) live = delete reg live) ∧
  (get_live_inst (Arith (Binop bop r1 r2 ri)) live =
    case ri of Reg r3 => insert r2 () (insert r3 () (delete r1 live))
    | _ => insert r2 () (delete r1 live)) ∧
  (get_live_inst (Arith (Shift shift r1 r2 n)) live =
    insert r2 () (delete r1 live)) ∧
  (get_live_inst (Arith (Div r1 r2 r3)) live =
    (insert r3 () (insert r2 () (delete r1 live)))) ∧
  (get_live_inst (Arith (AddCarry r1 r2 r3 r4)) live =
    (*r4 is live anyway*)
    insert r4 () (insert r3 () (insert r2 () (delete r1 live)))) ∧
  (get_live_inst (Arith (AddOverflow r1 r2 r3 r4)) live =
    insert r3 () (insert r2 () (delete r4 (delete r1 live)))) ∧
  (get_live_inst (Arith (SubOverflow r1 r2 r3 r4)) live =
    insert r3 () (insert r2 () (delete r4 (delete r1 live)))) ∧
  (get_live_inst (Arith (LongMul r1 r2 r3 r4)) live =
    insert r4 () (insert r3 () (delete r2 (delete r1 live)))) ∧
  (get_live_inst (Arith (LongDiv r1 r2 r3 r4 r5)) live =
    insert r5 () (insert r4 () (insert r3 () (delete r2 (delete r1 live))))) ∧
  (get_live_inst (Mem Load r (Addr a w)) live =
    insert a () (delete r live)) ∧
  (get_live_inst (Mem Store r (Addr a w)) live =
    insert a () (insert r () live)) ∧
  (get_live_inst (Mem Load32 r (Addr a w)) live =
    insert a () (delete r live)) ∧
  (get_live_inst (Mem Store32 r (Addr a w)) live =
    insert a () (insert r () live)) ∧
  (get_live_inst (Mem Load8 r (Addr a w)) live =
    insert a () (delete r live)) ∧
  (get_live_inst (Mem Store8 r (Addr a w)) live =
    insert a () (insert r () live)) ∧
  (get_live_inst (FP (FPLess r f1 f2)) live = delete r live) ∧
  (get_live_inst (FP (FPLessEqual r f1 f2)) live = delete r live) ∧
  (get_live_inst (FP (FPEqual r f1 f2)) live = delete r live) ∧
  (get_live_inst (FP (FPMovToReg r1 r2 d): 'a inst) live =
    if dimindex(:'a) = 64
      then delete r1 live
      else delete r1 (delete r2 live)) ∧
  (get_live_inst (FP (FPMovFromReg d r1 r2)) live =
    if dimindex(:'a) = 64
      then insert r1 () live
      else insert r2 () (insert r1 () live)) ∧
  (*Catchall -- for future instructions to be added*)
  (get_live_inst x live = live)
End

Definition big_union_def:
  big_union ls = FOLDR (λx y. union x y) LN ls
End

Definition get_live_exp_def:
  (get_live_exp (Var num) = insert num () LN ) ∧
  (get_live_exp (Load exp) = get_live_exp exp) ∧
  (get_live_exp (Op wop ls) =
    big_union (MAP get_live_exp ls)) ∧
  (get_live_exp (Shift sh exp nexp) = get_live_exp exp) ∧
  (get_live_exp expr = LN)
End

Definition numset_list_insert_def:
  (numset_list_insert [] t = t) ∧
  (numset_list_insert (x::xs) t = insert x () (numset_list_insert xs t))
End

Definition get_live_def:
  (get_live Skip live = live) ∧
  (*All SNDs are read and all FSTs are written*)
  (get_live (Move pri ls) live =
    let killed = FOLDR delete live (MAP FST ls) in
      numset_list_insert (MAP SND ls) killed) ∧
  (get_live (Inst i) live = get_live_inst i live) ∧
  (*num is written, exp is read*)
  (get_live (Assign num exp) live =
    let sub = get_live_exp exp in
      union sub (delete num live)) ∧
  (get_live (Get num store) live = delete num live) ∧
  (*Everything is read*)
  (get_live (Store exp num) live =
    insert num () (union (get_live_exp exp) live))∧
  (*Find liveset just before s2 which is the input liveset to s1*)
  (get_live (Seq s1 s2) live =
    get_live s1 (get_live s2 live)) ∧
  (get_live (MustTerminate s1) live =
    get_live s1 live) ∧
  (*First pmatch where branching appears:
    We get the livesets for e2 and e3, union them, add the if variable
    then pass the resulting liveset upwards
  *)
  (get_live (If cmp r1 ri e2 e3) live =
    let e2_live = get_live e2 live in
    let e3_live = get_live e3 live in
    let union_live = union e2_live e3_live in
       case ri of Reg r2 => insert r2 () (insert r1 () union_live)
      | _ => insert r1 () union_live) ∧
  (get_live (Alloc num numset) live = insert num () (union (FST numset) (SND numset))) ∧
  (get_live (StoreConsts a b c d ws) live =
    insert c () (insert d () (delete a (delete b live)))) ∧
  (get_live (Install r1 r2 r3 r4 numset) live =
    list_insert [r1;r2;r3;r4] (union (FST numset) (SND numset))) ∧
  (get_live (CodeBufferWrite r1 r2) live =
    list_insert [r1;r2] live) ∧
  (get_live (DataBufferWrite r1 r2) live =
    list_insert [r1;r2] live) ∧
  (get_live (FFI ffi_index ptr1 len1 ptr2 len2 numset) live =
   insert ptr1 () (insert len1 ()
     (insert ptr2 () (insert len2 () (union (FST numset) (SND numset)) )))) ∧
  (get_live (StoreConsts a b c d ws) live =
     (insert c () (insert d () live))) ∧
  (get_live (Raise num) live = insert num () live) ∧
  (get_live (Return num1 nums) live = insert num1 () (numset_list_insert nums live)) ∧
  (get_live Tick live = live) ∧
  (get_live (LocValue r l1) live = delete r live) ∧
  (get_live (Set n exp) live = union (get_live_exp exp) live) ∧
  (get_live (OpCurrHeap b n1 n2) live = insert n2 () (delete n1 live)) ∧
  (get_live (ShareInst mop v exp) live =
    let sub = get_live_exp exp in
      if mop = Store ∨ mop = Store8 ∨ mop = Store16 ∨ mop = Store32
      then union sub (insert v () live)
      else union sub (delete v live)) ∧
  (*Cut-set must be live, args input must be live
    For tail calls, there shouldn't be a liveset since control flow will
    never return into the same instance
    Otherwise, both args + cutsets live
  *)
  (get_live (Call NONE dest args h) live = numset_list_insert args LN) ∧
  (get_live (Call (SOME(_,cutset,_)) dest args h) live =
    union (union (FST cutset) (SND cutset)) (numset_list_insert args LN))
End

(* Dead instruction removal *)
Definition remove_dead_inst_def:
  (remove_dead_inst Skip (live:num_set) = T) ∧
  (remove_dead_inst (Const reg w) live = (lookup reg live = NONE)) ∧
  (remove_dead_inst (Arith (Binop bop r1 r2 ri)) live = (lookup r1 live = NONE)) ∧
  (remove_dead_inst (Arith (Shift shift r1 r2 n)) live = (lookup r1 live = NONE)) ∧
  (remove_dead_inst (Arith (Div r1 r2 r3)) live = (lookup r1 live = NONE)) ∧
  (remove_dead_inst (Arith (AddCarry r1 r2 r3 r4)) live =
    (lookup r1 live = NONE ∧ lookup r4 live = NONE)) ∧
  (remove_dead_inst (Arith (AddOverflow r1 r2 r3 r4)) live =
    (lookup r1 live = NONE ∧ lookup r4 live = NONE)) ∧
  (remove_dead_inst (Arith (SubOverflow r1 r2 r3 r4)) live =
    (lookup r1 live = NONE ∧ lookup r4 live = NONE)) ∧
  (remove_dead_inst (Arith (LongMul r1 r2 r3 r4)) live =
    (lookup r1 live = NONE ∧ lookup r2 live = NONE)) ∧
  (remove_dead_inst (Arith (LongDiv r1 r2 r3 r4 r5)) live =
    (lookup r1 live = NONE ∧ lookup r2 live = NONE)) ∧
  (remove_dead_inst (Mem Load r (Addr a w)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (Mem Load32 r (Addr a w)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (Mem Load8 r (Addr a w)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPLess r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPLessEqual r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPEqual r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPMovToReg r1 r2 d) :'a inst) live =
    if dimindex(:'a) = 64 then lookup r1 live = NONE
    else (lookup r1 live = NONE ∧ (lookup r2 live = NONE))) ∧
  (*Catchall -- for other instructions*)
  (remove_dead_inst x live = F)
End

(* Delete dead code, w.r.t. a set of live variables.
  The liveset is a tuple (live,nlive):
  - live is an sptree of live variables
  - nlive is a list of globals which are NOT live

  This code is written assuming flat_exp_conventions,
    so many trivial cases are omitted.
*)
Definition remove_dead_def:
  (remove_dead (Move pri ls) live nlive =
    let ls = FILTER (λx,y. lookup x live = SOME ()) ls in
    if ls = [] then (Skip,live,nlive)
    else
    let killed = FOLDR delete live (MAP FST ls) in
      (Move pri ls, numset_list_insert (MAP SND ls) killed,nlive)) ∧
  (remove_dead (Inst i) live nlive =
    if remove_dead_inst i live
    then (Skip,live,nlive)
    else (Inst i, get_live_inst i live,nlive)) ∧
  (remove_dead (Get num store) live nlive =
    if lookup num live = NONE then
      (Skip,live,nlive)
    else (Get num store, delete num live, FILTER (λs. store ≠ s) nlive)) ∧
  (remove_dead (OpCurrHeap b num src) live nlive =
    if lookup num live = NONE then
      (Skip,live,nlive)
    else (
      OpCurrHeap b num src,
        insert src () (delete num live), FILTER (λs. CurrHeap ≠ s) nlive)) ∧
  (remove_dead (LocValue r l1) live nlive =
    if lookup r live = NONE then
      (Skip, live,nlive)
    else (LocValue r l1, delete r live,nlive)) ∧
  (remove_dead (Set store_name exp) live nlive =
    case exp of
      Var r =>
      if MEM store_name nlive then
        (Skip, live, nlive)
      else
        (Set store_name (Var r), insert r () live, store_name::nlive)
    | _ =>
      let prog = Set store_name exp in
        (prog,get_live prog live,[])
  ) ∧
  (remove_dead (Seq s1 s2) live nlive =
    let (s2,s2live,s2nlive) = remove_dead s2 live nlive in
    let (s1,s1live,s1nlive) = remove_dead s1 s2live s2nlive in
    let prog =
      if s1 = Skip then
        s2
      else
        if s2 = Skip then s1
        else Seq s1 s2
    in (prog,s1live,s1nlive)) ∧
  (remove_dead (MustTerminate s1) live nlive =
    (* This can technically be optimized away if it was a Skip,
       but we should never use MustTerminate to wrap completely dead code
    *)
    let (s1,s1live,s1nlive) = remove_dead s1 live nlive in
      (MustTerminate s1,s1live,s1nlive)) ∧
  (remove_dead (If cmp r1 ri e2 e3) live nlive =
    let (e2,e2_live,e2_nlive) = remove_dead e2 live nlive in
    let (e3,e3_live,e3_nlive) = remove_dead e3 live nlive in
    let union_live = union e2_live e3_live in
    let liveset =
       case ri of Reg r2 => insert r2 () (insert r1 () union_live)
      | _ => insert r1 () union_live in
    let nliveset = FILTER (λs. MEM s e3_nlive) e2_nlive in
    let prog =
      if e2 = Skip ∧ e3 = Skip then Skip
      else If cmp r1 ri e2 e3 in
    (prog,liveset,nliveset)) ∧
  (remove_dead (Call(SOME(v,cutsets,ret_handler,l1,l2))dest args h) live nlive =
    (*top level*)
    let args_set = numset_list_insert args LN in
    let cutset = union (FST cutsets) (SND cutsets) in
    let live_set = union cutset args_set in
    let (ret_handler,_) = remove_dead ret_handler live nlive in
    let h =
      (case h of
        NONE => NONE
      | SOME(v',prog,l1,l2) =>
        SOME(v',FST (remove_dead prog live nlive),l1,l2)) in
    (Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args h,(live_set,[]))) ∧
  (* we should not remove the ShareInst Load instructions.
    * It produces a ffi event even if the variable is not in
    * the live set *)
  (* In the cases below, we either return nlive unchanged
    or we return [] because of control flow *)
  (remove_dead (Call NONE a b c) live nlive =
    let prog = Call NONE a b c in
      (prog, get_live prog live, [])) ∧
  (remove_dead (Alloc a b) live nlive =
    let prog = Alloc a b in
      (prog, get_live prog live, [])) ∧
  (remove_dead (Raise a) live nlive =
    let prog = Raise a in
      (prog, get_live prog live, [])) ∧
  (remove_dead (Return a b) live nlive =
    let prog = Return a b in
      (prog, get_live prog live, [])) ∧
  (remove_dead prog live nlive = (prog,get_live prog live,nlive))
End

Definition remove_dead_prog_def:
  remove_dead_prog prog = FST (remove_dead prog LN [])
End

(*Single step immediate writes by a prog*)
Definition get_writes_def:
  (get_writes (Move pri ls) = numset_list_insert (MAP FST ls) LN)∧
  (get_writes (Inst i) = get_writes_inst i) ∧
  (get_writes (Assign num exp) = insert num () LN)∧
  (get_writes (Get num store) = insert num () LN) ∧
  (get_writes (LocValue r l1) = insert r () LN) ∧
  (get_writes (Install r1 _ _ _ _) = insert r1 () LN) ∧
  (get_writes (OpCurrHeap b r1 _) = insert r1 () LN) ∧
  (get_writes (StoreConsts a b c d _) = insert a () (insert b () (insert c () (insert d () LN)))) ∧
  (get_writes (ShareInst Load v _) = insert v () LN) ∧
  (get_writes (ShareInst Load8 v _) = insert v () LN) ∧
  (get_writes (ShareInst Load16 v _) = insert v () LN) ∧
  (get_writes (ShareInst Load32 v _) = insert v () LN) ∧
  (get_writes prog = LN)
End

Theorem get_writes_pmatch:
  !inst.
  get_writes inst =
    pmatch inst of
    | Move pri ls => numset_list_insert (MAP FST ls) LN
    | Inst i => get_writes_inst i
    | Assign num exp => insert num () LN
    | Get num store => insert num () LN
    | LocValue r l1 => insert r () LN
    | Install r1 _ _ _ _ => insert r1 () LN
    | OpCurrHeap b r1 _ => insert r1 () LN
    | StoreConsts a b c d _ => insert a () (insert b () (insert c () (insert d () LN)))
    | ShareInst Load v _ => insert v () LN
    | ShareInst Load8 v _ => insert v () LN
    | ShareInst Load16 v _ => insert v () LN
    | ShareInst Load32 v _ => insert v () LN
    | prog => LN
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[get_writes_def]
QED

(* Old representation *)
(* Definition get_clash_sets_def:
  (get_clash_sets (Seq s1 s2) live =
    let (hd,ls) = get_clash_sets s2 live in
    let (hd',ls') = get_clash_sets s1 hd in
      (hd',(ls' ++ ls))) ∧
  (get_clash_sets (MustTerminate s1) live =
     get_clash_sets s1 live) ∧
  (get_clash_sets (If cmp r1 ri e2 e3) live =
    let (h2,ls2) = get_clash_sets e2 live in
    let (h3,ls3) = get_clash_sets e3 live in
    let union_live = union h2 h3 in
    let merged = case ri of Reg r2 => insert r2 () (insert r1 () union_live)
                      | _ => insert r1 () union_live in
      (merged,ls2++ls3)) ∧
  (get_clash_sets (Call(SOME(v,cutset,ret_handler,l1,l2))dest args h) live =
    (*top level*)
    let args_set = numset_list_insert args LN in
    let (hd,ls) = get_clash_sets ret_handler live in
    (*Outer liveset*)
    let live_set = union cutset args_set in
    (*Returning clash set*)
    let ret_clash = insert v () cutset in
    (case h of
      NONE => (live_set,ret_clash::hd::ls)
    | SOME(v',prog,l1,l2) =>
        let (hd',ls') = get_clash_sets prog live in
        (*Handler clash set*)
        let h_clash = insert v' () cutset in
        (live_set,h_clash::ret_clash::hd::hd'::ls++ls'))) ∧
  (*Catchall for cases where we dont have in sub programs live sets*)
  (get_clash_sets prog live =
    let i_set = union (get_writes prog) live in
      (get_live prog live,[i_set]))
  End
*)

(* Potentially more efficient liveset representation for checking / allocation*)
Definition get_delta_inst_def:
  (get_delta_inst Skip = Delta [] []) ∧
  (get_delta_inst (Const reg w) = Delta [reg] []) ∧
  (get_delta_inst (Arith (Binop bop r1 r2 ri)) =
    case ri of Reg r3 => Delta [r1] [r2;r3]
                  | _ => Delta [r1] [r2]) ∧
  (get_delta_inst (Arith (Shift shift r1 r2 n)) = Delta [r1] [r2]) ∧
  (get_delta_inst (Arith (Div r1 r2 r3)) = Delta [r1] [r3;r2]) ∧
  (get_delta_inst (Arith (AddCarry r1 r2 r3 r4)) = Delta [r1;r4] [r4;r3;r2]) ∧
  (get_delta_inst (Arith (AddOverflow r1 r2 r3 r4)) = Delta [r1;r4] [r3;r2]) ∧
  (get_delta_inst (Arith (SubOverflow r1 r2 r3 r4)) = Delta [r1;r4] [r3;r2]) ∧
  (get_delta_inst (Arith (LongMul r1 r2 r3 r4)) = Delta [r1;r2] [r4;r3]) ∧
  (get_delta_inst (Arith (LongDiv r1 r2 r3 r4 r5)) = Delta [r1;r2] [r5;r4;r3]) ∧
  (get_delta_inst (Mem Load r (Addr a w)) = Delta [r] [a]) ∧
  (get_delta_inst (Mem Store r (Addr a w)) = Delta [] [r;a]) ∧
  (get_delta_inst (Mem Load32 r (Addr a w)) = Delta [r] [a]) ∧
  (get_delta_inst (Mem Store32 r (Addr a w)) = Delta [] [r;a]) ∧
  (get_delta_inst (Mem Load8 r (Addr a w)) = Delta [r] [a]) ∧
  (get_delta_inst (Mem Store8 r (Addr a w)) = Delta [] [r;a]) ∧
  (get_delta_inst (FP (FPLess r f1 f2)) = Delta [r] []) ∧
  (get_delta_inst (FP (FPLessEqual r f1 f2)) = Delta [r] []) ∧
  (get_delta_inst (FP (FPEqual r f1 f2)) = Delta [r] []) ∧
  (get_delta_inst (FP (FPMovToReg r1 r2 d):'a inst) =
    if dimindex(:'a) = 64
      then Delta [r1] []
      else Delta [r1;r2] []) ∧
  (get_delta_inst (FP (FPMovFromReg d r1 r2)) =
    if dimindex(:'a) = 64
      then Delta [] [r1]
      else Delta [] [r1;r2]) ∧
  (*Catchall -- for future instructions to be added*)
  (get_delta_inst x = Delta [] [])
End

Definition get_reads_exp_def:
  (get_reads_exp (Var num) = [num]) ∧
  (get_reads_exp (Load exp) = get_reads_exp exp) ∧
  (get_reads_exp (Op wop ls) =
      FLAT (MAP get_reads_exp ls)) ∧
  (get_reads_exp (Shift sh exp nexp) = get_reads_exp exp) ∧
  (get_reads_exp expr = [])
End

Definition get_clash_tree_def:
  (get_clash_tree Skip = Delta [] []) ∧
  (get_clash_tree (Move pri ls) =
    Delta (MAP FST ls) (MAP SND ls)) ∧
  (get_clash_tree (Inst i) = get_delta_inst i) ∧
  (get_clash_tree (Assign num exp) = Delta [num] (get_reads_exp exp)) ∧
  (get_clash_tree (Get num store) = Delta [num] []) ∧
  (get_clash_tree (Store exp num) = Delta [] (num::get_reads_exp exp)) ∧
  (get_clash_tree (Seq s1 s2) = Seq (get_clash_tree s1) (get_clash_tree s2)) ∧
  (get_clash_tree (If cmp r1 ri e2 e3) =
    let e2t = get_clash_tree e2 in
    let e3t = get_clash_tree e3 in
    case ri of
      Reg r2 => Seq (Delta [] [r1;r2]) (Branch NONE e2t e3t)
    | _      => Seq (Delta [] [r1]) (Branch NONE e2t e3t)) ∧
  (get_clash_tree (MustTerminate s) =
    get_clash_tree s) ∧
  (get_clash_tree (Alloc num numset) =
    Seq (Delta [] [num]) (Set (union (FST numset) (SND numset)))) ∧
  (get_clash_tree (Install r1 r2 r3 r4 numset) =
    Seq (Delta [] [r4;r3;r2;r1]) (Seq (Set (union (FST numset) (SND numset))) (Delta [r1] []))) ∧
  (get_clash_tree (CodeBufferWrite r1 r2) =
    Delta [] [r2;r1]) ∧
  (get_clash_tree (DataBufferWrite r1 r2) =
    Delta [] [r2;r1]) ∧
  (get_clash_tree (FFI ffi_index ptr1 len1 ptr2 len2 numset) =
    Seq (Delta [] [ptr1;len1;ptr2;len2]) (Set (union (FST numset) (SND numset)))) ∧
  (get_clash_tree (Raise num) = Delta [] [num]) ∧
  (get_clash_tree (Return num1 nums) = Delta [] (num1::nums)) ∧
  (get_clash_tree Tick = Delta [] []) ∧
  (get_clash_tree (LocValue r l1) = Delta [r] []) ∧
  (get_clash_tree (Set n exp) = Delta [] (get_reads_exp exp)) ∧
  (get_clash_tree (OpCurrHeap b dst src) = Delta [dst] [src]) ∧
  (get_clash_tree (StoreConsts a b c d ws) = Delta [a;b;c;d] [c;d]) ∧
  (get_clash_tree (ShareInst op v exp) = if op = Store ∨ op = Store8 ∨ op = Store16 ∨ op = Store32
    then Delta [] (v::get_reads_exp exp)
    else Delta [v] $ get_reads_exp exp) ∧
  (get_clash_tree (Call ret dest args h) =
    let args_set = numset_list_insert args LN in
    case ret of
      NONE => Set args_set
    | SOME (vs,cutsets,ret_handler,_,_) =>
      let cutset = union (FST cutsets) (SND cutsets) in
      let live_set = union cutset args_set in
      (*Might be inefficient..*)
      let ret_tree = Seq (Set (numset_list_insert vs cutset)) (get_clash_tree ret_handler) in
      case h of
        NONE => Seq (Set live_set) ret_tree
      | SOME (v',prog,_,_) =>
        let handler_tree =
          Seq (Set (insert v' () cutset)) (get_clash_tree prog) in
        Branch (SOME live_set) ret_tree handler_tree)
End

(* Preference edges
  The allocator tries hard to coalesce these edges
*)
Definition get_prefs_def:
  (get_prefs (Move pri ls) acc = (MAP (λx,y. (pri,x,y)) ls) ++ acc) ∧
  (get_prefs (MustTerminate s1) acc =
    get_prefs s1 acc) ∧
  (get_prefs (Seq s1 s2) acc =
    get_prefs s1 (get_prefs s2 acc)) ∧
  (get_prefs (If cmp num rimm e2 e3) acc =
    get_prefs e2 (get_prefs e3 acc)) ∧
  (get_prefs (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) acc =
    case h of
      NONE => get_prefs ret_handler acc
    | SOME (v,prog,l1,l2) => get_prefs prog (get_prefs ret_handler acc)) ∧
  (get_prefs prog acc = acc)
End

Theorem get_prefs_pmatch:
  !s acc.
  get_prefs s acc =
    pmatch s of
    | (Move pri ls) => (MAP (λx,y. (pri,x,y)) ls) ++ acc
    | (MustTerminate s1) =>
    get_prefs s1 acc
    | (Seq s1 s2) =>
    get_prefs s1 (get_prefs s2 acc)
    | (If cmp num rimm e2 e3) =>
    get_prefs e2 (get_prefs e3 acc)
    | (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args NONE) =>
    get_prefs ret_handler acc
    | (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args (SOME (_,prog,_,_))) =>
    get_prefs prog (get_prefs ret_handler acc)
    | prog => acc
Proof
  rpt strip_tac
  >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
  >> rpt strip_tac
  >> every_case_tac
  >> fs [get_prefs_def]
  >- (rpt(POP_ASSUM MP_TAC)
  >> Q.SPEC_TAC (`acc`,`acc`) >> Q.SPEC_TAC (`s`,`s`)
  >> ho_match_mp_tac (theorem "get_prefs_ind")
  >> rpt strip_tac >> fs[Once get_prefs_def]
  >> every_case_tac >> metis_tac[pair_CASES])
QED

(*
  For each var, we collect 5 tuples indicating the number of
  instructions in which it is involved in:
    (lhs const,lhs reg,lhs memory, rhs reg, rhs memory)

  Currently, this just treats FP as a "reg" instruction

  This is meant to be small and quick to compute, because it has to be applied
  to the entire program just before register allocation, which can be huge.

*)

Type heu_data = ``:num#num#num#num#num``

val _ = Parse.hide"mem";

Definition add1_lhs_const_def:
  add1_lhs_const x (t: (heu_data num_map)) =
  case lookup x t of NONE =>
    insert x (1,0,0,0,0) t
  | SOME (const,reg,mem,rreg,rmem) =>
    insert x (const+1n,reg,mem,rreg,rmem) t
End

Definition add1_lhs_reg_def:
  add1_lhs_reg x (t: (heu_data num_map)) =
  case lookup x t of NONE =>
    insert x (0,1,0,0,0) t
  | SOME (const,reg,mem,rreg,rmem) =>
    insert x (const,reg+1,mem,rreg,rmem) t
End

Definition add1_lhs_mem_def:
  add1_lhs_mem x (t: (heu_data num_map)) =
  case lookup x t of NONE =>
    insert x (0,0,1,0,0) t
  | SOME (const,reg,mem,rreg,rmem) =>
    insert x (const,reg,mem+1,rreg,rmem) t
End

Definition add1_rhs_reg_def:
  add1_rhs_reg x (t: (heu_data num_map)) =
  case lookup x t of NONE =>
    insert x (0,0,0,1,0) t
  | SOME (const,reg,mem,rreg,rmem) =>
    insert x (const,reg,mem,rreg+1,rmem) t
End

Definition add1_rhs_mem_def:
  add1_rhs_mem x (t: (heu_data num_map)) =
  case lookup x t of NONE =>
    insert x (0,0,0,0,1) t
  | SOME (const,reg,mem,rreg,rmem) =>
    insert x (const,reg,mem,rreg,rmem+1) t
End

Definition get_heu_inst_def:
  (get_heu_inst Skip tup = tup) ∧
  (get_heu_inst (Const reg w) lr =
    (add1_lhs_const reg lr)) ∧
  (get_heu_inst (Arith (Binop bop r1 r2 ri)) lr =
    (case ri of
      Reg r3 => (* r1 := r2 op r3*)
        (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))
    | _ =>
        (add1_lhs_reg r1
        (add1_rhs_reg r2 lr)))) ∧
  (get_heu_inst (Arith (Shift shift r1 r2 n)) lr =
     (add1_lhs_reg r1
     (add1_rhs_reg r2 lr))) ∧
  (get_heu_inst (Arith (Div r1 r2 r3)) lr =
     (add1_lhs_reg r1
     (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))) ∧
  (get_heu_inst (Arith (AddCarry r1 r2 r3 r4)) lr =
    (*r1,r4 := r2,r3,r4 *)
     (add1_lhs_reg r4 (add1_lhs_reg r1
     (add1_rhs_reg r4 (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))))) ∧
  (get_heu_inst (Arith (AddOverflow r1 r2 r3 r4)) lr =
    (*r1,r4 := r2,r3 *)
     (add1_lhs_reg r4 (add1_lhs_reg r1
     (add1_rhs_reg r3 (add1_rhs_reg r2 lr))))) ∧
  (get_heu_inst (Arith (SubOverflow r1 r2 r3 r4)) lr =
    (*r1,r4 := r2,r3 *)
     (add1_lhs_reg r4 (add1_lhs_reg r1
     (add1_rhs_reg r3 (add1_rhs_reg r2 lr))))) ∧
  (get_heu_inst (Arith (LongMul r1 r2 r3 r4)) lr =
    (*r1,r2 := r3,r4 *)
     (add1_lhs_reg r2 (add1_lhs_reg r1
     (add1_rhs_reg r4 (add1_rhs_reg r3 lr))))) ∧
  (get_heu_inst (Arith (LongDiv r1 r2 r3 r4 r5)) lr =
    (*r1,r2 := r3,r4,r5 *)
     (add1_lhs_reg r2 (add1_lhs_reg r1
     (add1_rhs_reg r5 (add1_rhs_reg r4 (add1_rhs_reg r3 lr)))))) ∧
  (get_heu_inst (Mem Load r (Addr a w)) lr =
     (add1_lhs_mem r lr)) ∧
  (get_heu_inst (Mem Store r (Addr a w)) lr =
     (add1_rhs_mem r lr)) ∧
  (get_heu_inst (Mem Load32 r (Addr a w)) lr =
     (add1_lhs_mem r lr)) ∧
  (get_heu_inst (Mem Load8 r (Addr a w)) lr =
     (add1_lhs_mem r lr)) ∧
  (get_heu_inst (Mem Store32 r (Addr a w)) lr =
     (add1_rhs_mem r lr)) ∧
  (get_heu_inst (Mem Store8 r (Addr a w)) lr =
     (add1_rhs_mem r lr)) ∧
  (get_heu_inst (FP (FPLess r f1 f2)) lr =
     (add1_lhs_reg r lr)) ∧
  (get_heu_inst (FP (FPLessEqual r f1 f2)) lr =
     (add1_lhs_reg r lr)) ∧
  (get_heu_inst (FP (FPEqual r f1 f2)) lr =
     (add1_lhs_reg r lr)) ∧
  (get_heu_inst (FP (FPMovToReg r1 r2 d):'a inst) lr =
     (add1_lhs_reg r2 (add1_lhs_reg r1 lr))) ∧
  (get_heu_inst (FP (FPMovFromReg d r1 r2)) lr =
     (add1_rhs_reg r2 (add1_rhs_reg r1 lr))) ∧
  (*Catchall -- for future instructions to be added, and all other FP *)
  (get_heu_inst x lr = lr)
End

(* For Ifs, as a heuristic we take the max over branching paths *)
Definition heu_max_def:
  heu_max (c1,r1,m1,rr1,rm1) (c2,r2,m2,rr2,rm2) =
    (MAX c1 c2, MAX r1 r2, MAX m1 m2,MAX rr1 rr2, MAX rm1 rm2)
End

Definition heu_max_all_def:
  heu_max_all t1 t2 =
  let t1r = difference t1 t2 in (*everything in t1 not already in t2*)
  union
  t1r
  (mapi (λk v.
    case lookup k t1 of
      NONE => v
    | SOME v' => heu_max v v') t2)
End

Definition heu_merge_call_def:
  heu_merge_call (t1:num_set) t2 =
  union t1 t2
End

(* We use "lr" to approximate any new vars not already tracked in calls *)
Definition add_call_def:
  add_call lr calls:num_set =
  union (map (λv. ()) lr) calls
End

Definition get_heu_def:
  (get_heu fc (Move pri ls) (lr,calls) =
    (FOLDR add1_lhs_reg
    (FOLDR add1_rhs_reg lr (MAP SND ls))
    (MAP FST ls) ,calls)) ∧
  (get_heu fc (Inst i) (lr,calls) = (get_heu_inst i lr,calls)) ∧
  (get_heu fc (Get num store) (lr,calls) =
    (add1_lhs_mem num lr,calls)) ∧
  (get_heu fc (Set _ exp) (lr,calls) =
    (case exp of (Var r) =>
       (add1_rhs_mem r lr,calls)
    | _ => (lr,calls))) ∧ (* General Set exp ignored *)
  (get_heu fc (OpCurrHeap b dst src) (lr,calls) =
    (add1_lhs_reg dst (add1_rhs_reg src lr),calls)) ∧
  (get_heu fc (LocValue r l1) (lr,calls) =
    (add1_lhs_reg r lr,calls)) ∧
  (get_heu fc (Seq s1 s2) lr = get_heu fc s2 (get_heu fc s1 lr)) ∧
  (get_heu fc (MustTerminate s1) lr = get_heu fc s1 lr) ∧
  (get_heu fc (If cmp r1 ri e2 e3) lr =
    let (lr2,calls2) = get_heu fc e2 lr in
    let (lr3,calls3) = get_heu fc e3 lr in
    let lr = heu_max_all lr2 lr3 in
    let calls = heu_merge_call (calls2:num_set) calls3 in
    ((case ri of
      Reg r2 => add1_rhs_reg r1 (add1_rhs_reg r2 lr)
    | _ =>
      add1_rhs_reg r1 lr),calls)) ∧
  (get_heu fc (Call NONE dest args h) (lr,calls) =
    case dest of
      NONE => (lr,calls)
    | SOME p =>
      if p = fc then (lr,add_call lr calls)
      else (lr,calls)
    ) ∧
  (get_heu fc (Call (SOME (_,_,e2,_,_)) dest args h) (lr,calls) =
    let calls =
      case dest of NONE => calls
      | SOME p =>
        if p = fc then (add_call lr calls)
        else calls in
    let (lr2,calls2) = (get_heu fc e2 (lr,calls)) in
    case h of
      NONE => (lr2,calls)
    | SOME (_,e3,_,_) =>
      let (lr3,calls3) = get_heu fc e3 (lr,calls) in
      (heu_max_all lr2 lr3, heu_merge_call calls2 calls3)) ∧
  (get_heu fs (ShareInst Load r _) (lr,calls) = (add1_lhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Load8 r _) (lr,calls) = (add1_lhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Load16 r _) (lr,calls) = (add1_lhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Load32 r _) (lr,calls) = (add1_lhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Store r _) (lr,calls) = (add1_rhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Store8 r _) (lr,calls) = (add1_rhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Store16 r _) (lr,calls) = (add1_rhs_mem r lr,calls)) ∧
  (get_heu fs (ShareInst Store32 r _) (lr,calls) = (add1_rhs_mem r lr,calls)) ∧
  (* The remaining ones are exps, or otherwise unimportant from the
  pov of register allocation, since all their temps are already forced into
  specific registers
  Omitted: Skip, Assign, Store, FFI, Alloc, Raise, Tick, Call NONE*)
  (get_heu fc f lrc = lrc)
End

(* Forced edges for certain instructions *)
Definition get_forced_def:
  (get_forced (c:'a asm_config) ((Inst i):'a prog) acc =
    case i of
      Arith (AddCarry r1 r2 r3 r4) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          (if r1=r4 then [] else [(r1,r4)]) ++
          acc
       else acc
    | Arith (AddOverflow r1 r2 r3 r4) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          acc
       else acc
    | Arith (SubOverflow r1 r2 r3 r4) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          acc
       else acc
    | Arith (LongMul r1 r2 r3 r4) =>
       if (c.ISA = ARMv7) then
         (if (r1=r2) then [] else [(r1,r2)]) ++ acc
       else if (c.ISA = ARMv8) \/ (c.ISA = RISC_V) \/ (c.ISA = Ag32) then
         (if r1=r3 then [] else [(r1,r3)]) ++
         (if r1=r4 then [] else [(r1,r4)]) ++
         acc
       else
         acc
    | FP (FPMovToReg r1 r2 d) =>
        (if dimindex(:'a) = 32 ∧ r1 ≠ r2 then [(r1,r2)]
        else []) ++ acc
    | FP (FPMovFromReg d r1 r2) =>
        (if dimindex(:'a) = 32 ∧ r1 ≠ r2 then [(r1,r2)]
        else []) ++ acc
    | _ => acc) ∧
  (get_forced c (MustTerminate s1) acc =
    get_forced c s1 acc) ∧
  (get_forced c (Seq s1 s2) acc =
    get_forced c s1 (get_forced c s2 acc)) ∧
  (get_forced c (If cmp num rimm e2 e3) acc =
    get_forced c e2 (get_forced c e3 acc)) ∧
  (get_forced c (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) acc =
    case h of
      NONE => get_forced c ret_handler acc
    | SOME (v,prog,l1,l2) => get_forced c prog (get_forced c ret_handler acc)) ∧
  (get_forced c prog acc = acc)
End

Theorem get_forced_pmatch:
  !c prog acc.
  (get_forced (c:'a asm_config) prog acc =
    pmatch prog of
      Inst(Arith (AddCarry r1 r2 r3 r4)) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          (if r1=r4 then [] else [(r1,r4)]) ++
          acc
       else acc
    | Inst(Arith (AddOverflow r1 r2 r3 r4)) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          acc
       else acc
    | Inst(Arith (SubOverflow r1 r2 r3 r4)) =>
       if (c.ISA = MIPS ∨ c.ISA = RISC_V) then
          (if r1=r3 then [] else [(r1,r3)]) ++
          acc
       else acc
    | Inst(Arith (LongMul r1 r2 r3 r4)) =>
       if (c.ISA = ARMv7) then
         (if (r1=r2) then [] else [(r1,r2)]) ++ acc
       else if (c.ISA = ARMv8) \/ (c.ISA = RISC_V) \/ (c.ISA = Ag32) then
         (if r1=r3 then [] else [(r1,r3)]) ++
         (if r1=r4 then [] else [(r1,r4)]) ++
         acc
       else
         acc
    | Inst (FP (FPMovToReg r1 r2 d)) =>
        (if dimindex(:'a) = 32 ∧ r1 ≠ r2 then [(r1,r2)]
        else []) ++ acc
    | Inst (FP (FPMovFromReg d r1 r2)) =>
        (if dimindex(:'a) = 32 ∧ r1 ≠ r2 then [(r1,r2)]
        else []) ++ acc
    | MustTerminate s1 => get_forced c s1 acc
    | Seq s1 s2 => get_forced c s1 (get_forced c s2 acc)
    | If cmp num rimm e2 e3 =>
      get_forced c e2 (get_forced c e3 acc)
    | Call (SOME (v,cutset,ret_handler,l1,l2)) dest args NONE =>
      get_forced c ret_handler acc
    | Call (SOME (v,cutset,ret_handler,l1,l2)) dest args (SOME (_,prog,_,_)) =>
      get_forced c prog (get_forced c ret_handler acc)
    | _ => acc)
Proof
  rpt strip_tac
  >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
  >> rpt strip_tac
  >> every_case_tac
  >> fs[get_forced_def]
  >> rpt(POP_ASSUM MP_TAC)
  >> (fn (asms,g) => (asms,g) |> EVERY(map UNDISCH_TAC asms))
  >> Q.SPEC_TAC (`acc`,`acc`) >> Q.SPEC_TAC (`prog`,`prog`) >> Q.SPEC_TAC (`c`,`c`)
  >> ho_match_mp_tac (theorem "get_forced_ind")
  >> rpt strip_tac
  >> fs[get_forced_def]
  >> every_case_tac
  >> fs[]
  >> metis_tac[pair_CASES]
QED

(*col is injective over every cut set*)
Definition check_colouring_ok_alt_def:
  (check_colouring_ok_alt col [] = T) ∧
  (check_colouring_ok_alt col (x::xs) ⇔
    let names = MAP (col o FST) (toAList x) in
      ALL_DISTINCT names ∧ check_colouring_ok_alt col xs)
End

Definition every_even_colour_def:
  every_even_colour col ⇔
  EVERY (λ(x,y). if is_phy_var x then y = x DIV 2 else T) (toAList col)
End

(*Extract a colouring function from the generated sptree*)
Definition total_colour_def:
  total_colour col x =
    case lookup x col of NONE => if is_phy_var x then x else 0 | SOME x => 2*x
End

Theorem total_colour_alt:
  total_colour col = (\x. 2 * x) o (sp_default col)
Proof
  rw[FUN_EQ_THM]>>fs[total_colour_def,sp_default_def,lookup_any_def]>>
  TOP_CASE_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS,TWOxDIV2]
QED

(*Check that the oracle provided colour (if it exists) is okay*)
Definition oracle_colour_ok_def:
  oracle_colour_ok k col_opt tree prog ls ⇔
  case col_opt of
    NONE => NONE
  | SOME col =>
     let tcol = total_colour col in
     if (every_even_colour col ∧ check_clash_tree tcol tree LN LN ≠ NONE)
     then
       let prog = apply_colour tcol prog in
       if
         (* Note: possibly avoid these checks and instead check the oracle domain directly *)
         (*every_var is_phy_var prog ∧*)
         every_stack_var (λx. x ≥ 2*k) prog ∧
         EVERY (λ(x,y). (tcol x) ≠ (tcol y)) ls
       then
         SOME prog
       else
         NONE
     else NONE
End

(* Returns
  1) a lookup table
    v -> "spill cost"
  2) the move list, with associated priorities

  For now, the spill cost metric is just 6 magic numbers
*)
(*
  Canonize by flipping moves (all move x<=y)
  Filter some obviously impossible ones out
  Then SORT them by lexicographic order, and count
  returns (num, maxpriority, (x,y))
*)
Definition canonize_moves_aux_def:
  (canonize_moves_aux curp curm ctr [] acc = (ctr,curp,curm)::acc) ∧
  (canonize_moves_aux curp curm ctr ((p,m)::xs) acc =
    if curm = m then
      canonize_moves_aux (MAX curp p) m (ctr+1n) xs acc
    else
      canonize_moves_aux p m 1 xs ((ctr,curp,curm)::acc))
End

Definition canonize_moves_def:
  canonize_moves ls =
  let can1 = MAP (λ(p:num,(x:num,y:num)). if (x<=y) then (p,(x,y)) else (p,(y,x))) ls in
  let can2 = sort
    (λ(p1,(x1,y1)) (p2,(x2,y2)).
      if x1 = x2 then
        if y1 = y2 then
          p1 < p2
        else y1 < y2
      else x1 < x2) can1 in
  case can2 of [] => []
  | ((p,m)::xs) => canonize_moves_aux p m 1 xs []
End

(* TODO: ALL of these magic numbers must be adjusted!! *)

Definition get_spillcost_def:
  get_spillcost (c,lr,lm,rr,rm) istail =
  (c + 2*lr + 4*lm + 2*rr + 4 * rm) *
  if istail then 5 else 1n
End

(*
  Prioritize moves that happen a lot, and have high max priority
  also give some weight to the spill cost of their endpoints
*)
Definition get_coalescecost_def:
  get_coalescecost spillcost (n,p,(x,y))=
  let xcost = if lookup x spillcost = NONE then 0 else 1 in
  let ycost = if lookup y spillcost = NONE then 0 else 1n in
  (n * (10 * (p+1) + xcost + ycost),(x,y))
End

Definition get_heuristics_def:
  get_heuristics alg fc prog =
  if alg MOD 2n = 1n then
    let (lr,calls) = get_heu fc prog (LN,LN) in
    let moves = get_prefs prog [] in
    let spillcosts = mapi (λk v. get_spillcost v (lookup k calls = NONE)) lr in
    let canon_moves = canonize_moves moves in
    let heu_moves = MAP (get_coalescecost spillcosts) canon_moves in
    (heu_moves,SOME spillcosts)
  else
    let moves = get_prefs prog [] in
    (moves,NONE)
End

Definition select_reg_alloc_def:
  select_reg_alloc alg spillcosts k heu_moves tree forced fs =
    if 4 <= alg then
      linear_scan$linear_scan_reg_alloc k heu_moves tree forced
    else
      reg_alloc (if alg <= 1n then Simple else IRC) spillcosts k heu_moves tree forced fs
End

(* For a move x <- y
  if x is a register, then y should not be forced stack
  else,
    if y is a stack variable or forced stack,
    then we mark x as forced stack as well
*)
Definition merge_stack_only_def:
  merge_stack_only (x,y) (ts,fs) =
  if lookup x ts = SOME ()
  then
    let ts = if is_alloc_var y then insert y () ts else ts in
    let fs = if is_phy_var y then fs else insert x () fs in
    (ts, fs)
  else
    if is_stack_var x
    then
      let ts = if is_alloc_var y then insert y () ts else ts in
      (ts, fs)
    else
      (delete y ts, fs)
End

Definition merge_stack_sets_def:
  merge_stack_sets (ts,fs) (tsL,fsL) (tsR,fsR) =
  let keep1 = inter tsR (inter tsL ts) in
  let keep2 = union (difference tsL ts) (difference tsR ts) in
    (union keep1 keep2, union fsL fsR)
End

Definition remove_temp_stack_def:
  remove_temp_stack ls (ts,fs) =
    (FOLDR delete ts ls,fs)
End

(* Alloc variables that are already stack or
  only ever involved in stack moves *)
Definition get_stack_only_aux_def:
  (get_stack_only_aux tfs (Move pri ls) =
    FOLDR merge_stack_only tfs ls) ∧
  (get_stack_only_aux tfs (Seq s1 s2) =
    get_stack_only_aux (get_stack_only_aux tfs s2) s1) ∧
  (get_stack_only_aux tfs (If cmp r1 ri e2 e3) =
    let tfsL = get_stack_only_aux tfs e2 in
    let tfsR = get_stack_only_aux tfs e3 in
    let tfsM = merge_stack_sets tfs tfsL tfsR in
      case ri of
        Reg r2 => remove_temp_stack [r1;r2] tfsM
      | _ => remove_temp_stack [r1] tfsM
  ) ∧
  (get_stack_only_aux tfs (MustTerminate s) =
    get_stack_only_aux tfs s) ∧
  (get_stack_only_aux tfs (Call ret dest args h) =
    (case ret of
      NONE => tfs
    | SOME (v,cutset,ret_handler,_,_) =>
      let rettfs = get_stack_only_aux tfs ret_handler in
      case h of
        NONE => rettfs
      | SOME (v',handler,_,_) =>
        let handlertfs =
          get_stack_only_aux tfs handler in
        merge_stack_sets tfs rettfs handlertfs)) ∧
  (get_stack_only_aux tfs prog =
    case get_clash_tree prog of
      Delta ws rs => remove_temp_stack (ws++rs) tfs
    | _ => tfs)
End

Definition get_stack_only_def:
  get_stack_only prog = SND (get_stack_only_aux (LN,LN) prog)
End

(*
  fc is the current prog number
  alg is the allocation algorithm,
    0: simple allocator, no spill heuristics
    1: simple allocator + spill heuristics
    2: IRC allocator, no spill heuristics (default)
    3: IRC allocator + spill heuristics
  >=4: linear scan register allocator
  k is the number of registers
  prog is the program to be colored
  col_opt is an optional oracle colour
*)
Definition word_alloc_def:
  word_alloc fc c alg k prog col_opt =
  let tree = get_clash_tree prog in
  let fs = get_stack_only prog in
  (*let moves = get_prefs_sp prog [] in*)
  let forced = get_forced c prog [] in
  case oracle_colour_ok k col_opt tree prog forced of
    NONE =>
      let (heu_moves,spillcosts) = get_heuristics alg fc prog in
      (case select_reg_alloc alg spillcosts k heu_moves tree forced fs of
        M_success col =>
          apply_colour (total_colour col) prog
      | M_failure _ => prog (*cannot happen*))
  | SOME col_prog =>
      col_prog
End

(*The initial move, ssa and limit vars*)
Definition setup_ssa_def:
  setup_ssa n lim (prog:'a wordLang$prog) =
  let args = even_list n in
  let (new_ls,ssa',n') = list_next_var_rename args LN lim in
    (Move1 (ZIP(new_ls,args)),ssa',n')
End

Definition limit_var_def:
  limit_var prog =
    let x = max_var prog in
    x + (4 - (x MOD 4)) +1
End

Definition full_ssa_cc_trans_def:
  full_ssa_cc_trans n prog =
    let lim = limit_var prog in
    let (mov,ssa,na) = setup_ssa n lim prog in
    let (prog',ssa',na') = ssa_cc_trans prog ssa na in
      Seq mov prog'
End
