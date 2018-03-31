open preamble wordLangTheory reg_allocTheory

val _ = new_theory "word_alloc";
val _ = set_grammar_ancestry [
  "asm" (* for arity-2 Const *),
  "reg_alloc",
  "misc",
  "wordLang"
]
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(*Defines the algorithms related to the register allocator, currently:
0) Syntactic forms before and after allocation
1) SSA form
2) Colouring and Liveness Analysis
3) Combined passes
*)

(*SSA form*)
val apply_nummap_key_def = Define`
  apply_nummap_key f names =
  fromAList (MAP (λx,y.f x,y) (toAList names))`

val option_lookup_def = Define`
  option_lookup t v = dtcase lookup v t of NONE => 0n | SOME x => x`

val even_list_def = Define `
  (even_list = GENLIST (\x.2*x))`

(*Consistently sets up the next alloc variable rename for v*)
val next_var_rename_def = Define`
  next_var_rename v ssa (na:num) = (na,insert v na ssa,na+4)`

val list_next_var_rename_def = Define`
  (list_next_var_rename [] ssa (na:num) = ([],ssa,na)) ∧
  (list_next_var_rename (x::xs) ssa na =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ssa',na') = next_var_rename x ssa na in
    let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
      (y::ys,ssa'',na''))`

val fake_move_def = Define`
  fake_move v : α wordLang$prog = Inst (Const v 0w)`

(*Do the merging moves only*)
val merge_moves_def = Define`
  (merge_moves [] ssa_L ssa_R (na:num) = ([],[],na,ssa_L,ssa_R)) ∧
  (merge_moves (x::xs) ssa_L ssa_R na =
    let (seqL,seqR,na',ssa_L',ssa_R') =
      merge_moves xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    dtcase (optLx,optLy) of
      (SOME Lx,SOME Ly) =>
      if Lx = Ly then
        (seqL,seqR,na',ssa_L',ssa_R')
      else
        let Lmove = (na',Lx) in
        let Rmove = (na',Ly) in
        (Lmove::seqL, Rmove::seqR,na'+4, insert x na' ssa_L'
                                       , insert x na' ssa_R')
    | _ => (seqL,seqR,na',ssa_L',ssa_R'))`

(*Separately do the fake moves*)
val fake_moves_def = Define`
  (fake_moves [] ssa_L ssa_R (na:num) = (Skip:'a wordLang$prog,Skip:'a wordLang$prog,na,ssa_L,ssa_R)) ∧
  (fake_moves (x::xs) ssa_L ssa_R na =
    let (seqL,seqR,na',ssa_L',ssa_R') =
      fake_moves xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    dtcase (optLx,optLy) of
      (NONE,SOME Ly) =>
        let Lmove = Seq seqL (fake_move na') in
        let Rmove = Seq seqR (Move 1 [(na',Ly)]) in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | (SOME Lx,NONE) =>
        let Lmove = Seq seqL (Move 1 [(na',Lx)]) in
        let Rmove = Seq seqR (fake_move na') in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | _ => (seqL,seqR,na',ssa_L',ssa_R'))`

val fix_inconsistencies_def = Define`
  fix_inconsistencies ssa_L ssa_R na =
  let var_union = MAP FST (toAList (union ssa_L ssa_R)) in
  let (Lmov,Rmov,na',ssa_L',ssa_R') =
    merge_moves var_union ssa_L ssa_R na in
  let (Lseq,Rseq,na'',ssa_L'',ssa_R'') =
    fake_moves var_union ssa_L' ssa_R' na' in
    (Seq (Move 1 Lmov) Lseq,Seq (Move 1 Rmov) Rseq,na'',ssa_L'')`

(*ssa_cc_trans_inst does not need to interact with stack*)
(* Note: this needs to return a prog to support specific registers for AddCarry and other special insts
*)
val ssa_cc_trans_inst_def = Define`
  (ssa_cc_trans_inst Skip ssa na = (Skip,ssa,na)) ∧
  (ssa_cc_trans_inst (Const reg w) ssa na =
    let (reg',ssa',na') = next_var_rename reg ssa na in
      (Inst (Const reg' w),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Binop bop r1 r2 ri)) ssa na =
    dtcase ri of
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
    let mov_in = Move 0 [(0,r4')] in
    let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
    let mov_out = Move 0 [(r4'',0)] in
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
    let mov_out = Move 0 [(r4'',0)] in
      (Seq (Inst (Arith (AddOverflow r1' r2' r3' 0))) mov_out, ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (SubOverflow r1 r2 r3 r4)) ssa na =
    let r2' = option_lookup ssa r2 in
    let r3' = option_lookup ssa r3 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
    let mov_out = Move 0 [(r4'',0)] in
      (Seq (Inst (Arith (SubOverflow r1' r2' r3' 0))) mov_out, ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (LongMul r1 r2 r3 r4)) ssa na =
    let r3' = option_lookup ssa r3 in
    let r4' = option_lookup ssa r4 in
    let mov_in = Move 0 [(0,r3');(4,r4')] in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
    let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
    let mov_out = Move 0 [(r2',0);(r1',6)] in
      (Seq mov_in  (Seq (Inst (Arith (LongMul 6 0 0 4))) mov_out),ssa'',na'')) ∧
  (ssa_cc_trans_inst (Arith (LongDiv r1 r2 r3 r4 r5)) ssa na =
    let r3' = option_lookup ssa r3 in
    let r4' = option_lookup ssa r4 in
    let r5' = option_lookup ssa r5 in
    let mov_in = Move 0 [(6,r3');(0,r4')] in
    let (r2',ssa',na') = next_var_rename r2 ssa na in
    let (r1',ssa'',na'') = next_var_rename r1 ssa' na' in
    let mov_out = Move 0 [(r2',6);(r1',0)] in
      (Seq mov_in  (Seq (Inst (Arith (LongDiv 0 6 6 0 r5'))) mov_out),ssa'',na'')) ∧
  (ssa_cc_trans_inst (Mem Load r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Inst (Mem Load r' (Addr a' w)),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Store r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Inst (Mem Store r' (Addr a' w)),ssa,na)) ∧
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
    let r1' = option_lookup ssa r1 in
    let r2' = (dtcase lookup r2 ssa of NONE => 4 | SOME v => v) in
      (Inst (FP (FPMovFromReg d r1' r2')),ssa,na)) ∧
  (*Catchall -- for future instructions to be added, and all other FP *)
  (ssa_cc_trans_inst x ssa na = (Inst x,ssa,na))`

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
val ssa_cc_trans_exp_def = tDefine "ssa_cc_trans_exp" `
  (ssa_cc_trans_exp t (Var num) =
    Var (option_lookup t num)) ∧
  (ssa_cc_trans_exp t (Load exp) = Load (ssa_cc_trans_exp t exp)) ∧
  (ssa_cc_trans_exp t (Op wop ls) =
    Op wop (MAP (ssa_cc_trans_exp t) ls)) ∧
  (ssa_cc_trans_exp t (Shift sh exp nexp) =
    Shift sh (ssa_cc_trans_exp t exp) nexp) ∧
  (ssa_cc_trans_exp t expr = expr)`
  (WF_REL_TAC `measure (exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*Attempt to pull out "renaming" moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
val list_next_var_rename_move_def = Define`
  list_next_var_rename_move ssa n ls =
    let cur_ls = MAP (option_lookup ssa) ls in
    let (new_ls,ssa',n') = list_next_var_rename ls ssa n in
    (Move 1 (ZIP(new_ls,cur_ls)),ssa',n')`

val ssa_cc_trans_def = Define`
  (ssa_cc_trans Skip ssa na = (Skip,ssa,na)) ∧
  (ssa_cc_trans (Move pri ls) ssa na =
    let ls_1 = MAP FST ls in
    let ls_2 = MAP SND ls in
    let ren_ls2 = MAP (option_lookup ssa) ls_2 in
    let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
      (Move pri (ZIP(ren_ls1,ren_ls2)),ssa',na')) ∧
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
  (*Tricky case 1: we need to merge the ssa results from both branches by
    unSSA-ing the phi functions
  *)
  (ssa_cc_trans (If cmp r1 ri e2 e3) ssa na =
    let r1' = option_lookup ssa r1 in
    let ri' = dtcase ri of Reg r => Reg (option_lookup ssa r)
                      |  Imm v => Imm v in
    (*ssa is the copy for both branches,
      however, we can use new na2 and ns2*)
    let (e2',ssa2,na2) = ssa_cc_trans e2 ssa na in
    (*ssa2 is the ssa map for the first branch*)
    let (e3',ssa3,na3) = ssa_cc_trans e3 ssa na2 in
    (*ssa3 is the ssa map for the second branch, notice we
      continued using na2 here though!*)
    let (e2_cons,e3_cons,na_fin,ssa_fin) =
      fix_inconsistencies ssa2 ssa3 na3 in
    (If cmp r1' ri' (Seq e2' e2_cons) (Seq e3' e3_cons),ssa_fin,na_fin)) ∧
  (*For cutsets, we must restart the ssa mapping to maintain consistency*)
  (ssa_cc_trans (Alloc num numset) ssa na =
    let ls = MAP FST (toAList numset) in
    (*This trick allows us to not keep the "next stack" variable by
      simply starting from the next available stack location
      Assuming na is an alloc var of course..*)
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let num' = option_lookup ssa' num in
    let stack_set = apply_nummap_key (option_lookup ssa') numset in
    (*Restart the ssa map*)
    let ssa_cut = inter ssa' numset in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    let prog = (Seq (stack_mov)
               (Seq (Move 0 [(2,num')])
               (Seq (Alloc 2 stack_set) (ret_mov)))) in
    (prog,ssa'',na'')) ∧
  (ssa_cc_trans (Raise num) ssa na =
    let num' = option_lookup ssa num in
    let mov = Move 0 [(2,num')] in
    (Seq mov (Raise 2),ssa,na)) ∧
  (ssa_cc_trans (Return num1 num2) ssa na=
    let num1' = option_lookup ssa num1 in
    let num2' = option_lookup ssa num2 in
    let mov = Move 0 [(2,num2')] in
    (Seq mov (Return num1' 2),ssa,na)) ∧
  (ssa_cc_trans Tick ssa na = (Tick,ssa,na)) ∧
  (ssa_cc_trans (Set n exp) ssa na =
    let exp' = ssa_cc_trans_exp ssa exp in
    (Set n exp',ssa,na)) ∧
  (ssa_cc_trans (LocValue r l1) ssa na =
    let (r',ssa',na') = next_var_rename r ssa na in
      (LocValue r' l1,ssa',na')) ∧
  (ssa_cc_trans (FFI ffi_index ptr1 len1 ptr2 len2 numset) ssa na =
    let ls = MAP FST (toAList numset) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummap_key (option_lookup ssa') numset in
    let cptr1 = option_lookup ssa' ptr1 in
    let clen1 = option_lookup ssa' len1 in
    let cptr2 = option_lookup ssa' ptr2 in
    let clen2 = option_lookup ssa' len2 in
    let ssa_cut = inter ssa' numset in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    let prog = (Seq (stack_mov)
               (Seq (Move 0 [(2,cptr1);(4,clen1);(6,cptr2);(8,clen2)])
               (Seq (FFI ffi_index 2 4 6 8 stack_set) (ret_mov)))) in
    (prog,ssa'',na'')) ∧
  (ssa_cc_trans (Call NONE dest args h) ssa na =
    let names = MAP (option_lookup ssa) args in
    let conv_args = GENLIST (\x.2*x) (LENGTH names) in
    let move_args = (Move 0 (ZIP (conv_args,names))) in
    let prog = Seq move_args (Call NONE dest conv_args h) in
      (prog,ssa,na)) ∧
  (ssa_cc_trans (Call (SOME(ret,numset,ret_handler,l1,l2)) dest args h) ssa na =
    let ls = MAP FST (toAList numset) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummap_key (option_lookup ssa') numset in
    let names = MAP (option_lookup ssa) args in
    let conv_args = GENLIST (\x.2*(x+1)) (LENGTH names) in
    let move_args = (Move 0 (ZIP (conv_args,names))) in
    let ssa_cut = inter ssa' numset in
    let (ret_mov,ssa'',na'') =
      list_next_var_rename_move ssa_cut (na'+2) ls in
    (*ret_mov restores the cutset*)
    (*This recurses on the returning handler*)
    let (ret',ssa_2_p,na_2_p) = next_var_rename ret ssa'' na'' in
    let (ren_ret_handler,ssa_2,na_2) =
      ssa_cc_trans ret_handler ssa_2_p na_2_p in
    let mov_ret_handler =
        (Seq ret_mov (Seq (Move 0 [ret',2]) (ren_ret_handler))) in
    (dtcase h of
      NONE =>
        let prog =
          (Seq stack_mov (Seq move_args
          (Call (SOME(2,stack_set,mov_ret_handler,l1,l2))
                dest conv_args NONE))) in
        (prog,ssa_2,na_2)
    | SOME(n,h,l1',l2') =>
        let (n',ssa_3_p,na_3_p) = next_var_rename n ssa'' na_2 in
        let (ren_exc_handler,ssa_3,na_3) =
            (ssa_cc_trans h ssa_3_p na_3_p) in
        let mov_exc_handler =
            (Seq ret_mov (Seq(Move 0 [n',2]) (ren_exc_handler))) in
        let (ret_cons,exc_cons,na_fin,ssa_fin) =
            fix_inconsistencies ssa_2 ssa_3 na_3 in
        let cons_ret_handler = Seq mov_ret_handler ret_cons in
        let cons_exc_handler = Seq mov_exc_handler exc_cons in
        let prog =
            (Seq stack_mov (Seq move_args
            (Call (SOME(2,stack_set,cons_ret_handler,l1,l2))
               dest conv_args (SOME(2,cons_exc_handler,l1',l2'))))) in
        (prog,ssa_fin,na_fin)))`

(*Recursively applying colours to a program*)

val apply_colour_exp_def = tDefine "apply_colour_exp" `
  (apply_colour_exp f (Var num) = Var (f num)) /\
  (apply_colour_exp f (Load exp) = Load (apply_colour_exp f exp)) /\
  (apply_colour_exp f (Op wop ls) = Op wop (MAP (apply_colour_exp f) ls)) /\
  (apply_colour_exp f (Shift sh exp nexp) = Shift sh (apply_colour_exp f exp) nexp) /\
  (apply_colour_exp f expr = expr)`
(WF_REL_TAC `measure (exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC);

val apply_colour_imm_def = Define`
  (apply_colour_imm f (Reg n) = Reg (f n)) ∧
  (apply_colour_imm f x = x)`

val apply_colour_inst_def = Define`
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
  (apply_colour_inst f (Mem Load8 r (Addr a w)) =
    Mem Load8 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Store8 r (Addr a w)) =
    Mem Store8 (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (FP (FPLess r f1 f2)) = FP (FPLess (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPLessEqual r f1 f2)) = FP (FPLessEqual (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPEqual r f1 f2)) = FP (FPEqual (f r) f1 f2)) ∧
  (apply_colour_inst f (FP (FPMovToReg r1 r2 d)) = FP (FPMovToReg (f r1) (f r2) d)) ∧
  (apply_colour_inst f (FP (FPMovFromReg d r1 r2)) = FP (FPMovFromReg d (f r1) (f r2))) ∧
  (apply_colour_inst f x = x)` (*Catchall -- for future instructions to be added*)

val apply_colour_def = Define `
  (apply_colour f Skip = Skip) ∧
  (apply_colour f (Move pri ls) =
    Move pri (ZIP (MAP (f o FST) ls, MAP (f o SND) ls))) ∧
  (apply_colour f (Inst i) = Inst (apply_colour_inst f i)) ∧
  (apply_colour f (Assign num exp) = Assign (f num) (apply_colour_exp f exp)) ∧
  (apply_colour f (Get num store) = Get (f num) store) ∧
  (apply_colour f (Store exp num) = Store (apply_colour_exp f exp) (f num)) ∧
  (apply_colour f (Call ret dest args h) =
    let ret = dtcase ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (f v,apply_nummap_key f cutset,apply_colour f ret_handler,l1,l2) in
    let args = MAP f args in
    let h = dtcase h of NONE => NONE
                     | SOME (v,prog,l1,l2) => SOME (f v, apply_colour f prog,l1,l2) in
      Call ret dest args h) ∧
  (apply_colour f (Seq s1 s2) = Seq (apply_colour f s1) (apply_colour f s2)) ∧
  (apply_colour f (MustTerminate s1) = MustTerminate (apply_colour f s1)) ∧
  (apply_colour f (If cmp r1 ri e2 e3) =
    If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)) ∧
  (apply_colour f (FFI ffi_index ptr1 len1 ptr2 len2 numset) =
    FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2) (apply_nummap_key f numset)) ∧
  (apply_colour f (LocValue r l1) =
    LocValue (f r) l1) ∧
  (apply_colour f (Alloc num numset) =
    Alloc (f num) (apply_nummap_key f numset)) ∧
  (apply_colour f (Raise num) = Raise (f num)) ∧
  (apply_colour f (Return num1 num2) = Return (f num1) (f num2)) ∧
  (apply_colour f Tick = Tick) ∧
  (apply_colour f (Set n exp) = Set n (apply_colour_exp f exp)) ∧
  (apply_colour f p = p )`

val _ = export_rewrites ["apply_nummap_key_def","apply_colour_exp_def"
                        ,"apply_colour_inst_def","apply_colour_def"
                        ,"apply_colour_imm_def"];

(* Liveness Analysis*)

(*Writes made by any inst as a sptree*)
val get_writes_inst_def = Define`
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
  (get_writes_inst (Mem Load8 r (Addr a w)) = insert r () LN) ∧
  (get_writes_inst (FP (FPLess r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPLessEqual r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPEqual r f1 f2)) = insert r () LN) ∧
  (get_writes_inst (FP (FPMovToReg r1 r2 d) :'a inst) =
    if dimindex(:'a) = 64
      then insert r1 () LN
      else insert r2 () (insert r1 () LN)) ∧
  (get_writes_inst inst = LN)`

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
val get_live_inst_def = Define`
  (get_live_inst Skip live:num_set = live) ∧
  (get_live_inst (Const reg w) live = delete reg live) ∧
  (get_live_inst (Arith (Binop bop r1 r2 ri)) live =
    dtcase ri of Reg r3 => insert r2 () (insert r3 () (delete r1 live))
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
  (get_live_inst x live = live)`

val big_union_def = Define`
  big_union ls = FOLDR (λx y. union x y) LN ls`

val get_live_exp_def = tDefine"get_live_exp"`
  (get_live_exp (Var num) = insert num () LN ) ∧
  (get_live_exp (Load exp) = get_live_exp exp) ∧
  (get_live_exp (Op wop ls) =
    big_union (MAP get_live_exp ls)) ∧
  (get_live_exp (Shift sh exp nexp) = get_live_exp exp) ∧
  (get_live_exp expr = LN)`
  (WF_REL_TAC `measure (exp_size ARB)`>>
  rw[]>>
  imp_res_tac MEM_IMP_exp_size>>
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`) >> DECIDE_TAC)

val numset_list_insert_def = Define`
  (numset_list_insert [] t = t) ∧
  (numset_list_insert (x::xs) t = insert x () (numset_list_insert xs t))`

val get_live_def = Define`
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
  (*First case where branching appears:
    We get the livesets for e2 and e3, union them, add the if variable
    then pass the resulting liveset upwards
  *)
  (get_live (If cmp r1 ri e2 e3) live =
    let e2_live = get_live e2 live in
    let e3_live = get_live e3 live in
    let union_live = union e2_live e3_live in
       dtcase ri of Reg r2 => insert r2 () (insert r1 () union_live)
      | _ => insert r1 () union_live) ∧
  (get_live (Alloc num numset) live = insert num () numset) ∧
  (get_live (FFI ffi_index ptr1 len1 ptr2 len2 numset) live =
   insert ptr1 () (insert len1 ()
     (insert ptr2 () (insert len2 () numset)))) ∧
  (get_live (Raise num) live = insert num () live) ∧
  (get_live (Return num1 num2) live = insert num1 () (insert num2 () live)) ∧
  (get_live Tick live = live) ∧
  (get_live (LocValue r l1) live = delete r live) ∧
  (get_live (Set n exp) live = union (get_live_exp exp) live) ∧
  (*Cut-set must be live, args input must be live
    For tail calls, there shouldn't be a liveset since control flow will
    never return into the same instance
    Otherwise, both args + cutsets live
  *)
  (get_live (Call NONE dest args h) live = numset_list_insert args LN) ∧
  (get_live (Call (SOME(_,cutset,_)) dest args h) live =
    union cutset (numset_list_insert args LN))`

(* Dead instruction removal *)
val remove_dead_inst_def = Define`
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
  (remove_dead_inst (Mem Load8 r (Addr a w)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPLess r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPLessEqual r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPEqual r f1 f2)) live = (lookup r live = NONE)) ∧
  (remove_dead_inst (FP (FPMovToReg r1 r2 d) :'a inst) live =
    if dimindex(:'a) = 64 then lookup r1 live = NONE
    else (lookup r1 live = NONE ∧ (lookup r2 live = NONE))) ∧
  (*Catchall -- for other instructions*)
  (remove_dead_inst x live = F)`

(*Delete dead code, w.r.t. a set of live variables*)
val remove_dead_def = Define`
  (remove_dead Skip live = (Skip,live)) ∧
  (remove_dead (Move pri ls) live =
    let ls = FILTER (λx,y. lookup x live = SOME ()) ls in
    if ls = [] then (Skip,live)
    else
    let killed = FOLDR delete live (MAP FST ls) in
      (Move pri ls,numset_list_insert (MAP SND ls) killed)) ∧
  (remove_dead (Inst i) live =
    if remove_dead_inst i live then (Skip,live)
                               else (Inst i,get_live_inst i live)) ∧
  (remove_dead (Assign num exp) live =
    (if lookup num live = NONE then
      (Skip,live)
    else
      (Assign num exp, get_live (Assign num exp) live))) ∧
  (remove_dead (Get num store) live =
    if lookup num live = NONE then
      (Skip,live)
    else (Get num store,delete num live)) ∧
  (remove_dead (LocValue r l1) live =
    if lookup r live = NONE then
      (Skip,live)
    else (LocValue r l1,delete r live)) ∧
  (remove_dead (Seq s1 s2) live =
    let (s2,s2live) = remove_dead s2 live in
    let (s1,s1live) = remove_dead s1 s2live in
    let prog =
      if s1 = Skip then
        if s2 = Skip then Skip
        else s2
      else
        if s2 = Skip then s1
        else Seq s1 s2
    in (prog,s1live)) ∧
  (remove_dead (MustTerminate s1) live =
    (* This can technically be optimized away if it was a Skip,
       but we should never use MustTerminate to wrap completely dead code
    *)
    let (s1,s1live) = remove_dead s1 live in
      (MustTerminate s1,s1live)) ∧
  (remove_dead (If cmp r1 ri e2 e3) live =
    let (e2,e2_live) = remove_dead e2 live in
    let (e3,e3_live) = remove_dead e3 live in
    let union_live = union e2_live e3_live in
    let liveset =
       dtcase ri of Reg r2 => insert r2 () (insert r1 () union_live)
      | _ => insert r1 () union_live in
    let prog =
      if e2 = Skip ∧ e3 = Skip then Skip
      else If cmp r1 ri e2 e3 in
    (prog,liveset)) ∧
  (remove_dead (Call(SOME(v,cutset,ret_handler,l1,l2))dest args h) live =
    (*top level*)
    let args_set = numset_list_insert args LN in
    let live_set = union cutset args_set in
    let (ret_handler,_) = remove_dead ret_handler live in
    let h =
      (dtcase h of
        NONE => NONE
      | SOME(v',prog,l1,l2) =>
        SOME(v',FST (remove_dead prog live),l1,l2)) in
    (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h,live_set)) ∧
  (remove_dead prog live = (prog,get_live prog live))`

(*Single step immediate writes by a prog*)
val get_writes_def = Define`
  (get_writes (Move pri ls) = numset_list_insert (MAP FST ls) LN)∧
  (get_writes (Inst i) = get_writes_inst i) ∧
  (get_writes (Assign num exp) = insert num () LN)∧
  (get_writes (Get num store) = insert num () LN) ∧
  (get_writes (LocValue r l1) = insert r () LN) ∧
  (get_writes prog = LN)`

val get_writes_pmatch = Q.store_thm("get_writes_pmatch",`!inst.
  get_writes inst =
    case inst of
    | Move pri ls => numset_list_insert (MAP FST ls) LN
    | Inst i => get_writes_inst i
    | Assign num exp => insert num () LN
    | Get num store => insert num () LN
    | LocValue r l1 => insert r () LN
    | prog => LN`,
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[get_writes_def])

(* Old representation *)
val get_clash_sets_def = Define`
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
    let merged = dtcase ri of Reg r2 => insert r2 () (insert r1 () union_live)
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
    (dtcase h of
      NONE => (live_set,ret_clash::hd::ls)
    | SOME(v',prog,l1,l2) =>
        let (hd',ls') = get_clash_sets prog live in
        (*Handler clash set*)
        let h_clash = insert v' () cutset in
        (live_set,h_clash::ret_clash::hd::hd'::ls++ls'))) ∧
  (*Catchall for cases where we dont have in sub programs live sets*)
  (get_clash_sets prog live =
    let i_set = union (get_writes prog) live in
      (get_live prog live,[i_set]))`

(* Potentially more efficient liveset representation for checking / allocation*)
val get_delta_inst_def = Define`
  (get_delta_inst Skip = Delta [] []) ∧
  (get_delta_inst (Const reg w) = Delta [reg] []) ∧
  (get_delta_inst (Arith (Binop bop r1 r2 ri)) =
    dtcase ri of Reg r3 => Delta [r1] [r2;r3]
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
  (get_delta_inst x = Delta [] [])`

val get_reads_exp_def = tDefine "get_reads_exp" `
  (get_reads_exp (Var num) = [num]) ∧
  (get_reads_exp (Load exp) = get_reads_exp exp) ∧
  (get_reads_exp (Op wop ls) =
      FLAT (MAP get_reads_exp ls)) ∧
  (get_reads_exp (Shift sh exp nexp) = get_reads_exp exp) ∧
  (get_reads_exp expr = [])`
  (WF_REL_TAC `measure (exp_size ARB)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

val get_clash_tree_def = Define`
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
    dtcase ri of
      Reg r2 => Seq (Delta [] [r1;r2]) (Branch NONE e2t e3t)
    | _      => Seq (Delta [] [r1]) (Branch NONE e2t e3t)) ∧
  (get_clash_tree (MustTerminate s) =
    get_clash_tree s) ∧
  (get_clash_tree (Alloc num numset) =
    Seq (Delta [] [num]) (Set numset)) ∧
  (get_clash_tree (FFI ffi_index ptr1 len1 ptr2 len2 numset) =
    Seq (Delta [] [ptr1;len1;ptr2;len2]) (Set numset)) ∧
  (get_clash_tree (Raise num) = Delta [] [num]) ∧
  (get_clash_tree (Return num1 num2) = Delta [] [num1;num2]) ∧
  (get_clash_tree Tick = Delta [] []) ∧
  (get_clash_tree (LocValue r l1) = Delta [r] []) ∧
  (get_clash_tree (Set n exp) = Delta [] (get_reads_exp exp)) ∧
  (get_clash_tree (Call ret dest args h) =
    let args_set = numset_list_insert args LN in
    dtcase ret of
      NONE => Set (numset_list_insert args LN)
    | SOME (v,cutset,ret_handler,_,_) =>
      let live_set = union cutset args_set in
      (*Might be inefficient..*)
      let ret_tree = Seq (Set (insert v () cutset)) (get_clash_tree ret_handler) in
      dtcase h of
        NONE => Seq (Set live_set) ret_tree
      | SOME (v',prog,_,_) =>
        let handler_tree =
          (*They will actually always be equal if call_arg_conv is met*)
          if v = v' then get_clash_tree prog
          else Seq (Set (insert v' () cutset)) (get_clash_tree prog) in
        Branch (SOME live_set) ret_tree handler_tree)`

(* Preference edges *)
val get_prefs_def = Define`
  (get_prefs (Move pri ls) acc = (MAP (λx,y. (pri,x,y)) ls) ++ acc) ∧
  (get_prefs (MustTerminate s1) acc =
    get_prefs s1 acc) ∧
  (get_prefs (Seq s1 s2) acc =
    get_prefs s1 (get_prefs s2 acc)) ∧
  (get_prefs (If cmp num rimm e2 e3) acc =
    get_prefs e2 (get_prefs e3 acc)) ∧
  (get_prefs (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) acc =
    dtcase h of
      NONE => get_prefs ret_handler acc
    | SOME (v,prog,l1,l2) => get_prefs prog (get_prefs ret_handler acc)) ∧
  (get_prefs prog acc = acc)`

val get_prefs_pmatch = Q.store_thm("get_prefs_pmatch",`!s acc.
  get_prefs s acc =
    case s of
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
    | prog => acc`,
  rpt strip_tac
  >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
  >> rpt strip_tac
  >> every_case_tac
  >> fs [get_prefs_def]
  >- (rpt(POP_ASSUM MP_TAC)
  >> Q.SPEC_TAC (`acc`,`acc`) >> Q.SPEC_TAC (`s`,`s`)
  >> ho_match_mp_tac (theorem "get_prefs_ind")
  >> rpt strip_tac >> fs[Once get_prefs_def]
  >> every_case_tac >> metis_tac[pair_CASES]));

(* Forced edges for certain instructions
  At the moment this really only ever occurs for AddCarry, AddOverflow, SubOverflow
*)
val get_forced_def = Define`
  (get_forced (c:'a asm_config) ((Inst i):'a prog) acc =
    dtcase i of
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
       if (c.ISA = ARMv6) then
         (if (r1=r2) then [] else [(r1,r2)]) ++ acc
       else if (c.ISA = ARMv8) \/ (c.ISA = RISC_V) \/ (c.ISA = Tiny) then
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
    dtcase h of
      NONE => get_forced c ret_handler acc
    | SOME (v,prog,l1,l2) => get_forced c prog (get_forced c ret_handler acc)) ∧
  (get_forced c prog acc = acc)`

val get_forced_pmatch = Q.store_thm("get_forced_pmatch",`!c prog acc.
  (get_forced (c:'a asm_config) prog acc =
    case prog of
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
       if (c.ISA = ARMv6) then
         (if (r1=r2) then [] else [(r1,r2)]) ++ acc
       else if (c.ISA = ARMv8) \/ (c.ISA = RISC_V) \/ (c.ISA = Tiny) then
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
    | _ => acc)`,
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
  >> metis_tac[pair_CASES])

(*col is injective over every cut set*)
val check_colouring_ok_alt_def = Define`
  (check_colouring_ok_alt col [] = T) ∧
  (check_colouring_ok_alt col (x::xs) ⇔
    let names = MAP (col o FST) (toAList x) in
      ALL_DISTINCT names ∧ check_colouring_ok_alt col xs)`

val every_even_colour_def = Define`
  every_even_colour col ⇔
  EVERY (λ(x,y). if is_phy_var x then y = x DIV 2 else T) (toAList col)`

(*Extract a colouring function from the generated sptree*)
val total_colour_def = Define`
  total_colour col x =
    dtcase lookup x col of NONE => if is_phy_var x then x else 2*x | SOME x => 2*x`

(*Check that the oracle provided colour (if it exists) is okay*)
val oracle_colour_ok_def = Define`
  oracle_colour_ok k col_opt tree prog ls ⇔
  dtcase col_opt of
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
     else NONE`

(*alg is the allocation algorithm,
  k is the number of registers
  prog is the program to be colored
  col_opt is an optional oracle colour*)
val word_alloc_def = Define`
  word_alloc c (alg:num) k prog col_opt =
  let tree = get_clash_tree prog in
  (*let moves = get_prefs_sp prog [] in*)
  let forced = get_forced c prog [] in
  dtcase oracle_colour_ok k col_opt tree prog forced of
    NONE =>
      let moves = get_prefs prog [] in
      (dtcase reg_alloc k moves tree forced of
        Success col =>
          apply_colour (total_colour col) prog
      | Failure _ => prog (*cannot happen*))
  | SOME col_prog =>
      col_prog`

(*The initial move, ssa and limit vars*)
val setup_ssa_def = Define`
  setup_ssa n lim (prog:'a wordLang$prog) =
  let args = even_list n in
  let (new_ls,ssa',n') = list_next_var_rename args LN lim in
    (Move 1 (ZIP(new_ls,args)),ssa',n')`

val limit_var_def = Define`
  limit_var prog =
    let x = max_var prog in
    x + (4 - (x MOD 4)) +1`

val full_ssa_cc_trans_def = Define`
  full_ssa_cc_trans n prog =
    let lim = limit_var prog in
    let (mov,ssa,na) = setup_ssa n lim prog in
    let (prog',ssa',na') = ssa_cc_trans prog ssa na in
      Seq mov prog'`

val _ = export_theory();
