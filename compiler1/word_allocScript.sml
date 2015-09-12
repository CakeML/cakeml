open preamble wordLangTheory reg_allocTheory

val _ = ParseExtras.temp_tight_equality ();
val _ = new_theory "word_alloc";

(*Defines the algorithms related to the register allocator, currently:
1) SSA form
2) Colouring and Liveness Analysis
3) Combined passes
*)

(*SSA form*)
val apply_nummap_key_def = Define`
  apply_nummap_key f names =
  fromAList (MAP (λx,y.f x,y) (toAList names))`

val option_lookup_def = Define`
  option_lookup t v = case lookup v t of NONE => v | SOME x => x`

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
  fake_move v = Assign v (Const 0w)`

(*Do the merging moves only*)
val merge_moves_def = Define`
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
    | _ => (seqL,seqR,na',ssa_L',ssa_R'))`

(*Separately do the fake moves*)
val fake_moves_def = Define`
  (fake_moves [] ssa_L ssa_R (na:num) = (Skip:'a wordLang$prog,Skip:'a wordLang$prog,na,ssa_L,ssa_R)) ∧
  (fake_moves (x::xs) ssa_L ssa_R na =
    let (seqL,seqR,na',ssa_L',ssa_R') =
      fake_moves xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    case (optLx,optLy) of
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
val ssa_cc_trans_inst_def = Define`
  (ssa_cc_trans_inst Skip ssa na = (Skip,ssa,na)) ∧
  (ssa_cc_trans_inst (Const reg w) ssa na =
    let (reg',ssa',na') = next_var_rename reg ssa na in
      ((Const reg' w),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Binop bop r1 r2 ri)) ssa na =
    case ri of
      Reg r3 =>
      let r3' = option_lookup ssa r3 in
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Arith (Binop bop r1' r2' (Reg r3')),ssa',na')
    | _ =>
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Arith (Binop bop r1' r2' ri),ssa',na')) ∧
  (ssa_cc_trans_inst (Arith (Shift shift r1 r2 n)) ssa na =
    let r2' = option_lookup ssa r2 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
      (Arith (Shift shift r1' r2' n),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Load r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Mem Load r' (Addr a' w),ssa',na')) ∧
  (ssa_cc_trans_inst (Mem Store r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Mem Store r' (Addr a' w),ssa,na)) ∧
  (*Catchall -- for future instructions to be added*)
  (ssa_cc_trans_inst x ssa na = (x,ssa,na))`

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
val ssa_cc_trans_exp_def = tDefine "ssa_cc_trans_exp" `
  (ssa_cc_trans_exp t (Var num) =
    Var (case lookup num t of NONE => num | SOME x => x)) ∧
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
      (Inst i',ssa',na')) ∧
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
  (*Tricky case 1: we need to merge the ssa results from both branches by
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
    let names = MAP (option_lookup ssa') args in
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
    (case h of
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
  (apply_colour_inst f (Mem Load r (Addr a w)) =
    Mem Load (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f (Mem Store r (Addr a w)) =
    Mem Store (f r) (Addr (f a) w)) ∧
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
    let ret = case ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (f v,apply_nummap_key f cutset,apply_colour f ret_handler,l1,l2) in
    let args = MAP f args in
    let h = case h of NONE => NONE
                     | SOME (v,prog,l1,l2) => SOME (f v, apply_colour f prog,l1,l2) in
      Call ret dest args h) ∧
  (apply_colour f (Seq s1 s2) = Seq (apply_colour f s1) (apply_colour f s2)) ∧
  (apply_colour f (If cmp r1 ri e2 e3) =
    If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)) ∧
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
  (get_writes_inst (Mem Load r (Addr a w)) = insert r () LN) ∧
  (get_writes_inst inst = LN)`

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
val get_live_inst_def = Define`
  (get_live_inst Skip live:num_set = live) ∧
  (get_live_inst (Const reg w) live = delete reg live) ∧
  (get_live_inst (Arith (Binop bop r1 r2 ri)) live =
    case ri of Reg r3 => insert r2 () (insert r3 () (delete r1 live))
    | _ => insert r2 () (delete r1 live)) ∧
  (get_live_inst (Arith (Shift shift r1 r2 n)) live =
    insert r2 () (delete r1 live)) ∧
  (get_live_inst (Mem Load r (Addr a w)) live =
    insert a () (delete r live)) ∧
  (get_live_inst (Mem Store r (Addr a w)) live =
    insert a () (insert r () live)) ∧
  (*Catchall -- for future instructions to be added*)
  (get_live_inst x live = live)`

val get_live_exp_def = tDefine "get_live_exp" `
  (get_live_exp (Var num) = insert num () LN ) ∧
  (get_live_exp (Load exp) = get_live_exp exp) ∧
  (get_live_exp (Op wop ls) =
    (*Keep adding into live the new variables that are read*)
    FOLDR (λx y:num_set. union (get_live_exp x) y) LN ls) ∧
  (get_live_exp (Shift sh exp nexp) = get_live_exp exp) ∧
  (get_live_exp expr = LN)`
  (WF_REL_TAC `measure (exp_size ARB)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

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
  (*First case where branching appears:
    We get the livesets for e2 and e3, union them, add the if variable
    then pass the resulting liveset upwards
  *)
  (get_live (If cmp r1 ri e2 e3) live =
    let e2_live = get_live e2 live in
    let e3_live = get_live e3 live in
    let union_live = union e2_live e3_live in
       case ri of Reg r2 => insert r2 () (insert r1 () union_live)
      | _ => insert r1 () union_live) ∧
  (get_live (Alloc num numset) live = insert num () numset) ∧
  (get_live (Raise num) live = insert num () live) ∧
  (get_live (Return num1 num2) live = insert num1 () (insert num2 () live)) ∧
  (get_live Tick live = live) ∧
  (get_live (Set n exp) live = union (get_live_exp exp) live) ∧
  (*Cut-set must be live, args input must be live
    For tail calls, there shouldn't be a liveset since control flow will
    never return into the same instance
    Otherwise, both args + cutsets live
  *)
  (get_live (Call ret dest args h) live =
    let args_set = numset_list_insert args LN in
      case ret of NONE => args_set
                | SOME (_,cutset,_) => union cutset args_set)`


(*Single step immediate writes by a prog*)
val get_writes_def = Define`
  (get_writes (Move pri ls) = numset_list_insert (MAP FST ls) LN)∧
  (get_writes (Inst i) = get_writes_inst i) ∧
  (get_writes (Assign num exp) = insert num () LN)∧
  (get_writes (Get num store) = insert num () LN) ∧
  (get_writes prog = LN)`

val get_clash_sets_def = Define`
  (get_clash_sets (Seq s1 s2) live =
    let (hd,ls) = get_clash_sets s2 live in
    let (hd',ls') = get_clash_sets s1 hd in
      (hd',(ls' ++ ls))) ∧
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
      (get_live prog live,[i_set]))`

val get_spg_def = Define`
  get_spg prog live =
    let (hd,clash_sets) = get_clash_sets prog live in
      (clash_sets_to_sp_g (hd::clash_sets))`

(*Preference edges*)
val get_prefs_def = Define`
  (get_prefs (Move pri ls) acc = (MAP (λx,y. (pri,x,y)) ls) ++ acc) ∧
  (get_prefs (Seq s1 s2) acc =
    get_prefs s1 (get_prefs s2 acc)) ∧
  (get_prefs (If cmp num rimm e2 e3) acc =
    get_prefs e2 (get_prefs e3 acc)) ∧
  (get_prefs (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) acc =
    case h of
      NONE => get_prefs ret_handler acc
    | SOME (v,prog,l1,l2) => get_prefs prog (get_prefs ret_handler acc)) ∧
  (get_prefs prog acc = acc)`

(*allocate*)
val word_alloc_def = Define`
  word_alloc k prog =
  let clash_graph = get_spg prog LN in (*No live after set*)
  let moves = get_prefs prog [] in (*Get the moves in the graph*) 
  let col = reg_alloc 3 clash_graph k moves in 
  (*Get the register allocation function,
    TODO: We can choose the flag based on the size of graph/moves*)
    apply_colour (total_colour col) prog`

(*The initial move, ssa and limit vars*)
val setup_ssa_def = Define`
  setup_ssa n lim (prog:'a wordLang$prog) =
  let args = even_list n in
    list_next_var_rename_move LN lim (even_list n)`

(*I'm pretty sure this is already in HOL*)
val max2_def = Define`
  max2 (x:num) y = if x > y then x else y`

val max3_def = Define`
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)`

val _ = export_rewrites["max2_def","max3_def"];

val list_max_def = Define`
  (list_max [] acc:num = acc) ∧
  (list_max (x::xs) acc = list_max xs (max2 x acc))`

(*Find the maximum variable*)
val max_var_exp_def = tDefine "max_var_exp" `
  (max_var_exp (Var num) = num) ∧
  (max_var_exp (Load exp) = max_var_exp exp) ∧
  (max_var_exp (Op wop ls) = list_max (MAP (max_var_exp) ls) (0:num))∧
  (max_var_exp (Shift sh exp nexp) = max_var_exp exp) ∧
  (max_var_exp exp = 0:num)`
(WF_REL_TAC `measure (exp_size ARB )`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC);

val max_var_inst_def = Define`
  (max_var_inst Skip = 0) ∧
  (max_var_inst (Const reg w) = reg) ∧
  (max_var_inst (Arith (Binop bop r1 r2 ri)) =
    case ri of Reg r => max3 r1 r2 r | _ => max2 r1 r2) ∧
  (max_var_inst (Arith (Shift shift r1 r2 n)) = max2 r1 r2) ∧
  (max_var_inst (Mem Load r (Addr a w)) = max2 a r) ∧
  (max_var_inst (Mem Store r (Addr a w)) = max2 a r) ∧
  (max_var_inst _ = 0)`

val max_var_def = Define `
  (max_var Skip = 0) ∧
  (max_var (Move pri ls) =
    list_max (MAP FST ls ++ MAP SND ls) 0) ∧
  (max_var (Inst i) = max_var_inst i) ∧
  (max_var (Assign num exp) = max2 num (max_var_exp exp)) ∧
  (max_var (Get num store) = num) ∧
  (max_var (Store exp num) = max2 num (max_var_exp exp)) ∧
  (max_var (Call ret dest args h) =
    let n =
    (case ret of
      NONE => 0
    | SOME (v,cutset,ret_handler,l1,l2) =>
      let ret_handler_max = max_var ret_handler in
      let cutset_max = list_max (MAP FST (toAList cutset)) 0 in
        max3 v ret_handler_max cutset_max) in
    let n = max2 n (list_max args 0) in
    case h of
      NONE => n
    | SOME (v,prog,l1,l2) =>
      let exc_handler_max = max_var prog in
      max3 n v exc_handler_max) ∧
  (max_var (Seq s1 s2) = max2 (max_var s1) (max_var s2)) ∧
  (max_var (If cmp r1 ri e2 e3) =
    let r = case ri of Reg r => max2 r r1 | _ => r1 in
      max3 r (max_var e2) (max_var e3)) ∧
  (max_var (Alloc num numset) =
    max2 num (list_max (MAP FST (toAList numset)) 0)) ∧
  (max_var (Raise num) = num) ∧
  (max_var (Return num1 num2) = max2 num1 num2) ∧
  (max_var Tick = 0) ∧
  (max_var (Set n exp) = max_var_exp exp) ∧
  (max_var p = 0)`

val limit_var_def = Define`
  limit_var prog = 
    let x = max_var prog in
    x + (4 - (x MOD 4)) +1`
    
    (*
    Cases: x MOD 4
    0 => x+1
    1 => x+4
    2 => x+3
    3 => x+2
    In all cases, the result is a var that is 1 MOD 4
    *)
    
val full_ssa_cc_trans_def = Define`
  full_ssa_cc_trans n prog =
    let lim = limit_var prog in
    let (mov,ssa,na) = setup_ssa n lim prog in
    let (prog',ssa',na') = ssa_cc_trans prog ssa na in
      Seq mov prog'`

val word_trans_def = Define`
  word_trans n k prog =
  word_alloc k (full_ssa_cc_trans n prog)` 

val _ = export_theory();


