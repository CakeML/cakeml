open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory BasicProvers sortingTheory miscTheory
open word_langTheory word_lemmasTheory word_procTheory word_liveTheory
open monadsyntax state_transformerTheory

val _ = new_theory "word_ssa";

(*Define a ssa + calling conventions pass
  The strategy is the keep an sptree mapping of variables -> their latest names
  Whenever we get a new "write", we assign a new fresh name to it

  Alloc and Call will be special cases which instead generate alloc variables for cutsets
   
  The overall proof should be:

  prog (starts with 0,2,4,6... in locals)
  --> Add moves for each argument e.g. Move(2,2);Move(4,4) 
  --> 
*)
val _ = Hol_datatype `
  ssa_state = <| 
                ssa_map :num num_map;
                next_stack : num;
                next_alloc : num
             |>`

(*Returns renaming under the ssa map for v*)
val cur_var_rename_def = Define`
  cur_var_rename v =
  λs. (return case lookup v s.ssa_map of NONE => v | SOME x => x) s`

val get_next_alloc_def = Define`
  get_next_alloc = λs. (s.next_alloc, s with next_alloc := s.next_alloc+4)`

val update_ssa_map_def = Define`
  update_ssa_map v v' = λs.((), s with ssa_map:= insert v v' s.ssa_map)`

(*Consistently sets up the next variable rename for v*)
val next_var_rename_def = Define`
  next_var_rename v =
  do
    v' <- get_next_alloc;
    update_ssa_map v v';
    return v'
  od`

val get_next_stack_def = Define`
  get_next_stack = λs. (s.next_stack, s with next_stack := s.next_stack+4)`

val get_n_next_stack_def = Define`
  (get_n_next_stack (0:num) = λs. (return []) s) ∧ 
  (get_n_next_stack (SUC n) =
  do
    v <- get_next_stack;
    vs <- get_n_next_stack n;
    return (v::vs)
  od)`

val get_ssa_map_def = Define`
  get_ssa_map = λs. (return s.ssa_map) s`

(*not really correct, just for testing: the easiest way is to find something greater than every var
  mentioned in the program, then use 4n+3 and 4n+1*)
val init_ssa_state_def = Define`
  init_ssa_state = <| ssa_map := LN ; next_stack:=103; next_alloc:=101 |>`
     
val ssa_cc_trans_def = Define`
  (ssa_cc_trans Skip = return Skip) ∧ 
  (ssa_cc_trans (Move ls) =
    let ls_1 = MAP FST ls in
    let ls_2 = MAP SND ls in 
    do
      ren_ls2 <- mapM cur_var_rename ls_2;
      ren_ls1 <- mapM next_var_rename ls_1;
      return (Move(ZIP(ren_ls1,ren_ls2)))
    od) ∧
  (*inst,assign*)
  (ssa_cc_trans (Get num store) = 
    do
      num' <- next_var_rename num;
      return (Get num' store)
    od) ∧ 
  (*store*)
  (ssa_cc_trans (Seq s1 s2) =
    do
      s1' <- ssa_cc_trans s1; 
      s2' <- ssa_cc_trans s2;
      return (Seq s1' s2')
    od) ∧
  (*Tricky case 1: we need to merge the ssa results from both branches by
    unSSA-ing the phi functions
  *)
  (ssa_cc_trans (If e1 num e2 e3) = 
    do
      e1' <- ssa_cc_trans e1;
      num' <- cur_var_rename num;
      e2' <- ssa_cc_trans e2;
      ssa_map2 <- get_ssa_map;
      e3' <- ssa_cc_trans e3;
      ssa_map3 <- get_ssa_map;
      (*TODO: make consistent*)
      e2_cons <- return Skip;
      e3_cons <- return Skip;
      return (If e1' num' (Seq e2' e2_cons) (Seq e3' e3_cons))
    od) ∧ 
  (ssa_cc_trans (Alloc num numset) = 
    do
      num' <- cur_var_rename num;
      names <- mapM cur_var_rename (MAP FST (toAList numset));
      (*move all names into stack locations*)
      stack_names <- get_n_next_stack (LENGTH names);
      stack_set <- return (numset_list_insert stack_names LN);
      (*then move the stack vars into new ssa locations 
        for their ORIGIINAL names*)
      ren_names <- mapM next_var_rename names;
      return 
        (Seq (Move (ZIP (stack_names,names))) 
        (Seq (Alloc num' stack_set)
        (Move (ZIP (ren_names,stack_names)))))
    od) ∧ 
  (ssa_cc_trans (Raise num) =
    do
      num' <- cur_var_rename num;
      return (Raise num')
    od) ∧ 
  (ssa_cc_trans (Return num) =
    do
      num' <- cur_var_rename num;
      return (Return num')
    od) ∧ 
  (ssa_cc_trans Tick = return Tick) ∧ 
  (*set*)
  (*I think it may be easier to split Calls at the top level into 3 different cases
    because they have different control flow properties:
    1) Tail calls ⇒ just need to rename args, handler should be NONE..
    2) No handler ⇒ add a renamer to the returning handler to fixup the cutsets
    3) Handler ⇒ most complex, we will need renamers in both cases and THEN a consistency rename after
  *)
  (ssa_cc_trans (Call ret dest args h) =
    do
      (*args*)
      names <- mapM cur_var_rename args;
      conv_args <- return (even_list (LENGTH names));
      move_args <- return (Move (ZIP (conv_args,args)));
      (case ret of 
        NONE =>
        return
          (Seq move_args (Call NONE dest conv_args h))
      | SOME (ret,numset,ret_handler) => 
        do
          (*Returning cutset*)
          names <- mapM cur_var_rename (MAP FST (toAList numset));
          (*move all names into stack locations*)
          stack_names <- get_n_next_stack (LENGTH names);
          stack_set <- return (numset_list_insert stack_names LN);
          (*fresh names for cutset variables*)
          ren_names <- mapM next_var_rename names;
          move_cutset <- return (Move (ZIP (stack_names,names)));
          restore_cutset <- return (Move (ZIP (ren_names,stack_names)));
          ret' <- next_var_rename ret;
          ren_ret_handler <- ssa_cc_trans ret_handler;
          mov_ret_handler <- return 
            (Seq restore_cutset (Seq (Move[ret',0]) (ren_ret_handler)));  (*order is important*)
          (case h of
            NONE =>
            return
              (Seq move_args
              (Seq move_cutset
              (Call (SOME(0,stack_set,mov_ret_handler)) dest conv_args NONE)))
          | SOME(n,h) => 
            (*handler, TODO: we need to restore SSA consistency, like in If*)
            do
              ssa_map_ret <- get_ssa_map; 
              n' <- next_var_rename n;
              ren_exc_handler <- ssa_cc_trans h;
              mov_exc_handler <- return
                (Seq restore_cutset (Seq(Move[n',0]) (ren_exc_handler)));
              ssa_map_exc <- get_ssa_map;
              ret_cons <- return Skip;
              exc_cons <- return Skip;
              cons_ret_handler <- return (Seq mov_ret_handler ret_cons);
              cons_exc_handler <- return (Seq mov_exc_handler exc_cons);
              return
                (Seq move_args
                (Seq move_cutset
                (Call (SOME(0,stack_set,cons_ret_handler)) dest conv_args (SOME(0,cons_exc_handler)))))
            od)
        od)
    od)` 

  (*
EVAL ``ssa_cc_trans 

(Seq (Move [(1,2)]) (
Seq (Move [(3,1)])  (
Seq (Alloc 5 (numset_list_insert [1;2;3;4;5;6] LN)) (
Seq (Move [(1,5)]) Skip)))) init_ssa_state``

(Move([(1,2);(3,4)])) init_ssa_state``

Move 1,2
Move 3,1
Move 3,4
Move 1,5

*)
    
 (*First case where branching appears:
    We get the livesets for e2 and e3, union them, add the if variable
    then pass the resulting liveset upwards
  *)
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



val ssa_call_conv_trans_def = Define`
  (**)
  
  (*Returning calls*)
  (ssa_call_conv_trans lim (Call (SOME (ret,names,ret_handler)) dest args h) =
    (*Forcing args into registers*)
    let lim = if lim > 2 * LENGTH args then lim else 2*LENGTH args +1 in
    let conv_args = even_list (LENGTH args) in
    let names = nub (num_set_to_list names) in
    (*numset -> Alist, might want to add nub here to give all_distinct?
      This transform needs to be monotonic and injective on variable names*)
    let conv_names = MAP (\i. 2*i + lim) names in
    (*Move that restores the cutset*)
    let restore = Move (ZIP (names,conv_names)) in
    (*Both handlers are recursively renamed
      and exceptional return vals are mapped to 0
      NOTE: 2 Moves required because of possible shadowing of the cut-set values*)
    let conv_h = case h of NONE => NONE
                        |  SOME(n,h) => SOME(0, Seq restore
                                               (Seq (Move [n,0])
                                                    (call_conv_trans lim h))) in
    let conv_ret = Seq restore
                  (Seq (Move [ret,0])
                       (call_conv_trans lim ret_handler)) in
    Seq (Move (ZIP (conv_names++conv_args,names++args)))
        (Call (SOME (0,list_to_num_set conv_names,conv_ret)) dest conv_args conv_h))/\
  (*Tail calls -- Only need to add a move on the args to force args into registers
    (handler should be NONE)*)
  (call_conv_trans lim (Call NONE dest args h) =
    let conv_args = even_list (LENGTH args) in
    Seq (Move (ZIP (conv_args,args))) (Call NONE dest conv_args h)) /\
  (call_conv_trans lim (Seq p p') = Seq (call_conv_trans lim p) (call_conv_trans lim p')) /\
  (call_conv_trans lim (If g n c1 c2) = If (call_conv_trans lim g) n (call_conv_trans lim c1)
                                         (call_conv_trans lim c2)) /\
  (call_conv_trans lim x = x) `




val numset_list_insert_def = Define`
  (numset_list_insert [] t = t) ∧
  (numset_list_insert (x::xs) t = insert x () (numset_list_insert xs t))`

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

(*Fully general expressions is not needed but is
not too difficult to define
Note that these never write to a register so we dont need a live-after*)
val get_live_exp_def = tDefine "get_live_exp" `
  (get_live_exp (Var num) = insert num () LN ) ∧
  (get_live_exp (Load exp) = get_live_exp exp) ∧
  (get_live_exp (Op wop ls) =
    (*Keep adding into live the new variables that are read*)
    FOLDR (λx y:num_set. union (get_live_exp x) y) LN ls) ∧
  (get_live_exp (Shift sh exp nexp) = get_live_exp exp) ∧
  (get_live_exp expr = LN)`
  (WF_REL_TAC `measure (word_exp_size ARB)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*This defines the top level live sets for each prog
  i.e. given a live after, returns the liveset before that prog*)

