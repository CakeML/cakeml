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

val set_ssa_map_def = Define`
  set_ssa_map ssa_map = λs. ((), s with ssa_map:=ssa_map)`

val force_ssa_insert_def = Define`
  force_ssa_insert v v' = λs.((), s with ssa_map:=insert v v' s.ssa_map)`

(*not really correct, just for testing: the easiest way is to find something greater than every var
  mentioned in the program, then use 4n+3 and 4n+1*)
val init_ssa_state_def = Define`
  init_ssa_state = <| ssa_map := LN ; next_stack:=103; next_alloc:=101 |>`

(*Whenever we have 2 branches, we need to make them consistent at their join positions
  This is an approximation of phi functions
  Current idea:
  Our proof will have an assumption like:
  ∀v. v ∈ domain ssa_map ∧  v ∈ st.locals ⇒ ssa_map v ∈ cst.locals
  therefore, we really want to take a special union of the 2 branches:
  

  
  (if(__) then x=5 else y=4);z=x --> this produces 2 ssa maps, one with x, one with y.

  To retain the condition, the correct way is to reset the 
  
  However, we still add moves to the cur state to make everything nicer for reg alloc
*)

(*Find all the entries in the list that do not have the same value in map2,
  Ignoring all those that do not appear in the latter <-- not sure*)
val fix_inconsistencies_def = Define`
  (fix_inconsistencies [] = return (Skip,Skip)) ∧ 
  (fix_inconsistencies ((x,y)::xs) =
  do
    (m1,m2) <- fix_inconsistencies xs;
    cur_map <- get_ssa_map;
    (case lookup x cur_map of
      NONE => 
      do
        force_ssa_insert x y;
        return (m1,m2)
      od
    | SOME z =>
      if y = z then return (m1,m2)
      else
      do
        x' <- next_var_rename x;
        y_move <- return (Move [(x',y)]);
        z_move <- return (Move [(x',z)]);
        return (Seq y_move m1,Seq z_move m2)
      od)
  od)`

val ssa_cc_trans_inst_def = Define`
  (ssa_cc_trans_inst Skip = return Skip) ∧ 
  (ssa_cc_trans_inst (Const reg w) = 
    do
      reg' <- next_var_rename reg;
      return (Const reg' w)
    od) ∧ 
  (ssa_cc_trans_inst (Arith (Binop bop r1 r2 ri)) =
    case ri of Reg r3 => 
      do
        r3' <- cur_var_rename r3;
        r2' <- cur_var_rename r2;
        r1' <- next_var_rename r1; (*Must do the reads before the write e.g. x = x+y*)
        return (Arith (Binop bop r1' r2' (Reg r3')))
      od
    | _ => 
      do
        r2' <- cur_var_rename r2;
        r1' <- next_var_rename r1;
        return (Arith (Binop bop r1 r2 ri))
      od) ∧ 
  (ssa_cc_trans_inst (Arith (Shift shift r1 r2 n)) =
    do
      r2' <- cur_var_rename r2;
      r1' <- next_var_rename r1;
      return (Arith (Shift shift r1' r2' n))
    od) ∧ 
  (ssa_cc_trans_inst (Mem Load r (Addr a w)) =
    do
      a' <- cur_var_rename a;
      r' <- next_var_rename r;
      return (Mem Load r' (Addr a' w))
    od) ∧ 
  (ssa_cc_trans_inst (Mem Store r (Addr a w)) =
    do
      a' <- cur_var_rename a;
      r' <- cur_var_rename r;
      return (Mem Store r' (Addr a' w))
    od) ∧ 
  (*Catchall -- for future instructions to be added*)
  (ssa_cc_trans_inst x = return x)`

(*Expressions don't need to be monadic because they never write
  Easier termination this way
*)
val ssa_cc_trans_exp_def = tDefine "ssa_cc_trans_exp" `
  (ssa_cc_trans_exp t (Var num) =
    Var (case lookup num t of NONE => num | SOME x => x)) ∧ 
  (ssa_cc_trans_exp t (Load exp) = Load (ssa_cc_trans_exp t exp)) ∧
  (ssa_cc_trans_exp t (Op wop ls) =
    Op wop (MAP (ssa_cc_trans_exp t) ls)) ∧ 
  (ssa_cc_trans_exp t (Shift sh exp nexp) = 
    Shift sh (ssa_cc_trans_exp t exp) nexp) ∧
  (ssa_cc_trans_exp t expr = expr)`
  (WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)
 
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
  (ssa_cc_trans (Inst i) =
    do
      i' <- ssa_cc_trans_inst i;
      return (Inst i')
    od) ∧ 
  (ssa_cc_trans (Assign num exp) =
    do
      ssa_map <- get_ssa_map;
      exp' <- return (ssa_cc_trans_exp ssa_map exp);
      num' <- next_var_rename num;
      return (Assign num' exp')
    od) ∧ 
  (ssa_cc_trans (Get num store) = 
    do
      num' <- next_var_rename num;
      return (Get num' store)
    od) ∧ 
  (ssa_cc_trans (Store exp num) =
    do
      ssa_map <- get_ssa_map;
      exp' <- return (ssa_cc_trans_exp ssa_map exp);
      num' <- cur_var_rename num;
      return (Store exp' num')
    od) ∧
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
      ssa_map_pre <- get_ssa_map; (*Keep a copy before branch*)
      e2' <- ssa_cc_trans e2;
      ssa_map_post <- get_ssa_map; (*Keep a copy of first branch*)
      set_ssa_map ssa_map_pre; (*Restore to the original ssa_map*)
      e3' <- ssa_cc_trans e3;
      ls <- return (toAList ssa_map_post);
      (e2_cons,e3_cons) <- fix_inconsistencies ls;
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
  (ssa_cc_trans (Set n exp) = 
    do
      ssa_map <- get_ssa_map;
      exp' <- return (ssa_cc_trans_exp ssa_map exp);
      return (Set n exp')
    od) ∧  
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
          ssa_map_pre <- get_ssa_map; (*Keep a copy before branch*) 
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
            do
              ssa_map_post <- get_ssa_map; (*Keep a copy of the ret ssa map*)
              set_ssa_map ssa_map_pre; (*Restore to the original ssa_map*)
              n' <- next_var_rename n;
              ren_exc_handler <- ssa_cc_trans h;
              mov_exc_handler <- return
                (Seq restore_cutset (Seq(Move[n',0]) (ren_exc_handler)));
              ls <- return (toAList ssa_map_post);
              (ret_cons,exc_cons) <- fix_inconsistencies ls;
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

(Seq
(If (Move [(1,2)]) 0 
  (Seq (Move [(1,3)]) Skip) 
  (Seq (Move [(1,5)]) Skip))
(Seq (Move[(5,1)]) (Move [(6,4)]))) init_ssa_state`` 

Skip)

Seq (Alloc 5 (numset_list_insert [1;2;3;4;5;6] LN)) (
Seq (Move [(1,5)]) Skip)))) init_ssa_state``

(Move([(1,2);(3,4)])) init_ssa_state``

Move 1,2
Move 3,1
Move 3,4
Move 1,5

*)
    

