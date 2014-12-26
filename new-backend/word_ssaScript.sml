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
  --> Add moves for each argument in the locals e.g. Move(2,2);Move(4,4);prog
  --> SSA pass changes these uniformly to Move(4n+3,2);Move...;prog

  Properties that should be proved:
  1) Every Alloc/Call cutsets only contain stack variables
  2) Every Call uses args [0;2;4...]
  3) Correctness theorem w.r.t. to the monad
*)
val _ = Hol_datatype `
  ssa_state = <| 
                ssa_map :num num_map;
                next_stack : num;
                next_alloc : num
             |>`

(*If it's in the map then lookup the map else dont remap*)
val option_lookup_def = Define`
  option_lookup t v = case lookup v t of NONE => v | SOME x => x`

(*Consistently sets up the next variable rename for v*)
val next_var_rename_def = Define`
  next_var_rename v ssa (na:num) = (na,insert v na ssa,na+4)`

val list_next_var_rename_def = Define`
  (list_next_var_rename [] ssa (na:num) = ([],ssa,na)) ∧
  (list_next_var_rename (x::xs) ssa na =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ssa',na') = next_var_rename x ssa na in
    let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
      (y::ys,ssa'',na''))`

(*Returns renaming under the ssa map for v*)
val cur_var_rename_def = Define`
  cur_var_rename v =
  λs. (return (option_lookup s.ssa_map v)) s`

val get_next_alloc_def = Define`
  get_next_alloc = λs. (s.next_alloc, s with next_alloc := s.next_alloc+4)`

val update_ssa_map_def = Define`
  update_ssa_map v v' = λs.((), s with ssa_map:= insert v v' s.ssa_map)`

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

  If a variable exists in one branch but not the other, then merge it in
  Else,
    if they clash (i.e. both branches assigned to it, giving it different names) then add a move to undo the 
    renames
    Otherwise do nothing*)

(*Find all the entries in the list that do not have the same value in map2,
  Ignoring all those that do not appear in the latter <-- not sure*)
val fix_inconsistencies_def = Define`
  (fix_inconsistencies [] ssa na = (Skip,Skip,ssa,na)) ∧ 
  (fix_inconsistencies ((x,y)::xs) ssa na =
    let (m1,m2,ssa',na') = fix_inconsistencies xs ssa na in 
    (case lookup x ssa' of
      NONE => (m1,m2,insert x y ssa',na')
    | SOME z =>
      if y = z then (m1,m2,ssa',na')
      else
      let (x',ssa'',na'') = next_var_rename x ssa' na' in
      let y_move = Move [(x',y)] in
      let z_move = Move [(x',z)] in 
        (Seq y_move m1,Seq z_move m2,ssa'',na'')))`

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
  (WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

val ssa_cc_trans_def = Define`
  (ssa_cc_trans Skip ssa na ns = (Skip,ssa,na,ns)) ∧ 
  (ssa_cc_trans (Move ls) ssa na ns =
    let ls_1 = MAP FST ls in
    let ls_2 = MAP SND ls in 
    let ren_ls2 = MAP (option_lookup ssa) ls_2 in
    let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
      (Move(ZIP(ren_ls1,ren_ls2)),ssa',na',ns)) ∧ 
  (ssa_cc_trans (Inst i) ssa na ns =
    let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
      (Inst i',ssa',na',ns)) ∧ 
  (ssa_cc_trans (Assign num exp) ssa na ns =
    let exp' = ssa_cc_trans_exp ssa exp in
    let (num',ssa',na') = next_var_rename num ssa na in
      (Assign num' exp',ssa',na',ns)) ∧ 
  (ssa_cc_trans (Get num store) ssa na ns = 
    let (num',ssa',na') = next_var_rename num ssa na in
      (Get num' store,ssa',na',ns)) ∧ 
  (ssa_cc_trans (Store exp num) ssa na ns =
    let exp' = ssa_cc_trans_exp ssa exp in
    let num' = option_lookup ssa num in
      (Store exp' num',ssa,na,ns)) ∧ 
  (ssa_cc_trans (Seq s1 s2) ssa na ns =
    let (s1',ssa',na',ns') = ssa_cc_trans s1 ssa na ns in
    let (s2',ssa'',na'',ns'') = ssa_cc_trans s2 ssa' na' ns' in 
      (Seq s1' s2',ssa'',na'',ns'')) ∧ 
  (*Tricky case 1: we need to merge the ssa results from both branches by
    unSSA-ing the phi functions
  *)
  (ssa_cc_trans (If e1 num e2 e3) ssa na ns = 
    let (e1',ssa1,na1,ns1) = ssa_cc_trans e1 ssa na ns in
    let num' = option_lookup ssa1 num in
    (*ssa1 is the copy for both branches,
      however, we can use new na2 and ns2
    *)
    let (e2',ssa2,na2,ns2) = ssa_cc_trans e2 ssa1 na1 ns1 in
    (*ssa2 is the ssa map for the first branch*)
    let (e3',ssa3,na3,ns3) = ssa_cc_trans e3 ssa1 na2 ns2 in
    (*ssa3 is the ssa map for the second branch, notice we
      continued using na2 and ns2 here though!*)
    let ls = toAList ssa2 in
    let (e2_cons,e3_cons,ssa_fin,na_fin) = 
      fix_inconsistencies ls ssa3 na3 in
    (If e1' num' (Seq e2' e2_cons) (Seq e3' e3_cons),ssa_fin,na_fin,ns3))`
  (*Done till here*)
  (ssa_cc_trans (Alloc num numset) ssa na ns = 
    let num' = option_lookup ssa  num;
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
 
(*TODO: decide whether to prove this with or without permutation oracle machinery
  It is probably easier without, since we can force the key-vals pushed onto the stack to have
  the monotonicity properties wherever required

  needs more assumptions on the monad
*)
val ssa_locals_rel_def = Define`
  ssa_locals_rel ssa_map st_locs cst_locs =
  strong_locals_rel (option_lookup ssa_map) (domain ssa_map) st_locs cst_locs`

val mapM_cur_var_rename = prove(``
  ∀ls.
  mapM cur_var_rename ls ssa = (MAP (option_lookup ssa.ssa_map) ls,ssa)``,
  Induct>>fs[mapM_nil,mapM_cons,BIND_DEF,UNIT_DEF,option_lookup_def,UNCURRY,cur_var_rename_def])

val next_var_rename_rw = prove(``
  next_var_rename h ssa = (ssa.next_alloc,ssa with 
    <|ssa_map := insert h ssa.next_alloc ssa.ssa_map;next_alloc := ssa.next_alloc+4|>)``,
  rw[next_var_rename_def,get_next_alloc_def,BIND_DEF,IGNORE_BIND_DEF,update_ssa_map_def,UNIT_DEF])

val mapM_next_var_rename = prove(``
  ∀ls ssa.
  ALL_DISTINCT ls ⇒ 
  ∃ls' ssa'.
  mapM next_var_rename ls ssa = (ls',ssa') ∧
  ALL_DISTINCT ls' ∧
  ls' = MAP (option_lookup ssa'.ssa_map) ls``,
  Induct>>
  fs[mapM_nil,mapM_cons,BIND_DEF,UNIT_DEF,option_lookup_def,next_var_rename_rw]>>rw[]>>
  qpat_abbrev_tac`ssa' = ssa with <|ssa_map:=A;next_alloc:=B|>`>>
  qexists_tac`ssa'`>>
  first_x_assum(qspec_then`ssa'` assume_tac)>>rfs[Abbr`ssa'`]>>
  cheat)

val mapM_next_var_rename = prove(``
∃ls' ssa'. mapM next_var_rename ls ssa = (ls',ssa')``,
Cases_on`mapM next_var_rename ls ssa`>>fs[])


val ssa_cc_trans_correct = store_thm("ssa_cc_trans_correct",
``∀prog st cst ssa live.
  word_state_eq_rel st cst ∧
  st.permute = cst.permute ∧ 
  ssa_locals_rel ssa.ssa_map st.locals cst.locals 
  ⇒
  let (prog',ssa') = ssa_cc_trans prog ssa in
  let (res,rst) = wEval(prog,st) in
  let (res',rcst) = wEval(prog',cst) in
  if (res = SOME Error) then T 
  else
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧ 
    (case res of
      NONE => ssa_locals_rel ssa'.ssa_map rst.locals rcst.locals 
    | _    => T )``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,LET_THM,LAMBDA_PROD]>>
  Cases_on`prog`>>fs[ssa_cc_trans_def,UNIT_DEF,wEval_def,LET_THM]>>
  fs[BIND_DEF]
  >-
    fs[mapM_cur_var_rename]>>


  ,UNIT_DEF,wEval_def,BIND_DEF,LET_THM]>>
  cheat)
  (*
  >-
  (*Move*)
  cheat
  (*fs[mapM_cur_var_rename]>>
  IF_CASES_TAC>-
  imp_res_tac mapM_next_var_rename>>pop_assum(qspec_then`ssa` assume_tac)>>rfs[]>>
  fs[wEval_def,MAP_ZIP]>>
  FULL_CASE_TAC>> fs[]>>*)
  >-
  (*Inst*)
    cheat
  >-
  (*Assign*)
    cheat
  >-
  (*Get*)
    fs[next_var_rename_rw,wEval_def,word_state_eq_rel_def]>>
    EVERY_CASE_TAC>>fs[set_var_def]>>


  Cases_on`mapM cur_var_rename (MAP SND l) ssa`>>fs[]>>
  
  IF_CASES_TAC>>fs[UNCURRY]>>
  FULL_CASE_TAC>>fs[]>>


  >-
    FULL_CASE_TAC>>fs[UNCURRY]>>



  >>
    fs[UNCURRY]

  Cases_on`get_vars (MAP SND l) st`>>fs[LET_THM]


  (*Move*)
  fs[LET_THM,BIND_DEF,mapM_def,sequence_def,next_var_rename_def]
    
*) 



