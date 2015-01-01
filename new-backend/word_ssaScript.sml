open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory BasicProvers sortingTheory miscTheory
open word_langTheory word_lemmasTheory word_procTheory word_liveTheory

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
  3) Correctness theorem 
*)

(*If it's in the map then lookup the map else dont remap*)
val option_lookup_def = Define`
  option_lookup t v = case lookup v t of NONE => v | SOME x => x`

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

val list_next_stack_rename_def = Define`
  (list_next_stack_rename [] (ns:num) = ([],ns)) ∧
  (list_next_stack_rename (x::xs) ns =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ns') = (ns,ns+4) in
    let (ys,ns'') = list_next_stack_rename xs ns' in
      (y::ys,ns''))`

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
    (If e1' num' (Seq e2' e2_cons) (Seq e3' e3_cons),ssa_fin,na_fin,ns3)) ∧ 
  (ssa_cc_trans (Alloc num numset) ssa na ns = 
    let num' = option_lookup ssa num in 
    let ls = MAP FST (toAList numset) in
    let cur_ls = MAP (option_lookup ssa) ls in
    let (stack_ls,ns') = list_next_stack_rename cur_ls ns in 
    let stack_set = numset_list_insert stack_ls LN in
    let (ren_ls,ssa',na') = list_next_var_rename ls ssa na in
    let prog = (Seq (Move (ZIP (stack_ls,cur_ls))) 
               (Seq (Alloc num' stack_set)
               (Move (ZIP (ren_ls,stack_ls))))) in
    (prog,ssa',na',ns')) ∧ 
  (ssa_cc_trans (Raise num) ssa na ns =
    let num' = option_lookup ssa num in
    (Raise num',ssa,na,ns)) ∧ 
  (ssa_cc_trans (Return num) ssa na ns =
    let num' = option_lookup ssa num in
    (Return num',ssa,na,ns)) ∧ 
  (ssa_cc_trans Tick ssa na ns = (Tick,ssa,na,ns)) ∧ 
  (ssa_cc_trans (Set n exp) ssa na ns = 
    let exp' = ssa_cc_trans_exp ssa exp in
    (Set n exp',ssa,na,ns)) ∧ 
  (*I think it may be easier to split Calls at the top level into 3 different cases
    because they have different control flow properties:
    1) Tail calls ⇒ just need to rename args, handler should be NONE..
    2) No handler ⇒ add a renamer to the returning handler to fixup the cutsets
    3) Handler ⇒ most complex, we will need renamers in both cases and THEN a consistency rename after
  *)
  (ssa_cc_trans (Call ret dest args h) ssa na ns =
    let names = MAP (option_lookup ssa) args in 
    let conv_args = even_list (LENGTH names) in
    let move_args = (Move (ZIP (conv_args,args))) in
      (case ret of 
        NONE =>
          (Seq move_args (Call NONE dest conv_args h),ssa,na,ns)
      | SOME (ret,numset,ret_handler) => 
          let ls = MAP FST (toAList numset) in
          let cur_ls = MAP (option_lookup ssa) ls in
          let (stack_ls,ns_1) = list_next_stack_rename cur_ls ns in 
          let stack_set = numset_list_insert stack_ls LN in
          let (ren_ls,ssa_1,na_1) = list_next_var_rename ls ssa na in
          let move_cutset = Move (ZIP (stack_ls,cur_ls)) in
          let restore_cutset = Move (ZIP (ren_ls,stack_ls)) in
          (*ssa_1 is before branching*)
          let (ret',ssa_2_p,na_2_p) = next_var_rename ret ssa_1 na_1 in
          let (ren_ret_handler,ssa_2,na_2,ns_2) = 
            (ssa_cc_trans ret_handler ssa_2_p na_2_p ns_1) in
          let mov_ret_handler = 
            (Seq restore_cutset (Seq (Move[ret',0]) (ren_ret_handler))) in
          (case h of
            NONE =>
            let prog = 
              (Seq move_args (Seq move_cutset
              (Call (SOME(0,stack_set,mov_ret_handler)) 
                dest conv_args NONE))) in
            (prog,ssa_2,na_2,ns_2)
          | SOME(n,h) => 
            let (n',ssa_3_p,na_3_p) = next_var_rename n ssa_1 na_2 in
            let (ren_exc_handler,ssa_3,na_3,ns_3) =
              (ssa_cc_trans h ssa_3_p na_3_p ns_2) in
            let mov_exc_handler = 
              (Seq restore_cutset (Seq(Move[n',0]) (ren_exc_handler))) in
            let ls = toAList ssa_2 in
            let (ret_cons,exc_cons,ssa_fin,na_fin) = 
              fix_inconsistencies ls ssa_3 na_3 in
            let cons_ret_handler = Seq mov_ret_handler ret_cons in
            let cons_exc_handler = Seq mov_exc_handler exc_cons in
            let prog = 
              (Seq move_args (Seq move_cutset
              (Call (SOME(0,stack_set,cons_ret_handler))
               dest conv_args (SOME(0,cons_exc_handler))))) in
            (prog,ssa_fin,na_fin,ns_3))))` 

val fix_inconsistencies_no_call = prove(``
  ∀ls ssa na a b c d.
  fix_inconsistencies ls ssa na = (a,b,c,d) ⇒ 
  every_stack_var is_stack_var a ∧ 
  every_stack_var is_stack_var b ∧ 
  call_arg_convention a ∧
  call_arg_convention b``,
  Induct>>
  fs[fix_inconsistencies_def,call_arg_convention_def,every_stack_var_def]>>rw[]>>
  Cases_on`h`>>fs[fix_inconsistencies_def]>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  Cases_on`fix_inconsistencies ls ssa na`>>fs[]>>
  PairCases_on`r'`>>fs[LET_THM]>>
  EVERY_CASE_TAC>>fs[next_var_rename_def,call_arg_convention_def]>>
  pop_assum kall_tac>>rpt (pop_assum (SUBST1_TAC o SYM)>>fs[call_arg_convention_def,every_stack_var_def]))

val list_next_stack_rename_stack_vars = prove(``
  ∀(ls:num list) ns.
  is_stack_var ns ⇒ 
  let (ls',ns') = list_next_stack_rename ls ns in
  is_stack_var ns' ∧
  (*TODO:
  ns ≤ ns' ∧
  ALL_DISTINCT ls' probably need to prove these for correctness later*)  
  EVERY is_stack_var ls'``,
  Induct>>fs[list_next_stack_rename_def,LET_THM]>>rw[]>>
  `is_stack_var (ns+4)` by 
    (fs[is_stack_var_def]>>
    cheat)>>
  res_tac>>
  Cases_on`list_next_stack_rename ls (ns+4)`>>fs[])
  
val ssa_cc_trans_pre_alloc_conventions = store_thm("ssa_cc_trans_pre_alloc_conventions",
``∀prog ssa na ns.
  is_stack_var ns ⇒  
  let (prog',ssa',na',ns') = ssa_cc_trans prog ssa na ns in
  pre_alloc_conventions prog' ∧ 
  is_stack_var ns'``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,LET_THM,LAMBDA_PROD]>>
  Cases_on`prog`>>
  TRY(fs[ssa_cc_trans_def,pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,LET_THM,UNCURRY]>>rw[]>>NO_TAC)>>
  fs[ssa_cc_trans_def,pre_alloc_conventions_def]>>rw[]>>
  fs[call_arg_convention_def,every_stack_var_def]
  >-
  (EVERY_CASE_TAC>>
  TRY(fs[every_stack_var_def,Abbr`move_args`,call_arg_convention_def
      ,Abbr`conv_args`]>>NO_TAC)>>
  rw[]>>
  imp_res_tac list_next_stack_rename_stack_vars>>
  pop_assum(qspec_then`cur_ls` assume_tac)>>
  rfs[LET_THM]
  >-
    (unabbrev_all_tac>>fs[call_arg_convention_def,every_stack_var_def]>>
    first_x_assum(qspecl_then[`r'`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    discharge_hyps>-(fs[word_prog_size_def]>>DECIDE_TAC)>>
    discharge_hyps>-fs[]>>rw[]>>
    fs[domain_numset_list_insert,EVERY_MEM])
  >>
    unabbrev_all_tac>>fs[call_arg_convention_def,every_stack_var_def]>>
    first_assum(qspecl_then[`r''`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    discharge_hyps>-(fs[word_prog_size_def]>>DECIDE_TAC)>>
    discharge_hyps>-fs[]>>strip_tac>>
    first_assum(qspecl_then[`r`,`ssa_3_p`,`na_3_p`,`ns_2`] mp_tac)>>
    discharge_hyps>-(fs[word_prog_size_def]>>DECIDE_TAC)>>
    discharge_hyps>-rfs[]>>
    strip_tac>>rfs[]>>
    fs[domain_numset_list_insert,EVERY_MEM]>>
    metis_tac[fix_inconsistencies_no_call])
  >-
  (*Seq*)
  (first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_x_assum(qspecl_then[`w0`,`ssa'`,`na'`,`ns'`] assume_tac)>>
  rfs[word_prog_size_def]>>
  ntac 2 (pop_assum mp_tac >> discharge_hyps>-DECIDE_TAC)>>
  rw[])
  >-
  (*If*)
  (fs[]>>
  first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_assum(qspecl_then[`w0`,`ssa1`,`na1`,`ns1`] assume_tac)>>
  first_x_assum(qspecl_then[`w1`,`ssa1`,`na2`,`ns2`] assume_tac)>>
  rfs[word_prog_size_def]>>
  ntac 3 (pop_assum mp_tac >> discharge_hyps>-DECIDE_TAC)>>
  rw[]>>
  metis_tac[fix_inconsistencies_no_call])
  >>
  (*Alloc*)
  fs[Abbr`prog`,every_stack_var_def,call_arg_convention_def]>>
  imp_res_tac list_next_stack_rename_stack_vars>>
  pop_assum(qspec_then`cur_ls` assume_tac)>>
  rfs[LET_THM]>>rw[Abbr`stack_set`]>>
  fs[domain_numset_list_insert,EVERY_MEM])

(*
EVAL ``ssa_cc_trans 

(Seq
(If (Move [(1,2)]) 0 
  (Seq (Move [(1,3)]) Skip) 
  (Seq (Move [(1,5)]) Skip))
(Seq (Move[(5,1)]) (Move [(6,4)]))) LN 101 103`` 

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

*)

(*The relation should be that everything that is in st is option_lookup under the ssa_map in cst
When ssa_map is LN, this is trivially true for cst = st*)
val ssa_locals_rel_def = Define`
  ssa_locals_rel ssa st_locs cst_locs =
  strong_locals_rel (option_lookup ssa) (domain st_locs) st_locs cst_locs`

val list_next_var_rename_lemma = prove(``
  ∀ls ssa na ren_ls ssa' na'.
  list_next_var_rename ls ssa na = (ren_ls,ssa',na') ⇒ 
  MAP (option_lookup ssa') ls = ren_ls ∧ 
  ALL_DISTINCT ren_ls ∧ 
  na ≤ na'``,
  Induct>>fs[list_next_var_rename_def,LET_THM,next_var_rename_def]>>
  rw[]>>fs[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>fs[]>>
  res_tac
  >-
    cheat
  >-
    cheat
  >-
    DECIDE_TAC)

(*TODO:need assumptions on na and ns that they are greater than everything in the locals and greater than every program variable so that the insertion is always fresh*)
val ssa_cc_trans_correct = store_thm("ssa_cc_trans_correct",
``∀prog st cst ssa na ns.
  word_state_eq_rel st cst ∧
  st.permute = cst.permute ∧ 
  ssa_locals_rel ssa st.locals cst.locals 
  ⇒
  let (prog',ssa',na',ns') = ssa_cc_trans prog ssa na ns in
  let (res,rst) = wEval(prog,st) in
  let (res',rcst) = wEval(prog',cst) in
  if (res = SOME Error) then T 
  else
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧ 
    (case res of
      NONE => ssa_locals_rel ssa' rst.locals rcst.locals 
    | _    => T )``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>fs[ssa_cc_trans_def]>>rw[]>>
  fs[wEval_def]
  >-
    (qpat_assum`A=res` (SUBST_ALL_TAC o SYM)>>
    qpat_assum`A=res'` (SUBST_ALL_TAC o SYM)>>fs[])
  >>cheat) 

val _ = export_theory();
