open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory BasicProvers sortingTheory miscTheory
open word_langTheory word_lemmasTheory word_procTheory word_liveTheory
open rich_listTheory

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

val even_list_def = Define `
  (even_list = GENLIST (\x.2*x))`

val ALL_DISTINCT_even_list = prove(
 ``!n. ALL_DISTINCT (even_list n)``,
  rw[even_list_def]>>
  simp [ALL_DISTINCT_GENLIST])

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

(*For each entry that is in
  1) Ldiff = in R but not L --> Add moves to LHS
  2) Rdiff = in L but not R --> Add moves to RHS
  3) clash = in both --> For any inconsistencies, combine them
*)
(*This is slightly less efficient for fake moves
  but probably makes the proof easier*)
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
  (fake_moves [] ssa_L ssa_R (na:num) = (Skip:'a word_prog,Skip:'a word_prog,na,ssa_L,ssa_R)) ∧
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
  (WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*Attempt to pull out "renaming" moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
val list_next_var_rename_move_def = Define`
  list_next_var_rename_move ssa n ls =
    let cur_ls = MAP (option_lookup ssa) ls in
    let (new_ls,ssa',n') = list_next_var_rename cur_ls ssa n in
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
               (Seq (Alloc num' stack_set) (ret_mov))) in
    (prog,ssa'',na'')) ∧
  (*TODO: Priority? I think 0 works fine*)
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
    let conv_args = even_list (LENGTH names) in
    let move_args = (Move 0 (ZIP (conv_args,names))) in
    let prog = Seq move_args (Call NONE dest conv_args h) in
      (prog,ssa,na)) ∧ 
  (ssa_cc_trans (Call (SOME(ret,numset,ret_handler,l1,l2)) dest args h) ssa na =
    let ls = MAP FST (toAList numset) in
    let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na+2) ls in
    let stack_set = apply_nummap_key (option_lookup ssa') numset in
    let names = MAP (option_lookup ssa') args in
    let conv_args = even_list (LENGTH names) in
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

val size_tac = discharge_hyps>- (fs[word_prog_size_def]>>DECIDE_TAC)

(*
val fake_moves_conventions = prove(``
  ∀ls.
  let mov = fake_moves ls in 
  call_arg_convention mov ∧ 
  every_stack_var is_stack_var mov``,
  Induct>>rw[]>>unabbrev_all_tac>>
  fs[call_arg_convention_def,every_stack_var_def,fake_moves_def,LET_THM])

val merge_moves_conventions = prove(``
  ∀ls ssaL ssaR na ssaU.
  let (a:'a word_prog,b:'a word_prog,c,d) = 
    merge_moves ssaL ssaR ls na ssaU in
  every_stack_var is_stack_var a ∧ 
  every_stack_var is_stack_var b ∧ 
  call_arg_convention a ∧
  call_arg_convention b``,
  Induct>>rw[merge_moves_def]>>
  fs[call_arg_convention_def,every_stack_var_def]>>
  Cases_on`Lx=Ly`>>fs[]>>
  first_x_assum(qspecl_then[`ssaL`,`ssaR`,`na`,`ssaU`] assume_tac)>>
  rfs[LET_THM]>>
  unabbrev_all_tac>>
  fs[EQ_SYM_EQ,every_stack_var_def,call_arg_convention_def])

val fix_inconsistencies_conventions = prove(``
  ∀ssaL ssaR na.
  let (a:'a word_prog,b:'a word_prog,c,d) = 
    fix_inconsistencies ssaL ssaR na in 
  every_stack_var is_stack_var a ∧ 
  every_stack_var is_stack_var b ∧ 
  call_arg_convention a ∧
  call_arg_convention b``,
  fs[fix_inconsistencies_def,call_arg_convention_def,every_stack_var_def,UNCURRY]>>
  rpt strip_tac>>
  rw[]>>
  unabbrev_all_tac>>
  qabbrev_tac `ls = MAP FST (toAList (inter ssaL ssaR))` >>
  Q.SPECL_THEN [`ls`,`ssaL`,`ssaR`,`na`,`union ssaL ssaR`] 
    assume_tac merge_moves_conventions>>rfs[LET_THM]>>
  fs[every_stack_var_def,call_arg_convention_def]>>
  metis_tac[fake_moves_conventions])

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
  unabbrev_all_tac>>
  rfs[LET_THM,call_arg_convention_def,every_stack_var_def,even_list_def]
  >-
    (first_x_assum(qspecl_then[`r'`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    size_tac>>
    discharge_hyps>-fs[]>>rw[]>>
    fs[domain_numset_list_insert,EVERY_MEM])
  >>
    unabbrev_all_tac>>fs[call_arg_convention_def,every_stack_var_def]>>
    first_assum(qspecl_then[`r''`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    size_tac>>
    discharge_hyps>-fs[]>>strip_tac>>
    first_assum(qspecl_then[`r`,`ssa_3_p`,`na_3_p`,`ns_2`] mp_tac)>>
    size_tac>>
    discharge_hyps>-rfs[]>>
    strip_tac>>rfs[]>>
    fs[domain_numset_list_insert,EVERY_MEM]>>
    rw[]>>
    Q.SPECL_THEN [`ssa_2`,`ssa_3`,`na_3`] assume_tac fix_inconsistencies_conventions>>
    rfs[LET_THM])
  >-
  (*Seq*)
  (first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_x_assum(qspecl_then[`w0`,`ssa'`,`na'`,`ns'`] assume_tac)>>
  ntac 2 (pop_assum mp_tac >> size_tac)>>
  rw[])
  >-
  (*If*)
  (fs[]>>
  first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_assum(qspecl_then[`w0`,`ssa1`,`na1`,`ns1`] assume_tac)>>
  first_x_assum(qspecl_then[`w1`,`ssa1`,`na2`,`ns2`] assume_tac)>>
  ntac 3 (pop_assum mp_tac >> size_tac)>>
  rw[]>>
   Q.SPECL_THEN [`ssa2`,`ssa3`,`na3`] assume_tac fix_inconsistencies_conventions>>
  rfs[LET_THM])
  >>
  (*Alloc*)
  fs[Abbr`prog`,every_stack_var_def,call_arg_convention_def]>>
  imp_res_tac list_next_stack_rename_stack_vars>>
  pop_assum(qspec_then`cur_ls` assume_tac)>>
  rfs[LET_THM]>>rw[Abbr`stack_set`]>>
  fs[domain_numset_list_insert,EVERY_MEM])
*)

(*
EVAL ``ssa_cc_trans 
(Seq
(If (Move 0 [(1,2)]) 0 
  (If (Move 0 [(1,2)]) 0 (Move 0 [(42,3)]) Skip) 
  (Seq (Move 0  [(42,5)]) Skip))
(Seq (Move 0 [(5,42)]) (Move 0 [(6,4)]))) LN 101`` 

*)

(*--- Start proof related defs, proofs --- *)

val sym_sub_tac = SUBST_ALL_TAC o SYM;

(*This might not be the optimal invariant.. because it is very
  restrictive on the ssa_mapping*) 
val ssa_locals_rel_def = Define`
  ssa_locals_rel na ssa st_locs cst_locs =
  ((∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
  (∀x y. lookup x st_locs = SOME y ⇒ 
    x ∈ domain ssa ∧
    lookup (THE (lookup x ssa)) cst_locs = SOME y ∧ 
    (is_alloc_var x ⇒ x < na)))`    

(*ssa_map_ok specifies the form of ssa_maps we care about
  1) The remapped keys are ALL_DISTINCT
  2) The remap keyset is bounded, and no phy vars
*)
val ssa_map_ok_def = Define`
  ssa_map_ok na ssa =
  (∀x y. lookup x ssa = SOME y ⇒ 
    ¬is_phy_var y ∧ y < na ∧ 
    (∀z. z ≠ x ⇒ lookup z ssa ≠ SOME y))`

val list_next_var_rename_lemma_1 = prove(``
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒ 
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧ 
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧ 
  na' = na + 4* len``,
  Induct>>
  fs[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  rw[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>fs[]>>
  res_tac
  >-
    (`∀x. MEM x q ⇒ na < x` by
      (rw[MEM_MAP]>>DECIDE_TAC)>>
    qpat_assum`A = ls'` (sym_sub_tac)>>
    `¬ MEM na q` by 
      (SPOSE_NOT_THEN assume_tac>>
      res_tac>>DECIDE_TAC)>>
    fs[ALL_DISTINCT])
  >-
    (fs[MAP_MAP_o]>>
    qpat_assum`A = ls'` sym_sub_tac>>
    fs[MAP_EQ_f]>>rw[]>>
    DECIDE_TAC)
  >>
    DECIDE_TAC)

val list_next_var_rename_lemma_2 = prove(``
  ∀ls ssa na.
  ALL_DISTINCT ls ⇒ 
  let (ls',ssa',na') = list_next_var_rename ls ssa na in 
  ls' = MAP (λx. THE(lookup x ssa')) ls ∧ 
  domain ssa' = domain ssa ∪ set ls ∧ 
  ∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa``,
  Induct>>fs[list_next_var_rename_def,LET_THM,next_var_rename_def]>>
  rw[]>>
  first_x_assum(qspecl_then[`insert h na ssa`,`na+4`] assume_tac)>>
  rfs[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>Cases_on`r`>>
  fs[lookup_insert,EXTENSION]>>rw[]>>
  metis_tac[])

val exists_tac = qexists_tac`cst.permute`>>
    fs[wEval_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];

val ssa_locals_rel_get_var = prove(``
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  fs[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  rw[]>>
  FULL_CASE_TAC>>fs[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rfs[])

val ssa_locals_rel_get_vars = prove(``
  ∀ls y na ssa st cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y``,
  Induct>>fs[get_vars_def]>>rw[]>>
  Cases_on`get_var h st`>>fs[]>>
  imp_res_tac ssa_locals_rel_get_var>>fs[]>>
  Cases_on`get_vars ls st`>>fs[]>>
  res_tac>>fs[])

val ALOOKUP_ZIP_FAIL = prove(``
  ∀A B x.
  LENGTH A = LENGTH B ⇒  
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)``,
  rw[]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  fs[MAP_ZIP])

val ssa_map_ok_extend = prove(``
  ssa_map_ok na ssa ∧ 
  ¬is_phy_var na ⇒  
  ssa_map_ok (na+4) (insert h na ssa)``,
  fs[ssa_map_ok_def]>>
  rw[]>>fs[lookup_insert]>>
  Cases_on`x=h`>>fs[]>>
  res_tac>-
    DECIDE_TAC
  >-
    (SPOSE_NOT_THEN assume_tac>>res_tac>>
    DECIDE_TAC)
  >>
    Cases_on`z=h`>>fs[]>>DECIDE_TAC)

(*
val list_next_var_rename_correct = prove(``
  ∀ls ssa na pri.
  is_alloc_var na ∧
  wEval (Move pri ls,st) = (NONE,rst) ∧  
  ssa_map_ok na ssa
  ⇒ 
  let(ls',ssa',na') = list_next_var_rename ls ssa na in
  (ssa_locals_rel na ssa st.locals cst.locals 
  ⇒ 
  let (res,rcst) = wEval(Move pri (ZIP (ls',ls)),cst) in
    res = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa) ∧ 
    (∀x y. (x < na ∧ lookup x cst.locals = SOME y)
    ⇒  lookup x rcst.locals = SOME y) ∧
    ssa_locals_rel na' ssa' rst.locals rcst.locals ∧ 
    word_state_eq_rel rst rcst)``,
  Induct>>fs[merge_moves_def]>-
  (rw[]>>
  fs[wEval_def,word_state_eq_rel_def,get_vars_def,set_vars_def,list_insert_def]>>
  rfs[]>>rw[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pri`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  Cases_on`wEval(Move pri q,cstL)`>>fs[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rfs[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x'` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  discharge_hyps>-
    (fs[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  rw[]>>fs[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    fs[lookup_insert])
  >-
    (fs[ssa_locals_rel_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (Cases_on`x''=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h ssaL = SOME x'` (SUBST_ALL_TAC)>>
      fs[])>>
      res_tac>>
      fs[domain_lookup]>>
       `v'' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      fs[word_state_eq_rel_def])
 *)

val merge_moves_frame = prove(``
  ∀ls na ssaL ssaR.
  is_alloc_var na 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧  
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧ 
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
  Induct>>fs[merge_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>fs[]>>
  (CONJ_TAC>-
    (fs[is_alloc_var_def]>>
    (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`r1`,`4`] assume_tac)>>
    rfs[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions])

val merge_moves_fst = prove(``
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  na ≤ na' ∧ 
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveL) ∧ 
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveR) ``,
  Induct>>fs[merge_moves_def]>>rw[]>>
  fs[EVERY_MAP]>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`]assume_tac)>>
  rfs[LET_THM]>>
  EVERY_CASE_TAC>>fs[]>>
  qpat_assum`A = moveL` (sym_sub_tac)>>
  qpat_assum`A = moveR` (sym_sub_tac)>>
  fs[EVERY_MEM]>>rw[]>>
  res_tac>>
  DECIDE_TAC)

(*Characterize result of merge_moves*)
val merge_moves_frame2 = prove(``
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∧ 
  domain ssaR' = domain ssaR ∧
  ∀x. MEM x ls ∧ x ∈ domain (inter ssaL ssaR) ⇒ 
    lookup x ssaL' = lookup x ssaR'``,
  Induct>>fs[merge_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>fs[]
  >-
    metis_tac[]
  >> TRY
    (fs[domain_inter]>>rw[]>>
    qpat_assum`A=domain ssaL` (sym_sub_tac)>>
    qpat_assum`A=domain ssaR` (sym_sub_tac)>>
    fs[domain_lookup]>>
    fs[optionTheory.SOME_11]>>
    res_tac>>
    rfs[])
  >>
    fs[EXTENSION]>>rw[]>>
    metis_tac[domain_lookup,lookup_insert])

(*Another frame proof about unchanged lookups*)
val merge_moves_frame3 = prove(``
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  ∀x. ¬MEM x ls ∨ x ∉ domain (inter ssaL ssaR) ⇒ 
    lookup x ssaL' = lookup x ssaL ∧ 
    lookup x ssaR' = lookup x ssaR``,
  Induct>>fs[merge_moves_def]>-
    (rw[]>>fs[])>>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(metis_tac[])>>
  rw[]>>fs[lookup_insert]>>
  IF_CASES_TAC>>fs[]>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame2>>
  rfs[LET_THM]>>
  `h ∈ domain r3 ∧ h ∈ domain r2` by fs[domain_lookup]>>
  fs[domain_inter]>>
  metis_tac[])

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the cases are basically copy pasted... *)

val mov_eval_head = prove(``
  wEval(Move p moves,st) = (NONE,rst) ∧
  y ∈ domain st.locals ∧
  ¬MEM y (MAP FST moves) ∧ 
  ¬MEM x (MAP FST moves)
  ⇒ 
  wEval(Move p ((x,y)::moves),st) = (NONE, rst with locals:=insert x (THE (lookup y st.locals)) rst.locals)``,
  fs[wEval_def,get_vars_def,get_var_def,domain_lookup]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>
  fs[set_vars_def,list_insert_def]>>
  qpat_assum `A=rst` (sym_sub_tac)>>fs[])
   
val merge_moves_correctL = prove(``
  ∀ls na ssaL ssaR stL cstL pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧  
  ssa_map_ok na ssaL 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒ 
  let (resL,rcstL) = wEval(Move pri moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧ 
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧ 
    word_state_eq_rel cstL rcstL)``,
  Induct>>fs[merge_moves_def]>-
  (rw[]>>
  fs[wEval_def,word_state_eq_rel_def,get_vars_def,set_vars_def,list_insert_def]>>
  rfs[]>>rw[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pri`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  Cases_on`wEval(Move pri q,cstL)`>>fs[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rfs[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x'` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  discharge_hyps>-
    (fs[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  rw[]>>fs[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    fs[lookup_insert])
  >-
    (fs[ssa_locals_rel_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (Cases_on`x''=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h ssaL = SOME x'` (SUBST_ALL_TAC)>>
      fs[])>>
      res_tac>>
      fs[domain_lookup]>>
       `v'' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      fs[word_state_eq_rel_def])
 
val merge_moves_correctR = prove(``
  ∀ls na ssaL ssaR stR cstR pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧ 
  ssa_map_ok na ssaR 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒ 
  let (resR,rcstR) = wEval(Move pri moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧ 
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧ 
    word_state_eq_rel cstR rcstR)``,
  Induct>>fs[merge_moves_def]>-
  (rw[]>>
  fs[wEval_def,word_state_eq_rel_def,get_vars_def,set_vars_def,list_insert_def]>>
  rfs[]>>rw[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`,`pri`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  Cases_on`wEval(Move pri r0,cstR)`>>fs[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rfs[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x` mp_tac)>>discharge_hyps>-
    (SPOSE_NOT_THEN assume_tac>>fs[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  discharge_hyps>-
    (fs[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  rw[]>>fs[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    fs[lookup_insert])
  >-
    (fs[ssa_locals_rel_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (Cases_on`x''=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h ssaR = SOME x` (SUBST_ALL_TAC)>>
      fs[])>>
      res_tac>>
      fs[domain_lookup]>>
       `v'' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      fs[word_state_eq_rel_def])

val fake_moves_frame = prove(``
  ∀ls na ssaL ssaR.
  is_alloc_var na 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧  
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧ 
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
  Induct>>fs[fake_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[]>>
  Cases_on`fake_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>fs[]>>
  (CONJ_TAC>-
    (fs[is_alloc_var_def]>>
    (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`r1`,`4`] assume_tac)>>
    rfs[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions])

val fake_moves_frame2 = prove(``
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧ 
  domain ssaR' = domain ssaR ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧
  ∀x. MEM x ls ∧ x ∉ domain(inter ssaL ssaR) ⇒ lookup x ssaL' = lookup x ssaR'``,
  Induct>>fs[fake_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[LET_THM]>>
  Cases_on`fake_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>
  fs[EXTENSION,domain_inter]>>rw[]>>
  metis_tac[domain_lookup,lookup_insert])

val fake_moves_frame3 = prove(``
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves ls ssaL ssaR na in
  ∀x. ¬ MEM x ls ∨ x ∈ domain(inter ssaL ssaR) ⇒ 
    lookup x ssaL' = lookup x ssaL ∧ 
    lookup x ssaR' = lookup x ssaR``,
  Induct>>fs[fake_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[LET_THM]>>
  Cases_on`fake_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  Q.ISPECL_THEN[`ls`,`na`,`ssaL`,`ssaR`] assume_tac fake_moves_frame2>>
  rfs[LET_THM]>>
  EVERY_CASE_TAC>>
  fs[EXTENSION,domain_inter]>>rw[]>>
  fs[lookup_insert]>>
  IF_CASES_TAC>>fs[]>>
  `h ∈ domain r2` by fs[domain_lookup]>>
  res_tac>>
  fs[lookup_NONE_domain])

val fake_moves_correctL = prove(``
  ∀ls na ssaL ssaR stL cstL.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧ 
  ssa_map_ok na ssaL
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒ 
  let (resL,rcstL) = wEval(moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧ 
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧ 
    word_state_eq_rel cstL rcstL)``,
  Induct>>fs[fake_moves_def]>-
    (rw[]>>
    fs[wEval_def,word_state_eq_rel_def,get_vars_def,set_vars_def,list_insert_def]>>
    rfs[]>>rw[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`fake_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  fs[wEval_def,LET_THM,wEval_def,fake_move_def,word_exp_def]>>
  Cases_on`wEval(q,cstL)`>>fs[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r2` by 
    (imp_res_tac fake_moves_frame>>
    fs[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>rfs[])
  >-
    (fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,get_vars_def,get_var_def,set_vars_def,list_insert_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h r2 = SOME v'''` SUBST_ALL_TAC>>
      fs[]>>
      rfs[])
      >>
      res_tac>>fs[]>>
      `v''' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def])
  >-
    (fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,set_var_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
        (res_tac>>fs[])
      >>
      res_tac>>fs[]>>
      `v' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def]))
 
val fake_moves_correctR = prove(``
  ∀ls na ssaL ssaR stR cstR.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧ 
  ssa_map_ok na ssaR 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒ 
  let (resR,rcstR) = wEval(moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧ 
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧ 
    word_state_eq_rel cstR rcstR)``,
  Induct>>fs[fake_moves_def]>-
  (rw[]>>
  fs[wEval_def,word_state_eq_rel_def,get_vars_def,set_vars_def,list_insert_def]>>
  rfs[]>>rw[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`fake_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  fs[wEval_def,LET_THM,wEval_def,fake_move_def,word_exp_def]>>
  Cases_on`wEval(r0,cstR)`>>fs[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r3` by 
    (imp_res_tac fake_moves_frame>>
    fs[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>rfs[])
  >-
    (fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,set_var_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
        (res_tac>>fs[])
      >>
      res_tac>>fs[]>>
      `v' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def])
  >-
    (fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,get_vars_def,get_var_def,set_vars_def,list_insert_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h r3 = SOME v'''` SUBST_ALL_TAC>>
      fs[]>>
      rfs[])
      >>
      res_tac>>fs[]>>
      `v''' < r1` by 
        (fs[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def]))
 
(*Swapping lemma that allows us to swap in ssaL for ssaR
  after we are done fixing them*)
val ssa_eq_rel_swap = prove(``
  ssa_locals_rel na ssaR st.locals cst.locals ∧ 
  domain ssaL = domain ssaR ∧ 
  (∀x. lookup x ssaL = lookup x ssaR) ⇒ 
  ssa_locals_rel na ssaL st.locals cst.locals``,
  rw[ssa_locals_rel_def]) 

val ssa_locals_rel_more = prove(``
  ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒ 
  ssa_locals_rel na' ssa stlocs cstlocs``,
  rw[ssa_locals_rel_def]>>fs[]
  >- metis_tac[]>>
  res_tac>>fs[]>>
  DECIDE_TAC)

val ssa_map_ok_more = prove(``
  ssa_map_ok na ssa ∧ na ≤ na' ⇒ 
  ssa_map_ok na' ssa``,
  fs[ssa_map_ok_def]>>rw[] 
  >-
    metis_tac[]>>
  res_tac>>fs[]>>DECIDE_TAC)
  
val toAList_domain = prove(``
  ∀x. MEM x (MAP FST (toAList t)) ⇔ x ∈ domain t``,
  fs[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup])
   
val get_vars_eq = prove(
  ``(set ls) SUBSET domain st.locals ==> ?y. get_vars ls st = SOME y /\
                                             y = MAP (\x. THE (lookup x st.locals)) ls``,
  Induct_on`ls`>>fs[get_vars_def,get_var_def]>>rw[]>>
  fs[domain_lookup])

val get_var_ignore = prove(``
  ∀ls a.
  get_var x cst = SOME y ∧ 
  ¬MEM x ls ∧ 
  LENGTH ls = LENGTH a ⇒ 
  get_var x (set_vars ls a cst) = SOME y``,
  Induct>>fs[get_var_def,set_vars_def,list_insert_def]>>
  rw[]>>
  Cases_on`a`>>fs[list_insert_def,lookup_insert])

(*TODO: REMOVE CHEATS*)
val list_next_var_rename_move_preserve = GEN_ALL(prove(``
  ssa_locals_rel na ssa st.locals cst.locals ∧ 
  set ls ⊆ domain st.locals ∧ 
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssa ∧ 
  word_state_eq_rel st cst 
  ⇒
  let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
  let (res,rcst) = wEval (mov,cst) in
    res = NONE ∧ 
    ssa_locals_rel na' ssa' st.locals rcst.locals ∧ 
    word_state_eq_rel st rcst``,
  fs[list_next_var_rename_move_def,ssa_locals_rel_def]>>
  rw[]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  `ALL_DISTINCT cur_ls` by 
    (fs[Abbr`cur_ls`]>>
    match_mp_tac ALL_DISTINCT_MAP_INJ>>
    rw[option_lookup_def]>>
    TRY(`x ∈ domain st.locals ∧ y ∈ domain st.locals` by 
      (fs[SUBSET_DEF]>>NO_TAC))>>
    TRY(`x' ∈ domain st.locals ∧ y' ∈ domain st.locals` by 
      (fs[SUBSET_DEF]>>NO_TAC))>>
    fs[domain_lookup]>>res_tac>>
    fs[ssa_map_ok_def]>>
    metis_tac[])>>
  imp_res_tac list_next_var_rename_lemma_2>>
  pop_assum kall_tac>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  fs[LET_THM,wEval_def]>>rfs[]>>
  rfs[MAP_ZIP,LENGTH_COUNT_LIST]>>fs[]>>
  `set cur_ls ⊆ domain cst.locals` by 
    (fs[SUBSET_DEF,Abbr`cur_ls`]>>rw[MEM_MAP]>>
    res_tac>>
    fs[domain_lookup]>>
    res_tac>>
    fs[option_lookup_def]>>
    qpat_assum`A=SOME v''` SUBST_ALL_TAC>>fs[]>>
    metis_tac[])>>
  imp_res_tac get_vars_eq>>
  fs[]>>qpat_assum`A=rcst` (sym_sub_tac)
  >-
    (fs[set_vars_def]>>
    Cases_on`MEM x cur_ls`>>fs[]
    >-
      cheat
      (*y in the first part of the list insert*)
    >>
    res_tac>>
    (*y in cst.locals already*)
    cheat)
  >-
    (fs[set_vars_def,lookup_list_insert]>>
    Cases_on`MEM x cur_ls`>>fs[]
    >-
      cheat (*should be in the ZIP*)
    >>
      (*Shouldn't be in the ZIP*)
      cheat)
  >-
    (res_tac>>DECIDE_TAC)
  >>
    fs[word_state_eq_rel_def,set_vars_def]))

val get_vars_list_insert_eq_gen= prove(
``!ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars ls (st with locals := list_insert (a++ls) (b++x) locs) = SOME x``,
  ho_match_mp_tac list_insert_ind>>
  rw[]>-
    (Cases_on`x`>>fs[get_vars_def])>>
  fs[get_vars_def,get_var_def,lookup_list_insert]>>
  `LENGTH (ls::ls') = LENGTH (x::x')` by fs[]>>
  IMP_RES_TAC rich_listTheory.ZIP_APPEND>>
  ntac 9 (pop_assum (SUBST1_TAC o SYM))>>
  fs[ALOOKUP_APPEND]>>
  first_assum(qspec_then `ls` assume_tac)>>fs[]>>
  `ALOOKUP (ZIP (a,b)) ls = NONE` by metis_tac[ALOOKUP_NONE,MEM_MAP,MAP_ZIP]>>
  fs[]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  `LENGTH (a++[ls]) = LENGTH (b++[x])` by fs[]>> rfs[]>>
  `a++[ls]++ls' = a++ls::ls' /\ b++[x]++x' = b++x::x'` by fs[]>>
  ntac 2 (pop_assum SUBST_ALL_TAC)>> fs[])

val get_vars_set_vars_eq = prove(``
  ∀ls x.
  ALL_DISTINCT ls ∧ LENGTH x = LENGTH ls ⇒ 
  get_vars ls (set_vars ls x cst) = SOME x``,
  fs[get_vars_def,set_vars_def]>>rw[]>>
  Q.ISPECL_THEN [`cst`,`ls`,`x`,`cst.locals`,`[]:num list`
    ,`[]:'a word_loc list`] mp_tac (GEN_ALL get_vars_list_insert_eq_gen)>>
  discharge_hyps>>fs[])

val domain_list_insert = prove(
  ``!a b locs. LENGTH a = LENGTH b ==>
    domain (list_insert a b locs) = domain locs UNION set a``,
  Induct_on`a`>>Cases_on`b`>>fs[list_insert_def]>>rw[]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM])

val ssa_locals_rel_ignore_set_var = prove(``
  ssa_map_ok na ssa ∧ 
  ssa_locals_rel na ssa st.locals cst.locals ∧ 
  is_phy_var v 
  ⇒ 
  ssa_locals_rel na ssa st.locals (set_var v a cst).locals``,
  rw[ssa_locals_rel_def,ssa_map_ok_def,set_var_def]>>
  fs[lookup_insert]>-
    metis_tac[]
  >>
  res_tac>>
  fs[domain_lookup]>>
  metis_tac[])

val ssa_locals_rel_ignore_list_insert = prove(``
  ssa_map_ok na ssa ∧ 
  ssa_locals_rel na ssa st.locals cst.locals ∧ 
  EVERY is_phy_var ls ∧ 
  LENGTH ls = LENGTH x
  ⇒ 
  ssa_locals_rel na ssa st.locals (list_insert ls x cst.locals)``,
  rw[ssa_locals_rel_def,ssa_map_ok_def]>>
  fs[domain_list_insert,lookup_list_insert]>-
    metis_tac[]
  >>
  res_tac>>
  fs[domain_lookup]>>
  res_tac>>
  `ALOOKUP (ZIP(ls,x)) v = NONE` by 
    (rw[ALOOKUP_FAILS,MEM_ZIP]>>
    metis_tac[EVERY_EL])>>
  fs[])

val is_alloc_var_add = prove(``
  is_alloc_var na ⇒ is_alloc_var (na+4)``,
  fs[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rfs[]))

val is_stack_var_add= prove(``
  is_stack_var na ⇒ is_stack_var (na+4)``,
  fs[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rfs[]))

val is_alloc_var_flip = prove(``
  is_alloc_var na ⇒ is_stack_var (na+2)``,
  fs[is_alloc_var_def,is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`na`,`2`] assume_tac)>>
    rw[]>>fs[]))

val is_stack_var_flip = prove(``
  is_stack_var na ⇒ is_alloc_var (na+2)``,
  fs[is_alloc_var_def,is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`na`,`2`] assume_tac)>>
    rw[]>>fs[]))

val list_next_var_rename_props = prove(``
  ∀ls ssa na ls' ssa' na'.
  (is_alloc_var na ∨ is_stack_var na) ∧ 
  ssa_map_ok na ssa ∧ 
  list_next_var_rename ls ssa na = (ls',ssa',na')
  ⇒
  na ≤ na' ∧  
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧ 
  ssa_map_ok na' ssa'``,
  Induct>>fs[list_next_var_rename_def,next_var_rename_def]>>
  LET_ELIM_TAC>>
  first_x_assum(qspecl_then[`ssa''`,`na''`,`ys`,`ssa'''`,`na'''`] 
    mp_tac)>>
  (discharge_hyps>-
    (fs[ssa_map_ok_def]>>rw[]
    >-
      metis_tac[is_alloc_var_add,is_stack_var_add]
    >-
      (fs[lookup_insert]>>Cases_on`x=h`>>fs[]>>
      metis_tac[convention_partitions])
    >-
      (fs[lookup_insert]>>Cases_on`x=h`>>fs[]>>
      res_tac>>DECIDE_TAC)
    >>
      fs[lookup_insert]>>Cases_on`x=h`>>Cases_on`z=h`>>fs[]
      >-
        (SPOSE_NOT_THEN assume_tac>>res_tac>>fs[])
      >>
        res_tac>>DECIDE_TAC))>>
  rw[]>> TRY(DECIDE_TAC)>> fs[]>>
  metis_tac[is_alloc_var_add,is_stack_var_add])

val list_next_var_rename_move_props = prove(``
  ∀ls ssa na ls' ssa' na'.
  (is_alloc_var na ∨ is_stack_var na) ∧ 
  ssa_map_ok na ssa ∧ 
  list_next_var_rename_move ssa na ls = (ls',ssa',na')
  ⇒
  na ≤ na' ∧  
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧ 
  ssa_map_ok na' ssa'``,
  fs[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  fs[]>>
  imp_res_tac list_next_var_rename_props)

val ssa_cc_trans_inst_props = prove(``
  ∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ∧ 
  ssa_map_ok na ssa ∧ 
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'``,
  Induct>>rw[]>>
  TRY(Cases_on`a`)>>
  TRY(Cases_on`r`)>>
  TRY(Cases_on`m`)>>
  fs[ssa_cc_trans_inst_def,next_var_rename_def]>>rw[]>>
  fs[LET_THM]>>
  TRY(DECIDE_TAC)>>
  metis_tac[ssa_map_ok_extend,convention_partitions,is_alloc_var_add])
   
val exp_tac = (LET_ELIM_TAC>>fs[next_var_rename_def]>>
    TRY(DECIDE_TAC)>>
    metis_tac[ssa_map_ok_extend,convention_partitions,is_alloc_var_add])

val fix_inconsistencies_props = prove(``
  ∀ssaL ssaR na a b na' ssaU.
  fix_inconsistencies ssaL ssaR na = (a,b,na',ssaU) ∧ 
  is_alloc_var na ∧ 
  ssa_map_ok na ssaL ∧
  ssa_map_ok na ssaR 
  ⇒
  na ≤ na' ∧ 
  is_alloc_var na' ∧
  ssa_map_ok na' ssaU``,
  fs[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`var_union`] assume_tac)>> 
  Q.ISPECL_THEN [`var_union`,`na''`,`ssa_L'`,`ssa_R'`] assume_tac fake_moves_frame>>
  rfs[LET_THM]>>
  DECIDE_TAC)

(*TODO: FIGURE OUT WHY METIS FAILS*)
(*Prove the properties that hold of ssa_cc_trans independent of semantics*)
val ssa_cc_trans_props = prove(``
  ∀prog ssa na prog' ssa' na'.
  ssa_cc_trans prog ssa na = (prog',ssa',na') ∧ 
  ssa_map_ok na ssa ∧ 
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'``,
  ho_match_mp_tac (fetch "-" "ssa_cc_trans_ind")>>
  fs[ssa_cc_trans_def]>>
  strip_tac >-
    (LET_ELIM_TAC>>
    fs[]>>
    metis_tac[list_next_var_rename_props])>>
  strip_tac >-
    (LET_ELIM_TAC>>
    fs[]>>
    metis_tac[ssa_cc_trans_inst_props])>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    (LET_ELIM_TAC>>fs[]>>
    DECIDE_TAC)>>
  strip_tac >-
    (LET_ELIM_TAC>>fs[]>>
    imp_res_tac ssa_map_ok_more>>
    first_x_assum(qspec_then`na3` assume_tac)>>rfs[]>>
    fs[]>>
    imp_res_tac fix_inconsistencies_props>>DECIDE_TAC)>>
  strip_tac >-
    (fs[list_next_var_rename_move_def]>>LET_ELIM_TAC>>fs[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (rw[Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>fs[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    (*metis_tac doesnt seem to like the theorem so we do this manually*)
    assume_tac list_next_var_rename_props>>
    first_assum(qspecl_then[`cur_ls`,`ssa`,`na+2`,`new_ls`,`ssa'''`,`na''`] mp_tac)>>
    `is_stack_var (na+2)` by metis_tac[is_alloc_var_flip]>>
    (discharge_hyps>-metis_tac[ssa_map_ok_more])>>
    strip_tac>>
    first_x_assum(qspecl_then[`cur_ls'`,`ssa_cut`,`na''+2`,`new_ls'`,`ssa'`,`na'`] mp_tac)>>
    `is_alloc_var (na''+2)` by metis_tac[is_stack_var_flip]>>
    (discharge_hyps>- metis_tac[ssa_map_ok_more]) >>
    rw[]>>
    DECIDE_TAC)>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    exp_tac>>
  strip_tac >-
    (LET_ELIM_TAC>>fs[]>>
    rfs[])>>
  (*Calls*)
  Cases_on`h`>-
    cheat >>
  cheat)

val PAIR_ZIP_MEM = prove(``
  LENGTH c = LENGTH d ∧ 
  MEM (a,b) (ZIP (c,d)) ⇒ 
  MEM a c ∧ MEM b d``,
  rw[]>>imp_res_tac MEM_ZIP>>
  fs[MEM_EL]>>
  metis_tac[])

val ALOOKUP_ZIP_MEM = prove(``
  LENGTH a = LENGTH b ∧ 
  ALOOKUP (ZIP (a,b)) x = SOME y
  ⇒ 
  MEM x a ∧ MEM y b``,
  rw[]>>imp_res_tac ALOOKUP_MEM>>
  metis_tac[PAIR_ZIP_MEM])

val ALOOKUP_ALL_DISTINCT_REMAP = prove(``
  ∀ls x f y n.
  LENGTH ls = LENGTH x ∧
  ALL_DISTINCT (MAP f ls) ∧ 
  n < LENGTH ls ∧ 
  ALOOKUP (ZIP (ls,x)) (EL n ls) = SOME y
  ⇒ 
  ALOOKUP (ZIP (MAP f ls,x)) (f (EL n ls)) = SOME y``,
  Induct>>rw[]>>
  Cases_on`x`>>fs[]>>
  imp_res_tac ALL_DISTINCT_MAP>>
  Cases_on`n`>>fs[]>>
  `¬MEM h ls` by metis_tac[MEM_MAP]>>
  fs[MEM_EL]>>
  pop_assum(qspec_then`n'` assume_tac)>>rfs[]>>
  fs[]>>
  `f h ≠ f (EL n' ls)` by 
    (SPOSE_NOT_THEN assume_tac>>
    first_x_assum(qspec_then`n'` assume_tac)>>rfs[]>>
    metis_tac[EL_MAP])>>
  metis_tac[])

val set_toAList_keys = prove(``
  set (MAP FST (toAList t)) = domain t``,
  fs[EXTENSION,MEM_MAP]>>rw[]>>
  fs[EXISTS_PROD,MEM_toAList,domain_lookup])

fun fcs t r = Cases_on t>>Cases_on r>>fs[]

val is_phy_var_tac = 
    fs[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

val ssa_map_ok_inter = prove(``
  ssa_map_ok na ssa ⇒
  ssa_map_ok na (inter ssa ssa')``,
  fs[ssa_map_ok_def,lookup_inter]>>rw[]>>EVERY_CASE_TAC>>
  fs[]>>
  metis_tac[])

val ZIP_MAP_FST_SND_EQ = prove(``
  ∀ls. ZIP (MAP FST ls,MAP SND ls) = ls``,
  Induct>>fs[])

val ssa_cc_trans_correct = store_thm("ssa_cc_trans_correct",
``∀prog st cst ssa na.
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  (*The following 3 assumptions are from the transform properties and
    independent of semantics*)
  is_alloc_var na ∧
  every_var (λx. x < na) prog ∧
  ssa_map_ok na ssa 
  ⇒
  ∃perm'.
  let (res,rst) = wEval(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (prog',ssa',na') = ssa_cc_trans prog ssa na in
  let (res',rcst) = wEval(prog',cst) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧ 
    (case res of
      NONE => 
        ssa_locals_rel na' ssa' rst.locals rcst.locals 
    | _    => T )``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,wEval_def]>>
  Cases_on`prog`
  >-
    exists_tac
  >-
    (exists_tac>>EVERY_CASE_TAC>>fs[set_vars_def]>>
    Cases_on`list_next_var_rename (MAP FST l) ssa na`>>
    Cases_on`r`>>
    fs[wEval_def]>>
    imp_res_tac list_next_var_rename_lemma_1>>
    imp_res_tac list_next_var_rename_lemma_2>>
    fs[LET_THM]>>
    fs[MAP_ZIP,LENGTH_COUNT_LIST]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    pop_assum(qspecl_then[`ssa`,`na`,`cst`] assume_tac)>>
    rfs[set_vars_def]>>
    fs[ssa_locals_rel_def]>>
    first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
    rfs[]>>
    imp_res_tac get_vars_length_lemma>>
    CONJ_ASM1_TAC
    >-
      (rw[domain_lookup]>>
      fs[lookup_list_insert]>>
      EVERY_CASE_TAC>>
      rfs[ALOOKUP_NONE,MAP_ZIP]>>
      `¬ (MEM x' (MAP FST l))` by
        (CCONTR_TAC>>
        fs[MEM_MAP]>>
        first_x_assum(qspec_then`x'` assume_tac)>>
        rfs[]>>
        metis_tac[])>>
      `x' ∈ domain q' ∧ x' ∈ domain ssa` by
        (CONJ_ASM1_TAC>-
          fs[domain_lookup]
        >>
        fs[EXTENSION]>>metis_tac[])>>
      metis_tac[domain_lookup])
    >> 
    fs[strong_locals_rel_def]>>rw[]>>rfs[lookup_list_insert]
    >-
      (Cases_on`MEM x' (MAP FST l)`>>
      fs[]>>
      Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
      rfs[]>>fs[])
    >-
      (Cases_on`MEM x' (MAP FST l)`>>
      fs[]
      >-
        (`ALL_DISTINCT (MAP FST (ZIP (MAP FST l,x)))` by fs[MAP_ZIP]>>
        fs[MEM_EL]>>
        imp_res_tac ALOOKUP_ALL_DISTINCT_EL>>
        pop_assum(qspec_then `n'` mp_tac)>>
        discharge_hyps>>
        fs[LENGTH_ZIP]>>rw[]>>
        rfs[EL_ZIP]>>fs[]>>
        imp_res_tac ALOOKUP_ALL_DISTINCT_REMAP>>
        fs[LENGTH_MAP])
      >>
      Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
      rfs[ssa_map_ok_def]>>fs[]>>
      res_tac>>
      fs[domain_lookup]>>res_tac>>
      qabbrev_tac `ls = MAP (\x. THE (lookup x q')) (MAP FST l)`>>
      qsuff_tac `ALOOKUP (ZIP (ls,x)) v = NONE` >>
      fs[]>>fs[ALOOKUP_NONE]>>
      qpat_assum`A = ls` (sym_sub_tac)>>
      fs[MAP_ZIP,LENGTH_COUNT_LIST]>>
      fs[MEM_MAP]>>rw[]>>
      DECIDE_TAC)
    >>
      EVERY_CASE_TAC>>rfs[every_var_def]
      >-
        metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
      >>
        `MEM x' (MAP FST l)` by 
          metis_tac[ALOOKUP_ZIP_MEM,LENGTH_MAP]>>
        fs[EVERY_MEM]>>
        metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``])
  >-(*Inst*) cheat
  >-(*Assign*)
    (exists_tac>>cheat)
  >-(*Get -- Useful for illustrating the need for
    the various assumptions on na*) 
    (exists_tac>>EVERY_CASE_TAC>>
    fs[next_var_rename_def,wEval_def]>>
    fs[set_var_def,ssa_locals_rel_def]>>
    rw[]>>fs[lookup_insert]>>Cases_on`x'=n`>>fs[]
    >-
      metis_tac[]
    >-
      (res_tac>>
      fs[domain_lookup,ssa_map_ok_def]>>
      first_x_assum(qspecl_then[`x'`,`v`]assume_tac)>>
      (*Next part is a key reasoning step --
        We only have alloc_vars < na in the range of ssa
        Otherwise, the new one may overwrite an old mapping
      *)
      rfs[]>>
      `v ≠ na` by DECIDE_TAC >>
      fs[])
    >-
      (*This illustrates need for every_var assumption*)
      (fs[every_var_def]>>DECIDE_TAC)
    >>
      (*Finally, this illustrates need for <na assumption on st.locals*)
      fs[ssa_map_ok_def]>>res_tac>>fs[]>>DECIDE_TAC)
  >-(*Set*)
    (exists_tac>>cheat)
  >- (*Store*)
    cheat
  >- (*Call*)
    Cases_on`o'`
    >-
    (*Tail call*)
    (exists_tac>>
    fs[MAP_ZIP,even_list_def]>>
    qpat_abbrev_tac`ls = GENLIST (λx.2*x) (LENGTH l)`>>
    `ALL_DISTINCT ls` by
      (fs[Abbr`ls`,ALL_DISTINCT_GENLIST]>>
      rw[]>>DECIDE_TAC)>>
    fs[get_vars_perm]>>
    Cases_on`get_vars l st`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    `get_vars ls (set_vars ls x cst) = SOME x` by 
      (match_mp_tac get_vars_set_vars_eq>>
      fs[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP]>>
      metis_tac[get_vars_length_lemma])>>
    fs[set_vars_def]>>
    EVERY_CASE_TAC>>
    fs[call_env_def,dec_clock_def]>>
    ntac 2 (pop_assum mp_tac)>>
    qpat_abbrev_tac`cst'=cst with <|locals:=A;clock:=B|>`>>
    qpat_abbrev_tac`st'=st with <|locals:=A;permute:=B;clock:=C|>`>>
    `cst'=st'` by 
      (unabbrev_all_tac>>fs[word_state_component_equality])>>
    rfs[])
    >>
    (*Non tail call*)
    PairCases_on`x`>>
    Q.PAT_ABBREV_TAC`pp = ssa_cc_trans X Y Z` >>
    PairCases_on`pp` >> simp[] >>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    simp_tac std_ss [ssa_cc_trans_def]>>
    LET_ELIM_TAC>>
    fs[wEval_def,get_vars_perm]>>
    Cases_on`get_vars l st`>>fs[]>>
    Cases_on`find_code o1 x st.code`>>fs[]>>
    Cases_on`x'`>>
    Cases_on`cut_env x1 st.locals`>>fs[]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] 
      mp_tac list_next_var_rename_move_preserve>>
    discharge_hyps>-
      (rw[]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        fs[]>>DECIDE_TAC)
      >-
        (fs[cut_env_def,Abbr`ls`]>>
        metis_tac[SUBSET_DEF,toAList_domain])
      >-
        fs[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        fs[]>>DECIDE_TAC))
    >>
    LET_ELIM_TAC>>fs[]>>
    `ssa_map_ok na' ssa'` by 
      (rpt VAR_EQ_TAC>>
      `na ≤ na+2` by DECIDE_TAC>>
      `is_stack_var (na+2)` by fs[is_alloc_var_flip]>>
      metis_tac[ssa_map_ok_more,list_next_var_rename_move_props])>>
    rfs[]>>
    fs[MAP_ZIP,even_list_def]>>
    `ALL_DISTINCT conv_args` by
      (fs[Abbr`conv_args`,ALL_DISTINCT_GENLIST]>>
      rw[]>>DECIDE_TAC)>>
    (*Establish invariants about ssa_cut to use later*)
    `domain ssa_cut = domain x1` by 
      (fs[EXTENSION,Abbr`ssa_cut`,domain_inter]>>
      rw[EQ_IMP_THM]>>
      fs[cut_env_def,SUBSET_DEF]>>
      res_tac>>
      fs[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (rw[]>>fs[Abbr`ssa_cut`,lookup_inter]>>
      EVERY_CASE_TAC>>fs[])>>
    (*Probably need to case split here to deal with the 2 cases*)
    Cases_on`o0`>>fs[]
    >-
    (*No handler*)
    (qpat_assum`A=pp0` (sym_sub_tac)>>fs[Abbr`prog`]>>
    qpat_assum`A=stack_mov` (sym_sub_tac)>>fs[]>>
    fs[wEval_def,LET_THM,Abbr`move_args`]>>
    `LENGTH conv_args = LENGTH names` by 
      (unabbrev_all_tac >>fs[])>>
    fs[MAP_ZIP]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    fs[Abbr`names`]>>
    `LENGTH l = LENGTH x` by
      metis_tac[get_vars_length_lemma]>>
    `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by 
      (match_mp_tac get_vars_set_vars_eq>>
      fs[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP])>>
    fs[set_vars_def]>>
    qpat_abbrev_tac `rcst' = 
      rcst with locals:= list_insert conv_args x rcst.locals`>>
    (*Important preservation step*)
    `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
      (fs[Abbr`rcst'`,Abbr`conv_args`]>>
      match_mp_tac ssa_locals_rel_ignore_list_insert>>
      fs[EVERY_MEM,MEM_GENLIST]>>
      rw[]>>
      is_phy_var_tac) >> 
    fs[word_state_eq_rel_def]>>
    qabbrev_tac`f = option_lookup ssa'`>>
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`x1`,`st.locals`,`rcst'.locals`,`x'`,`f`] 
      mp_tac cut_env_lemma>>
    discharge_hyps>-
      (rfs[Abbr`f`]>> 
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]>-
        (SPOSE_NOT_THEN assume_tac>>
        `x'' ∈ domain st.locals ∧ y ∈ domain st.locals` by
          fs[SUBSET_DEF,cut_env_def]>>
        fs[domain_lookup,option_lookup_def,ssa_map_ok_def]>>
        res_tac>>
        fs[]>>
        metis_tac[])
      >>
        fs[option_lookup_def,domain_lookup]>>
        res_tac>>
        fs[]>>
        qpat_assum`A=SOME v` SUBST_ALL_TAC>>fs[])
    >>
    rw[Abbr`rcst'`]>>fs[]>>
    IF_CASES_TAC>>fs[call_env_def]>>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    Q.ISPECL_THEN[
      `y:'a word_loc num_map`,`x'`,`st with clock := st.clock-1`,
      `f`,`rcst' with clock := st.clock-1`,`NONE:(num#'a word_prog#num#num)option`,`NONE:(num#'a word_prog#num#num)option`,`λn. rcst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    discharge_hyps>-
      rfs[Abbr`rcst'`]
    >>
    strip_tac>>
    rfs[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x' 
            (NONE:(num # 'a word_prog #num #num)option)
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 (Loc x3 x4::q)`>>
    qpat_abbrev_tac `envy = (push_env y A B) with locals := C`>>
    assume_tac wEval_stack_swap>>
    pop_assum(qspecl_then [`r`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC>-
      (rw[]>>qexists_tac`perm`>>
       fs[dec_clock_def])>>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      fs[push_env_def,word_state_component_equality]>>
      fs[LET_THM,env_to_list_def,dec_clock_def])>>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>
       fs[word_state_component_equality])>>
    FULL_CASE_TAC
    >-
      (strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      discharge_hyps>-
      (unabbrev_all_tac>>
       fs[word_state_component_equality,dec_clock_def])>>
      strip_tac>>fs[]>>
      rfs[]>>
      (*Backwards chaining*)
      fs[Abbr`envy`,Abbr`envx`,word_state_component_equality]>>
      Q.ISPECL_THEN [`(rcst' with clock := st.clock-1)`,
                    `r' with stack := st'`,`y`,`F`]
                    assume_tac push_env_pop_env_s_key_eq>>
      Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                    `r'`,`x'`,`F`]
                    assume_tac push_env_pop_env_s_key_eq>>
      (*This went missing somewhere..*)
      `rcst'.clock = st.clock` by 
        fs[markerTheory.Abbrev_def]>>
      pop_assum SUBST_ALL_TAC>>
      rfs[]>>
      (*Now is a good place to establish the invariant ssa_locals_rel*)
      `ssa_locals_rel na' ssa_cut y'.locals y''.locals ∧ 
       word_state_eq_rel y' y''` by 
      (fs[word_state_component_equality]>>
      `s_key_eq y'.stack y''.stack` by
        metis_tac[s_key_eq_trans,s_key_eq_sym]>>
      assume_tac pop_env_frame>>rfs[word_state_eq_rel_def]>>
      fs[LET_THM,ssa_locals_rel_def]>>
      rw[]
      >-
        (res_tac>>
        qpat_assum`A=domain(fromAList l'')` (sym_sub_tac)>>
        fs[Abbr`f`,option_lookup_def]>>
        qexists_tac`x''`>>fs[]>>
        fs[Abbr`ssa_cut`,domain_inter,lookup_inter]>>
        EVERY_CASE_TAC>>fs[]>>
        metis_tac[domain_lookup])
      >-
        fs[domain_lookup]
      >-
        (`x'' ∈ domain ssa_cut` by metis_tac[domain_lookup]>>
        fs[domain_lookup]>>
        res_tac>>
        `v = f x''` by fs[Abbr`f`,option_lookup_def]>>
        fs[push_env_def,LET_THM,env_to_list_def]>>
        fs[s_key_eq_def,s_val_eq_def]>>
        Cases_on`opt`>>Cases_on`opt'`>>
        fs[s_frame_key_eq_def,s_frame_val_eq_def]>>
        fs[lookup_fromAList]>>
        imp_res_tac key_map_implies>>
        rfs[]>>
        `l'' = ZIP(MAP FST l'',MAP SND l'')` by fs[ZIP_MAP_FST_SND_EQ]>>
        pop_assum SUBST1_TAC>>
        pop_assum (SUBST1_TAC o SYM)>>
        match_mp_tac ALOOKUP_key_remap_2>>
        fs[]>>CONJ_TAC>>
        metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])
      >>
        fs[cut_env_def,SUBSET_DEF]>>
        `x'' ∈ domain st.locals` by fs[domain_lookup]>>
        fs[domain_lookup])>>
     fs[]>>
      (*We set variable 0 but it is never in the 
        locals so the ssa_locals_rel property is preserved*)
      `ssa_locals_rel na' ssa_cut y'.locals 
        (set_var 0 a y'').locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        fs[]>>
        rw[]
        >-
          metis_tac[Abbr`ssa_cut`,ssa_map_ok_inter]
        >> is_phy_var_tac)>> (*The ssa_ok property should come automatic*)
      Q.SPECL_THEN [`y'`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 0 a y'')`] mp_tac 
                   list_next_var_rename_move_preserve>>
      discharge_hyps>-
      (rw[]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        fs[]>>
        qexists_tac`na'`>>fs[]>>
        rfs[])
      >-
        fs[Abbr`ls`,set_toAList_keys]
      >-
        fs[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
      >-
        (`na' ≤ na'+2`by DECIDE_TAC>>
        metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
      >>
        fs[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      fs[Abbr`mov_ret_handler`,wEval_def]>>
      rfs[LET_THM]>>
      `get_vars [0] rcst'' = SOME [a]` by cheat>>
      (*Use the fact that ret_move doesn't overwrite 0*)
      fs[set_vars_def,list_insert_def]>>
      (*Setting up the return values, probably prove together instead of cheating stuff*)
      qabbrev_tac`res_st = (set_var x0 a y')`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      (*Probably isn't that hard but prove in a lemma instead*)
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by 
        cheat>>
      first_x_assum(qspecl_then[`x2`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`] mp_tac)>>
      size_tac>>discharge_hyps>-
      (fs[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
      rfs[]>>
      (*Obvious frame thms*)
      cheat)>>
      rw[]>>
      qspecl_then[`r`,`push_env x' F
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 q`,`perm'`]
      assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with locals := D`>>
      qpat_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def
        ,word_state_component_equality,FUN_EQ_THM])>>
      fs[pop_env_perm,set_var_perm]>>
      EVERY_CASE_TAC>>fs[])
    >-
      (*Excepting without handler*)
      (fs[]>>strip_tac>>
      imp_res_tac s_val_eq_LAST_N_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e'`,`ls'`] assume_tac)>>
      rfs[]>>
      qexists_tac`perm`>>
      `ls'''=ls'` by
        (unabbrev_all_tac>>
        fs[push_env_def,env_to_list_def,LET_THM]>>
        Cases_on`st.handler < LENGTH st.stack`
        >-
          (imp_res_tac bvp_lemmasTheory.LAST_N_TL>>
          rfs[]>>fs[])
        >>
          `st.handler = LENGTH st.stack` by DECIDE_TAC>>
          rpt (qpat_assum `LAST_N A B = C` mp_tac)>-
          simp[LAST_N_LENGTH_cond])>>
      fs[]>>
      metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans])
    >>
      rw[]>>qexists_tac`perm`>>fs[]>>
      TRY(pop_assum(qspec_then`envy.stack` mp_tac)>>
      discharge_hyps>-
      (unabbrev_all_tac>>fs[word_state_component_equality])>>
      rw[]>>fs[]>>NO_TAC))
  >>
    (*Handler reasoning*)
    qpat_assum`A=(pp0,pp1,pp2)` mp_tac>>Cases_on`x''`>>fs[]>>
    LET_ELIM_TAC>>
    rfs[]>>
    qpat_assum`A=pp0` (sym_sub_tac)>>fs[Abbr`prog'`]>>
    qpat_assum`A=stack_mov` (sym_sub_tac)>>fs[]>>
    fs[wEval_def,LET_THM,Abbr`move_args`]>>
    `LENGTH conv_args = LENGTH names` by 
      (unabbrev_all_tac >>fs[])>>
    fs[MAP_ZIP]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    fs[Abbr`names`]>>
    `LENGTH l = LENGTH x` by
      metis_tac[get_vars_length_lemma]>>
    `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by 
      (match_mp_tac get_vars_set_vars_eq>>
      fs[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP])>>
    fs[set_vars_def]>>
    qpat_abbrev_tac `rcst' = 
      rcst with locals:= list_insert conv_args x rcst.locals`>>
    (*Important preservation lemma*)
    `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
      (fs[Abbr`rcst'`,Abbr`conv_args`]>>
      match_mp_tac ssa_locals_rel_ignore_list_insert>>
      fs[EVERY_MEM,MEM_GENLIST]>>
      rw[]>>
      cheat) >> (*should be obvious*)
    fs[word_state_eq_rel_def]>>
    qabbrev_tac`f = option_lookup ssa'`>>
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`x1`,`st.locals`,`rcst'.locals`,`x'`,`f`] 
      mp_tac cut_env_lemma>>
    discharge_hyps>-
      (rfs[Abbr`f`]>> 
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]>-
        (SPOSE_NOT_THEN assume_tac>>
        `x'' ∈ domain st.locals ∧ y ∈ domain st.locals` by
          fs[SUBSET_DEF,cut_env_def]>>
        fs[domain_lookup,option_lookup_def,ssa_map_ok_def]>>
        res_tac>>
        fs[]>>
        metis_tac[])
      >>
        fs[option_lookup_def,domain_lookup]>>
        res_tac>>
        fs[]>>
        qpat_assum`A=SOME v` SUBST_ALL_TAC>>fs[])
    >>
    rw[Abbr`rcst'`]>>fs[]>>
    IF_CASES_TAC>>fs[call_env_def]>>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    assume_tac (GEN_ALL push_env_s_val_eq)>>
    pop_assum (qspecl_then[
      `y`,`x'`,`st with clock := st.clock-1`,
      `f`,`rcst' with clock := st.clock-1`,`T`,`λn. rcst.permute (n+1)`]
      mp_tac)>>
    discharge_hyps>-
      rfs[Abbr`rcst'`]
    >>
    strip_tac>>
    rfs[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x' T
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 q`>>
    qpat_abbrev_tac `envy = (push_env y A B) with locals := C`>>
    assume_tac wEval_stack_swap>>
    pop_assum(qspecl_then [`r`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC>-
      (rw[]>>qexists_tac`perm`>>
       fs[dec_clock_def])>>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      fs[push_env_def,word_state_component_equality]>>
      fs[LET_THM,env_to_list_def,dec_clock_def])>>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>
       fs[word_state_component_equality])>>
    FULL_CASE_TAC
    >-
      (*
      Going to be basically the same as above except with an
      extra bit at the end for the consistency fixing

      strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      discharge_hyps>-
      (unabbrev_all_tac>>
       fs[word_state_component_equality,dec_clock_def])>>
      strip_tac>>fs[]>>
      rfs[]>>
      (*Backwards chaining*)
      fs[Abbr`envy`,Abbr`envx`,word_state_component_equality]>>
      Q.ISPECL_THEN [`(rcst' with clock := st.clock-1)`,
                    `r'' with stack := st'`,`y`,`T`]
                    assume_tac push_env_pop_env_s_key_eq>>
      Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                    `r''`,`x'`,`T`]
                    assume_tac push_env_pop_env_s_key_eq>>
      (*This went missing somewhere..*)
      `rcst'.clock = st.clock` by cheat>>
      pop_assum SUBST_ALL_TAC>>
      rfs[]>>
      `domain y''.locals = domain y` by cheat>>
      fs[]>>
      `ssa_locals_rel na' ssa_cut y'.locals y''.locals ∧ 
       word_state_eq_rel y' y''` by 
       cheat>>
      fs[]>>
      (*We set variable 0 but it is never in the 
        locals so the ssa_locals_rel property is preserved*)
      `ssa_locals_rel na' ssa_cut y'.locals 
        (set_var 0 a y'').locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        fs[]>>cheat)>> (*The ssa_ok property should come automatic*)
      Q.SPECL_THEN [`y'`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 0 a y'')`] mp_tac 
                   list_next_var_rename_move_preserve>>
      discharge_hyps>-
      (rw[]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        fs[]>>
        HINT_EXISTS_TAC>>fs[])
      >-
        cheat (*should need to prove this in the previous part*)
      >-
        fs[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
      >-
        cheat (*because it is ok on na'*)
      >>
        fs[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      (*
      fsAbbr`cons_ret_handler`,Abbr`cons_ret_handler`,wEval_def]>>
      rfs[LET_THM]>>
      `get_vars [0] rcst'' = SOME [a]` by cheat>>
      fs[set_vars_def,list_insert_def]>>
      (*Setting up the return values, probably prove together instead of cheating stuff*)
      qabbrev_tac`res_st = (set_var x0 a y')`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by cheat>>
      first_x_assum(qspecl_then[`x2`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`] mp_tac)>>
      size_tac>>discharge_hyps>-
      (fs[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
      cheat)>>
      rw[]>>
      qspecl_then[`r`,`push_env x' F
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 q`,`perm'`]
      assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with locals := D`>>
      qpat_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def
        ,word_state_component_equality,FUN_EQ_THM])>>
      fs[pop_env_perm,set_var_perm]>>
      EVERY_CASE_TAC>>fs[])*) *)
      cheat
    >-
      (*Excepting with handler*)
      (fs[]>>strip_tac>>
      imp_res_tac s_val_eq_LAST_N_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e'`,`ls'`] assume_tac)>>
      rfs[]>>
      unabbrev_all_tac>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      rpt (qpat_assum `LAST_N A B = C` mp_tac)>>
      simp[LAST_N_LENGTH_cond]>>
      rpt strip_tac>>
      fs[domain_fromAList]>>
      imp_res_tac list_rearrange_keys>>
      `set (MAP FST lss') = domain y` by
        (qpat_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
        fs[EXTENSION]>>rw[EXISTS_PROD]>>
        simp[MEM_MAP,QSORT_MEM]>>rw[EQ_IMP_THM]
        >-
          (Cases_on`y'`>>
          fs[MEM_toAList]>>
          imp_res_tac domain_lookup>>
          metis_tac[])
        >>
          fs[EXISTS_PROD,MEM_toAList]>>
          metis_tac[domain_lookup])>>
      `domain x' = set (MAP FST lss)` by
        (qpat_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
          fs[EXTENSION,MEM_MAP,QSORT_MEM,MEM_toAList
            ,EXISTS_PROD,domain_lookup])>>
      fs[word_state_eq_rel_def]>>
      rfs[]>>
      fs[domain_fromAList]>>
      qabbrev_tac`ssa_cut = inter ssa' x1`>>
      qpat_abbrev_tac`cres=r'' with <|locals:= A;stack := B;handler:=C|>`>>
      `ssa_locals_rel na' ssa_cut r''.locals cres.locals ∧ 
       word_state_eq_rel r'' cres` by
      (fs[word_state_eq_rel_def,Abbr`cres`]>>
      fs[LET_THM,ssa_locals_rel_def]>>
      rw[Abbr`ssa_cut`]
      >-
        (fs[domain_fromAList,option_lookup_def,lookup_inter]>>
        EVERY_CASE_TAC>>fs[]>>
        qexists_tac`x''`>>fs[]>>
        metis_tac[EXTENSION,domain_lookup])
      >-
        (`MEM x'' (MAP FST lss)` by cheat>>
        metis_tac[EXTENSION])
      >-
        (`MEM x'' (MAP FST lss)` by cheat>>
        cheat)
      >-
        (`MEM x'' (MAP FST lss)` by cheat>>
        fs[EXTENSION,every_var_def]>>res_tac>>
        `na ≤ na'` by cheat>>
        `x'' < na` by metis_tac[]>>
        DECIDE_TAC)
      >>
        metis_tac[s_key_eq_trans,s_val_and_key_eq])>>
      `ssa_locals_rel na' ssa_cut r''.locals 
        (set_var 0 w cres).locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        fs[]>>rw[]
        >-
          metis_tac[Abbr`ssa_cut`,ssa_map_ok_inter]
        >> is_phy_var_tac)>> 
      Q.SPECL_THEN [`r''`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 0 w cres)`] mp_tac 
                   list_next_var_rename_move_preserve>>
      discharge_hyps>-
      (rw[]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        fs[]>>
        qexists_tac`na'`>>fs[]>>
        rfs[])
      >-
        fs[domain_fromAList,set_toAList_keys]
      >-
        fs[ALL_DISTINCT_MAP_FST_toAList]
      >-
        (`na' ≤ na'+2`by DECIDE_TAC>>
        metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
      >>
        fs[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      rfs[LET_THM,wEval_def]>>
      `get_vars [0] rcst' = SOME [w]` by cheat>>
      (*Use the fact that ret_move doesn't overwrite 0*)
      fs[set_vars_def,list_insert_def]>>
      qabbrev_tac`res_st = (set_var q' w r'')`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_3_p ssa_3_p res_st.locals res_rcst.locals` by 
        cheat>>
      first_x_assum(qspecl_then[`r'`,`res_st`,`res_rcst`,`ssa_3_p`,`na_3_p`] mp_tac)>>
      size_tac>>discharge_hyps>-
      (fs[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
      rfs[]>>
      (*Obvious frame thms*)
      cheat)>>
      rw[]>>
      qspecl_then[`r`,`push_env x' T
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 q`,`perm'`]
      assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      fs[push_env_def,env_to_list_def,LET_THM]>>
      rfs[]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = st with <|locals:=A;stack:=B;permute:=C;handler:=D;clock:=E|>`>>
      qpat_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = st with <|locals:=A;stack:=B;permute:=C;handler:=D;clock:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def
        ,word_state_component_equality,FUN_EQ_THM])>>
      fs[pop_env_perm,set_var_perm]>>
      fs[domain_fromAList]>>
      Cases_on`wEval (r',res_st with permute:=perm')`>>Cases_on`q''`>>
      Cases_on`wEval(ren_exc_handler,res_rcst)`>>Cases_on`q''`>>
      fs[]>>
      (*Fix inconsistencies*)
      cheat)
    >>
      cheat)
  >- (*Seq*)
    (rw[]>>fs[wEval_def,ssa_cc_trans_def,LET_THM]>>
    last_assum(qspecl_then[`w`,`st`,`cst`,`ssa`,`na`] mp_tac)>>
    size_tac>>
    discharge_hyps>>fs[every_var_def]>>rw[]>>
    Cases_on`ssa_cc_trans w ssa na`>>Cases_on`r`>>fs[]>>
    Cases_on`ssa_cc_trans w0 q' r'`>>Cases_on`r`>>fs[]>>
    fs[wEval_def,LET_THM]>>
    Cases_on`wEval(w,st with permute:=perm')`>>fs[]
    >- (qexists_tac`perm'`>>fs[]) >>
    Cases_on`wEval(q,cst)`>>fs[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>rw[]>>fs[])
    >>
    fs[]>>
    first_assum(qspecl_then[`w0`,`r`,`r'''`,`q'`,`r'`] mp_tac)>>
    size_tac>>
    discharge_hyps>-
      (rfs[]>>imp_res_tac ssa_cc_trans_props>>
      fs[]>>
      match_mp_tac every_var_mono>>
      HINT_EXISTS_TAC>>
      fs[]>>DECIDE_TAC)>>
    rw[]>>
    qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[])
  >- (*If*)
   (qpat_abbrev_tac `A = ssa_cc_trans B C D` >>
    PairCases_on`A`>>simp[]>>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    fs[wEval_def,ssa_cc_trans_def]>>
    LET_ELIM_TAC>>fs[get_var_perm,get_var_imm_perm]>>
    qpat_assum`B = A0` sym_sub_tac>>fs[wEval_def]>>
    Cases_on`get_var n st`>>fs[]>>
    Cases_on`x`>>fs[]>>
    Cases_on`get_var_imm r st`>>fs[]>>
    Cases_on`x`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_var>>fs[Abbr`r1'`]>>
    `get_var_imm ri' cst = SOME(Word c'')` by 
      (Cases_on`r`>>fs[Abbr`ri'`,get_var_imm_def]>>
      metis_tac[ssa_locals_rel_get_var])>>
    Cases_on`word_cmp c c' c''`>>fs[]
    >-
      (first_assum(qspecl_then[`w`,`st`,`cst`,`ssa`,`na`] mp_tac)>>
      size_tac>>
      discharge_hyps>-
        (rfs[]>>imp_res_tac ssa_cc_trans_props>>
        fs[every_var_def])
      >>
      rw[]>>
      qexists_tac`perm'`>>fs[LET_THM]>>
      Cases_on`wEval(w,st with permute := perm')`>>
      Cases_on`wEval(e2',cst)`>>fs[]>>
      Cases_on`q'`>>fs[]>>rfs[]>>
      (*Start reasoning about fix_inconsistencies*)
      fs[fix_inconsistencies_def]>>
      qpat_assum`A=(B,C,D,E)` mp_tac>>LET_ELIM_TAC>>
      fs[]>>
      imp_res_tac ssa_cc_trans_props>>
      Q.SPECL_THEN [`var_union`,`na3`,`ssa2`,`ssa3`,`r'`,`r''`,`1`] mp_tac 
        merge_moves_correctL>>
      fs[]>>
      discharge_hyps_keep>- 
        (fs[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]>>
        metis_tac[ssa_map_ok_more])>>
      LET_ELIM_TAC>>
      ntac 3 (pop_assum mp_tac)>>discharge_hyps
      >-
        metis_tac[ssa_map_ok_more,ssa_locals_rel_more]
      >>
      rw[]>>simp[Once wEval_def]>>
      Q.SPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`r'`,`rcstL`]mp_tac 
        fake_moves_correctL>>
      discharge_hyps>- 
      (Q.ISPECL_THEN [`var_union`,`na3`,`ssa2`,`ssa3`] assume_tac merge_moves_frame>>rfs[LET_THM])>>
      LET_ELIM_TAC>>
      ntac 3 (pop_assum mp_tac)>>discharge_hyps
      >-
        metis_tac[ssa_map_ok_more,ssa_locals_rel_more]>>
      rw[]>>fs[word_state_eq_rel_def]>>rfs[])
    >>
      (first_assum(qspecl_then[`w0`,`st`,`cst`,`ssa`,`na2`] mp_tac)>>
      size_tac>>
      discharge_hyps>-
        (rfs[]>>imp_res_tac ssa_cc_trans_props>>rw[]
        >-
          metis_tac[ssa_locals_rel_more]
        >-
          (fs[every_var_def]>>match_mp_tac every_var_mono>>
          Q.EXISTS_TAC`λx.x<na`>>fs[] >>
          DECIDE_TAC)
        >>
          metis_tac[ssa_map_ok_more])
      >>
      rw[]>>
      qexists_tac`perm'`>>fs[LET_THM]>>
      Cases_on`wEval(w0,st with permute := perm')`>>
      Cases_on`wEval(e3',cst)`>>fs[]>>
      Cases_on`q'`>>fs[]>>rfs[]>>
      (*Start reasoning about fix_inconsistencies*)
      fs[fix_inconsistencies_def]>>
      qpat_assum`A=(B,C,D,E)` mp_tac>>LET_ELIM_TAC>>
      fs[]>>
      Q.SPECL_THEN [`var_union`,`na3`,`ssa2`,`ssa3`,`r'`,`r''`,`1`] mp_tac 
        merge_moves_correctR>>
      imp_res_tac ssa_cc_trans_props>>
      fs[]>>
      discharge_hyps_keep>- 
        (fs[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]>>
        metis_tac[ssa_map_ok_more])>>
      LET_ELIM_TAC>>
      rw[]>>simp[Once wEval_def]>>
      Q.SPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`r'`,`rcstR`]mp_tac 
        fake_moves_correctR>>
      discharge_hyps>- 
      (Q.ISPECL_THEN [`var_union`,`na3`,`ssa2`,`ssa3`] assume_tac merge_moves_frame>>rfs[LET_THM])>>
      LET_ELIM_TAC>>
      ntac 3 (pop_assum mp_tac)>>discharge_hyps
      >-
        metis_tac[ssa_map_ok_more,ssa_locals_rel_more]>>
      rw[]>>
      rfs[]>>
      fs[word_state_eq_rel_def]>>
      Q.ISPECL_THEN[`var_union`,`na3`,`ssa2`,`ssa3`] assume_tac 
        merge_moves_frame2>>
      Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
        fake_moves_frame2>>
      Q.ISPECL_THEN[`var_union`,`na3`,`ssa2`,`ssa3`] assume_tac 
        merge_moves_frame3>>
      Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
        fake_moves_frame3>>
      rfs[LET_THM]>>
      match_mp_tac (GEN_ALL ssa_eq_rel_swap)>>
      HINT_EXISTS_TAC>>rfs[]>>
      fs[Abbr`var_union`,EXTENSION]>>CONJ_ASM1_TAC>-
        (fs[toAList_domain,domain_union]>>
        metis_tac[])
      >>
      fs[toAList_domain]>>rw[]>>
      reverse(Cases_on`x ∈ domain (union ssa2 ssa3)`)>-
        (fs[domain_union]>>
        metis_tac[lookup_NONE_domain])
      >>
      fs[domain_inter]>>
      metis_tac[]))
  >- (*Alloc*)
    (fs[ssa_cc_trans_def,wEval_def,get_var_perm,LET_THM]>>
    Cases_on`get_var n st`>>
    rw[]>>
    Cases_on`x`>>fs[wAlloc_def]>>
    Cases_on`cut_env s st.locals`>>fs[]>>
    qpat_abbrev_tac`ls = MAP FST (toAList s)`>>
    Cases_on`list_next_var_rename_move ssa (na+2) ls`>>Cases_on`r`>>
    Cases_on`list_next_var_rename_move (inter q' s) (r'+2) ls`>>Cases_on`r`>>
    fs[wEval_def]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    (*Probably useful?*)
    discharge_hyps_keep>-
      (rw[]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        fs[]>>DECIDE_TAC)
      >-
        (fs[cut_env_def,Abbr`ls`]>>
        metis_tac[SUBSET_DEF,toAList_domain])
      >-
        fs[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        fs[]>>DECIDE_TAC))>>
    LET_ELIM_TAC>>fs[]>>
    `ssa_map_ok na' ssa'` by cheat >> 
    (*separately provable*)
    imp_res_tac ssa_locals_rel_get_var>>fs[]>>
    rfs[wAlloc_def]>>
    qabbrev_tac`f = option_lookup q'`>>
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`s`,`st.locals`,`rcst.locals`,`x`
                  ,`f` ] mp_tac cut_env_lemma>>
    discharge_hyps>-
      (rfs[Abbr`f`]>> 
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]>-
        (SPOSE_NOT_THEN assume_tac>>
        `x' ∈ domain st.locals ∧ y ∈ domain st.locals` by
          fs[SUBSET_DEF,cut_env_def]>>
        fs[domain_lookup,option_lookup_def,ssa_map_ok_def]>>
        res_tac>>
        fs[]>>
        metis_tac[])
      >>
        fs[option_lookup_def,domain_lookup]>>
        res_tac>>
        fs[]>>
        qpat_assum`A=SOME v'` SUBST_ALL_TAC>>fs[])
    >>
    rw[]>>fs[set_store_def]>>
    Q.ISPECL_THEN [`y`,`x`,`st with store:= st.store |+ (AllocSize,Word c)`
    ,`f`,`rcst with store:= rcst.store |+ (AllocSize,Word c)`
    ,`NONE:(num#'a word_prog #num # num)option`,`NONE:(num#'a word_prog #num # num)option`,`rcst.permute`] assume_tac (GEN_ALL push_env_s_val_eq)>>
    rfs[word_state_eq_rel_def]>>
    qexists_tac`perm`>>fs[]>>
    qpat_abbrev_tac `st' = push_env x NONE A`>>
    qpat_abbrev_tac `cst' = push_env y NONE B`>>
    Cases_on`wGC st'`>>fs[]>>
    qspecl_then [`st'`,`cst'`,`x'`] mp_tac wGC_s_val_eq_gen>>
    discharge_hyps_keep>-
      (unabbrev_all_tac>>
      fs[push_env_def,LET_THM,env_to_list_def,word_state_eq_rel_def]>>
      rfs[])
    >>
    rw[]>>simp[]>>
    unabbrev_all_tac>>
    imp_res_tac wGC_frame>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    Cases_on`pop_env x'`>>fs[]>>
    `ssa_locals_rel na' (inter q' s) x''.locals y'.locals ∧
     word_state_eq_rel x'' y'` by
      (imp_res_tac wGC_s_key_eq>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      pop_assum mp_tac>>simp[Once s_key_eq_sym]>>
      strip_tac>>
      rpt (qpat_assum `s_key_eq A B` mp_tac)>>
      qpat_abbrev_tac `lsA = list_rearrange (rcst.permute 0)
        (QSORT key_val_compare ( (toAList y)))`>>
      qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (QSORT key_val_compare ( (toAList x)))`>>
      ntac 4 strip_tac>>
      Q.ISPECL_THEN [`x'.stack`,`y'`,`t'`,`NONE:(num#num#num) option`
        ,`lsA`,`rcst.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      discharge_hyps
      >-
        (fs[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      Q.ISPECL_THEN [`t'.stack`,`x''`,`x'`,`NONE:(num#num#num) option`
        ,`lsB`,`st.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      discharge_hyps
      >-
        (fs[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      rw[]
      >-
        (
        qabbrev_tac`f=option_lookup q'`>>
        simp[]>>
        fs[ssa_locals_rel_def,lookup_fromAList]>>
        `MAP SND ls'' = MAP SND ls'` by
          fs[s_val_eq_def,s_frame_val_eq_def]>>
        rw[]>>
        `MAP FST (MAP (λ(x,y). (f x,y)) lsB) =
         MAP f (MAP FST lsB)` by
          fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
        fs[Abbr`f`]>>
        `LENGTH lsB = LENGTH ls'` by cheat
        >-
          (fs[domain_fromAList,MAP_ZIP,LENGTH_MAP]>>
          cheat) (*x''' is in x*)
        >-
          (`MEM x''' (MAP FST lsB)` by cheat>>
          unabbrev_all_tac>>
          `MEM x''' (MAP FST (toAList x))` by cheat>>
          fs[domain_inter]>>cheat)
        >-
          (*need to use previous conjunct
          match_mp_tac ALOOKUP_key_remap_2>>rw[]>>
          metis_tac[s_key_eq_def,s_frame_key_eq_def,LENGTH_MAP]*)
          cheat
        >>
          (*x''' in x, and dom x = dom s and every_var < na*)
          cheat
          )
        >>
        fs[word_state_eq_rel_def,pop_env_def]>>
        rfs[word_state_component_equality]>>
        metis_tac[s_val_and_key_eq,s_key_eq_sym
          ,s_val_eq_sym,s_key_eq_trans])
      >>
      fs[word_state_eq_rel_def]>>FULL_CASE_TAC>>fs[has_space_def]>>
      Cases_on`x'''`>>
      EVERY_CASE_TAC>>fs[call_env_def]>>
      Q.SPECL_THEN [`x''`,`inter q' s`,`na'+2`,`(MAP FST (toAList s))`
                   ,`y'`] mp_tac list_next_var_rename_move_preserve>>
      discharge_hyps>-
      (rw[]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        fs[]>>
        qpat_assum `A = fromAList l` sym_sub_tac>>
        HINT_EXISTS_TAC>>fs[])
      >-
        cheat (*should need to prove this in the previous part*)
      >-
        cheat (*because q' is ok on na'*)
      >>
        fs[word_state_eq_rel_def])>>
      rw[]>>fs[LET_THM]>>
      Cases_on`wEval (q'',y')`>>fs[word_state_eq_rel_def])
  >-
    (*Raise*)
    (exists_tac>>fs[get_var_perm]>>
    Cases_on`get_var n st`>>imp_res_tac ssa_locals_rel_get_var>>
    fs[get_vars_def,get_var_def,set_vars_def,lookup_list_insert]>>
    fs[jump_exc_def]>>EVERY_CASE_TAC>>fs[])
  >-
    (*Return*)
    (exists_tac>>fs[get_var_perm]>>
    Cases_on`get_var n st`>>
    Cases_on`get_var n0 st`>>
    imp_res_tac ssa_locals_rel_get_var>>
    fs[get_vars_def,set_vars_def]>>
    imp_res_tac ssa_locals_rel_ignore_list_insert>>
    ntac 4 (pop_assum kall_tac)>>
    pop_assum(qspecl_then [`[x']`,`[2]`] mp_tac)>>
    discharge_hyps>-fs[]>>
    discharge_hyps>- is_phy_var_tac>>
    rw[]>>fs[list_insert_def]>>
    assume_tac (GEN_ALL ssa_locals_rel_get_var)>>
    qpat_abbrev_tac`rcst=cst with locals:=A`>>
    first_assum(qspecl_then[`x`,`st`,`ssa`,`na`,`n`,`rcst`] assume_tac)>>
    first_x_assum(qspecl_then[`x'`,`st`,`ssa`,`na`,`n0`,`rcst`] assume_tac)>>
    unabbrev_all_tac>>rfs[]>>
    fs[get_var_def,call_env_def])
  >-
    (exists_tac>>
    EVERY_CASE_TAC>>fs[call_env_def,dec_clock_def])
  >> cheat)

val get_vars_eq = prove(
  ``(set ls) SUBSET domain st.locals ==> ?y. get_vars ls st = SOME y /\
                                             y = MAP (\x. THE (lookup x st.locals)) ls``,
  Induct_on`ls`>>fs[get_vars_def,get_var_def]>>rw[]>>
  fs[domain_lookup])

(*The initial move, ssa and limit vars*)
val setup_ssa_def = Define`
  setup_ssa n lim (prog:'a word_prog) = 
  let args = even_list n in 
    list_next_var_rename_move LN lim (even_list n)`

(*For starting up*)
val setup_ssa_props = prove(``
  is_alloc_var lim ∧ 
  domain st.locals = set (even_list n) ⇒ 
  let (mov:'a word_prog,ssa,na) = setup_ssa n lim (prog:'a word_prog) in
  let (res,cst) = wEval(mov,st) in
    res = NONE ∧
    word_state_eq_rel st cst ∧
    ssa_map_ok na ssa ∧ 
    ssa_locals_rel na ssa st.locals cst.locals ∧ 
    is_alloc_var na ∧ 
    lim ≤ na``,
  rw[setup_ssa_def,list_next_var_rename_move_def]>>
  fs[word_state_eq_rel_def,wEval_def]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  fs[LET_THM,MAP_ZIP,LENGTH_COUNT_LIST]>>
  fs[ALL_DISTINCT_MAP]>>
  `set args ⊆ domain st.locals` by fs[]>>
  imp_res_tac get_vars_eq>>
  `MAP (option_lookup LN) args = args` by 
    fs[MAP_EQ_ID,option_lookup_def,lookup_def]>>
  fs[set_vars_def,word_state_component_equality]
  >>
    TRY(`ssa_map_ok lim LN` by 
      fs[ssa_map_ok_def,lookup_def]>>
    imp_res_tac list_next_var_rename_props>>NO_TAC)
  >>
    (fs[ssa_locals_rel_def]>>
    `ALL_DISTINCT args` by
      (unabbrev_all_tac>>
      fs[even_list_def,ALL_DISTINCT_GENLIST]>>rw[]>>
      DECIDE_TAC)>>
    imp_res_tac list_next_var_rename_lemma_2>>
    pop_assum kall_tac>>
    pop_assum(qspecl_then [`LN`,`lim`] mp_tac)>>
    LET_ELIM_TAC>>fs[]>>rfs[]
    >-
      (qpat_assum`A=cst.locals` (sym_sub_tac)>>
      fs[domain_list_insert,LENGTH_COUNT_LIST]>>
      `x ∈ domain ssa` by fs[domain_lookup]>>
      qpat_assum `MAP f args = B` (sym_sub_tac)>>
      DISJ2_TAC>>
      fs[MEM_MAP]>>
      qexists_tac`x`>>
      `x ∈ domain ssa` by fs[domain_lookup]>>
      fs[]>>metis_tac[EXTENSION])
    >-
      (`x ∈ domain st.locals` by fs[domain_lookup]>>
      metis_tac[EXTENSION])
    >-
      (qpat_assum`A=cst.locals` (sym_sub_tac)>>
      fs[lookup_list_insert,LENGTH_COUNT_LIST]>>
      fs[ALOOKUP_ALL_DISTINCT_EL]>>
      cheat)
    >>
      `x ∈ domain st.locals` by fs[domain_lookup]>>
      `MEM x args` by metis_tac[EXTENSION]>>
      fs[Abbr`args`]>>
      fs[even_list_def,MEM_GENLIST]>>
      `is_phy_var x` by is_phy_var_tac>>
      metis_tac[convention_partitions]))

(*dummy def*)
val limit_var_def = Define`
  limit_var prog = 3:num`

(*dummy property*)
val limit_var_props = prove(``
  limit_var prog = lim ⇒ 
  is_alloc_var lim ∧
  every_var (λx. x< lim) prog``, cheat)
   
val full_ssa_cc_trans_def = Define`
  full_ssa_cc_trans n prog =
    let lim = limit_var prog in
    let (mov,ssa,na) = setup_ssa n lim prog in
    let (prog',ssa',na') = ssa_cc_trans prog ssa na in
      Seq mov prog'`

(*Full correctness theorem*)
val _ = prove(``
  ∀prog st n.
  domain st.locals = set (even_list n) ⇒ 
  ∃perm'.
  let (res,rst) = wEval(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (res',rcst) = wEval(full_ssa_cc_trans n prog,st) in
    res = res' ∧
    word_state_eq_rel rst rcst``,
  rw[]>>
  qpat_abbrev_tac`sprog = full_ssa_cc_trans n prog`>>
  fs[full_ssa_cc_trans_def]>>
  pop_assum mp_tac>>LET_ELIM_TAC>>
  assume_tac limit_var_props>>
  pop_assum mp_tac>> discharge_hyps>- metis_tac[]>>
  rw[]>>
  imp_res_tac setup_ssa_props>>
  pop_assum(qspec_then`prog` mp_tac)>>
  LET_ELIM_TAC>>
  simp[Abbr`sprog`,Once wEval_def]>>
  rfs[]>>
  Q.ISPECL_THEN [`prog`,`st`,`cst`,`ssa`,`na`] mp_tac ssa_cc_trans_correct>>
  discharge_hyps>-
    (fs[]>>match_mp_tac every_var_mono>>HINT_EXISTS_TAC >>
    rw[]>>DECIDE_TAC)>>
  rw[]>>
  qexists_tac`perm'`>>rw[]>>
  fs[LET_THM])

 
val _ = export_theory();
