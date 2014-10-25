open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open word_langTheory
open alistTheory
open BasicProvers

val _ = new_theory "word_live";

(*Define a liveness analysis algorithm*)

(*This is the version to use for proofs*)

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees
*)
val get_live_inst_def = Define`
  (get_live_inst Skip live:num_set = live) ∧
  (*R:=W*) 
  (get_live_inst (Const reg w) live = delete reg live) ∧
  (*r1 := op r2,ri*)
  (get_live_inst (Arith (Binop bop r1 r2 ri)) live =
    case ri of Reg r3 => insert r2 () (insert r3 () (delete r1 live))
    | _ => insert r2 () (delete r1 live)) ∧
  (*r1 := shift r2 n*) 
  (get_live_inst (Arith (Shift shift r1 r2 n)) live =
    insert r2 () (delete r1 live)) ∧ 
  (*similar*)
  (get_live_inst (Mem Load r (Addr a w)) live =
    insert a () (delete r live)) ∧
  (*reads both a and r*)
  (get_live_inst (Mem Store r (Addr a w)) live =
    insert a () (insert r () live)) ∧ 
  (*Catchall -- for future instructions to be added*) 
  (get_live_inst x live = live)` 

(*Fully general expressions is not needed but is 
not too difficult to define
Note that it never writes to a register so we dont need a live-after set*)
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

(*This defines the top level live sets*)
val get_live_def = Define`
  (get_live Skip live = live) ∧ 
  (*All 2nds are read and all 1sts are written*)
  (get_live (Move ls) live =
    let killed = FOLDR delete live (MAP FST ls) in
      FOLDR (\x y. insert x () y) killed (MAP SND ls)) ∧ 
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
  (get_live (If e1 num e2 e3) live =
    let e2_live = get_live e2 live in 
    let e3_live = get_live e3 live in
      get_live e1 (insert num () (union e2_live e3_live))) ∧
  (*With cut-sets, the cut-set itself must always be live
    I think we can probably discard the input live set
    NOTE: Actually, live should probably always be exactly
          equivalent to the cut-set
  *)
  (get_live (Alloc num numset) live = insert num () numset) ∧ 
  (get_live (Raise num) live = insert num () live) ∧
  (get_live (Return num) live = insert num () live) ∧
  (get_live Tick live = live) ∧
  (get_live (Set n exp) live = union (get_live_exp exp) live) ∧
  (*Cut-set must be live, args input must be live
    For tail calls, there shouldn't be a liveset since control flow will
    never return into the same instance
    Otherwise, both args + cutsets live
    TODO: Suspiciously simple...
  *) 
  (get_live (Call ret dest args h) live =
    let args_set = FOLDR (\x y. insert x () y) LN args in
      case ret of NONE => args_set
                | SOME (_,cutset,_) => union cutset args_set)`
 
(*Coloring respects live sets
  NOTE: This differs significantly from David's definition
*)
val coloring_ok_def = Define`
  (coloring_ok f (Seq s1 s2) live =
    (*Expand get_live*)
    let s2_live = get_live s2 live in
      INJ f (domain s2_live) UNIV ∧ 
      coloring_ok f s2 live ∧ coloring_ok f s1 s2_live) ∧ 
  (coloring_ok f (If e1 num e2 e3) live =
    let e2_live = get_live e2 live in 
    let e3_live = get_live e3 live in
    (*All of them must be live at once*)
    let merged = insert num () (union e2_live e3_live) in 
      INJ f (domain merged) UNIV ∧ 
      coloring_ok f e2 live ∧ coloring_ok f e3 live ∧ 
      coloring_ok f e1 merged) ∧ 
  (*Only care about returning case where there is a returning handler 
    and (maybe) exception handlers*)
  (coloring_ok f (Call (SOME (v,cutset,ret_handler)) dest args h) live =
    (*top level*)
    (INJ f (domain cutset) UNIV ∧ 
    (*returning handler*)
    (*not sure what to write for the return value yet..
      it probably needs to be colored differently from everything
      else in the liveset before returning handler because 
      it might end up overwriting something otherwise 
      EVEN IF it is not used
      this may not be the nicest way to state it though..*)
    INJ f (domain(insert v () (get_live ret_handler live))) UNIV ∧ 
    coloring_ok f ret_handler live ∧
    (*exception handler*)
    (case h of 
    | NONE => T
    | SOME(v,prog) =>
        INJ f (domain(insert v () (get_live prog live))) UNIV ∧ 
        coloring_ok f prog live))) ∧ 
  (*Catchall for cases where we dont have in sub programs live sets*)
  (coloring_ok f prog live = 
    (INJ f (domain live) UNIV ∧ 
    INJ f (domain (get_live prog live)) UNIV))`


(*Slightly smarter version of get_live that returns a tuple 
  (hdlive,livesets) where hdlive is the liveset in front of 
  that instruction and livesets is everything induced inside
*)
val get_live_sets_def = Define`
  (get_live_sets (Seq s1 s2) live =
    let (hd,ls) = get_live_sets s2 live in
    let (hd',ls') = get_live_sets s1 hd in
      (hd',(ls ++ (hd::ls')))) ∧ 
  (get_live_sets (If e1 num e2 e3) live =
    let (h2,ls2) = get_live_sets e2 live in 
    let (h3,ls3) = get_live_sets e3 live in
    let merged = insert num () (union h2 h3) in 
    let (h,ls1) = get_live_sets e1 merged in
      (h,ls1++(merged:: (ls2++ls3)))) ∧    
  (get_live_sets (Call (SOME (v,cutset,ret_handler)) dest args h) live =
    (*top level*)
    let args_set = FOLDR (\x y. insert x () y) LN args in
    let (hd,ls) = get_live_sets ret_handler live in
    let ls = (insert v () hd) :: ls in 
    (case h of 
    | NONE => (union cutset args_set,ls)
    | SOME(v,prog) =>
        let (hd',ls') = get_live_sets prog live in
        let ls' = (insert v () hd') :: ls' in 
        (union cutset args_set,ls++ls'))) ∧ 
  (*Catchall for cases where we dont have in sub programs live sets*)
  (get_live_sets prog live = (get_live prog live,[live]))`

val merge_pair_def = Define`
  merge_pair = \x,y. x::y`

(*
EVAL ``MAP toAList (merge_pair (get_live_sets
  (Seq (Move [1,2;3,4;5,6]) 
  (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE))
  (insert 100 () LN)))``

*)

(*Alternative to coloring_ok for get_live_sets*)
val coloring_ok_alt_def = Define`
  coloring_ok_alt f prog live =
    EVERY (λs. INJ f (domain s) UNIV) 
    (merge_pair (get_live_sets prog live))`

val _= export_rewrites["merge_pair_def"];

val get_live_sets_thm = prove(
``!prog live hd ls.
  get_live_sets prog live = (hd,ls) ⇒ 
  get_live prog live = hd``,
  Induct>>rw[get_live_sets_def]>>fs[LET_THM]
  >-
    (Cases_on`o'`>>fs[get_live_sets_def]>>
    PairCases_on`x`>>fs[get_live_sets_def,get_live_def]>>
    fs[LET_THM,UNCURRY]>>
    EVERY_CASE_TAC>>fs[])
  >-
    (Cases_on`get_live_sets prog' live`>>fs[]>>
    Cases_on`get_live_sets prog q`>>fs[]>>
    metis_tac[get_live_def])
  >>
    Cases_on`get_live_sets prog'' live`>>
    Cases_on`get_live_sets prog' live`>>
    Cases_on`get_live_sets prog (insert n () (union q' q))`>>fs[]>>
    fs[get_live_def,LET_THM]>>metis_tac[])

val INJ_UNION = prove(
``!f A B.
  INJ f (A ∪ B) UNIV ⇒ 
  INJ f A UNIV ∧ 
  INJ f B UNIV``,
  rw[]>>
  metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_UNION])

(*Cant find this anywhere...*)
val SUBSET_OF_INSERT = store_thm("SUBSET_OF_INSERT",
``!s x. s ⊆ x INSERT s``,
  rw[SUBSET_DEF])

val coloring_ok_alt_thm = prove(
``!f prog live.
  coloring_ok_alt f prog live ⇒ 
  coloring_ok f prog live``,
  ho_match_mp_tac (fetch "-" "coloring_ok_ind")>>
  rw[]>>
  fs[get_live_sets_def,coloring_ok_alt_def,coloring_ok_def]
  >- 
    (fs[LET_THM]>>
    Cases_on`get_live_sets prog' live`>>
    Cases_on`get_live_sets prog q`>>fs[]>>
    imp_res_tac get_live_sets_thm>>fs[])
  >- 
    (fs[LET_THM]>>
    Cases_on`get_live_sets prog' live`>>
    Cases_on`get_live_sets prog'' live`>>
    Cases_on`get_live_sets prog (insert num () (union q q'))`>>fs[]>>
    imp_res_tac get_live_sets_thm>>fs[]>>
    fs[domain_insert,domain_union]>>
    `domain q ∪ domain q' ⊆ num INSERT domain q ∪ domain q'` by
      fs[SUBSET_DEF]>>
    metis_tac[INJ_UNION,SUBSET_DEF,INJ_SUBSET])
  >>
    (fs[coloring_ok_alt_def,coloring_ok_def,get_live_sets_def]>>
    EVERY_CASE_TAC>>fs[LET_THM]>>
    Cases_on`get_live_sets prog live`>>
    imp_res_tac get_live_sets_thm>>fs[]>>
    fs[domain_union]
    >-
      (`domain q ⊆ f' INSERT domain q` by fs[SUBSET_DEF]>>
      metis_tac[INJ_UNION,INJ_SUBSET,SUBSET_DEF])
    >>
      Cases_on`get_live_sets r live`>>fs[domain_union]>>
      `domain q' ⊆ f' INSERT domain q'` by fs[SUBSET_DEF]>>
      `domain q'' ⊆ q INSERT domain q''` by fs[SUBSET_DEF]>>
      imp_res_tac get_live_sets_thm>>fs[]>>
      rw[]>>
      metis_tac[INJ_UNION,INJ_SUBSET,SUBSET_DEF]))

val _ = export_theory();
