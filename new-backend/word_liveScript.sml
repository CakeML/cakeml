open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open word_langTheory
open word_procTheory
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

(*
  States equal on all components except:
  1) permute (which needs to be changed to reorder the keys)
  2) locals  (because vars are renamed)
*)

val word_state_eq_rel_def = Define`
  word_state_eq_rel s t ⇔ 
  t.store = s.store ∧ 
  t.stack = s.stack ∧ 
  t.memory = s.memory ∧ 
  t.mdomain = s.mdomain ∧ 
  t.gc_fun = s.gc_fun ∧ 
  t.handler = s.handler ∧ 
  t.clock = s.clock ∧ 
  t.code = s.code ∧ 
  t.output = s.output`

(*tlocs is a supermap of slocs under f*)
val strong_locals_rel_def = Define`
  strong_locals_rel f slocs tlocs ⇔
  ∀n v. (lookup n slocs = SOME v) ==> (lookup (f n) tlocs = SOME v)`

val weak_locals_rel_def = Define`
  weak_locals_rel f slocs tlocs ⇔ 
    slocs = tlocs ∨ strong_locals_rel f slocs tlocs`

val ignore_inc = prove(``
∀perm:num->num->num.
  (λn. perm(n+0)) = perm``,rw[FUN_EQ_THM]) 

val ignore_perm = prove(``
∀st. st with permute := st.permute = st`` ,
 rw[]>>fs[word_state_component_equality])

val get_vars_perm = prove(``
∀args.get_vars args (st with permute:=perm) = get_vars args st``,
  Induct>>rw[get_vars_def,get_var_def])

val pop_env_perm = prove(``
  pop_env (rst with permute:=perm) =
  (case pop_env rst of
    NONE => NONE 
  | SOME rst' => SOME (rst' with permute:=perm))``,
  fs[pop_env_def]>>EVERY_CASE_TAC>>
  fs[word_state_component_equality])

val set_var_perm = prove(``
  set_var v x (s with permute:=perm) =
  (set_var v x s) with permute:=perm``,
  fs[set_var_def])

val word_state_rewrites = prove(``
  (st with clock:=A) with permute:=B =
  (st with <|clock:=A ;permute:=B|>)``,
  fs[])

val perm_assum_tac = (first_x_assum(qspec_then`perm`assume_tac)>>
          fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
          qexists_tac`λx. if x = 0 then st.permute 0 else perm' (x-1)`>>
          fs[call_env_def]>>
          `(λn. perm' n) = perm'` by fs[FUN_EQ_THM]>>
          simp[]);

(*For any target result permute, we can find an initial permute such that the resulting permutation is the same*)
val permute_swap_lemma = prove(``
∀prog st perm.
  let (res,rst) = wEval(prog,st) in 
    res ≠ SOME Error  (*Provable without this assum*)
    ⇒ 
    ∃perm'. wEval(prog,st with permute := perm') = 
    (res,rst with permute:=perm)``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>>cheat)
  >-
    (fs[wEval_def]>>metis_tac[ignore_perm])
  >- ...

  >- (*Seq*)
    fs[wEval_def,LET_THM]>>
    Cases_on`wEval(prog,st)`>>fs[]>>
    Cases_on`q`>>fs[]
    >-
      (last_x_assum(qspec_then `perm` assume_tac)>>fs[]>>
      last_x_assum(qspec_then `perm'` assume_tac)>>fs[]>>
      qexists_tac`perm''`>>fs[])
    >>
      qexists_tac`st.permute`>>fs[ignore_perm]>>
      first_assum(qspecl_then[`
  >- (*Call*)
    (fs[wEval_def,LET_THM]>>
    fs[get_vars_perm]>>
    Cases_on`get_vars args st`>>fs[]>>
    Cases_on`find_code dest x st.code`>>fs[]>>
    Cases_on`x'`>>
    Cases_on`ret`>>fs[]
    >- (*Tail Call*)
      (EVERY_CASE_TAC>>
      TRY(qexists_tac`perm`>>
        fs[word_state_component_equality,call_env_def]>>NO_TAC)>>
      Cases_on`x'`>>
      fs[dec_clock_def]>>
      first_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
      qexists_tac`perm'`>>
      fs[word_state_component_equality,call_env_def]>>
      qpat_assum`A=res`(SUBST1_TAC o SYM)>>fs[])
    >>
      PairCases_on`x'`>>fs[]>>
      Cases_on`cut_env x'1 st.locals`>>fs[]>>
      Cases_on`st.clock=0`>>fs[]
      >-
        (fs[call_env_def]>>
        qexists_tac`perm`>>fs[word_state_component_equality])
      >>
      Cases_on`wEval(r,call_env q(push_env x' 
              (IS_SOME handler) (dec_clock st)))`>>
      Cases_on`q'`>>fs[]>>
      Cases_on`x''`>>fs[]
      >-
        (Cases_on`pop_env r'`>>fs[]>>
        Cases_on`domain x''.locals = domain x'`>>fs[]>>
        Cases_on`wEval(x'2,set_var x'0 a x'')`>>
        Cases_on`q'`>>fs[]>>
        last_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
        last_x_assum(qspec_then`perm'`assume_tac)>>fs[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
        `(λn. perm'' n) = perm''` by fs[FUN_EQ_THM]>>
        fs[word_state_component_equality,call_env_def]>>
        fs[pop_env_perm]>>
        fs[set_var_perm]>>Cases_on`res`>>
        qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[])
      >-
        (FULL_CASE_TAC>>fs[]
        >- 
          (perm_assum_tac>>
          qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[])
        >>
        Cases_on`x''`>>fs[]>>
        Cases_on`domain r'.locals = domain x'`>>fs[]>>
        Cases_on`wEval (r'',set_var q' w r')`>>
        Cases_on`q'' = SOME Error`>>fs[]>>
        first_x_assum(qspec_then`perm`assume_tac)>>fs[]>>
        last_x_assum(qspec_then`perm'`assume_tac)>>fs[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        fs[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
        `(λn. perm'' n) = perm''` by fs[FUN_EQ_THM]>>
        fs[word_state_component_equality,call_env_def]>>
        fs[set_var_perm]>>
        metis_tac[word_state_component_equality])
      >>
        perm_assum_tac>>
        qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[])
        

val liveness_theorem = prove(``
∀prog st cst f live.
  coloring_ok f prog live ∧
  word_state_eq_rel st cst ∧
  strong_locals_rel f st.locals cst.locals
  (*Not necessary? permute already quantified
  ∧ cst.permute = perm*)
  ⇒ 
  ∃perm'.  
  let (res,rst) = wEval(prog,st with permute:=perm') in
  if (res = SOME Error) then T else 
  let (res',rcst) = wEval(apply_color f prog,cst) in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧ 
    (case res of 
      NONE => strong_locals_rel f rst.locals rcst.locals
    | _    => weak_locals_rel f rst.locals rcst.locals)``,
  Induct>>cheat
  ...
  >- (*Seq*)
    (rw[]>>fs[wEval_def,coloring_ok_def,LET_THM]>>
    last_x_assum(qspecl_then[`st`,`cst`,`f`,`get_live prog' live`]
      assume_tac)>> rfs[]>>
    Cases_on`wEval(prog,st with permute:=perm')`>>fs[]
    >- (qexists_tac`perm'`>>fs[]) >>
    Cases_on`wEval(apply_color f prog,cst)`>>fs[]>>
    REVERSE (Cases_on`q`)>>fs[]
    >- (qexists_tac`perm'`>>rw[])
    >>
    first_x_assum(qspecl_then[`r`,`r'`,`f`,`live`] assume_tac)>>rfs[]>>
    (*temp should be the permute composition of perm' and perm''
      such that wEval(prog,st with permute:=temp) gives
      (NONE,r with permute:=perm'')
    *)
    qspecl_then[`prog`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>qpat_assum`A=q'` (SUBST_ALL_TAC o SYM)>>
    fs[]>>
    qexists_tac`perm'''`>>rw[]>>fs[])

    `wEval(prog,st with permute:=temp) = (NONE,r with permute:=perm'')` 
      by cheat >>
    fs[]
    
    Cases_on`wEval(prog',r with permute := perm'')`>>fs[]
    >- 
      
    qpat_assum `NONE = q'` (SUBST_ALL_TAC o SYM)>>
    qexists_tac`perm'`>>rw[]
    )
    >>
      
        
    fs[]>>rw[])
    qexists_tac`st.permute`>>fs[word_state_component_equality]

(*
∀prog f live.
  coloring_ok f prog live
  ⇒ 
  ∀perm cst.
  cst.permute = perm
  ⇒  
  ∃perm'.
  ∀st res rst. 
    word_state_eq_rel st cst ∧
    strong_locals_rel f st.locals cst.locals ∧
    st.permute = perm' ∧ 
    wEval(prog,st) = (res,rst) ∧
    res ≠ SOME Error
    ⇒ 
    ∃rcst.
      wEval(apply_color f prog,cst) = (res,rcst) ∧
      word_state_eq_rel rst rcst ∧
      (case res of 
        NONE => strong_locals_rel f rst.locals rcst.locals
      | _    => weak_locals_rel f rst.locals rcst.locals)``,


completeInduct_on`word_prog_size (K 0) prog`>>
rpt strip_tac>>
fs[PULL_FORALL]>>
Cases_
(*Cant do homatchmptac*)
  Induct>>rw[]
  >-
    simp[wEval_def] (*??? too easy.. might be something wrong*)
  >-
   ...
  >-(*Seq*) 
    fs[coloring_ok_def,wEval_def,LET_THM]>>
    res_tac>>
    first_x_assum(qspec_then`cst` assume_tac)>>fs[]>>


∀prog st rst f cst res live.
  (*I think these are safe outside the exists*)
  coloring_ok f qprog live ∧ 
  ⇒
  ∀perm. 
    ∃perm'.
      ∀st.
      word_state_eq_rel st cst ∧ 
      strong_locals_rel f st.locals cst.locals
      st.permute = perm' ∧ 
      cst.permute = perm ∧ 
      wEval(prog,st) = (res,rst) ∧
      res ≠ SOME Error
      ⇒ 
      ∃rcst (*i*).
          (*I think structural induction works better than induction 
    on evaluation relation for this proof because of I need to do a
    swap of the permute midway through the induction for Seq and If
    TODO: need to match the induction thm correctly for Call
    *)
  Induct>>

  >-(rw[wEval_def]>>EVERY_CASE_TAC>>metis_tac[])

  (*Seq*)
  rw[wEval_def,coloring_ok_def,LET_THM]>>
  Cases_on`wEval(prog,st)`>>fs[]>>
  IF_CASES_TAC>>fs[]
  last_x_assum(qspecl_then [`st`,`rst`,`f`,`cst`,`res`
              ,`(get_live prog' live)`] assume_tac)>>rfs[]
  fs[wEval_def,coloring_ok_def,LET_THM]>>
    Cases_on`wEval(prog,st)`>>fs[]>>
    IF_CASES_TAC>>fs[]
    >-
     (
     first_x_assum(qspecl_then[`st`,`r`,`f`,`cst`,`NONE`
                               ,`(get_live prog' live)`]assume_tac)>>
     rfs[]>>
     (*Proof idea:
     wEval(prog,st) -> (NONE,r)

     
     
     *)


     qexists_tac`perm'`>>rw[]>>rfs[]>>
     
     last_x_assum(qspecl_then[`perm`,`r`,`f`,`cst`
                                ,`q`,`live`]assume_tac)>>
      rfs[]>>
      qexists_tac`perm'`>>rw[]>>rfs[])
    >>
      (first_x_assum(qspecl_then[`perm`,`r`,`f`,`cst`
                                ,`q`,`(get_live prog' live)`]assume_tac)>>
      fs[]>>qexists_tac`perm'`>>rw[]>>rfs[]>>metis_tac[])


  
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]
  >-(*Skip*)
    (fs[wEval_def,word_state_eq_rel_def]>>
    EVERY_CASE_TAC>>
    qexists_tac`perm`>>
    metis_tac[ignore_inc])
  >-(*Alloc*)
    (fs[wEval_def]>>
    cheat)
  >-(*Move*)
    cheat
  >-(*Inst*)
    cheat
  >-(*Assign*)
    cheat*)


  >-(*Get*)
    cheat
  >-(*Set*)
    cheat
  >-(*Store*)
    cheat
  >-(*Tick*)
    (fs[wEval_def,call_env_def,word_state_eq_rel_def]>>
    qexists_tac `perm`>>fs[]>>
    IF_CASES_TAC
    >-
      (rw[]>>fs[weak_locals_rel_def]>>
      metis_tac[ignore_inc])
    >>
      rw[dec_clock_def,word_state_component_equality]>>
      fs[strong_locals_rel_def]>>
      qexists_tac `rst with <|locals:=cst.locals;permute:=cst.permute|>`>>
      fs[]>>metis_tac[ignore_inc])
  >-(*Seq*)
    (*This needs a side lemma*)
  
val _ = export_theory();
