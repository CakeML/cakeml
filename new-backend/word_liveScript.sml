open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory BasicProvers sortingTheory miscTheory
open word_langTheory word_lemmasTheory word_procTheory

val _ = new_theory "word_live";

(*Define a liveness analysis algorithm*)

val numset_list_insert_def = Define`
  (numset_list_insert [] t = t) ∧ 
  (numset_list_insert (x::xs) t = insert x () (numset_list_insert xs t))`

(*This is the version to use for proofs*)

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
val get_live_def = Define`
  (get_live Skip live = live) ∧ 
  (*All SNDs are read and all FSTs are written*)
  (get_live (Move ls) live =
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
  (get_live (If e1 num e2 e3) live =
    let e2_live = get_live e2 live in 
    let e3_live = get_live e3 live in
      get_live e1 (insert num () (union e2_live e3_live))) ∧
  (get_live (Alloc num numset) live = insert num () numset) ∧ 
  (get_live (Raise num) live = insert num () live) ∧
  (get_live (Return num) live = insert num () live) ∧
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

(* For register allocation, we are concerned with the 
   interference graph formed from clash sets 
   Therefore we require coloring_ok to check all the clash sets 
   in the prog

   For each instruction n, the clash set is:
   live_after(n) ∪ writes(n)

   Overall, f must also be injective over the initial liveset

  NOTE: This differs significantly from David's definition which relies
        on no_dead_code
*)

(*Single step immediate writes by a prog*)
val get_writes_def = Define`
  (get_writes (Move ls) = numset_list_insert (MAP FST ls) LN)∧
  (get_writes (Inst i) = get_writes_inst i) ∧
  (get_writes (Assign num exp) = insert num () LN)∧
  (get_writes (Get num store) = insert num () LN) ∧
  (get_writes prog = LN)` 

val coloring_ok_def = Define`
  (coloring_ok f (Seq s1 s2) live =
    (*Normal live sets*)
    let s2_live = get_live s2 live in
    let s1_live = get_live s1 s2_live in
      INJ f (domain s1_live) UNIV ∧  
      (*Internal clash sets*)
      coloring_ok f s2 live ∧ coloring_ok f s1 s2_live) ∧
  (coloring_ok f (If e1 num e2 e3) live =
    let e2_live = get_live e2 live in 
    let e3_live = get_live e3 live in
    (*All of them must be live at once*)
    let merged = insert num () (union e2_live e3_live) in
    let e1_live = get_live e1 merged in  
      INJ f (domain e1_live) UNIV ∧
      (*Internal interference sets*) 
      coloring_ok f e2 live ∧ coloring_ok f e3 live ∧ 
      coloring_ok f e1 merged) ∧ 
  (coloring_ok f (Call (SOME (v,cutset,ret_handler)) dest args h) live =
    let args_set = numset_list_insert args LN in
    INJ f (domain (union cutset args_set)) UNIV ∧
    INJ f (domain (insert v () cutset)) UNIV ∧ 
    (*returning handler*)
    coloring_ok f ret_handler live ∧
    (*exception handler*)
    (case h of 
    | NONE => T
    | SOME(v,prog) =>
        INJ f (domain (insert v () cutset)) UNIV ∧
        coloring_ok f prog live)) ∧ 
  (coloring_ok f prog live =
    (*live before must be fine, and clash set must be fine*)
    let lset = get_live prog live in  
    let iset = union (get_writes prog) live in
      INJ f (domain lset) UNIV ∧ INJ f (domain iset) UNIV)`

(*Slightly smarter version that collects clash sets into a list
  Result is a tuple:
  (hdlive,clash_sets) where hdlive is the liveset in front of 
  that program and clash_sets is everything induced inside
*)
val get_clash_sets_def = Define`
  (get_clash_sets (Seq s1 s2) live =
    let (hd,ls) = get_clash_sets s2 live in
    let (hd',ls') = get_clash_sets s1 hd in
      (hd',(ls' ++ ls))) ∧ 
  (get_clash_sets (If e1 num e2 e3) live =
    let (h2,ls2) = get_clash_sets e2 live in 
    let (h3,ls3) = get_clash_sets e3 live in
    let merged = insert num () (union h2 h3) in 
    let (h,ls1) = get_clash_sets e1 merged in
      (h,ls1++ls2++ls3)) ∧    
  (get_clash_sets (Call (SOME (v,cutset,ret_handler)) dest args h) live =
    (*top level*)
    let args_set = numset_list_insert args LN in
    let (hd,ls) = get_clash_sets ret_handler live in
    (*Outer liveset*)
    let live_set = union cutset args_set in
    (*Returning clash set*)
    let ret_clash = insert v () cutset in 
    (case h of
      NONE => (live_set,ret_clash::hd::ls)
    | SOME(v',prog) =>
        let (hd',ls') = get_clash_sets prog live in
        (*Handler clash set*)
        let h_clash = insert v' () cutset in 
        (live_set,h_clash::ret_clash::hd::hd'::ls++ls'))) ∧ 
  (*Catchall for cases where we dont have in sub programs live sets*)
  (get_clash_sets prog live =
    let i_set = union (get_writes prog) live in
      (get_live prog live,[i_set]))` 

val coloring_ok_alt_def = Define`
  coloring_ok_alt f prog live = 
    let (hd,ls) = get_clash_sets prog live in 
    EVERY (λs. INJ f (domain s) UNIV) ls ∧ 
    INJ f (domain hd) UNIV`

(*Equivalence on everything except permutation and locals*)
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

(*tlocs is a supermap of slocs under f for everything in a given
  live set*)
val strong_locals_rel_def = Define`
  strong_locals_rel f ls slocs tlocs ⇔
  ∀n v. 
    n ∈ ls ∧ lookup n slocs = SOME v ⇒
    lookup (f n) tlocs = SOME v`

(*--- FINISHED DEFS ---*)

(*--- LEMMAS --- *)
val domain_numset_list_insert = prove(``
  ∀ls locs. 
  domain (numset_list_insert ls locs) = domain locs UNION set ls``,
  Induct>>fs[numset_list_insert_def]>>rw[]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM])

val strong_locals_rel_get_var = prove(``
  strong_locals_rel f live st.locals cst.locals ∧
  n ∈ live ∧  
  get_var n st = SOME x 
  ⇒ 
  get_var (f n) cst = SOME x``,
  fs[get_var_def,strong_locals_rel_def])

val strong_locals_rel_get_vars = prove(``
  ∀ls y f live st cst.
  strong_locals_rel f live st.locals cst.locals ∧
  (∀x. MEM x ls ⇒ x ∈ live) ∧ 
  get_vars ls st = SOME y
  ⇒ 
  get_vars (MAP f ls) cst = SOME y``,
  Induct>>fs[get_vars_def]>>rw[]>>
  Cases_on`get_var h st`>>fs[]>>
  `h ∈ live` by fs[]>>
  imp_res_tac strong_locals_rel_get_var>>fs[]>>
  Cases_on`get_vars ls st`>>fs[]>>
  res_tac>>
  pop_assum(qspec_then`live` mp_tac)>>discharge_hyps
  >-metis_tac[]>>
  fs[])

val domain_FOLDR_delete = prove(``
  ∀ls live. domain (FOLDR delete live ls) =
  (domain live) DIFF (set ls)``,
  Induct>>
  fs[DIFF_INSERT,EXTENSION]>>
  metis_tac[])

val domain_FOLDR_union_subset = prove(``
  !ls a.
  MEM a ls ⇒ 
  domain (get_live_exp a) ⊆ 
  domain (FOLDR (λx y.union (get_live_exp x) y) LN ls)``,
  Induct>>rw[]>>fs[domain_union,SUBSET_UNION,SUBSET_DEF]>>
  metis_tac[])

val SUBSET_OF_INSERT = store_thm("SUBSET_OF_INSERT",
``!s x. s ⊆ x INSERT s``,
  rw[SUBSET_DEF])

val INJ_UNION = prove(
``!f A B.
  INJ f (A ∪ B) UNIV ⇒ 
  INJ f A UNIV ∧ 
  INJ f B UNIV``,
  rw[]>>
  metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_UNION])

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

val wGC_perm = prove(``
  wGC st = SOME x ⇒ 
  wGC (st with permute:=perm) = SOME (x with permute := perm)``,
  fs[wGC_def,LET_THM]>>EVERY_CASE_TAC>>
  fs[word_state_component_equality])

val get_var_perm = prove(``
  get_var n (st with permute:=perm) =
  (get_var n st)``,fs[get_var_def])

val set_var_perm = prove(``
  set_var v x (s with permute:=perm) =
  (set_var v x s) with permute:=perm``,
  fs[set_var_def])

val get_vars_perm = prove(``
  ∀ls. get_vars ls (st with permute:=perm) =
  (get_vars ls st)``,
  Induct>>fs[get_vars_def,get_var_perm])

val set_vars_perm = prove(``
  ∀ls. set_vars ls x (st with permute := perm) =
       (set_vars ls x st) with permute:=perm``,
  fs[set_vars_def])

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

val word_exp_perm = prove(``
  ∀s exp. word_exp (s with permute:=perm) exp =
          word_exp s exp``,
  ho_match_mp_tac word_exp_ind>>rw[word_exp_def]
  >-
    (EVERY_CASE_TAC>>fs[mem_load_def])
  >>
    `ws=ws'` by 
      (unabbrev_all_tac>>
      fs[MAP_EQ_f])>>
    fs[])

val mem_store_perm = prove(``
  mem_store a (w:'a word_loc) (s with permute:=perm) =
  case mem_store a w s of
    NONE => NONE
  | SOME x => SOME(x with permute:=perm)``,
  fs[mem_store_def]>>EVERY_CASE_TAC>>
  fs[word_state_component_equality])

val jump_exc_perm = prove(``
  jump_exc (st with permute:=perm) =
  case jump_exc st of
    NONE => NONE
  | SOME x => SOME (x with permute:=perm)``,
  fs[jump_exc_def]>>
  EVERY_CASE_TAC>>
  fs[word_state_component_equality])

(*For any target result permute, we can find an initial permute such that the resulting permutation is the same*)
val permute_swap_lemma = prove(``
∀prog st perm.
  let (res,rst) = wEval(prog,st) in 
    res ≠ SOME Error  (*Provable without this assum*)
    ⇒ 
    ∃perm'. wEval(prog,st with permute := perm') = 
    (res,rst with permute:=perm)``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>>fs[wEval_def]
  >-
    metis_tac[ignore_perm]
  >-
    (fs[wAlloc_def]>>
    qexists_tac`λx. if x = 0 then st.permute 0 else perm (x-1)`>>
    fs[get_var_perm]>>
    FULL_CASE_TAC>>FULL_CASE_TAC>>fs[]
    >-
      (Cases_on`x`>>fs[])
    >>
    FULL_CASE_TAC>>fs[]>>
    Cases_on`wGC (push_env x F(set_store AllocSize (Word c) st))`>>
    fs[push_env_def,env_to_list_def,LET_THM,set_store_def]>>
    imp_res_tac wGC_perm>>fs[pop_env_perm]>>
    ntac 3 (FULL_CASE_TAC>>fs[])>>
    fs[has_space_def]>>
    IF_CASES_TAC>>
    fs[word_state_component_equality,FUN_EQ_THM,call_env_def])
  >-
    (qexists_tac`perm`>>fs[get_vars_perm]>>
    ntac 2 (FULL_CASE_TAC>>fs[])>>
    fs[set_vars_perm])
  >-
    (qexists_tac`perm`>>
    fs[wInst_def,word_assign_def]>>EVERY_CASE_TAC>>
    fs[set_var_perm,word_exp_perm,get_var_perm,mem_store_perm]>>
    TRY(metis_tac[word_exp_perm,word_state_component_equality])>>
    rfs[]>>fs[])
  >-
    (fs[word_exp_perm]>>EVERY_CASE_TAC>>
    fs[set_var_perm]>>
    metis_tac[word_state_component_equality])
  >-
    (EVERY_CASE_TAC>>fs[set_var_perm]>>
    metis_tac[word_state_component_equality])
  >-
    (fs[word_exp_perm]>>EVERY_CASE_TAC>>
    fs[set_store_def]>>
    qexists_tac`perm`>>fs[word_state_component_equality])
  >-
    (fs[word_exp_perm]>>EVERY_CASE_TAC>>
    fs[get_var_perm,mem_store_perm]>>
    metis_tac[word_state_component_equality])
  >-
    (qexists_tac`perm`>>
    EVERY_CASE_TAC>>fs[dec_clock_def,call_env_def]>>
    fs[word_state_component_equality])
  >- (*Seq*)
    (fs[wEval_def,LET_THM]>>
    Cases_on`wEval(prog,st)`>>fs[]>>
    Cases_on`q`>>fs[]
    >-
      (last_x_assum(qspec_then `perm` assume_tac)>>fs[]>>
      last_x_assum(qspec_then `perm'` assume_tac)>>fs[]>>
      qexists_tac`perm''`>>fs[])
    >>
      first_x_assum(qspecl_then[`perm`]assume_tac)>>rfs[]>>
      Cases_on`x`>>fs[]>>
      qexists_tac`perm'`>>fs[]>>
      qpat_assum`A=res`(SUBST1_TAC o SYM)>>fs[])
  >-
    (fs[get_var_perm]>>EVERY_CASE_TAC>>
    fs[call_env_def,word_state_component_equality])
  >-
    (fs[get_var_perm]>>EVERY_CASE_TAC>>
    fs[jump_exc_perm]>>metis_tac[word_state_component_equality])
  >-
    (Cases_on`wEval(prog,st)`>>fs[]>>
    Cases_on`q`>>fs[]
    >-
      (ntac 2(FULL_CASE_TAC>>fs[])>>
      Cases_on`c=0w`>>fs[]>>
      first_x_assum(qspec_then `perm` assume_tac)>>fs[LET_THM]>>rfs[]>>
      first_x_assum(qspec_then `perm'` assume_tac)>>fs[]>>
      qexists_tac`perm''`>>fs[get_var_perm])
    >>
      first_x_assum(qspec_then`perm`assume_tac)>>fs[LET_THM]>>
      Cases_on`x`>>rfs[]>>
      qexists_tac`perm'`>>fs[]>>
      qpat_assum`A=res`(SUBST1_TAC o SYM)>>fs[])
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
        qpat_assum`A=res` (SUBST1_TAC o SYM)>>fs[]))
        
val size_tac= (fs[word_prog_size_def]>>DECIDE_TAC);

(*Neater rewrite.. maybe should go into word_proc as the def instead*)
val apply_nummap_key_rw = prove(``
  apply_nummap_key f names = 
  fromAList (MAP (λx,y.f x,y) (toAList names))``,
  rw[]>>AP_TERM_TAC>>
  fs[ZIP_MAP,MAP_MAP_o,MAP_EQ_f,FORALL_PROD])

val apply_nummap_key_domain = prove(``
  ∀f names.
  domain (apply_nummap_key f names) =
  IMAGE f (domain names)``,
  fs[domain_def,apply_nummap_key_rw,domain_fromAList]>>
  fs[MEM_MAP,MAP_MAP_o,EXTENSION,EXISTS_PROD]>>
  metis_tac[MEM_toAList,domain_lookup])

val cut_env_lemma = prove(``
  ∀names sloc tloc x f. 
  INJ f (domain names) UNIV ∧   
  cut_env names sloc = SOME x ∧ 
  strong_locals_rel f (domain names) sloc tloc 
  ⇒ 
  ∃y. cut_env (apply_nummap_key f names) tloc = SOME y ∧
      domain y = IMAGE f (domain x) ∧
      strong_locals_rel f (domain names) x y ∧
      INJ f (domain x) UNIV ∧ 
      domain x = domain names``, 
      (*this old lemma is too strong: exact_colored_locals f x y
        not sure if i need the strength though...
      *)
  rpt strip_tac>>
  fs[domain_inter,apply_nummap_key_rw,cut_env_def,apply_nummap_key_domain
    ,strong_locals_rel_def]>>
  CONJ_ASM1_TAC>-
    (fs[SUBSET_DEF,domain_lookup]>>rw[]>>metis_tac[])>>
  CONJ_ASM1_TAC>-
    (Q.ISPECL_THEN[`f`,`names`] assume_tac apply_nummap_key_domain>>
    fs[apply_nummap_key_rw]>>
    fs[SUBSET_INTER_ABSORPTION,INTER_COMM]>>
    metis_tac[domain_inter])>>
  rw[]>-
    (rw[]>>fs[lookup_inter]>>
    Cases_on`lookup n sloc`>>fs[]>>
    Cases_on`lookup n names`>>fs[]>>
    res_tac>>
    imp_res_tac MEM_toAList>>
    fs[lookup_fromAList]>>
    EVERY_CASE_TAC>>
    fs[ALOOKUP_NONE,MEM_MAP,FORALL_PROD]>>metis_tac[])
  >>
    fs[domain_inter,SUBSET_INTER_ABSORPTION,INTER_COMM])

val MEM_nub = prove(``
  ∀x ls. MEM x ls ⇔ MEM x (nub ls)``,
  fs[nub_def])

val LENGTH_list_rerrange = prove(``
  LENGTH (list_rearrange mover xs) = LENGTH xs``,
  fs[list_rearrange_def]>>
  IF_CASES_TAC>>fs[])

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other
  Fortunately someone already proved a lemma about this in miscTheory
*)
val list_rearrange_perm = prove(``
  PERM xs ys
  ⇒
  ∃perm. list_rearrange perm xs = ys``,
  rw[]>>
  imp_res_tac PERM_BIJ>>fs[list_rearrange_def]>>
  qexists_tac`f`>>
  IF_CASES_TAC>>
  fs[BIJ_DEF,INJ_DEF]>>metis_tac[])

(*Main theorem for permute oracle usage!
  This shows that we can push locals that are exactly matching using 
  any desired permutation
  and we can choose the final permutation to be anything we want
  (In Alloc we choose it to be cst.permute, in Call something
   given by the IH)
*)

val env_to_list_perm = prove(``
  ∀tperm.
  domain y = IMAGE f (domain x) ∧
  INJ f (domain x) UNIV ∧ 
  strong_locals_rel f (domain x) x y
  ⇒ 
  let (l,permute) = env_to_list y perm in 
  ∃perm'.
    let(l',permute') = env_to_list x perm' in
      permute' = tperm ∧ (*Just change the first permute*)
      MAP (λx,y.f x,y) l' = l``,
  rw[]>>
  fs[env_to_list_def,LET_THM,strong_locals_rel_def]>>
  qabbrev_tac `xls = QSORT key_val_compare (nub(toAList x))`>>
  qabbrev_tac `yls = QSORT key_val_compare (nub(toAList y))`>>
  qabbrev_tac `ls = list_rearrange (perm 0) yls`>>
  fs[(GEN_ALL o SYM o SPEC_ALL) list_rearrange_MAP]>>
  `PERM (MAP (λx,y.f x,y) xls) yls` by
    (match_mp_tac PERM_ALL_DISTINCT >>rw[]
    >-
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>rw[]
      >-
        (fs[INJ_DEF,Abbr`xls`,QSORT_MEM]>>
        Cases_on`x'`>>Cases_on`y'`>>fs[]>>
        imp_res_tac MEM_toAList>>
        fs[domain_lookup])
      >>
      fs[Abbr`xls`]>>
      metis_tac[QSORT_PERM,all_distinct_nub,ALL_DISTINCT_PERM])
    >-
      metis_tac[QSORT_PERM,all_distinct_nub,ALL_DISTINCT_PERM]
    >>
      unabbrev_all_tac>>
      fs[QSORT_MEM,MEM_MAP]>>
      fs[EQ_IMP_THM]>>rw[]
      >-
        (Cases_on`y'`>>fs[MEM_toAList]>>metis_tac[domain_lookup])
      >>
        Cases_on`x'`>>fs[MEM_toAList]>>
        imp_res_tac domain_lookup>>
        fs[EXTENSION]>>res_tac>>
        qexists_tac`x',r`>>fs[]>>
        fs[MEM_toAList,domain_lookup]>>
        first_x_assum(qspecl_then[`x'`,`v'`] assume_tac)>>rfs[])
  >>
  `PERM yls ls` by
    (fs[list_rearrange_def,Abbr`ls`]>>
    qpat_assum`A=l` (SUBST1_TAC o SYM)>>
    IF_CASES_TAC>>fs[]>>
    match_mp_tac PERM_ALL_DISTINCT>>
    CONJ_ASM1_TAC>-
      metis_tac[QSORT_PERM,all_distinct_nub,ALL_DISTINCT_PERM]>>
    CONJ_ASM1_TAC>-
      (fs[ALL_DISTINCT_GENLIST]>>rw[]>>
      fs[EL_ALL_DISTINCT_EL_EQ]>>
      `perm 0 i = perm 0 i'` by
        (fs[BIJ_DEF,INJ_DEF]>>
        metis_tac[])>>
      fs[BIJ_DEF,INJ_DEF])
    >>
      fs[MEM_GENLIST,BIJ_DEF,INJ_DEF,SURJ_DEF]>>
      fs[MEM_EL]>>metis_tac[])>>
  imp_res_tac PERM_TRANS>>
  imp_res_tac list_rearrange_perm>>
  qexists_tac`λn. if n = 0:num then perm' else tperm (n-1)`>>
  fs[FUN_EQ_THM])

val mem_list_rearrange = prove(``
  ∀ls x f. MEM x (list_rearrange f ls) ⇔ MEM x ls``,
  fs[MEM_EL]>>rw[list_rearrange_def]>>
  imp_res_tac BIJ_IFF_INV>>
  fs[BIJ_DEF,INJ_DEF,SURJ_DEF]>>
  rw[EQ_IMP_THM]>>fs[EL_GENLIST]
  >- metis_tac[]>>
  qexists_tac `g n`>>fs[])
  
(*Proves s_val_eq and some extra conditions on the resulting lists*)
val push_env_s_val_eq = prove(``
  ∀tperm.
  st.handler = cst.handler ∧ 
  st.stack = cst.stack ∧ 
  domain y = IMAGE f (domain x) ∧
  INJ f (domain x) UNIV ∧ 
  strong_locals_rel f (domain x) x y
  ⇒
  ?perm.
  (let (l,permute) = env_to_list y cst.permute in 
  let(l',permute') = env_to_list x perm in
      permute' = tperm ∧ 
      MAP (λx,y.f x,y) l' = l ∧    
      (∀x y. MEM x (MAP FST l') ∧ MEM y (MAP FST l') 
        ∧ f x = f y ⇒ x = y) ) ∧ 
  s_val_eq (push_env x b (st with permute:=perm)).stack 
           (push_env y b cst).stack``,
  rw[]>>fs[push_env_def]>>
  imp_res_tac env_to_list_perm>>
  pop_assum(qspecl_then[`tperm`,`cst.permute`]assume_tac)>>fs[LET_THM]>>
  Cases_on`env_to_list y cst.permute`>>
  fs[]>>
  qexists_tac`perm'`>>
  Cases_on`env_to_list x perm'`>>
  fs[env_to_list_def,LET_THM]>>
  fs[s_val_eq_def,s_val_eq_refl]>>
  rw[]>-
    (fs[INJ_DEF,MEM_MAP]>>
    imp_res_tac mem_list_rearrange>>
    fs[QSORT_MEM]>>
    Cases_on`y'''`>>Cases_on`y''`>>fs[MEM_toAList]>>
    metis_tac[domain_lookup])>>
  EVERY_CASE_TAC>>fs[s_frame_val_eq_def]>>
  qpat_abbrev_tac `q = list_rearrange A 
    (QSORT key_val_compare (nub (toAList x)))`>>
  `MAP SND (MAP (λx,y.f x,y) q) = MAP SND q` by 
    (fs[MAP_MAP_o]>>AP_THM_TAC>>AP_TERM_TAC>>fs[FUN_EQ_THM]>>
    rw[]>>Cases_on`x'`>>fs[])>>
  metis_tac[])

val INJ_less = prove(``
  INJ f s' UNIV ∧ s ⊆ s'
  ⇒ 
  INJ f s UNIV``,
  metis_tac[INJ_DEF,SUBSET_DEF])

(*TODO: MOVE TO lemmas
wGC doesn't touch other components*)
val wGC_frame = prove(``
  wGC st = SOME st'
  ⇒ 
  st'.mdomain = st.mdomain ∧
  st'.gc_fun = st.gc_fun ∧ 
  st'.handler = st.handler ∧ 
  st'.clock = st.clock ∧ 
  st'.code = st.code ∧ 
  st'.locals = st.locals ∧ 
  st'.output = st.output ∧ 
  st'.permute = st.permute``,
  fs[wGC_def,LET_THM]>>EVERY_CASE_TAC>>
  fs[word_state_component_equality])

val ZIP_MAP_FST_SND_EQ = prove(``
  ∀ls. ZIP (MAP FST ls,MAP SND ls) = ls``,
  Induct>>fs[])

(*Convenient rewrite for pop_env*)
val s_key_eq_val_eq_pop_env = prove(``
  pop_env s = SOME s' ∧ 
  s_key_eq s.stack ((StackFrame ls opt)::keys) ∧ 
  s_val_eq s.stack vals 
  ⇒
  ∃ls' rest.
  vals = StackFrame ls' opt :: rest ∧ 
  s'.locals = fromAList (ZIP (MAP FST ls,MAP SND ls')) ∧
  s_key_eq s'.stack keys ∧ 
  s_val_eq s'.stack rest ∧
  case opt of NONE => s'.handler = s.handler 
            | SOME h => s'.handler = h``,
  strip_tac>>
  fs[pop_env_def]>>
  EVERY_CASE_TAC>>
  Cases_on`vals`>>
  fs[s_val_eq_def,s_key_eq_def]>>
  Cases_on`h`>>Cases_on`o'`>>
  fs[s_frame_key_eq_def,s_frame_val_eq_def]>>
  fs[word_state_component_equality]>>
  metis_tac[ZIP_MAP_FST_SND_EQ])

(*Less powerful form*)
val ALOOKUP_key_remap_2 = prove(``
  ∀ls vals f.
    (∀x y. MEM x ls ∧ MEM y ls ∧ f x = f y ⇒ x = y) ∧ 
    LENGTH ls = LENGTH vals ∧  
    ALOOKUP (ZIP (ls,vals)) n = SOME v
    ⇒ 
    ALOOKUP (ZIP (MAP f ls,vals)) (f n) = SOME v``,
  Induct>>rw[]>>
  Cases_on`vals`>>fs[]>>
  Cases_on`h=n`>>fs[]>>
  `MEM n ls` by 
    (imp_res_tac ALOOKUP_MEM>>
    imp_res_tac MEM_ZIP>>
    fs[]>>
    metis_tac[MEM_EL])>>
  first_assum(qspecl_then[`h`,`n`] assume_tac)>>
  IF_CASES_TAC>>fs[])

val lookup_list_insert = store_thm("lookup_list_insert",
  ``!x (y:'a word_loc list) t (z:num). LENGTH x = LENGTH y ==>
    (lookup z (list_insert x y t) =
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)``,
    ho_match_mp_tac list_insert_ind>>
    rw[]>-
      (Cases_on`y`>>
      fs[LENGTH,list_insert_def]) >>
    Cases_on`z=x`>>
      rw[lookup_def,list_insert_def]>>
    fs[lookup_insert])

val strong_locals_rel_subset = prove(``
  s ⊆ s' ∧ 
  strong_locals_rel f s' st.locals cst.locals
  ⇒ 
  strong_locals_rel f s st.locals cst.locals``,
  rw[strong_locals_rel_def]>>
  metis_tac[SUBSET_DEF])

val env_to_list_keys = prove(``
  let (l,permute) = env_to_list x perm in
  set (MAP FST l) = domain x``,
  fs[LET_THM,env_to_list_def,EXTENSION,MEM_MAP,EXISTS_PROD]>>
  rw[EQ_IMP_THM]
  >-
    (imp_res_tac mem_list_rearrange>>
    fs[QSORT_MEM,MEM_toAList,domain_lookup])
  >>
    fs[mem_list_rearrange,QSORT_MEM,MEM_toAList,domain_lookup])

val list_rearrange_keys = prove(``
  list_rearrange perm ls = e ⇒ 
  set(MAP FST e) = set(MAP FST ls)``,
  fs[LET_THM,EXTENSION]>>rw[EQ_IMP_THM]>>
  metis_tac[MEM_toAList,mem_list_rearrange,MEM_MAP])

val push_env_pop_env_s_key_eq = prove(
  ``∀s t x b. s_key_eq (push_env x b s).stack t.stack ⇒
       ∃l ls opt. 
              t.stack = (StackFrame l opt)::ls ∧ 
              ∃y. (pop_env t = SOME y ∧
                   y.locals = fromAList l ∧  
                   domain x = domain y.locals ∧
                   s_key_eq s.stack y.stack)``,
  rw[push_env_def]>>fs[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  fs[s_key_eq_def,pop_env_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[domain_fromAList,s_frame_key_eq_def]>>
  qpat_assum `A = MAP FST l` (SUBST1_TAC o SYM)>>
  fs[EXTENSION,mem_list_rearrange,MEM_MAP,QSORT_MEM,MEM_toAList
    ,EXISTS_PROD,domain_lookup])

val pop_env_frame = prove(
  ``s_val_eq r'.stack st' ∧
    s_key_eq y'.stack y''.stack ∧ 
    pop_env (r' with stack:= st') = SOME y'' ∧ 
    pop_env r' = SOME y'
    ⇒
    word_state_eq_rel y' y''``,
    fs[pop_env_def]>>EVERY_CASE_TAC>>
    fs[s_val_eq_def,s_frame_val_eq_def,word_state_eq_rel_def
      ,word_state_component_equality]>>
    rw[]>>rfs[]>>
    metis_tac[s_val_and_key_eq])

val key_map_implies = prove(
 ``MAP (λx,y.f x,y) l' = l
 ⇒ MAP f (MAP FST l') = MAP FST l``,
 rw[]>>match_mp_tac LIST_EQ>>
 rw[EL_MAP]>>
 Cases_on`EL x l'`>>fs[])

(*Main proof of liveness theorem starts here*)

val apply_color_exp_lemma = prove(
  ``∀st w cst f res. 
    word_exp st w = SOME res ∧ 
    word_state_eq_rel st cst ∧ 
    strong_locals_rel f (domain (get_live_exp w)) st.locals cst.locals
    ⇒ 
    word_exp cst (apply_color_exp f w) = SOME res``,
  ho_match_mp_tac word_exp_ind>>rw[]>>
  fs[word_exp_def,apply_color_exp_def,strong_locals_rel_def
    ,get_live_exp_def,word_state_eq_rel_def]
  >-
    (EVERY_CASE_TAC>>fs[])
  >-
    (Cases_on`word_exp st w`>>fs[]>>
    `mem_load x st = mem_load x cst` by
      fs[mem_load_def]>>fs[])
  >-
    (fs[LET_THM]>>
    `MAP (\a.word_exp st a) wexps =
     MAP (\a.word_exp cst a) (MAP (\a. apply_color_exp f a) wexps)` by
       (simp[MAP_MAP_o] >>
       simp[MAP_EQ_f] >>
       gen_tac >>
       strip_tac >>
       first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
       fs[EVERY_MEM,MEM_MAP,PULL_EXISTS
         ,miscTheory.IS_SOME_EXISTS] >>
       first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
       strip_tac >>
       disch_then(qspecl_then[`cst`,`f`,`x`]mp_tac) >>
       discharge_hyps
       >-
         (fs[]>>
         imp_res_tac domain_FOLDR_union_subset>>
         rw[]>>
         metis_tac[SUBSET_DEF])>>
       fs[]) >>
     pop_assum(SUBST1_TAC o SYM) >>
     simp[EQ_SYM_EQ])
  >>
    EVERY_CASE_TAC>>fs[]>>res_tac>>fs[]>>
    metis_tac[])

(*Frequently used tactics*)
val exists_tac = qexists_tac`cst.permute`>>
    fs[wEval_def,LET_THM,word_state_eq_rel_def
      ,get_live_def,coloring_ok_def];    

val exists_tac_2 = 
    Cases_on`word_exp st w`>>fs[word_exp_perm]>>
    imp_res_tac apply_color_exp_lemma>>
    pop_assum (qspecl_then[`f`,`cst`] mp_tac)>>
    discharge_hyps
    >-
      metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
               ,strong_locals_rel_subset];
               
val setup_tac = Cases_on`word_exp st exp`>>fs[]>>
      imp_res_tac apply_color_exp_lemma>>
      pop_assum(qspecl_then[`f`,`cst`]mp_tac)>>unabbrev_all_tac;
     

(*TODO: Find a better name, this is not exactly about liveness*) 

val liveness_theorem = store_thm("liveness_theorem",
``∀prog st cst f live.
  coloring_ok f prog live ∧
  word_state_eq_rel st cst ∧
  strong_locals_rel f (domain (get_live prog live)) st.locals cst.locals 
  ⇒ 
  ∃perm'.  
  let (res,rst) = wEval(prog,st with permute:=perm') in
  if (res = SOME Error) then T else 
  let (res',rcst) = wEval(apply_color f prog,cst) in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧ 
    (case res of 
      NONE => strong_locals_rel f (domain live) 
              rst.locals rcst.locals
    | _    => T )``,
  (*Induct on size of program*)
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,wEval_def]>>
  Cases_on`prog`
  >- (*Skip*)
    exists_tac
  >- (*Move*)
    (exists_tac>>
    fs[MAP_ZIP,get_writes_def,domain_union,domain_numset_list_insert]>>
    Cases_on`ALL_DISTINCT (MAP FST l)`>>fs[]>>
    `ALL_DISTINCT (MAP f (MAP FST l))` by
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>rw[]>>
      FULL_SIMP_TAC bool_ss [INJ_DEF]>>
      first_x_assum(qspecl_then[`x`,`y`] assume_tac)>>
      simp[])>>
    fs[MAP_MAP_o,get_vars_perm] >>
    Cases_on`get_vars (MAP SND l) st`>>fs[]>>
    `get_vars (MAP f (MAP SND l)) cst = SOME x` by
      (imp_res_tac strong_locals_rel_get_vars>>
      first_x_assum(qspec_then `MAP SND ls` mp_tac)>>fs[])>>
    fs[set_vars_def,MAP_MAP_o]>>
    fs[strong_locals_rel_def]>>rw[]>>
    `LENGTH l = LENGTH x` by 
      metis_tac[LENGTH_MAP,get_vars_length_lemma]>>
    fs[lookup_list_insert]>>
    Cases_on`ALOOKUP (ZIP (MAP FST l,x)) n`>>fs[]
    >-
    (*NONE:
      Therefore n is not in l but it is in live and so it is not deleted
     *)
      (`n ∈ domain (FOLDR delete live (MAP FST l))` by
        (fs[domain_FOLDR_delete]>>
        fs[ALOOKUP_NONE]>>rfs[MAP_ZIP])>>
      EVERY_CASE_TAC>>fs[]>>
      imp_res_tac ALOOKUP_MEM>>
      pop_assum mp_tac>>
      fs[MEM_ZIP]>>strip_tac>>
      rfs[EL_MAP,ALOOKUP_NONE]>>
      rfs[MAP_ZIP]>>
      `n = FST (EL n' l)` by
        (FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_assum(qspecl_then[`n`,`FST (EL n' l)`] mp_tac)>>
        discharge_hyps>-
          (rw[]>>DISJ1_TAC>>
          metis_tac[MEM_MAP,MEM_EL])>>
        metis_tac[])>>
      metis_tac[MEM_EL,MEM_MAP])
    >>
      imp_res_tac ALOOKUP_MEM>>
      `ALOOKUP (ZIP (MAP (f o FST) l ,x)) (f n) = SOME v'` by 
        (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
        pop_assum mp_tac>>
        fs[MAP_ZIP,MEM_ZIP,LENGTH_MAP]>>strip_tac>>fs[]>>
        HINT_EXISTS_TAC>>fs[EL_MAP])>>
      fs[])
  >- (*Inst*)
    (exists_tac>>
    Cases_on`i`>> (TRY (Cases_on`a`))>> (TRY(Cases_on`m`))>>
    fs[get_live_def,get_live_inst_def,wInst_def,word_assign_def
      ,word_exp_perm]
    >-
      (Cases_on`word_exp st (Const c)`>>
      fs[word_exp_def,set_var_def,strong_locals_rel_def,get_writes_def
        ,get_writes_inst_def,domain_union,lookup_insert]>>
      rw[]>>
      FULL_SIMP_TAC bool_ss [INJ_DEF]>>
      first_x_assum(qspecl_then [`n'`,`n`] assume_tac)>>fs[])
    >-
      (Cases_on`r`>>fs[]>>
      qpat_abbrev_tac `exp = (Op b [Var n0;B])`>>setup_tac>>
      (discharge_hyps
      >-
        (fs[get_live_exp_def,domain_union]>>
        `{n0} ⊆ (n0 INSERT domain live DELETE n)` by fs[SUBSET_DEF]>>
        TRY(`{n0} ∪ {n'} ⊆ (n0 INSERT n' INSERT domain live DELETE n)` by
          fs[SUBSET_DEF])>>
        metis_tac[strong_locals_rel_subset])
      >>
      fs[apply_color_exp_def,word_state_eq_rel_def]>>
      fs[set_var_def,strong_locals_rel_def,lookup_insert,get_writes_def
        ,get_writes_inst_def]>>
      rw[]>>
      TRY(qpat_abbrev_tac `n''=n'`)>>
      Cases_on`n''=n`>>fs[]>>
      `f n'' ≠ f n` by 
        (fs[domain_union]>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_x_assum(qspecl_then[`n''`,`n`] mp_tac)>>
        discharge_hyps>-
          rw[]>>
        metis_tac[])>>
      fs[]))
    >-
      (qpat_abbrev_tac`exp = (Shift s (Var n0) B)`>>
      setup_tac>>
      discharge_hyps>-
        (fs[get_live_exp_def]>>
        `{n0} ⊆ n0 INSERT domain live DELETE n` by fs[SUBSET_DEF]>>
        metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset])>>
      fs[word_exp_def,word_state_eq_rel_def,set_var_def]>>
      Cases_on`lookup n0 st.locals`>>fs[strong_locals_rel_def]>>
      res_tac>>
      fs[lookup_insert]>>
      rw[]>>
      Cases_on`n=n'`>>fs[]>>
      `f n' ≠ f n` by 
        (fs[domain_union,get_writes_inst_def,get_writes_def]>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_x_assum(qspecl_then[`n'`,`n`]mp_tac)>>
        discharge_hyps>-rw[]>>
        metis_tac[])>>
      fs[])
    >-
      (qpat_abbrev_tac`exp=(Load (Op Add [Var n';A]))`>>
      setup_tac>>
      discharge_hyps>-
        (fs[get_live_exp_def]>>
        `{n'} ⊆ n' INSERT domain live DELETE n` by fs[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      fs[word_state_eq_rel_def,LET_THM,set_var_def]>>
      rw[strong_locals_rel_def]>>
      fs[lookup_insert]>>
      Cases_on`n''=n`>>fs[]>>
      `f n'' ≠ f n` by 
        (fs[domain_union,get_writes_def,get_writes_inst_def]>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_x_assum(qspecl_then[`n''`,`n`]mp_tac)>>
        discharge_hyps>-rw[]>>
        metis_tac[])>>
      fs[strong_locals_rel_def])
    >>
      (qpat_abbrev_tac`exp=Op Add [Var n';A]`>>
      setup_tac>>
      discharge_hyps>-
        (fs[get_live_exp_def]>>
        `{n'} ⊆ n' INSERT n INSERT domain live` by fs[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      fs[word_state_eq_rel_def,LET_THM,set_var_def]>>
      rw[get_var_perm]>>
      Cases_on`get_var n st`>>fs[]>>
      imp_res_tac strong_locals_rel_get_var>>
      Cases_on`mem_store x x' st`>>fs[mem_store_def,strong_locals_rel_def]))
  >- (*Assign*)
    (exists_tac>>exists_tac_2>>
    rw[word_state_eq_rel_def,set_var_perm,set_var_def]>>
    fs[strong_locals_rel_def]>>rw[]>>
    fs[lookup_insert]>>Cases_on`n=n'`>>fs[get_writes_def]>>
    `f n' ≠ f n` by 
      (FULL_SIMP_TAC bool_ss [INJ_DEF]>>
      first_x_assum(qspecl_then [`n`,`n'`] mp_tac)>>
      rw[domain_union,domain_delete])>>
    fs[domain_union])
  >- (*Get*)
    (exists_tac>>
    EVERY_CASE_TAC>>
    fs[coloring_ok_def,set_var_def,strong_locals_rel_def,get_live_def]>>
    fs[LET_THM,get_writes_def]>>rw[]>>
    fs[lookup_insert]>>Cases_on`n'=n`>>fs[]>>
    `f n' ≠ f n` by
      (FULL_SIMP_TAC bool_ss [INJ_DEF,domain_union,domain_insert]>>
      first_x_assum(qspecl_then[`n`,`n'`] assume_tac)>>
      rfs[])>>
    fs[])
  >- (*Set*)
    (exists_tac>>exists_tac_2>>
    rw[]>>
    rfs[set_store_def,word_state_eq_rel_def,get_var_perm]>>
    metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
             ,domain_union,SUBSET_UNION])
  >-
    (*Store*)
    (exists_tac>>exists_tac_2>>
    rw[]>>
    rfs[set_store_def,word_state_eq_rel_def,get_var_perm]>>
    Cases_on`get_var n st`>>fs[]>>
    imp_res_tac strong_locals_rel_get_var>>
    fs[mem_store_def]>>
    EVERY_CASE_TAC>>fs[]>>
    metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
             ,domain_union,SUBSET_UNION])
  >- (*Call*)
    (fs[wEval_def,LET_THM,coloring_ok_def,get_live_def,get_vars_perm]>>
    Cases_on`get_vars l st`>>fs[]>>
    imp_res_tac strong_locals_rel_get_vars>>
    pop_assum kall_tac>>
    pop_assum mp_tac>>discharge_hyps>-
      (rw[domain_numset_list_insert]>>
      EVERY_CASE_TAC>>fs[domain_numset_list_insert,domain_union])>>
    pop_assum kall_tac>>rw[]>>
    Cases_on`find_code o1 x st.code`>>fs[word_state_eq_rel_def]>>
    Cases_on`x'`>>fs[]>>
    FULL_CASE_TAC
    >-
    (*Tail call*)
      (Cases_on`o0`>>fs[]>>
      qexists_tac`cst.permute`>>fs[]>>
      Cases_on`st.clock=0`>-fs[call_env_def]>>
      fs[]>>
      `call_env q (dec_clock cst) = 
       call_env q (dec_clock(st with permute:= cst.permute))` by
        fs[call_env_def,dec_clock_def,word_state_component_equality]>>
      rfs[]>>EVERY_CASE_TAC>>
      fs[])
    >>
    (*Returning calls*)
    PairCases_on`x'`>>fs[]>>
    Cases_on`cut_env x'1 st.locals`>>fs[]>>
    imp_res_tac cut_env_lemma>>
    pop_assum kall_tac>>
    pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
    discharge_hyps>-
      fs[strong_locals_rel_def,domain_union]>>
    discharge_hyps>-
      (fs[coloring_ok_def,LET_THM,domain_union]>>
      `domain x'1 ⊆ x'0 INSERT domain x'1` by fs[SUBSET_DEF]>>
      metis_tac[SUBSET_UNION,INJ_less,INSERT_UNION_EQ])>>
    rw[]>>fs[]>>
    Cases_on`st.clock=0`>>fs[call_env_def]>>
    `(IS_SOME (case o0 of NONE => NONE
      | SOME (v,prog) => SOME (f v,apply_color f prog))) = IS_SOME o0` by
      (EVERY_CASE_TAC>>fs[])>>
    simp[]>>
    qpat_abbrev_tac `b = IS_SOME o0`>>
    assume_tac (GEN_ALL push_env_s_val_eq)>>
    pop_assum (qspecl_then[
      `y`,`x'`,`st with clock := st.clock-1`,
      `f`,`cst with clock := st.clock-1`,`b`,`λn. cst.permute (n+1)`]
      assume_tac)>>
    rfs[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x' b
            (st with <|permute := perm; clock := st.clock − 1|>) with
          locals := fromList2 q`>>
    qpat_abbrev_tac `envy = (push_env y A B) with locals := C`>>
    assume_tac wEval_stack_swap>>
    pop_assum(qspecl_then [`r`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC>-
      (rw[]>>qexists_tac`perm`>>fs[dec_clock_def])>>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      fs[push_env_def,word_state_component_equality]>>
      fs[LET_THM,env_to_list_def,dec_clock_def])>>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>
       fs[word_state_component_equality])>>
    FULL_CASE_TAC
    >-
    (*Result*)
    (strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
    discharge_hyps>-
      (unabbrev_all_tac>>
       fs[word_state_component_equality,dec_clock_def])>>
    strip_tac>>fs[]>>
    rfs[]>>
    (*Backwards chaining*)
    fs[Abbr`envy`,Abbr`envx`,word_state_component_equality]>>
    Q.ISPECL_THEN [`(cst with clock := st.clock-1)`,
                  `r' with stack := st'`,`y`,`b`] 
                  assume_tac push_env_pop_env_s_key_eq>>
    Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                  `r'`,`x'`,`b`] 
                  assume_tac push_env_pop_env_s_key_eq>>
    rfs[]>>
    (*Now we can finally use the IH*)
    last_x_assum(qspecl_then[`x'2`,`set_var x'0 a y'`
                            ,`set_var (f x'0) a y''`,`f`,`live`]mp_tac)>>
    discharge_hyps>-size_tac>>
    fs[coloring_ok_def]>>
    discharge_hyps>-
      (fs[set_var_def,word_state_component_equality]>>
      `s_key_eq y'.stack y''.stack` by 
        metis_tac[s_key_eq_trans,s_key_eq_sym]>>
      assume_tac pop_env_frame>>rfs[word_state_eq_rel_def]>>
      fs[coloring_ok_def,LET_THM,strong_locals_rel_def]>>
      rw[]>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      fs[s_key_eq_def,s_val_eq_def]>>
      Cases_on`o0`>>Cases_on`opt`>>Cases_on`opt'`>>
      TRY(Cases_on`x''`)>>
      fs[s_frame_key_eq_def,s_frame_val_eq_def]>>
      Cases_on`n=x'0`>>
      fs[lookup_insert]>>
      `f n ≠ f x'0` by
        (imp_res_tac domain_lookup>>
        fs[domain_fromAList]>>
        (*some assumption movements to make this faster*)
        qpat_assum `INJ f (x'0 INSERT A) B` mp_tac>>
        rpt (qpat_assum `INJ f A B` kall_tac)>>
        strip_tac>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        pop_assum(qspecl_then [`n`,`x'0`] mp_tac)>>
        rw[domain_union])>>
      fs[lookup_fromAList]>>
      imp_res_tac key_map_implies>>
      rfs[]>>
      `l'' = ZIP(MAP FST l'',MAP SND l'')` by fs[ZIP_MAP_FST_SND_EQ]>>
      pop_assum SUBST1_TAC>>
      pop_assum (SUBST1_TAC o SYM)>>
      match_mp_tac ALOOKUP_key_remap_2>>
      fs[]>>CONJ_TAC>>
      metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])>>
    rw[]>>
    qpat_abbrev_tac`b =IS_SOME A`>>
    qspecl_then[`r`,`push_env x' b
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
    (*Exceptions*)
    (fs[]>>strip_tac>>
    imp_res_tac s_val_eq_LAST_N_exists>>
    first_x_assum(qspecl_then[`envy.stack`,`e'`,`ls'`] assume_tac)>>
    rfs[]>>
    Cases_on`o0`
    >-
      (*No handler*)
      (fs[]>>
      qexists_tac`perm`>>
      Cases_on`b`>>fs[]>>
      `ls=ls'` by 
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
      metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans])
    >>
      (*Handler*)
      Cases_on`x''`>>fs[]>>
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
      fs[]>>
      qpat_abbrev_tac `cr'=r' with<|locals:= A;stack:=B;handler:=C|>`>>
      (*Use the IH*)
      last_x_assum(qspecl_then[`r''`,`set_var q' w r'`
                            ,`set_var (f q') w cr'`,`f`,`live`]mp_tac)>>
      discharge_hyps>-size_tac>>
      fs[coloring_ok_def]>>
      discharge_hyps>-
      (fs[set_var_def,word_state_component_equality,Abbr`cr'`]>>
      fs[coloring_ok_def,LET_THM,strong_locals_rel_def]>>
      rw[]>-metis_tac[s_key_eq_trans,s_val_and_key_eq]>>
      Cases_on`q' = n`>>fs[lookup_insert]>>
      `f n ≠ f q'` by
        (imp_res_tac domain_lookup>>
        fs[domain_fromAList]>>
        qpat_assum `INJ f (q' INSERT A) B` mp_tac>>
        qpat_assum `INJ f A B` kall_tac>>
        `n ∈ set (MAP FST lss)` by fs[]>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        strip_tac>>pop_assum(qspecl_then [`n`,`q'`] mp_tac)>>
        rw[domain_union]>>
        metis_tac[])>>
      fs[lookup_fromAList]>>
      imp_res_tac key_map_implies>>
      rfs[]>>
      `lss' = ZIP(MAP FST lss',MAP SND lss')` by fs[ZIP_MAP_FST_SND_EQ]>>
      pop_assum SUBST1_TAC>>
      pop_assum (SUBST1_TAC o SYM)>>
      match_mp_tac ALOOKUP_key_remap_2>>
      fs[]>>CONJ_TAC>>
      metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])>>
      rw[]>>
      qspecl_then[`r`,`st with <|locals := fromList2 q;stack :=
            StackFrame (list_rearrange (perm 0)
              (QSORT key_val_compare (nub (toAList x'))))
              (SOME r'.handler)::st.stack;
            permute := (λn. perm (n + 1)); handler := LENGTH st.stack;
            clock := st.clock − 1|>`,`perm'`]
        assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      `(λn. perm'' n) = perm''` by fs[FUN_EQ_THM]>>
      `domain (fromAList lss) = domain x'1` by 
        metis_tac[domain_fromAList]>>
      fs[set_var_perm])
    >>
    (*The rest*)
    rw[]>>qexists_tac`perm`>>fs[]>>
    TRY(pop_assum(qspec_then`envy.stack` mp_tac)>>
      discharge_hyps>-
      (unabbrev_all_tac>>fs[word_state_component_equality])>>
      rw[]>>fs[]>>NO_TAC))
   >- (*Seq*)
    (rw[]>>fs[wEval_def,coloring_ok_def,LET_THM,get_live_def]>>
    last_assum(qspecl_then[`w`,`st`,`cst`,`f`,`get_live w0 live`]
      mp_tac)>>
    discharge_hyps>-size_tac>>
    rw[]>>
    Cases_on`wEval(w,st with permute:=perm')`>>fs[]
    >- (qexists_tac`perm'`>>fs[]) >>
    Cases_on`wEval(apply_color f w,cst)`>>fs[]>>
    REVERSE (Cases_on`q`)>>fs[]
    >- 
      (qexists_tac`perm'`>>rw[])
    >>
    first_assum(qspecl_then[`w0`,`r`,`r'`,`f`,`live`] mp_tac)>>
    discharge_hyps>- size_tac>>
    rw[]>>
    qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[])
  >- (*If*)
    (fs[wEval_def,coloring_ok_def,LET_THM,get_live_def]>>
    last_assum(qspecl_then[`w`,`st`,`cst`,`f`
               ,`insert n () (union (get_live w0 live) (get_live w1 live))`] 
               mp_tac)>>
    discharge_hyps>- size_tac>>
    rw[]>>
    Cases_on`wEval(w,st with permute:=perm')`>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    Cases_on`wEval(apply_color f w,cst)`>>fs[]>>
    REVERSE (Cases_on`q`)>>fs[]
    >- 
      (qexists_tac`perm'`>>rw[])
    >>
    qpat_assum `NONE = q'` (SUBST_ALL_TAC o SYM)>>
    fs[]>>
    Cases_on`get_var n r`>>fs[]
    >-
      (qexists_tac`perm'`>>rw[])
    >>
    imp_res_tac strong_locals_rel_get_var>>fs[]>>
    REVERSE (Cases_on`x`)
    >-
      (qexists_tac`perm'`>>rw[])
    >>
    Cases_on`c = 0w`>>fs[]
    >-
      (first_assum(qspecl_then[`w1`,`r`,`r'`,`f`,`live`] mp_tac)>>
      discharge_hyps>- size_tac>>
      discharge_hyps>-
        (fs[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
      rw[]>>
      qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      qexists_tac`perm'''`>>rw[get_var_perm]>>fs[])
    >>
      (first_assum(qspecl_then[`w0`,`r`,`r'`,`f`,`live`] mp_tac)>>
      discharge_hyps>- size_tac>>
      discharge_hyps>-
        (fs[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
      rw[]>>
      qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      qexists_tac`perm'''`>>rw[get_var_perm]>>fs[]))
  >- (*Alloc*)
    (
    fs[wEval_def,coloring_ok_def,get_var_perm,get_live_def]>>
    Cases_on`get_var n st`>>fs[LET_THM]>>
    imp_res_tac strong_locals_rel_get_var>>fs[]>>
    Cases_on`x`>>fs[wAlloc_def]>>
    Cases_on`cut_env s st.locals`>>fs[]>>
    `domain s ⊆ (n INSERT domain s)` by fs[SUBSET_DEF]>>
    imp_res_tac strong_locals_rel_subset>>
    imp_res_tac cut_env_lemma>>
    pop_assum mp_tac>>discharge_hyps
    >-
      (match_mp_tac (GEN_ALL INJ_less)>>metis_tac[])
    >>
    rw[]>>fs[set_store_def]>>
    assume_tac (GEN_ALL push_env_s_val_eq)>>
    pop_assum (qspecl_then[
      `y`,`x`,`st with store:= st.store |+ (AllocSize,Word c)`,
      `f`,`cst with store:= cst.store |+ (AllocSize,Word c)`,`F`,
      `cst.permute`]assume_tac)>>
    rfs[word_state_eq_rel_def]>>
    qexists_tac`perm`>>fs[]>>
    qpat_abbrev_tac `st' = push_env x F A`>>
    qpat_abbrev_tac `cst' = push_env y F B`>>
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
    `strong_locals_rel f (domain live) x''.locals y'.locals ∧
     word_state_eq_rel x'' y'` by
      (imp_res_tac wGC_s_key_eq>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      ntac 2(pop_assum mp_tac>>simp[Once s_key_eq_sym])>>
      ntac 2 strip_tac>>
      rpt (qpat_assum `s_key_eq A B` mp_tac)>>
      qpat_abbrev_tac `lsA = list_rearrange (cst.permute 0)
        (QSORT key_val_compare (nub (toAList y)))`>>
      qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (QSORT key_val_compare (nub (toAList x)))`>>
      ntac 4 strip_tac>>
      Q.ISPECL_THEN [`x'.stack`,`y'`,`t'`,`NONE:num option`
        ,`lsA`,`cst.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      discharge_hyps
      >-
        (fs[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      Q.ISPECL_THEN [`t'.stack`,`x''`,`x'`,`NONE:num option`
        ,`lsB`,`st.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      discharge_hyps
      >-
        (fs[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      rw[]
      >-
        (
        simp[]>>
        fs[strong_locals_rel_def,lookup_fromAList]>>
        `MAP SND l = MAP SND ls'` by 
          fs[s_val_eq_def,s_frame_val_eq_def]>>
        rw[]>>
        `MAP FST (MAP (λ(x,y). (f x,y)) lsB) =
         MAP f (MAP FST lsB)` by
          fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
        fs[]>>
        match_mp_tac ALOOKUP_key_remap_2>>rw[]>>
        metis_tac[s_key_eq_def,s_frame_key_eq_def,LENGTH_MAP])
      >>
        fs[word_state_eq_rel_def,pop_env_def]>>
        rfs[word_state_component_equality]>>
        metis_tac[s_val_and_key_eq,s_key_eq_sym
          ,s_val_eq_sym,s_key_eq_trans])>>
    fs[word_state_eq_rel_def]>>FULL_CASE_TAC>>fs[has_space_def]>>
    Cases_on`x'''`>>
    EVERY_CASE_TAC>>fs[call_env_def])
    >-
      (exists_tac>>
      Cases_on`get_var n st`>>fs[get_var_perm]>>
      imp_res_tac strong_locals_rel_get_var>>fs[jump_exc_def]>>
      EVERY_CASE_TAC>>fs[])
    >-
      (exists_tac>>
      Cases_on`get_var n st`>>fs[get_var_perm]>>
      imp_res_tac strong_locals_rel_get_var>>
      fs[call_env_def])
    >>
      (exists_tac>>IF_CASES_TAC>>fs[call_env_def,dec_clock_def]))

(*
EVAL ``MAP toAList ( (λx,y. (x::y)) (get_clash_sets
  (Seq (Move [1,2;3,4;5,6]) 
  (Call 
  (SOME (3,list_insert [1;3;5;7;9] [();();();();()] LN,Move[100,3])) 
  (SOME 400) 
  [7;9] 
  (SOME(4,Move [100,4])))) (insert 100 () LN)))``
*)

(*Prove that we can substitute get_clash_sets for get_live*)

(*hd element is just get_live*)
val get_clash_sets_hd = prove(
``∀prog live hd ls.
  get_clash_sets prog live = (hd,ls) ⇒ 
  get_live prog live = hd``,
  Induct>>rw[get_clash_sets_def]>>fs[LET_THM]
  >-
    (Cases_on`o'`>>fs[get_clash_sets_def,LET_THM]>>
    PairCases_on`x`>>fs[get_clash_sets_def,get_live_def]>>
    fs[LET_THM,UNCURRY]>>
    EVERY_CASE_TAC>>fs[])
  >-
    (Cases_on`get_clash_sets prog' live`>>fs[]>>
    Cases_on`get_clash_sets prog q`>>fs[]>>
    metis_tac[get_live_def])
  >>
    Cases_on`get_clash_sets prog'' live`>>
    Cases_on`get_clash_sets prog' live`>>
    Cases_on`get_clash_sets prog (insert n () (union q' q))`>>fs[]>>
    fs[get_live_def,LET_THM]>>metis_tac[])

(*The liveset passed in at the back is always satisfied*)
val get_clash_sets_tl = prove(
``∀prog live f.
  let (hd,ls) = get_clash_sets prog live in 
  EVERY (λs. INJ f (domain s) UNIV) ls ⇒ 
  INJ f (domain live) UNIV``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  fs[PULL_FORALL]>>
  rpt strip_tac>>
  Cases_on`prog`>>
  fs[coloring_ok_alt_def,LET_THM,get_clash_sets_def,get_live_def]>>
  fs[get_writes_def]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >-
    (Cases_on`o'`>>fs[UNCURRY,get_clash_sets_def,LET_THM]
    >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
    >>
    PairCases_on`x`>>fs[]>>
    first_x_assum(qspecl_then[`x2`,`live`,`f`] mp_tac)>>
    discharge_hyps >- size_tac>>rw[]>>
    fs[get_clash_sets_def,UNCURRY,LET_THM]>>
    Cases_on`o0`>>TRY (Cases_on`x`)>>fs[])
  >>
    (first_x_assum(qspecl_then[`w0`,`live`,`f`]mp_tac)>>
    discharge_hyps>-size_tac>>rw[]>>
    fs[UNCURRY]))

val coloring_ok_alt_thm = prove(
``∀f prog live.
  coloring_ok_alt f prog live 
  ⇒ 
  coloring_ok f prog live``,
  ho_match_mp_tac (fetch "-" "coloring_ok_ind")>>
  rw[]>>
  fs[get_clash_sets_def,coloring_ok_alt_def,coloring_ok_def,LET_THM]
  >- 
    (Cases_on`get_clash_sets prog' live`>>
    Cases_on`get_clash_sets prog q`>>fs[]>>
    imp_res_tac get_clash_sets_hd>>
    fs[]>>
    Q.ISPECL_THEN [`prog`,`q`,`f`] assume_tac get_clash_sets_tl>>
    rfs[LET_THM])
  >-
    (Cases_on`get_clash_sets prog'' live`>>
    Cases_on`get_clash_sets prog' live`>>
    Cases_on`get_clash_sets prog (insert num () (union q' q))`>>
    imp_res_tac get_clash_sets_hd>>
    fs[]>>
    Q.ISPECL_THEN [`prog`,`insert num () (union q' q)`,`f`]
      assume_tac get_clash_sets_tl>>
    rfs[LET_THM,domain_union]>>
    `domain q' ⊆ num INSERT domain q' ∪ domain q` by fs[SUBSET_DEF]>>
    `domain q ⊆ num INSERT domain q' ∪ domain q` by fs[SUBSET_DEF]>>
    metis_tac[INJ_SUBSET,SUBSET_DEF])
  >>
    Cases_on`h`>>fs[LET_THM]
    >-
      (Cases_on`get_clash_sets prog live`>>fs[])
    >>
    PairCases_on`x`>>fs[]>>
    Cases_on`get_clash_sets prog live`>>fs[]>>
    Cases_on`get_clash_sets x1 live`>>fs[]>>
    EVERY_CASE_TAC>>
    fs[LET_THM]>>
    Cases_on`get_clash_sets prog live`>>
    fs[UNCURRY])

val _ = export_theory();
