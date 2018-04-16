open preamble backendComputeLib sptreeTheory wordLangTheory reachabilityTheory

val _ = add_backend_compset computeLib.the_compset;

val m = Hol_pp.print_apropos;
val f = DB.find;

val _ = new_theory "word_elim";


(******************************************************** FIND LOCATIONS/REFERENCES *********************************************************)

val findWordLoc_def = Define `
    (findWordLoc (name:num, _, _) = name) 
`

val findWordRef_def = Define `
    (findWordRef (MustTerminate p) = findWordRef p) ∧
    (findWordRef (Call ret target _ handler) = union 
        (case target of | NONE => LN | SOME n => (insert n () LN))
            (union
                (case ret of | NONE => LN | SOME (_,_,ret_handler,l1,_) => insert l1 () (findWordRef (ret_handler)))
                (case handler of | NONE => LN | SOME (_,ex_handler,_,_) => findWordRef (ex_handler)))
    ) ∧
    (findWordRef (Seq p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (If _ _ _ p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (LocValue _ n) = insert n () LN) ∧  
    (findWordRef _ = LN)
`
    
val findWordRef_ind = theorem "findWordRef_ind";

val wf_findWordRef = Q.store_thm("wf_findWordRef",
    `∀ prog tree . findWordRef prog = tree ⇒ wf tree`,
    recInduct findWordRef_ind >> rw[findWordRef_def, wf_union, wf_def, wf_insert] >>
    TRY(CASE_TAC) >> rw[wf_def, wf_insert]
    >- (Cases_on `ret` >> Cases_on `handler` >> fs[wf_union, wf_def] >>
        PairCases_on `x` >> fs[] >> TRY(PairCases_on `x'`) >> fs[wf_union, wf_insert])
    >- (Cases_on `ret` >> Cases_on `handler` >> fs[wf_union, wf_insert, wf_def] >>
        PairCases_on `x'` >> fs[wf_union, wf_insert, wf_def] >> PairCases_on `x''` >> 
        fs[wf_insert, wf_union, wf_def])
);


(******************************************************** CODE ANALYSIS *********************************************************)

val analyseWordCode_def = Define`
    (analyseWordCode [] = LN:num_set num_map) ∧ 
    (analyseWordCode ((n, args, prog)::t) = insert n (findWordRef prog) (analyseWordCode t))
`

val wf_analyseWordCode = Q.store_thm("wf_analyseWordCode",
    `∀ l t . analyseWordCode l = t ⇒ wf t`,
    Induct >- (rw[analyseWordCode_def] >> rw[wf_def])
    >> Cases_on `h` >> Cases_on `r` >> rw[analyseWordCode_def] >> rw[wf_insert]
);

val lookup_analyseWordCode = Q.store_thm ("lookup_analyseWordCode",
`∀ code n arity prog. ALOOKUP code n = SOME (arity, prog) ⇒ lookup n (analyseWordCode code) = SOME (findWordRef prog)`,
    Induct >> fs[FORALL_PROD] >> fs[analyseWordCode_def] >> fs[lookup_insert] >> rw[]);


(******************************************************** CODE REMOVAL *********************************************************)

val removeWordCode_def = Define `
    removeWordCode reachable l = FILTER (\ x . IS_SOME (lookup (FST x) reachable)) l
`

val removeWordCode_thm = Q.store_thm("removeWordCode_thm",
    `∀ n reachable v l . n ∈ domain reachable ∧ MEM (n, v) l ⇒ MEM (n, v) (removeWordCode reachable l)`,
    Induct_on `l` >> rw[] >> fs[removeWordCode_def] >> fs[domain_lookup] >> Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[]
);

val removeWordCode_thm = Q.store_thm("removeWordCode_thm",
    `∀ n reachable:num_set l . ALL_DISTINCT (MAP FST l) 
    ⇒ ∀ v . (n ∈ domain reachable ∧ MEM (n, v) l ⇔ MEM (n, v) (removeWordCode reachable l))`,
    rw[] >> EQ_TAC >> rw[]
    >- (Induct_on `l` >> rw[] >> fs[removeWordCode_def] >> fs[domain_lookup] >> Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[])
    >> fs[removeWordCode_def]
    >- (Induct_on `l` >> rw[] >> fs[domain_lookup, IS_SOME_EXISTS])
    >- (fs[MEM_MAP, MEM_FILTER] >> qexists_tac `y` >> rw[])
);

val removeWordProg_def = Define `
    removeWordProg (n:num) code =
        let t = analyseWordCode code in
        let reachable = closure_spt (insert n () (LN:num_set)) t in
        removeWordCode reachable code
`


(******************************************************** REACHABILITY *********************************************************)

val analyseWordCode_reachable_thm = Q.store_thm("analyseWordCode_reachable_thm",
    `∀ (code : (ctor_id, ctor_id # α prog) alist) t start n tree. analyseWordCode code = t ∧  start = insert n () (LN:num_set) ∧ 
        domain start ⊆ domain tree ∧ tree = mk_wf_set_tree t
    ⇒ domain (closure_spt start tree) = 
        {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`,   
    rw[] >> fs[domain_insert] >> 
    qspecl_then [`mk_wf_set_tree (analyseWordCode code)`, `insert n () LN`] mp_tac closure_spt_thm >>  
    `wf_set_tree(mk_wf_set_tree (analyseWordCode code))` by metis_tac[mk_wf_set_tree_thm] >> rw[] >>
    rw[wf_insert, wf_def] 
);





val _ = export_theory();

