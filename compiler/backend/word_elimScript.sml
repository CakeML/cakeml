open preamble backendComputeLib sptreeTheory wordLangTheory reachabilityTheory flat_elimTheory

val _ = add_backend_compset computeLib.the_compset;

val m = Hol_pp.print_apropos;
val f = DB.find;

val _ = new_theory "word_elim";


(*********************************** GLOBAL VAR INIT/LOOKUP ***********************************)

val findWordLoc_def = Define `
    (findWordLoc (name:num, _, _) = name) 
`

(* OLD DEFINITION
val findWordRef_def = Define `
    (findWordRef (MustTerminate p) = findWordRef p) ∧
    (findWordRef (Call _ target _ _) = case target of
        | NONE => LN
        | SOME n => (insert n () LN)) ∧
    (findWordRef (Seq p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (If _ _ _ p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (LocValue n _) = insert n () LN) ∧ 
    (findWordRef _ = LN)
`
*)

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
        PairCases_on `x` >> fs[] >> PairCases_on `x'` >> fs[wf_union])
    >- (Cases_on `ret` >> Cases_on `handler` >> fs[wf_union, wf_insert, wf_def] >>
        PairCases_on `x'` >> fs[wf_union, wf_insert, wf_def] >> PairCases_on `x''` >> 
        fs[wf_insert, wf_union, wf_def])
);

(*********************************** CODE ANALYSIS ***********************************)

val analyseWordCode_def = Define`
    (analyseWordCode [] = LN:num_set num_map) ∧ 
    (analyseWordCode ((n, args, prog)::t) = insert n (findWordRef prog) (analyseWordCode t))
`

val wf_analyseWordCode = Q.store_thm("wf_analyseWordCode",
    `∀ l t . analyseWordCode l = t ⇒ wf t`,
    Induct >- (rw[analyseWordCode_def] >> rw[wf_def])
    >> Cases_on `h` >> Cases_on `r` >> rw[analyseWordCode_def] >> rw[wf_insert]
);

(**************************************** CODE REMOVAL ****************************************)

val removeWordCode_def = Define `
    removeWordCode reachable l = FILTER (\ x . IS_SOME (lookup (FST x) reachable)) l
`

val removeWordCode_thm = Q.store_thm("removeWordCode_thm",
    `∀ n reachable v l . n ∈ domain reachable ∧ MEM (n, v) l ⇒ MEM (n, v) (removeWordCode reachable l)`,
    Induct_on `l` >> rw[] >> fs[removeWordCode_def] >> fs[domain_lookup] >> Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[]
);

val removeWordProg_def = Define `
    removeWordProg (n:num) code =
        let t = analyseWordCode code in
        let reachable = closure_spt (insert n () (LN:num_set)) t in
        removeWordCode reachable code
`

(*********************************** REACHABILITY ***********************************)

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

(****************************************************************************************)
(*
val analyseWordExp_def = Define `
    analyseWordExp e = (LN:num_set, insert (findWordLoc e) (findWordRef ((SND o SND) e)) LN)
`
        
val wf_analyseWordExp = Q.store_thm("wf_analyseExp_def",
    `∀ e roots tree . analyseWordExp e = (roots, tree) ⇒ (wf roots) ∧ (wf tree)`,
    rw[analyseWordExp_def] >> rw[wf_def, wf_insert]
);

val analyseWordExp_domain = Q.store_thm("analyseExp_domain",
   `∀ e roots tree . analyseWordExp e = (roots, tree) ⇒ (domain roots ⊆ domain tree)`,
    rw[analyseWordExp_def] >> rw[domain_def]
);

val analyseWordCode_def = Define `
    analyseWordCode start [] = (insert start () LN:num_set, LN) ∧ 
    analyseWordCode start (h::t) = codeAnalysis_union (analyseWordExp h) (analyseWordCode t)
`
val analyseWordProg_def = Define `
    analyseWordProg ( program, (code :(num # 'a prog) num_map) ) =
        let start = (findWordRef program) in
        codeAnalysis_union (start, map (K (LN:num_set)) start) (analyseWordCode (toAList code))`


val analyseWordCode_thm = Q.store_thm("analyse_code_thm",
    `∀ code root tree . analyseWordCode code = (root, tree) 
    ⇒ (wf root) ∧ (wf tree) ∧ (domain root ⊆ domain tree)`,
    Induct
    >- (rw[analyseWordCode_def] >> rw[wf_def]) 
    >> Cases_on `h` >> simp[analyseWordCode_def] >> Cases_on `analyseWordExp (q,r)` >>
       Cases_on `analyseWordCode code` >> rw[] >> rfs[]
       >- (qspecl_then [`(q,r)`, `q'`, `r'`] mp_tac wf_analyseWordExp >> rw[] >>
            imp_res_tac wf_codeAnalysis_union >> fs[])
       >- (qspecl_then [`(q,r)`, `q'`, `r'`] mp_tac wf_analyseWordExp >> rw[] >>
           qspecl_then [`root'`, `q''`, `q'`, `r'`, `r''`, `tree`] mp_tac wf_codeAnalysis_union_strong >>
           fs[])
       >- (qspecl_then [`(q,r)`, `q'`, `r'`] mp_tac analyseWordExp_domain >> rw[] >> 
            imp_res_tac domain_codeAnalysis_union)
);


val analyseWordProg_thm = Q.store_thm("analyseWordProg_thm",
    `∀ program code root tree . analyseWordProg (program, code) = (root, tree)
    ⇒ wf root ∧ domain root ⊆ domain tree`,
    rw[analyseWordProg_def] >> rw[wf_codeAnalysis_union] >> Cases_on `analyseWordCode (toAList code)` >>
    imp_res_tac analyseWordCode_thm
    >- (`wf(findWordRef program)` by metis_tac[wf_findWordRef] >>
        `wf (map (K LN) (findWordRef program))` by metis_tac[wf_map] >>
        qspecl_then [`root'`, `q`, `findWordRef program`, `map (K (LN:num_set)) 
            (findWordRef program)`, `r`, `tree`]  mp_tac wf_codeAnalysis_union_strong >> fs[])
    >- (`domain (findWordRef program) = domain (map (K (LN:num_set)) (findWordRef program))` 
            by rw[domain_map] >> fs[SET_EQ_SUBSET] >> rw[domain_codeAnalysis_union] >>
        qspecl_then [`(findWordRef program)`, `q`, `root'`, `map (K LN) (findWordRef program)`, `r`, `tree`] 
            mp_tac domain_codeAnalysis_union >> fs[])
);


val keep_word_def = Define `
    keep_word reachable e = let location = (findWordLoc e) in
        if (lookup location reachable) = NONE then F else T
`

val removeUnreachable_def = Define `
    removeUnreachable reachable l = FILTER (keep_word reachable) l
`



(*********************************** REACHABILITY ***********************************)

val word_analysis_reachable_list_thm = Q.store_thm("word_analysis_reachable_list_thm",
   `∀ compiled start tree t . ((start, t) = analyseWordCode compiled) ∧ 
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) = {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`   
    , 
    rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >> rw[] >> 
    `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`compiled`, `start`] mp_tac analyseWordCode_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >> metis_tac[SUBSET_TRANS]
);

val word_analysis_reachable_code_thm = Q.store_thm("word_analysis_reachable_code_thm",
   `∀ program code start tree t . analyseWordProg (program, code) = (start, t) ∧ 
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) = {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`   
    , 
    rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >> rw[] >> 
    `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`program`, `code`, `start`] mp_tac analyseWordProg_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >> metis_tac[SUBSET_TRANS]
);

*)

(*********************************** TESTING ***********************************)


(*
open asmTheory
(*
val data_conf = 
    ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=F; has_longdiv:=T; has_fp_ops:=F;
    call_empty_ffi:=F; gc_kind:=Simple|>``;*)
val data_conf = 
    ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=F; has_longdiv:=T; has_fp_ops:=F;
    gc_kind:=Simple|>``;
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``;
val lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=x64_config;init_clock:=5|>``
val x64_config_def = Define`
   x64_config =
      <| ISA := x86_64
       ; encode := (\ x . []) (* BAD *)
       ; reg_count := 16
       ; fp_reg_count := 8
       ; avoid_regs := [4;5]
       ; link_reg := NONE
       ; two_reg_arith := T
       ; big_endian := F
       ; valid_imm := \b i. ^min32 <= i ∧ i <= ^max32
       ; addr_offset := (^min32, ^max32)
       ; byte_offset := (^min32, ^max32)
       ; jump_offset := (^min32 + 13w, ^max32 + 5w)
       ; cjump_offset := (^min32 + 13w, ^max32 + 5w)
       ; loc_offset := (^min32 + 7w, ^max32 + 7w)
       ; code_alignment := 0
       |>`

val pat_to_word_compile_def = Define `
    pat_to_word_compile p =
        let clos = pat_to_clos$compile p in
        let (clos_conf, bvl) = clos_to_bvl$compile default_config clos in
        let (s, bvi, l, n1, n2) = bvl_to_bvi$compile clos_conf.start default_config bvl in
        let data = bvi_to_data$compile_prog bvi in
        let (col, word) = 
            data_to_word$compile ^(data_conf) ^(word_to_word_conf) x64_config data in
        (col, word)
`

val destDlet_def = Define `destDlet (Dlet e) = e`;

val word_compile_def = Define `
    word_compile c p = 
        let (c', flat) = source_to_flat$compile c p in
        let pat = flat_to_pat$compile_exps [] (MAP destDlet flat) in
        (MAP pat_to_word_compile pat) 
`

val compile_to_word_def = Define `compile_to_word p = word_compile empty_config p`;

val l = ``Locs (locn 1 2 3) (locn 1 2 3)``

val input = ``
    [Dlet ^l (* gl0 *) (Pvar "five") (Lit (IntLit 5))]
     Dlet ^l (* gl1 *) (Pvar "f") (Fun "x" (Var (Short "five"))); (* f = λ x . five *)
     Dlet ^l (* gl2 *) (Pvar "g") (Fun "y" (Var (Short "y"))); (* g = λ y . y *)
     Dletrec ^l (* gl3 *) [("foo","i",App Opapp [Var (Short "f"); Lit (IntLit 0)])];
        (* foo = λ i . f 0 *) 
     Dletrec ^l 
       [("bar1","i",App Opapp [Var (Short "bar2"); Lit (IntLit 0)]); (*gl4*)
        ("bar2","i",App Opapp [Var (Short "bar1"); Lit (IntLit 0)])]; (*gl5*)
            (* bar1 = λ i . bar2 0  ∧  bar2 = λ i . bar1 0 *)
     Dlet ^l (* gl6 *) (Pvar "main") (App Opapp [Var (Short "f"); Lit (IntLit 0)])]
        (* main = f 0 *)
``

EVAL ``compile_to_word ^input``
*)
(*

val test_compile_def = Define `
    test_compile code = compile_to_word code
`

val test_analyse_roots_def = Define `
    test_analyse_roots code = domain (FST (analyseCode (my_compile code)))
`

val test_analyse_tree_def = Define `
    test_analyse_tree code = toAList (SND (analyseCode (my_compile code)))
`

val test_analyse_closure_def = Define `
    test_analyse_closure code = 
        let (roots, tree) = analyseCode (my_compile code) in
        (closure_spt roots tree)
`

val test_analyse_removal_def = Define `
    test_analyse_removal code =
        let compiled = (my_compile code) in
        let (roots, tree) = analyseCode compiled in
        let reachable = (closure_spt roots tree) in
        removeUnreachable reachable compiled
`

val test_code = EVAL ``test_compile ^input``;
val test_result = EVAL ``test_analyse_removal ^input``;

*)
val _ = export_theory();

