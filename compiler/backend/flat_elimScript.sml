open preamble backendComputeLib sptreeTheory flatLangTheory reachabilityTheory

val _ = add_backend_compset computeLib.the_compset;

val m = Hol_pp.print_apropos;
val f = DB.find;

val _ = new_theory "flat_elim";

(*********************************** HELPER FUNCTIONS ************************************)

(* TODO - make sure isHidden is just right (everything else should be safe enough) *)

val isHidden_def = Define `
    (isHidden (Fun _ _ _) = T) ∧
    (isHidden (Letrec _ _ _) = T) ∧
    (isHidden (Mat _ (Fun _ _ _) _) = T) ∧
    (isHidden (Mat _ (Letrec _ _ _) _) = T) ∧ 
    (isHidden (App _ (GlobalVarInit _) [Fun _ _ _]) = T) ∧
    (isHidden (App _ (GlobalVarInit _) [Letrec _ _ _]) = T) ∧  
    (isHidden _ = F)
`

val dest_GlobalVarInit_def = Define `
    dest_GlobalVarInit (GlobalVarInit n) = SOME n ∧ 
    dest_GlobalVarInit _ = NONE
`

val dest_GlobalVarLookup_def = Define `
    dest_GlobalVarLookup (GlobalVarLookup n) = SOME n ∧
    dest_GlobalVarLookup _ = NONE
`

val num_set_tree_union_def = Define `
    (num_set_tree_union (LN:num_set num_map) t2 = t2) ∧
    (num_set_tree_union (LS a) t =
     case t of
       | LN => LS a
       | LS b => LS (union a b)
       | BN t1 t2 => BS t1 a t2
       | BS t1 b t2 => BS t1 (union a b) t2) ∧ 
  (num_set_tree_union (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BS t1 a t2
       | BN t1' t2' => BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2')
       | BS t1' a t2' => BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')) ∧ 
  (num_set_tree_union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS b => BS t1 (union a b) t2
       | BN t1' t2' => BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')
       | BS t1' b t2' => BS (num_set_tree_union t1 t1') (union a b) (num_set_tree_union t2 t2'))
`;

val num_set_tree_union_empty = Q.store_thm("num_set_tree_union_empty",
    `∀ t1 t2 . isEmpty(num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2`,
    Induct >> rw[num_set_tree_union_def] >> CASE_TAC >> rw[num_set_tree_union_def]
);

val wf_num_set_tree_union = Q.store_thm("wf_num_set_tree_union",
    `∀ t1 t2 result . wf t1 ∧ wf t2 ∧ num_set_tree_union t1 t2 = result ⇒ wf result`,
    Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >> TRY(CASE_TAC) >>
    rw[wf_def] >> TRY(metis_tac[wf_def, num_set_tree_union_empty])
);

val domain_num_set_tree_union = Q.store_thm ("domain_num_set_tree_union",
    `∀ t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 ∪ domain t2`,
    Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
    rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >> rw[UNION_ASSOC] >> 
    rw[UNION_COMM] >> metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
);


(*********************************** GLOBAL VAR INIT/LOOKUP ***********************************)

val exp_size_map_snd = Q.store_thm("exp_size_map_snd",
    `∀ p_es . exp6_size (MAP SND p_es) ≤ exp3_size p_es`,
    Induct >> rw[exp_size_def] >> 
    Cases_on `exp6_size (MAP SND p_es) = exp3_size p_es` >> 
    `exp_size (SND h) ≤ exp5_size h` by (Cases_on `h` >> rw[exp_size_def]) >> rw[]
);

val exp_size_map_snd_snd = Q.store_thm("exp_size_map_snd_snd",
    `∀ vv_es . exp6_size (MAP (λ x . SND (SND x)) vv_es) ≤ exp1_size vv_es`,
    Induct >> rw[exp_size_def] >>
    Cases_on `exp6_size (MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
    `exp_size (SND (SND h)) ≤ exp2_size h` by 
        (Cases_on `h` >> Cases_on `r` >> rw[exp_size_def]) >> rw[]
);

(* TODO - OPTIMISE THIS, PROBABLY DOESN'T NEED SO MANY CASES *)
(* TODO - PROVE WF WITHOUT NEEDING MK_WF *)

val findLoc_def = tDefine "findLoc" `
    (findLoc (e:flatLang$exp) = case e of
        | Raise _ er => findLoc er
        | Handle _ eh p_es =>
            union (findLoc eh) (findLocL (MAP SND p_es))
        | Lit _ _ => LN:num_set
        | Con _ _ es => findLocL es
        | Var_local _ _ => LN
        | Fun _ _ ef => findLoc ef
        | App _ op es => (case (dest_GlobalVarInit op) of
            | SOME n => (insert n () (findLocL es))
            | NONE => findLocL es)
        | If _ ei1 ei2 ei3 => 
            union (findLoc ei1) (union (findLoc ei2) (findLoc ei3))
        | Mat _ em p_es => 
            union (findLoc em) (findLocL (MAP SND p_es))
        | Let _ _ el1 el2 => union (findLoc el1) (findLoc el2)
        | Letrec _ vv_es elr1 => 
            union (findLocL (MAP (SND o SND) vv_es)) (findLoc elr1)) ∧ 
    (findLocL [] = LN) ∧
    (findLocL (e::es) = union (mk_wf (findLoc e)) (findLocL es)) (* mk_wf here shouldn't be necessary *)
` 
    (
        WF_REL_TAC `measure (λ e . case e of
            | INL x => exp_size x
            | INR y => exp6_size y)` >>
        rw[exp_size_def]
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
        >- (qspec_then `p_es'` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es') = exp3_size p_es'` >>
            rw[])
        >- (qspec_then `vv_es` mp_tac exp_size_map_snd_snd >>
            Cases_on `exp6_size(MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
            rw[])
    )


val findLoc_ind = theorem "findLoc_ind";

(*
val wf_findLocL = Q.store_thm("wf_findLocL",
    `∀ l . (∀ e1. wf(findLoc e1)) ⇒ wf(findLocL l)`,
    Induct >> rw[] >> rw[Once findLoc_def, wf_def, wf_union]
);

val wf_findLoc_basic = Q.store_thm("wf_findLoc_basic",
    `∀ e . (∀ l . wf(findLocL l)) ⇒ wf(findLoc e)`,
    Induct >> rw[Once findLoc_def] >>
    TRY(CASE_TAC) >> rw[wf_union, wf_def, wf_insert]
);
*)

val wf_findLocL = Q.store_thm("wf_findLocL",
    `∀ l . wf(findLocL l)`,
    Induct >> rw[] >> rw[Once findLoc_def, wf_def, wf_union]
);

val wf_findLoc = Q.store_thm("wf_findLoc",
    `∀ e . wf(findLoc e)`,
    ASSUME_TAC wf_findLocL >>
    Induct >> rw[Once findLoc_def] >> TRY(CASE_TAC) >> rw[wf_union, wf_def, wf_insert]
);

val findLookups_def = tDefine "findLookups" `
    (findLookups e = case e of 
        | Raise _ er => findLookups er
        | Handle _ eh p_es =>
            union (findLookups eh) (findLookupsL (MAP SND p_es))
        | Lit _ _ => LN
        | Con _ _ es => findLookupsL es
        | Var_local _ _ => LN
        | Fun _ _ ef => findLookups ef
        | App _ op es => (case (dest_GlobalVarLookup op) of
            | SOME n => (insert n () (findLookupsL es))
            | NONE => findLookupsL es)
        | If _ ei1 ei2 ei3 => 
            union (findLookups ei1) (union (findLookups ei2) (findLookups ei3))
        | Mat _ em p_es => 
            union (findLookups em) (findLookupsL (MAP SND p_es))
        | Let _ _ el1 el2 => union (findLookups el1) (findLookups el2)
        | Letrec _ vv_es elr1 => 
            union (findLookupsL (MAP (SND o SND) vv_es)) (findLookups elr1)) ∧ 
        (findLookupsL [] = LN) ∧ 
        (findLookupsL (e::es) = union (findLookups e) (findLookupsL es))
`
    (
        WF_REL_TAC `measure (λ e . case e of 
                | INL x => exp_size x 
                | INR (y:flatLang$exp list) => flatLang$exp6_size y)` >> rw[exp_size_def]
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
        >- (qspec_then `p_es'` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es') = exp3_size p_es'` >>
            rw[])
        >- (qspec_then `vv_es` mp_tac exp_size_map_snd_snd >>
            Cases_on `exp6_size(MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
            rw[])
    );


(*********************************** CODE ANALYSIS ***********************************)

val analyseExp_def = Define `
    analyseExp e = let locs = (findLoc e) in let lookups = (findLookups e) in
        if (isHidden e) then (LN, map (K lookups) locs) 
        else (locs, map (K lookups) locs)
`

val wf_analyseExp = Q.store_thm("wf_analyseExp",
    `∀ e roots tree . analyseExp e = (roots, tree) ⇒ (wf roots) ∧ (wf tree)`,
    simp[analyseExp_def] >> Cases_on `isHidden e` >> rw[wf_map] >>
    rw[wf_def, wf_map, wf_findLoc]
);

val analyseExp_domain = Q.store_thm("analyseExp_domain",
   `∀ e roots tree . analyseExp e = (roots, tree) ⇒ (domain roots ⊆ domain tree)`,
    simp[analyseExp_def] >> Cases_on `isHidden e` >> rw[] >> rw[domain_def, domain_map]
);

val codeAnalysis_union_def = Define `
    codeAnalysis_union (r1, t1) (r2, t2) = ((union r1 r2), (num_set_tree_union t1 t2))
`

val wf_codeAnalysis_union = Q.store_thm("wf_codeAnalysis_union",
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2 
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`,
    rw[codeAnalysis_union_def] >> rw[wf_union]
);

val wf_codeAnalysis_union_strong = Q.store_thm("wf_codeAnalysis_union_strong",
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3. wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`,
    rw[codeAnalysis_union_def] >> rw[wf_union] >> imp_res_tac wf_num_set_tree_union >> fs[]
);

val domain_codeAnalysis_union = Q.store_thm("domain_codeAnalysis_union",
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 . domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧ 
    codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`,
    rw[codeAnalysis_union_def] >> rw[domain_union] >> rw[domain_num_set_tree_union] >>
    fs[SUBSET_DEF]
);

val analyseCode_def = Define `
    analyseCode [] = (LN, LN) ∧ 
    analyseCode ((Dlet e)::cs) = codeAnalysis_union (analyseExp e) (analyseCode cs) ∧ 
    analyseCode (_::cs) = analyseCode cs
` 

val analyseCode_thm = Q.store_thm("analyseCode_thm",
    `∀ code root tree . analyseCode code = (root, tree) 
    ⇒ (wf root) ∧ (domain root ⊆ domain tree)`,
    Induct 
    >-(rw[analyseCode_def] >> rw[wf_def])
    >> Cases_on `h` >> simp[analyseCode_def] >> Cases_on `analyseExp e` >>
       Cases_on `analyseCode code` >>
       first_x_assum (qspecl_then [`q'`, `r'`] mp_tac) >> simp[] >>
       qspecl_then [`e`, `q`, `r`] mp_tac wf_analyseExp >> simp[] >> rw[]
       >- imp_res_tac wf_codeAnalysis_union
       >> qspecl_then [`e`, `q`, `r`] mp_tac analyseExp_domain >> rw[] >> 
          imp_res_tac domain_codeAnalysis_union
);


(**************************************** CODE REMOVAL ****************************************)

val lit0_def = Define `
    lit0 n = Dlet (App None (GlobalVarInit n) [Lit None (IntLit 0)])
`
(*
val keep_def = Define `
    (keep reachable (Dlet e) = case (findLoc e) of
        | LN => T (* no global vars, skip over *)
        | locs => (if isEmpty (inter locs reachable) then F else T)) ∧ 
        (* i.e. if none of the global variables that e may assign to are in
           the reachable set, then do not keep - if any are in, then keep *)
    (keep reachable _ = T) (* not a Dlet, may be type info etc. so keep *)
`
*)

val keep_def = Define `
    (keep reachable (Dlet e) = 
        if isEmpty (inter (findLoc e) reachable) then F else T) ∧ 
        (* i.e. if none of the global variables that e may assign to are in
           the reachable set, then do not keep - if any are in, then keep *)
    (keep reachable _ = T) (* not a Dlet, may be type info etc. so keep *)
`

val keep_ind = theorem "keep_ind";

val removeUnreachable_def = Define `
    removeUnreachable reachable l = FILTER (keep reachable) l
`

val removeFlatProg_def = Define `
    removeFlatProg code =
        let (r, t) = analyseCode code in
        let reachable = closure_spt r t in
        removeUnreachable reachable code
`


(*********************************** MAKE WF_SET_TREE ***********************************)

(* TODO - USE THIS FOLD DEFINITION OF SUPERDOMAIN 

val sd_def = Define `
    sd (t:sp_graph) = (foldi (λ k v a . union v a) 0 LN) t
`

val subspt_sd = Q.store_thm("subspt_sd",
    `∀ t1 a t2 . subspt (sd t1) (sd (BS t1 a t2)) ∧  
                 subspt (sd t2) (sd (BS t1 a t2)) ∧ 
                 subspt a (sd (BS t1 a t2)) ∧ 
                 subspt (sd t1) (sd (BN t1 t2)) ∧ 
                 subspt (sd t2) (sd (BN t1 t2))`,
    
    simp[subspt_domain, sd_def]
    Induct >> Induct_on `t2` >> fs[foldi_def, domain_def, domain_union]
    metis_tac[SUBSET_TRANS, foldi_def, union_def]

    rw[foldi_def, domain_union]
    fs[foldi_def, domain_def]

*)

val superdomain_def = Define `
    superdomain LN = LN ∧ 
    superdomain (LS (t:num_set)) = t ∧ 
    superdomain (BN t1 t2) = union (superdomain t1) (superdomain t2) ∧ 
    superdomain (BS t1 a t2) = union (superdomain t1) (union a (superdomain t2))
`

val subspt_superdomain = Q.store_thm("subspt_superdomain",
    `∀ t1 a t2 . subspt (superdomain t1) (superdomain (BS t1 a t2)) ∧  
                 subspt (superdomain t2) (superdomain (BS t1 a t2)) ∧ 
                 subspt a (superdomain (BS t1 a t2)) ∧ 
                 subspt (superdomain t1) (superdomain (BN t1 t2)) ∧ 
                 subspt (superdomain t2) (superdomain (BN t1 t2))`,
    rw[subspt_domain, superdomain_def, domain_union, SUBSET_DEF]
);

val superdomain_thm = Q.store_thm("superdomain_thm",
    `∀ x y (tree:num_set num_map) . lookup x tree = SOME y ⇒ domain y ⊆ domain (superdomain tree)`,
    Induct_on `tree` >- rw[lookup_def] 
    >- rw[lookup_def, superdomain_def, foldi_def, domain_map]
    >> rw[] >> fs[lookup_def] >> Cases_on `EVEN x` >> res_tac >> 
       qspecl_then [`tree`, `a`, `tree'`] mp_tac subspt_superdomain >> 
       Cases_on `x = 0` >> fs[subspt_domain] >> metis_tac[SUBSET_TRANS]
);

val mk_wf_set_tree_def = Define `
    mk_wf_set_tree t =
        let t' = union t (map (K LN) (superdomain t)) in mk_wf (map (mk_wf) t')
`

val mk_wf_set_tree_domain = Q.store_thm("mk_wf_set_tree_domain",
    `∀ tree . domain tree ⊆ domain (mk_wf_set_tree tree)`,
    Induct >> rw[mk_wf_set_tree_def, domain_map, domain_mk_wf, domain_union, SUBSET_DEF]
);

val mk_wf_set_tree_thm = Q.store_thm("mk_wf_set_tree_thm",
    `∀ x tree . x = mk_wf_set_tree tree ⇒ wf_set_tree x`,
    rw[mk_wf_set_tree_def, wf_set_tree_def] >> fs[lookup_map] >> rw[domain_map, domain_union] >>
    fs[lookup_union] >> Cases_on `lookup x' tree` >> fs[] >- fs[lookup_map] >> rw[] >> 
    qspecl_then [`x'`, `x`, `tree`] mp_tac superdomain_thm >> rw[SUBSET_DEF]
);


(*********************************** REACHABILITY ***********************************)

val analysis_reachable_thm = Q.store_thm("analysis_reachable_thm",
   `∀ (compiled : dec list) start tree t . ((start, t) = analyseCode compiled) ∧ 
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) = {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`   
    , 
    rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >> rw[] >> 
    `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`compiled`, `start`, `t`] mp_tac analyseCode_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >> metis_tac[SUBSET_TRANS]
);

(* TODO - write syntactic condition assuming that the above property holds i.e. each Dlet binds only one global var *)

(* TODO *)


(*********************************** TESTING ***********************************)

val flat_compile_def = Define `
    flat_compile c p = 
        let (c',p) = source_to_flat$compile c p in p
`

val compile_to_flat_def = Define `compile_to_flat p = flat_compile empty_config p`;

val l = ``Locs (locn 1 2 3) (locn 1 2 3)``

val input = ``
    [Dlet ^l (* gl0 *) (Pvar "five") (Lit (IntLit 5));
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

val test_compile_def = Define `
    test_compile code = compile_to_flat code
`

val test_analyse_roots_def = Define `
    test_analyse_roots code = domain (FST (analyseCode (test_compile code)))
`

val test_analyse_tree_def = Define `
    test_analyse_tree code = toAList (SND (analyseCode (test_compile code)))
`

val test_analyse_closure_def = Define `
    test_analyse_closure code = 
        let (roots, tree) = analyseCode (test_compile code) in
        (closure_spt roots tree)
`

val test_analyse_removal_def = Define `
    test_analyse_removal code =
        let compiled = (test_compile code) in
        let (roots, tree) = analyseCode compiled in
        let reachable = (closure_spt roots tree) in
        removeUnreachable reachable compiled
`

val test_code = EVAL ``test_compile ^input``;
val test_result = EVAL ``test_analyse_removal ^input``;


(*
    Overall:
    gl0 := "five" = 5
    gl1 := "f" = λ x . gl0 = "five"
    gl2 := "g" = λ y . y
    gl3 := "foo" = λ i . (gl1 = "f") 0
    gl4 := _ = λ i . (gl5) 0
    gl5 := _ = λ i . (gl4) 0
    gl6 := "main" = (gl1 = "f") 0
[
    ***** WHAT DOES THIS DO? *****
    Dlet (Let _ NONE (App _ (GlobalVarAlloc 7) []) (Con _ NONE [])); --> what does this do?

    GL0 ***** Match 5 => "five", stored in gl0 *****
    Dlet (Mat _ (Lit _ (IntLit 5)) 
        [(Pvar "five", App _ (GlobalVarInit 0) [Var_local _ "five"])]
    );

    GL1 ****** Match (λ x . lookup gl0) => "f", stored in gl1 (gl0 contains "five" = 5) *****
    Dlet (Mat _ (Fun _ "x" (App _ (GlobalVarLookup 0) [])) 
        [(Pvar "f",  App _ (GlobalVarInit 1) [Var_local _ "f"])]
    );

    GL 2 ***** Match (λ y . y) =>  "g", stored in gl2 *****
    Dlet (Mat _ (Fun _ "y" (Var_local _ "y"))
        [(Pvar "g", App _ (GlobalVarInit 2) [Var_local _ "g"])]
    );

    GL3 ***** gl3 := (letrec "foo" = λ i . (lookup gl1) 0)   --> i.e foo = (fn i => "f" 0) *****
    Dlet (App _ (GlobalVarInit 3) 
        [Letrec _ 
            [( "foo","i", App _ Opapp [App _ (GlobalVarLookup 1) [];  Lit _ (IntLit 0)] )]
            (Var_local _ "foo")
        ]    
    );

    GL4 ***** gl4 := (λ i . (lookup gl5) 0)  --> i.e. gl4 := ("bar1" = "bar2" 0) *****
    Dlet (App _ (GlobalVarInit 4) [Fun _ "i" 
        (App _ Opapp [App _ (GlobalVarLookup 5) []; Lit _ (IntLit 0)])  
    ] );
    
    GL5 ***** gl5 := (λ i . (lookup gl4) 0)  --> i.e. gl5 := ("bar1" = "bar2" 0) *****
    Dlet (App _ (GlobalVarInit 5) [Fun _ "i"
        (App _ Opapp [App _ (GlobalVarLookup 4) []; Lit _ (IntLit 0)])
    ] );

    GL6 ***** Match ((lookup 1) 0) => "main", stored in gl6  --> i.e. "main" = "f" 0 *****
    Dlet (Mat _ (App _ Opapp [App _ (GlobalVarLookup 1) []; Lit _ (IntLit 0)])
        [( Pvar "main", App _ (GlobalVarInit 6) [Var_local _ "main"] )]
    )
]
*)

val _ = export_theory();

