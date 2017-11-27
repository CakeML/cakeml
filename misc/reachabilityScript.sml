open preamble

val m = Hol_pp.print_apropos;
val f = DB.find;
val _ = type_abbrev("num_set",``:unit spt``);
fun tzDefine s q = Lib.with_flag (computeLib.auto_import_definitions,false) (tDefine s q);


(****************************** RESULTS FROM SPTREETHEORY ******************************)

val mk_BN_thm = prove(
  ``!t1 t2. mk_BN t1 t2 =
            if isEmpty t1 /\ isEmpty t2 then LN else BN t1 t2``,
  REPEAT Cases >> EVAL_TAC);

val mk_BS_thm = prove(
  ``!t1 t2. mk_BS t1 x t2 =
            if isEmpty t1 /\ isEmpty t2 then LS x else BS t1 x t2``,
  REPEAT Cases >> EVAL_TAC);

val oddevenlemma = prove(
  ``2n * y + 1 <> 2 * x + 2``,
  disch_then (mp_tac o AP_TERM ``EVEN``) >>
  simp[EVEN_ADD, EVEN_MULT]);



(**************************************** LEMMAS ****************************************)

(********** DOMAINS **********)

val size_domain = Q.store_thm("size_domain",
    `∀ t . size t = CARD (domain t)`,
    Induct_on `t`
    >- rw[size_def, domain_def]
    >- rw[size_def, domain_def]
    >> rw[pred_setTheory.CARD_UNION_EQN, pred_setTheory.CARD_INJ_IMAGE]
    >| [
    `IMAGE (λn. 2 * n + 2) (domain t) ∩ IMAGE (λn. 2 * n + 1) (domain t') = {}`
        by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[] ,
    `(({0} ∩ IMAGE (λn. 2 * n + 2) (domain t)) = {}) /\
     (({0} UNION (IMAGE (\n. 2 * n + 2) (domain t))) 
          INTER (IMAGE (\n. 2 * n + 1) (domain t')) = {})`
    by (rw[GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >> Cases_on `ODD x`
        >> fs[ODD_EXISTS, ADD1, oddevenlemma]
           )
        >> simp[]
    ]
);

val domain_difference = Q.store_thm("domain_difference",
    `∀ t1 t2 . domain (difference t1 t2) = (domain t1) DIFF (domain t2)`,
    simp[pred_setTheory.EXTENSION, domain_lookup, lookup_difference] >>
    rw [] >> Cases_on `lookup x t1` 
    >- fs[]
    >> fs[] >> Cases_on `lookup x t2`
        >- rw[] >- rw[]
);


(********** DELETION **********)

val delete_fail = Q.store_thm ("delete_fail",
    `∀ n t . (wf t) ⇒ (n ∉  domain t <=> (delete n t = t))`,
    simp[domain_lookup] >>
    recInduct lookup_ind >>
    rw[lookup_def, wf_def, delete_def, mk_BN_thm, mk_BS_thm]
);

val size_delete = Q.store_thm ( "size_delete",
    `∀ n t . (size (delete n t) = if (lookup n t = NONE) then (size t) else (size t - 1))`,
    rw[size_def] >>
    fs[lookup_NONE_domain] >>
    TRY (qpat_assum `n NOTIN d` (qspecl_then [] mp_tac)) >>
    rfs[delete_fail, size_def] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain]
);


(********** LOOKUP **********)

val lookup_zero = Q.store_thm ( "lookup_zero", 
  `∀ n t x. (lookup n t = SOME x) ==> (size t <> 0)`,
   recInduct lookup_ind 
   \\ rw[lookup_def]    
);


(********** SUBTREES/SUBSETS **********)

val difference_sub = Q.store_thm("difference_sub",
    `(difference a b = LN) ⇒ (domain a ⊆ domain b)`,
    rw[] >>
    `(domain (difference a b) = {})` by rw[domain_def] >>
    fs[EXTENSION, domain_difference, SUBSET_DEF] >>
    metis_tac[]
);
  
val empty_sub = Q.store_thm("empty_sub",
    `isEmpty(difference a b) ∧ (subspt b a) ==> (domain a = domain b)`,
    fs[subspt_def] >>
    rw[] >>
    imp_res_tac difference_sub >>
    metis_tac[GSYM SUBSET_DEF, SUBSET_ANTISYM]
);  

val subspt_delete = Q.store_thm("subspt_delete",
    `∀ a b x . subspt a b ⇒ subspt (delete x a) b`,
    rw[subspt_def, lookup_delete]
);


(********** WELL-FORMEDNESS **********)

val wf_difference = Q.store_thm("wf_difference",
    `∀ t1 t2 . (wf t1 ∧ wf t2) ⇒ wf (difference t1 t2)`,
    Induct >> rw[difference_def, wf_def] >> CASE_TAC >> fs[wf_def] 
    >> rw[wf_def, wf_mk_BN, wf_mk_BS]
); 



(**************************************** ADJACENCY/REACHABILITY DEFINITIONS ****************************************)

val isAdjacent_def = Define `
    isAdjacent tree x y = 
    ∃ aSetx aSety. ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () ) 
        ∧ ( lookup y tree = SOME aSety )
`;

val adjacent_domain = Q.store_thm("adjacent_domain",
    `∀ tree x y . isAdjacent tree x y ⇒ x ∈ domain tree ∧ y ∈ domain tree`,
    rw[isAdjacent_def] >> rw[domain_lookup]
);

val isReachable_def = Define `
    isReachable tree = RTC (isAdjacent tree)
`;

val reachable_domain = Q.store_thm("reachable_domain",
    `∀ tree x y . isReachable tree x y ⇒ (x = y ∨ (x ∈ domain tree ∧ y ∈ domain tree))`, 
    simp[isReachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> metis_tac[adjacent_domain]
);

val rtc_isAdjacent = Q.store_thm("rtc_isAdjacent",
    `s ⊆ t ∧ (∀ k . k ∈ t ⇒ ∀ n . (isAdjacent fullTree k n ⇒ n ∈ t)) ⇒ 
    ∀ x y . RTC(isAdjacent fullTree) x y ⇒ x ∈ s ⇒ y ∈ t`,
    strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    fs[SUBSET_DEF] >>
    metis_tac []
);



(**************************************** GETONE ****************************************)

val getOne_def = Define `
    (getOne (LS ()) = 0n) ∧ 
    (getOne (BN LN t2) = 2n * (getOne t2) + 1n) ∧ 
    (getOne (BN t1 _ ) = 2n * (getOne t1) + 2n) ∧ 
    (* BN LN LN case should not occur under WF *)
    (getOne (BS _ () _) = 0n)
`;

val getOne_ind = theorem "getOne_ind";

val getOne_domain = Q.store_thm("getOne_domain",
    `∀ t . (wf t) ∧ (t ≠ LN) ⇒ (getOne t ∈ domain t)`,
    recInduct getOne_ind >> rw[getOne_def] >> fs[wf_def]
);



(**************************************** CLOSE_SPT ****************************************)

val close_spt_def = tDefine "close_spt" `
    (close_spt (reachable :num_set) (seen :num_set) tree = 
    let toLook = difference seen reachable in
    if toLook = LN then reachable else
    let index = (getOne toLook) in
    case (lookup index tree) of
        | NONE => reachable
        | SOME new => 
        close_spt (insert index () reachable) (union new seen) (delete index tree)
    )` 
    (WF_REL_TAC `measure (λ (reachable, toLook, tree) . size tree)` 
    \\ rw[size_delete, lookup_zero] 
    \\ imp_res_tac lookup_zero
    \\ fs[]);

val close_spt_ind = theorem "close_spt_ind";

val wf_close_spt = Q.store_thm("wf_close_spt",
    `∀ reachable seen tree. (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧ (∀ n x . (lookup n tree = SOME x) ⇒ wf x)
    ⇒ wf (close_spt reachable seen tree)`,
    recInduct close_spt_ind >> rw[] >> once_rewrite_tac [close_spt_def] >> rw[] >> 
    CASE_TAC >- rw[]
    >> `∀n x. lookup n (delete (getOne (difference seen reachable)) tree) = SOME x ⇒ wf x` by (
            rw[lookup_delete] >> metis_tac[] ) >>
        metis_tac [wf_insert, wf_union, wf_delete, lookup_delete]
);

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔  
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧ 
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧ 
        wf tree
`
val close_spt_thm = Q.store_thm("close_spt_thm",
    `∀ reachable seen tree fullTree x (roots:num set) . 
        (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧ (wf fullTree) ∧ 
        (∀ n x . (lookup n fullTree = SOME x) ⇒ wf x) ∧ 
        (close_spt reachable seen tree = x) ∧ 
        (subspt reachable seen) ∧ 
        (subspt tree fullTree) ∧ 
        (∀ n . n ∉ domain (reachable) ⇒ (lookup n tree = lookup n fullTree)) ∧ 
        (∀ k . k ∈ domain (seen) ⇒ (∃ n . (n ∈ roots) ∧ (isReachable fullTree n k))) ∧ 
        (∀ k . k ∈ domain (reachable) ⇒ (∀ a . (isAdjacent fullTree k a) ⇒ a ∈ domain (seen))) ∧ 
        (roots ⊆ domain (seen)) ∧ 
        (roots ⊆ domain (fullTree)) ∧ 
        (wf_set_tree fullTree)
      ⇒ (domain x = {a | ∃ n . (isReachable fullTree n a) ∧ (n ∈ roots)})`,
    recInduct close_spt_ind
    >> rw[] >> once_rewrite_tac [close_spt_def] >> simp[] 
    >> IF_CASES_TAC 
    >- (
        drule empty_sub >> fs[] >> rw[] >> fs[] >> fs[EXTENSION] >> rw[] >> EQ_TAC >> rw[] 
        >- metis_tac[]
        >> fs[SUBSET_DEF] >> fs[isReachable_def] >> `roots ⊆ domain (reachable)` by fs[SUBSET_DEF] >>
            drule rtc_isAdjacent >> impl_tac >> metis_tac[]
       )
    >> CASE_TAC >> fs[] >> fs[subspt_domain] >> rw[] >> fs[SUBSET_DEF] >> rw[EXTENSION] 
    >- (
        fs[lookup_NONE_domain] >>
        `getOne (difference seen reachable) ∈ domain (difference seen reachable)`
            by rw[wf_difference, getOne_domain] >>
        fs[domain_difference] >> res_tac >> imp_res_tac reachable_domain >>
        `n ∈ domain fullTree` by metis_tac[] >> fs[domain_lookup] >> rfs[]
       )  
    >> rfs[EXTENSION] >> pop_assum match_mp_tac >>
    `∀ n x. lookup n tree = SOME x ⇒ wf x` by (fs[subspt_def, domain_lookup] >> metis_tac[]) >>
    `getOne (difference seen reachable) ∈ domain (union x seen)` by (
        rw[domain_union, getOne_domain] >>
        `domain (difference seen reachable) ⊆ domain seen` by rw[domain_difference] >>
        `getOne(difference seen reachable)∈ domain(difference seen reachable)` 
            by rw[getOne_domain, wf_difference] >>
         fs[SUBSET_DEF] >> metis_tac [] ) >>
    `∀k. k = getOne (difference seen reachable) ∨ k ∈ domain reachable ⇒
        ∀a. isAdjacent fullTree k a ⇒ a ∈ domain (union x seen)` by (
        pop_assum kall_tac >> strip_tac >> Cases_on `k ∈ domain reachable`
        >> simp[domain_union] >> metis_tac [domain_union, isAdjacent_def, domain_lookup, SOME_11]) >>
    `∀k. k ∈ domain (union x seen) ⇒ ∃n. n ∈ roots ∧ isReachable fullTree n k` by (
        reverse(rw[domain_union] >> Cases_on `k ∈ domain seen` >> rw[])
        >- metis_tac [] 
        >> `getOne (difference seen reachable) ∈ domain seen ∧
            getOne (difference seen reachable) ∉ domain reachable` 
            by ( `getOne(difference seen reachable) ∈ domain (difference seen reachable)` 
                    by rw[wf_difference, getOne_domain] >>
                 fs[domain_difference]) >>
            res_tac >> qexists_tac `n` >> rw[isReachable_def, Once RTC_CASES2] >> disj2_tac >>
            qexists_tac `getOne (difference seen reachable)` >> rw[isAdjacent_def]
            >- metis_tac[isReachable_def] >> qexists_tac `x` >>
            res_tac >> rw[] >> fs[domain_lookup] >>
            qpat_x_assum `wf_set_tree _` assume_tac >> fs[wf_set_tree_def] >>
            qpat_x_assum `_ = SOME x` assume_tac >> qpat_x_assum `∀ x . _` kall_tac >>
            first_x_assum drule >> rw[SUBSET_DEF, domain_lookup]
      ) 
      >> asm_rewrite_tac[] >>
      simp[wf_insert, wf_difference, wf_union, wf_delete, lookup_delete, wf_close_spt,
        domain_union, subspt_delete, lookup_delete] >> 
        fs[domain_union] >> metis_tac[wf_union]
);



(**************************************** CLOSURE_SPT ****************************************)

val closure_spt_def = Define `(closure_spt start tree = close_spt LN (insert start () LN) tree)`;

val closure_spt_lemma = 
    close_spt_thm |> Q.SPECL [`LN`, `insert start () LN`, `tree`, `tree`]
        |> SIMP_RULE std_ss [
            GSYM closure_spt_def, wf_def, wf_insert, subspt_def, domain_def, NOT_IN_EMPTY,
            domain_insert, SUBSET_DEF
           ] 
        |> Q.SPECL[`{start}`]
        |> SIMP_RULE std_ss [ConseqConvTheory.AND_CLAUSES_XX, IN_SING, Once isReachable_def, RTC_REFL, AND_CLAUSES]
;


val closure_spt_thm = Q.store_thm ("closure_spt_thm",
    `(start ∈ domain tree) ∧ (wf_set_tree tree)
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . isReachable tree start a}`,
    assume_tac closure_spt_lemma >> rw[] >> fs[wf_set_tree_def] >> 
    first_x_assum match_mp_tac >> rw[]  >> fs[] >> res_tac >> fs[]
);



(*********************************************************************************************************************************************************)

(* ORIGINAL CASE 2.2 PROOF
            rfs[EXTENSION] >> pop_assum (qspecl_then [`fullTree`, `roots`] mp_tac) >> rw[] >>
            pop_assum match_mp_tac >>
            `wf (insert (getOne (difference seen reachable)) () reachable)` by rw[wf_insert, wf_difference] >>
            `∀ n x. lookup n tree = SOME x ⇒ wf x` by (
                fs[subspt_def] >> rw[domain_lookup] >>
                `lookup n fullTree = SOME x'` by fs[domain_lookup] >>
                metis_tac[]) >>
            `wf (union x seen)` by metis_tac[wf_union] >>
            `wf (delete (getOne (difference seen reachable)) tree)` by rw[wf_delete] >>
            `∀ n x n'. lookup n (delete n' tree) = SOME x ⇒ wf x` by (rw[lookup_delete] >> metis_tac[]) >>
            `wf (close_spt (insert (getOne (difference seen reachable)) () reachable) (union x seen)
                (delete (getOne (difference seen reachable)) tree))` by metis_tac[wf_close_spt] >>
            `getOne (difference seen reachable) ∈ domain (union x seen)` by (
                rw[domain_union, getOne_domain] >>
                `domain (difference seen reachable) ⊆ domain seen` by rw[domain_difference] >>
                fs[SUBSET_DEF] >>
                `getOne(difference seen reachable)∈ domain(difference seen reachable)` 
                    by rw[getOne_domain, wf_difference] >>
                metis_tac [] ) >>
            `∀x'. x' ∈ domain reachable ⇒ x' ∈ domain (union x seen)` by rw[domain_union] >>
            `subspt (delete (getOne (difference seen reachable)) tree) fullTree` by rw[subspt_delete] >>    
            `∀n . n ≠ getOne (difference seen reachable) ∧ n ∉ domain reachable ⇒
                lookup n (delete (getOne (difference seen reachable)) tree) = lookup n fullTree`
                by rw[lookup_delete] >>
            `∀k. k = getOne (difference seen reachable) ∨ k ∈ domain reachable ⇒
                     ∀a. isAdjacent fullTree k a ⇒ a ∈ domain (union x seen)` by (
                   pop_assum kall_tac >> strip_tac
                   >> Cases_on `k ∈ domain reachable`
                   >> simp[domain_union]
                   >> metis_tac [domain_union, isAdjacent_def, domain_lookup, SOME_11]
                ) >>
            
            `∀x'. x' ∈ roots ⇒ x' ∈ domain (union x seen)` by rw[domain_union] >>
            asm_rewrite_tac [] >>
            
            `∀k. k ∈ domain (union x seen) ⇒ ∃n. n ∈ roots ∧ isReachable fullTree n k` by (
                rw[domain_union] >> Cases_on `k ∈ domain seen` >> rw[] (* reverse (rw[]) *)
                >| [
                    rw[] >>
                    `getOne (difference seen reachable) ∈ domain seen` by ( 
                        `getOne(difference seen reachable) ∈ domain (difference seen reachable)` 
                            by rw[wf_difference, getOne_domain] >>
                        fs[domain_difference]
                    ) >>
                    res_tac >> qexists_tac `n` >> rw[] >> rw[isReachable_def, Once RTC_CASES2] >> disj2_tac >>
                    qexists_tac `getOne (difference seen reachable)` >> rw[isAdjacent_def]
                    >- metis_tac[isReachable_def] >> qexists_tac `x` >>
                    `getOne (difference seen reachable) ∉ domain reachable` by (
                        `getOne (difference seen reachable) ∈ domain (difference seen reachable)` 
                            by rw[wf_difference, getOne_domain] >>
                        fs[domain_difference]
                    ) >>
                    res_tac >> rw[] >> fs[domain_lookup] >>
                    qpat_x_assum `wf_set_tree _` assume_tac >>
                    fs[wf_set_tree_def] >>
                    qpat_x_assum `_ = SOME x` assume_tac >>
                    first_x_assum drule >>
                    rw[SUBSET_DEF, domain_lookup]
                    ,
                    metis_tac[]
                   ]
            ) >>        
             metis_tac[]
*)


(* TRICOLOUR
val white_def = Define `
    white (reachable :num_set) (seen :num_set) (tree :num_set spt) = 
        difference (difference tree seen) reachable
`;

val grey_def = Define `
    grey (reachable :num_set) (seen :num_set) (tree :num_set spt) = difference seen reachable
`;

val black_def = Define `
    black (reachable :num_set) (seen :num_set) (tree :num_set spt) = reachable
`;

val tricolour_disjoint = Q.store_thm("tricolour_disjoint",
    `∀ reachable seen tree .
        (domain (white reachable seen tree) ∩ domain (grey reachable seen tree) = {}) ∧
        (domain (white reachable seen tree) ∩ domain (black reachable seen tree) = {}) ∧
        (domain (grey reachable seen tree) ∩ domain (black reachable seen tree) = {})`,
        rw[white_def, grey_def, black_def, domain_difference]
        >> rw[pred_setTheory.DIFF_DEF, 
            GSYM pred_setTheory.DISJOINT_DEF, pred_setTheory.IN_DISJOINT]
        >| [
            Cases_on `x ∈ domain seen` >> rw[] >> rw[] ,
            Cases_on `x ∈ domain reachable` >> rw[] >> rw[] ,
            Cases_on `x ∈ domain reachable` >> rw[] >> rw[]
           ]
*)
