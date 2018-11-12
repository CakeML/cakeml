open preamble sptreeTheory flatLangTheory flat_elimTheory
     flatSemTheory flatPropsTheory

val _ = new_theory "flat_elimProof";

val grammar_ancestry =
  ["flat_elim", "flatSem", "flatLang", "flatProps",
    "misc", "ffi", "sptree"];

val _ = set_grammar_ancestry grammar_ancestry;

(* BEGIN TODO: move to sptreeTheory *)

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

val num_set_domain_eq = Q.store_thm("num_set_domain_eq",
    `∀ t1 t2:num_set . wf t1 ∧ wf t2 ⇒
        (domain t1 = domain t2 ⇔ t1 = t2)`,
    rw[] >> EQ_TAC >> rw[spt_eq_thm] >> fs[EXTENSION, domain_lookup] >>
    pop_assum (qspec_then `n` mp_tac) >> strip_tac >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[]
);

val union_num_set_sym = Q.store_thm ("union_num_set_sym",
    `∀ t1:num_set t2 . union t1 t2 = union t2 t1`,
    Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]
);

val mk_wf_union = Q.store_thm("mk_wf_union",
    `∀ t1 t2 . mk_wf (union t1 t2) = union (mk_wf t1) (mk_wf t2)`,
    rw[] >> `wf(union (mk_wf t1) (mk_wf t2)) ∧ wf(mk_wf (union t1 t2))` by
        metis_tac[wf_mk_wf, wf_union] >>
    rw[spt_eq_thm] >> fs[lookup_union, lookup_mk_wf]
);

val domain_difference = Q.store_thm("domain_difference",
    `∀ t1 t2 . domain (difference t1 t2) = (domain t1) DIFF (domain t2)`,
    simp[pred_setTheory.EXTENSION, domain_lookup, lookup_difference] >>
    rw [] >> Cases_on `lookup x t1`
    >- fs[]
    >> fs[] >> Cases_on `lookup x t2`
        >- rw[] >- rw[]
);

val difference_sub = Q.store_thm("difference_sub",
    `(difference a b = LN) ⇒ (domain a ⊆ domain b)`,
    rw[] >>
    `(domain (difference a b) = {})` by rw[domain_def] >>
    fs[EXTENSION, domain_difference, SUBSET_DEF] >>
    metis_tac[]
);

val wf_difference = Q.store_thm("wf_difference",
    `∀ t1 t2 . (wf t1 ∧ wf t2) ⇒ wf (difference t1 t2)`,
    Induct >> rw[difference_def, wf_def] >> CASE_TAC >> fs[wf_def]
    >> rw[wf_def, wf_mk_BN, wf_mk_BS]
);

val delete_fail = Q.store_thm ("delete_fail",
    `∀ n t . (wf t) ⇒ (n ∉  domain t ⇔ (delete n t = t))`,
    simp[domain_lookup] >>
    recInduct lookup_ind >>
    rw[lookup_def, wf_def, delete_def, mk_BN_thm, mk_BS_thm]
);

val size_delete = Q.store_thm ( "size_delete",
    `∀ n t . (size (delete n t) =
        if (lookup n t = NONE) then (size t) else (size t - 1))`,
    rw[size_def] >>
    fs[lookup_NONE_domain] >>
    TRY (qpat_assum `n NOTIN d` (qspecl_then [] mp_tac)) >>
    rfs[delete_fail, size_def] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain] >>
    fs[lookup_NONE_domain] >>
    fs[size_domain]
);

val lookup_zero = Q.store_thm ( "lookup_zero",
  `∀ n t x. (lookup n t = SOME x) ==> (size t <> 0)`,
   recInduct lookup_ind
   \\ rw[lookup_def]
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

val inter_union_empty = Q.store_thm("inter_union_empty",
    `∀ a b c . isEmpty (inter (union a b) c)
  ⇔ isEmpty (inter a c) ∧ isEmpty (inter b c)`,
    rw[] >> EQ_TAC >> rw[] >>
    `wf (inter (union a b) c) ∧ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >>
    TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> EVERY_CASE_TAC >> fs[]
);

val inter_insert_empty = Q.store_thm("inter_insert_empty",
    `∀ n t1 t2 . isEmpty (inter (insert n () t1) t2)
  ⇒ n ∉ domain t2 ∧ isEmpty(inter t1 t2)`,
    rw[] >>
    `∀ k . lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def]
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >>
        pop_assum (qspec_then `n` mp_tac) >>
        rw[] >> fs[] >> EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >>
        fs[EXTENSION] >> rw[] >>
        pop_assum (qspec_then `x` mp_tac) >> rw[] >>
        first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >>
        Cases_on `x = n` >> fs[] >>
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
);

val fromList2_value = Q.store_thm("fromList2_value",
    `∀ e l t n . MEM e l ⇔  ∃ n . lookup n (fromList2 l) = SOME e`,
    rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >>
        rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
);

val wf_spt_fold_tree = Q.store_thm("wf_spt_fold_tree",
    `∀ tree : num_set num_map y : num_set.
        wf tree ∧ (∀ n x . (lookup n tree = SOME x) ⇒ wf x) ∧ wf y
      ⇒ wf(spt_fold union y tree)`,
    Induct >> rw[] >> fs[spt_fold_def]
    >- (fs[wf_def] >> metis_tac[lookup_def, wf_union])
    >> `wf(spt_fold union y tree)` by (
            last_x_assum match_mp_tac >>
            fs[] >> rw[]
            >- fs[wf_def]
            >> last_x_assum match_mp_tac >>
               qexists_tac `2 * n + 2` >>
               fs[lookup_def] >> fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >> (last_x_assum match_mp_tac >> fs[] >> rw[]
        >-  fs[wf_def]
        >- (last_x_assum match_mp_tac >>
            qexists_tac `2 * n + 1` >> fs[lookup_def, EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
        >>  `wf a` by (last_x_assum match_mp_tac >>
                qexists_tac `0` >> fs[lookup_def]) >>
            fs[wf_union])
);

val lookup_spt_fold_union = Q.store_thm("lookup_spt_fold_union",
    `∀ tree : num_set num_map y : num_set n : num .
        lookup n (spt_fold union y tree) = SOME ()
      ⇒ lookup n y = SOME () ∨
        ∃ n1 s . lookup n1 tree = SOME s ∧ lookup n s = SOME ()`,
    Induct >> rw[]
    >-  fs[spt_fold_def]
    >-  (fs[spt_fold_def, lookup_union] >> EVERY_CASE_TAC >>
        fs[] >>
        DISJ2_TAC >>
        qexists_tac `0` >> qexists_tac `a` >> fs[lookup_def])
    >- (
        fs[spt_fold_def] >>
        res_tac
        >- (
            res_tac >> fs[]
            >- (
               DISJ2_TAC >>
               fs[lookup_def] >>
               qexists_tac `n1 * 2 + 2` >> qexists_tac `s` >>
               fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >>
               fs[DIV_MULT]
               )
            >- (
               DISJ2_TAC >>
               fs[lookup_def] >>
               qexists_tac `n1' * 2 + 2` >> qexists_tac `s'` >>
               fs[EVEN_DOUBLE, EVEN_ADD] >>
               once_rewrite_tac[MULT_COMM] >>
               fs[DIV_MULT]
               )
            )
        >- (
            res_tac >> fs[] >>
            DISJ2_TAC >>
            fs[lookup_def] >>
            qexists_tac `2 * n1 + 1` >> qexists_tac `s` >>
            fs[EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >>
            fs[MULT_DIV]
            )
        )
    >- (
        fs[spt_fold_def] >>
        res_tac
        >- (
            fs[lookup_union] >>
            EVERY_CASE_TAC
            >- (
                res_tac >> fs[]
                >- (
                   DISJ2_TAC >>
                   fs[lookup_def] >>
                   qexists_tac `n1 * 2 + 2` >> qexists_tac `s` >>
                   fs[EVEN_DOUBLE, EVEN_ADD] >>
                   once_rewrite_tac[MULT_COMM] >>
                   fs[DIV_MULT]
                   )
                >- (
                   DISJ2_TAC >>
                   fs[lookup_def] >>
                   qexists_tac `n1' * 2 + 2` >> qexists_tac `s'` >>
                   fs[EVEN_DOUBLE, EVEN_ADD] >>
                   once_rewrite_tac[MULT_COMM] >>
                   fs[DIV_MULT]
                   )
                )
            >- (
                DISJ2_TAC >>
                qexists_tac `0` >> qexists_tac `a` >>
                fs[lookup_def]
                )
            )
        >- (
            DISJ2_TAC >>
            fs[lookup_def] >>
            qexists_tac `2 * n1 + 1` >> qexists_tac `s` >>
            fs[EVEN_DOUBLE, EVEN_ADD] >>
            once_rewrite_tac[MULT_COMM] >>
            fs[MULT_DIV]
            )
    )
);

val lookup_spt_fold_union_STRONG = Q.store_thm("lookup_spt_fold_union_STRONG",
    `∀ tree : num_set num_map y : num_set n : num .
        lookup n (spt_fold union y tree) = SOME ()
      <=> lookup n y = SOME () ∨
        ∃ n1 s . lookup n1 tree = SOME s ∧ lookup n s = SOME ()`,
    Induct >> rw[] >> EQ_TAC >> fs[lookup_spt_fold_union] >> rw[] >>
    fs[spt_fold_def, lookup_def, lookup_union]
    >- (EVERY_CASE_TAC >> fs[])
    >- (EVERY_CASE_TAC >> fs[]
        >- (DISJ1_TAC >> DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        >- (DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        )
    >- (EVERY_CASE_TAC >> fs[])
    >- (EVERY_CASE_TAC >> fs[]
        >- (rw[] >> fs[NOT_NONE_SOME])
        >- (DISJ1_TAC >> DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        >- (DISJ2_TAC >>
            qexists_tac `(n1 - 1) DIV 2` >> qexists_tac `s` >> fs[])
        )
);

val subspt_domain_spt_fold_union = Q.store_thm("subspt_domain_spt_fold_union",
    `∀ t1 : num_set num_map t2 y : num_set .
        subspt t1 t2
      ⇒ domain (spt_fold union y t1) ⊆ domain (spt_fold union y t2)`,
    rw[SUBSET_DEF] >> fs[domain_lookup] >>
    qspecl_then [`t1`, `y`] mp_tac lookup_spt_fold_union_STRONG >>
    qspecl_then [`t2`, `y`] mp_tac lookup_spt_fold_union_STRONG >>
    ntac 2 strip_tac >> res_tac
    >- metis_tac[]
    >> ntac 2 (first_x_assum kall_tac) >>
       `lookup n1 t2 = SOME s` by fs[subspt_def, domain_lookup] >>
       metis_tac[]
);

val domain_spt_fold_union = Q.store_thm("domain_spt_fold_union",
    `∀ tree : num_set num_map y : num_set .
        (∀ k v . lookup k tree = SOME v ⇒ domain v ⊆ domain tree)
      ⇒ domain (spt_fold union y tree) ⊆ domain y ∪ domain tree`,
    rw[] >> qspec_then `tree` mp_tac lookup_spt_fold_union >>
    rw[] >> fs[SUBSET_DEF, domain_lookup] >> rw[] >> res_tac >> fs[] >>
    metis_tac[]
);

val domain_spt_fold_union_LN = Q.store_thm("domain_spt_fold_union_LN",
    `∀ tree : num_set num_map  .
        (∀ k v . lookup k tree = SOME v ⇒ domain v ⊆ domain tree)
      ⇔ domain (spt_fold union LN tree) ⊆ domain tree`,
    rw[] >> EQ_TAC >> rw[]
    >- (drule domain_spt_fold_union >>
        strip_tac >> first_x_assum (qspec_then `LN` mp_tac) >> fs[])
    >- (qspec_then `tree` mp_tac lookup_spt_fold_union_STRONG >>
        rw[] >> fs[SUBSET_DEF, domain_lookup, lookup_def] >> rw[] >>
        metis_tac[])
);

(* END TODO *)

(*****************************************************************************)



(**************************** ANALYSIS LEMMAS *****************************)

val isPure_EVERY_aconv = Q.store_thm ("isPure_EVERY_aconv",
    `∀ es . EVERY (λ a . isPure a) es = EVERY isPure es`,
    Induct >> fs[]
);

val wf_findLoc_wf_findLocL = Q.store_thm ("wf_findLoc_wf_findLocL",
    `(∀ e locs . findLoc  e = locs ⇒ wf locs) ∧
    (∀ l locs . findLocL l = locs ⇒ wf locs)`,
    ho_match_mp_tac findLoc_ind >> rw[findLoc_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarInit op` >> fs[wf_insert]
);

val wf_findLocL = Q.store_thm("wf_findLocL",
    `∀ l . wf(findLocL l)`,
    metis_tac[wf_findLoc_wf_findLocL]
);

val wf_findLoc = Q.store_thm("wf_findLoc",
    `∀ e . wf(findLoc e)`,
    metis_tac[wf_findLoc_wf_findLocL]
);

val wf_findLookups_wf_findLookupsL = Q.store_thm (
    "wf_findLookups_wf_findLookupsL",
    `(∀ e lookups . findLookups e = lookups ⇒ wf lookups) ∧
    (∀ l lookups . findLookupsL l = lookups ⇒ wf lookups)`,
    ho_match_mp_tac findLookups_ind >>
    rw[findLookups_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarLookup op` >> fs[wf_insert]
);

val wf_findLookupsL = Q.store_thm("wf_findLookupsL",
    `∀ l . wf(findLookupsL l)`,
    metis_tac[wf_findLookups_wf_findLookupsL]
);

val wf_findLookups = Q.store_thm("wf_findLookups",
    `∀ e . wf(findLookups e)`,
    metis_tac[wf_findLookups_wf_findLookupsL]
);

val findLookupsL_MEM = Q.store_thm("findLookupsL_MEM",
    `∀ e es . MEM e es ⇒ domain (findLookups e) ⊆ domain (findLookupsL es)`,
    Induct_on `es` >> rw[] >> fs[findLookups_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
);

val findLookupsL_APPEND = Q.store_thm("findLookupsL_APPEND",
    `∀ l1 l2 . findLookupsL (l1 ++ l2) =
        union (findLookupsL l1) (findLookupsL l2)`,
    Induct >> fs[findLookups_def] >> fs[union_assoc]
);

val findLookupsL_REVERSE = Q.store_thm("findLookupsL_REVERSE",
    `∀ l . findLookupsL l = findLookupsL (REVERSE l)`,
    Induct >> fs[findLookups_def] >>
    fs[findLookupsL_APPEND, findLookups_def, union_num_set_sym]
);

val findLoc_EVERY_isEmpty = Q.store_thm("findLoc_EVERY_isEmpty",
    `∀ l reachable:num_set .
        EVERY (λ e . isEmpty (inter (findLoc e) reachable)) l
      ⇔ isEmpty (inter (findLocL l) reachable)`,
    Induct >- fs[Once findLoc_def, inter_def]
    >> fs[EVERY_DEF] >> rw[] >> EQ_TAC >> rw[] >>
       qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
       fs[inter_union_empty]
);

val wf_analyseExp = Q.store_thm("wf_analyseExp",
    `∀ e roots tree . analyseExp e = (roots, tree) ⇒ (wf roots) ∧ (wf tree)`,
    simp[analyseExp_def] >> rw[] >>
    metis_tac[
        wf_def, wf_map, wf_union, wf_findLoc, wf_findLookups_wf_findLookupsL]
);

val analyseExp_domain = Q.store_thm("analyseExp_domain",
    `∀ e roots tree . analyseExp e = (roots, tree)
  ⇒ (domain roots ⊆ domain tree)`,
    simp[analyseExp_def] >> rw[] >> rw[domain_def, domain_map]
);




(**************************** ELIMINATION LEMMAS *****************************)

val keep_Dlet = Q.store_thm("keep_Dlet",
    `∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x`,
   Cases_on `h` >> rw[keep_def]
);

val num_set_tree_union_empty = Q.store_thm("num_set_tree_union_empty",
    `∀ t1 t2 . isEmpty(num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2`,
    Induct >> rw[num_set_tree_union_def] >> CASE_TAC >>
    rw[num_set_tree_union_def]
);

val wf_num_set_tree_union = Q.store_thm("wf_num_set_tree_union",
    `∀ t1 t2 result . wf t1 ∧ wf t2 ∧ num_set_tree_union t1 t2 = result
  ⇒ wf result`,
    Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >>
    TRY(CASE_TAC) >>
    rw[wf_def] >>
    TRY(metis_tac[wf_def, num_set_tree_union_empty])
);

val domain_num_set_tree_union = Q.store_thm ("domain_num_set_tree_union",
    `∀ t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 ∪ domain t2`,
    Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
    rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
);

val num_set_tree_union_sym = Q.store_thm("num_set_tree_union_sym",
    `∀ (t1 : num_set num_map) t2 .
        num_set_tree_union t1 t2 = num_set_tree_union t2 t1`,
    Induct >> rw[num_set_tree_union_def] >>
    Cases_on `t2` >> fs[num_set_tree_union_def] >>
    fs[union_num_set_sym]
);

val lookup_domain_num_set_tree_union = Q.store_thm(
    "lookup_domain_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 x . lookup n t1 = SOME x
  ⇒ ∃ y . lookup n (num_set_tree_union t1 t2) = SOME y ∧ domain x ⊆ domain y`,
    Induct_on `t1` >> rw[]
    >- fs[lookup_def]
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >> Cases_on `EVEN n` >> fs[])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >>
        Cases_on `n = 0` >> fs[domain_union] >> Cases_on `EVEN n` >> fs[])
);

val lookup_NONE_num_set_tree_union = Q.store_thm (
    "lookup_NONE_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 . lookup n t1 = NONE
    ⇒ lookup n (num_set_tree_union t1 t2) = lookup n t2`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >> Cases_on `n = 0` >> fs[] >>
    Cases_on `EVEN n` >> fs[]
);

val lookup_SOME_SOME_num_set_tree_union = Q.store_thm (
    "lookup_SOME_SOME_num_set_tree_union",
    `∀ n (t1:num_set num_map) x1 t2 x2 .
    lookup n t1 = SOME x1 ∧ lookup n t2 = SOME x2
  ⇒ lookup n (num_set_tree_union t1 t2) = SOME (union x1 x2)`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >>
    Cases_on `EVEN n` >> fs[] >>
    Cases_on `n = 0` >> fs[]
);

val lookup_num_set_tree_union = Q.store_thm("lookup_num_set_tree_union",
    `∀ (t1 : num_set num_map) t2 n .
        lookup n (num_set_tree_union t1 t2) = case (lookup n t1) of
            | NONE => lookup n t2
            | SOME s1 => case (lookup n t2) of
                | NONE => SOME s1
                | SOME s2 => SOME (union s1 s2)`,
    rw[] >> Cases_on `lookup n t1` >> fs[]
    >-  fs[lookup_NONE_num_set_tree_union]
    >- (Cases_on `lookup n t2` >> fs[]
        >- (fs[lookup_NONE_num_set_tree_union, num_set_tree_union_sym] >>
            imp_res_tac lookup_NONE_num_set_tree_union >>
            pop_assum (qspec_then `t1` mp_tac) >> rw[] >>
            fs[num_set_tree_union_sym])
        >-  fs[lookup_SOME_SOME_num_set_tree_union])
);

val wf_codeAnalysis_union = Q.store_thm("wf_codeAnalysis_union",
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`,
    rw[codeAnalysis_union_def] >> rw[wf_union]
);

val wf_codeAnalysis_union_strong = Q.store_thm("wf_codeAnalysis_union_strong",
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`,
    rw[codeAnalysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
);

val domain_codeAnalysis_union = Q.store_thm("domain_codeAnalysis_union",
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`,
    rw[codeAnalysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
);

val wf_codeAnalysis_union = Q.store_thm("wf_codeAnalysis_union",
    `∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3`,
    rw[codeAnalysis_union_def] >> rw[wf_union]
);

val wf_codeAnalysis_union_strong = Q.store_thm("wf_codeAnalysis_union_strong",
    `∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3`,
    rw[codeAnalysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
);

val domain_codeAnalysis_union = Q.store_thm("domain_codeAnalysis_union",
    `∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    codeAnalysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3`,
    rw[codeAnalysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
);

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



(**************************** REACHABILITY LEMMAS *****************************)

val subspt_superdomain = Q.store_thm("subspt_superdomain",
    `∀ t1 a t2 . subspt (superdomain t1) (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t2) (superdomain (BS t1 a t2)) ∧
                 subspt a (superdomain (BS t1 a t2)) ∧
                 subspt (superdomain t1) (superdomain (BN t1 t2)) ∧
                 subspt (superdomain t2) (superdomain (BN t1 t2))`,
    rw[subspt_domain, superdomain_def, domain_union, SUBSET_DEF]
);

val superdomain_thm = Q.store_thm("superdomain_thm",
    `∀ x y (tree:num_set num_map) . lookup x tree = SOME y
  ⇒ domain y ⊆ domain (superdomain tree)`,
    Induct_on `tree` >- rw[lookup_def]
    >- rw[lookup_def, superdomain_def, foldi_def, domain_map]
    >> rw[] >> fs[lookup_def] >> Cases_on `EVEN x` >> res_tac >>
       qspecl_then [`tree`, `a`, `tree'`] mp_tac subspt_superdomain >>
       Cases_on `x = 0` >> fs[subspt_domain] >> metis_tac[SUBSET_TRANS]
);

val superdomain_inverse_thm = Q.store_thm("superdomain_inverse_thm",
    `∀ n tree . n ∈ domain (superdomain tree)
    ⇒ ∃ k aSet . lookup k tree = SOME aSet ∧ n ∈ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >>
    fs[lookup_def, domain_union] >> res_tac
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `0` >> fs[])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
        once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
);

val superdomain_not_in_thm = Q.store_thm("superdomain_not_in_thm",
    `∀ n tree . n ∉ domain (superdomain tree)
  ⇒ ∀ k aSet . lookup k tree = SOME aSet ⇒ n ∉ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >>
    res_tac >> Cases_on `k = 0` >> Cases_on `EVEN k` >> fs[] >> metis_tac[]
);

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

val mk_wf_set_tree_domain = Q.store_thm("mk_wf_set_tree_domain",
    `∀ tree . domain tree ⊆ domain (mk_wf_set_tree tree)`,
    Induct >>
    rw[mk_wf_set_tree_def, domain_map, domain_mk_wf, domain_union, SUBSET_DEF]
);

val mk_wf_set_tree_thm = Q.store_thm("mk_wf_set_tree_thm",
    `∀ x tree . x = mk_wf_set_tree tree ⇒ wf_set_tree x`,
    rw[mk_wf_set_tree_def, wf_set_tree_def] >> fs[lookup_map] >>
    rw[domain_map, domain_union] >> fs[lookup_union] >>
    Cases_on `lookup x' tree` >> fs[] >- fs[lookup_map] >> rw[] >>
    qspecl_then [`x'`, `x`, `tree`] mp_tac superdomain_thm >> rw[SUBSET_DEF]
);

val lookup_mk_wf_set_tree = Q.store_thm("lookup_mk_wf_set_tree",
    `∀ n tree x . lookup n tree = SOME x
  ⇒ ∃ y . lookup n (mk_wf_set_tree tree) = SOME y ∧ domain x = domain y`,
    rw[mk_wf_set_tree_def] >> rw[lookup_map] >> rw[lookup_union]
);

val lookup_domain_mk_wf_set_tree = Q.store_thm("lookup_domain_mk_wf_set_tree",
    `∀ n t x y . lookup n (mk_wf_set_tree t) = SOME x ⇒
        lookup n t = SOME y ⇒ domain y = domain x`,
    rw[mk_wf_set_tree_def] >> fs[lookup_map, lookup_union] >>
    metis_tac[domain_mk_wf]
);

val wf_close_spt = Q.store_thm("wf_close_spt",
    `∀ reachable seen tree. (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧
        (∀ n x . (lookup n tree = SOME x) ⇒ wf x)
  ⇒ wf (close_spt reachable seen tree)`,
    recInduct close_spt_ind >> rw[] >>
    once_rewrite_tac [close_spt_def] >> rw[] >>
    fs[] >>
    last_x_assum match_mp_tac >>
    reverse(rw[]) >> fs[wf_union, wf_difference]
    >-  metis_tac[]
    >>  match_mp_tac wf_union >>
        fs[] >>
        match_mp_tac wf_spt_fold_tree >>
        fs[wf_def] >>
        fs[lookup_inter] >>
        rw[] >> EVERY_CASE_TAC >> fs[] >> rveq >>
        metis_tac[]
);



(**************************** OTHER LEMMAS *****************************)

val domain_superdomain_num_set_tree_union = Q.store_thm(
    "domain_superdomain_num_set_tree_union",
    `∀ t1 t2 . domain (superdomain t1)
        ⊆ domain (superdomain (num_set_tree_union t1 t2))`,
    fs[SUBSET_DEF] >> rw[] >> imp_res_tac superdomain_inverse_thm >>
    imp_res_tac lookup_domain_num_set_tree_union >>
    pop_assum (qspec_then `t2` mp_tac) >>
    rw[] >> imp_res_tac superdomain_thm >> metis_tac[SUBSET_DEF]
);

val domain_superdomain_num_set_tree_union_STRONG = Q.store_thm(
    "domain_superdomain_num_set_tree_union_STRONG",
    `∀ t1 t2 . domain (superdomain t1) ∪ domain (superdomain t2) =
        domain (superdomain (num_set_tree_union t1 t2))`,
    fs[EXTENSION] >> rw[] >> EQ_TAC >> rw[]
    >- metis_tac[domain_superdomain_num_set_tree_union,
                 SUBSET_DEF, num_set_tree_union_sym]
    >- metis_tac[domain_superdomain_num_set_tree_union,
                 SUBSET_DEF, num_set_tree_union_sym]
    >- (imp_res_tac superdomain_inverse_thm >> fs[lookup_num_set_tree_union] >>
        EVERY_CASE_TAC >> fs[]
        >- (disj1_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (disj2_tac >> imp_res_tac superdomain_thm >> fs[SUBSET_DEF])
        >- (rveq >> imp_res_tac superdomain_thm >>
            fs[SUBSET_DEF, domain_union])
       )
);

val mk_wf_set_tree_num_set_tree_union = Q.store_thm(
    "mk_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 . mk_wf_set_tree (num_set_tree_union t1 t2) =
        num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2)`,
    rw[] >>
    `wf (mk_wf_set_tree (num_set_tree_union t1 t2))`
        by metis_tac[mk_wf_set_tree_thm, wf_set_tree_def] >>
    `wf (num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2))` by
        metis_tac[mk_wf_set_tree_thm, wf_set_tree_def,
                  wf_num_set_tree_union] >>
    rw[spt_eq_thm] >> simp[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >>
    fs[lookup_num_set_tree_union] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >>
    fs[OPTION_MAP_COMPOSE, mk_wf_def] >> Cases_on `lookup n t1` >>
    Cases_on `lookup n t2` >> fs[] >>
    EVERY_CASE_TAC >> fs[mk_wf_def, union_def] >>
    fs[lookup_NONE_domain, GSYM domain_lookup] >>
    qspecl_then [`t1`, `t2`] mp_tac
        domain_superdomain_num_set_tree_union_STRONG >>
    strip_tac >> fs[EXTENSION]
    >-  metis_tac[]
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >- (qsuff_tac `n ∈ domain (superdomain (num_set_tree_union t1 t2))`
        >- rw[domain_lookup]
        >> imp_res_tac domain_lookup >> metis_tac[])
    >-  metis_tac[mk_wf_union]
);



(************************** ADJACENCY/REACHABILITY ***************************)

val isAdjacent_def = Define `
    isAdjacent tree x y =
    ∃ aSetx aSety.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () ) ∧
        ( lookup y tree = SOME aSety )
`;

val adjacent_domain = Q.store_thm("adjacent_domain",
    `∀ tree x y . isAdjacent tree x y ⇒ x ∈ domain tree ∧ y ∈ domain tree`,
    rw[isAdjacent_def] >> rw[domain_lookup]
);

val isReachable_def = Define `
    isReachable tree = RTC (isAdjacent tree)
`;

val reachable_domain = Q.store_thm("reachable_domain",
    `∀ tree x y . isReachable tree x y
  ⇒ (x = y ∨ (x ∈ domain tree ∧ y ∈ domain tree))`,
    simp[isReachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    metis_tac[adjacent_domain]
);

val rtc_isAdjacent = Q.store_thm("rtc_isAdjacent",
    `s ⊆ t ∧ (∀ k . k ∈ t ⇒ ∀ n . (isAdjacent fullTree k n ⇒ n ∈ t)) ⇒
    ∀ x y . RTC(isAdjacent fullTree) x y ⇒ x ∈ s ⇒ y ∈ t`,
    strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    fs[SUBSET_DEF] >>
    metis_tac []
);

val isAdjacent_num_set_tree_union = Q.store_thm(
    "isAdjacent_num_set_tree_union",
    `∀ t1 t2 n m .
        isAdjacent t1 n m ⇒ isAdjacent (num_set_tree_union t1 t2) n m`,
    rw[isAdjacent_def] >> imp_res_tac lookup_domain_num_set_tree_union >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    fs[SUBSET_DEF, domain_lookup]
);

val isAdjacent_wf_set_tree_num_set_tree_union = Q.store_thm (
    "isAdjacent_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m .
        isAdjacent (mk_wf_set_tree t1) n m
        ⇒ isAdjacent (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    rw[isAdjacent_def] >> fs[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >> fs[PULL_EXISTS] >>
    fs[lookup_num_set_tree_union] >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[] >>
    rveq >> fs[lookup_def, mk_wf_def, lookup_union] >>
    EVERY_CASE_TAC >> fs[] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union >>
    rw[SUBSET_DEF, domain_lookup]
);

val isReachable_wf_set_tree_num_set_tree_union = Q.store_thm (
    "isReachable_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m .
        isReachable (mk_wf_set_tree t1) n m
      ⇒ isReachable (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    simp[isReachable_def] >> strip_tac >> strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
    simp[Once RTC_CASES2] >> disj2_tac >> qexists_tac `m` >> fs[] >>
    imp_res_tac isAdjacent_wf_set_tree_num_set_tree_union >> fs[]
);



(************************** DEFINITIONS ***************************)

val v_size_map_snd = Q.store_thm("exp_size_map_snd",
    `∀ vvs . v3_size (MAP SND vvs) ≤ v1_size vvs`,
    Induct >> rw[v_size_def] >>
    Cases_on `v3_size (MAP SND vvs) = v1_size vvs` >>
    `v_size (SND h) ≤ v2_size h` by (Cases_on `h` >> rw[v_size_def]) >> rw[]
);

val findVglobals_def = tDefine "findVglobals" `
    (findVglobals (Conv _ vl) = (findVglobalsL vl):num_set) ∧
    (findVglobals (Closure vvs _ e) =
        union (findVglobalsL (MAP SND vvs)) (findLookups e)) ∧
    (findVglobals (Recclosure vvs vves _) =
        union (findVglobalsL (MAP SND vvs))
            (findLookupsL (MAP (SND o SND) vves))) ∧
    (findVglobals (Vectorv vl) = findVglobalsL vl) ∧
    (findVglobals _ = LN) ∧
    (findVglobalsL [] = LN) ∧
    (findVglobalsL (h::t) = union (findVglobals h) (findVglobalsL t))
`
(
    WF_REL_TAC `measure (λ e . case e of
            | INL x => v_size x
            | INR y => v3_size y)` >>
    rw[v_size_def] >> qspec_then `vvs` mp_tac v_size_map_snd >>
    Cases_on `v3_size(MAP SND vvs) = v1_size vvs` >> rw[]
);

val findVglobals_ind = theorem "findVglobals_ind";

val findVglobalsL_APPEND = Q.store_thm("findVglobalsL_APPEND",
    `∀ l1 l2 . findVglobalsL (l1 ++ l2) =
        union (findVglobalsL l1) (findVglobalsL l2)`,
    Induct >> fs[findVglobals_def] >> fs[union_assoc]
);

val findVglobalsL_REVERSE = Q.store_thm("findVglobalsL_REVERSE",
    `∀ l . findVglobalsL l = findVglobalsL (REVERSE l)`,
    Induct >> fs[findVglobals_def] >>
    fs[findVglobalsL_APPEND, union_num_set_sym, findVglobals_def]
);

val findVglobalsL_MEM = Q.store_thm("findVglobalsL_MEM",
    `∀ k v vs . MEM (k, v) vs
  ⇒ domain (findVglobals v) ⊆ domain (findVglobalsL (MAP SND vs))`,
    Induct_on `vs` >> rw[] >> fs[findVglobals_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
);

val findVglobalsL_EL = Q.store_thm("findVglobalsL_EL",
    `∀ n vs . n < LENGTH vs ⇒
    domain (findVglobals (EL n vs)) ⊆ domain(findVglobalsL vs)`,
    Induct >> fs[EL] >> rw[] >> Cases_on `vs` >>
    fs[findVglobals_def, domain_union] >>
    Cases_on `n = 0` >> fs[] >>  fs[EXTENSION, SUBSET_DEF]
);

val findVglobals_MAP_Recclosure = Q.store_thm("findVglobals_MAP_Recclosure",
    `∀ (funs:(tvarN,tvarN # flatLang$exp) alist) v l .
        domain (findVglobalsL (MAP (λ (f,x,e). Recclosure v l f) funs)) ⊆
            domain (findVglobalsL (MAP SND v)) ∪
            domain (findLookupsL (MAP (SND o SND) l))`,
    Induct >> fs[findVglobals_def] >> rw[domain_union] >>
    PairCases_on `h` >> fs[findVglobals_def, domain_union]
);

val findVglobalsL_REPLICATE = Q.store_thm ("findVglobalsL_REPLICATE",
    `∀ n v vs . domain (findVglobalsL (REPLICATE n v)) ⊆
        domain (findVglobals v)`,
    Induct >> fs[REPLICATE, findVglobals_def, domain_union]
);

val findVglobalsL_LUPDATE = Q.store_thm ("findVglobalsL_LUPDATE",
    `∀ n vs (reachable:num_set) v . n < LENGTH vs ∧
    domain (findVglobalsL vs) ⊆ domain reachable ∧
    domain (findVglobals v) ⊆ domain reachable
  ⇒ domain (findVglobalsL (LUPDATE v n vs)) ⊆ domain reachable`,
    Induct_on `vs` >> rw[] >> Cases_on `n` >> fs[LUPDATE_def] >>
    fs[findVglobals_def, domain_union]
);

val findVglobals_v_to_list = Q.store_thm("findVglobals_v_to_list",
    `∀ x reachable xs .
        domain (findVglobals x) ⊆ domain reachable ∧ v_to_list x = SOME xs
    ⇒ domain (findVglobalsL xs) ⊆ domain reachable`,
    recInduct v_to_list_ind >>
    fs[v_to_list_def, findVglobals_def, domain_union] >> rw[] >>
    Cases_on `v_to_list v2` >> fs[] >> rveq >>
    fs[findVglobals_def, domain_union] >> metis_tac[]
);

val findVglobals_list_to_v = Q.store_thm("findVglobals_list_to_v",
    `∀ xs reachable x .
        domain (findVglobalsL xs) ⊆ domain reachable ∧ list_to_v xs = x
    ⇒ domain (findVglobals x) ⊆ domain reachable`,
    Induct >> fs[list_to_v_def, findVglobals_def, domain_union]
);

val findRefsGlobals_def = Define `
    (findRefsGlobals (Refv a::t) =
        union (findVglobals a) (findRefsGlobals t)) ∧
    (findRefsGlobals (Varray l::t) =
        union (findVglobalsL l) (findRefsGlobals t)) ∧
    (findRefsGlobals (_::t) = findRefsGlobals t) ∧
    (findRefsGlobals [] = LN)
`

val findRefsGlobals_ind = theorem "findRefsGlobals_ind";

val findRefsGlobals_EL = Q.store_thm("findRefsGlobals_EL",
    `∀ n l . n < LENGTH l ⇒
        (∀ a . EL n l = Refv a
            ⇒ domain (findVglobals a) ⊆ domain (findRefsGlobals l)) ∧
        (∀ vs . EL n l = Varray vs
            ⇒ domain (findVglobalsL vs) ⊆ domain (findRefsGlobals l))`,
    Induct >> rw[]
    >- (Cases_on `l` >> fs[findRefsGlobals_def, domain_union])
    >- (Cases_on `l` >> fs[findRefsGlobals_def, domain_union])
    >> fs[EL] >> first_x_assum (qspec_then `TL l` mp_tac) >> rw[] >>
       `n < LENGTH (TL l)` by fs[LENGTH_TL] >> fs[] >>
       Cases_on `l` >> fs[] >>
       Cases_on `h` >> fs[findRefsGlobals_def, domain_union, SUBSET_DEF]
);

val findRefsGlobals_MEM = Q.store_thm("findRefsGlobals_MEM",
    `∀ refs reachable:num_set .
        domain (findRefsGlobals refs) ⊆ domain reachable
      ⇒ (∀ a . MEM (Refv a) refs
            ⇒ domain (findVglobals a) ⊆ domain reachable) ∧
        (∀ vs . MEM (Varray vs) refs
            ⇒ domain (findVglobalsL vs) ⊆ domain reachable)`,
    Induct >> rw[] >> fs[findRefsGlobals_def, domain_union] >>
    Cases_on `h` >> fs[findRefsGlobals_def, domain_union]
);

val findRefsGlobals_LUPDATE = Q.store_thm ("findRefsGlobals_LUPDATE",
    `∀ reachable:num_set refs n .
        n < LENGTH refs ∧ domain (findRefsGlobals refs) ⊆ domain reachable
      ⇒
        (∀ a . domain (findVglobals a) ⊆ domain reachable
            ⇒ domain (findRefsGlobals (LUPDATE (Refv a) n refs))
                ⊆ domain reachable) ∧
    (∀ vs . domain (findVglobalsL vs) ⊆ domain reachable
        ⇒ domain (findRefsGlobals (LUPDATE (Varray vs) n  refs))
            ⊆ domain reachable) ∧
    (∀ ws. domain (findRefsGlobals (LUPDATE (W8array ws) n refs))
        ⊆ domain reachable)`,
    Induct_on `refs` >> rw[] >> Cases_on `h` >>
    fs[findRefsGlobals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, findRefsGlobals_def, domain_union] >>
    fs[domain_union, LUPDATE_def] >> Cases_on `n` >> fs[] >>
    fs[LUPDATE_def, findRefsGlobals_def, domain_union]
);

val findRefsGlobals_APPEND = Q.store_thm ("findRefsGlobals_APPEND",
    `∀ refs new . findRefsGlobals (refs ++ new) =
        union (findRefsGlobals refs) (findRefsGlobals new)`,
    Induct >> rw[] >> fs[findRefsGlobals_def] >>
    Cases_on `h` >> fs[findRefsGlobals_def] >> fs[union_assoc]

);

val findEnvGlobals_def = Define `
    findEnvGlobals env = findVglobalsL (MAP SND env.v)
`

val findResultGlobals_def = Define `
    (findResultGlobals (SOME (Rraise v)) = findVglobals v) ∧
    (findResultGlobals _ = LN)
`

val findResultGlobals_ind = theorem "findResultGlobals_ind";

val findSemPrimResGlobals_def = Define `
    (findSemPrimResGlobals (Rerr e :
        (flatSem$v list, flatSem$v) semanticPrimitives$result) =
        findResultGlobals (SOME e)) ∧
    (findSemPrimResGlobals (Rval e) = findVglobalsL e)
`

(* s = state, t = removed state *)
val globals_rel_def = Define `
    globals_rel
        (reachable : num_set) (s : 'a flatSem$state) (t : 'a flatSem$state) ⇔
        LENGTH s.globals = LENGTH t.globals ∧
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t.globals
        ⇒ EL n s.globals = EL n t.globals) ∧
        (∀ n x . n < LENGTH t.globals ∧ EL n t.globals = SOME x
            ⇒ EL n s.globals = SOME x) ∧
        (∀ n . n < LENGTH t.globals ∧ EL n s.globals = NONE
            ⇒ EL n t.globals = NONE) ∧
        (∀ n x . n ∈ domain reachable ∧ n < LENGTH t.globals ∧
            EL n t.globals = SOME x
          ⇒ domain (findVglobals x) ⊆ domain reachable)
`

val globals_rel_trans = Q.store_thm("globals_rel_trans",
    `∀ reachable s1 s2 s3 .
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3`,
    rw[globals_rel_def]
);

val decsClosed_def = Define `
    decsClosed (reachable : num_set) decs ⇔  ∀ r t . analyseCode decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ isReachable (mk_wf_set_tree t) n m
      ⇒ m ∈ domain reachable)
`

val decsClosed_reduce = Q.store_thm ("decsClosed_reduce",
    `∀ reachable h t . decsClosed reachable (h::t) ⇒ decsClosed reachable t`,
    fs[decsClosed_def] >> rw[] >> Cases_on `h` >> fs[analyseCode_def]
    >- (Cases_on `analyseExp e` >> fs[codeAnalysis_union_def, domain_union])
    >- (Cases_on `analyseExp e` >> fs[codeAnalysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >> pop_assum match_mp_tac >>
        assume_tac isReachable_wf_set_tree_num_set_tree_union >> fs[] >>
        fs[Once num_set_tree_union_sym])
    >> metis_tac[]
);

val decsClosed_reduce_HD = Q.store_thm("decsClosed_reduce_HD",
    `∀ reachable h t . decsClosed reachable (h::t) ⇒ decsClosed reachable [h]`,
    fs[decsClosed_def] >> rw[] >> Cases_on `h` >> fs[analyseCode_def] >>
    Cases_on `analyseExp e` >>
    fs[codeAnalysis_union_def, domain_union] >> rveq >> fs[domain_def]
    >- (Cases_on `analyseCode t` >> fs[codeAnalysis_union_def, domain_union])
    >- (fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
        Cases_on `analyseCode t` >> fs[codeAnalysis_union_def, domain_union] >>
        imp_res_tac isReachable_wf_set_tree_num_set_tree_union >>
        pop_assum (qspec_then `r` mp_tac) >> strip_tac >> res_tac)
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
);

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧
    s.ffi = t.ffi ∧ globals_rel reachable s t ∧
    domain (findRefsGlobals s.refs) ⊆ domain reachable
`

val flat_state_rel_trans = Q.store_thm("flat_state_rel_trans",
    `∀ reachable s1 s2 s3 . flat_state_rel reachable s1 s2 ∧
        flat_state_rel reachable s2 s3
    ⇒ flat_state_rel reachable s1 s3`,
    rw[flat_state_rel_def, globals_rel_def]
);

(**************************** FLATLANG LEMMAS *****************************)

val pmatch_Match_reachable = Q.store_thm ("pmatch_Match_reachable",
    `(∀ env refs p v l a reachable:num_set . pmatch env refs p v l = Match a ∧
        domain (findVglobalsL (MAP SND env.v)) ⊆ domain reachable ∧
        domain (findVglobals v) ⊆ domain reachable ∧
        domain (findVglobalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (findRefsGlobals refs) ⊆ domain reachable
    ⇒ domain (findVglobalsL (MAP SND a)) ⊆ domain reachable)
  ∧
    (∀ env refs p vs l a reachable:num_set .
        pmatch_list env refs p vs l = Match a ∧
        domain (findVglobalsL (MAP SND env.v)) ⊆ domain reachable ∧
        domain (findVglobalsL vs) ⊆ domain reachable ∧
        domain (findVglobalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (findRefsGlobals refs) ⊆ domain reachable
    ⇒ domain (findVglobalsL (MAP SND a)) ⊆ domain reachable)`
  ,
    ho_match_mp_tac pmatch_ind >> rw[pmatch_def] >>
    fs[findVglobals_def, domain_union]
    >- (Cases_on `store_lookup lnum refs` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[semanticPrimitivesTheory.store_lookup_def] >>
        first_x_assum (qspec_then `reachable` match_mp_tac) >> rw[] >>
        imp_res_tac findRefsGlobals_EL >> metis_tac[SUBSET_TRANS])
    >- (Cases_on `pmatch env refs p v l` >> fs[domain_union])
);


val findVglobals_list_to_v_APPEND = Q.store_thm(
    "findVglobals_list_to_v_APPEND",
    `∀ xs reachable ys .
        domain (findVglobalsL xs) ⊆ domain reachable ∧
        domain(findVglobalsL ys) ⊆ domain reachable
    ⇒ domain (findVglobals (list_to_v (xs ++ ys))) ⊆ domain reachable`,
    Induct >> fs[list_to_v_def, findVglobals_def, domain_union] >>
    metis_tac[findVglobals_list_to_v]
);

val findVglobals_Unitv = Q.store_thm("findVglobals_Unitv[simp]",
  `findVglobals (Unitv cc) = LN`,
  EVAL_TAC);

val do_app_SOME_flat_state_rel = Q.store_thm("do_app_SOME_flat_state_rel",
    `∀ reachable state removed_state op l new_state result new_removed_state.
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧
        domain(findVglobalsL l) ⊆ domain reachable ∧
        domain (findLookups (App tra op [])) ⊆ domain reachable
          ⇒ do_app cc state op l = SOME (new_state, result) ∧
            result ≠ Rerr (Rabort Rtype_error)
            ⇒ ∃ new_removed_state .
                flat_state_rel reachable new_state new_removed_state ∧
                do_app cc removed_state op l =
                    SOME (new_removed_state, result) ∧
                domain (findSemPrimResGlobals (list_result result)) ⊆
                    domain reachable`,

    rw[] >> qpat_x_assum `flat_state_rel _ _ _` mp_tac >>
    simp[Once flat_state_rel_def] >> strip_tac >>
    `∃ this_case . this_case op` by (qexists_tac `K T` >> simp[]) >>
    reverse (Cases_on `op`) >> fs[]
    >- (fs[do_app_def] >> Cases_on `l` >> fs[findVglobals_def] >>
        rveq >> fs[flat_state_rel_def] >>
        fs[findLookups_def, dest_GlobalVarLookup_def] >>
        fs[findSemPrimResGlobals_def] >>
        Cases_on `EL n new_state.globals` >> fs[] >> res_tac >>
        Cases_on `EL n removed_state.globals` >> fs[findVglobals_def] >>
        fs[globals_rel_def] >> res_tac >> fs[] >> rveq >> metis_tac[])
    >- (fs[do_app_def] >> Cases_on `l` >> fs[findVglobals_def] >>
        Cases_on `t` >> fs[] >>
        rveq >> fs[flat_state_rel_def, globals_rel_def] >> rfs[] >>
        fs[EL_LUPDATE] >> rw[] >>
        fs[findSemPrimResGlobals_def, findVglobals_def] >>
        metis_tac[]) >>
    fs[do_app_cases] >> rveq >> fs[] >> rw[] >>
    fs[findSemPrimResGlobals_def, findVglobals_def, findResultGlobals_def] >>
    fs[semanticPrimitivesTheory.store_assign_def,
       semanticPrimitivesTheory.store_v_same_type_def, subscript_exn_v_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,
       semanticPrimitivesTheory.store_lookup_def,
       chr_exn_v_def, Boolv_def, div_exn_v_def] >>
    fs[flat_state_rel_def, findVglobals_def,
       domain_union, findRefsGlobals_def] >> rveq >> rfs[globals_rel_def]
    (* 21 subgoals *)
    >- (rw[] >> Cases_on `n' < LENGTH removed_state.globals` >> rveq >> fs[]
        >- fs[EL_APPEND1] >- fs[EL_APPEND2] >- fs[EL_APPEND1] >- fs[EL_APPEND2]
        >- metis_tac[EL_APPEND1]
        >- (fs[EL_APPEND2] >>
            `n' - LENGTH removed_state.globals < n` by fs[] >>
            metis_tac[EL_REPLICATE])
        >- (fs[EL_APPEND1] >> metis_tac[])
        >- (fs[EL_APPEND2] >>
            `n' - LENGTH removed_state.globals < n` by fs[] >>
            fs[EL_REPLICATE]))
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >-  metis_tac[findVglobals_v_to_list, findVglobals_list_to_v_APPEND]
    >- (qsuff_tac
        `domain (findVglobalsL (LUPDATE v'''''' (Num (ABS i''''''')) vs))
            ⊆ domain reachable`
        >-  metis_tac[findRefsGlobals_LUPDATE]
        >>  match_mp_tac findVglobalsL_LUPDATE >> fs[] >>
            imp_res_tac EL_MEM >> rfs[] >>
            fs[findRefsGlobals_def] >> metis_tac[findRefsGlobals_MEM])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (imp_res_tac findRefsGlobals_EL >>
        `domain (findVglobals (EL (Num (ABS i'''''')) vs))
            ⊆ domain (findVglobalsL vs)` by
            (match_mp_tac findVglobalsL_EL >> decide_tac) >>
             metis_tac[SUBSET_TRANS])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >- metis_tac[] >>
        fs[findRefsGlobals_APPEND, domain_union, findRefsGlobals_def] >>
        metis_tac[findVglobalsL_REPLICATE, SUBSET_DEF])
    >- (`Num (ABS i''''') < LENGTH vs'` by fs[] >>
        metis_tac[findVglobalsL_EL, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (metis_tac[findVglobals_v_to_list, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (fs[findRefsGlobals_APPEND, domain_union, findRefsGlobals_def] >>
        metis_tac[])
    >- (metis_tac[findRefsGlobals_EL, SUBSET_DEF])
    >- (rw[] >>
        fs[findRefsGlobals_APPEND, findRefsGlobals_def,
           findVglobals_def, domain_union] >> res_tac)
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
);



(**************************** MAIN LEMMAS *****************************)

val close_spt_thm = Q.store_thm("close_spt_thm",
    `∀ reachable seen tree closure (roots : num set) .
        (wf reachable) ∧ (wf seen) ∧ (wf_set_tree tree) ∧
        (close_spt reachable seen tree = closure) ∧
        (subspt reachable seen) ∧
        (roots ⊆ domain (seen)) ∧
        (domain seen ⊆ domain tree) ∧
        (∀ k . k ∈ domain (seen)
            ⇒ (∃ n . (n ∈ roots) ∧ (isReachable tree n k))) ∧
        (∀ k . k ∈ domain (reachable)
            ⇒ (∀ a . (isAdjacent tree k a) ⇒ a ∈ domain (seen)))
      ⇒ (domain closure = {a | ∃ n . (isReachable tree n a) ∧ (n ∈ roots)})`
  ,
    recInduct close_spt_ind >> rw[] >>
    once_rewrite_tac [close_spt_def] >> simp[] >> fs[wf_set_tree_def] >>
    IF_CASES_TAC
    >- (
        imp_res_tac inter_eq_LN  >>
        imp_res_tac subspt_domain >>
        fs[SUBSET_DEF, EXTENSION, IN_DISJOINT, domain_difference] >>
        `domain reachable = domain seen` by (
            fs[EXTENSION] >> rw[] >> EQ_TAC >> fs[] >> metis_tac[]) >>
        imp_res_tac num_set_domain_eq >>
        fs[] >> rveq >> rw[] >> EQ_TAC >> rw[]
        >- (qpat_x_assum `∀ k . k ∈ domain seen ⇒ _` (qspec_then `x` mp_tac) >>
            reverse(impl_tac) >> rw[] >> metis_tac[])
        >> (imp_res_tac reachable_domain >> rveq >> fs[] >>
            res_tac >>
            qspecl_then [`domain reachable`, `domain reachable`, `tree`] mp_tac
                (rtc_isAdjacent |> GEN_ALL) >>
            strip_tac >> fs[] >>
            fs[isReachable_def] >>
            res_tac)
        )
    >- (
        fs[] >>
        first_x_assum match_mp_tac >>
        fs[wf_union, wf_difference, subspt_domain, domain_union] >>
        fs[SUBSET_DEF] >>
        rw[] >> fs[]
        >- (
            match_mp_tac wf_union >>
            fs[] >>
            match_mp_tac wf_spt_fold_tree >>
            fs[wf_inter, wf_def] >>
            fs[lookup_inter] >>
            rw[] >> EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[subspt_lookup] >>
            res_tac >>
            metis_tac[]
            )
        >-  metis_tac[]
        >-  metis_tac[]
        >- (
            qspecl_then [`tree`, `LN`] mp_tac domain_spt_fold_union >>
            fs[domain_def] >>
            impl_tac
            >- (rw[] >> res_tac >> fs[SUBSET_DEF])
            >- (rw[] >>
                qspecl_then
                    [`inter tree (difference seen reachable)`, `tree`, `LN`]
                    mp_tac subspt_domain_spt_fold_union >>
                rw[] >> fs[SUBSET_DEF] >>
                first_x_assum mp_tac >> impl_tac >> fs[] >>
                fs[subspt_alt, lookup_inter, domain_difference] >> rw[] >>
                EVERY_CASE_TAC >> fs[])
            )
        >- (
            fs[domain_lookup] >>
            imp_res_tac lookup_spt_fold_union >>
            fs[lookup_def] >>
            fs[lookup_inter] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[lookup_difference] >> EVERY_CASE_TAC >> fs[] >>
            res_tac >>
            qexists_tac `v'` >> fs[]
            )
        >- (
            fs[domain_lookup] >>
            imp_res_tac lookup_spt_fold_union >>
            fs[lookup_def] >>
            fs[lookup_inter] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >>
            fs[lookup_difference] >> EVERY_CASE_TAC >> fs[] >>
            res_tac >>
            qexists_tac `n` >> fs[] >>
            fs[isReachable_def] >>
            simp[Once RTC_CASES2] >>
            DISJ2_TAC >>
            qexists_tac `n1` >> fs[] >>
            fs[isAdjacent_def]
            )
        >-  metis_tac[]
        >- (
            Cases_on `a ∈ domain seen` >> fs[] >>
            Cases_on `a ∈ domain reachable` >> rfs[]
            >-  metis_tac[]
            >>  `a ∈ domain tree` by fs[isAdjacent_def, domain_lookup] >>
                `k ∈ domain tree` by fs[isAdjacent_def, domain_lookup] >>
                `k ∈ domain (inter tree (difference seen reachable))` by
                    fs[domain_inter, domain_difference] >>
                fs[isAdjacent_def] >>
                fs[domain_lookup] >>
                qspecl_then
                    [`inter tree (difference seen reachable)`, `LN`, `a`]
                    mp_tac (GSYM lookup_spt_fold_union_STRONG) >>
                fs[lookup_def] >> strip_tac >>
                fs[lookup_inter] >> EVERY_CASE_TAC >> fs[] >>
                rveq >> fs[] >>
                fs[EQ_IMP_THM] >>
                first_x_assum match_mp_tac >>
                fs[lookup_difference] >>
                qexists_tac `k` >> fs[]
            )
    )
);

val closure_spt_lemma =
    close_spt_thm |> Q.SPECL [`LN`, `start:num_set`, `tree`]
        |> SIMP_RULE std_ss [
            GSYM closure_spt_def, wf_def, wf_insert,
            subspt_def, domain_def, NOT_IN_EMPTY,
            domain_insert, SUBSET_DEF
           ]
        |> Q.SPECL[`domain (start:num_set)`]
        |> SIMP_RULE std_ss [
                ConseqConvTheory.AND_CLAUSES_XX,
                ConseqConvTheory.IMP_CLAUSES_XX,
                IN_SING, Once isReachable_def, RTC_REFL, AND_CLAUSES
           ] |> GEN_ALL
;

val closure_spt_thm = Q.store_thm("closure_spt_thm",
    `∀ tree start . wf start ∧ (wf_set_tree tree) ∧
    (domain start ⊆ domain tree)
  ⇒ domain (closure_spt start tree) =
        {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`,
    rw[] >> assume_tac closure_spt_lemma >> rw[] >> fs[wf_set_tree_def] >>
    first_x_assum match_mp_tac >> reverse(rw[]) >> res_tac >> fs[SUBSET_DEF] >>
    qexists_tac `k` >> fs[]
);

val analysis_reachable_thm = Q.store_thm("analysis_reachable_thm",
   `∀ (compiled : dec list) start tree t .
        ((start, t) = analyseCode compiled) ∧
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . isReachable tree n a ∧ n ∈ domain start}`
    ,
    rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >>
    rw[] >> `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`compiled`, `start`, `t`] mp_tac analyseCode_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >>
    metis_tac[SUBSET_TRANS]
);

(******** EVALUATE MUTUAL INDUCTION ********)

val evaluate_sing_keep_flat_state_rel_eq_lemma = Q.store_thm(
    "evaluate_sing_keep_flat_state_rel_eq_lemma",
    `(∀ env (state:'a flatSem$state) exprL new_state
        result reachable:num_set removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        domain (findLookupsL exprL) ⊆ domain reachable ∧
        env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate env removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (findSemPrimResGlobals result) ⊆ domain reachable)
   ∧
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result
        reachable:num_set removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        domain (findLookupsL (MAP SND patExp_list)) ⊆ domain reachable ∧
        env.exh_pat ∧
        domain (findVglobals v) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate_match env removed_state v patExp_list err_v =
            (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (findSemPrimResGlobals result) ⊆ domain reachable)`
      ,
        ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac
        (* EVALUATE CASES *)
            (* EMPTY LIST CASE *)
        >- (fs[evaluate_def] >> rveq >>
            fs[findSemPrimResGlobals_def, findVglobals_def])
            (* NON_EMPTY, NON-SINGLETON LIST CASE *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >>
            fs[findLookups_def, domain_union] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            Cases_on `evaluate env q (e2::es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
            fs[] >>
            reverse(Cases_on `r` >> fs[]) >- (rw[] >> fs[])
            >- (strip_tac >> rw[] >>
                fs[findSemPrimResGlobals_def,
                    findVglobals_def, domain_union] >>
                imp_res_tac evaluate_sing >> rveq >> rveq >>
                fs[findVglobals_def]))
        (* SINGLETON LIST CASES *)
            (* Lit - DONE!!! *)
        >- (fs[evaluate_def] >> rveq >> fs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def])
            (* Raise *)
        >- (rpt gen_tac >> strip_tac >> fs[findLookups_def] >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >> strip_tac >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (
                CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >> Cases_on `r` >> fs[] >> rveq >> fs[] >>
            fs[findSemPrimResGlobals_def,
                findVglobals_def, findResultGlobals_def] >>
            imp_res_tac evaluate_sing >> rveq >> rveq >> fs[findVglobals_def])
            (* Handle - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            fs[findLookups_def, domain_union] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            Cases_on `r` >> rw[] >> rfs[] >>
            Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] match_mp_tac) >>
            fs[findSemPrimResGlobals_def, findResultGlobals_def])
            (* Con NONE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `env.check_ctor` >> fs[] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >>
            simp[Once findVglobalsL_REVERSE])
            (* Con SOME - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >>
            simp[Once findVglobalsL_REVERSE])
            (* Var_local - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >> fs[findLookups_def] >>
            Cases_on `ALOOKUP env.v n` >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >>
            imp_res_tac ALOOKUP_MEM >> imp_res_tac findVglobalsL_MEM >>
            fs[findEnvGlobals_def] >> fs[SUBSET_DEF])
            (* Fun - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >>
            fs[findSemPrimResGlobals_def,
                findEnvGlobals_def, findVglobals_def] >>
            fs[domain_union, findLookups_def])
            (* App *)
        >- (
            rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (
                qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> fs[] >>
            `domain (findLookupsL es) ⊆ domain reachable` by (
                Cases_on `op` >> fs[dest_GlobalVarLookup_def] >>
                fs[domain_insert]) >>
            fs[] >>
            Cases_on `r` >> fs[] >> strip_tac >> rveq >> fs[] >> rfs[] >>
            Cases_on `op = Opapp` >> fs[]
            >- (Cases_on `do_opapp (REVERSE a)` >> fs[] >>
                Cases_on `x` >> fs[] >>
                Cases_on `q.clock = 0` >> fs[]
                >- (rveq >>
                    qpat_x_assum
                        `flat_state_rel reachable new_state _` mp_tac >>
                    simp[Once flat_state_rel_def] >> strip_tac >> rveq >>
                    fs[flat_state_rel_def,
                        findSemPrimResGlobals_def, findResultGlobals_def])
                >- (first_x_assum (qspecl_then
                        [`reachable`, `dec_clock new_removed_state`] mp_tac) >>
                    fs[] >>
                    qpat_x_assum `flat_state_rel reachable q _` mp_tac >>
                    simp[Once flat_state_rel_def] >>
                    strip_tac >> strip_tac >>
                    qpat_x_assum `_ ⇒ _` match_mp_tac  >>
                    fs[flat_state_rel_def, globals_rel_def,
                        dec_clock_def, findEnvGlobals_def] >> rfs[] >> rveq >>
                    fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >>
                    fs[findSemPrimResGlobals_def] >>
                    fs[SWAP_REVERSE_SYM, findVglobals_def, domain_union] >>
                    rw[]
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (
                            fs[MEM_MAP] >> qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac findLookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
                        fs[findVglobalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by
                            (rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >>
                        fs[] >>
                        `domain (findVglobalsL (MAP (λ(f,x,e).
                            Recclosure l l0 f) l0)) ⊆
                            domain(findVglobalsL (MAP SND l)) ∪
                        domain (findLookupsL (MAP (SND o SND) l0))` by
                            metis_tac[findVglobals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[])
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (fs[MEM_MAP] >>
                        qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac findLookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
                        fs[findVglobalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by (
                            rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >> fs[] >>
                        `domain (findVglobalsL
                            (MAP (λ(f,x,e). Recclosure l l0 f) l0)) ⊆
                            domain(findVglobalsL (MAP SND l)) ∪
                        domain (findLookupsL (MAP (SND o SND) l0))` by
                            metis_tac[findVglobals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[]))
                )
            >- (Cases_on `do_app env.check_ctor q op (REVERSE a)` >> fs[] >>
                PairCases_on `x` >> fs[] >> rveq >>
                drule (GEN_ALL do_app_SOME_flat_state_rel) >>
                fs[findLookups_def] >> disch_then drule >> strip_tac >>
                pop_assum (qspecl_then [
                    `env.check_ctor`, `REVERSE a`, `new_state`, `x1`] mp_tac) >>
                    simp[Once findVglobalsL_REVERSE] >>
                fs[] >> strip_tac >>
                `domain (case dest_GlobalVarLookup op of
                    NONE => LN | SOME n => insert n () LN) ⊆ domain reachable`
                        by (Cases_on `dest_GlobalVarLookup op` >> fs[]) >>
                            fs[findSemPrimResGlobals_def] >> rfs[]))
            (* If - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >> fs[] >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >>
            Cases_on `r` >> fs[] >>
            Cases_on `do_if (HD a) e2 e3` >> fs[] >>
            fs[do_if_def] >> EVERY_CASE_TAC >> fs[])
            (* Mat - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
                match_mp_tac) >> fs[] >>
            fs[findSemPrimResGlobals_def] >>
            imp_res_tac evaluate_sing >> rveq >> fs[] >> rveq >>
            fs[findVglobals_def])
            (* Let - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            `r ≠ Rerr(Rabort Rtype_error)` by
                (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
                match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[findVglobals_def, domain_union] >>
            fs[findSemPrimResGlobals_def] >> imp_res_tac evaluate_sing >>
            rveq >> fs[] >> rveq >> fs[findVglobals_def])
            (* Letrec *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
            strip_tac >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, build_rec_env_def] >>
            fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >>
            fs[MAP_MAP_o] >>
            `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs =
                MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by
                    (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
            `domain (findVglobalsL (MAP (SND o (λ(f,x,e).
                (f, Recclosure env.v funs f))) funs)) ⊆
                domain (findVglobalsL (MAP SND env.v)) ∪
                domain (findLookupsL (MAP (SND o SND) funs))` by
                    metis_tac[findVglobals_MAP_Recclosure] >>
            fs[SUBSET_DEF] >> metis_tac[])
        (* EVALUATE_MATCH CASES *)
            (* EMPTY LIST CASE - DONE!!! *)
        >- (fs[evaluate_def])
            (* NON-EMPTY LIST CASE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate_match _ _ _ _ _ =  _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (pat_bindings p [])` >> fs[] >>
            strip_tac >>
            `state'.refs = removed_state.refs` by fs[flat_state_rel_def] >>
            fs[] >>
            Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, findVglobalsL_APPEND, domain_union] >>
            drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >>
            disch_then match_mp_tac >> fs[findVglobals_def] >> rw[] >>
            fs[flat_state_rel_def])
);

(******** EVALUATE SPECIALISATION ********)

val evaluate_sing_keep_flat_state_rel_eq = Q.store_thm(
    "evaluate_sing_keep_flat_state_rel_eq",
    `∀ env (state:'a flatSem$state) exprL new_state result expr
        reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
        exprL = [expr] ∧
        keep reachable (Dlet expr) ∧ env.exh_pat ∧
        domain(findLookups expr) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate (env with v := []) removed_state exprL
            = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state`
      ,
        rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
        drule (CONJUNCT1 evaluate_sing_keep_flat_state_rel_eq_lemma) >> fs[] >>
        strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[] >>
        impl_tac >> fs[] >>
        simp[findEnvGlobals_def, findVglobals_def, Once findLookups_def] >>
        simp[EVAL ``findLookupsL []``] >> rw[] >> fs[]
);

(******** EVALUATE_DEC ********)

val evaluate_dec_flat_state_rel = Q.store_thm("evaluate_dec_flat_state_rel",
    `∀ env (state:'a flatSem$state) dec new_state new_ctors result
        reachable removed_state .
        evaluate_dec env state dec = (new_state, new_ctors, result) ∧
        env.exh_pat ∧
        decsClosed reachable [dec] ∧
        flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        domain (findEnvGlobals env) ⊆ domain reachable
    ⇒ ∃ new_removed_state .
        evaluate_dec env removed_state dec =
            (new_removed_state, new_ctors, result) ∧
        flat_state_rel reachable new_state new_removed_state`
      ,
        rw[] >> qpat_x_assum `evaluate_dec _ _ _ = _` mp_tac >>
        reverse(Induct_on `dec`) >> fs[evaluate_dec_def] >> strip_tac >>
        strip_tac >>
        fs[keep_def]
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def])
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def]) >>
        strip_tac >> strip_tac >>
        assume_tac evaluate_sing_keep_flat_state_rel_eq >> fs[] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`env`, `state'`, `q`, `r`, `e`,
            `reachable`, `removed_state`] mp_tac) >> strip_tac >>
        fs[keep_def] >> rfs[] >> fs[] >>
        `domain (findLookups e) ⊆ domain reachable` by (
            fs[decsClosed_def] >> fs[analyseCode_def] >> fs[analyseExp_def] >>
            reverse(Cases_on `isPure e`) >> fs[]
            >- (fs[codeAnalysis_union_def] >> fs[domain_union]) >>
            reverse(Cases_on `isHidden e`) >> fs[] >>
            fs[codeAnalysis_union_def, domain_union] >>
            fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
            simp[SUBSET_DEF] >>
            rw[] >> first_x_assum match_mp_tac >>
            fs[spt_eq_thm, wf_inter, wf_def] >> fs[lookup_inter_alt] >>
            fs[lookup_def] >> Cases_on `lookup n (findLoc e)` >> fs[] >>
            fs[domain_lookup] >>
            asm_exists_tac >> fs[] >> fs[isReachable_def] >>
            match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
            `(lookup n (map (K (findLookups e)) (findLoc e))) =
                SOME (findLookups e)` by fs[lookup_map] >>
            imp_res_tac lookup_mk_wf_set_tree >> fs[] >>
            `wf_set_tree (mk_wf_set_tree (map (K (findLookups e)) (findLoc e)))`
                by metis_tac[mk_wf_set_tree_thm] >>
            fs[wf_set_tree_def] >> res_tac >> `y = findLookups e`
                by metis_tac[wf_findLookups, num_set_domain_eq] >>
            rveq >> fs[] >> fs[SUBSET_DEF, domain_lookup]) >>
        fs[] >> `r ≠ Rerr (Rabort Rtype_error)` by
            (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
        qpat_x_assum `_ = (_,_,_) ` mp_tac >> fs[] >>
        EVERY_CASE_TAC >> fs[] >> rw[] >>
        fs[findResultGlobals_def, findSemPrimResGlobals_def]
);




(********************** CASE: *NOT* keep reachable h ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

val evaluate_flat_state_rel_lemma = Q.store_thm (
    "evaluate_flat_state_rel_lemma",
    `(∀ env (state:'a flatSem$state) exprL new_state result
        reachable removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        EVERY isPure exprL ∧
        EVERY (λ e. isEmpty (inter (findLoc e) reachable)) exprL ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ values : flatSem$v list . result = Rval values)
   ∧
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result
        reachable removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        EVERY isPure (MAP SND patExp_list) ∧
        EVERY (λ e. isEmpty (inter (findLoc e) reachable))
            (MAP SND patExp_list) ∧
        env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ values : flatSem$v list . result = Rval values)`
  ,
    ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac
    >| [
        (* EVALUATE_DECS_CASES *)

        (* EMPTY LIST CASE - DONE!!! *)
        fs[evaluate_def] >> rveq >> fs[findVglobals_def]
      ,
        (* NON-EMPTY, NON-SINGLETON LIST CASE - DONE!!! *)
        rpt gen_tac >> strip_tac >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (Cases_on `evaluate env q (e2 :: es)` >> fs[] >>
            first_x_assum drule >> disch_then drule >>
            fs[] >> Cases_on `r` >> fs[]
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`]
                    mp_tac) >> fs[] >>
                rw[] >> fs[findVglobals_def, domain_union] >>
                `LENGTH a = 1` by (imp_res_tac evaluate_sing >> fs[]) >>
                Cases_on `a` >> fs[findVglobals_def, domain_union])
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`]
                    mp_tac) >>
                fs[] >> rw[] >> fs[] >> qpat_x_assum `EXISTS _ _` mp_tac >>
                once_rewrite_tac [GSYM NOT_EVERY] >> strip_tac))
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            rw[] >> fs[])

      , (* SINGLETON LIST CASES *)

        (* Lit - DONE!!! *)
        fs[evaluate_def] >> rveq >> fs[findVglobals_def]
      ,
        (* Raise - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[isPure_def]
      ,
        (* Handle - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (rveq >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[isPure_def] >> strip_tac >>
            qpat_x_assum `isEmpty _` mp_tac >>
            simp[Once findLoc_def] >>
            strip_tac >>
            qpat_x_assum `isEmpty _ ⇒ _` match_mp_tac >> fs[] >>
            imp_res_tac inter_union_empty)
        >- (fs[isPure_def] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
            strip_tac >>
            `isEmpty(inter (findLocL (MAP SND patExp_list)) reachable) ∧
            isEmpty (inter (findLoc e) reachable)` by
                metis_tac[inter_union_empty] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >> strip_tac >> fs[])
      ,
        (* Con NONE - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        reverse(Cases_on `env.check_ctor`) >> fs[] >> fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> rveq >>
            fs[isPure_def, findVglobals_def] >> fs[EVERY_REVERSE] >>
            simp[Once findVglobalsL_REVERSE] >> fs[isPure_EVERY_aconv] >>
            rfs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
            strip_tac >>
            fs[findLoc_EVERY_isEmpty])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            rveq >> fs[isPure_def] >> fs[EVERY_REVERSE, isPure_EVERY_aconv] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >>
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
            fs[findLoc_EVERY_isEmpty])
      ,
        (* Con SOME - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >>
        strip_tac >> fs[evaluate_def] >>
        Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >> fs[] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >> Cases_on `r` >>
        fs[] >>
        fs[isPure_def, isPure_EVERY_aconv, EVERY_REVERSE] >> rveq >>
        fs[findLoc_EVERY_isEmpty] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[EVERY_REVERSE, isPure_EVERY_aconv] >>
        once_rewrite_tac [(GSYM NOT_EXISTS)] >>
        once_rewrite_tac [GSYM NOT_EVERY] >> fs[findLoc_EVERY_isEmpty]
      ,
        (* Var_local - DONE!!! *)
        fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >>
        rveq >> fs[] >>
        fs[findVglobals_def, findEnvGlobals_def] >> imp_res_tac ALOOKUP_MEM >>
        imp_res_tac findVglobalsL_MEM >> imp_res_tac SUBSET_TRANS
      ,
        (* Fun - DONE!!! *)
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >>
        strip_tac >> fs[evaluate_def] >>
        rveq >>
        fs[findVglobals_def, domain_union, findEnvGlobals_def, isPure_def] >>
        fs[findLoc_def]
      ,
        (* App - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        fs[isPure_def] >> qpat_x_assum `isEmpty _` mp_tac >>
        simp[Once findLoc_def] >>
        strip_tac >> fs[] >> fs[EVERY_REVERSE] >> fs[findLoc_EVERY_isEmpty] >>
        Cases_on `r` >> fs[]
        >- (Cases_on `op = Opapp` >> fs[isPure_def, dest_GlobalVarInit_def] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            strip_tac >>
            Cases_on `op` >>
            fs[isPure_def, dest_GlobalVarInit_def, do_app_def] >>
            fs[isPure_EVERY_aconv] >> imp_res_tac inter_insert_empty >>
            EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
            fs[findVglobals_def, flat_state_rel_def] >> rw[] >> fs[] >> rfs[] >>
            fs[globals_rel_def] >>
            fs[LUPDATE_SEM] >>
            reverse(rw[]) >- metis_tac[] >>
            Cases_on `n = n'` >> fs[] >>
            qpat_x_assum `∀ n . _ ∧ _ ⇒ _` match_mp_tac >>
            fs[EL_LUPDATE])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >>
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            Cases_on `op` >>
            fs[isPure_def, isPure_EVERY_aconv, dest_GlobalVarInit_def] >>
            imp_res_tac inter_insert_empty)
      ,
        (* If - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
        fs[isPure_def] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >>
        `isEmpty (inter (findLoc e1) reachable) ∧
            isEmpty (inter (findLoc e2) reachable) ∧
            isEmpty (inter (findLoc e3) reachable)` by
                metis_tac[inter_union_empty] >>
        Cases_on `r` >> fs[]
        >- (fs[do_if_def, Boolv_def] >> Cases_on `HD a` >> fs[] >>
            EVERY_CASE_TAC >> fs[] >>
            rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
                mp_tac) >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`]
                mp_tac) >> fs[])
        >- (rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[])
      ,
        (* Mat - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >> fs[isPure_def] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >>
        `isEmpty (inter (findLocL (MAP SND patExp_list)) reachable) ∧
            isEmpty (inter (findLoc e) reachable)` by
                metis_tac[inter_union_empty] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> Cases_on `r` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> fs[isPure_EVERY_aconv, findLoc_EVERY_isEmpty] >> rfs[] >>
        imp_res_tac evaluate_sing >> rveq >> fs[findVglobals_def]
      ,
        (* Let - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[isPure_def] >>
        fs[isPure_def] >> qpat_x_assum `isEmpty _ ` mp_tac >>
        simp[Once findLoc_def] >>
        strip_tac >> imp_res_tac inter_union_empty >>
        Cases_on `r` >> fs[]
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            strip_tac >> strip_tac >>
            fs[findEnvGlobals_def] >>
            qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
            fs[libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[findVglobals_def, domain_union] >>
            imp_res_tac evaluate_sing >> rveq >> fs[findVglobals_def])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[])
      ,
        (* Letrec - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        strip_tac >> fs[isPure_def] >> rfs[] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >>
        `isEmpty (inter (findLocL (MAP (SND o SND) funs)) reachable) ∧
            isEmpty (inter (findLoc e) reachable)` by
                metis_tac[inter_union_empty] >>
        fs[] >> qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
        fs[findEnvGlobals_def, build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
        fs[findVglobalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
        `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs =
            MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by
                (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
        fs[]
      , (* EVALUATE_MATCH CASES *)

        (* EMPTY LIST CASE - DONE!!! *)
        fs[evaluate_def]
      ,
        (* NON-EMPTY LIST CASE - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (pat_bindings p [])` >>
        fs[] >>
        Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >>
        impl_tac >> fs[] >>
        fs[findEnvGlobals_def, findVglobalsL_APPEND, domain_union] >>
        drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >>
        disch_then match_mp_tac >>
        fs[findVglobals_def] >> rw[] >> metis_tac[]
    ]
);

(******** EVALUATE SPECIALISATION ********)


val evaluate_sing_notKeep_flat_state_rel = Q.store_thm(
    "evaluate_sing_notKeep_flat_state_rel",
    `∀ env (state:'a flatSem$state) exprL new_state result expr
        reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
        exprL = [expr] ∧
        ¬keep reachable (Dlet expr) ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧
        ∃ value : flatSem$v . result = Rval [value]`
  ,
    rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
    drule (CONJUNCT1 evaluate_flat_state_rel_lemma) >> fs[] >>
    disch_then drule >> disch_then drule >> fs[] >>
    rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[findVglobals_def]
);



(******************************* MAIN PROOFS ******************************)

val flat_decs_removal_lemma = Q.store_thm ("flat_decs_removal_lemma",
    `∀ env (state:'a flatSem$state) decs new_state new_ctors result
        reachable removed_decs removed_state .
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ env.exh_pat ∧
        removeUnreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        decsClosed reachable decs
    ⇒ ∃ new_removed_state .
        new_removed_state.ffi = new_state.ffi /\
        evaluate_decs env removed_state removed_decs =
            (new_removed_state, new_ctors, result)`,
    Induct_on `decs`
    >- (rw[evaluate_decs_def, removeUnreachable_def] >>
        fs[evaluate_decs_def, findResultGlobals_def, flat_state_rel_def])
    >>  fs[evaluate_decs_def, removeUnreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (fs[evaluate_decs_def] >>
            `∃ r . evaluate_dec env state' h = r` by simp[] >>
            PairCases_on `r` >> fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by
                (CCONTR_TAC >> fs[]) >>
            drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >>
            rw[] >> fs[] >>
            pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[] >>
            `decsClosed reachable [h]` by imp_res_tac decsClosed_reduce_HD >>
            fs[] >>
            reverse(Cases_on `r2` >> fs[] >> rw[] >> rveq >> EVERY_CASE_TAC)
            >- fs[flat_state_rel_def] >>
            fs[] >> first_x_assum drule >> fs[] >> rveq >> strip_tac >>
            pop_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
            fs[] >>
            reverse(impl_tac) >- rw[] >> fs[findEnvGlobals_def] >>
            imp_res_tac decsClosed_reduce)
        >>  reverse(EVERY_CASE_TAC) >> fs[] >> rveq >>
            rename1 `_ _ decs = (n_state, ctors, res)` >>
            imp_res_tac keep_Dlet >> rveq >>
            fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >>
            rveq >> rw[UNION_EMPTY] >>
            `env with c updated_by $UNION {} = env` by
                fs[environment_component_equality] >> fs[]
            >- (drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                strip_tac >>
                pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
                strip_tac >> fs[])
            >>  first_x_assum match_mp_tac >> fs[] >> asm_exists_tac >> fs[] >>
                imp_res_tac decsClosed_reduce >> fs[] >>
                drule evaluate_sing_notKeep_flat_state_rel >> fs[]
);

val flat_removal_thm = Q.store_thm ("flat_removal_thm",
    `∀ exh_pat check_ctor ffi k decs new_state new_ctors result roots tree
        reachable removed_decs .
        evaluate_decs (initial_env exh_pat check_ctor)
            (initial_state ffi k) decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ exh_pat ∧
        (roots, tree) = analyseCode decs ∧
        reachable = closure_spt roots (mk_wf_set_tree tree) ∧
        removeUnreachable reachable decs = removed_decs
    ⇒ ∃ s .
        s.ffi = new_state.ffi /\
        evaluate_decs (initial_env exh_pat check_ctor) (initial_state ffi k)
            removed_decs = (s, new_ctors, result)`
  ,
    rpt strip_tac >> drule flat_decs_removal_lemma >>
    rpt (disch_then drule) >> strip_tac >>
    pop_assum (qspecl_then
        [`reachable`, `removed_decs`, `initial_state ffi k`] mp_tac) >> fs[] >>
    reverse(impl_tac) >- (rw[] >> fs[])
    >>  qspecl_then [`decs`, `roots`, `mk_wf_set_tree tree`, `tree`]
            mp_tac analysis_reachable_thm >>
        impl_tac >> rw[initial_env_def, initial_state_def]
        >- (fs[flat_state_rel_def, globals_rel_def] >> fs[findRefsGlobals_def])
        >- (fs[findEnvGlobals_def, findVglobals_def])
        >- (fs[decsClosed_def] >> rw[] >> `(r,t) = (roots, tree)` by
            metis_tac[] >> fs[] >> rveq
            >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[isReachable_def])
            >- (qexists_tac `n'` >> fs[isReachable_def] >>
                metis_tac[transitive_RTC, transitive_def]))
);

val flat_remove_eval_sim = Q.store_thm("flat_remove_eval_sim",
  `eval_sim ffi T T ds1 T T (removeFlatProg ds1)
                            (\d1 d2. d2 = removeFlatProg d1) F`,
  rw [eval_sim_def] \\ qexists_tac `0` \\ fs [removeFlatProg_def]
  \\ pairarg_tac \\ fs []
  \\ drule flat_removal_thm \\ rw [] \\ fs []);

val flat_remove_semantics = save_thm ("flat_remove_semantics",
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           flat_remove_eval_sim |> SIMP_RULE (srw_ss()) []);

(* syntactic results *)

val elist_globals_filter = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) = {||}`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

val esgc_free_filter = Q.prove (
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds)))`,
  Induct_on `ds` \\ rw []);

val elist_globals_filter_SUB_BAG = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

val removeFlatProg_elist_globals_eq_empty = Q.store_thm (
  "removeFlatProg_elist_globals_eq_empty",
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))) = {||}`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter]);

val removeFlatProg_esgc_free = Q.store_thm ("removeFlatProg_esgc_free",
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds)))`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [esgc_free_filter]);

val removeFlatProg_sub_bag = Q.store_thm ("removeFlatProg_sub_bag",
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter_SUB_BAG]);

val removeFlatProg_distinct_globals = Q.store_thm (
  "removeFlatProg_distinct_globals",
  `BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT (elist_globals
     (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))))`,
  metis_tac [removeFlatProg_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]);


val _ = export_theory();
