(*
  Correctness proof for flatLang dead code elimination
*)
open preamble sptreeTheory flatLangTheory flat_elimTheory
     flatSemTheory flatPropsTheory

val _ = new_theory "flat_elimProof";

val grammar_ancestry =
  ["flat_elim", "flatSem", "flatLang", "flatProps",
    "misc", "ffi", "sptree"];

val _ = set_grammar_ancestry grammar_ancestry;


(**************************** ANALYSIS LEMMAS *****************************)

Theorem wf_find_loc_wf_find_locL:
     (∀ e locs . find_loc  e = locs ⇒ wf locs) ∧
    (∀ l locs . find_locL l = locs ⇒ wf locs)
Proof
    ho_match_mp_tac find_loc_ind >> rw[find_loc_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarInit op` >> fs[wf_insert]
QED

Theorem wf_find_locL:
     ∀ l . wf(find_locL l)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_loc:
     ∀ e . wf(find_loc e)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_lookups_wf_find_lookupsL:
     (∀ e lookups . find_lookups e = lookups ⇒ wf lookups) ∧
    (∀ l lookups . find_lookupsL l = lookups ⇒ wf lookups)
Proof
    ho_match_mp_tac find_lookups_ind >>
    rw[find_lookups_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarLookup op` >> fs[wf_insert]
QED

Theorem wf_find_lookupsL:
     ∀ l . wf(find_lookupsL l)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED

Theorem wf_find_lookups:
     ∀ e . wf(find_lookups e)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED

Theorem find_lookupsL_MEM:
     ∀ e es . MEM e es ⇒ domain (find_lookups e) ⊆ domain (find_lookupsL es)
Proof
    Induct_on `es` >> rw[] >> fs[find_lookups_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
QED

Theorem find_lookupsL_APPEND:
     ∀ l1 l2 . find_lookupsL (l1 ++ l2) =
        union (find_lookupsL l1) (find_lookupsL l2)
Proof
    Induct >> fs[find_lookups_def] >> fs[union_assoc]
QED

Theorem find_lookupsL_REVERSE:
     ∀ l . find_lookupsL l = find_lookupsL (REVERSE l)
Proof
    Induct >> fs[find_lookups_def] >>
    fs[find_lookupsL_APPEND, find_lookups_def, union_num_set_sym]
QED

Theorem find_loc_EVERY_isEmpty:
     ∀ l reachable:num_set .
        EVERY (λ e . isEmpty (inter (find_loc e) reachable)) l
      ⇔ isEmpty (inter (find_locL l) reachable)
Proof
    Induct >- fs[Once find_loc_def, inter_def]
    >> fs[EVERY_DEF] >> rw[] >> EQ_TAC >> rw[] >>
       qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
       fs[inter_union_empty]
QED

Theorem wf_analyse_exp:
     ∀ e roots tree . analyse_exp e = (roots, tree) ⇒ (wf roots) ∧ (wf tree)
Proof
    simp[analyse_exp_def] >> rw[] >>
    metis_tac[
        wf_def, wf_map, wf_union, wf_find_loc, wf_find_lookups_wf_find_lookupsL]
QED

Theorem analyse_exp_domain:
     ∀ e roots tree . analyse_exp e = (roots, tree)
  ⇒ (domain roots ⊆ domain tree)
Proof
    simp[analyse_exp_def] >> rw[] >> rw[domain_def, domain_map]
QED




(**************************** ELIMINATION LEMMAS *****************************)

Theorem keep_Dlet:
     ∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x
Proof
   Cases_on `h` >> rw[keep_def]
QED

Theorem num_set_tree_union_empty:
     ∀ t1 t2 . isEmpty(num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2
Proof
    Induct >> rw[num_set_tree_union_def] >> CASE_TAC >>
    rw[num_set_tree_union_def]
QED

Theorem wf_num_set_tree_union:
     ∀ t1 t2 result . wf t1 ∧ wf t2 ∧ num_set_tree_union t1 t2 = result
  ⇒ wf result
Proof
    Induct >> rw[num_set_tree_union_def, wf_def] >> rw[wf_def] >>
    TRY(CASE_TAC) >>
    rw[wf_def] >>
    TRY(metis_tac[wf_def, num_set_tree_union_empty])
QED

Theorem domain_num_set_tree_union:
     ∀ t1 t2 . domain (num_set_tree_union t1 t2) = domain t1 ∪ domain t2
Proof
    Induct >> rw[num_set_tree_union_def, domain_def] >> CASE_TAC >>
    rw[domain_def, domain_union] >> rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    rw[UNION_ASSOC] >> rw[UNION_COMM] >>
    metis_tac[UNION_ASSOC, UNION_COMM, UNION_IDEMPOT]
QED

Theorem num_set_tree_union_sym:
     ∀ (t1 : num_set num_map) t2 .
        num_set_tree_union t1 t2 = num_set_tree_union t2 t1
Proof
    Induct >> rw[num_set_tree_union_def] >>
    Cases_on `t2` >> fs[num_set_tree_union_def] >>
    fs[union_num_set_sym]
QED

Theorem lookup_domain_num_set_tree_union:
     ∀ n (t1:num_set num_map) t2 x . lookup n t1 = SOME x
  ⇒ ∃ y . lookup n (num_set_tree_union t1 t2) = SOME y ∧ domain x ⊆ domain y
Proof
    Induct_on `t1` >> rw[]
    >- fs[lookup_def]
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >> Cases_on `EVEN n` >> fs[])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >>
        fs[lookup_def, domain_union] >>
        Cases_on `n = 0` >> fs[domain_union] >> Cases_on `EVEN n` >> fs[])
QED

Theorem lookup_NONE_num_set_tree_union:
     ∀ n (t1:num_set num_map) t2 . lookup n t1 = NONE
    ⇒ lookup n (num_set_tree_union t1 t2) = lookup n t2
Proof
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >> Cases_on `n = 0` >> fs[] >>
    Cases_on `EVEN n` >> fs[]
QED

Theorem lookup_SOME_SOME_num_set_tree_union:
     ∀ n (t1:num_set num_map) x1 t2 x2 .
    lookup n t1 = SOME x1 ∧ lookup n t2 = SOME x2
  ⇒ lookup n (num_set_tree_union t1 t2) = SOME (union x1 x2)
Proof
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >>
    Cases_on `EVEN n` >> fs[] >>
    Cases_on `n = 0` >> fs[]
QED

Theorem lookup_num_set_tree_union:
     ∀ (t1 : num_set num_map) t2 n .
        lookup n (num_set_tree_union t1 t2) = case (lookup n t1) of
            | NONE => lookup n t2
            | SOME s1 => case (lookup n t2) of
                | NONE => SOME s1
                | SOME s2 => SOME (union s1 s2)
Proof
    rw[] >> Cases_on `lookup n t1` >> fs[]
    >-  fs[lookup_NONE_num_set_tree_union]
    >- (Cases_on `lookup n t2` >> fs[]
        >- (fs[lookup_NONE_num_set_tree_union, num_set_tree_union_sym] >>
            imp_res_tac lookup_NONE_num_set_tree_union >>
            pop_assum (qspec_then `t1` mp_tac) >> rw[] >>
            fs[num_set_tree_union_sym])
        >-  fs[lookup_SOME_SOME_num_set_tree_union])
QED

Theorem wf_code_analysis_union:
     ∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3
Proof
    rw[code_analysis_union_def] >> rw[wf_union]
QED

Theorem wf_code_analysis_union_strong:
     ∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3
Proof
    rw[code_analysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
QED

Theorem domain_code_analysis_union:
     ∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3
Proof
    rw[code_analysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
QED

Theorem wf_code_analysis_union:
     ∀ r3 r2 r1 t1 t2 t3. wf r1 ∧ wf r2
        ∧ code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3
Proof
    rw[code_analysis_union_def] >> rw[wf_union]
QED

Theorem wf_code_analysis_union_strong:
     ∀ r3:num_set r2 r1 (t1:num_set num_map) t2 t3.
        wf r1 ∧ wf r2 ∧ wf t1 ∧ wf t2 ∧
        code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒  wf r3 ∧ wf t3
Proof
    rw[code_analysis_union_def] >> rw[wf_union] >>
    imp_res_tac wf_num_set_tree_union >> fs[]
QED

Theorem domain_code_analysis_union:
     ∀ r1:num_set r2 r3 (t1:num_set num_map) t2 t3 .
    domain r1 ⊆ domain t1 ∧ domain r2 ⊆ domain t2 ∧
    code_analysis_union (r1, t1) (r2, t2) = (r3, t3) ⇒ domain r3 ⊆ domain t3
Proof
    rw[code_analysis_union_def] >> rw[domain_union] >>
    rw[domain_num_set_tree_union] >> fs[SUBSET_DEF]
QED

Theorem analyse_code_thm:
     ∀ code root tree . analyse_code code = (root, tree)
    ⇒ (wf root) ∧ (domain root ⊆ domain tree)
Proof
    Induct
    >-(rw[analyse_code_def] >> rw[wf_def])
    >> Cases_on `h` >> simp[analyse_code_def] >> Cases_on `analyse_exp e` >>
       Cases_on `analyse_code code` >>
       first_x_assum (qspecl_then [`q'`, `r'`] mp_tac) >> simp[] >>
       qspecl_then [`e`, `q`, `r`] mp_tac wf_analyse_exp >> simp[] >> rw[]
       >- imp_res_tac wf_code_analysis_union
       >> qspecl_then [`e`, `q`, `r`] mp_tac analyse_exp_domain >> rw[] >>
          imp_res_tac domain_code_analysis_union
QED



(**************************** REACHABILITY LEMMAS *****************************)

Theorem subspt_superdomain:
   ∀ t1 a t2 . subspt (superdomain t1) (superdomain (BS t1 a t2)) ∧
               subspt (superdomain t2) (superdomain (BS t1 a t2)) ∧
               subspt a (superdomain (BS t1 a t2)) ∧
               subspt (superdomain t1) (superdomain (BN t1 t2)) ∧
               subspt (superdomain t2) (superdomain (BN t1 t2))
Proof
    fs[subspt_domain, superdomain_def] >>
    fs[SUBSET_DEF, domain_lookup, lookup_spt_fold_union_STRONG, lookup_def] >>
    rw[]
    >- (
      qexists_tac `2 * n1 + 2` >>
      fs[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT]
      )
    >- (
      qexists_tac `2 * n1 + 1` >>
      fs[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]
      )
    >- (
      qexists_tac `0` >>
      fs[]
      )
    >- (
      qexists_tac `2 * n1 + 2` >>
      fs[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT]
      )
    >- (
      qexists_tac `2 * n1 + 1` >>
      fs[EVEN_DOUBLE, EVEN_ADD] >>
      once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]
      )
QED

Theorem superdomain_thm:
   ∀ x y (tree : unit spt spt) . lookup x tree = SOME y
  ⇒ domain y ⊆ domain (superdomain tree)
Proof
    fs[superdomain_def, domain_lookup, SUBSET_DEF] >>
    fs[lookup_spt_fold_union_STRONG, lookup_def] >>
    rw[] >> metis_tac[]
QED

Theorem superdomain_inverse_thm:
   ∀ n tree . n ∈ domain (superdomain tree)
  ⇒ ∃ k aSet . lookup k tree = SOME aSet ∧ n ∈ domain aSet
Proof
    fs[superdomain_def, domain_lookup] >>
    fs[lookup_spt_fold_union_STRONG, lookup_def]
QED

Theorem superdomain_not_in_thm:
   ∀ n tree . n ∉ domain (superdomain tree)
  ⇒ ∀ k aSet . lookup k tree = SOME aSet ⇒ n ∉ domain aSet
Proof
    fs[superdomain_def, domain_lookup] >>
    fs[lookup_spt_fold_union_STRONG, lookup_def] >>
    rw[] >> metis_tac[]
QED

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

Theorem mk_wf_set_tree_domain:
     ∀ tree . domain tree ⊆ domain (mk_wf_set_tree tree)
Proof
    Induct >>
    rw[mk_wf_set_tree_def, domain_map, domain_mk_wf, domain_union, SUBSET_DEF]
QED

Theorem mk_wf_set_tree_thm:
     ∀ x tree . x = mk_wf_set_tree tree ⇒ wf_set_tree x
Proof
    rw[mk_wf_set_tree_def, wf_set_tree_def] >> fs[lookup_map] >>
    rw[domain_map, domain_union] >> fs[lookup_union] >>
    Cases_on `lookup x' tree` >> fs[] >- fs[lookup_map] >> rw[] >>
    qspecl_then [`x'`, `x`, `tree`] mp_tac superdomain_thm >> rw[SUBSET_DEF]
QED

Theorem lookup_mk_wf_set_tree:
     ∀ n tree x . lookup n tree = SOME x
  ⇒ ∃ y . lookup n (mk_wf_set_tree tree) = SOME y ∧ domain x = domain y
Proof
    rw[mk_wf_set_tree_def] >> rw[lookup_map] >> rw[lookup_union]
QED

Theorem lookup_domain_mk_wf_set_tree:
     ∀ n t x y . lookup n (mk_wf_set_tree t) = SOME x ⇒
        lookup n t = SOME y ⇒ domain y = domain x
Proof
    rw[mk_wf_set_tree_def] >> fs[lookup_map, lookup_union] >>
    metis_tac[domain_mk_wf]
QED

Theorem wf_close_spt:
     ∀ reachable seen tree. (wf reachable) ∧ (wf seen) ∧ (wf tree) ∧
        (∀ n x . (lookup n tree = SOME x) ⇒ wf x)
  ⇒ wf (close_spt reachable seen tree)
Proof
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
QED



(**************************** OTHER LEMMAS *****************************)

Theorem domain_superdomain_num_set_tree_union:
     ∀ t1 t2 . domain (superdomain t1)
        ⊆ domain (superdomain (num_set_tree_union t1 t2))
Proof
    fs[SUBSET_DEF] >> rw[] >> imp_res_tac superdomain_inverse_thm >>
    imp_res_tac lookup_domain_num_set_tree_union >>
    pop_assum (qspec_then `t2` mp_tac) >>
    rw[] >> imp_res_tac superdomain_thm >> metis_tac[SUBSET_DEF]
QED

Theorem domain_superdomain_num_set_tree_union_STRONG:
     ∀ t1 t2 . domain (superdomain t1) ∪ domain (superdomain t2) =
        domain (superdomain (num_set_tree_union t1 t2))
Proof
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
QED

Theorem mk_wf_set_tree_num_set_tree_union:
     ∀ t1 t2 . mk_wf_set_tree (num_set_tree_union t1 t2) =
        num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2)
Proof
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
QED



(************************** ADJACENCY/REACHABILITY ***************************)

val is_adjacent_def = Define `
    is_adjacent tree x y =
    ∃ aSetx aSety.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () ) ∧
        ( lookup y tree = SOME aSety )
`;

Theorem adjacent_domain:
     ∀ tree x y . is_adjacent tree x y ⇒ x ∈ domain tree ∧ y ∈ domain tree
Proof
    rw[is_adjacent_def] >> rw[domain_lookup]
QED

val is_reachable_def = Define `
    is_reachable tree = RTC (is_adjacent tree)
`;

Theorem reachable_domain:
     ∀ tree x y . is_reachable tree x y
  ⇒ (x = y ∨ (x ∈ domain tree ∧ y ∈ domain tree))
Proof
    simp[is_reachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    metis_tac[adjacent_domain]
QED

Theorem rtc_is_adjacent:
     s ⊆ t ∧ (∀ k . k ∈ t ⇒ ∀ n . (is_adjacent fullTree k n ⇒ n ∈ t)) ⇒
    ∀ x y . RTC(is_adjacent fullTree) x y ⇒ x ∈ s ⇒ y ∈ t
Proof
    strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    fs[SUBSET_DEF] >>
    metis_tac []
QED

Theorem is_adjacent_num_set_tree_union:
     ∀ t1 t2 n m .
        is_adjacent t1 n m ⇒ is_adjacent (num_set_tree_union t1 t2) n m
Proof
    rw[is_adjacent_def] >> imp_res_tac lookup_domain_num_set_tree_union >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    fs[SUBSET_DEF, domain_lookup]
QED

Theorem is_adjacent_wf_set_tree_num_set_tree_union:
     ∀ t1 t2 n m .
        is_adjacent (mk_wf_set_tree t1) n m
        ⇒ is_adjacent (mk_wf_set_tree (num_set_tree_union t1 t2)) n m
Proof
    rw[is_adjacent_def] >> fs[mk_wf_set_tree_def] >> fs[lookup_map] >>
    fs[lookup_union] >> fs[lookup_map] >> fs[PULL_EXISTS] >>
    fs[lookup_num_set_tree_union] >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[] >>
    rveq >> fs[lookup_def, mk_wf_def, lookup_union] >>
    EVERY_CASE_TAC >> fs[] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union >>
    rw[SUBSET_DEF, domain_lookup]
QED

Theorem is_reachable_wf_set_tree_num_set_tree_union:
     ∀ t1 t2 n m .
        is_reachable (mk_wf_set_tree t1) n m
      ⇒ is_reachable (mk_wf_set_tree (num_set_tree_union t1 t2)) n m
Proof
    simp[is_reachable_def] >> strip_tac >> strip_tac >>
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
    simp[Once RTC_CASES2] >> disj2_tac >> qexists_tac `m` >> fs[] >>
    imp_res_tac is_adjacent_wf_set_tree_num_set_tree_union >> fs[]
QED



(************************** DEFINITIONS ***************************)

Theorem SUM_MAP_v3_size:
  !xs. SUM (MAP v3_size xs) = LENGTH xs +
    SUM (MAP (list_size char_size ∘ FST) xs) +
    SUM (MAP (v_size ∘ SND) xs)
Proof
  Induct \\ simp [FORALL_PROD, v_size_def]
QED

Definition find_v_globals_def:
    (find_v_globals (Conv _ vl) = (find_v_globalsL vl):num_set) ∧
    (find_v_globals (Closure env _ e) =
        union (find_v_globalsL (MAP SND env.v)) (find_lookups e)) ∧
    (find_v_globals (Recclosure env vves _) =
        union (find_v_globalsL (MAP SND env.v))
            (find_lookupsL (MAP (SND o SND) vves))) ∧
    (find_v_globals (Vectorv vl) = find_v_globalsL vl) ∧
    (find_v_globals _ = LN) ∧
    (find_v_globalsL [] = LN) ∧
    (find_v_globalsL (h::t) = union (find_v_globals h) (find_v_globalsL t))
Termination
    WF_REL_TAC `measure (λ e . case e of
            | INL x => v_size x
            | INR y => v4_size y)` >>
    rw[v_size_def, v_size_aux, SUM_MAP_v3_size, MAP_MAP_o]
End

val find_v_globals_ind = theorem "find_v_globals_ind";

Theorem find_v_globalsL_APPEND:
     ∀ l1 l2 . find_v_globalsL (l1 ++ l2) =
        union (find_v_globalsL l1) (find_v_globalsL l2)
Proof
    Induct >> fs[find_v_globals_def] >> fs[union_assoc]
QED

Theorem find_v_globalsL_REVERSE:
     ∀ l . find_v_globalsL l = find_v_globalsL (REVERSE l)
Proof
    Induct >> fs[find_v_globals_def] >>
    fs[find_v_globalsL_APPEND, union_num_set_sym, find_v_globals_def]
QED

Theorem find_v_globalsL_MEM:
     ∀ k v vs . MEM (k, v) vs
  ⇒ domain (find_v_globals v) ⊆ domain (find_v_globalsL (MAP SND vs))
Proof
    Induct_on `vs` >> rw[] >> fs[find_v_globals_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
QED

Theorem find_v_globalsL_EL:
     ∀ n vs . n < LENGTH vs ⇒
    domain (find_v_globals (EL n vs)) ⊆ domain(find_v_globalsL vs)
Proof
    Induct >> fs[EL] >> rw[] >> Cases_on `vs` >>
    fs[find_v_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[] >>  fs[EXTENSION, SUBSET_DEF]
QED

Theorem find_v_globals_MAP_Recclosure:
    ∀ funs v l.
    domain (find_v_globalsL (MAP (λx. Recclosure env l (f x)) funs)) =
    (if NULL funs then {}
        else domain (find_v_globalsL (MAP SND env.v)) ∪
            domain (find_lookupsL (MAP (SND o SND) l)))
Proof
    Induct >> fs[find_v_globals_def] >> rw[domain_union]
QED

Theorem find_v_globalsL_REPLICATE:
     ∀ n v vs . domain (find_v_globalsL (REPLICATE n v)) ⊆
        domain (find_v_globals v)
Proof
    Induct >> fs[REPLICATE, find_v_globals_def, domain_union]
QED

Theorem find_v_globalsL_LUPDATE:
     ∀ n vs (reachable:num_set) v . n < LENGTH vs ∧
    domain (find_v_globalsL vs) ⊆ domain reachable ∧
    domain (find_v_globals v) ⊆ domain reachable
  ⇒ domain (find_v_globalsL (LUPDATE v n vs)) ⊆ domain reachable
Proof
    Induct_on `vs` >> rw[] >> Cases_on `n` >> fs[LUPDATE_def] >>
    fs[find_v_globals_def, domain_union]
QED

Theorem find_v_globals_v_to_list:
     ∀ x reachable xs .
        domain (find_v_globals x) ⊆ domain reachable ∧ v_to_list x = SOME xs
    ⇒ domain (find_v_globalsL xs) ⊆ domain reachable
Proof
    recInduct v_to_list_ind >>
    fs[v_to_list_def, find_v_globals_def, domain_union] >> rw[] >>
    Cases_on `v_to_list v2` >> fs[] >> rveq >>
    fs[find_v_globals_def, domain_union] >> metis_tac[]
QED

Theorem find_v_globals_list_to_v:
     ∀ xs reachable x .
        domain (find_v_globalsL xs) ⊆ domain reachable ∧ list_to_v xs = x
    ⇒ domain (find_v_globals x) ⊆ domain reachable
Proof
    Induct >> fs[list_to_v_def, find_v_globals_def, domain_union]
QED

val find_refs_globals_def = Define `
    (find_refs_globals (Refv a::t) =
        union (find_v_globals a) (find_refs_globals t)) ∧
    (find_refs_globals (Varray l::t) =
        union (find_v_globalsL l) (find_refs_globals t)) ∧
    (find_refs_globals (_::t) = find_refs_globals t) ∧
    (find_refs_globals [] = LN)
`

val find_refs_globals_ind = theorem "find_refs_globals_ind";

Theorem find_refs_globals_EL:
     ∀ n l . n < LENGTH l ⇒
        (∀ a . EL n l = Refv a
            ⇒ domain (find_v_globals a) ⊆ domain (find_refs_globals l)) ∧
        (∀ vs . EL n l = Varray vs
            ⇒ domain (find_v_globalsL vs) ⊆ domain (find_refs_globals l))
Proof
    Induct >> rw[]
    >- (Cases_on `l` >> fs[find_refs_globals_def, domain_union])
    >- (Cases_on `l` >> fs[find_refs_globals_def, domain_union])
    >> fs[EL] >> first_x_assum (qspec_then `TL l` mp_tac) >> rw[] >>
       `n < LENGTH (TL l)` by fs[LENGTH_TL] >> fs[] >>
       Cases_on `l` >> fs[] >>
       Cases_on `h` >> fs[find_refs_globals_def, domain_union, SUBSET_DEF]
QED

Theorem find_refs_globals_MEM:
     ∀ refs reachable:num_set .
        domain (find_refs_globals refs) ⊆ domain reachable
      ⇒ (∀ a . MEM (Refv a) refs
            ⇒ domain (find_v_globals a) ⊆ domain reachable) ∧
        (∀ vs . MEM (Varray vs) refs
            ⇒ domain (find_v_globalsL vs) ⊆ domain reachable)
Proof
    Induct >> rw[] >> fs[find_refs_globals_def, domain_union] >>
    Cases_on `h` >> fs[find_refs_globals_def, domain_union]
QED

Theorem find_refs_globals_LUPDATE:
     ∀ reachable:num_set refs n .
        n < LENGTH refs ∧ domain (find_refs_globals refs) ⊆ domain reachable
      ⇒
        (∀ a . domain (find_v_globals a) ⊆ domain reachable
            ⇒ domain (find_refs_globals (LUPDATE (Refv a) n refs))
                ⊆ domain reachable) ∧
    (∀ vs . domain (find_v_globalsL vs) ⊆ domain reachable
        ⇒ domain (find_refs_globals (LUPDATE (Varray vs) n  refs))
            ⊆ domain reachable) ∧
    (∀ ws. domain (find_refs_globals (LUPDATE (W8array ws) n refs))
        ⊆ domain reachable)
Proof
    Induct_on `refs` >> rw[] >> Cases_on `h` >>
    fs[find_refs_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, find_refs_globals_def, domain_union] >>
    fs[domain_union, LUPDATE_def] >> Cases_on `n` >> fs[] >>
    fs[LUPDATE_def, find_refs_globals_def, domain_union]
QED

Theorem find_refs_globals_APPEND:
     ∀ refs new . find_refs_globals (refs ++ new) =
        union (find_refs_globals refs) (find_refs_globals new)
Proof
    Induct >> rw[] >> fs[find_refs_globals_def] >>
    Cases_on `h` >> fs[find_refs_globals_def] >> fs[union_assoc]
QED

val find_env_globals_def = Define `
    find_env_globals env = find_v_globalsL (MAP SND env.v)
`

val find_result_globals_def = Define `
    (find_result_globals (SOME (Rraise v)) = find_v_globals v) ∧
    (find_result_globals _ = LN)
`

val find_result_globals_ind = theorem "find_result_globals_ind";

val find_sem_prim_res_globals_def = Define `
    (find_sem_prim_res_globals (Rerr e :
        (flatSem$v list, flatSem$v) semanticPrimitives$result) =
        find_result_globals (SOME e)) ∧
    (find_sem_prim_res_globals (Rval e) = find_v_globalsL e)
`

val s =  ``s:('c,'ffi) state``
val t = mk_var ("t", type_of s)
val new_state = mk_var ("new_state", type_of s);
val state = mk_var ("state", type_of s);

Definition v_has_Eval_def1:
  (v_has_Eval (Closure env _ e) = (has_Eval e ∨
    EXISTS v_has_Eval (MAP SND env.v))) ∧
  (v_has_Eval (Conv _ vl) = EXISTS v_has_Eval vl) ∧
  (v_has_Eval (Recclosure env nm_es _) =
    (EXISTS v_has_Eval (MAP SND env.v) ∨
      EXISTS has_Eval (MAP (SND o SND) nm_es))) ∧
  (v_has_Eval (Vectorv vl) = EXISTS v_has_Eval vl) ∧
  (v_has_Eval _ = F)
Termination
  WF_REL_TAC `measure (λe. v_size e)`
  \\ rw [v_size_def]
  \\ fs [v_size_aux, MEM_MAP, EXISTS_PROD, MEM_SPLIT, SUM_APPEND, v_size_def]
End

Theorem v_has_Eval_def = CONV_RULE (DEPTH_CONV ETA_CONV) v_has_Eval_def1

(* s = state, t = removed state *)
val globals_rel_def = Define `
    globals_rel
      (reachable : num_set) ^s ^t ⇔
        LENGTH s.globals = LENGTH t.globals ∧
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t.globals
          ⇒ EL n s.globals = EL n t.globals) ∧
        (∀ n x . n < LENGTH t.globals ∧ EL n t.globals = SOME x
          ⇒ EL n s.globals = SOME x) ∧
        (∀ n . n < LENGTH t.globals ∧ EL n s.globals = NONE
          ⇒ EL n t.globals = NONE) ∧
        (∀ n x . n ∈ domain reachable ∧ n < LENGTH t.globals ∧
          EL n t.globals = SOME x
            ⇒ ~ v_has_Eval x ∧ domain (find_v_globals x) ⊆ domain reachable)
`

Theorem globals_rel_trans:
     ∀ reachable s1 s2 s3 .
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3
Proof
    rw[globals_rel_def]
QED

val decs_closed_def = Define `
    decs_closed (reachable : num_set) decs ⇔  ∀ r t . analyse_code decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ is_reachable (mk_wf_set_tree t) n m
      ⇒ m ∈ domain reachable)
`

Theorem decs_closed_reduce:
     ∀ reachable h t . decs_closed reachable (h::t) ⇒ decs_closed reachable t
Proof
    fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def]
    >- (Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union])
    >- (Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >> pop_assum match_mp_tac >>
        assume_tac is_reachable_wf_set_tree_num_set_tree_union >> fs[] >>
        fs[Once num_set_tree_union_sym])
    >> metis_tac[]
QED

Theorem decs_closed_reduce_HD:
     ∀ reachable h t .
        decs_closed reachable (h::t) ⇒ decs_closed reachable [h]
Proof
    fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def] >>
    Cases_on `analyse_exp e` >>
    fs[code_analysis_union_def, domain_union] >> rveq >> fs[domain_def]
    >- (Cases_on `analyse_code t` >> fs[code_analysis_union_def, domain_union])
    >- (fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
        Cases_on `analyse_code t` >>
        fs[code_analysis_union_def, domain_union] >>
        imp_res_tac is_reachable_wf_set_tree_num_set_tree_union >>
        pop_assum (qspec_then `r` mp_tac) >> strip_tac >> res_tac)
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
    >- (fs[EVAL ``mk_wf_set_tree LN``] >>
        imp_res_tac reachable_domain >> fs[domain_def])
QED

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable ^s ^t ⇔
      s.clock = t.clock ∧ s.refs = t.refs ∧
      s.ffi = t.ffi ∧ globals_rel reachable s t ∧
      s.c = t.c ∧
      domain (find_refs_globals s.refs) ⊆ domain reachable ∧
      EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs
`

Theorem flat_state_rel_trans:
  ∀ reachable s1 s2 s3 .
    flat_state_rel reachable s1 s2 ∧
    flat_state_rel reachable s2 s3
  ⇒ flat_state_rel reachable s1 s3
Proof
  rw[flat_state_rel_def, globals_rel_def]
QED

(**************************** FLATLANG LEMMAS *****************************)

Theorem pmatch_Match_reachable:
     (∀ env ^s p v l a reachable:num_set . pmatch env s p v l = Match a ∧
        domain (find_v_globals v) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals s.refs) ⊆ domain reachable
    ⇒ domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)
  ∧
    (∀ env ^s p vs l a reachable:num_set .
        pmatch_list env s p vs l = Match a ∧
        domain (find_v_globalsL vs) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals s.refs) ⊆ domain reachable
    ⇒ domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)
Proof
    ho_match_mp_tac pmatch_ind >> rw[pmatch_def] >>
    fs[find_v_globals_def, domain_union]
    >- (Cases_on `store_lookup lnum s.refs` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[semanticPrimitivesTheory.store_lookup_def] >>
        first_x_assum (qspec_then `reachable` match_mp_tac) >> rw[] >>
        imp_res_tac find_refs_globals_EL >> metis_tac[SUBSET_TRANS]) >>
    Cases_on `pmatch env s p v l` >> fs[domain_union,CaseEq"match_result"]
QED

Theorem find_v_globals_list_to_v_APPEND:
     ∀ xs reachable ys .
        domain (find_v_globalsL xs) ⊆ domain reachable ∧
        domain(find_v_globalsL ys) ⊆ domain reachable
    ⇒ domain (find_v_globals (list_to_v (xs ++ ys))) ⊆ domain reachable
Proof
    Induct >> fs[list_to_v_def, find_v_globals_def, domain_union] >>
    metis_tac[find_v_globals_list_to_v]
QED

Theorem find_v_globals_Unitv[simp]:
   find_v_globals Unitv = LN
Proof
  EVAL_TAC
QED

Theorem EVERY_EL_IMP:
  EVERY P xs /\ n < LENGTH xs ==> P (EL n xs)
Proof
  simp [EVERY_EL]
QED

val v_has_Eval_Unitv = EVAL ``v_has_Eval Unitv``;

Theorem v_has_Eval_list_to_v:
  v_has_Eval (list_to_v xs) = EXISTS v_has_Eval xs
Proof
  Induct_on `xs` \\ fs [list_to_v_def, v_has_Eval_def]
QED

Theorem v_has_Eval_v_to_list:
  !v xs. v_to_list v = SOME xs ==> v_has_Eval v = EXISTS v_has_Eval xs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ simp [v_to_list_def, v_has_Eval_def]
  \\ rw [option_case_eq, PULL_EXISTS]
  \\ rfs []
QED

Theorem do_app_SOME_flat_state_rel:
     ∀ reachable state removed_state op l new_state result new_removed_state.
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧
        domain(find_v_globalsL l) ⊆ domain reachable ∧
        domain (find_lookups (App tra op [])) ⊆ domain reachable ∧
        EVERY ($~ ∘ v_has_Eval) l
          ⇒ do_app state op l = SOME (new_state, result) ∧
            result ≠ Rerr (Rabort Rtype_error)
            ⇒ ∃ new_removed_state .
                flat_state_rel reachable new_state new_removed_state ∧
                do_app removed_state op l =
                    SOME (new_removed_state, result) ∧
                domain (find_sem_prim_res_globals (list_result result)) ⊆
                    domain reachable ∧
                EVERY ($~ ∘ v_has_Eval) (result_vs (list_result result))
Proof
    rw[] >> qpat_x_assum `flat_state_rel _ _ _` mp_tac >>
    simp[Once flat_state_rel_def] >> strip_tac >>
    `∃ this_case . this_case op` by (qexists_tac `K T` >> simp[]) >>
    reverse (Cases_on `op`) >> fs[]
    >- (rename [`El`]
        \\ fs [do_app_def,CaseEq"list",CaseEq"lit",CaseEq"v"] \\ rveq \\ fs []
        \\ fs [flat_state_rel_def,find_v_globals_def,find_sem_prim_res_globals_def]
        THEN1
         (fs [v_has_Eval_def]
          \\ drule_then drule EVERY_EL_IMP
          \\ rw []
          \\ rename [`domain (find_v_globalsL xs) ⊆ domain reachable`]
          \\ qpat_x_assum `domain (find_v_globalsL xs) ⊆ domain reachable` mp_tac
          \\ qpat_x_assum `n < LENGTH xs` mp_tac
          \\ qid_spec_tac `n`
          \\ qid_spec_tac `xs`
          \\ Induct \\ fs [find_v_globals_def,domain_union,v_has_Eval_def]
          \\ strip_tac \\ Cases \\ fs [])
        \\ fs [CaseEq"option",CaseEq"store_v"] \\ rveq \\ fs []
        \\ fs [find_sem_prim_res_globals_def,find_v_globals_def]
        \\ rfs [semanticPrimitivesTheory.store_alloc_def,
              semanticPrimitivesTheory.store_lookup_def,
              chr_exn_v_def, Boolv_def, div_exn_v_def]
        \\ drule_then drule EVERY_EL_IMP
        \\ rw []
        \\ match_mp_tac SUBSET_TRANS
        \\ once_rewrite_tac [CONJ_COMM]
        \\ asm_exists_tac \\ asm_rewrite_tac []
        \\ drule EL_MEM
        \\ fs [MEM_SPLIT] \\ rveq \\ fs [] \\ strip_tac \\ rveq
        \\ fs [find_refs_globals_APPEND,find_refs_globals_def,domain_union]
        \\ fs [SUBSET_DEF])
    >- (rename [`TagLenEq`]
        \\ fs [do_app_def,CaseEq"list",CaseEq"lit",CaseEq"v",CaseEq"option",
               pair_case_eq] \\ rveq \\ fs []
        \\ fs [flat_state_rel_def,find_v_globals_def,find_sem_prim_res_globals_def]
        \\ rw [Boolv_def]  \\ EVAL_TAC)
    >- (rename [`Eval`]
        \\ fs [do_app_def]
    )
    >- (fs[do_app_def] >> Cases_on `l` >> fs[find_v_globals_def] >>
        rveq >> fs[flat_state_rel_def] >>
        fs[find_lookups_def, dest_GlobalVarLookup_def] >>
        fs[find_sem_prim_res_globals_def] >>
        Cases_on `EL n new_state.globals` >> fs[] >> res_tac >>
        Cases_on `EL n removed_state.globals` >> fs[find_v_globals_def] >>
        fs[globals_rel_def] >> res_tac >> fs[] >> rveq >> metis_tac[])
    >- (fs[do_app_def] >> Cases_on `l` >> fs[find_v_globals_def] >>
        Cases_on `t` >> fs[] >>
        rveq >> fs[flat_state_rel_def, globals_rel_def] >> rfs[] >>
        fs[EL_LUPDATE] >> rw[] >>
        fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
        fs[v_has_Eval_def, Unitv_def] >>
        metis_tac[]) >>
    fs[do_app_cases] >> rveq >> fs[] >> rw[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        find_result_globals_def] >>
    fs[semanticPrimitivesTheory.store_assign_def,
       semanticPrimitivesTheory.store_v_same_type_def, subscript_exn_v_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,
       semanticPrimitivesTheory.store_lookup_def,
       chr_exn_v_def, Boolv_def, div_exn_v_def] >>
    simp [v_has_Eval_Unitv, v_has_Eval_def] >>
    fs[flat_state_rel_def, find_v_globals_def,
       domain_union, find_refs_globals_def] >> rveq >> rfs[globals_rel_def]
    (* 26 subgoals *)
    >- (
        rw[] >> Cases_on `n' < LENGTH removed_state.globals` >> rveq >>
        fs[EL_APPEND1, EL_APPEND2, EL_REPLICATE] >>
        TRY (`n' - LENGTH removed_state.globals < n` by fs[]) >>
        fs[EL_APPEND1, EL_APPEND2, EL_REPLICATE] >>
        metis_tac[EL_APPEND1]
    )
    >- (simp [listTheory.IMP_EVERY_LUPDATE] >>
            metis_tac[find_refs_globals_LUPDATE, IMP_EVERY_LUPDATE])
    >-  metis_tac[find_v_globals_v_to_list, find_v_globals_list_to_v_APPEND]
    >- (imp_res_tac v_has_Eval_v_to_list \\ fs [v_has_Eval_list_to_v])
    >- (fs [integerTheory.INT_NOT_LT]
        \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ rveq \\ fs []
        \\ fs [GREATER_EQ,GSYM NOT_LESS]
        \\ rename [`LUPDATE (Varray (LUPDATE v6 n6 vs)) lnum6`]
        \\ drule_then drule EVERY_EL_IMP
        \\ simp [store_v_vs_def, IMP_EVERY_LUPDATE]
        \\ qsuff_tac `domain (find_v_globalsL (LUPDATE v6 n6 vs)) ⊆ domain reachable`
        >-  metis_tac[find_refs_globals_LUPDATE]
        >>  match_mp_tac find_v_globalsL_LUPDATE >> fs[] >>
            imp_res_tac EL_MEM >> rfs[] >>
            fs[find_refs_globals_def] >> metis_tac[find_refs_globals_MEM])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (imp_res_tac find_refs_globals_EL >>
        `domain (find_v_globals (EL (Num (ABS i'''''')) vs))
            ⊆ domain (find_v_globalsL vs)` by
            (match_mp_tac find_v_globalsL_EL >> decide_tac) >>
             metis_tac[SUBSET_TRANS])
    >- (drule_then drule EVERY_EL_IMP \\ simp [EVERY_EL])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >- metis_tac[] >>
        fs[find_refs_globals_APPEND, domain_union, find_refs_globals_def,
            EVERY_REPLICATE] >>
        metis_tac[find_v_globalsL_REPLICATE,SUBSET_TRANS])
    >- (fs [integerTheory.INT_NOT_LT]
        \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ rveq \\ fs []
        \\ fs [GREATER_EQ,GSYM NOT_LESS]
        \\ metis_tac[find_v_globalsL_EL, SUBSET_DEF])
    >- (fs [v_has_Eval_def, EVERY_EL])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (metis_tac[find_v_globals_v_to_list, SUBSET_DEF])
    >- (imp_res_tac v_has_Eval_v_to_list \\ fs[])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (fs [v_has_Eval_def]
        \\ rename [`find_v_globals (list_to_v (MAP (λc. Litv (Char c)) ss))`]
        \\ `find_v_globals (list_to_v (MAP (λc. Litv (Char c)) ss)) = LN` by
             (Induct_on `ss` \\ fs [list_to_v_def,find_v_globals_def])
        \\ fs [])
    >- simp [v_has_Eval_list_to_v, EVERY_MAP, v_has_Eval_def]
    >- (rw[IMP_EVERY_LUPDATE] >> metis_tac[find_refs_globals_LUPDATE])
    >- (rw[IMP_EVERY_LUPDATE] >> metis_tac[find_refs_globals_LUPDATE])
    >- (rw[IMP_EVERY_LUPDATE] >> metis_tac[find_refs_globals_LUPDATE])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (fs[find_refs_globals_APPEND, domain_union, find_refs_globals_def] >>
        metis_tac[])
    >- (rw[] >>
        fs[find_refs_globals_APPEND, find_refs_globals_def,
           find_v_globals_def, domain_union] >> res_tac)
    >- (rw[IMP_EVERY_LUPDATE] >> metis_tac[find_refs_globals_LUPDATE])
QED



(**************************** MAIN LEMMAS *****************************)

Theorem close_spt_thm:
     ∀ reachable seen tree closure (roots : num set) .
        (wf reachable) ∧ (wf seen) ∧ (wf_set_tree tree) ∧
        (close_spt reachable seen tree = closure) ∧
        (subspt reachable seen) ∧
        (roots ⊆ domain (seen)) ∧
        (domain seen ⊆ domain tree) ∧
        (∀ k . k ∈ domain (seen)
            ⇒ (∃ n . (n ∈ roots) ∧ (is_reachable tree n k))) ∧
        (∀ k . k ∈ domain (reachable)
            ⇒ (∀ a . (is_adjacent tree k a) ⇒ a ∈ domain (seen)))
      ⇒ (domain closure = {a | ∃ n . (is_reachable tree n a) ∧ (n ∈ roots)})
Proof
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
                (rtc_is_adjacent |> GEN_ALL) >>
            strip_tac >> fs[] >>
            fs[is_reachable_def] >>
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
                fs[subspt_lookup, lookup_inter, domain_difference] >> rw[] >>
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
            fs[is_reachable_def] >>
            simp[Once RTC_CASES2] >>
            DISJ2_TAC >>
            qexists_tac `n1` >> fs[] >>
            fs[is_adjacent_def]
            )
        >-  metis_tac[]
        >- (
            Cases_on `a ∈ domain seen` >> fs[] >>
            Cases_on `a ∈ domain reachable` >> rfs[]
            >-  metis_tac[]
            >>  `a ∈ domain tree` by fs[is_adjacent_def, domain_lookup] >>
                `k ∈ domain tree` by fs[is_adjacent_def, domain_lookup] >>
                `k ∈ domain (inter tree (difference seen reachable))` by
                    fs[domain_inter, domain_difference] >>
                fs[is_adjacent_def] >>
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
QED

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
                IN_SING, Once is_reachable_def, RTC_REFL, AND_CLAUSES
           ] |> GEN_ALL
;

Theorem closure_spt_thm:
     ∀ tree start . wf start ∧ (wf_set_tree tree) ∧
    (domain start ⊆ domain tree)
  ⇒ domain (closure_spt start tree) =
        {a | ∃ n . is_reachable tree n a ∧ n ∈ domain start}
Proof
    rw[] >> assume_tac closure_spt_lemma >> rw[] >> fs[wf_set_tree_def] >>
    first_x_assum match_mp_tac >> reverse(rw[]) >> res_tac >> fs[SUBSET_DEF] >>
    qexists_tac `k` >> fs[]
QED

Theorem analysis_reachable_thm:
    ∀ (compiled : dec list) start tree t .
        ((start, t) = analyse_code compiled) ∧
        (tree = mk_wf_set_tree t)
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . is_reachable tree n a ∧ n ∈ domain start}
Proof
    rw[] >> qspecl_then [`mk_wf_set_tree t`, `start`] mp_tac closure_spt_thm >>
    rw[] >> `wf_set_tree(mk_wf_set_tree t)` by metis_tac[mk_wf_set_tree_thm] >>
    qspecl_then [`compiled`, `start`, `t`] mp_tac analyse_code_thm >>
    qspec_then `t` mp_tac mk_wf_set_tree_domain >> rw[] >>
    metis_tac[SUBSET_TRANS]
QED

Theorem flat_state_rel_pmatch:
  (! c_env ^new_state p a env.
    flat_state_rel reachable new_state new_removed_state ==>
    pmatch c_env new_removed_state p a env =
    pmatch c_env new_state p a env) /\
  (! c_env ^new_state p a env.
    flat_state_rel reachable new_state new_removed_state ==>
    pmatch_list c_env new_removed_state p a env =
    pmatch_list c_env new_state p a env)
Proof
  ho_match_mp_tac pmatch_ind \\ rw []
  \\ fs [pmatch_def,flat_state_rel_def]
  \\ rw [] \\ fs [] \\ rpt (CASE_TAC \\ fs [])
QED

Theorem flat_state_rel_pmatch_rows:
  flat_state_rel reachable new_state new_removed_state ==>
  pmatch_rows c_env (pes: (pat # exp) list) new_removed_state a =
  pmatch_rows c_env pes new_state a
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ rw [] \\ fs []
  \\ drule (CONJUNCT1 flat_state_rel_pmatch) \\ fs []
QED

Theorem pmatch_rows_find_lookups:
  pmatch_rows c_env pes q a = Match (env',p',e') /\
  domain (find_lookupsL (MAP SND pes)) ⊆ domain reachable ==>
  domain (find_lookups e') ⊆ domain reachable
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ fs [CaseEq"match_result"] \\ rw []
  \\ fs [find_lookups_def,domain_union]
QED

Theorem pmatch_rows_IMP_pmatch:
  pmatch_rows c_env pes s v = Match (env',p',e') ==>
  pmatch c_env s p' v [] = Match env' /\ MEM (p',e') pes
Proof
  Induct_on `pes`
  \\ fs [pmatch_rows_def,FORALL_PROD,CaseEq"match_result"]
  \\ rw [] \\ fs []
QED

Theorem pmatch_not_has_Eval:
  (
  ! c_env ^s p v bindings env.
  pmatch c_env s p v bindings = Match env /\ ~ v_has_Eval v /\
  EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs /\
  EVERY ($~ ∘ v_has_Eval ∘ SND) bindings ==>
  EVERY ($~ ∘ v_has_Eval ∘ SND) env
  ) /\ (
  ! c_env ^s ps vs bindings env.
  pmatch_list c_env s ps vs bindings = Match env /\
  EVERY ($~ ∘ v_has_Eval) vs /\
  EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs /\
  EVERY ($~ ∘ v_has_Eval ∘ SND) bindings ==>
  EVERY ($~ ∘ v_has_Eval ∘ SND) env
  )
Proof
  ho_match_mp_tac pmatch_ind
  \\ simp [pmatch_def]
  \\ rw []
  \\ simp []
  \\ fs [v_has_Eval_def, option_case_eq, case_eq_thms]
  \\ fs []
  >- (
    fs [semanticPrimitivesTheory.store_lookup_def]
    \\ drule_then drule EVERY_EL_IMP
    \\ simp []
  )
  \\ fs [CaseEq "match_result"]
  \\ fs []
QED

(******** EVALUATE INDUCTION ********)

val evaluate_exp_ind = evaluate_ind
  |> Q.SPECL [`P`, `\_ _ _. T`, `\_ _ _. T`]
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> Q.GEN `P`

Theorem evaluate_keep_flat_state_rel_eq_lemma:
    (∀ env ^state exprL new_state
        result reachable:num_set removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        domain (find_lookupsL exprL) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        EVERY (($~) ∘ v_has_Eval ∘ SND) env.v ∧
        EVERY (($~) ∘ has_Eval) exprL ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate env removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (find_sem_prim_res_globals result) ⊆ domain reachable ∧
        EVERY (($~) ∘ v_has_Eval) (result_vs result))
Proof
  ho_match_mp_tac evaluate_exp_ind >> rpt CONJ_TAC >> rpt GEN_TAC >>
  TRY strip_tac >>
  TRY (simp [] >> NO_TAC)
  (* EVALUATE CASES *)
  >- ( (* EMPTY LIST CASE *)
    fs[evaluate_def] >> rveq >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def]
    )
  >- ( (* NON_EMPTY, NON-SINGLETON LIST CASE *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >>
    fs[find_lookups_def, domain_union] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
    Cases_on `evaluate env q (e2::es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
    fs[] >>
    reverse(Cases_on `r` >> fs[])
    >- (
      rw[] >> fs[]
    )
    >- (
      strip_tac >> rw[] >>
      fs[find_sem_prim_res_globals_def,
          find_v_globals_def, domain_union] >>
      imp_res_tac evaluate_sing >> rveq >> rveq >>
      fs[find_v_globals_def]
      )
    )
  (* SINGLETON LIST CASES *)
  >- ( (* Lit *)
    fs[evaluate_def] >> rveq >> fs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def, v_has_Eval_def]
    )
  >- ( (* Raise *)
    rpt gen_tac >> strip_tac >> fs[find_lookups_def, has_Eval_def] >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def, pair_case_eq] >>
    strip_tac >> fs [] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    strip_tac >>
    fs[case_eq_thms] >> rveq >> fs[] >>
    fs[find_sem_prim_res_globals_def,
        find_v_globals_def, find_result_globals_def] >>
    imp_res_tac evaluate_sing >> rveq >> rveq >> fs[find_v_globals_def]
    )
  >- ( (* Handle *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    fs[find_lookups_def, domain_union, has_Eval_def] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    strip_tac >>
    Cases_on `r` >> rw[] >> rfs[] >>
    Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
    fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] >> rveq >> fs [] >>
    drule flat_state_rel_pmatch_rows >> fs [] >>
    rfs [] >> strip_tac >> first_x_assum match_mp_tac >> fs [] >>
    conj_tac THEN1 metis_tac [pmatch_rows_find_lookups] >>
    fs [find_env_globals_def] >>
    fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
    imp_res_tac pmatch_rows_IMP_pmatch >>
    drule (CONJUNCT1 pmatch_not_has_Eval) >>
    fs [flat_state_rel_def] >>
    fs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    res_tac >>
    fs [] >>
    rw [] >>
    drule_then irule (CONJUNCT1 pmatch_Match_reachable) >>
    fs[find_v_globals_def] >>
    fs [find_sem_prim_res_globals_def,find_result_globals_def]
    )
  >- ( (* Con NONE *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >>
    Cases_on `r` >>
    rw[] >> rfs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        v_has_Eval_def, EVERY_REVERSE] >>
    simp[Once find_v_globalsL_REVERSE]
    )
  >- ( (* Con SOME *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    `state'.c = removed_state.c` by fs[flat_state_rel_def] >>
    fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    IF_CASES_TAC >> fs [] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        v_has_Eval_def, EVERY_REVERSE] >>
    simp[Once find_v_globalsL_REVERSE]
    )
  >- ( (* Var_local *)
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> strip_tac >> rveq >> fs[find_lookups_def] >>
    Cases_on `ALOOKUP env.v n` >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
    imp_res_tac ALOOKUP_MEM >> imp_res_tac find_v_globalsL_MEM >>
    fs[find_env_globals_def] >> fs[SUBSET_DEF] >>
    fs[EVERY_MEM] >> res_tac >> fs []
    )
  >- ( (* Fun *)
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> strip_tac >> rveq >>
    fs[find_sem_prim_res_globals_def,
        find_env_globals_def, find_v_globals_def] >>
    fs[domain_union, find_lookups_def] >>
    fs[v_has_Eval_def, has_Eval_def, EVERY_MAP, o_DEF]
    )
  >- ( (* App *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >> fs[] >>
    `domain (find_lookupsL es) ⊆ domain reachable` by (
        Cases_on `op` >> fs[dest_GlobalVarLookup_def] >>
        fs[domain_insert]) >>
    fs[] >>
    Cases_on `r` >> fs[] >> strip_tac >> rveq >> fs[] >> rfs[] >>
    Cases_on `op = Opapp` >> fs[]
    >- (
      Cases_on `do_opapp (REVERSE a)` >> fs[] >>
      Cases_on `x` >> fs[] >>
      Cases_on `q.clock = 0` >> fs[]
      >- (
        rveq >>
        qpat_x_assum
            `flat_state_rel reachable new_state _` mp_tac >>
        simp[Once flat_state_rel_def] >> strip_tac >> rveq >>
        fs[flat_state_rel_def,
            find_sem_prim_res_globals_def, find_result_globals_def]
        )
      >- (
        first_x_assum (qspecl_then
            [`reachable`, `dec_clock new_removed_state`] mp_tac) >>
        fs[] >>
        qpat_x_assum `flat_state_rel reachable q _` mp_tac >>
        simp[Once flat_state_rel_def] >>
        strip_tac >> strip_tac >>
        qpat_x_assum `_ ⇒ _` match_mp_tac  >>
        fs[flat_state_rel_def, globals_rel_def,
            dec_clock_def, find_env_globals_def] >> rfs[] >> rveq >>
        asm_rewrite_tac [] >>
        fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >>
        fs[find_sem_prim_res_globals_def] >>
        fs[SWAP_REVERSE_SYM, find_v_globals_def, domain_union, v_has_Eval_def,
            o_DEF, EVERY_MAP] >>
        rw[]
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [MEM_SPLIT] >>
          fs [find_lookupsL_APPEND, domain_union, find_lookups_def]
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[find_v_globalsL_APPEND, domain_union] >>
          fs[MAP_MAP_o] >>
          simp [ELIM_UNCURRY, o_DEF, find_v_globals_MAP_Recclosure] >>
          rw []
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[EVERY_MAP, ELIM_UNCURRY, v_has_Eval_def]
          )
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [EVERY_MEM] >> res_tac >> fs []
          )
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [MEM_SPLIT] >>
          fs [find_lookupsL_APPEND, domain_union, find_lookups_def]
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[find_v_globalsL_APPEND, domain_union] >>
          fs[MAP_MAP_o] >>
          simp [ELIM_UNCURRY, o_DEF, find_v_globals_MAP_Recclosure] >>
          rw []
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs [EVERY_MAP, ELIM_UNCURRY, v_has_Eval_def]
          )
       >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [EVERY_MEM] >> res_tac >> fs []
          )
        )
      )
    >- (
      Cases_on `do_app q op (REVERSE a)` >> fs[] >>
      PairCases_on `x` >> fs[] >> rveq >>
      drule (GEN_ALL do_app_SOME_flat_state_rel) >>
      fs[find_lookups_def] >> disch_then drule >> strip_tac >>
      pop_assum (qspecl_then [
          `REVERSE a`, `new_state`, `x1`] mp_tac) >>
          simp[Once find_v_globalsL_REVERSE] >>
      fs[EVERY_REVERSE] >> strip_tac >>
      `domain (case dest_GlobalVarLookup op of
          NONE => LN | SOME n => insert n () LN) ⊆ domain reachable`
              by (Cases_on `dest_GlobalVarLookup op` >> fs[]) >>
      fs[find_sem_prim_res_globals_def] >> rfs[] >>
      fs[]
      )
    )
  >- ( (* If *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >> fs[] >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
    fs[] >>
    Cases_on `r` >> fs[] >>
    Cases_on `do_if (HD a) e2 e3` >> fs[] >>
    fs[do_if_def] >>
    first_x_assum match_mp_tac >>
    fs[] >>
    fs[flat_state_rel_def] >>
    EVERY_CASE_TAC >> fs[]
    )
  >- ( (* Mat *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
    Cases_on `r` >> fs[] >>
    fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] >> rveq >> fs [] >>
    drule flat_state_rel_pmatch_rows >> fs [] THEN1 EVAL_TAC >>
    rfs [] >> strip_tac >> first_x_assum match_mp_tac >> fs [] >>
    conj_tac THEN1 metis_tac [pmatch_rows_find_lookups] >>
    fs [find_env_globals_def] >>
    imp_res_tac evaluate_sing >> rveq >> fs [] >>
    fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
    imp_res_tac pmatch_rows_IMP_pmatch >>
    drule (CONJUNCT1 pmatch_not_has_Eval) >>
    fs [flat_state_rel_def] >>
    fs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    res_tac >>
    fs [] >>
    rw [] >>
    drule (CONJUNCT1 pmatch_Match_reachable) >>
    disch_then match_mp_tac >>
    fs[find_v_globals_def] >>
    fs [find_sem_prim_res_globals_def,find_result_globals_def] >>
    fs [flat_state_rel_def,find_v_globals_def]
    )
  >- ( (* Let *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
    Cases_on `r` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
        match_mp_tac) >> fs[] >>
    fs[find_env_globals_def, libTheory.opt_bind_def] >>
    Cases_on `n` >> fs[] >>
    fs[find_v_globals_def, domain_union] >>
    fs[find_sem_prim_res_globals_def] >> imp_res_tac evaluate_sing >>
    rveq >> fs[] >> rveq >> fs[find_v_globals_def]
    )
  >- ( (* Letrec *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
    strip_tac >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`]
        match_mp_tac) >> fs[] >>
    fs[find_env_globals_def, build_rec_env_def, has_Eval_def] >>
    fs[FOLDR_CONS_triple] >> fs[find_v_globalsL_APPEND, domain_union] >>
    fs[MAP_MAP_o, EVERY_MAP] >>
    fs [ELIM_UNCURRY, o_DEF, v_has_Eval_def, EVERY_MAP] >>
    simp [find_v_globals_MAP_Recclosure] >>
    rw [o_DEF]
  )
QED

(******** EVALUATE SPECIALISATION ********)

Theorem evaluate_sing_keep_flat_state_rel_eq:
    ∀ env ^state exprL new_state result expr
      reachable removed_state .
      flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
      flat_state_rel reachable state removed_state ∧
      exprL = [expr] ∧
      keep reachable (Dlet expr) ∧
      domain(find_lookups expr) ⊆ domain reachable ∧
      ~ has_Eval expr ∧
      result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate (env with v := []) removed_state exprL
            = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state
Proof
  rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
  drule evaluate_keep_flat_state_rel_eq_lemma >> fs[] >>
  strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`]
      mp_tac) >> fs[] >>
  impl_tac >> fs[] >>
  simp[find_env_globals_def, find_v_globals_def, Once find_lookups_def] >>
  simp[EVAL ``find_lookupsL []``] >> rw[] >> fs[]
QED

(******** EVALUATE_DEC ********)

Theorem evaluate_dec_flat_state_rel:
  ∀ ^state ctors dec new_state new_ctors result
    reachable removed_state .
    evaluate_dec state ctors dec = (new_state, new_ctors, result) ∧
    decs_closed reachable [dec] ∧
    flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
    ~ has_Eval_dec dec ∧
    result ≠ SOME (Rabort Rtype_error)
  ⇒ ∃ new_removed_state .
      evaluate_dec removed_state ctors dec =
          (new_removed_state, new_ctors, result) ∧
      flat_state_rel reachable new_state new_removed_state
Proof
  rw[] >> qpat_x_assum `evaluate_dec _ _ _ = _` mp_tac >>
  reverse(Induct_on `dec`) >> fs[evaluate_def] >> strip_tac >>
  strip_tac >>
  fs[keep_def]
  >- (
    fs[flat_state_rel_def] >>
    fs[is_fresh_exn_def] >>
    rw[] >> fs[find_result_globals_def] >>
    fs[globals_rel_def] >>
    metis_tac[]
    )
  >- (
    fs[flat_state_rel_def] >>
    fs[is_fresh_exn_def] >>
    rw[] >> fs[find_result_globals_def] >>
    fs[globals_rel_def] >>
    metis_tac[]
    ) >>
  rpt strip_tac >>
  fs [pair_case_eq] >>
  drule_then drule evaluate_sing_keep_flat_state_rel_eq >>
  fs [keep_def, has_Eval_dec_def] >>
  `domain (find_lookups e) ⊆ domain reachable` by (
    fs[decs_closed_def] >> fs[analyse_code_def] >>
    fs[analyse_exp_def] >>
    reverse(Cases_on `is_pure e`) >> fs[]
    >- (fs[code_analysis_union_def] >> fs[domain_union]) >>
    reverse(Cases_on `is_hidden e`) >> fs[] >>
    fs[code_analysis_union_def, domain_union] >>
    fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
    simp[SUBSET_DEF] >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[spt_eq_thm, wf_inter, wf_def] >> fs[lookup_inter_alt] >>
    fs[lookup_def] >> Cases_on `lookup n (find_loc e)` >> fs[] >>
    fs[domain_lookup] >>
    asm_exists_tac >> fs[] >> fs[is_reachable_def] >>
    match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
    `(lookup n (map (K (find_lookups e)) (find_loc e))) =
        SOME (find_lookups e)` by fs[lookup_map] >>
    imp_res_tac lookup_mk_wf_set_tree >> fs[] >>
    `wf_set_tree (mk_wf_set_tree
        (map (K (find_lookups e)) (find_loc e)))`
        by metis_tac[mk_wf_set_tree_thm] >>
    fs[wf_set_tree_def] >> res_tac >> `y = find_lookups e`
        by metis_tac[wf_find_lookups, num_set_domain_eq] >>
    rveq >> fs[] >> fs[SUBSET_DEF, domain_lookup]
  ) >>
  simp [] >>
  impl_tac >- (CCONTR_TAC >> fs []) >>
  EVERY_CASE_TAC >> fs[] >> rw[] >>
  fs[flat_state_rel_def]
QED

Theorem total_pat_IMP:
  (! c_env ^s p v env res.
     pmatch c_env s p v env = res /\ total_pat p ==> res <> No_match) /\
  (! c_env ^s ps vs env res.
     LENGTH ps = LENGTH vs /\
     pmatch_list c_env s ps vs env = res /\
     total_pat_list ps ==> res <> No_match)
Proof
  ho_match_mp_tac pmatch_ind \\ rw []
  \\ fs [pmatch_def,CaseEq"bool",total_pat_def]
  \\ CCONTR_TAC \\ fs []
  \\ fs [pmatch_stamps_ok_OPTREL, OPTREL_def]
  \\ rveq
  \\ fs [total_pat_def]
  \\ fs [CaseEq"match_result"] \\ fs []
QED

Theorem EXISTS_total_pat:
  EXISTS total_pat (MAP FST pes) ==>
  pmatch_rows c_env pes new_state v <> No_match
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ strip_tac
  \\ reverse (Cases_on `EXISTS total_pat (MAP FST pes)`)
  \\ full_simp_tac std_ss [] THEN1
   (rw [] \\ Cases_on `pmatch c_env new_state p_1 v []` \\ fs []
    \\ drule (CONJUNCT1 total_pat_IMP) \\ fs [] \\ fs [CaseEq"match_result"])
  \\ Cases_on `pmatch_rows c_env pes new_state v` \\ fs []
  \\ fs [CaseEq"match_result"]
QED


(********************** CASE: *NOT* keep reachable h ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

Theorem evaluate_flat_state_rel_lemma:
  (∀ env ^state exprL new_state result
      reachable removed_state .
      flatSem$evaluate env state exprL = (new_state, result) ∧
      EVERY is_pure exprL ∧
      EVERY (($~) ∘ v_has_Eval ∘ SND) env.v ∧
      EVERY (($~) ∘ has_Eval) exprL ∧
      EVERY (λ e. isEmpty (inter (find_loc e) reachable)) exprL ∧
      flat_state_rel reachable state removed_state ∧
      result ≠ Rerr (Rabort Rtype_error)
  ⇒ ?values. flat_state_rel reachable new_state removed_state ∧
      result = Rval values ∧
      EVERY (($~) ∘ v_has_Eval) values)
Proof
  ho_match_mp_tac evaluate_exp_ind >> rpt CONJ_TAC >> rpt GEN_TAC
  >> TRY (simp [] >> NO_TAC) >> strip_tac
  (* EVALUATE_DECS_CASES *)
  >- ( (* EMPTY LIST CASE *)
      fs[evaluate_def] >> rveq >> fs[find_v_globals_def]
      )
  >- ( (* NON-EMPTY, NON-SINGLETON LIST CASE *)
    rpt gen_tac >> strip_tac >>
    qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (
      Cases_on `evaluate env q (e2 :: es)` >> fs[] >>
      first_x_assum drule >> disch_then drule >>
      fs[] >> Cases_on `r` >> fs[]
      >- (
        first_x_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[] >>
        rw[] >> fs[find_v_globals_def, domain_union] >>
        imp_res_tac evaluate_sing >>
        fs [] >>
        first_x_assum match_mp_tac >>
        fs[]
        )
      >- (
        rveq >>
        fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >> rw[] >> fs[] >>
        qpat_x_assum `EXISTS _ _` mp_tac >>
        once_rewrite_tac [GSYM NOT_EVERY] >> strip_tac
        )
      )
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >> rw[] >> fs[]
      )
    )
      (* SINGLETON LIST CASES *)
  >- ( (* Lit *)
    fs[evaluate_def] >> rveq >> fs[find_v_globals_def, v_has_Eval_def]
    )
  >- ((* Raise *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `evaluate env state' [e]` >> fs[] >>
    Cases_on `r` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[is_pure_def]
    )
  >- ( (* Handle *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def, has_Eval_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (rveq >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[is_pure_def] >> strip_tac >>
        qpat_x_assum `isEmpty _` mp_tac >>
        simp[Once find_loc_def] >>
        strip_tac >>
        qpat_x_assum `isEmpty _ ⇒ _` match_mp_tac >> fs[] >>
        imp_res_tac inter_union_empty)
    >- (fs[is_pure_def] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        `isEmpty(inter (find_locL (MAP SND pes)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >> strip_tac >> fs[])
    )
  >- ( (* Con NONE *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def, has_Eval_def] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      strip_tac >> rveq >>
      fs[is_pure_def, find_v_globals_def] >> fs[EVERY_REVERSE] >>
      simp[Once find_v_globalsL_REVERSE] >> fs[] >>
      rfs[v_has_Eval_def, EVERY_REVERSE] >>
      qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
      strip_tac >>
      fs[find_loc_EVERY_isEmpty]
      )
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      rveq >> fs[is_pure_def] >> fs[EVERY_REVERSE] >>
      once_rewrite_tac [(GSYM NOT_EXISTS)] >>
      once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
      qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
      fs[find_loc_EVERY_isEmpty]
      )
    )
  >- ( (* Con SOME *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >>
    strip_tac >> fs[evaluate_def] >>
    fs [bool_case_eq] >>
    rfs[] >> fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    Cases_on `r` >>
    fs[has_Eval_def] >>
    fs[is_pure_def, EVERY_REVERSE] >> rveq >>
    fs[find_loc_EVERY_isEmpty, v_has_Eval_def, EVERY_REVERSE] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[EVERY_REVERSE] >>
    once_rewrite_tac [(GSYM NOT_EXISTS)] >>
    once_rewrite_tac [GSYM NOT_EVERY] >>
    fs[find_loc_EVERY_isEmpty]
    )
  >- ( (* Var_local *)
    fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >>
    rveq >> fs[] >>
    fs[find_v_globals_def, find_env_globals_def, EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >>
    res_tac >> fs [] >>
    imp_res_tac find_v_globalsL_MEM >> imp_res_tac SUBSET_TRANS
    )
  >- ( (* Fun *)
    qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >>
    strip_tac >> fs[evaluate_def] >>
    rveq >>
    fs[find_v_globals_def, domain_union,
        find_env_globals_def, is_pure_def, v_has_Eval_def, has_Eval_def] >>
    fs[find_loc_def, EVERY_MAP, o_DEF]
    )
  >- ( (* App *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    fs[is_pure_def] >> qpat_x_assum `isEmpty _` mp_tac >>
    simp[Once find_loc_def] >>
    strip_tac >> fs[] >> fs[EVERY_REVERSE] >> fs[find_loc_EVERY_isEmpty] >>
    Cases_on `r` >> fs[]
    >- (
      Cases_on `op = Opapp` >> fs[is_pure_def, dest_GlobalVarInit_def] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      strip_tac >>
      Cases_on `op` >>
      fs[is_pure_def, dest_GlobalVarInit_def, do_app_def] >>
      rfs [has_Eval_def] >>
      fs[] >> imp_res_tac inter_insert_empty >>
      EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
      simp[v_has_Eval_Unitv] >>
      fs[find_v_globals_def, flat_state_rel_def] >> rw[] >>
      fs[] >> rfs[] >>
      fs[globals_rel_def] >>
      fs[LUPDATE_SEM] >>
      simp [EL_LUPDATE, bool_case_eq] >>
      metis_tac []
      )
    >- (
      rveq >> fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[has_Eval_def] >>
      once_rewrite_tac [(GSYM NOT_EXISTS)] >>
      once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
      Cases_on `op` >>
      fs[is_pure_def, dest_GlobalVarInit_def] >>
      imp_res_tac inter_insert_empty
      )
    )
  >- ( (* If *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
    fs[is_pure_def, has_Eval_def] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    `isEmpty (inter (find_loc e1) reachable) ∧
        isEmpty (inter (find_loc e2) reachable) ∧
        isEmpty (inter (find_loc e3) reachable)` by
            metis_tac[inter_union_empty] >>
    Cases_on `r` >> fs[]
    >- (
      fs[do_if_def, Boolv_def] >> Cases_on `HD a` >> fs[] >>
      EVERY_CASE_TAC >> fs[] >>
      rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
          mp_tac) >> fs[] >>
      strip_tac >> rfs[] >>
      first_x_assum (drule_then drule) >>
      fs[]
      )
    >- (
      rveq >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[]
      )
    )
  >- ( (* Mat *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    fs[is_pure_def, has_Eval_def] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    `isEmpty (inter (find_locL (MAP SND pes)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
    reverse (Cases_on `r`) >> fs[]
    THEN1 (rveq \\ fs [] \\ metis_tac [])
    \\ fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] \\ rveq \\ fs []
    \\ imp_res_tac EXISTS_total_pat \\ fs []
    \\ last_x_assum match_mp_tac \\ first_x_assum drule
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ drule pmatch_rows_IMP_pmatch \\ strip_tac
    \\ fs [GSYM find_loc_EVERY_isEmpty]
    \\ drule (CONJUNCT1 pmatch_not_has_Eval)
    \\ imp_res_tac evaluate_sing
    \\ fs [flat_state_rel_def]
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ res_tac \\ fs []
    \\ fs [flat_state_rel_def]
    )
  >- ( (* Let *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e1]` >> fs[is_pure_def, has_Eval_def] >>
    fs[is_pure_def] >> qpat_x_assum `isEmpty _ ` mp_tac >>
    simp[Once find_loc_def] >>
    strip_tac >>
    fs[inter_union_empty] >>
    Cases_on `r` >> fs[]
    >- (
      first_x_assum drule >>
      disch_then drule >>
      strip_tac >>
      fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      impl_tac >> fs[] >>
      imp_res_tac evaluate_sing >>
      fs[libTheory.opt_bind_def] >>
      every_case_tac >> simp []
      )
    >- (
      rveq >> fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[]
      )
    )
  >- ( (* Letrec *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[] >>
    strip_tac >> fs[is_pure_def, has_Eval_def] >> rfs[] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    first_x_assum irule >>
    `isEmpty (inter (find_locL (MAP (SND o SND) funs)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
    fs[find_env_globals_def, build_rec_env_def] >>
    fs[FOLDR_CONS_triple, EVERY_MAP, o_DEF] >>
    fs[ELIM_UNCURRY, v_has_Eval_def, EVERY_MAP, o_DEF]
    )
QED

(******** EVALUATE SPECIALISATION ********)

Theorem evaluate_sing_notKeep_flat_state_rel:
  ∀ env state exprL new_state result expr
      reachable removed_state .
      flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
      exprL = [expr] ∧
      ~ has_Eval expr ∧
      ¬keep reachable (Dlet expr) ∧
      flat_state_rel reachable state removed_state ∧
      result ≠ Rerr (Rabort Rtype_error)
  ⇒ flat_state_rel reachable new_state removed_state ∧
      ∃ value : flatSem$v . result = Rval [value]
Proof
  rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
  drule evaluate_flat_state_rel_lemma >> fs[] >>
  disch_then drule >> disch_then drule >> fs[] >>
  rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[find_v_globals_def]
QED



(******************************* MAIN PROOFS ******************************)

Theorem flat_decs_removal_lemma:
     ∀ ^state ctors decs new_state new_ctors result
        reachable removed_decs removed_state .
        evaluate_decs state ctors decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        remove_unreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        EVERY ($~ ∘ has_Eval_dec) decs ∧
        decs_closed reachable decs
    ⇒ ∃ new_removed_state .
        new_removed_state.ffi = new_state.ffi /\
        evaluate_decs removed_state ctors removed_decs =
            (new_removed_state, new_ctors, result)
Proof
    Induct_on `decs`
    >- (rw[evaluate_def, remove_unreachable_def] >>
        fs[evaluate_def, find_result_globals_def, flat_state_rel_def])
    >>  fs[evaluate_def, remove_unreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (
          fs[evaluate_def] >>
          fs [pair_case_eq] >>
          rveq >> fs [] >>
          rename [`evaluate_dec _ _ _ = (_, _, r1)`] >>
          `r1 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >>
          drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >>
          rw[] >> fs[] >>
          pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
          fs[] >>
          `decs_closed reachable [h]` by imp_res_tac decs_closed_reduce_HD >>
          fs[] >>
          reverse(Cases_on `r1` >> fs[] >> rw[] >> rveq >> EVERY_CASE_TAC)
          >- fs[flat_state_rel_def] >>
          fs[] >> first_x_assum drule >> fs[] >> rveq >> strip_tac >>
          pop_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
          fs[] >>
          reverse(impl_tac) >- rw[] >> fs[find_env_globals_def] >>
          imp_res_tac decs_closed_reduce >> fs[]
          )
        >>  reverse(EVERY_CASE_TAC) >> fs[] >> rveq >>
            imp_res_tac keep_Dlet >> rveq >>
            fs[Once evaluate_def] >> EVERY_CASE_TAC >> fs[] >>
            rveq >> rw[UNION_EMPTY]
            >- (
                drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                strip_tac >>
                rfs [has_Eval_dec_def] >>
                metis_tac [])
            >>  first_x_assum match_mp_tac >>
                fs[] >> asm_exists_tac >> fs[] >>
                imp_res_tac decs_closed_reduce >> fs[] >>
                drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                fs [has_Eval_dec_def]
QED

Theorem flat_removal_thm:
  ∀ ffi k decs new_state new_ctors result roots tree
      reachable removed_decs .
      evaluate_decs (initial_state ffi k ec) initial_ctors decs =
        (new_state, new_ctors, result) ∧
      result ≠ SOME (Rabort Rtype_error) ∧
      (roots, tree) = analyse_code decs ∧
      reachable = closure_spt roots (mk_wf_set_tree tree) ∧
      ~ EXISTS has_Eval_dec decs ∧
      remove_unreachable reachable decs = removed_decs
  ⇒ ∃ s .
      s.ffi = new_state.ffi /\
      evaluate_decs (initial_state ffi k ec) initial_ctors
          removed_decs = (s, new_ctors, result)
Proof
  rpt strip_tac >> drule flat_decs_removal_lemma >>
  rpt (disch_then drule) >> strip_tac >>
  pop_assum (qspec_then `initial_state ffi k ec` mp_tac) >>
  reverse(impl_tac)
  >- (rw[] >> fs[]) >>
  qspecl_then [`decs`, `roots`, `mk_wf_set_tree tree`, `tree`]
    mp_tac analysis_reachable_thm >>
  fs [NOT_EXISTS] >>
  rw[initial_state_def]
  >- (
    fs[flat_state_rel_def, globals_rel_def] >>
    fs[find_refs_globals_def]
    )
  >- (
    fs[decs_closed_def] >> rw[] >>
    `(r,t) = (roots, tree)` by metis_tac[] >>
    fs[] >> rveq
    >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[is_reachable_def])
    >- (
      qexists_tac `n'` >> fs[is_reachable_def] >>
       metis_tac[transitive_RTC, transitive_def]
       )
    )
QED

Theorem flat_remove_eval_sim:
   eval_sim ffi ds1 (remove_flat_prog ds1) ec ec
                    (\d1 d2. d2 = remove_flat_prog d1) F
Proof
  rw [eval_sim_def] \\ qexists_tac `0` \\ fs [remove_flat_prog_def]
  \\ pairarg_tac \\ fs []
  \\ drule flat_removal_thm \\ rw [] \\ fs []
  \\ rfs []
QED

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

Theorem remove_flat_prog_elist_globals_eq_empty:
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) = {||}
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter]
QED

Theorem remove_flat_prog_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds)))
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [esgc_free_filter]
QED

Theorem remove_flat_prog_sub_bag:
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ rw []
  \\ metis_tac [elist_globals_filter_SUB_BAG]
QED

Theorem remove_flat_prog_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT (elist_globals
     (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))))
Proof
  metis_tac [remove_flat_prog_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED

val _ = export_theory();
