open preamble sptreeTheory reg_allocTheory linear_scanTheory reg_allocProofTheory

val _ = new_theory "linear_scanProof"

val is_subset_compute_eq = Q.store_thm("is_subset_compute_eq",
    `!s1 s2. is_subset_compute s1 s2 <=>
    !x. (?y1. lookup x s1 = SOME y1) ==> (?y2. lookup x s2 = SOME y2)`,
    rpt strip_tac >>
    eq_tac THEN1 (
      rw [is_subset_compute_def] >>
      `MEM (x, y1) (toAList s1)` by metis_tac [MEM_toAList] >>
      `(\(a, b). lookup a s2 <> NONE) (x, y1)` by fs [EVERY_MEM] >>
      fs [] >>
      Cases_on `lookup x s2` >> fs[]
    ) >>
    rw [is_subset_compute_def] >>
    `!x. (?y1. MEM (x, y1) (toAList s1)) ==> (?y2. lookup x s2 = SOME y2)` by fs [MEM_toAList] >>
    pop_assum mp_tac >>
    qspec_tac (`toAList s1`, `l`) >>
    Induct_on `l` >>
    rw [] >>
    fs [PULL_EXISTS] >>
    Cases_on `h` >>
    rw [] >>
    pop_assum (qspecl_then [`q`,`r`] assume_tac) >>
    Cases_on `lookup q s2` >> rw []
)

val is_subset_eq = Q.store_thm("is_subset_eq",
    `!s1 s2. is_subset s1 s2 <=>
    !x. (?y1. lookup x s1 = SOME y1) ==> (?y2. lookup x s2 = SOME y2)`,
    rw [] >>
    eq_tac THEN1 (
        rw [is_subset_def] >>
        `x IN (domain s1)` by simp [domain_lookup] >>
        `x IN (domain s2)` by fs [SUBSET_DEF] >>
        fs [domain_lookup]
    ) >>
    fs [PULL_EXISTS] >>
    rw [is_subset_def, SUBSET_DEF] >>
    `?y1. lookup x s1 = SOME y1` by fs [domain_lookup] >>
    `?y2. lookup x s2 = SOME y2` by simp [] >>
    fs [domain_lookup]
)

val union_monotone = Q.store_thm("union_monotone",
    `!s1 s2 s1' s2'.
    is_subset s1 s1' /\ is_subset s2 s2' ==> is_subset (union s1 s2) (union s1' s2')`,
    rpt strip_tac >>
    fs [is_subset_eq, lookup_union, PULL_EXISTS] >>
    rpt gen_tac >>
    NTAC 2 (first_x_assum (qspecl_then [`x`, `y1`] assume_tac)) >>
    Cases_on `lookup x s1` >> Cases_on `lookup x s1'` >> rw []
)

val insert_monotone = Q.store_thm("insert_monotone",
    `!s1 s2 x v.
    is_subset s1 s2 ==> is_subset (insert x a s1) (insert x a s2)`,
    rw [is_subset_eq, lookup_insert] >>
    Cases_on `x' = x` >>
    rw [] >> metis_tac []
)

val numset_list_insert_monotone = Q.store_thm("numset_list_insert_monotone",
    `!l s1 s2.
    is_subset s1 s2 ==> is_subset (numset_list_insert l s1) (numset_list_insert l s2)`,
    Induct_on `l` >>
    rw [numset_list_insert_def] >>
    `is_subset (insert h () s1) (insert h () s2)` by simp [insert_monotone] >>
    rw []
)

val delete_monotone = Q.store_thm("delete_monotone",
    `!s1 s2 x v.
    is_subset s1 s2 ==> is_subset (delete x s1) (delete x s2)`,
    rw [is_subset_eq, lookup_delete, IS_SOME_EXISTS] >> metis_tac [NOT_SOME_NONE]
)

val numset_list_delete_monotone = Q.store_thm("numset_list_delete_monotone",
    `!l s1 s2.
    is_subset s1 s2 ==> is_subset (numset_list_delete l s1) (numset_list_delete l s2)`,
    Induct_on `l` >>
    rw [numset_list_delete_def] >>
    `is_subset (delete h s1) (delete h s2)` by simp [delete_monotone] >>
    rw []
)

val domain_numset_list_delete = Q.store_thm("domain_numset_list_delete",
    `!l s.  domain (numset_list_delete l s) = (domain s) DIFF (set l)`,
    Induct_on `l` >>
    rw [numset_list_delete_def, DIFF_INSERT]
)

val check_partial_col_input_monotone = Q.store_thm("check_partial_col_input_monotone",
    `!f live1 flive1 live2 flive2 l liveout2 fliveout2.
    IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 ==>
    is_subset live1 live2 ==>
    INJ f (domain live2) UNIV ==>
    check_partial_col f l live2 flive2 = SOME (liveout2, fliveout2) ==>
    ?liveout1 fliveout1. check_partial_col f l live1 flive1 = SOME (liveout1, fliveout1)
    `,

    sg `!x f s fs. (domain fs) = (IMAGE f (domain s)) /\ lookup x s = SOME () ==> lookup (f x) fs = SOME ()` THEN1 (
        rw [] >>
        `x IN (domain s)` by fs [domain_lookup] >>
        `f x IN (IMAGE f (domain s))` by fs [IMAGE_IN] >>
        `f x IN (domain fs)` by metis_tac [] >>
        fs [domain_lookup]
    ) >>

    Induct_on `l` >>
    rw [check_partial_col_def] >>

    `!x. lookup x live1 = SOME () ==> lookup (f x) flive1 = SOME ()` by metis_tac [] >>
    `!x. lookup x live2 = SOME () ==> lookup (f x) flive2 = SOME ()` by metis_tac [] >>

    sg `!x. ((?y. lookup x flive1 = SOME y) /\ lookup x flive2 = NONE) ==> F` THEN1 (
        rpt strip_tac >>
        fs [is_subset_def] >>
        `(IMAGE f (domain live1)) SUBSET (IMAGE f (domain live2))` by fs [IMAGE_SUBSET] >>
        `(domain flive1) SUBSET (domain flive2)` by metis_tac [] >>
        `x IN (domain flive1)` by fs [domain_lookup] >>
        `x IN (domain flive2)` by fs [SUBSET_DEF] >>
        `?y. lookup x flive2 = SOME y` by fs [domain_lookup] >>
        fs [NOT_SOME_NONE]
    ) >>

    Cases_on `lookup h live1` >>
    Cases_on `lookup h live2` >>
    rw []

    (* NONE NONE *)
    THEN1 (
        Cases_on `lookup (f h) flive1` >>
        Cases_on `lookup (f h) flive2` >>
        fs []
        (* NONE NONE *)
        THEN1 (
          `IMAGE f (domain (insert h () live2)) = domain (insert (f h) () flive2)` by rw [domain_insert, IMAGE_INSERT] >>
          `IMAGE f (domain (insert h () live1)) = domain (insert (f h) () flive1)` by rw [domain_insert, IMAGE_INSERT] >>
          sg `INJ f (domain (insert h () live2)) UNIV` THEN1 (
            rw [domain_insert, INJ_INSERT] >>
            `(f y) IN (IMAGE f (domain live2))` by fs [IMAGE_IN] >>
            `(f y) IN (domain flive2)` by metis_tac [] >>
            `(f h) IN (domain flive2)` by metis_tac [] >>
            `?y. lookup (f h) flive2 = SOME y` by fs [domain_lookup] >>
            fs [NOT_SOME_NONE]
          ) >>
          `is_subset (insert h () live1) (insert h () live2)` by rw [insert_monotone] >>
          first_x_assum drule >>
          metis_tac []
        )
        (* SOME NONE *)
        THEN1 (
            metis_tac []
        )
    )
    (* NONE SOME *)
    THEN1 (
        Cases_on `lookup (f h) flive2` >> fs [] THEN1 (
            (* Contradiction *)
            `lookup (f h) flive2 = SOME ()` by rfs [] >>
            metis_tac [NOT_SOME_NONE]
        ) >>
        Cases_on `lookup (f h) flive1` >> fs [] THEN1 (
            `IMAGE f (domain (insert h () live1)) = domain (insert (f h) () flive1)` by rw [domain_insert, IMAGE_INSERT] >>
            sg `is_subset (insert h () live1) live2` THEN1 (
                rw [is_subset_eq, lookup_insert] >>
                Cases_on `x = h` >> fs [is_subset_eq]
            ) >>
            first_x_assum (qspecl_then [`f`, `insert h () live1`, `insert (f h) () flive1`] assume_tac) >>
            metis_tac [] (* slow :( *)
        ) >>
        sg `?x.f h = f x /\ x IN (domain live1)` THEN1 (
            `(f h) IN (domain flive1)` by fs [domain_lookup] >>
            `(f h) IN (IMAGE f (domain live1))` by metis_tac [] >>
            metis_tac [IMAGE_applied, IN_DEF]
        ) >>
        `lookup h live1 <> SOME ()` by rw [NOT_SOME_NONE] >>
        `~(h IN (domain live1))` by rw [domain_lookup] >>
        `x <> h` by metis_tac [] >>
        `x IN (domain live2)` by fs [is_subset_def, SUBSET_DEF] >>
        `h IN (domain live2)` by fs [domain_lookup] >>
        metis_tac [INJ_DEF]
    )
    (* SOME NONE *)
    THEN1 (
        `h IN (domain live1)` by fs [domain_lookup] >>
        `h IN (domain live2)` by fs [SUBSET_DEF, is_subset_def] >>
        `lookup h live2 = SOME ()` by fs [domain_lookup] >>
        metis_tac [NOT_SOME_NONE]
    )
    (* SOME SOME *)
    THEN1 (
        fs [] >>
        `lookup (f h) flive1 = SOME ()` by rfs [] >>
        `lookup (f h) flive2 = SOME ()` by rfs [] >>
        metis_tac []
    )
)

val numset_list_delete_IMAGE = Q.store_thm("numset_list_delete_IMAGE",
    `!f l live flive a b.
    domain flive = IMAGE f (domain live) ==>
    INJ f (domain live) UNIV ==>
    check_partial_col f l live flive = SOME(a, b) ==>
    domain (numset_list_delete (MAP f l) flive) = IMAGE f (domain (numset_list_delete l live))`,

    Induct_on `l` >>
    rw [numset_list_delete_def, check_partial_col_def] >> rw [] >>
    Cases_on `lookup h live` >> fs [] THEN1 (
        Cases_on `lookup (f h) flive` >> fs [] >>
        `h NOTIN domain live` by fs [lookup_NONE_domain] >>
        `(f h) NOTIN domain flive` by fs [lookup_NONE_domain] >>
        `(f h) NOTIN (IMAGE f (domain live))` by metis_tac [] >>
        `domain (delete (f h) flive) = IMAGE f (domain (delete h live))` by rw [domain_delete, DELETE_NON_ELEMENT_RWT] >>
        `domain (insert (f h) () flive) = IMAGE f (domain (insert h () live))` by rw [domain_insert] >>
        `(domain live DELETE h) SUBSET domain live` by rw [DELETE_SUBSET] >>
        `INJ f (domain (delete h live)) UNIV` by metis_tac [domain_delete, INJ_SUBSET, UNIV_SUBSET] >>
        sg `INJ f (domain (insert h () live)) UNIV` THEN1 (
            rw [domain_insert, INJ_INSERT] >>
            `f y IN IMAGE f (domain live)` by rw [IMAGE_IN] >>
            metis_tac []
        ) >>
        `is_subset (delete h live) live` by rw [is_subset_def, domain_delete, DELETE_SUBSET] >>
        `is_subset live (insert h () live)` by rw [is_subset_def, domain_insert, INSERT_SUBSET] >>
        `?a b. check_partial_col f l live flive = SOME (a, b)` by metis_tac [check_partial_col_input_monotone] >>
        `?a b. check_partial_col f l (delete h live) (delete (f h) flive) = SOME (a, b)` by metis_tac [check_partial_col_input_monotone] >>
        rw []
    ) >>

    `h IN domain live` by rw [domain_lookup] >>
    `f h IN domain flive` by rw [IMAGE_IN] >>
    sg `domain (delete (f h) flive) = IMAGE f (domain (delete h live))` THEN1 (
      rw [domain_delete] >> rw [EXTENSION] >>
      eq_tac THEN1 (
        rw [] >> qexists_tac `x'` >> simp [] >> CCONTR_TAC >> fs []
      ) >>
      rw [] THEN1 (
        qexists_tac `x'` >> simp []
      ) >>
      CCONTR_TAC >> fs [] >> `x' = h` by metis_tac [INJ_DEF]
    ) >>
    `domain (delete h live) SUBSET domain live` by rw [domain_delete, SUBSET_DELETE] >>
    `INJ f (domain (delete h live)) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
    `?a b. check_partial_col f l live flive = SOME (a, b)` by metis_tac [check_partial_col_input_monotone, is_subset_def] >>
    `?a b. check_partial_col f l (delete h live) (delete (f h) flive) = SOME (a, b)` by metis_tac [check_partial_col_input_monotone, is_subset_def] >>
    rw []
)

val check_partial_col_output_monotone = Q.store_thm("check_partial_col_output_monotone",
    `!f live1 flive1 live2 flive2 l liveout2 fliveout2.
    is_subset live1 live2 ==>
    check_partial_col f l live1 flive1 = SOME (liveout1, fliveout1) ==>
    check_partial_col f l live2 flive2 = SOME (liveout2, fliveout2) ==>
    is_subset liveout1 liveout2
    `,
    rw [is_subset_def] >>
    (*`domain liveout1 = (set l) UNION (domain live1)` by metis_tac [check_partial_col_domain, FST]*)
    `domain liveout1 = (set l) UNION (domain live1)` by metis_tac [check_partial_col_domain, FST] >>
    `domain liveout2 = (set l) UNION (domain live2)` by metis_tac [check_partial_col_domain, FST] >>
    `(domain live2) SUBSET ((set l) UNION (domain live2))` by rw [SUBSET_UNION] >>
    rw [] >>
    metis_tac [SUBSET_TRANS]
)

val check_partial_col_IMAGE = Q.store_thm("check_partial_col_IMAGE",`
    !f l live flive live' flive'.
    (domain flive) = IMAGE f (domain live) ==>
    check_partial_col f l live flive = SOME (live', flive') ==>
    (domain flive') = IMAGE f (domain live')
    `,

    Induct_on `l` >>
    fs [check_partial_col_def] >> rw [] >>
    Cases_on`lookup h live` >>
    Cases_on`lookup (f h) flive` >>
    fs [] >>
    `domain (insert (f h) () flive) = IMAGE f (domain (insert h () live))` by rw [domain_insert] >>
    metis_tac []
)

val check_partial_col_success_INJ_lemma = Q.prove(`
    !l live flive f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_partial_col f l live flive = SOME (live',flive')
    ==>
    INJ f (set l UNION domain live) UNIV`,

    Induct_on `l` >> rw [] >>
    fs [check_partial_col_def] >>
    Cases_on `lookup h live` THEN1 (
        Cases_on `lookup (f h) flive` >> fs [] >>
        `domain (insert (f h) () flive) = IMAGE f (domain (insert h () live))` by metis_tac [domain_insert, IMAGE_INSERT] >>
        sg `INJ f (domain (insert h () live)) UNIV` THEN1 (
            rw [domain_insert, INJ_INSERT] >>
            `(f y) IN (domain flive)` by rw [] >>
            `(f h) NOTIN (domain flive)` by rw [domain_lookup, option_nchotomy] >>
            metis_tac []
        ) >>
        `INJ f (set l UNION domain (insert h () live)) UNIV` by metis_tac [] >>
        metis_tac [INSERT_UNION_EQ, UNION_COMM, domain_insert]
    ) >>
    fs [INSERT_UNION_EQ] >>
    `h IN (domain live)` by rw [domain_lookup] >>
    `h IN (set l) UNION (domain live)` by metis_tac [SUBSET_DEF, SUBSET_UNION] >>
    `!(x : num) s. x IN s ==> x INSERT s = s` by metis_tac [INSERT_applied, IN_DEF, EXTENSION] >>
    metis_tac []
)

val check_partial_col_success_INJ = Q.store_thm("check_partial_col_success_INJ", `
    !l live flive f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_partial_col f l live flive = SOME (live',flive')
    ==>
    INJ f (domain live') UNIV`,

    rw [] >>
    `domain live' = set l UNION domain live` by metis_tac [check_partial_col_domain, FST] >>
    metis_tac [check_partial_col_success_INJ_lemma]
)

val branch_domain = Q.store_thm("branch_domain",`
    !(live1 : num_set) (live2 : num_set).
    set (MAP FST (toAList (difference live2 live1))) UNION domain live1 = domain live1 UNION domain live2`,

    `!(live1 : num_set) (live2 : num_set). set (MAP FST (toAList (difference live2 live1))) = domain (difference live2 live1)` by rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup] >>
    `!(s : num -> bool) (t : num -> bool). t DIFF s UNION s = s UNION t` by (rw [EXTENSION] >> Cases_on `x IN t` >> rw []) >>
    rw [domain_difference]
)

val check_partial_col_branch_comm = Q.store_thm("check_partial_col_branch_comm",
    `!f live1 flive1 live2 flive2 a b.
    INJ f (domain live1) UNIV ==>
    domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) ==>
    check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 = SOME (a, b) ==>
    ?c d. check_partial_col f (MAP FST (toAList (difference live1 live2))) live2 flive2 = SOME (c, d)`,

    rw [] >>
    `domain a = domain live1 UNION domain live2` by metis_tac [check_partial_col_domain, branch_domain, FST] >>
    `INJ f (domain live1 UNION domain live2) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `set (MAP FST (toAList (difference live1 live2))) UNION domain live2 = domain live1 UNION domain live2` by metis_tac [UNION_COMM, domain_difference, branch_domain] >>
    metis_tac [check_partial_col_success]
)

val check_partial_col_list_monotone = Q.store_thm("check_partial_col_list_monotone",
    `!f live flive (s1 : num_set) (s2 : num_set) a b.
    domain flive = IMAGE f (domain live) ==>
    INJ f (domain live) UNIV ==>
    is_subset s1 s2 ==>
    check_partial_col f (MAP FST (toAList s2)) live flive= SOME (a, b) ==>
    ?c d. check_partial_col f (MAP FST (toAList s1)) live flive = SOME (c, d)`,

    rw [] >>
    `!(s : num_set). set (MAP FST (toAList s)) = domain s` by rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup] >>
    `INJ f (domain a) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `domain a = (domain s2 UNION domain live)` by metis_tac [check_partial_col_domain, FST] >>
    `domain s1 UNION domain live SUBSET domain a` by fs [is_subset_def, SUBSET_DEF] >>
    `INJ f (domain s1 UNION domain live) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
    metis_tac [check_partial_col_success]
)

val check_live_tree_success = Q.store_thm("check_live_tree_success", `
    !lt live flive live' flive' f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_live_tree f lt live flive = SOME (live',flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV`,

    Induct_on `lt`

    (* StartLive *)
    THEN1 (
      rw [check_live_tree_def] >>
      Cases_on `check_partial_col f l live flive` >> fs [] >>
      Cases_on `x`
      THEN1 (
        metis_tac [numset_list_delete_IMAGE]
      )
      THEN1 (
        `domain live' SUBSET domain live` by metis_tac [domain_numset_list_delete, DIFF_SUBSET] >>
        metis_tac [INJ_SUBSET, UNIV_SUBSET]
      )
    )
    (* EndLive *)
    THEN1 (
      rw [check_live_tree_def]
      THEN1 (
        metis_tac [check_partial_col_IMAGE]
      )
      THEN1 (
        metis_tac [check_partial_col_success_INJ]
      )
    )
    (* Branch *)
    THEN1 (
      rw [check_live_tree_def] >>
      Cases_on `check_live_tree f lt live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      Cases_on `check_live_tree f lt' live flive` >> fs [] >>
      Cases_on `x` >> fs []
      THEN1 (
        metis_tac [check_partial_col_IMAGE]
      )
      THEN1 (
        `INJ f (domain q) UNIV` by metis_tac [] >>
        `domain r = IMAGE f (domain q)` by metis_tac [check_partial_col_IMAGE] >>
        metis_tac [check_partial_col_success_INJ]
      )
    )
    (* Seq *)
    THEN1 (
      rw [check_live_tree_def] >>
      Cases_on `check_live_tree f lt' live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      `domain r = IMAGE f (domain q)` by metis_tac []
      THEN1 (
        metis_tac []
      )
      THEN1 (
        `INJ f (domain q) UNIV` by metis_tac [] >>
        metis_tac []
      )
    )
)

val ALL_DISTINCT_INJ_MAP = Q.store_thm("ALL_DISTINCT_INJ_MAP",
    `!f l. ALL_DISTINCT (MAP f l) ==> INJ f (set l) UNIV`,
    Induct_on `l` >> rw [INJ_INSERT] >>
    `MEM (f y) (MAP f l)` by metis_tac [MEM_MAP] >>
    `~(MEM (f y) (MAP f l))` by metis_tac []
)

val check_col_output = Q.store_thm("check_col_output",
    `!f live live' flive'.
    check_col f live = SOME (live', flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV`,
    rw [check_col_def]
    THEN1 (
      rw [EXTENSION, domain_fromAList, MEM_MAP] >>
      rw [MEM_toAList, EXISTS_PROD, domain_lookup, PULL_EXISTS]
    )
    THEN1 (
      `INJ f (set (MAP FST (toAList live))) UNIV` by metis_tac [ALL_DISTINCT_INJ_MAP, MAP_MAP_o] >>
      `set (MAP FST (toAList live)) = domain live` by rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup] >>
      metis_tac []
    )
)

val check_col_success = Q.store_thm("check_col_success",
    `!f live.
    INJ f (domain live) UNIV ==>
    ?flive. check_col f live = SOME (live, flive)`,

    rw [check_col_def] >>
    sg `!x y. MEM x (MAP FST (toAList live)) /\ MEM y (MAP FST (toAList live)) /\ (f x = f y) ==> (x = y)` THEN1 (
        rw [MEM_toAList, MEM_MAP, EXISTS_PROD] >>
        `x IN domain live /\ y IN domain live` by rw [domain_lookup] >>
        fs [INJ_DEF]
    ) >>
    metis_tac [ALL_DISTINCT_MAP_INJ, MAP_MAP_o, ALL_DISTINCT_MAP_FST_toAList]
)

val check_clash_tree_output = Q.store_thm("check_clash_tree_output", `
    !f ct live flive live' flive'.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_clash_tree f ct live flive = SOME (live', flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV`,

    Induct_on `ct` >>
    simp [check_clash_tree_def]

    (* Delta *)
    THEN1 (
      rpt gen_tac >> strip_tac >>
      Cases_on `check_partial_col f l live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      `domain (numset_list_delete (MAP f l) flive) = IMAGE f (domain (numset_list_delete l live))` by metis_tac [numset_list_delete_IMAGE] >>
      `domain (numset_list_delete l live) SUBSET (domain live)` by rw [domain_numset_list_delete] >>
      `INJ f (domain (numset_list_delete l live)) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
      strip_tac
      THEN1 metis_tac [check_partial_col_IMAGE]
      THEN1 metis_tac [check_partial_col_success_INJ]
    )
    (* Set *)
    THEN1 (
      rw [] >> metis_tac [check_col_output]
    )
    (* Branch *)
    THEN1 (
        rpt gen_tac >> strip_tac >>
        Cases_on `check_clash_tree f ct live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `check_clash_tree f ct' live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `o'` >> fs [] THEN1 (
            `domain r = IMAGE f (domain q)` by metis_tac [check_partial_col_IMAGE] >>
            `INJ f (domain q) UNIV` by metis_tac [check_partial_col_success_INJ] >>
            strip_tac
            THEN1 metis_tac [check_partial_col_IMAGE]
            THEN1 metis_tac [check_partial_col_success_INJ]

        ) >>
        metis_tac [check_col_output]
    )
    (* Seq *)
    THEN1 (
        rpt gen_tac >> strip_tac >>
        Cases_on `check_clash_tree f ct' live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [] >>
        metis_tac []
    )
)

val get_live_tree_correct = Q.store_thm("get_live_tree_correct",
    `!f live1 flive1 live2 flive2 ct live2' flive2'.
    IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 ==>
    INJ f (domain live2) UNIV ==>
    is_subset live1 live2 ==>
    check_live_tree f (get_live_tree ct) live2 flive2 = SOME (live2', flive2') ==>
    ?live1' flive1'. check_clash_tree f ct live1 flive1 = SOME (live1', flive1') /\
    IMAGE f (domain live1') = domain flive1' /\
    is_subset live1' live2'
    `,

    Induct_on `ct`

    (* Delta *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        fs [check_live_tree_def] >>
        Cases_on `check_partial_col f l live2 flive2` >> fs [] >>
        Cases_on `x` >>
        `?a b. check_partial_col f l live1 flive1 = SOME (a, b)` by metis_tac [check_partial_col_input_monotone] >>
        rw [] >>
        `is_subset (numset_list_delete l live1) (numset_list_delete l live2)` by metis_tac [numset_list_delete_monotone] >>
        sg `INJ f (domain (numset_list_delete l live2)) UNIV` THEN1 (
          rw [domain_numset_list_delete] >>
          `(domain live2 DIFF set l) SUBSET (domain live2)` by fs [SUBSET_DIFF] >>
          metis_tac [SUBSET_DIFF, INJ_SUBSET, UNIV_SUBSET]
        ) >>
        sg `IMAGE f (domain (numset_list_delete l live1)) = domain (numset_list_delete (MAP f l) flive1)` THEN1 (
            `INJ f (domain live1) UNIV` by metis_tac [is_subset_def, INJ_SUBSET, UNIV_SUBSET] >>
            metis_tac [numset_list_delete_IMAGE]
        ) >>
        sg `IMAGE f (domain (numset_list_delete l live2)) = domain (numset_list_delete (MAP f l) flive2)` THEN1 (
            metis_tac [numset_list_delete_IMAGE]
        ) >>
        `?live1' flive1'. check_partial_col f l0 (numset_list_delete l live1)
        (numset_list_delete (MAP f l) flive1) = SOME (live1', flive1')` by metis_tac [check_partial_col_input_monotone] >>
        `is_subset live1' live2'` by metis_tac [check_partial_col_output_monotone] >>
        `IMAGE f (domain live1') = domain flive1'` by metis_tac [check_partial_col_IMAGE] >>
        rw []
    )

    (* Set *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        `domain live2' = (set (MAP FST (toAList s))) UNION (domain live2)` by metis_tac [check_partial_col_domain, FST] >>
        `INJ f (domain live2') UNIV` by metis_tac [check_partial_col_success_INJ] >>
        `set (MAP FST (toAList s)) = domain s` by rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
        `domain live2' = domain s UNION domain live2` by metis_tac [check_partial_col_domain, FST] >>
        `domain s SUBSET domain live2'` by rw [SUBSET_DEF] >>
        `INJ f (domain s) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
        `?live1' flive1'. check_col f s = SOME (live1', flive1')` by metis_tac [check_col_success] >>
        qexists_tac `live1'` >>
        qexists_tac `flive1'` >>
        rw []
        THEN1 metis_tac [check_col_output]
        THEN1 fs [check_col_def, is_subset_def]
    )

    (* Branch *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        fs [check_live_tree_def] >>
        Cases_on `o'` >> fs [check_live_tree_def] >> TRY (rename1 `toAList cutset`) >>
        Cases_on `check_live_tree f (get_live_tree ct) live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `check_live_tree f (get_live_tree ct') live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?live11 flive11. check_clash_tree f ct live1 flive1 = SOME (live11, flive11)` by metis_tac [] >>
        `?live12 flive12. check_clash_tree f ct' live1 flive1 = SOME (live12, flive12)` by metis_tac [] >>
        rw []
        THEN1 (
            sg `is_subset live11 q` THEN1 (
              last_x_assum (qspecl_then [`f`, `live1`, `flive1`, `live2`, `flive2`, `q`, `r`] assume_tac) >>
              res_tac >>
              `live1'' = live11` by metis_tac [SOME_11, PAIR_EQ] >>
              fs []
            ) >>
            sg `is_subset live12 q'` THEN1 (
              first_x_assum (qspecl_then [`f`, `live1`, `flive1`, `live2`, `flive2`, `q'`, `r'`] assume_tac) >>
              res_tac >>
              `live1'' = live12` by metis_tac [SOME_11, PAIR_EQ] >>
              fs []
            ) >>
            `!(a : num_set) (b : num_set) (c : num_set). is_subset a b ==> is_subset (difference a c) (difference b c)` by rw [is_subset_def, domain_difference, SUBSET_DEF] >>
            `is_subset (difference live12 q) (difference q' q)` by rw [] >>
            `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
            `?a b. check_partial_col f (MAP FST (toAList (difference live12 q))) q r = SOME (a, b)` by metis_tac [check_partial_col_list_monotone] >>
            `INJ f (domain live1) UNIV` by metis_tac [is_subset_def, INJ_SUBSET, UNIV_SUBSET] >>
            `domain flive12 = IMAGE f (domain live12)` by metis_tac [check_clash_tree_output] >>
            `INJ f (domain live12) UNIV` by metis_tac [check_clash_tree_output] >>
            `?a fa. check_partial_col f (MAP FST (toAList (difference q live12))) live12 flive12 = SOME (a, fa)` by metis_tac [check_partial_col_branch_comm] >>
            `is_subset (difference live11 live12) (difference q live12)` by rw [] >>
            `?b fb. check_partial_col f (MAP FST (toAList (difference live11 live12))) live12 flive12 = SOME (b, fb)` by metis_tac [check_partial_col_list_monotone] >>
            `domain flive11 = IMAGE f (domain live11)` by metis_tac [check_clash_tree_output] >>
            `?c fc. check_partial_col f (MAP FST (toAList (difference live12 live11))) live11 flive11 = SOME (c, fc)` by metis_tac [check_partial_col_branch_comm] >>
            qexists_tac `c` >>
            qexists_tac `fc` >>
            simp [] >>
            strip_tac
            THEN1 metis_tac [check_partial_col_IMAGE]
            THEN1 (
                `domain c = set (MAP FST (toAList (difference live12 live11))) UNION domain live11` by metis_tac [check_partial_col_domain, FST] >>
                `domain c = domain live11 UNION domain live12` by metis_tac [branch_domain, check_partial_col_domain, FST] >>
                `domain live2' = domain q UNION domain q'` by metis_tac [branch_domain, check_partial_col_domain, FST] >>
                rw [is_subset_def] >>
                rw [SUBSET_DEF] >>
                metis_tac [SUBSET_DEF, is_subset_def]
            )
        )
        THEN1 (
            Cases_on `check_partial_col f (MAP FST (toAList (difference q' q))) q r` >> fs [] >>
            Cases_on `x` >> fs [] >>
            `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
            `domain r'' = IMAGE f (domain q'') /\ INJ f (domain q'') UNIV` by metis_tac [check_partial_col_IMAGE, check_partial_col_success_INJ] >>
            `INJ f (domain live2') UNIV` by metis_tac [check_partial_col_IMAGE, check_partial_col_success_INJ] >>
            `domain live2' = set (MAP FST (toAList cutset)) UNION domain q''` by metis_tac[check_partial_col_domain, FST] >>
            `set (MAP FST (toAList cutset)) = domain cutset` by rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
            `domain cutset SUBSET domain live2'` by rw [SUBSET_DEF] >>
            `INJ f (domain cutset) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
            `?live1' flive1'. check_col f cutset = SOME (live1', flive1')` by metis_tac [check_col_success] >>
            qexists_tac `live1'` >>
            qexists_tac `flive1'` >>
            rw []
            THEN1 metis_tac [check_col_output]
            THEN1 fs [check_col_def, is_subset_def]
        )
    )

    (* Seq *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        Cases_on `check_live_tree f (get_live_tree ct') live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?t2_out ft2_out. check_clash_tree f ct' live1 flive1 = SOME (t2_out, ft2_out) /\ IMAGE f (domain t2_out) = domain ft2_out /\ is_subset t2_out q` by metis_tac [] >>
        simp [] >>
        `IMAGE f (domain q) = domain r` by metis_tac [check_live_tree_success] >>
        `INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
        metis_tac []
    )
)

val _ = export_theory ();
