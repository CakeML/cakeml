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

val numset_list_insert_FOLDL = Q.store_thm("numset_list_insert_FOLDL",
    `!l live. numset_list_insert l live = FOLDL (\live x. insert x () live) live l`,
    Induct_on `l` >> rw [numset_list_insert_def]
)

val numset_list_insert_nottailrec_FOLDR = Q.store_thm("numset_list_insert_nottailrec_FOLDR",
    `!l live. numset_list_insert_nottailrec l live = FOLDR (\x live. insert x () live) live l`,
    Induct_on `l` >> rw [numset_list_insert_nottailrec_def]
)

val both_numset_list_insert_equal = Q.store_thm("both_numset_list_insert_equal",
    `!l live.
    numset_list_insert l live = numset_list_insert_nottailrec (REVERSE l) live`,

    rw [numset_list_insert_FOLDL, numset_list_insert_nottailrec_FOLDR, FOLDR_FOLDL_REVERSE]
)

val numset_list_insert_monotone = Q.store_thm("numset_list_insert_monotone",
    `!l s1 s2.
    is_subset s1 s2 ==> is_subset (numset_list_insert l s1) (numset_list_insert l s2)`,
    Induct_on `l` >>
    rw [numset_list_insert_def] >>
    `is_subset (insert h () s1) (insert h () s2)` by simp [insert_monotone] >>
    rw []
)

val domain_numset_list_insert = Q.store_thm("domain_numset_list_insert",
    `!l s.  domain (numset_list_insert l s) = set l UNION domain s`,
    Induct_on `l` >>
    rw [numset_list_insert_def] >>
    metis_tac [numset_list_insert_def, INSERT_UNION_EQ, UNION_COMM]
)

(* why breaking encapsulation like this? To get rid of the assumption `wf s` *)
val lookup_insert_id = Q.store_thm("lookup_insert_id",
    `!x (y:unit) s. lookup x s = SOME () ==> s = insert x () s`,

    recInduct insert_ind >>
    rw []
    THEN1 (
        imp_res_tac domain_lookup >>
        fs [domain_empty]
    )
    THEN1 (
        fs [lookup_def] >>
        once_rewrite_tac [insert_def] >>
        simp []
    )
    THEN1 (
        fs [lookup_def] >>
        Cases_on `EVEN k` >> fs [] >>
        once_rewrite_tac [insert_def] >>
        rw []
    )
    THEN1 (
        fs [lookup_def] >>
        Cases_on `EVEN k` >> fs [] >>
        Cases_on `k=0` >> fs [] >>
        once_rewrite_tac [insert_def] >>
        rw []
    )
)

val numset_list_insert_FILTER = Q.store_thm("numset_list_insert_FILTER",
   `!l live.
    numset_list_insert (FILTER (λx. lookup x live = NONE) l) live =
    numset_list_insert l live`,

    sg `!x l live. lookup x live = SOME () ==> lookup x (numset_list_insert_nottailrec l live) = SOME ()` THEN1 (
        Induct_on `l` >>
        rw [numset_list_insert_nottailrec_def, lookup_insert]
    ) >>
    rw [both_numset_list_insert_equal, GSYM FILTER_REVERSE] >>
    qabbrev_tac `l' = REVERSE l` >>
    WEAKEN_TAC (fn x => true) >>
    Induct_on `l'` >>
    rw [numset_list_insert_nottailrec_def] >>
    Cases_on `lookup h live` >> fs [NOT_SOME_NONE] >>
    simp [lookup_insert_id]
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

val check_partial_col_branch_domain = Q.store_thm("check_partial_col_branch_domain",`
    !(live1 : num_set) (live2 : num_set) flive1 liveout fliveout.
    check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 = SOME (liveout, fliveout) ==>
    domain liveout = domain live1 UNION domain live2`,
    metis_tac [branch_domain, check_partial_col_domain, FST]
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

val get_live_tree_correct_lemma = Q.store_thm("get_live_tree_correct_lemma",
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

val get_live_tree_correct = Q.store_thm("get_live_tree_correct",
    `!f live flive ct live' flive'.
    IMAGE f (domain live) = domain flive ==>
    INJ f (domain live) UNIV ==>
    check_live_tree f (get_live_tree ct) live flive = SOME (live', flive') ==>
    ?live'' flive''. check_clash_tree f ct live flive = SOME (live'', flive'')
    `,
    metis_tac [get_live_tree_correct_lemma, is_subset_def, SUBSET_REFL]
)

val get_live_tree_correct_LN = Q.store_thm("get_live_tree_correct_LN",
    `!f live flive ct live' flive'.
    check_live_tree f (get_live_tree ct) LN LN = SOME (live', flive') ==>
    ?live'' flive''. check_clash_tree f ct LN LN = SOME (live'', flive'')
    `,
    rw [get_live_tree_correct]
)


val check_partial_col_FILTER_NONE = Q.store_thm("check_partial_col_FILTER_NONE",
    `!f l (live' : num_set) (live : num_set) flive liveout fliveout.
    domain flive = IMAGE f (domain live) /\
    domain live = domain live' /\
    INJ f (domain live) UNIV /\
    check_partial_col f (FILTER (\x. lookup x live' = NONE) l) live flive = SOME (liveout, fliveout) ==>
    ?liveout' fliveout'. check_partial_col f l live flive = SOME (liveout', fliveout') /\
    domain liveout' = domain liveout`,

    rw [] >>
    `INJ f (domain liveout) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `domain liveout = set (FILTER (\x. lookup x live' = NONE) l) UNION domain live` by metis_tac [check_partial_col_domain, FST] >>
    `!x. (lookup x live = NONE) <=> (lookup x live' = NONE)` by metis_tac [lookup_NONE_domain] >>
    sg `set (FILTER (\x. lookup x live' = NONE) l) UNION domain live = set l UNION domain live` THEN1 (
      rw [EXTENSION, MEM_FILTER, lookup_NONE_domain, domain_lookup] >>
      Cases_on `lookup x live` >>
      `!a. a <> SOME () <=> a = NONE` by (Cases_on `a` >> rw []) >>
      rw [] >>
      metis_tac []
    ) >>
    metis_tac [check_partial_col_success, check_partial_col_domain, FST]
)

val check_partial_col_same_domain = Q.store_thm("check_partial_col_same_domain",
    `!l live1 flive1 live2 flive2 live1out flive1out f.
    domain live1 = domain live2 /\
    domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) /\
    INJ f (domain live1) UNIV /\
    check_partial_col f l live1 flive1 = SOME (live1out, flive1out) ==>
    ?live2out flive2out. check_partial_col f l live2 flive2 = SOME (live2out, flive2out) /\
    domain live1out = domain live2out`,

    rw [] >>
    `domain live1out = set l UNION domain live1` by metis_tac [check_partial_col_domain, FST] >>
    `INJ f (domain live1out) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `?a b. check_partial_col f l live2 flive2 = SOME (a, b)` by metis_tac [check_partial_col_success] >>
    `domain a = set l UNION domain live1` by metis_tac [check_partial_col_domain, FST] >>
    rw []
)

val check_live_tree_same_domain = Q.store_thm("check_live_tree_same_domain",
    `!lt live1 flive1 live2 flive2 live1out flive1out f.
    domain live1 = domain live2 ==>
    INJ f (domain live1) UNIV ==>
    domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) ==>
    check_live_tree f lt live1 flive1 = SOME (live1out, flive1out) ==>
    ?live2out flive2out. check_live_tree f lt live2 flive2 = SOME (live2out, flive2out) /\
    domain live1out = domain live2out`,

    Induct_on `lt` >>
    rw [check_live_tree_def]

    (* StartLive *)
    THEN1 (
        Cases_on `check_partial_col f l live1 flive1` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_partial_col f l live2 flive2 = SOME (a, b)` by metis_tac [check_partial_col_same_domain] >>
        rw [domain_numset_list_delete]
    )

    (* EndLive *)
    THEN1 (
        metis_tac [check_partial_col_same_domain]
    )

    (* Branch *)
    THEN1 (
        Cases_on `check_live_tree f lt live1 flive1` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `check_live_tree f lt' live1 flive1` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_live_tree f lt live2 flive2 = SOME (a, b) /\ domain a = domain q` by metis_tac [] >>
        `?a b. check_live_tree f lt' live2 flive2 = SOME (a, b) /\ domain a = domain q'` by metis_tac [] >>
        simp [] >>
        `set (MAP FST (toAList (difference a' a))) UNION domain a = domain a UNION domain a'` by rw [branch_domain] >>
        `domain live1out = domain a UNION domain a'` by metis_tac [check_partial_col_branch_domain] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
        `INJ f (domain live1out) UNIV` by metis_tac [check_partial_col_success_INJ] >>
        `domain b = IMAGE f (domain a)` by metis_tac [check_live_tree_success] >>
        `?live2out flive2out.  check_partial_col f (MAP FST (toAList (difference a' a))) a b = SOME (live2out,flive2out)` by metis_tac [check_partial_col_success] >>
        `domain live2out = domain a UNION domain a'` by metis_tac [check_partial_col_branch_domain] >>
        rw []
    )

    (* Seq *)
    THEN1 (
        Cases_on `check_live_tree f lt' live1 flive1` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_live_tree f lt' live2 flive2 = SOME (a, b) /\ domain q = domain a` by metis_tac [] >>
        simp [] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
        `domain b = IMAGE f (domain a)` by metis_tac [check_live_tree_success] >>
        `?c d. check_live_tree f lt a b = SOME (c, d) /\ domain live1out = domain c` by metis_tac [] >>
        rw []
    )
)

val fix_endlive_check_live_tree = Q.store_thm("fix_endlive_check_live_tree",
    `!lt lt' live1 live1out live2 flive2 live2out' flive2out' f.
    domain live1 = domain live2 /\
    (lt', live1out) = fix_endlive lt live1 /\
    domain flive2 = IMAGE f (domain live2) /\
    INJ f (domain live2) UNIV /\
    check_live_tree f lt' live2 flive2 = SOME (live2out', flive2out') ==>
    ?live2out flive2out. check_live_tree f lt live2 flive2 = SOME (live2out, flive2out) /\
    domain live1out = domain live2out' /\
    domain live2out' = domain live2out
    `,

    Induct_on `lt`

    (* StartLive *)
    THEN1 (
        rw [fix_endlive_def, check_live_tree_def] >> fs [check_live_tree_def] >>
        Cases_on `check_partial_col f l live2 flive2` >> fs [] >>
        `domain (numset_list_delete l live2) = domain live2out'` by rw [] >>
        fs [domain_numset_list_delete]
    )

    (* EndLive *)
    THEN1 (
        rw [fix_endlive_def, check_live_tree_def] >> fs [check_live_tree_def] >>
        `?live2out flive2out. check_partial_col f l live2 flive2 = SOME (live2out, flive2out) /\ domain live2out = domain live2out'` by metis_tac [check_partial_col_FILTER_NONE] >>
        qexists_tac `live2out` >>
        qexists_tac `flive2out` >>
        simp [domain_numset_list_insert] >>
        metis_tac [check_partial_col_domain, FST]
    )

    (* Branch *)
    THEN1 (
        rename1 `Branch lt1 lt2` >>
        simp [fix_endlive_def, check_live_tree_def] >>
        rpt gen_tac >> strip_tac >>
        NTAC 2 (pairarg_tac >> fs []) >>
        rfs [check_live_tree_def] >>
        Cases_on `check_live_tree f lt1' live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `check_live_tree f lt2' live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_live_tree f lt1 live2 flive2 = SOME (a, b) /\ domain live1' = domain q /\ domain q = domain a` by metis_tac [] >>
        `?a b. check_live_tree f lt2 live2 flive2 = SOME (a, b) /\ domain live2' = domain q' /\ domain q' = domain a` by metis_tac [] >>
        `set (MAP FST (toAList (difference a' a))) UNION domain a = domain a UNION domain a'` by rw [branch_domain] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
        `INJ f (domain live2out') UNIV` by metis_tac [check_partial_col_success_INJ] >>
        `domain live2out' = domain q UNION domain q'` by metis_tac [check_partial_col_branch_domain] >>
        `INJ f (domain a UNION domain a') UNIV` by metis_tac [] >>
        `domain b = IMAGE f (domain a)` by metis_tac [check_live_tree_success] >>
        `?live2out flive2out. check_partial_col f (MAP FST (toAList (difference a' a))) a b = SOME (live2out, flive2out)` by metis_tac [check_partial_col_success] >>
        qexists_tac `live2out` >>
        qexists_tac `flive2out` >>
        rw []
        THEN1 rw [domain_numset_list_insert, branch_domain]
        THEN1 metis_tac [check_partial_col_branch_domain]
    )

    (* Seq *)
    THEN1 (
        rename1 `Seq lt1 lt2` >>
        simp [fix_endlive_def, check_live_tree_def] >>
        rpt gen_tac >> strip_tac >>
        NTAC 2 (pairarg_tac >> fs []) >>
        rfs [check_live_tree_def] >>
        Cases_on `check_live_tree f lt2' live2 flive2` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_live_tree f lt2 live2 flive2 = SOME (a, b) /\ domain live2' = domain q /\ domain q = domain a` by metis_tac [] >>
        simp [] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_success] >>
        last_x_assum (qspecl_then [`lt1'`, `live2'`, `live1'`, `q`, `r`, `live2out'`, `flive2out'`, `f`] assume_tac) >>
        `?a b. check_live_tree f lt1 q r = SOME (a, b) /\ domain live1' = domain a /\ domain a = domain live2out'` by metis_tac [] >>
        `domain b = IMAGE f (domain a)` by metis_tac [check_live_tree_success] >>
        `?c d. check_live_tree f lt1 a b = SOME (c, d) /\ domain c = domain a'` by metis_tac [check_live_tree_same_domain] >>
        rw []
    )
)

val check_endlive_fixed_fix_endlive = Q.store_thm("check_endlive_fixed_fix_endlive",
    `!lt live liveout lt'.
    fix_endlive lt live = (lt', liveout) ==>
    check_endlive_fixed lt' live = (T, liveout)`,

    Induct_on `lt` >>
    rw [fix_endlive_def, check_endlive_fixed_def]
    (* StartLive *)
    THEN1 (
      rw [check_endlive_fixed_def]
    )
    (* EndLive *)
    THEN1 (
      rw [check_endlive_fixed_def]
      THEN1 simp [EVERY_FILTER]
      THEN1 simp [numset_list_insert_FILTER]
    ) >>
    (* Branch & Seq *)
    NTAC 2 (pairarg_tac >> fs []) >>
    res_tac >>
    rw [check_endlive_fixed_def]
)

val check_partial_col_numset_list_insert = Q.store_thm("check_partial_col_numset_list_insert",
    `!f s fs s' fs' l.
    check_partial_col f l s fs = SOME (s', fs') ==>
    s' = numset_list_insert l s`,
    Induct_on `l` >>
    rw [check_partial_col_def, numset_list_insert_def] >>
    Cases_on `lookup h s` >> fs [] >>
    Cases_on `lookup (f h) fs` >> fs [] >>
    metis_tac [lookup_insert_id]
)


val check_live_tree_forward_output = Q.store_thm("check_live_tree_forward_output", `
    !lt live flive live' flive' f live''.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_endlive_fixed_forward lt live = (T, live'') /\
    check_live_tree_forward f lt live flive = SOME (live',flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV /\
    live'' = live' `,

    Induct_on `lt`
    (* StartLive *)
    THEN1 (
      rw [check_live_tree_forward_def, check_endlive_fixed_forward_def]
      THEN1 metis_tac [check_partial_col_IMAGE]
      THEN1 metis_tac [check_partial_col_success_INJ]
      THEN1 metis_tac [check_partial_col_numset_list_insert]
    )
    (* EndLive *)
    THEN1 (
      simp [check_live_tree_forward_def, check_endlive_fixed_forward_def] >>
      rpt gen_tac >> strip_tac >>
      `set l SUBSET domain live` by fs [SUBSET_DEF, domain_lookup, EVERY_MEM] >>
      `domain live = set l UNION domain live` by (rw [EXTENSION] >> Cases_on `MEM x l` >> fs [SUBSET_DEF]) >>
      `?a b. check_partial_col f l live flive = SOME (a, b)` by metis_tac [check_partial_col_success] >>
      strip_tac
      THEN1 metis_tac [numset_list_delete_IMAGE]
      THEN1 (
        `domain (numset_list_delete l live) SUBSET domain live` by metis_tac [domain_numset_list_delete, DIFF_SUBSET] >>
        metis_tac [INJ_SUBSET, UNIV_SUBSET]
      )
    )
    (* Branch *)
    THEN1 (
      simp [check_live_tree_forward_def, check_endlive_fixed_forward_def] >>
      rpt gen_tac >> strip_tac >>
      NTAC 2 (pairarg_tac >> fs []) >> rveq >>
      Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      Cases_on `check_live_tree_forward f lt' live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [] >>
      rpt strip_tac
      THEN1 metis_tac [check_partial_col_IMAGE]
      THEN1 metis_tac [check_partial_col_success_INJ]
      THEN1 metis_tac [check_partial_col_numset_list_insert]
    )
    (* Seq *)
    THEN1 (
      simp [check_live_tree_forward_def, check_endlive_fixed_forward_def] >>
      rpt gen_tac >> strip_tac >>
      NTAC 2 (pairarg_tac >> fs []) >> rveq >>
      Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV /\ q = live1` by metis_tac [] >>
      rpt strip_tac >>
      metis_tac []
    )
)

val exists_IMAGE_f = Q.store_thm("exists_IMAGE_f",
    `!f (s : num_set). ?(fs : num_set). domain fs = IMAGE f (domain s)`,
    rw [] >>
    qexists_tac `fromAList (MAP (\x. (f (FST x), ())) (toAList s))` >>
    rw [EXTENSION, domain_fromAList, MEM_MAP, MEM_toAList, EXISTS_PROD] >>
    rw [domain_lookup]
)

val check_endlive_fixed_forward_eq_check_live_tree_forward = Q.store_thm("check_endlive_fixed_forward_eq_check_live_tree_forward",
    `!lt live flive liveout1 fliveout1 liveout2 b.
    check_live_tree_forward f lt live flive = SOME (liveout1, fliveout1) /\
    check_endlive_fixed_forward lt live = (b, liveout2) ==>
    liveout1 = liveout2`,

    Induct_on `lt` >>
    rw [check_endlive_fixed_forward_def, check_live_tree_forward_def]
    (* StartLive *)
    THEN1 metis_tac [check_partial_col_numset_list_insert]
    (* Branch *)
    THEN1 (
      NTAC 2 (pairarg_tac >> fs []) >>
      Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      Cases_on `check_live_tree_forward f lt' live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      metis_tac [check_partial_col_numset_list_insert]
    )
    (* Seq *)
    THEN1 (
      NTAC 2 (pairarg_tac >> fs []) >>
      Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
      Cases_on `x` >> fs [] >>
      metis_tac [check_partial_col_numset_list_insert]
    )
)

val check_endlive_fixed_backward_forward = Q.store_thm("check_endlive_fixed_backward_forward",
    `!live lt liveout liveout'.
    check_endlive_fixed lt live = (T, liveout) /\
    is_subset liveout liveout' ==>
    ?livein. check_endlive_fixed_forward lt liveout' = (T, livein) /\
    is_subset live livein`,

    Induct_on `lt` >>
    simp [check_endlive_fixed_def, check_endlive_fixed_forward_def]

    (* StartLive *)
    THEN1 (
      rw [is_subset_def, domain_numset_list_delete, domain_numset_list_insert] >>
      fs [SUBSET_DEF] >>
      rw [] >>
      Cases_on `MEM x l` >> fs []
    )

    (* EndLive *)
    THEN1 (
      rw [domain_lookup]
      THEN1 (
        fs [is_subset_def, domain_numset_list_insert, SUBSET_DEF, EVERY_MEM] >>
        rw [] >>
        `?y. lookup x liveout' = SOME y` by metis_tac [domain_lookup] >>
        Cases_on `y` >> simp []
      )
      THEN1 (
        fs [is_subset_def, domain_numset_list_delete, domain_numset_list_insert, SUBSET_DEF, EVERY_MEM] >>
        strip_tac >> CCONTR_TAC >> fs [] >>
        `lookup x live = NONE` by rw [] >>
        fs [lookup_NONE_domain]
      )
    )

    (* Branch *)
    THEN1 (
      rw [] >>
      NTAC 4 (pairarg_tac >> fs []) >> rveq >>
      `domain live1' UNION domain live2' SUBSET domain liveout'` by fs [is_subset_def, domain_numset_list_insert, branch_domain] >>
      `is_subset live1' liveout'` by fs [is_subset_def] >>
      `is_subset live2' liveout'` by fs [is_subset_def] >>
      `?livein1. check_endlive_fixed_forward lt liveout' = (T, livein1) /\ is_subset live livein1` by metis_tac [] >>
      `?livein2. check_endlive_fixed_forward lt' liveout' = (T, livein2) /\ is_subset live livein2` by metis_tac [] >>
      fs [] >> rveq >>
      fs [is_subset_def, domain_numset_list_insert, branch_domain] >>
      `domain live1 SUBSET domain live1 UNION domain live2` by fs [] >>
      metis_tac [SUBSET_TRANS]
    )

    (* Seq *)
    THEN1 (
      rw [] >>
      NTAC 4 (pairarg_tac >> fs []) >> rveq >>
      `?livein1. check_endlive_fixed_forward lt liveout' = (T, livein1) /\ is_subset live2' livein1` by metis_tac [] >>
      fs [] >> rveq >>
      `?livein2. check_endlive_fixed_forward lt' live1 = (T, livein2) /\ is_subset live livein2` by metis_tac [] >>
      fs [] >> rveq >> rw []
    )
)


val check_endlive_fixed_eq_get_live_backward = Q.store_thm("check_endlive_fixed_eq_get_live_backward",
    `!lt live liveout b.
    check_endlive_fixed lt live = (b, liveout) ==>
    liveout = get_live_backward lt live`,

    Induct_on `lt` >>
    rw [check_endlive_fixed_def, get_live_backward_def] >>
    NTAC 2 (pairarg_tac >> fs []) >>
    res_tac >> fs []
)


val check_live_tree_forward_backward = Q.store_thm("check_live_tree_forward_backward",
    `!f live flive lt liveout fliveout liveout' fliveout' bla.
    INJ f (domain live) UNIV /\
    domain flive = IMAGE f (domain live) /\ domain fliveout' = IMAGE f (domain liveout') /\
    is_subset (get_live_backward lt liveout') live /\
    check_endlive_fixed lt liveout' = (T, bla) /\
    check_live_tree_forward f lt live flive = SOME (liveout, fliveout)
    ==>
    ?flivein. check_live_tree f lt liveout' fliveout' = SOME (get_live_backward lt liveout', flivein) /\
    is_subset liveout' liveout`,

    Induct_on `lt` >>
    rw [check_live_tree_forward_def, check_live_tree_def, check_endlive_fixed_def, get_live_backward_def]
    (* StartLive *)
    THEN1 (
        `domain liveout = set l UNION domain live` by metis_tac [check_partial_col_domain, FST] >>
        `INJ f (domain liveout) UNIV` by metis_tac [check_partial_col_success_INJ] >>
        fs [is_subset_def, domain_numset_list_delete] >>
        sg `set l UNION domain liveout' SUBSET domain liveout` THEN1 (
            rw [SUBSET_DEF] >>
            Cases_on `MEM x l` >>
            fs [SUBSET_DEF]
        ) >>
        `INJ f (set l UNION domain liveout') UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
        `?a fa. check_partial_col f l liveout' fliveout' = SOME (a, fa)` by metis_tac [check_partial_col_success] >>
        rw [SUBSET_DEF] >>
        Cases_on `MEM x l` >> fs [SUBSET_DEF]
    )
    (* EndLive *)
    THEN1 (
        `INJ f (set l UNION domain liveout') UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET, is_subset_def, domain_numset_list_insert] >>
        `?a b. check_partial_col f l liveout' fliveout' = SOME (a, b)` by metis_tac [check_partial_col_success] >>
        rw []
        THEN1 metis_tac [check_partial_col_numset_list_insert]
        THEN1 (
          fs [is_subset_def, domain_numset_list_delete, domain_numset_list_insert, SUBSET_DEF] >>
          rw [] >>
          CCONTR_TAC >> fs [] >>
          `lookup x liveout' = NONE` by fs [EVERY_MEM] >>
          fs [lookup_NONE_domain]
        )
    )
    (* Branch *)
    THEN1 (
        Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        Cases_on `check_live_tree_forward f lt' live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        NTAC 2 (pairarg_tac >> fs []) >> rveq >>
        fs [is_subset_def, branch_domain, domain_numset_list_insert] >>
        `?flivein.  check_live_tree f lt liveout' fliveout' = SOME (get_live_backward lt liveout', flivein) /\ domain liveout' ⊆ domain q` by metis_tac [] >>
        `?flivein.  check_live_tree f lt' liveout' fliveout' = SOME (get_live_backward lt' liveout', flivein) /\ domain liveout' ⊆ domain q'` by metis_tac [] >>
        rw [] >>
        qabbrev_tac `a = get_live_backward lt liveout'` >>
        qabbrev_tac `b = get_live_backward lt' liveout'` >>
        `a = live1 /\ b = live2` by metis_tac [check_endlive_fixed_eq_get_live_backward] >>
        rveq >>
        sg `INJ f (set (MAP FST (toAList (difference b a))) UNION domain a) UNIV` THEN1 (
            simp [branch_domain] >>
            `(domain a UNION domain b) SUBSET domain live` by fs [] >>
            metis_tac [INJ_SUBSET, UNIV_SUBSET]
        ) >>
        sg `domain flivein = IMAGE f (domain a)` THEN1 (
          `?z. check_endlive_fixed_forward lt live = (T, z)` by metis_tac [check_endlive_fixed_backward_forward, is_subset_def] >>
          `INJ f (domain q) UNIV` by metis_tac [check_live_tree_forward_output] >>
          `INJ f (domain liveout') UNIV` by metis_tac [is_subset_def, INJ_SUBSET, UNIV_SUBSET] >>
          metis_tac [check_live_tree_success]
        ) >>
        `?c d. check_partial_col f (MAP FST (toAList (difference b a))) a flivein = SOME (c, d)` by metis_tac [check_partial_col_success] >>
        rw []
        THEN1 metis_tac [check_partial_col_numset_list_insert]
        THEN1 (
            `domain liveout = domain q UNION domain q'` by metis_tac [check_partial_col_domain, FST, branch_domain] >>
            fs [SUBSET_DEF]
        )
    )
    (* Seq *)
    THEN1 (
        Cases_on `check_live_tree_forward f lt live flive` >> fs [] >>
        Cases_on `x` >> fs [] >>
        NTAC 2 (pairarg_tac >> fs []) >> rveq >>
        qabbrev_tac `a = get_live_backward lt' liveout'` >>
        qabbrev_tac `b = get_live_backward lt a` >>
        `live2 = a /\ bla = b` by metis_tac [check_endlive_fixed_eq_get_live_backward] >>
        rveq >>
        sg `is_subset a q` THEN1 (
          `?(fmiddle:num_set). domain fmiddle = IMAGE f (domain a)` by simp [exists_IMAGE_f] >>
          last_x_assum (qspecl_then [`f`, `live`, `flive`, `q`, `r`, `a`, `fmiddle`, `b`] assume_tac) >>
          metis_tac []
        ) >>
        `?z. check_endlive_fixed_forward lt live = (T, z)` by metis_tac [check_endlive_fixed_backward_forward] >>
        `domain r = IMAGE f (domain q) /\ INJ f (domain q) UNIV` by metis_tac [check_live_tree_forward_output] >>
        `?flivein. check_live_tree f lt' liveout' fliveout' = SOME (a,flivein) /\ is_subset liveout' liveout` by metis_tac [] >>
        sg `domain flivein = IMAGE f (domain a)` THEN1 (
          `?z. check_endlive_fixed_forward lt' q = (T, z)` by metis_tac [check_endlive_fixed_backward_forward] >>
          `INJ f (domain liveout) UNIV` by metis_tac [check_live_tree_forward_output] >>
          `INJ f (domain liveout') UNIV` by (fs [is_subset_def] >> metis_tac [INJ_SUBSET, UNIV_SUBSET]) >>
          metis_tac [check_live_tree_success]
        ) >>
        last_x_assum (qspecl_then [`f`, `live`, `flive`, `q`, `r`, `a`, `flivein`, `b`] assume_tac) >>
        `?flivein'. check_live_tree f lt a flivein = SOME (get_live_backward lt a, flivein')` by metis_tac [] >>
        rw []
    )
)

val fix_domination_fixes_domination = Q.store_thm("fix_domination_fixes_domination",
    `!lt. domain (get_live_backward (fix_domination lt) LN) = EMPTY`,
    rw [get_live_backward_def, fix_domination_def, domain_numset_list_delete] >>
    rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup]
)

val fix_domination_check_live_tree = Q.store_thm("fix_domination_check_live_tree",
    `!f lt liveout fliveout.
    check_live_tree f (fix_domination lt) LN LN = SOME (liveout, fliveout) ==>
    ?liveout' fliveout'. check_live_tree f lt LN LN = SOME (liveout', fliveout')`,

    rw [check_live_tree_def, fix_domination_def] >>
    Cases_on `check_live_tree f lt LN LN` >> fs [] >>
    Cases_on `x` >> fs []
)

val fix_domination_check_endlive_fixed = Q.store_thm("fix_domination_check_endlive_fixed",
    `!lt liveout.
    check_endlive_fixed lt LN = (T, liveout) ==>
    ?liveout'. check_endlive_fixed (fix_domination lt) LN = (T, liveout')`,
    rw [check_endlive_fixed_def, fix_domination_def]
)

val fix_live_tree_fixes_everything = Q.store_thm("fix_live_tree_fixes_everything",
    `!lt.
    is_subset (get_live_backward (fix_live_tree lt) LN) LN /\
    ?liveout. check_endlive_fixed (fix_live_tree lt) LN = (T, liveout)`,

    rw [is_subset_def, fix_live_tree_def]
    THEN1 rw [fix_domination_fixes_domination]
    THEN1 (
        Cases_on `fix_endlive lt LN` >> fs [] >>
        metis_tac [fix_domination_check_endlive_fixed, check_endlive_fixed_fix_endlive]
    )
)

val fix_live_tree_check_live_tree = Q.store_thm("fix_live_tree_check_live_tree",
    `!f lt liveout fliveout.
    check_live_tree f (fix_live_tree lt) LN LN = SOME (liveout, fliveout) ==>
    ?liveout' fliveout'. check_live_tree f lt LN LN = SOME (liveout', fliveout')`,

    rw [fix_live_tree_def] >>
    Cases_on `fix_endlive lt LN` >> fs [] >>
    `?a b. check_live_tree f q LN LN = SOME (a, b)` by metis_tac [fix_domination_check_live_tree] >>
    qspecl_then [`lt`, `q`, `LN`, `r`, `LN`, `LN`, `a`, `b`, `f`] assume_tac fix_endlive_check_live_tree >>
    fs [] >>
    metis_tac []
)

val fix_live_tree_check_live_tree_forward_backward = Q.store_thm("fix_live_tree_check_live_tree_forward_backward",
    `!f lt liveout fliveout.
    check_live_tree_forward f (fix_live_tree lt) LN LN = SOME (liveout, fliveout) ==>
    ?livein flivein. check_live_tree f lt LN LN = SOME (livein, flivein)`,

    rw [] >>
    sg `?livein flivein. check_live_tree f (fix_live_tree lt) LN LN = SOME (livein, flivein)` THEN1 (
      `is_subset (get_live_backward (fix_live_tree lt) LN) (LN:num_set) /\ ?bla. check_endlive_fixed (fix_live_tree lt) LN = (T, bla)` by rw [fix_live_tree_fixes_everything] >>
      qspecl_then [`f`, `LN`, `LN`, `fix_live_tree lt`, `liveout`, `fliveout`, `LN`, `LN`, `bla`] assume_tac check_live_tree_forward_backward >>
      fs [] >>
      metis_tac []
    ) >>
    metis_tac [fix_live_tree_check_live_tree]
)

val _ = export_theory ();
