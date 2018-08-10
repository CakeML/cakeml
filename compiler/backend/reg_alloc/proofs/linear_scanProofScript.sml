open preamble sptreeTheory reg_allocTheory linear_scanTheory reg_allocProofTheory
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "linear_scanProof"

val _ = disable_tyabbrev_printing "type_ident"

val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

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

    (* Writes *)
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
    (* Reads *)
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

    (* Writes *)
    THEN1 (
        Cases_on `check_partial_col f l live1 flive1` >> fs [] >>
        Cases_on `x` >> fs [] >>
        `?a b. check_partial_col f l live2 flive2 = SOME (a, b)` by metis_tac [check_partial_col_same_domain] >>
        rw [domain_numset_list_delete]
    )

    (* Reads *)
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

    (* Writes *)
    THEN1 (
        rw [fix_endlive_def, check_live_tree_def] >> fs [check_live_tree_def] >>
        Cases_on `check_partial_col f l live2 flive2` >> fs [] >>
        `domain (numset_list_delete l live2) = domain live2out'` by rw [] >>
        fs [domain_numset_list_delete]
    )

    (* Reads *)
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
    (* Writes *)
    THEN1 (
      rw [check_endlive_fixed_def]
    )
    (* Reads *)
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
    (* Writes *)
    THEN1 (
      rw [check_live_tree_forward_def, check_endlive_fixed_forward_def]
      THEN1 metis_tac [check_partial_col_IMAGE]
      THEN1 metis_tac [check_partial_col_success_INJ]
      THEN1 metis_tac [check_partial_col_numset_list_insert]
    )
    (* Reads *)
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
    (* Writes *)
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

    (* Writes *)
    THEN1 (
      rw [is_subset_def, domain_numset_list_delete, domain_numset_list_insert] >>
      fs [SUBSET_DEF] >>
      rw [] >>
      Cases_on `MEM x l` >> fs []
    )

    (* Reads *)
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

val check_partial_col_numset_list_insert = Q.store_thm("check_partial_col_numset_list_insert",
    `!f l live flive liveout fliveout.
    check_partial_col f l live flive = SOME (liveout, fliveout) ==>
    liveout = numset_list_insert l live`,

    Induct_on `l` >>
    rw [numset_list_insert_def, check_partial_col_def] >>
    Cases_on `lookup h live` >> fs []
    THEN1 (
      Cases_on `lookup (f h) flive` >> fs [] >>
      res_tac
    )
    THEN1 (
        `live = insert h () live` by rw [lookup_insert_id] >>
        metis_tac []
    )
)

val check_live_tree_eq_get_live_backward = Q.store_thm("check_live_tree_eq_get_live_backward",
    `!f lt live flive liveout fliveout.
    check_live_tree f lt live flive = SOME (liveout, fliveout) ==>
    liveout = get_live_backward lt live`,

    Induct_on `lt` >>
    rw [check_live_tree_def, get_live_backward_def]
    (* Writes *)
    THEN1 (
        every_case_tac >> fs []
    )
    (* Reads *)
    THEN1 (
        metis_tac [check_partial_col_numset_list_insert]
    )
    (* Branch *)
    THEN1 (
        every_case_tac >> fs [] >>
        res_tac >>
        metis_tac [check_partial_col_numset_list_insert]
    )
    (* Seq *)
    THEN1 (
        every_case_tac >> fs [] >>
        res_tac >>
        metis_tac []
    )
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
    (* Writes *)
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
    (* Reads *)
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

val check_live_tree_forward_eq_get_live_forward = Q.store_thm("check_live_tree_forward_eq_get_live_forward",
    `!f lt live flive liveout fliveout.
    check_live_tree_forward f lt live flive = SOME (liveout, fliveout) ==>
    liveout = get_live_forward lt live`,

    Induct_on `lt` >>
    rw [check_live_tree_forward_def, get_live_forward_def] >>
    every_case_tac >> fs [] >>
    metis_tac [check_partial_col_numset_list_insert]
)

val check_endlive_fixed_forward_eq_get_live_forward = Q.store_thm("check_endlive_fixed_forward_eq_get_live_forward",
    `!lt live liveout b.
    check_endlive_fixed_forward lt live = (b, liveout) ==>
    liveout = get_live_forward lt live`,

    Induct_on `lt` >>
    rw [check_endlive_fixed_forward_def, get_live_forward_def] >>
    TRY (NTAC 2 (pairarg_tac >> fs [])) >>
    metis_tac [check_partial_col_numset_list_insert]
)

val size_of_live_tree_positive = Q.store_thm("size_of_live_tree_positive",
    `!lt. 0 <= size_of_live_tree lt`,
    Induct_on `lt` >> rw [size_of_live_tree_def]
)

val check_number_property_strong_monotone_weak = Q.store_thm("check_number_property_strong_monotone_weak",
    `!P Q lt n live.
    (!n' live'. P n' live' ==> Q n' live') /\
    check_number_property_strong P lt n live ==>
    check_number_property_strong Q lt n live`,

    Induct_on `lt` >>
    rw [check_number_property_strong_def] >>
    res_tac >> simp []
)


val check_number_property_strong_monotone = Q.store_thm("check_number_property_strong_monotone",
    `!P Q lt n live.
    (!n' live'. (n - size_of_live_tree lt) <= n' /\ P n' live' ==> Q n' live') /\
    check_number_property_strong P lt n live ==>
    check_number_property_strong Q lt n live`,

    Induct_on `lt` >>
    simp [check_number_property_strong_def, size_of_live_tree_def]
    (* Branch & Seq *)
    >> (
      rw []
      THEN1 (
        `!n' live'. n - size_of_live_tree lt' - size_of_live_tree lt <= n' /\ P n' live' ==> Q n' live'` by (
          rw [] >>
          `n - (size_of_live_tree lt + size_of_live_tree lt') <= n'` by intLib.COOPER_TAC >>
          rw []
        ) >>
        metis_tac []
      )
      THEN1 (
        `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
        `(!n' live'. n - size_of_live_tree lt' <= n' /\ P n' live' ==> Q n' live')` by (
            rw [] >>
            `n - (size_of_live_tree lt + size_of_live_tree lt') <= n'` by intLib.COOPER_TAC >>
            rw []
        ) >>
        metis_tac []
      )
    )
)

val check_number_property_strong_end = Q.store_thm("check_number_property_strong_end",
    `!P lt n live.
    check_number_property_strong P lt n live ==>
    P (n - size_of_live_tree lt) (get_live_backward lt live)`,

    Induct_on `lt` >>
    rw [check_number_property_strong_def, get_live_backward_def, size_of_live_tree_def] >>
    (* Seq *)
    res_tac >>
    `n - size_of_live_tree lt' - size_of_live_tree lt = n - (size_of_live_tree lt + size_of_live_tree lt')` by intLib.COOPER_TAC >>
    metis_tac []
)

val check_number_property_monotone_weak = Q.store_thm("check_number_property_monotone_weak",
    `!P Q lt n live.
    (!n' live'. P n' live' ==> Q n' live') /\
    check_number_property P lt n live ==>
    check_number_property Q lt n live`,

    Induct_on `lt` >>
    rw [check_number_property_def] >>
    res_tac >> simp []
)


val lookup_numset_list_add_if = Q.store_thm("lookup_numset_list_add_if",
    `!r l v s.
    lookup r (numset_list_add_if l v s P) =
        if MEM r l then
          case lookup r s of
          | (SOME vr) =>
            if P v vr then SOME v
            else SOME vr
          | NONE =>
            SOME v
        else
          lookup r s
    `,

    Induct_on `l` >>
    simp [numset_list_add_if_def] >>
    rpt gen_tac >>
    Cases_on `lookup h s` >> fs []
    THEN1 (
        Cases_on `MEM r l` >> fs [] >>
        rw [lookup_insert]
    ) >>
    Cases_on `r = h` >> fs [] >> rveq
    THEN1 (
        Cases_on `P v x` >> fs []
    ) >>
    Cases_on `P v x` >> fs [] >>
    simp [lookup_insert]
)


val lookup_numset_list_add_if_lt = Q.store_thm("lookup_numset_list_add_if_lt",
    `!r l v s.
    lookup r (numset_list_add_if_lt l v s) =
        if MEM r l then
          case lookup r s of
          | (SOME vr) =>
            if v <= vr then SOME v
            else SOME vr
          | NONE =>
            SOME v
        else
          lookup r s
    `,
    simp [numset_list_add_if_lt_def] >>
    rw [lookup_numset_list_add_if]
)

val lookup_numset_list_add_if_gt = Q.store_thm("lookup_numset_list_add_if_gt",
    `!r l v s.
    lookup r (numset_list_add_if_gt l v s) =
        if MEM r l then
          case lookup r s of
          | (SOME vr) =>
            if vr <= v then SOME v
            else SOME vr
          | NONE =>
            SOME v
        else
          lookup r s
    `,
    simp [numset_list_add_if_gt_def] >>
    rw [lookup_numset_list_add_if]
)

val domain_numset_list_add_if = Q.store_thm("domain_numset_list_add_if",
    `!l v s P. domain (numset_list_add_if l v s P) = set l UNION domain s`,
    Induct_on `l` >>
    rw [numset_list_add_if_def] >>
    Cases_on `lookup h s`
    THEN1 (
        rw [EXTENSION] >>
        metis_tac []
    )
    THEN1 (
        `h IN domain s` by rw [domain_lookup] >>
        rw [EXTENSION] >>
        metis_tac []
    )
)

val domain_numset_list_add_if_lt = Q.store_thm("domain_numset_list_add_if_lt",
    `!l v s. domain (numset_list_add_if_lt l v s) = set l UNION domain s`,
    rw [numset_list_add_if_lt_def, domain_numset_list_add_if]
)

val domain_numset_list_add_if_gt = Q.store_thm("domain_numset_list_add_if_gt",
    `!l v s. domain (numset_list_add_if_gt l v s) = set l UNION domain s`,
    rw [numset_list_add_if_gt_def, domain_numset_list_add_if]
)

val lookup_numset_list_delete = Q.store_thm("lookup_numset_list_delete",
    `!l s x. lookup x (numset_list_delete l s) = if MEM x l then NONE else lookup x s`,
    Induct_on `l` >>
    rw [numset_list_delete_def, lookup_delete] >>
    fs []
)

val get_intervals_nout = Q.store_thm("get_intervals_nout",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    n_out = n_in - (size_of_live_tree lt)`,

    Induct_on `lt` >>
    rw [get_intervals_def, size_of_live_tree_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n_out = n2 - (size_of_live_tree lt)` by metis_tac [] >>
    `n2 = n_in - (size_of_live_tree lt')` by metis_tac [] >>
    intLib.COOPER_TAC
)

val get_intervals_withlive_nout = Q.store_thm("get_intervals_withlive_nout",
    `!lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live ==>
    n_out = n_in - (size_of_live_tree lt)`,

    Induct_on `lt` >>
    rw [get_intervals_withlive_def, size_of_live_tree_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n_out = n2 - (size_of_live_tree lt)` by metis_tac [] >>
    `n2 = n_in - (size_of_live_tree lt')` by metis_tac [] >>
    rveq >> intLib.COOPER_TAC
)


val get_intervals_intend_augment = Q.store_thm("get_intervals_intend_augment",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    !r v. lookup r end_in = SOME v ==> (?v'. lookup r end_out = SOME v' /\ v <= v')`,

    Induct_on `lt` >>
    rw [get_intervals_def]
    (* Writes *)
    THEN1 (
        rw [lookup_numset_list_add_if_gt]
    )
    (* Reads *)
    THEN1 (
        rw [lookup_numset_list_add_if_gt]
    ) >>
    (* Branch & Seq *)
    rpt (pairarg_tac >> fs []) >>
    `?v'. lookup r int_end2 = SOME v' /\ v <= v'` by metis_tac [] >>
    `?v''. lookup r end_out = SOME v'' /\ v' <= v''` by metis_tac [] >>
    rw [] >>
    intLib.COOPER_TAC
)

val check_number_property_intend = Q.store_thm("check_number_property_intend",
    `!end_out lt n_in live_in.
    check_number_property (\n (live : num_set). !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live_in ==>
    !r. r IN domain (get_live_backward lt live_in) ==> ?v. lookup r end_out = SOME v /\ n_in-(size_of_live_tree lt) <= v`,

    Induct_on `lt` >>
    rw [check_number_property_def, get_live_backward_def, size_of_live_tree_def]
    (* Writes *)
    THEN1 (
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Reads *)
    THEN1 (
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Branch *)
    THEN1 (
        fs [branch_domain, domain_numset_list_insert] >>
        res_tac >> rw [] >>
        `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
        intLib.COOPER_TAC
    )
    (* Seq *)
    THEN1 (
        res_tac >> rw [] >>
        intLib.COOPER_TAC
    )
)

val get_intervals_live_less_end = Q.store_thm("get_intervals_live_less_end",
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r. r IN domain live_in ==> ?v. lookup r end_in = SOME v /\ n_in <= v) ==>
    check_number_property (\n (live : num_set). !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live_in`,

    Induct_on `lt` >>
    simp [get_intervals_def, check_number_property_def] >>
    rpt gen_tac >> strip_tac >> rveq
    (* Writes *)
    THEN1 (
        rw [domain_numset_list_delete, lookup_numset_list_add_if_gt]
    )
    (* Reads *)
    THEN1 (
        rw [domain_numset_list_insert, lookup_numset_list_add_if_gt] >>
        every_case_tac >> rw [] >> intLib.COOPER_TAC
    ) >>
    (* Common Branch & Seq proof *)
    rpt (pairarg_tac >> fs []) >>
    `n2 = n_in - (size_of_live_tree lt') /\ n_out = n2 - (size_of_live_tree lt)` by metis_tac [get_intervals_nout] >>
    `check_number_property (\n live. !r. r IN domain live ==> ?v. lookup r int_end2 = SOME v /\ n+1 <= v) lt' n_in live_in` by metis_tac [] >>
    `check_number_property (\n live. !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt' n_in live_in` by (
        sg `!n' (live' : num_set). (\n live. !r. r IN domain live ==> ?v. lookup r int_end2 = SOME v /\ n+1 <= v) n' live' ==> (\n live. !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) n' live'` THEN1 (
            rw [] >>
            `?v. lookup r int_end2 = SOME v /\ n'+1 <= v` by rw [] >>
            `?v'. lookup r end_out = SOME v' /\ v <= v'` by metis_tac [get_intervals_intend_augment] >>
            rw [] >> intLib.COOPER_TAC
        ) >>
        qspecl_then [`\n live. !r. r IN domain live ==> ?v. lookup r int_end2 = SOME v /\ n+1 <= v`, `\n live. !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v`, `lt'`, `n_in`, `live_in`] assume_tac check_number_property_monotone_weak >>
        rw []
    ) >>
    `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
    simp []
    (* Branch *)
    THEN1 (
        sg `!r. r IN domain live_in ==> ?v. lookup r int_end2 = SOME v /\ n2 <= v` THEN1 (
            rw [] >>
            `?v. lookup r end_in = SOME v /\ n_in <= v` by rw [] >>
            `?v'. lookup r int_end2 = SOME v' /\ v <= v'` by metis_tac [get_intervals_intend_augment] >>
            rw [] >>
            intLib.COOPER_TAC
        ) >>
        metis_tac []
    )
    (* Seq *)
    THEN1 (
        `!r. r IN domain (get_live_backward lt' live_in) ==> ?v. lookup r int_end2 = SOME v /\ n_in - size_of_live_tree lt' <= v` by metis_tac [check_number_property_intend] >>
        metis_tac []
    )
)

val get_intervals_withlive_intbeg_reduce = Q.store_thm("get_intervals_withlive_intbeg_reduce",
    `!lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,

    Induct_on `lt` >>
    simp [get_intervals_withlive_def] >>
    rpt gen_tac >> strip_tac
    (* Writes *)
    THEN1 (
        rpt strip_tac >>
        fs [lookup_numset_list_add_if_lt] >>
        rw [] >>
        every_case_tac >>
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Reads *)
    THEN1 (
        rpt strip_tac >>
        fs [lookup_numset_list_delete] >>
        rw [] >>
        every_case_tac >>
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Branch *)
    THEN1 (
      rpt (pairarg_tac >> fs []) >>
      `(!r. option_CASE (lookup r int_beg2) n2 (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\ (!r v. lookup r int_beg2 = SOME v ==> n2 <= v)` by (res_tac >> metis_tac []) >>
      `!r v. lookup r (difference int_beg2 live) = SOME v ==> n2 <= v` by (rw [lookup_difference] >> res_tac) >>
      `(!r. option_CASE (lookup r int_beg1) n1 (\x.x) <= option_CASE (lookup r (difference int_beg2 live)) n2 (\x.x)) /\ (!r v. lookup r (difference int_beg2 live) = SOME v ==> n2 <= v) /\ (!r v. lookup r int_beg1 = SOME v ==> n1 <= v)` by (res_tac >> metis_tac []) >>
      fs [lookup_difference] >>
      `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_withlive_nout] >>
      `n1 = n2 - size_of_live_tree lt` by metis_tac [get_intervals_withlive_nout] >>
      `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
      rpt strip_tac
      THEN1 (
          rpt (first_x_assum (qspec_then `r` assume_tac)) >>
          rpt CASE_TAC >>
          Cases_on `lookup r int_beg1` >> Cases_on `lookup r int_beg2` >>
          Cases_on `lookup r live` >>
          rfs [] >> fs [] >> rw [] >>
          rpt (qpat_x_assum `lookup _ _ = _` kall_tac) >>
          intLib.COOPER_TAC
      )
      THEN1 res_tac
    )
    (* Seq*)
    THEN1 (
      rpt (pairarg_tac >> fs []) >>
      `(!r. option_CASE (lookup r int_beg2) n2 (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\ (!r v. lookup r beg_in = SOME v ==> n_in <= v) /\ (!r v. lookup r int_beg2 = SOME v ==> n2 <= v)` by (res_tac >> metis_tac []) >>
      `(!r. option_CASE (lookup r int_beg1) n1 (\x.x) <= option_CASE (lookup r int_beg2) n2 (\x.x)) /\ (!r v. lookup r int_beg2 = SOME v ==> n2 <= v) /\ (!r v. lookup r int_beg1 = SOME v ==> n1 <= v)` by (res_tac >> metis_tac []) >>
      simp [lookup_numset_list_delete] >>
      `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_withlive_nout] >>
      `n1 = n2 - size_of_live_tree lt` by metis_tac [get_intervals_withlive_nout] >>
      `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
      rpt strip_tac
      THEN1 (
          rpt CASE_TAC >>
          rpt (first_x_assum (qspec_then `r` assume_tac)) >>
          rfs [] >> rw [] >>
          intLib.COOPER_TAC
      )
      THEN1 res_tac
    )
)

val get_intervals_withlive_intbeg_nout = Q.store_thm("get_intervals_withlive_intbeg_nout",
    `!lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,
    metis_tac [get_intervals_withlive_intbeg_reduce]
)

val get_intervals_intbeg_nout = Q.store_thm("get_intervals_intbeg_nout",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,

    Induct_on `lt` >>
    rw [get_intervals_def]
    (* Writes *)
    THEN1 (
        fs [lookup_numset_list_add_if_lt] >>
        every_case_tac >>
        res_tac >>
        intLib.COOPER_TAC
    )
    (* Reads *)
    THEN1 (
        fs [lookup_numset_list_delete] >>
        res_tac >>
        intLib.COOPER_TAC
    ) >>
    (* Branch & Seq*)
    rpt (pairarg_tac >> fs []) >>
    `!r v. lookup r int_beg2 = SOME v ==> n2 <= v` by metis_tac [] >>
    `!r v. lookup r beg_out = SOME v ==> n_out <= v` by metis_tac [] >>
    res_tac
)


val get_intervals_withlive_live_intbeg = Q.store_thm("get_intervals_withlive_live_intbeg",
    `!lt n_in beg_in end_in live n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r. r IN domain live ==> r NOTIN domain beg_in) ==>
    (!r. r IN domain (get_live_backward lt live) ==> r NOTIN domain beg_out)`,

    Induct_on `lt` >>
    rw [get_intervals_withlive_def, get_live_backward_def]
    (* Writes *)
    THEN1 fs [domain_numset_list_delete, domain_numset_list_add_if_lt]
    (* Reads *)
    THEN1 fs [domain_numset_list_delete, domain_numset_list_insert]
    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        simp [domain_difference] >>
        fs [domain_numset_list_insert, branch_domain] >>
        `!s. lookup r s = SOME () <=> r IN domain s` by rw [domain_lookup] >>
        simp [] >>
        fs [domain_numset_list_insert, branch_domain, domain_union]
    )
    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `!r. r IN domain (get_live_backward lt' live) ==> r NOTIN domain int_beg2` by (res_tac >> metis_tac []) >>
        res_tac >>
        metis_tac []
    )
)

val get_intervals_withlive_beg_less_live = Q.store_thm("get_intervals_withlive_beg_less_live",
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) /\
    (!r. r IN domain live_in ==> r NOTIN domain beg_in) ==>
    check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) lt n_in live_in`,

    Induct_on `lt` >>
    simp [get_intervals_withlive_def, get_live_backward_def, check_number_property_strong_def] >>
    rpt (gen_tac ORELSE disch_tac)
    (* Writes *)
    THEN1 (
        fs [domain_numset_list_delete, lookup_numset_list_add_if_lt] >>
        `lookup r beg_in = NONE` by rw [lookup_NONE_domain] >>
        fs []
    )
    (* Reads *)
    THEN1 (
        fs [domain_numset_list_insert, lookup_numset_list_delete] >>
        `lookup r beg_in = NONE` by rw [lookup_NONE_domain] >>
        fs []
    )

    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r int_beg2) n2 (\x.x) <= n) lt' n_in live_in` by metis_tac [] >>
        `!r. r IN domain live_in ==> r NOTIN domain (difference int_beg2 live_in)` by (rw [domain_difference] >> fs [domain_lookup]) >>
        `!r v. lookup r (difference int_beg2 live_in) = SOME v ==> n2 <= v` by (rw [lookup_difference] >> metis_tac [get_intervals_withlive_intbeg_nout]) >>
        `!r v. lookup r int_beg1 = SOME v ==> n1 <= v` by metis_tac [get_intervals_withlive_intbeg_nout] >>
        `check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r int_beg1) n1 (\x.x) <= n) lt n2 live_in` by metis_tac [] >>
        `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_withlive_nout] >>
        `n1 = n2 - size_of_live_tree lt` by metis_tac [get_intervals_withlive_nout] >>
        `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
        fs [] >>
        `domain (union (get_live_backward lt live_in) (get_live_backward lt' live_in)) = domain (get_live_backward lt live_in) UNION domain (get_live_backward lt' live_in)` by rw [domain_union] >>
        qabbrev_tac `set_union = union (get_live_backward lt live_in) (get_live_backward lt' live_in)` >>
        rpt strip_tac
        THEN1 (
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') - size_of_live_tree lt <= n /\ (!r. r IN domain live ==> option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n) ==> (!r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
            rw [lookup_difference] >>
            rpt CASE_TAC >>
            first_x_assum (qspec_then `r` assume_tac) >>
            rfs [] >> intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `\n live. !r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `lt`, `n_in - size_of_live_tree lt'`, `live_in`] assume_tac check_number_property_strong_monotone >>
          metis_tac []
        )
        THEN1 (
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') <= n /\ (!r. r IN domain live ==> option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n) ==> (!r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
            rw [lookup_difference] >>
            rpt CASE_TAC
            THEN1 intLib.COOPER_TAC
            THEN1 (
              `!r. option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= option_CASE (lookup r (difference int_beg2 live_in)) (n_in - size_of_live_tree lt') (\x.x)` by metis_tac [get_intervals_withlive_intbeg_reduce] >>
              rpt (last_x_assum (qspec_then `r` assume_tac)) >>
              rfs [lookup_difference] >>
              Cases_on `lookup r live_in` >> fs []
              THEN1 intLib.COOPER_TAC >>
              Cases_on `lookup r int_beg2` >> fs [] >>
              intLib.COOPER_TAC
            )
            THEN1 intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n`, `\n live. !r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `lt'`, `n_in`, `live_in`] assume_tac check_number_property_strong_monotone >>
          metis_tac []
        )
        THEN1 (
          fs [domain_numset_list_insert, branch_domain, lookup_difference] >>
          (
            rw [size_of_live_tree_def]
            THEN1 (
              CASE_TAC
              THEN1 intLib.COOPER_TAC
              THEN1 (
                `r NOTIN domain set_union` by fs [lookup_NONE_domain] >>
                rfs []
              )
            )
            THEN1 intLib.COOPER_TAC
        )
      )
    )

    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r int_beg2) n2 (\x.x) <= n) lt' n_in live_in` by metis_tac [] >>
        `!r v. lookup r int_beg2 = SOME v ==> n2 <= v` by (rw [lookup_numset_list_delete] >> metis_tac [get_intervals_withlive_intbeg_nout]) >>
        `!r v. lookup r int_beg2 = SOME v ==> n2 <= v` by metis_tac [get_intervals_withlive_intbeg_nout] >>
        `!r. r IN domain (get_live_backward lt' live_in) ==> r NOTIN domain int_beg2` by metis_tac [get_intervals_withlive_live_intbeg] >>
        `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_withlive_nout] >>
        `n1 = n2 - size_of_live_tree lt` by metis_tac [get_intervals_withlive_nout] >>
        `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
        rpt strip_tac
        THEN1 metis_tac []
        THEN1 (
          fs [] >>
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') <= n /\ (!r. r IN domain live ==> option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n) ==> (!r. r IN domain live ==> option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
              rw [] >>
              `!r. option_CASE (lookup r beg_out) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x)` by metis_tac [get_intervals_withlive_intbeg_reduce] >>
              rpt (last_x_assum (qspec_then `r` assume_tac)) >> rfs [] >>
              Cases_on `lookup r beg_out` >> fs []
              THEN1 intLib.COOPER_TAC >>
              Cases_on `lookup r int_beg2` >> rfs [] >>
              intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n`, `\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `lt'`, `n_in`, `live_in`] assume_tac check_number_property_strong_monotone >>
          metis_tac []
        )
    )
)

val get_intervals_withlive_n_eq_get_intervals_n = Q.store_thm("get_intervals_withlive_n_eq_get_intervals_n",
    `!lt n beg end beg' end' n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end' live ==>
    n1 = n2`,
    Induct_on `lt` >>
    rw [get_intervals_def, get_intervals_withlive_def] >>
    rpt (pairarg_tac >> fs []) >>
    metis_tac []
)

val get_intervals_withlive_end_eq_get_intervals_end = Q.store_thm("get_intervals_withlive_end_eq_get_intervals_end",
    `!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end live ==>
    end1 = end2`,
    Induct_on `lt` >>
    rw [get_intervals_def, get_intervals_withlive_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n2' = n2''` by metis_tac [get_intervals_withlive_n_eq_get_intervals_n] >> rveq >>
    metis_tac []
)

val get_intervals_withlive_beg_eq_get_intervals_beg_when_some = Q.store_thm("get_intervals_withlive_beg_eq_get_intervals_beg_when_some",
    `!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end live /\
    (!r v. lookup r beg = SOME v ==> n <= v) /\
    (!r v. lookup r beg' = SOME v ==> n <= v) /\
    (!r v1 v2. lookup r beg = SOME v1 /\ lookup r beg' = SOME v2 ==> v1 = v2)
    ==>
    !r v1 v2. lookup r beg1 = SOME v1 /\ lookup r beg2 = SOME v2 ==> v1 = v2`,

    Induct_on `lt` >>
    REWRITE_TAC [get_intervals_def, get_intervals_withlive_def, LET_THM] >>
    rpt gen_tac >> strip_tac
    (* Writes *)
    THEN1 (
        rw [] >>
        fs [lookup_numset_list_add_if_lt] >>
        every_case_tac >>
        fs [] >>
        res_tac >>
        intLib.COOPER_TAC
    )
    (* Reads *)
    THEN1 (
        rw [] >>
        fs [lookup_numset_list_delete] >>
        res_tac
    ) >>
    (* Common Branch & Seq proof *)
    rpt (pairarg_tac >> fs []) >>
    `n2'' = n2'` by metis_tac [get_intervals_withlive_n_eq_get_intervals_n] >>
    `int_end2 = int_end2'` by metis_tac [get_intervals_withlive_end_eq_get_intervals_end] >>
    rveq >>
    `!r v. lookup r int_beg2' = SOME v ==> n2' <= v` by metis_tac [get_intervals_intbeg_nout] >>
    `!r v. lookup r int_beg2 = SOME v ==> n2' <= v` by metis_tac [get_intervals_withlive_intbeg_nout] >>
    `!r v1 v2. lookup r int_beg2' = SOME v1 /\ lookup r int_beg2 = SOME v2 ==> v1 = v2` by (
        first_x_assum (qspecl_then [`n`, `beg`, `beg'`, `end`, `n2'`, `int_beg2'`, `int_end2`, `n2'`, `int_beg2`, `int_end2`, `live`] assume_tac) >>
        res_tac >>
        metis_tac []
    )
    (* Branch *)
    THEN1 (
        `!r v1 v2. lookup r int_beg2' = SOME v1 /\ lookup r (difference int_beg2 live) = SOME v2 ==> v1 = v2` by (
            simp [lookup_difference] >> rpt strip_tac >>
            metis_tac []
        ) >>
        `!r v1 v2. lookup r beg1 = SOME v1 /\ lookup r int_beg1 = SOME v2 ==> v1 = v2` by (
            `!r v. lookup r (difference int_beg2 live) = SOME v ==> n2' <= v` by (rw [lookup_difference] >> res_tac) >>
            rveq >>
            last_x_assum (qspecl_then [`n2'`, `int_beg2'`, `difference int_beg2 live`, `int_end2`, `n1`, `beg1`, `end1`, `n1'`, `int_beg1`, `end2`, `live`] assume_tac) >>
            rpt strip_tac >>
            res_tac >>
            metis_tac []
        ) >>
        REWRITE_TAC [lookup_difference] >>
        rpt strip_tac >>
        Cases_on `lookup r (union (get_live_backward lt live) (get_live_backward lt' live))` >> fs [] >>
        res_tac
    )
    (* Seq *)
    THEN1 (
        last_x_assum (qspecl_then [`n2'`, `int_beg2'`, `int_beg2`, `int_end2`, `n1`, `beg1`, `end1`, `n1'`, `beg2`, `end2`, `get_live_backward lt' live`] assume_tac) >>
        res_tac >>
        metis_tac []
    )
)

val get_intervals_withlive_beg_subset_get_intervals_beg = Q.store_thm("get_intervals_withlive_beg_subset_get_intervals_beg",
    `!lt n beg_in1 beg_in2 end n1 beg_out1 end1 n2 beg_out2 end2 live.
    (n1, beg_out1, end1) = get_intervals_withlive lt n beg_in1 end live /\
    (n2, beg_out2, end2) = get_intervals lt n beg_in2 end /\
    domain beg_in1 SUBSET domain beg_in2 ==>
    domain beg_out1 SUBSET domain beg_out2`,

    Induct_on `lt` >>
    rw [get_intervals_withlive_def, get_intervals_def]
    (* Writes *)
    THEN1 (
        rw [domain_numset_list_add_if_lt] >>
        fs [SUBSET_DEF]
    )
    (* Reads *)
    THEN1 (
        rw [domain_numset_list_delete] >>
        fs [SUBSET_DEF]
    )
    (* Common Branch & Seq *)
    >>
    rpt (pairarg_tac >> fs []) >>
    `n2'' = n2'` by metis_tac [get_intervals_withlive_n_eq_get_intervals_n] >>
    rveq >>
    `int_end2' = int_end2` by metis_tac [get_intervals_withlive_end_eq_get_intervals_end] >>
    rveq >>
    `domain int_beg2' SUBSET domain int_beg2` by metis_tac []
    (* Branch *)
    THEN1 (
        `domain (difference int_beg2' live) SUBSET domain int_beg2` by (rw [domain_difference] >> fs [SUBSET_DEF]) >>
        `domain int_beg1 SUBSET domain beg_out2` by metis_tac [] >>
        rw [domain_difference] >>
        fs [SUBSET_DEF]
    )
    (* Seq *)
    THEN1 (
        metis_tac []
    )
)

val get_intervals_beg_subset_registers = Q.store_thm("get_intervals_beg_subset_registers",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    domain beg_out SUBSET (domain beg_in UNION (live_tree_registers lt))`,

    Induct_on `lt` >>
    rw [get_intervals_def, live_tree_registers_def]
    THEN1 rw [domain_numset_list_add_if_lt]
    >>
    rpt (pairarg_tac >> fs []) >>
    `domain int_beg2 SUBSET (domain beg_in UNION (live_tree_registers lt'))` by metis_tac [] >>
    `domain beg_out SUBSET (domain int_beg2 UNION (live_tree_registers lt))` by metis_tac [] >>
    fs [SUBSET_DEF] >>
    metis_tac []
)

val get_intervals_withlive_beg_monotone = Q.store_thm("get_intervals_withlive_beg_monotone",
    `!lt n beg end live n' beg' end' (s : int num_map) n1 beg1 end1 n2 beg2 end2.
    (n1, beg1, end1) = get_intervals_withlive lt n beg end live /\
    (n2, beg2, end2) = get_intervals_withlive lt n' beg' end' live /\
    domain beg' = domain beg UNION domain s ==>
    ?(s' : int num_map). domain beg2 = domain beg1 UNION domain s' /\ domain s' SUBSET domain s`,

    Induct_on `lt` >>
    rw [get_intervals_withlive_def]
    (* Writes *)
    THEN1 (
        rw [domain_numset_list_add_if_lt, domain_union] >>
        qexists_tac `s` >>
        rw [SUBSET_DEF, EXTENSION] >>
        eq_tac >> rw [] >> rw []
    )
    (* Reads *)
    THEN1 (
        rw [domain_numset_list_delete, domain_union] >>
        qexists_tac `numset_list_delete l s` >>
        rw [EXTENSION, SUBSET_DEF, domain_numset_list_delete] >>
        eq_tac >> rw [] >> rw []
    )
    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `?(s' : int num_map). domain int_beg2 = domain int_beg2' UNION domain s' /\ domain s' SUBSET domain s` by metis_tac [] >>
        sg `domain (difference int_beg2 live) = domain (difference int_beg2' live) UNION domain (difference s' live)` THEN1 (
            rw [domain_difference] >>
            rw [EXTENSION] >> eq_tac >> rw [] >> rw []
        ) >>
        `domain (difference s' live) SUBSET domain s'` by rw [domain_difference, SUBSET_DEF] >>
        qabbrev_tac `s'' = difference s' live` >>
        `?(s''' : int num_map). domain int_beg1 = domain int_beg1' UNION domain s''' /\ domain s''' SUBSET domain s''` by metis_tac [] >>
        qexists_tac `difference s''' (union (get_live_backward lt live) (get_live_backward lt' live))` >>
        rw [domain_difference]
        THEN1 (
          rw [EXTENSION] >>
          eq_tac >> rw [] >> rw []
        )
        THEN1 (
            fs [SUBSET_DEF]
        )
    )
    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `?(s' : int num_map). domain int_beg2 = domain int_beg2' UNION domain s' /\ domain s' SUBSET domain s` by metis_tac [] >>
        `?(s'' : int num_map). domain int_beg1 = domain int_beg1' UNION domain s'' /\ domain s'' SUBSET domain s'` by metis_tac [] >>
        qexists_tac `s''` >>
        rw [] >>
        fs [SUBSET_DEF]
    )
)

val get_intervals_withlive_registers_subset_beg = Q.store_thm("get_intervals_withlive_registers_subset_beg",
    `!lt n_in beg_in end_in n_out beg_out end_out live_in.
    domain end_in SUBSET domain beg_in UNION domain live_in /\
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in ==>
    domain end_out SUBSET domain beg_out UNION domain (get_live_backward lt live_in)`,

    Induct_on `lt` >>
    rw [get_intervals_withlive_def, get_live_backward_def, live_tree_registers_def]

    (* Writes *)
    THEN1 (
        rw [domain_numset_list_add_if_lt, domain_numset_list_delete, domain_numset_list_add_if_gt] >>
        fs [SUBSET_DEF] >>
        metis_tac []
    )

    (* Reads *)
    THEN1 (
        rw [domain_numset_list_insert, domain_numset_list_delete, domain_numset_list_add_if_gt] >>
        fs [SUBSET_DEF] >>
        metis_tac []
    )

    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain int_end2 SUBSET domain int_beg2 UNION domain (get_live_backward lt' live_in)` by metis_tac [] >>
        sg `?n1' int_beg1' int_end1'. (n1', int_beg1', int_end1') = get_intervals_withlive lt n2 (union (difference int_beg2 live_in) (difference int_end2 int_beg2)) int_end2 live_in` THEN1 (
            `?x. x = get_intervals_withlive lt n2 (union (difference int_beg2 live_in) (difference int_end2 int_beg2)) int_end2 live_in` by rw [] >>
            PairCases_on `x` >>
            metis_tac []
        ) >>
        `int_end1' = int_end1` by (`?x. x = get_intervals lt n2 LN int_end2` by rw [] >> PairCases_on `x` >> metis_tac [get_intervals_withlive_end_eq_get_intervals_end]) >>
        rveq >>
        sg `domain int_end2 SUBSET domain (union (difference int_beg2 live_in) (difference int_end2 int_beg2)) UNION domain live_in` THEN1 (
            rw [domain_union, domain_difference, SUBSET_DEF] >>
            metis_tac []
        ) >>
        `domain end_out SUBSET domain int_beg1' UNION domain (get_live_backward lt live_in)` by metis_tac [] >>
        sg `?(setunion : int num_map). domain int_beg1' = domain int_beg1 UNION domain setunion /\ domain setunion SUBSET domain (difference int_end2 int_beg2)` THEN1 (
            `domain (union (difference int_beg2 live_in) (difference int_end2 int_beg2)) = domain (difference int_beg2 live_in) UNION domain (difference int_end2 int_beg2)` by rw [domain_union] >>
            metis_tac [get_intervals_withlive_beg_monotone]
        ) >>
        fs [domain_numset_list_insert, branch_domain] >>
        fs [domain_union, domain_difference] >>
        fs [SUBSET_DEF] >>
        rw [] >>
        Cases_on `x IN domain (get_live_backward lt' live_in)` >> fs [] >>
        Cases_on `x IN domain (get_live_backward lt live_in)` >> fs [] >>
        rpt (first_x_assum (qspec_then `x` assume_tac)) >>
        `(x IN domain int_beg1 \/ x IN domain setunion) \/ x IN domain (get_live_backward lt live_in)` by rw [] >>
        `x IN domain int_end2 /\ x NOTIN domain int_beg2` by rw [] >>
        `x IN domain int_beg2 \/ x IN domain (get_live_backward lt' live_in)` by rw []
    )

    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain int_end2 SUBSET domain int_beg2 UNION domain (get_live_backward lt' live_in)` by metis_tac [] >>
        metis_tac []
    )
)

val get_intervals_withlive_live_tree_registers_subset_endout = Q.store_thm("get_intervals_withlive_live_tree_registers_subset_endout",
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in /\
    domain live_in SUBSET domain end_in ==>
    domain end_in UNION live_tree_registers lt UNION domain (get_live_backward lt live_in) SUBSET domain end_out`,

    Induct_on `lt` >>
    simp [get_intervals_withlive_def, live_tree_registers_def, get_live_backward_def] >>
    rpt (gen_tac ORELSE disch_tac)

    (* Writes *)
    THEN1 (
        fs [domain_numset_list_delete, domain_numset_list_add_if_gt, SUBSET_DEF]
    )

    (* Reads *)
    THEN1 (
        fs [domain_numset_list_insert, domain_numset_list_add_if_gt, SUBSET_DEF] >>
        rw [] >> rw []
    )

    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        simp [domain_numset_list_insert, branch_domain] >>
        `domain end_in UNION live_tree_registers lt' UNION domain (get_live_backward lt' live_in) SUBSET domain int_end2` by (fs [] >> metis_tac []) >>
        `domain live_in SUBSET domain int_end2` by fs [SUBSET_DEF] >>
        `domain int_end2 UNION live_tree_registers lt UNION domain (get_live_backward lt live_in) SUBSET domain int_end1` by (fs [] >> metis_tac []) >>
        fs [SUBSET_DEF]
    )

    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain end_in UNION live_tree_registers lt' UNION domain (get_live_backward lt' live_in) SUBSET domain int_end2` by (fs [] >> metis_tac []) >>
        `domain int_end2 UNION live_tree_registers lt UNION domain (get_live_backward lt (get_live_backward lt' live_in)) SUBSET domain int_end1` by (fs [] >> metis_tac []) >>
        fs [SUBSET_DEF]
    )
)

val get_intervals_domain_eq_live_tree_registers = Q.store_thm("get_intervals_domain_eq_live_tree_registers",
    `!lt n beg end.
    (n, beg, end) = get_intervals (fix_domination lt) 0 LN LN ==>
    domain beg = live_tree_registers (fix_domination lt) /\
    domain end = live_tree_registers (fix_domination lt)`,

    rpt (gen_tac ORELSE disch_tac) >>
    `domain (get_live_backward (fix_domination lt) LN) = EMPTY` by rw [fix_domination_fixes_domination] >>
    sg `?n' beg' end'. (n', beg', end') = get_intervals_withlive (fix_domination lt) 0 LN LN LN` THEN1 (
      `?x. x = get_intervals_withlive (fix_domination lt) 0 LN LN LN` by rw [] >>
      PairCases_on `x` >> metis_tac []
    ) >>
    qabbrev_tac `lt' = fix_domination lt` >>
    `end = end'` by metis_tac [get_intervals_withlive_end_eq_get_intervals_end] >>
    rveq >>
    `domain (LN : int num_map) SUBSET domain (LN : num_set)` by rw [domain_empty] >>
    `domain (LN : int num_map) SUBSET domain (LN : int num_map)` by rw [domain_empty] >>
    imp_res_tac get_intervals_withlive_live_tree_registers_subset_endout >>
    imp_res_tac get_intervals_withlive_registers_subset_beg >>
    imp_res_tac get_intervals_withlive_beg_subset_get_intervals_beg >>
    imp_res_tac get_intervals_beg_subset_registers >>
    rfs [] >>
    fs [SUBSET_DEF, EXTENSION] >>
    rw [] >> eq_tac >> rw []
)

val get_intervals_withlive_domain_eq_live_tree_registers = Q.store_thm("get_intervals_withlive_domain_eq_live_tree_registers",
    `!lt n beg end.
    (n, beg, end) = get_intervals_withlive (fix_domination lt) 0 LN LN LN ==>
    domain beg = live_tree_registers (fix_domination lt) /\
    domain end = live_tree_registers (fix_domination lt)`,

    rpt (gen_tac ORELSE disch_tac) >>
    `domain (get_live_backward (fix_domination lt) LN) = EMPTY` by rw [fix_domination_fixes_domination] >>
    sg `?n' beg' end'. (n', beg', end') = get_intervals (fix_domination lt) 0 LN LN` THEN1 (
      `?x. x = get_intervals (fix_domination lt) 0 LN LN` by rw [] >>
      PairCases_on `x` >> metis_tac []
    ) >>
    qabbrev_tac `lt' = fix_domination lt` >>
    `end = end'` by metis_tac [get_intervals_withlive_end_eq_get_intervals_end] >>
    rveq >>
    `domain (LN : int num_map) SUBSET domain (LN : num_set)` by rw [domain_empty] >>
    `domain (LN : int num_map) SUBSET domain (LN : int num_map)` by rw [domain_empty] >>
    imp_res_tac get_intervals_withlive_live_tree_registers_subset_endout >>
    imp_res_tac get_intervals_withlive_registers_subset_beg >>
    imp_res_tac get_intervals_withlive_beg_subset_get_intervals_beg >>
    imp_res_tac get_intervals_beg_subset_registers >>
    rfs [] >>
    fs [SUBSET_DEF, EXTENSION] >>
    rw [] >> eq_tac >> rw []
)

val get_intervals_withlive_beg_eq_get_intervals_beg = Q.store_thm("get_intervals_withlive_beg_eq_get_intervals_beg",
    `!lt n beg end n' beg' end'.
    (n, beg, end) = get_intervals_withlive (fix_domination lt) 0 LN LN LN /\
    (n', beg', end') = get_intervals (fix_domination lt) 0 LN LN ==>
    !(r:num). lookup r beg = lookup r beg'`,

    rw [] >>
    imp_res_tac get_intervals_withlive_domain_eq_live_tree_registers >>
    imp_res_tac get_intervals_domain_eq_live_tree_registers >>
    `domain beg = domain beg'` by rw [] >>
    `!r (v:int). lookup r LN = SOME v ==> 0 <= v` by rw [lookup_def, NOT_SOME_NONE] >>
    `!r (v1:int) (v2:int). lookup r LN = SOME v1 /\ lookup r LN = SOME v2 ==> v1 = v2` by rw [lookup_def, NOT_SOME_NONE] >>
    imp_res_tac get_intervals_withlive_beg_eq_get_intervals_beg_when_some >>
    Cases_on `lookup r beg` >>
    Cases_on `lookup r beg'`
    THEN1 simp []
    THEN1 metis_tac [domain_lookup]
    THEN1 metis_tac [domain_lookup]
    THEN1 metis_tac []
)

val get_intervals_end_increase = Q.store_thm("get_intervals_end_increase",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    domain end_in SUBSET domain end_out`,

    Induct_on `lt` >>
    rw [get_intervals_def]
    (* Writes *)
    THEN1 rw [domain_numset_list_add_if_gt]
    (* Reads *)
    THEN1 rw [domain_numset_list_add_if_gt]
    (* Branch & Seq *)
    >>
    rpt (pairarg_tac >> fs []) >>
    `domain end_in SUBSET domain int_end2` by metis_tac [] >>
    `domain int_end2 SUBSET domain end_out` by metis_tac [] >>
    fs [SUBSET_DEF]
)

val check_number_property_subset_endout = Q.store_thm("check_number_property_subset_endout",
    `!lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    domain live_in SUBSET domain end_in ==>
    check_number_property_strong (\n (live:num_set). domain live SUBSET domain end_out) lt n_in live_in`,

    Induct_on `lt` >>
    simp [get_intervals_def, check_number_property_strong_def] >>
    rpt (gen_tac ORELSE disch_tac)

    (* Writes *)
    THEN1 (
        fs [domain_numset_list_delete, domain_numset_list_add_if_gt, SUBSET_DEF]
    )

    (* Reads *)
    THEN1 (
        fs [domain_numset_list_insert, domain_numset_list_add_if_gt, SUBSET_DEF] >>
        rw [] >> rw []
    )

    (* Common Branch & Seq *)
    >> (
        rpt (pairarg_tac >> fs []) >>
        `check_number_property_strong (\n (live:num_set). domain live SUBSET domain int_end2) lt' n_in live_in` by metis_tac [] >>
        `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_nout] >>
        `domain end_in SUBSET domain int_end2` by metis_tac [get_intervals_end_increase] >>
        `domain int_end2 SUBSET domain end_out` by metis_tac [get_intervals_end_increase] >>
        `!n (live:num_set). domain live SUBSET domain int_end2 ==> domain live SUBSET domain end_out` by (rw [] >> fs [SUBSET_DEF]) >>
        qspecl_then [`\n (live:num_set). domain live SUBSET domain int_end2`, `\n (live:num_set). domain live SUBSET domain end_out`] assume_tac check_number_property_strong_monotone_weak
    )

    (* Branch *)
    THEN1 (
        `domain live_in SUBSET domain int_end2` by fs [SUBSET_DEF] >>
        `check_number_property_strong (\n (live:num_set). domain live SUBSET domain end_out) lt (n_in - size_of_live_tree lt') live_in` by metis_tac [] >>
        `check_number_property_strong (\n (live:num_set). domain live SUBSET domain end_out) lt' n_in live_in` by rw [] >>
        imp_res_tac check_number_property_strong_end >>
        fs [] >>
        rw [get_live_backward_def, domain_numset_list_insert, branch_domain]
    )

    (* Seq *)
    THEN1 (
        sg `?n2' int_beg2' int_end2'. (n2', int_beg2', int_end2') = get_intervals_withlive lt' n_in beg_in end_in live_in` THEN1 (
            `?x. x = get_intervals_withlive lt' n_in beg_in end_in live_in` by rw [] >>
            PairCases_on `x` >>
            metis_tac []
        ) >>
        `int_end2 = int_end2'` by metis_tac [get_intervals_withlive_end_eq_get_intervals_end] >>
        rveq >>
        imp_res_tac get_intervals_withlive_live_tree_registers_subset_endout >> fs [] >>
        metis_tac []
    )
)

val get_intervals_beg_less_live = Q.store_thm("get_intervals_beg_less_live",
    `!lt live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals (fix_domination lt) 0 LN LN ==>
    check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) (fix_domination lt) 0 LN`,

    rw [] >>
    sg `?n_out' beg_out' end_out'. (n_out', beg_out', end_out') = get_intervals_withlive (fix_domination lt) 0 LN LN LN` THEN1 (
        `?x. x = get_intervals_withlive (fix_domination lt) 0 LN LN LN` by rw [] >>
        PairCases_on `x` >>
        metis_tac []
    ) >>
    `!r v. lookup r (LN : int num_map) = SOME v ==> 0 <= v` by rw [lookup_def] >>
    `!r. r IN domain (LN : num_set) ==> r NOTIN domain (LN : int num_map)` by rw [domain_def] >>
    imp_res_tac get_intervals_withlive_beg_less_live >>
    imp_res_tac get_intervals_withlive_beg_eq_get_intervals_beg >>
    `n_out = n_out'` by metis_tac [get_intervals_withlive_n_eq_get_intervals_n] >>
    rveq >>
    `(\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) = (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out') n_out (\x.x) <= n)` by rw [EXTENSION] >>
    qabbrev_tac `P = \n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n` >>
    qabbrev_tac `Q = \n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out') n_out (\x.x) <= n` >>
    rw []
)

val get_intervals_intbeg_reduce = Q.store_thm("get_intervals_intbeg_reduce",
    `!lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,

    Induct_on `lt` >>
    simp [get_intervals_def] >>
    rpt gen_tac >> strip_tac
    (* Writes *)
    THEN1 (
        rpt strip_tac >>
        fs [lookup_numset_list_add_if_lt] >>
        rw [] >>
        every_case_tac >>
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Reads *)
    THEN1 (
        rpt strip_tac >>
        fs [lookup_numset_list_delete] >>
        rw [] >>
        every_case_tac >>
        res_tac >>
        rw [] >>
        intLib.COOPER_TAC
    )
    (* Branch & Seq *)
    >> (
      rpt (pairarg_tac >> fs []) >>
      `(!r. option_CASE (lookup r int_beg2) n2 (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\ (!r v. lookup r int_beg2 = SOME v ==> n2 <= v)` by (res_tac >> metis_tac []) >>
      `(!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r int_beg2) n2 (\x.x)) /\ (!r v. lookup r beg_out = SOME v ==> n_out <= v)` by (res_tac >> metis_tac []) >>
      rw []
      THEN1 (
        rpt (first_x_assum (qspec_then `r` assume_tac)) >>
        intLib.COOPER_TAC
      )
      THEN1 (
        rpt (first_x_assum (qspec_then `r` assume_tac)) >>
        rpt (first_x_assum (qspec_then `v` assume_tac)) >>
        fs []
      )
    )
)

val check_startlive_prop_monotone = Q.store_thm("check_startlive_prop_monotone",
    `!lt beg ndef end beg' ndef' end' n_in.
    (!r. option_CASE (lookup r beg') ndef' (\x.x) <= option_CASE (lookup r beg) ndef (\x.x)) /\
    (!r v. lookup r end = SOME v ==> (?v'. lookup r end' = SOME v' /\ v <= v')) /\
    check_startlive_prop lt n_in beg end ndef ==>
    check_startlive_prop lt n_in beg' end' ndef'`,

    Induct_on `lt` >>
    rw [check_startlive_prop_def] >>
    (
      CASE_TAC ORELSE res_tac >>
      rpt (first_x_assum (qspec_then `r` assume_tac)) >>
      rfs [] >>
      intLib.COOPER_TAC
    )
)

val check_startlive_prop_augment_ndef = Q.store_thm("check_startlive_prop_augment_ndef",
    `!lt n_in beg_out end_out ndef.
    check_startlive_prop lt n_in beg_out end_out ndef /\
    ndef  <= ndef' /\
    ndef' <= n_in - size_of_live_tree lt==>
    check_startlive_prop lt n_in beg_out end_out ndef'`,

    Induct_on `lt` >>
    simp [check_startlive_prop_def, size_of_live_tree_def] >>
    rpt gen_tac >> strip_tac
    (* Writes *)
    THEN1 (
        rw [] >>
        res_tac >>
        CASE_TAC >> fs [] >>
        intLib.COOPER_TAC
    )
    (* Branch & Seq *)
    >> (
        `0 <= size_of_live_tree lt /\ 0 <= size_of_live_tree lt'` by rw [size_of_live_tree_positive] >>
        `ndef' <= (n_in - size_of_live_tree lt') - size_of_live_tree lt` by intLib.COOPER_TAC >>
        `ndef' <= n_in - size_of_live_tree lt'` by intLib.COOPER_TAC >>
        metis_tac []
    )
)

val get_intervals_check_startlive_prop = Q.store_thm("get_intervals_check_startlive_prop",
    `!lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    check_startlive_prop lt n_in beg_out end_out n_out`,

    Induct_on `lt` >>
    simp [get_intervals_def, check_startlive_prop_def] >>
    rpt (gen_tac ORELSE disch_tac)
    (* Writes *)
    THEN1 (
        rw [lookup_numset_list_add_if_lt, lookup_numset_list_add_if_gt] >>
        every_case_tac >>
        intLib.COOPER_TAC
    )
    (* Branch & Seq *)
    >> (
        rpt (pairarg_tac >> fs []) >>
        `check_startlive_prop lt' n_in int_beg2 int_end2 n2` by metis_tac [] >>
        `!r v. lookup r int_beg2 = SOME v ==> n2 <= v` by metis_tac [get_intervals_intbeg_reduce] >>
        `check_startlive_prop lt n2  beg_out end_out n_out` by metis_tac [] >>
        `!r v. lookup r int_end2 = SOME v ==> ?v'. lookup r end_out = SOME v' /\ v <= v'` by metis_tac [get_intervals_intend_augment] >>
        `!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r int_beg2) n2 (\x.x)` by metis_tac [get_intervals_intbeg_reduce] >>
        `n2 = n_in - size_of_live_tree lt'` by metis_tac [get_intervals_nout] >>
        rveq >>
        rw [] >>
        metis_tac [check_startlive_prop_monotone]
    )
)

val exists_point_inside_interval_interval_intersect = Q.store_thm("exists_point_inside_interval_interval_intersect",
    `!l1 r1 l2 r2 v.
    point_inside_interval (l1, r1) v  /\ point_inside_interval (l2, r2) v ==>
    interval_intersect (l1, r1) (l2, r2)`,
    rw [point_inside_interval_def, interval_intersect_def] >>
    intLib.COOPER_TAC
)

val check_intervals_check_live_tree_lemma = Q.store_thm("check_intervals_check_live_tree_lemma",
    `!lt n_in beg_out end_out f live flive.
    check_startlive_prop lt n_in beg_out end_out (n_in - size_of_live_tree lt) /\
    check_number_property_strong (\n (live' : num_set). !r. r IN domain live' ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) lt n_in live  /\
    check_number_property (\n (live' : num_set). !r. r IN domain live' ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live /\
    check_number_property_strong (\n (live' : num_set). domain live' SUBSET domain end_out) lt n_in live /\
    domain beg_out = domain end_out /\
    live_tree_registers lt SUBSET domain end_out /\
    check_intervals f beg_out end_out /\
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV ==>
    ?liveout fliveout. check_live_tree f lt live flive = SOME (liveout, fliveout)`,

    Induct_on `lt` >>
    rw [check_number_property_def, check_number_property_strong_def, check_live_tree_def, check_startlive_prop_def, live_tree_registers_def]

    (* Writes *)
    THEN1 (
        fs [check_intervals_def] >>
        sg `!r. MEM r l ==> point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) n_in` THEN1 (
            rw [] >>
            `option_CASE (lookup r beg_out) (n_in - size_of_live_tree (Writes l)) (\x.x) <= n_in /\ ?ve. lookup r end_out = SOME ve /\ n_in <= ve` by rw [] >>
            `r IN domain beg_out` by fs [SUBSET_DEF] >>
            `?vb. lookup r beg_out = SOME vb` by rfs [domain_lookup] >>
            fs [] >>
            rw [point_inside_interval_def]
        ) >>
        sg `!r. r IN domain (numset_list_delete l live) ==> point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) n_in` THEN1 (
            rw [] >>
            res_tac >>
            `r IN domain beg_out` by fs [SUBSET_DEF] >>
            `?vb. lookup r beg_out = SOME vb` by rfs [domain_lookup] >>
            fs [] >>
            rw [point_inside_interval_def] >>
            intLib.COOPER_TAC
        ) >>
        sg `!r. r IN set l UNION domain live ==> point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) n_in` THEN1 (
            rpt (gen_tac ORELSE disch_tac) >>
            `MEM r l \/ r IN domain (numset_list_delete l live)` by fs [domain_numset_list_delete] >>
            rw []
        ) >>
        sg `set l UNION domain live SUBSET domain beg_out` THEN1 (
            REWRITE_TAC [SUBSET_DEF] >>
            rpt strip_tac >>
            `x IN set l \/ x IN domain (numset_list_delete l live)` by fs [domain_numset_list_delete] >>
            fs [SUBSET_DEF]
        ) >>
        sg `INJ f (set l UNION domain live) UNIV` THEN1 (
            REWRITE_TAC [INJ_DEF] >>
            strip_tac
            THEN1 rw [] >>
            rpt strip_tac >>
            res_tac >>
            `x IN domain beg_out /\ y IN domain beg_out` by fs [SUBSET_DEF] >>
            imp_res_tac exists_point_inside_interval_interval_intersect >>
            rw []
        ) >>
        imp_res_tac check_partial_col_success >>
        rw []
    )

    (* Reads *)
    THEN1 (
        fs [check_intervals_def, domain_numset_list_insert] >>
        sg `!r. MEM r l \/ r IN domain live ==> point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) n_in` THEN1 (
            rpt (gen_tac ORELSE disch_tac) >>
            `option_CASE (lookup r beg_out) n_out (\x.x) <= n_in - 1` by fs [] >>
            `?ve. lookup r end_out = SOME ve /\ n_in <= ve` by fs [] >>
            `r IN domain beg_out` by fs [SUBSET_DEF] >>
            `?vb. lookup r beg_out = SOME vb` by rfs [domain_lookup] >>
            fs [] >>
            rw [point_inside_interval_def] >>
            intLib.COOPER_TAC
        ) >>
        sg `INJ f (set l UNION domain live) UNIV` THEN1 (
            REWRITE_TAC [INJ_DEF] >>
            strip_tac
            THEN1 rw [] >>
            rpt strip_tac >>
            `point_inside_interval (THE (lookup x beg_out), THE (lookup x end_out)) n_in` by fs [] >>
            `point_inside_interval (THE (lookup y beg_out), THE (lookup y end_out)) n_in` by fs [] >>
            `x IN domain beg_out /\ y IN domain end_out` by fs [SUBSET_DEF] >>
            imp_res_tac exists_point_inside_interval_interval_intersect >>
            rw []
        ) >>
        imp_res_tac check_partial_col_success >>
        rw []
    )

    (* Branch *)
    THEN1 (
        sg `?live2 flive2. check_live_tree f lt' live flive = SOME (live2, flive2)` THEN1 (
            `n_in - size_of_live_tree lt' <= n_in - size_of_live_tree lt'` by intLib.COOPER_TAC >>
            `0 <= size_of_live_tree lt` by rw [size_of_live_tree_positive] >>
            `n_in - size_of_live_tree (Branch lt lt') <= n_in - size_of_live_tree lt'` by (rw [size_of_live_tree_def] >> intLib.COOPER_TAC) >>
            `check_startlive_prop lt' n_in beg_out end_out (n_in - size_of_live_tree lt')` by metis_tac [check_startlive_prop_augment_ndef] >>
            metis_tac []
        ) >>
        sg `?live1 flive1. check_live_tree f lt live flive = SOME (live1, flive1)` THEN1 (
            `n_in - size_of_live_tree (Branch lt lt') = n_in - size_of_live_tree lt' - size_of_live_tree lt` by (rw [size_of_live_tree_def] >> intLib.COOPER_TAC) >>
            metis_tac []
        ) >>
        rw [] >>
        `live2 = get_live_backward lt' live` by metis_tac [check_live_tree_eq_get_live_backward] >>
        `live1 = get_live_backward lt live` by metis_tac [check_live_tree_eq_get_live_backward] >>
        `domain flive1 = IMAGE f (domain live1)` by metis_tac [check_live_tree_success] >>
        rveq >>
        fs [get_live_backward_def, domain_numset_list_insert, branch_domain, size_of_live_tree_def] >>
        sg `!r. r IN domain (get_live_backward lt live) \/ r IN domain (get_live_backward lt' live) ==> point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) (n_in - (size_of_live_tree lt + size_of_live_tree lt'))` THEN1 (
            imp_res_tac check_number_property_intend >>
            rw [] >>
            res_tac >>
            `n_in - size_of_live_tree lt' - size_of_live_tree lt = n_in - (size_of_live_tree lt + size_of_live_tree lt')` by intLib.COOPER_TAC >>
            `r IN domain beg_out` by fs [SUBSET_DEF] >>
            `?vb. lookup r beg_out = SOME vb` by fs [domain_lookup] >>
            fs [point_inside_interval_def] >>
            `0 <= size_of_live_tree lt` by rw [size_of_live_tree_positive] >>
            intLib.COOPER_TAC
        ) >>
        sg `INJ f (domain (get_live_backward lt live) UNION domain (get_live_backward lt' live)) UNIV` THEN1 (
            REWRITE_TAC [INJ_DEF] >>
            strip_tac
            THEN1 rw [] >>
            rpt strip_tac >>
            `point_inside_interval (THE (lookup x beg_out), THE (lookup x end_out)) (n_in - (size_of_live_tree lt + size_of_live_tree lt'))` by fs [] >>
            `point_inside_interval (THE (lookup y beg_out), THE (lookup y end_out)) (n_in - (size_of_live_tree lt + size_of_live_tree lt'))` by fs [] >>
            `x IN domain beg_out /\ y IN domain beg_out` by fs [SUBSET_DEF] >>
            imp_res_tac exists_point_inside_interval_interval_intersect >>
            fs [check_intervals_def]
        ) >>
        `INJ f (set (MAP FST (toAList (difference (get_live_backward lt' live) (get_live_backward lt live)))) UNION (domain (get_live_backward lt live))) UNIV` by rw [branch_domain] >>
        metis_tac [check_partial_col_success]
    )

    (* Seq *)
    THEN1 (
        sg `?live2 flive2. check_live_tree f lt' live flive = SOME (live2, flive2)` THEN1 (
            `n_in - size_of_live_tree lt' <= n_in - size_of_live_tree lt'` by intLib.COOPER_TAC >>
            `0 <= size_of_live_tree lt` by rw [size_of_live_tree_positive] >>
            `n_in - size_of_live_tree (Seq lt lt') <= n_in - size_of_live_tree lt'` by (rw [size_of_live_tree_def] >> intLib.COOPER_TAC) >>
            `check_startlive_prop lt' n_in beg_out end_out (n_in - size_of_live_tree lt')` by metis_tac [check_startlive_prop_augment_ndef] >>
            metis_tac []
        ) >>
        sg `?live1 flive1. check_live_tree f lt live2 flive2 = SOME (live1, flive1)` THEN1 (
            `live2 = get_live_backward lt' live` by metis_tac [check_live_tree_eq_get_live_backward] >>
            `domain flive2 = IMAGE f (domain live2) /\ INJ f (domain live2) UNIV` by metis_tac [check_live_tree_success] >>
            `n_in - size_of_live_tree (Seq lt lt') = n_in - size_of_live_tree lt' - size_of_live_tree lt` by (rw [size_of_live_tree_def] >> intLib.COOPER_TAC) >>
            metis_tac []
        ) >>
        rw []
    )
)

val check_intervals_check_live_tree = Q.store_thm("check_intervals_check_live_tree",
    `!lt n_out beg_out end_out f.
    (n_out, beg_out, end_out) = get_intervals (fix_domination lt) 0 LN LN /\
    check_intervals f beg_out end_out ==>
    ?liveout fliveout. check_live_tree f (fix_domination lt) LN LN = SOME (liveout, fliveout)`,

    rw [] >>
    imp_res_tac get_intervals_check_startlive_prop >>
    imp_res_tac get_intervals_beg_less_live >>
    imp_res_tac get_intervals_live_less_end >>
    imp_res_tac check_number_property_subset_endout >>
    rpt (first_x_assum (qspec_then `LN` assume_tac)) >>
    fs [lookup_def] >>
    imp_res_tac get_intervals_domain_eq_live_tree_registers >>
    `domain beg_out = domain end_out` by simp [] >>
    `live_tree_registers (fix_domination lt) SUBSET domain end_out` by simp [SUBSET_DEF] >>
    `domain (LN : num_set) = IMAGE f (domain (LN : num_set))` by rw [] >>
    `INJ f (domain (LN : num_set)) UNIV` by rw [] >>
    imp_res_tac get_intervals_nout >>
    metis_tac [check_intervals_check_live_tree_lemma]
)

val colors_sub_eqn = Q.store_thm("colors_sub_eqn[simp]",`
  colors_sub n s =
  if n < LENGTH s.colors then
    (Success (EL n s.colors),s)
  else
    (Failure (Subscript),s)`,
  rw[colors_sub_def]>>
  fs[Marray_sub_def]);

val update_colors_eqn = Q.store_thm("update_colors_eqn[simp]",`
  update_colors n t s =
  if n < LENGTH s.colors then
     (Success (),s with colors := LUPDATE t n s.colors)
  else
     (Failure (Subscript),s)`,
  rw[update_colors_def]>>
  fs[Marray_update_def]);

val msimps = [st_ex_bind_def,st_ex_return_def];

val lookup_default_id_def = Define`
    lookup_default_id s x = option_CASE (lookup x s) x (\x.x)
`

val find_reg_exchange_step_def = Define`
    find_reg_exchange_step colors r (exch, invexch) =
        let col1 = EL r colors in
        let fcol1 = r DIV 2 in
        let col2 = lookup_default_id invexch fcol1 in
        let fcol2 = lookup_default_id exch col1 in
        (insert col1 fcol1 (insert col2 fcol2 exch), insert fcol1 col1 (insert fcol2 col2 invexch))
`

val find_reg_exchange_FOLDL = Q.store_thm("find_reg_exchange_FOLDL",
    `!l colors exch invexch sth.
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    find_reg_exchange l exch invexch sth = (Success (FOLDL (\a b. find_reg_exchange_step sth.colors b a) (exch, invexch) l), sth)`,
    Induct_on `l` >>
    rw [FOLDL, find_reg_exchange_def, find_reg_exchange_step_def, lookup_default_id_def] >>
    rw msimps
)

val lookup_default_id_insert = Q.store_thm("lookup_default_id_insert",
    `!s k1 k2 v.
    lookup_default_id (insert k2 v s) k1 = if k1 = k2 then v else lookup_default_id s k1`,
    rw [lookup_default_id_def, lookup_insert]
)

val id_def = Define `id x = x`

val find_reg_exchange_FOLDR_correct = Q.store_thm("find_reg_exchange_FOLDR_correct",
    `!l colors exch invexch k.
    ALL_DISTINCT (MAP (\r. EL r colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (exch, invexch) = FOLDR (\a b. find_reg_exchange_step colors a b) (LN, LN) l ==>
    ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.x) /\ (lookup_default_id invexch) o (lookup_default_id exch) = (\x.x)) /\
    (!r. MEM r l ==> lookup_default_id exch (EL r colors) = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r colors <=> k <= r DIV 2)) ==>
        (!c. id (k <= c <=> k <= lookup_default_id exch c)))`,

    Induct_on `l` >>
    simp [FOLDR, FUN_EQ_THM] >>
    rpt gen_tac

    THEN1 (
        strip_tac >>
        fs [lookup_def, lookup_default_id_def] >>
        fs [id_def]
    ) >>

    strip_tac >>
    `?x. FOLDR (\a b. find_reg_exchange_step colors a b) (LN : num num_map, LN : num num_map) l = x` by rw [] >>
    PairCases_on `x` >>
    rename1 `FOLDR _ _ _ = (exch1, invexch1)` >>
    `(exch, invexch) = find_reg_exchange_step colors h (exch1, invexch1)` by metis_tac [] >>
    qpat_x_assum `(exch, invexch) = _ _ _ (FOLDR _ _ _)` kall_tac >>

    last_x_assum drule >> strip_tac >>
    first_x_assum (qspecl_then [`exch1`, `invexch1`, `k`] assume_tac) >> rfs [] >>

    fs [find_reg_exchange_step_def] >>
    `?col1. EL h colors = col1` by rw [] >>
    `?fcol1. h DIV 2 = fcol1` by rw [] >>
    `?col2. lookup_default_id invexch1 fcol1 = col2` by rw [] >>
    `?fcol2. lookup_default_id exch1 col1 = fcol2` by rw [] >>
    strip_tac

    THEN1 (
        rw [lookup_default_id_insert] >>
        every_case_tac >>
        fs [FUN_EQ_THM] >>
        metis_tac []
    ) >>
    strip_tac
    THEN1 (
        rw [lookup_default_id_insert]
        THEN1 (
          fs [MEM_MAP] >>
          metis_tac []
        )
        THEN1 (
          `lookup_default_id exch1 (EL r colors) = h DIV 2` by (fs [FUN_EQ_THM] >> metis_tac []) >>
          `r DIV 2 = h DIV 2` by (res_tac >> rw []) >>
          `is_phy_var h` by rw [] >>
          `is_phy_var r` by rw [] >>
          fs [is_phy_var_def] >>
          `r = h` by intLib.COOPER_TAC >>
          rw []
        )
        THEN1 (
          rw [lookup_default_id_insert]
        )
    )
    THEN1 (
        rpt strip_tac >>
        `!r. MEM r l ==> (k <= EL r colors <=> k <= r DIV 2)` by rw [] >>
        fs [] >>
        rw [lookup_default_id_insert]
        THEN1 rw [id_def] >>
        simp [id_def] >>
        sg `!c. id (k <= lookup_default_id invexch1 c) <=> k <= c` THEN1 (
            rw [id_def] >>
            qpat_x_assum `!c. id _` (qspec_then `lookup_default_id invexch1 c` assume_tac) >>
            rfs [FUN_EQ_THM] >>
            fs [id_def]
        ) >>
        eq_tac
        THEN1 (
            rw [] >>
            `k <= h DIV 2` by metis_tac [id_def] >>
            `k <= EL h colors` by metis_tac [] >>
            rpt (last_x_assum (qspec_then `EL h colors` assume_tac)) >>
            fs [id_def]
        )
        THEN1 (
            rw [] >>
            `k <= EL h colors` by (rpt (first_x_assum (qspec_then `EL h colors` assume_tac)) >> fs [id_def]) >>
            `k <= h DIV 2` by metis_tac [] >>
            rpt (last_x_assum (qspec_then `h DIV 2` assume_tac)) >>
            fs [id_def]
        )
    )
)

val find_reg_exchange_correct = Q.store_thm("find_reg_exchange_correct",
    `!l sth k.
    ALL_DISTINCT (MAP (\r. EL r sth.colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    ?exch invexch. find_reg_exchange l LN LN sth = (Success (exch, invexch), sth) /\
    ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.x) /\ (lookup_default_id invexch) o (lookup_default_id exch) = (\x.x)) /\
    (!r. MEM r l ==> lookup_default_id exch (EL r sth.colors) = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors <=> k <= r DIV 2)) ==>
        (!c. id (k <= c <=> k <= lookup_default_id exch c)))`,

    simp [find_reg_exchange_FOLDL, GSYM FOLDR_REVERSE] >>
    rpt gen_tac >> strip_tac >>
    `?x. x = FOLDR (\b a. find_reg_exchange_step sth.colors b a) (LN, LN) (REVERSE l)` by rw [] >>
    PairCases_on `x` >>
    qexists_tac `x0` >>
    qexists_tac `x1` >>

    `REVERSE (REVERSE l) = l` by rw [REVERSE_REVERSE] >>
    qabbrev_tac `l' = REVERSE l` >>
    rveq >>
    fs [MEM_REVERSE, MAP_REVERSE] >>
    metis_tac [find_reg_exchange_FOLDR_correct]
)

val MAP_colors_eq_lemma = Q.store_thm("MAP_colors_eq_lemma",
    `!sth n f.
    n <= LENGTH sth.colors ==>
    ?sthout. (Success (), sthout) = MAP_colors f n sth /\
    LENGTH sth.colors = LENGTH sthout.colors /\
    (!n'. n' < n ==> EL n' sthout.colors = f (EL n' sth.colors)) /\
    (!n'. n <= n' ==> EL n' sthout.colors = EL n' sth.colors)`,

    Induct_on `n` >>
    rw [MAP_colors_def] >> rw msimps >>
    `?sth'. sth' = <| colors := LUPDATE (f (EL n sth.colors)) n sth.colors |>` by rw [] >>
    `n <= LENGTH sth'.colors` by rw [] >>
    `LENGTH sth'.colors = LENGTH sth.colors` by rw [] >>
    res_tac >>
    first_x_assum (qspec_then `f` assume_tac) >> fs [] >>
    qexists_tac `sthout` >>
    rw []
    THEN1 (
        `n' <= n` by rw [] >>
        Cases_on `n' = n`
        THEN1 (
            `n <= n'` by rw [] >>
            res_tac >>
            rw [EL_LUPDATE]
        )
        THEN1 (
            `n' < n` by rw [] >>
            res_tac >>
            rw [EL_LUPDATE]
        )
    )
    THEN1 (
        `n <= n'` by rw [] >>
        res_tac >>
        rw [EL_LUPDATE]
    )
)

val MAP_colors_eq = Q.store_thm("MAP_colors_eq",
    `!sth f.
    ?sthout. (Success (), sthout) = MAP_colors f (LENGTH sth.colors) sth /\
    (!n. n < LENGTH sth.colors ==> EL n sthout.colors = f (EL n sth.colors)) /\
    LENGTH sth.colors = LENGTH sthout.colors`,
    rw [] >>
    `LENGTH sth.colors <= LENGTH sth.colors` by rw [] >>
    metis_tac [MAP_colors_eq_lemma]
)

val apply_reg_exchange_correct = Q.store_thm("apply_reg_exchange_correct",
    `!l sth k.
    ALL_DISTINCT (MAP (\r. EL r sth.colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    ?sthout. (Success (), sthout) = apply_reg_exchange l sth /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    (!r1 r2. r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors ==> EL r1 sthout.colors = EL r2 sthout.colors ==> EL r1 sth.colors = EL r2 sth.colors) /\
    (!r. MEM r l ==> EL r sthout.colors = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors <=> k <= r DIV 2)) ==>
    (!r. r < LENGTH sth.colors ==> id (k <= EL r sth.colors <=> k <= EL r sthout.colors)))`,

    rpt gen_tac >> strip_tac >>
    fs [apply_reg_exchange_def] >>
    fs msimps >>
    drule find_reg_exchange_correct >>
    strip_tac >> rfs [] >>
    first_x_assum (qspec_then `k` assume_tac) >> rfs [] >>
    simp [colors_length_def, Marray_length_def] >>
    simp [GSYM lookup_default_id_def] >>
    qspecl_then [`sth`, `\c. lookup_default_id exch c`] assume_tac MAP_colors_eq >> fs [] >>
    qexists_tac `sthout` >>
    rw [] >>
    fs [FUN_EQ_THM] >>
    metis_tac []
)

val less_FST_def = Define`
    less_FST (x:int#num) y = (FST x <= FST y)
`

val transitive_less_FST = Q.store_thm("transitive_less_FST",
    `transitive less_FST`,
    rw [transitive_def, less_FST_def] >>
    intLib.COOPER_TAC
)

val good_linear_scan_state_def = Define`
    good_linear_scan_state int_beg int_end st sth l (pos:int) forced = (
        ALL_DISTINCT (st.colorpool ++ MAP (\(e,r). EL r sth.colors) st.active) /\
        EVERY (\r. r < LENGTH sth.colors) l /\
        EVERY (\r. EL r sth.colors < st.stacknum) l /\
        domain st.phyregs = { EL r sth.colors | r | MEM r l /\ is_phy_var r /\ EL r sth.colors < st.colormax } /\
        ALL_DISTINCT (MAP (\r. EL r sth.colors) (FILTER is_phy_var l)) /\
        EVERY (\c. c < st.colornum) st.colorpool /\
        EVERY (\e,r. EL r sth.colors < st.colornum) st.active /\
        st.colornum <= st.colormax /\
        st.colormax <= st.stacknum /\
        EVERY (\r. EL r sth.colors < st.colormax ==> EL r sth.colors < st.colornum) l /\
        EVERY (\r. the 0 (lookup r int_beg) <= pos) l /\
        EVERY (\r. ((pos <= the 0 (lookup r int_end) /\ EL r sth.colors < st.colormax) ==> (MEM (the 0 (lookup r int_end), r) st.active))) l /\
        EVERY (\r. ((MEM (the 0 (lookup r int_end), r) st.active) ==> (pos <= 1 + the 0 (lookup r int_end)))) l /\
        (!r1 r2. MEM r1 l /\ MEM r2 l /\ interval_intersect (the 0 (lookup r1 int_beg), the 0 (lookup r1 int_end)) (the 0 (lookup r2 int_beg), the 0 (lookup r2 int_end)) /\ EL r1 sth.colors = EL r2 sth.colors ==> r1 = r2) /\
        SORTED less_FST st.active /\
        EVERY (\e,r. e = the 0 (lookup r int_end)) st.active /\
        EVERY (\e,r. MEM r l) st.active /\
        EVERY (\r1,r2. MEM r1 l /\ MEM r2 l /\ EL r1 sth.colors = EL r2 sth.colors ==> r1 = r2) forced
    )
`

val remove_inactive_intervals_invariants = Q.store_thm("remove_inactive_intervals_invariants",
    `!beg st int_beg int_end sth l pos forced.
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    pos <= beg ==>
    ?stout sthout. (Success stout, sthout) = remove_inactive_intervals beg st sth /\
    good_linear_scan_state int_beg int_end stout sthout l beg forced`,

    recInduct remove_inactive_intervals_ind >>
    rw [] >>
    once_rewrite_tac [remove_inactive_intervals_def] >>
    rw msimps >>
    Cases_on `st.active`

    THEN1 (
        rfs [good_linear_scan_state_def] >>
        fs [EVERY_MEM] >> rw []
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
        THEN1 (
          CCONTR_TAC >> fs [] >>
          `pos <= the 0 (lookup r int_end)` by intLib.COOPER_TAC >>
          res_tac
        )
    ) >>

    PairCases_on `h` >>
    rename1 `st.active = (e,r)::activetail` >>
    rw []

    THEN1 (
        rfs [] >>
        `r < LENGTH sth.colors` by fs [EVERY_MEM, FORALL_PROD, good_linear_scan_state_def] >>
        rfs [] >>
        first_x_assum (qspecl_then [`EL r sth.colors`, `int_beg`, `int_end`, `sth`, `l`, `e+1`, `forced`] assume_tac) >>
        `e+1 <= beg` by intLib.COOPER_TAC >>
        sg `good_linear_scan_state int_beg int_end (st with <| active := activetail; colorpool updated_by (\l. (EL r sth.colors)::l) |>) sth l (e+1) forced` THEN1 (
            qpat_x_assum `good_linear_scan_state _ _ _ _ _ _ _ /\ _ ==> _` kall_tac >>
            fs [good_linear_scan_state_def] >>
            `pos <= 1+e` by (fs [EVERY_MEM] >> metis_tac []) >>
            sg `!(h:num) l1 l2. PERM (l1 ++ h::l2) ((h::l1) ++ l2)` THEN1 (
              rw [] >>
              `PERM (l1 ++ [h]) ([h] ++ l1)` by simp [PERM_APPEND] >>
              `PERM (l1 ++ [h] ++ l2) ([h] ++ l1 ++ l2)` by simp [PERM_APPEND_IFF] >>
              rfs [] >>
              `l1 ++ h::l2 = (l1 ++ [h]) ++ l2` by simp [] >>
              simp []
            ) >>
            `ALL_DISTINCT ((EL r sth.colors :: st.colorpool) ++ MAP (\(e,r). EL r sth.colors) activetail)` by metis_tac [ALL_DISTINCT_PERM] >>
            rfs [] >>
            fs [EVERY_MEM] >> rw []
            THEN1 (
              res_tac >>
              intLib.COOPER_TAC
            )
            THEN1 (
              `pos <= the 0 (lookup r' int_end)` by intLib.COOPER_TAC >>
              res_tac >>
              CCONTR_TAC >>
              intLib.COOPER_TAC
            )
            THEN1 (
              assume_tac transitive_less_FST >>
              imp_res_tac SORTED_EQ >>
              fs [less_FST_def] >>
              intLib.COOPER_TAC
            )
            THEN1 imp_res_tac SORTED_TL
        ) >>
        rw []
    )

    THEN1 (
        rfs [] >>
        `beg <= e` by intLib.COOPER_TAC >>
        sg `!e r. MEM (e,r) st.active ==> beg <= e` THEN1 (
          assume_tac transitive_less_FST >>
          rw []
          THEN1 rw [] >>
          fs [good_linear_scan_state_def] >>
          `less_FST (e,r) (e',r')` by imp_res_tac SORTED_EQ >>
          fs [less_FST_def] >>
          intLib.COOPER_TAC
        ) >>
        qpat_x_assum `st.active = _` kall_tac >>
        fs [good_linear_scan_state_def] >>
        fs [EVERY_MEM] >> rw []
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
        THEN1 (
          `pos <= the 0 (lookup r int_end)` by intLib.COOPER_TAC >>
          metis_tac []
        )
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
    )
)

val add_active_interval_output = Q.store_thm("add_active_interval_output",
    `!lin x lout.
    SORTED less_FST lin /\
    lout = add_active_interval (e,r) lin ==>
    SORTED less_FST lout /\
    ?l1 l2. lin = l1 ++ l2 /\ lout = l1 ++ (e,r)::l2`,

    Induct_on `lin` >>
    rw [add_active_interval_def]

    THEN1 (
        rw [SORTED_DEF, less_FST_def]
    )
    THEN1 (
        qexists_tac `[]` >> qexists_tac `h::lin` >>
        rw []
    )
    THEN1 (
        `FST h <= e` by intLib.COOPER_TAC >>
        assume_tac transitive_less_FST >>
        fs [SORTED_EQ] >>
        rw [] >>
        rw [less_FST_def]
    )
    THEN1 (
        `FST h <= e` by intLib.COOPER_TAC >>
        assume_tac transitive_less_FST >>
        fs [SORTED_EQ] >>
        qexists_tac `h::l1` >> qexists_tac `l2` >>
        rw []
    )
)

val find_color_in_list_output = Q.store_thm("find_color_in_list_output",
    `!forbidden col l rest.
    find_color_in_list l forbidden = SOME (col, rest) ==>
    MEM col l /\ col NOTIN domain forbidden /\
    ?l1 l2. rest = l1 ++ l2 /\ l = l1 ++ col::l2`,

    NTAC 2 gen_tac >>
    Induct_on `l` >>
    rpt gen_tac >>
    simp [find_color_in_list_def] >>
    TOP_CASE_TAC
    THEN1 (
      rw []
      THEN1 fs [lookup_NONE_domain]
      THEN1 (
        qexists_tac `[]` >>
        qexists_tac `l` >>
        rw []
      )
    )
    THEN1 (
      rw [] >>
      every_case_tac >> fs [] >>
      qexists_tac `h::l1` >>
      qexists_tac `l2` >>
      rw []
    )
)

val find_color_in_colornum_invariants = Q.store_thm("find_color_in_colornum_invariants",
    `!st forbidden int_beg int_end sth l pos forced.
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    domain forbidden SUBSET {EL r sth.colors | r | MEM r l} /\
    find_color_in_colornum st forbidden = (stout, SOME col) ==>
    good_linear_scan_state int_beg int_end (stout with colorpool updated_by (\l. col::l)) sth l pos forced /\
    st.colornum <= col /\ col < stout.colornum /\
    st.colornum <= stout.colornum /\
    col NOTIN domain forbidden /\
    stout.active = st.active`,

    rw [find_color_in_colornum_def] >> rw []
    THEN1 (
      fs [good_linear_scan_state_def] >>
      rveq >>
      fs [EVERY_MEM, FORALL_PROD] >> rw []
      THEN1 (
        CCONTR_TAC >> fs [] >>
        res_tac >> intLib.COOPER_TAC
      )
      THEN1 (
        CCONTR_TAC >> fs [MEM_MAP, EXISTS_PROD] >>
        res_tac >> intLib.COOPER_TAC
      ) >>
      fs [lookup_NONE_domain] >>
      res_tac >> intLib.COOPER_TAC
    )
    THEN1 (
      CCONTR_TAC >> fs [good_linear_scan_state_def] >>
      `st.colornum IN {EL r sth.colors | r | MEM r l}` by fs [SUBSET_DEF] >>
      fs [EVERY_MEM] >>
      rpt (first_x_assum (qspec_then `r` assume_tac)) >>
      rfs []
    )
)

val find_color_invariants = Q.store_thm("find_color_invariants",
    `!st forbidden stout col int_beg int_end sth l pos forced.
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    domain forbidden SUBSET {EL r sth.colors | r | MEM r l} /\
    find_color st forbidden = (stout, SOME col) ==>
    good_linear_scan_state int_beg int_end (stout with colorpool updated_by (\l. col::l)) sth l pos forced /\
    col < stout.colornum /\
    col NOTIN domain forbidden /\
    (MEM col st.colorpool \/ st.colornum <= col) /\
    stout.active = st.active`,

    rpt gen_tac >>
    simp [find_color_def] >>
    Cases_on `find_color_in_list st.colorpool forbidden` >>
    simp [] >> strip_tac
    THEN1 metis_tac [find_color_in_colornum_invariants]
    THEN1 (
      PairCases_on `x` >>
      rename1 `find_color_in_list st.colorpool forbidden = SOME (col' , rest)` >> fs [] >> rveq >>
      imp_res_tac find_color_in_list_output >>
      simp [] >>
      sg `PERM st.colorpool (col::rest)` THEN1 (
        simp [] >>
        `PERM (l1 ++ [col]) ([col] ++ l1)` by simp [PERM_APPEND] >>
        fs [] >>
        `PERM (l1 ++ [col] ++ l2) (col::l1 ++ l2)` by simp [PERM_APPEND_IFF] >>
        FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC, APPEND]
      ) >>
      sg `ALL_DISTINCT (col::(l1++l2) ++ MAP (\(e,r). EL r sth.colors) st.active)` THEN1 (
        FULL_SIMP_TAC pure_ss [good_linear_scan_state_def] >>
        metis_tac [ALL_DISTINCT_PERM, PERM_APPEND_IFF]
      ) >>
      fs [good_linear_scan_state_def, EVERY_MEM] >>
      metis_tac []
    )
)

val update_color_active_colors_same = Q.store_thm("update_color_active_colors_same",
    `!e reg active regcol colors.
    MAP (\e,r. EL r (LUPDATE regcol reg colors)) (FILTER (\e,r. r <> reg) active) = MAP (\e,r. EL r colors) (FILTER (\e,r. r <> reg) active)`,
    Induct_on `active` >>
    rw [] >>
    pairarg_tac >>
    rw [EL_LUPDATE] >>
    fs []
)

(* TODO: this proof is terribly slow because the simplifier messes up, even if with the "lower lever" tactics *)
val forced_update_stack_color_lemma = Q.store_thm("forced_update_stack_color_lemma",
    `!(colors : num list) (stacknum : num) l r2 r1.
    EVERY (\r. EL r colors < stacknum) l /\
    MEM r2 l /\
    r1 < LENGTH colors /\
    EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum r1 colors) ==>
    r1 = r2`,

    Induct_on `l` >>
    rw []
    THEN1 (
        FULL_SIMP_TAC bool_ss [EL_LUPDATE] >>
        REV_FULL_SIMP_TAC pure_ss [] >>
        FULL_SIMP_TAC bool_ss [] >>
        Cases_on `h = r1` >> FULL_SIMP_TAC bool_ss [] >>
        FULL_SIMP_TAC arith_ss []
    )
    THEN1 metis_tac []
)

(* TODO: this should be part of the standard library, but I couldn't find it *)
val IS_SPARSE_SUBLIST_def = Define`
  (
    IS_SPARSE_SUBLIST [] l2 = T
  ) /\ (
    IS_SPARSE_SUBLIST (x::xs) [] = F
  ) /\ (
    IS_SPARSE_SUBLIST (x::xs) (y::ys) =
      ((x=y /\ IS_SPARSE_SUBLIST xs ys) \/ IS_SPARSE_SUBLIST (x::xs) ys)
  )`

val FILTER_IS_SPARSE_SUBLIST = Q.store_thm("FILTER_IS_SPARSE_SUBLIST",
    `!l. IS_SPARSE_SUBLIST (FILTER P l) l`,
    Induct_on `l` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Cases_on `FILTER P l` >>
    rw [IS_SPARSE_SUBLIST_def]
)

val MEM_SPARSE_SUBLIST = Q.store_thm("MEM_SPARSE_SUBLIST",
    `!l1 l2 x. IS_SPARSE_SUBLIST l1 l2 /\ MEM x l1 ==> MEM x l2`,
    Induct_on `l1` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Induct_on `l2` >>
    fs [IS_SPARSE_SUBLIST_def] >> rw [] >>
    rw []
)

val IS_SPARSE_SUBLIST_APPEND = Q.store_thm("IS_SPARSE_SUBLIST_APPEND",
    `!l1 l2 l. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (l ++ l1) (l ++ l2)`,
    Induct_on `l` >>
    rw [IS_SPARSE_SUBLIST_def]
)

val MAP_IS_SPARSE_SUBLIST = Q.store_thm("MAP_IS_SPARSE_SUBLIST",
    `!l1 l2. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (MAP f l1) (MAP f l2)`,
    Induct_on `l1` >>
    Induct_on `l2` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    rfs []
)

val ALL_DISTINCT_IS_SPARSE_SUBLIST = Q.store_thm("ALL_DISTINCT_IS_SPARSE_SUBLIST",
    `!l1 l2. ALL_DISTINCT l2 /\ IS_SPARSE_SUBLIST l1 l2 ==> ALL_DISTINCT l1`,
    Induct_on `l1` >>
    rw [IS_SPARSE_SUBLIST_def]
    THEN1 (
        Induct_on `l2` >> fs [IS_SPARSE_SUBLIST_def] >> rw []
        THEN1 (
          CCONTR_TAC >> fs [] >>
          imp_res_tac MEM_SPARSE_SUBLIST
        ) >>
        res_tac
    )
    THEN1 (
        Induct_on `l2` >> fs [IS_SPARSE_SUBLIST_def] >> rw [] >>
        res_tac
    )
)

val spill_register_FILTER_invariants_hidden = Q.store_thm("spill_register_FILTER_invariants_hidden",
    `!int_beg int_end st sth l pos forced reg.
    id (~(is_phy_var reg) \/ ~(MEM reg l)) /\
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    reg < LENGTH sth.colors /\
    the 0 (lookup reg int_beg) <= pos ==>
    ?stout sthout. (Success stout, sthout) = spill_register (st with active := FILTER (\e,r. r <> reg) st.active) reg sth /\
    good_linear_scan_state int_beg int_end stout sthout (reg::l) pos forced`,

    rw [spill_register_def] >> rw msimps >>
    fs [good_linear_scan_state_def] >>
    rpt strip_tac
    THEN1 (
        rw [update_color_active_colors_same] >>
        metis_tac [FILTER_IS_SPARSE_SUBLIST, MAP_IS_SPARSE_SUBLIST, IS_SPARSE_SUBLIST_APPEND, ALL_DISTINCT_IS_SPARSE_SUBLIST]
    )
    THEN1 rw [EL_LUPDATE]
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD] >>
        rw [EL_LUPDATE] >>
        `EL r sth.colors < st.stacknum` by rw [] >>
        rw []
    )
    THEN1 (
        rw [EXTENSION] >>
        eq_tac >>
        rw [] >>
        qexists_tac `r` >>
        rw [EL_LUPDATE] >>
        fs [EL_LUPDATE, id_def]
    )
    THEN1 (
        `!r. MEM r l ==> EL r sth.colors < st.stacknum` by fs [EVERY_MEM] >>
        rpt (qpat_x_assum `EVERY _ _` kall_tac) >>
        rpt (qpat_x_assum `!x x. _` kall_tac) >>
        rpt (qpat_x_assum `domain _ = _` kall_tac) >>
        sg `MAP (\r. EL r (LUPDATE st.stacknum reg sth.colors)) (FILTER is_phy_var l) = MAP (\r. EL r sth.colors) (FILTER is_phy_var l)` THEN1 (
            rpt (qpat_x_assum `ALL_DISTINCT _` kall_tac) >>
            fs [id_def] >>
            Induct_on `l` >>
            rfs [EL_LUPDATE] >> rw [] >>
            every_case_tac >>
            res_tac
        ) >>
        rw [] >>
        rpt (qpat_x_assum `ALL_DISTINCT _` kall_tac) >>
        rpt (qpat_x_assum `MAP _ _ =  _` kall_tac) >>
        rpt (qpat_x_assum `id _` kall_tac) >>
        simp [EL_LUPDATE] >>
        Induct_on `l` >> rw [] >>
        `EL h sth.colors < st.stacknum` by rw [] >>
        rw []
    )
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER] >>
        metis_tac []
    )
    THEN1 fs [EL_LUPDATE]
    THEN1 fs [EL_LUPDATE, EVERY_MEM]
    THEN1 fs [MEM_FILTER]
    THEN1 fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 rw []
    THEN1 metis_tac [forced_update_stack_color_lemma]
    THEN1 metis_tac [forced_update_stack_color_lemma]
    THEN1 (
        fs [EL_LUPDATE] >>
        Cases_on `r1 = reg /\ reg < LENGTH sth.colors` >>
        Cases_on `r2 = reg /\ reg < LENGTH sth.colors` >>
        fs [EVERY_MEM] >>
        TRY (`EL r2 sth.colors < st.stacknum` by rw []) >>
        TRY (`EL r1 sth.colors < st.stacknum` by rw []) >>
        rw []
    )
    THEN1 metis_tac [transitive_less_FST, SORTED_FILTER]
    THEN1 fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER] >>
        metis_tac []
    )
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD] >>
        RW_TAC bool_ss [EL_LUPDATE] >>
        rename1 `MEM (r1, r2) forced`
        THEN1 (
            Cases_on `MEM r2 l` >> fs [] >>
            `EL r2 sth.colors < st.stacknum` by rw [] >>
            rw []
        )
        THEN1 (
            Cases_on `MEM r1 l` >> fs [] >>
            `EL r1 sth.colors < st.stacknum` by rw [] >>
            rw []
        )
    )
)

val spill_register_FILTER_invariants =
  spill_register_FILTER_invariants_hidden
  |> REWRITE_RULE [id_def]
  |> curry save_thm "spill_register_FILTER_invariants"

val FILTER_MEM_active = Q.store_thm("FILTER_MEM_active",
    `!(reg:num) l. (!(e:int). ~(MEM (e,reg) l)) ==> FILTER (\e,r. r <> reg) l = l`,
    Induct_on `l` >> rw [] >>
    pairarg_tac >> fs [] >>
    metis_tac []
)

val spill_register_invariants = Q.store_thm("spill_register_invariants",
    `!int_beg int_end st sth l pos forced reg.
    (!e. ~(MEM (e,reg) st.active)) /\
    (~(is_phy_var reg) \/ ~(MEM reg l)) /\
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    reg < LENGTH sth.colors /\
    the 0 (lookup reg int_beg) <= pos ==>
    ?stout sthout. (Success stout, sthout) = spill_register st reg sth /\
    good_linear_scan_state int_beg int_end stout sthout (reg::l) pos forced`,

    rw [] >>
    `FILTER (\e,r. r <> reg) st.active = st.active` by simp [FILTER_MEM_active] >>
    `st = st with active := FILTER (\e,r. r <> reg) st.active` by simp [linear_scan_state_component_equality] >>
    metis_tac [spill_register_FILTER_invariants]
)

val edges_to_adjlist_step_def = Define`
    edges_to_adjlist_step int_beg (a,b) acc =
      if ($< LEX $<=) (the 0i (lookup a int_beg), a) (the 0i (lookup b int_beg), b) then
        insert b (a::(the [] (lookup b acc))) acc
      else
        insert a (b::(the [] (lookup a acc))) acc
`

val edges_to_adjlist_FOLDL = Q.store_thm("edges_to_adjlist_FOLDL",
    `!forced int_beg acc.
    edges_to_adjlist forced int_beg acc = FOLDL (\acc pair. edges_to_adjlist_step int_beg pair acc) acc forced`,
    Induct_on `forced`
    THEN1 rw [edges_to_adjlist_def] >>
    rw [] >>
    PairCases_on `h` >>
    rw [edges_to_adjlist_def, edges_to_adjlist_step_def] >>
    every_case_tac
)

val forbidden_is_from_forced_def = Define`
    forbidden_is_from_forced forced int_beg reg forbidden =
        !reg2. ($< LEX $<=) (the 0i (lookup reg2 int_beg), reg2) (the 0i (lookup reg int_beg), reg) /\
               (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) ==>
               MEM reg2 forbidden
`

val forbidden_is_from_map_color_forced_def = Define`
    forbidden_is_from_map_color_forced forced l colors reg forbidden =
        !reg2. MEM reg2 l /\
               (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) ==>
               EL reg2 colors IN domain forbidden
`

val edges_to_adjlist_FOLDR_output = Q.store_thm("edges_to_adjlist_FOLDR_output",
    `!forced int_beg.
    !reg. forbidden_is_from_forced forced int_beg reg (the [] (lookup reg (FOLDR (\pair acc. edges_to_adjlist_step int_beg pair acc) LN forced)))`,

    simp [forbidden_is_from_forced_def] >>
    Induct_on `forced`
    THEN1 rw [forbidden_is_from_forced_def] >>
    simp [] >>
    rpt gen_tac >>
    first_x_assum (qspec_then `int_beg` assume_tac) >>
    qabbrev_tac `adjlist = FOLDR (\pair acc. edges_to_adjlist_step int_beg pair acc) LN forced` >>
    qpat_x_assum `Abbrev _` kall_tac >>
    PairCases_on `h` >>

    strip_tac
    THEN1 (
      fs [] >>
      simp [edges_to_adjlist_step_def, the_def]
    )
    THEN1 (
      simp [edges_to_adjlist_step_def, the_def] >>
      CASE_TAC >>
      rw [lookup_insert, the_def] >>
      rw [METIS_PROVE [] ``!a b. a \/ b <=> ~a ==> b``]
    )
    THEN1 (
      fs [] >>
      simp [edges_to_adjlist_step_def, the_def] >>
      CASE_TAC
      THEN1 (
        sg `h0 = h1` THEN1 (
          fs [LEX_DEF] >>
          intLib.COOPER_TAC
        ) >>
        simp [the_def]
      )
      THEN1 (
        simp [lookup_insert, the_def]
      )
    )
    THEN1 (
      simp [edges_to_adjlist_step_def, the_def] >>
      CASE_TAC >>
      rw [lookup_insert, the_def] >>
      rw [METIS_PROVE [] ``!a b. a \/ b <=> ~a ==> b``]
    )
)

val edges_to_adjlist_output = Q.store_thm("edges_to_adjlist_output",
    `!forced int_beg.
    !reg. forbidden_is_from_forced forced int_beg reg (the [] (lookup reg (edges_to_adjlist forced int_beg LN)))`,

    rw [edges_to_adjlist_FOLDL, GSYM FOLDR_REVERSE] >>
    qspecl_then [`REVERSE forced`, `int_beg`, `reg`] assume_tac edges_to_adjlist_FOLDR_output >>
    fs [forbidden_is_from_forced_def] >>
    metis_tac []
)

val state_invariants_remove_head = Q.store_thm("state_invariants_remove_head",
    `!int_beg int_end stout sthout reg l pos forced.
    MEM reg l /\
    good_linear_scan_state int_beg int_end stout sthout (reg::l) pos forced ==>
    good_linear_scan_state int_beg int_end stout sthout l pos forced`,

    rw [] >>
    `!r. r = reg \/ MEM r l <=> MEM r l` by metis_tac [] >>
    rw [good_linear_scan_state_def] >>
    fs [good_linear_scan_state_def] >>
    every_case_tac >> fs []
)

val find_last_stealable_success = Q.store_thm("find_last_stealable_success",
    `!forbidden sth active.
    EVERY (\e,r. r < LENGTH sth.colors) active ==>
    ?optout. find_last_stealable active forbidden sth = (Success optout, sth)`,

    NTAC 2 gen_tac >>
    Induct_on `active` >>
    rw [find_last_stealable_def] >> simp msimps >>
    fs [] >>
    every_case_tac >>
    PairCases_on `h` >>
    rfs []
)

val find_last_stealable_output = Q.store_thm("find_last_stealable_output",
    `!forbidden sth active steal rest.
    find_last_stealable active forbidden sth = (Success (SOME (steal, rest)), sth) ==>
    ~is_phy_var (SND steal) /\ lookup (EL (SND steal) sth.colors) forbidden = NONE /\
    ?l1 l2. rest = l1 ++ l2 /\ active = l1 ++ steal::l2`,

    NTAC 2 gen_tac >>
    Induct_on `active` >>
    rw [find_last_stealable_def] >> simp msimps >>
    fs msimps
    THEN1 (
        every_case_tac >> fs [] >>
        rveq >> simp []
    )
    THEN1 (
        every_case_tac >> fs []
    )
    THEN1 (
        every_case_tac >> fs []
        THEN1 (
            qexists_tac `[]` >>
            qexists_tac `active` >>
            rw []
        )
        THEN1 (
            qexists_tac `h::l1` >>
            qexists_tac `l2` >>
            rw []
        )
    )
)

val good_linear_scan_state_active_length_colors = Q.store_thm("good_linear_scan_state_active_length_colors",
    `!int_beg int_end st sth l pos forced.
    good_linear_scan_state int_beg int_end st sth l pos forced ==>
    EVERY (\e,r. r < LENGTH sth.colors) st.active`,

    rw [good_linear_scan_state_def, EVERY_MEM] >>
    res_tac >>
    rpt (pairarg_tac >> fs [])
)

val color_register_eq = Q.store_thm("color_register_eq",
    `!st reg col rend.
    color_register st reg col rend =
      do
        update_colors reg col;
        return (
          st with
            <| active  updated_by add_active_interval (rend, reg)
             ; phyregs := if is_phy_var reg then  (insert col ()) st.phyregs else st.phyregs
             |>
        )
      od`,
    rw [color_register_def] >> fs msimps >>
    rw [FUN_EQ_THM] >>
    every_case_tac >>
    simp [linear_scan_state_component_equality]
)

val color_register_invariants = Q.store_thm("color_register_invariants",
    `!int_beg int_end st sth l pos forced reg col forbidden.
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    forbidden_is_from_map_color_forced forced l sth.colors reg forbidden /\
    col NOTIN domain forbidden /\
    (is_phy_var reg ==> domain st.phyregs SUBSET domain forbidden) /\
    ~MEM col (st.colorpool ++ MAP (\(e,r). EL r sth.colors) st.active) /\
    the 0 (lookup reg int_beg) = pos /\
    the 0 (lookup reg int_beg) <= the 0 (lookup reg int_end) /\
    col < st.colornum /\
    reg < LENGTH sth.colors /\
    ~MEM reg l
    ==>
    ?stout sthout. (Success stout, sthout) = color_register st reg col (the 0 (lookup reg int_end)) sth /\
    good_linear_scan_state int_beg int_end stout sthout (reg::l) pos forced`,

    rpt strip_tac >> simp [color_register_eq] >> simp msimps >>
    fs [good_linear_scan_state_def] >>
    rpt strip_tac
    THEN1 (
      sg `!e. ~MEM (e,reg) st.active` THEN1 (
        strip_tac >> CCONTR_TAC >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD] >>
        res_tac
      ) >>
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
      sg `MAP (\e,r. EL r (LUPDATE col reg sth.colors)) l1 = MAP (\e,r. EL r sth.colors) l1 /\ MAP (\e,r. EL r (LUPDATE col reg sth.colors)) l2 = MAP (\e,r. EL r sth.colors) l2` THEN1 (
        strip_tac >>
        rw [MAP_EQ_f] >>
        pairarg_tac >> fs [] >>
        rw [EL_LUPDATE] >>
        fs [] >> res_tac
      ) >>
      simp [EL_LUPDATE] >>
      sg `!ll1 ll2 (x:num) ll3. PERM (ll1 ++ ll2 ++ [x] ++ ll3) ([x] ++ ll1 ++ ll2 ++ ll3)` THEN1 (
        rw [] >>
        `PERM (ll1 ++ ll2 ++ [x]) ([x] ++ (ll1 ++ ll2))` by rw [PERM_APPEND] >>
        `PERM (ll1 ++ ll2 ++ [x] ++ ll3) ([x] ++ (ll1 ++ ll2) ++ ll3)` by rw [PERM_APPEND_IFF] >>
        fs []
      ) >>
      sg `ALL_DISTINCT ([col] ++ st.colorpool ++ MAP (\e,r. EL r sth.colors) st.active)` THEN1 (
        qpat_x_assum `st.active = _` kall_tac >>
        simp []
      ) >>
      REV_FULL_SIMP_TAC pure_ss [MAP_APPEND, APPEND_ASSOC] >>
      metis_tac [ALL_DISTINCT_PERM]
    )
    THEN1 simp [EL_LUPDATE]
    THEN1 (
      fs [EVERY_MEM, EL_LUPDATE] >>
      rw []
    )
    THEN1 (
      rfs [] >>
      rw [EL_LUPDATE, EXTENSION]
      THEN1 (
        eq_tac
        THEN1 (
          rw []
          THEN1 (qexists_tac `reg` >> rw [])
          THEN1 (qexists_tac `r` >> rw [] >> fs [])
        )
        THEN1 (
          rw [] >>
          Cases_on `r = reg` >> fs [] >>
          disj2_tac >> qexists_tac `r` >>
          rw []
        )
      )
      THEN1 (
        eq_tac >> rw [] >> metis_tac []
      )
    )
    THEN1 (
        rw []
        THEN1 (
          simp [EL_LUPDATE] >>
          `col NOTIN domain st.phyregs` by metis_tac [SUBSET_DEF] >>
          qpat_x_assum `col NOTIN domain st.phyregs` mp_tac >>
          once_rewrite_tac [METIS_PROVE [] ``!a b. a ==> b <=> ~b ==> ~a``] >>
          rw [MEM_MAP, MEM_FILTER] >>
          Cases_on `r = reg` >> fs [] >>
          qexists_tac `r` >> rw []
        ) >> (
          sg `MAP (\r. EL r (LUPDATE col reg sth.colors)) (FILTER is_phy_var l) = MAP (\r. EL r sth.colors) (FILTER is_phy_var l)` THEN1 (
              qpat_x_assum `~MEM reg l` mp_tac >>
              rpt (first_x_assum kall_tac) >>
              Induct_on `l` >>
              fs [EL_LUPDATE] >> rw []
          ) >>
          simp []
        )
    )
    THEN1 (
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
      rw [EL_LUPDATE] >>
      fs [EVERY_MEM, FORALL_PROD] >>
      metis_tac []
    )
    THEN1 fs [EL_LUPDATE, EVERY_MEM]
    THEN1 (
        fs [EL_LUPDATE, EVERY_MEM] >>
        rw []
    )
    THEN1 (
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs []
    )
    THEN1 (
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
      fs [EVERY_MEM] >>
      rw [EL_LUPDATE]
    )
    THEN1 (
        intLib.COOPER_TAC
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs [] >>
        rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
        fs [EVERY_MEM] >>
        rw []
        THEN1 fs []
        THEN1 intLib.COOPER_TAC
        THEN1 fs []
    )
    THEN1 fs [EL_LUPDATE]
    THEN1 (
        rveq >>
        CCONTR_TAC >>
        rfs [EL_LUPDATE] >>
        fs [interval_intersect_def, EVERY_MEM] >>
        `EL r2 sth.colors < st.colormax` by rw [] >>
        `MEM (the 0 (lookup r2 int_end), r2) st.active` by rw [] >>
        fs [MEM_MAP, FORALL_PROD] >>
        metis_tac []
    )
    THEN1 (
        rveq >>
        CCONTR_TAC >>
        rfs [EL_LUPDATE] >>
        fs [interval_intersect_def, EVERY_MEM] >>
        `EL r1 sth.colors < st.colormax` by rw [] >>
        `MEM (the 0 (lookup r1 int_end), r1) st.active` by rw [] >>
        fs [MEM_MAP, FORALL_PROD] >>
        metis_tac []
    )
    THEN1 (
        fs [EL_LUPDATE] >>
        every_case_tac >> rfs []
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs []
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs [] >>
        rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD]
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs [] >>
        rpt (first_x_assum (qspecl_then [`reg`, `the 0 (lookup reg int_end)`] assume_tac)) >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD] >>
        metis_tac []
    )
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD, forbidden_is_from_map_color_forced_def] >>
        rw [] >>
        rename1 `MEM (reg1, reg2) forced`
        THEN1 (
          REV_FULL_SIMP_TAC bool_ss [EL_LUPDATE] >>
          Cases_on `reg1 = reg2` >> fs [] >>
          `EL reg2 sth.colors IN domain forbidden` by res_tac
        )
        THEN1 (
          REV_FULL_SIMP_TAC bool_ss [EL_LUPDATE] >>
          Cases_on `reg1 = reg2` >> fs [] >>
          `EL reg1 sth.colors IN domain forbidden` by res_tac >>
          metis_tac []
        )
        THEN1 (
          REV_FULL_SIMP_TAC bool_ss [EL_LUPDATE] >>
          Cases_on `reg1 = reg` >> FULL_SIMP_TAC bool_ss [] >>
          Cases_on `reg2 = reg` >> FULL_SIMP_TAC bool_ss []
        )
    )
)

val find_spill_invariants = Q.store_thm("find_spill_invariants",
    `!int_beg int_end st sth l pos forced reg.
    (!e. ~(MEM (e,reg) st.active)) /\
    ~MEM reg l /\
    good_linear_scan_state int_beg int_end st sth l pos forced /\
    reg < LENGTH sth.colors /\
    forbidden_is_from_map_color_forced forced l sth.colors reg forbidden /\
    (is_phy_var reg ==> domain st.phyregs SUBSET domain forbidden) /\
    the 0 (lookup reg int_end) = rend /\
    the 0 (lookup reg int_beg) = pos /\
    the 0 (lookup reg int_beg) <= the 0 (lookup reg int_end) ==>
    ?stout sthout. (Success stout, sthout) = find_spill st forbidden reg rend force sth /\
    good_linear_scan_state int_beg int_end stout sthout (reg::l) pos forced`,

    rw [find_spill_def] >> simp msimps >>
    imp_res_tac good_linear_scan_state_active_length_colors >>
    `?optsteal. find_last_stealable st.active forbidden sth = (Success optsteal, sth)` by metis_tac [find_last_stealable_success] >>
    simp [] >>
    CASE_TAC
    THEN1 rw [spill_register_invariants] >>
    PairCases_on `x` >>
    rename1 `find_last_stealable _ _ _ = (Success (SOME ((stealend, stealreg), rest)), _)` >>
    simp [] >>
    reverse CASE_TAC
    THEN1 rw [spill_register_invariants] >>
    qpat_x_assum `_ \/ _ < _` kall_tac >>
    imp_res_tac find_last_stealable_output >>
    `stealreg < LENGTH sth.colors` by fs [EVERY_MEM, FORALL_PROD] >>
    `MEM (stealend, stealreg) st.active` by rw [] >>
    `MEM stealreg l` by fs [good_linear_scan_state_def, EVERY_MEM, FORALL_PROD] >>
    rw [] >>
    FULL_SIMP_TAC pure_ss [SND] >>
    `(EL stealreg sth.colors) NOTIN domain forbidden` by fs [lookup_NONE_domain] >>
    `EL stealreg sth.colors < st.colornum` by fs [good_linear_scan_state_def] >>
    sg `ALL_DISTINCT ([EL stealreg sth.colors] ++ st.colorpool ++ (MAP (\e,r. EL r sth.colors) l1) ++ (MAP (\e,r. EL r sth.colors) l2))` THEN1 (
        `ALL_DISTINCT (st.colorpool ++ MAP (\e,r. EL r sth.colors) st.active)` by rfs [good_linear_scan_state_def] >>
        REV_FULL_SIMP_TAC std_ss [MAP, MAP_APPEND] >>
        sg `!ll ll1 (x:num) ll2. PERM (ll ++ (ll1 ++ x::ll2)) ([x] ++ ll ++ ll1 ++ ll2)` THEN1 (
            rw [] >>
            `PERM (ll ++ ll1 ++ [x]) ([x] ++ (ll ++ ll1))` by simp [PERM_APPEND] >>
            `PERM (ll ++ ll1 ++ [x] ++ ll2) ([x] ++ (ll ++ ll1) ++ ll2)` by simp [PERM_APPEND_IFF] >>
            FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC, APPEND]
        ) >>
        FULL_SIMP_TAC pure_ss [APPEND] >>
        metis_tac [ALL_DISTINCT_PERM]
    ) >>
    sg `(!e. ~MEM (e, stealreg) l1) /\ (!e. ~MEM (e, stealreg) l2)` THEN1 (
        `ALL_DISTINCT (MAP (\e,r. EL r sth.colors) st.active)` by rfs [good_linear_scan_state_def, ALL_DISTINCT_APPEND] >>
        `ALL_DISTINCT st.active` by metis_tac [ALL_DISTINCT_MAP] >>
        rfs [] >>
        sg `!(x:int#num) ll1 ll2. PERM (ll1 ++ [x] ++ ll2) ([x] ++ ll1 ++ ll2)` THEN1 (
            rw [] >>
            `PERM (ll1 ++ [x]) ([x] ++ ll1)` by simp [PERM_APPEND] >>
            `PERM (ll1 ++ [x] ++ ll2) ([x] ++ ll1 ++ ll2)` by simp [PERM_APPEND_IFF] >>
            fs []
        ) >>
        fs [] >>
        `ALL_DISTINCT ((stealend, stealreg)::(l1 ++ l2))` by metis_tac [ALL_DISTINCT_PERM] >>
        fs [] >>
        `EVERY (\e,r. e = the 0 (lookup r int_end)) (l1++l2)` by fs [good_linear_scan_state_def, EVERY_APPEND] >>
        fs [EVERY_APPEND] >>
        `stealend = the 0 (lookup stealreg int_end)` by fs [good_linear_scan_state_def, EVERY_MEM, FORALL_PROD] >>
        fs [] >>
        rw [] >>
        CCONTR_TAC >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD] >>
        res_tac >>
        fs []
    ) >>
    sg `FILTER (\e,r. r <> stealreg) st.active = l1 ++ l2` THEN1 (
        imp_res_tac FILTER_MEM_active >>
        simp [FILTER_APPEND]
    ) >>
    `the 0 (lookup stealreg int_beg) <= the 0 (lookup reg int_beg)` by fs [good_linear_scan_state_def, EVERY_MEM] >>
    qspecl_then [`int_beg`, `int_end`, `st`, `sth`, `l`, `the 0 (lookup reg int_beg)`, `forced`, `stealreg`] assume_tac (GSYM spill_register_FILTER_invariants) >>
    rfs [] >>
    imp_res_tac state_invariants_remove_head >>
    qspecl_then [`int_beg`, `int_end`, `stout`, `sthout`, `l`, `the 0 (lookup reg int_beg)`, `forced`, `reg`, `EL stealreg sth.colors`, `forbidden`] assume_tac color_register_invariants >>
    rfs [] >>
    fs (spill_register_def::msimps) >> Cases_on `stealreg < LENGTH sth.colors` >> fs [] >>
    rveq >>
    fs [] >>
    sg `forbidden_is_from_map_color_forced forced l (LUPDATE st.stacknum stealreg sth.colors) reg forbidden` THEN1 (
        fs [forbidden_is_from_map_color_forced_def] >>
        rw [EL_LUPDATE] >>
        rfs [] >>
        `EL reg2 sth.colors IN domain forbidden` by metis_tac []
    ) >>
    fs [] >>
    rfs [] >>
    sg `~MEM (EL stealreg sth.colors) (MAP (\e,r. EL r (LUPDATE st.stacknum stealreg sth.colors)) (l1 ++ l2))` THEN1 (
        sg `!(l: (int#num) list). (!e. ~MEM (e, stealreg) l) ==> MAP (\e,r. EL r (LUPDATE st.stacknum stealreg sth.colors)) l = MAP (\e,r. EL r sth.colors) l` THEN1 (
            rpt (first_x_assum kall_tac) >>
            Induct_on `l` >>
            rw [EL_LUPDATE] >>
            pairarg_tac >> fs [] >>
            rw [] >> metis_tac []
        ) >>
        rfs []
    ) >>
    fs [] >>
    metis_tac []
)

val _ = export_theory ();
