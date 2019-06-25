(*
  Proves correctness of the linear-scan register allocator.
*)
open preamble sptreeTheory reg_allocTheory linear_scanTheory reg_allocProofTheory libTheory
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "linear_scanProof"

val _ = disable_tyabbrev_printing "type_ident"
val _ = disable_tyabbrev_printing "alist"

val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

(* TODO: clean up this file: e.g., move things upstream *)

Theorem set_MAP_FST_toAList_eq_domain:
     !s. set (MAP FST (toAList s)) = domain s
Proof
    rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup]
QED

Theorem numset_list_insert_FOLDL:
     !l live. numset_list_insert l live = FOLDL (\live x. insert x () live) live l
Proof
    Induct_on `l` >> rw [numset_list_insert_def]
QED

Theorem numset_list_insert_nottailrec_FOLDR:
     !l live. numset_list_insert_nottailrec l live = FOLDR (\x live. insert x () live) live l
Proof
    Induct_on `l` >> rw [numset_list_insert_nottailrec_def]
QED

Theorem both_numset_list_insert_equal:
     !l live.
    numset_list_insert l live = numset_list_insert_nottailrec (REVERSE l) live
Proof
    rw [numset_list_insert_FOLDL, numset_list_insert_nottailrec_FOLDR, FOLDR_FOLDL_REVERSE]
QED

Theorem domain_numset_list_insert:
     !l s.  domain (numset_list_insert l s) = set l UNION domain s
Proof
    Induct_on `l` >>
    rw [numset_list_insert_def] >>
    metis_tac [numset_list_insert_def, INSERT_UNION_EQ, UNION_COMM]
QED

(* why breaking encapsulation like this? To get rid of the assumption `wf s` *)
Theorem lookup_insert_id:
     !x (y:unit) s. lookup x s = SOME () ==> s = insert x () s
Proof
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
QED

Theorem numset_list_insert_FILTER:
    !l live.
    numset_list_insert (FILTER (λx. lookup x live = NONE) l) live =
    numset_list_insert l live
Proof
    sg `!x l live. lookup x live = SOME () ==> lookup x (numset_list_insert_nottailrec l live) = SOME ()` THEN1 (
        Induct_on `l` >>
        rw [numset_list_insert_nottailrec_def, lookup_insert]
    ) >>
    rw [both_numset_list_insert_equal, GSYM FILTER_REVERSE] >>
    qabbrev_tac `l' = REVERSE l` >>
    qpat_x_assum `Abbrev _` kall_tac >>
    Induct_on `l'` >>
    rw [numset_list_insert_nottailrec_def] >>
    Cases_on `lookup h live` >> fs [NOT_SOME_NONE] >>
    simp [lookup_insert_id]
QED

Theorem domain_numset_list_delete:
     !l s.  domain (numset_list_delete l s) = (domain s) DIFF (set l)
Proof
    Induct_on `l` >>
    rw [numset_list_delete_def, DIFF_INSERT]
QED

Theorem check_partial_col_success_INJ_lemma:
     !l live flive f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_partial_col f l live flive = SOME (live',flive')
    ==>
    INJ f (set l UNION domain live) UNIV
Proof
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
QED

Theorem check_partial_col_success_INJ:
      !l live flive f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_partial_col f l live flive = SOME (live',flive')
    ==>
    INJ f (set l UNION domain live) UNIV /\
    INJ f (domain live') UNIV
Proof
    rw [] >>
    `domain live' = set l UNION domain live` by metis_tac [check_partial_col_domain, FST] >>
    metis_tac [check_partial_col_success_INJ_lemma]
QED

Theorem check_partial_col_input_monotone:
     !f live1 flive1 live2 flive2 l v.
    IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 ==>
    domain live1 SUBSET domain live2 ==>
    INJ f (domain live2) UNIV ==>
    check_partial_col f l live2 flive2 = SOME v ==>
    ?livein1 flivein1. check_partial_col f l live1 flive1 = SOME (livein1, flivein1)
Proof
    rw [] >>
    PairCases_on `v` >>
    `INJ f (set l UNION domain live2) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `set l UNION domain live1 SUBSET set l UNION domain live2` by fs [SUBSET_DEF] >>
    `INJ f (set l UNION domain live1) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
    metis_tac [check_partial_col_success]
QED

Theorem numset_list_delete_IMAGE:
     !f l live flive v.
    domain flive = IMAGE f (domain live) ==>
    INJ f (domain live) UNIV ==>
    check_partial_col f l live flive = SOME v ==>
    domain (numset_list_delete (MAP f l) flive) = IMAGE f (domain (numset_list_delete l live))
Proof
    rw [] >>
    PairCases_on `v` >>
    `INJ f (set l UNION domain live) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    rw [domain_numset_list_delete, EXTENSION] >>
    eq_tac >> strip_tac
    THEN1 (
        fs [MEM_MAP] >>
        metis_tac []
    )
    THEN1 (
        strip_tac
        THEN1 metis_tac [] >>
        CCONTR_TAC >> fs [MEM_MAP, INJ_IFF] >>
        metis_tac []
    )
QED

Theorem check_partial_col_IMAGE:
      !f l live flive live' flive'.
    (domain flive) = IMAGE f (domain live) ==>
    check_partial_col f l live flive = SOME (live', flive') ==>
    (domain flive') = IMAGE f (domain live')
Proof
    Induct_on `l` >>
    fs [check_partial_col_def] >> rw [] >>
    Cases_on`lookup h live` >>
    Cases_on`lookup (f h) flive` >>
    fs [] >>
    `domain (insert (f h) () flive) = IMAGE f (domain (insert h () live))` by rw [domain_insert] >>
    metis_tac []
QED

Theorem branch_domain:
      !(live1 : num_set) (live2 : num_set).
    set (MAP FST (toAList (difference live2 live1))) UNION domain live1 = domain live1 UNION domain live2
Proof
    `!(live1 : num_set) (live2 : num_set). set (MAP FST (toAList (difference live2 live1))) = domain (difference live2 live1)` by rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup] >>
    `!(s : num -> bool) (t : num -> bool). t DIFF s UNION s = s UNION t` by (rw [EXTENSION] >> Cases_on `x IN t` >> rw []) >>
    rw [domain_difference]
QED

Theorem check_partial_col_branch_domain:
      !(live1 : num_set) (live2 : num_set) flive1 liveout fliveout.
    check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 = SOME (liveout, fliveout) ==>
    domain liveout = domain live1 UNION domain live2
Proof
    metis_tac [branch_domain, check_partial_col_domain, FST]
QED


Theorem check_partial_col_branch_comm:
     !f live1 flive1 live2 flive2 a b.
    INJ f (domain live1) UNIV ==>
    domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) ==>
    check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 = SOME (a, b) ==>
    ?c d. check_partial_col f (MAP FST (toAList (difference live1 live2))) live2 flive2 = SOME (c, d)
Proof
    rw [] >>
    `domain a = domain live1 UNION domain live2` by metis_tac [check_partial_col_domain, branch_domain, FST] >>
    `INJ f (domain live1 UNION domain live2) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `set (MAP FST (toAList (difference live1 live2))) UNION domain live2 = domain live1 UNION domain live2` by metis_tac [UNION_COMM, domain_difference, branch_domain] >>
    metis_tac [check_partial_col_success]
QED

Theorem check_partial_col_list_monotone:
     !f live flive (s1 : num_set) (s2 : num_set) a b.
    domain flive = IMAGE f (domain live) ==>
    INJ f (domain live) UNIV ==>
    domain s1 SUBSET domain s2 ==>
    check_partial_col f (MAP FST (toAList s2)) live flive= SOME (a, b) ==>
    ?c d. check_partial_col f (MAP FST (toAList s1)) live flive = SOME (c, d)
Proof
    rw [] >>
    `!(s : num_set). set (MAP FST (toAList s)) = domain s` by rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup] >>
    `INJ f (domain a) UNIV` by metis_tac [check_partial_col_success_INJ] >>
    `domain a = (domain s2 UNION domain live)` by metis_tac [check_partial_col_domain, FST] >>
    `domain s1 UNION domain live SUBSET domain a` by fs [SUBSET_DEF] >>
    `INJ f (domain s1 UNION domain live) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
    metis_tac [check_partial_col_success]
QED

Theorem check_live_tree_success:
      !lt live flive live' flive' f.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_live_tree f lt live flive = SOME (live',flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV
Proof
    Induct_on `lt`

    (* Writes *)
    THEN1 (
      rw [check_live_tree_def] >>
      fs [case_eq_thms]
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
      THEN1 metis_tac [check_partial_col_IMAGE]
      THEN1 metis_tac [check_partial_col_success_INJ]
    )
    (* Branch *)
    THEN1 (
      rw [check_live_tree_def] >>
      fs [case_eq_thms] >> rveq
      THEN1 (
        metis_tac [check_partial_col_IMAGE]
      )
      THEN1 (
        `INJ f (domain livein1) UNIV` by metis_tac [] >>
        `domain flivein1 = IMAGE f (domain livein1)` by metis_tac [check_partial_col_IMAGE] >>
        metis_tac [check_partial_col_success_INJ]
      )
    )
    (* Seq *)
    THEN1 (
      rw [check_live_tree_def] >>
      fs [case_eq_thms] >> rveq >>
      `domain flivein2 = IMAGE f (domain livein2)` by metis_tac [] >>
      `INJ f (domain livein2) UNIV` by metis_tac [] >>
      metis_tac []
    )
QED

Theorem ALL_DISTINCT_INJ_MAP:
     !f l. ALL_DISTINCT (MAP f l) ==> INJ f (set l) UNIV
Proof
    Induct_on `l` >> rw [INJ_INSERT] >>
    `MEM (f y) (MAP f l)` by metis_tac [MEM_MAP] >>
    `~(MEM (f y) (MAP f l))` by metis_tac []
QED

Theorem check_col_output:
     !f live live' flive'.
    check_col f live = SOME (live', flive') ==>
    domain flive' = IMAGE f (domain live') /\
    INJ f (domain live') UNIV
Proof
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
QED

Theorem check_col_success:
     !f live.
    INJ f (domain live) UNIV ==>
    ?flive. check_col f live = SOME (live, flive)
Proof
    rw [check_col_def] >>
    sg `!x y. MEM x (MAP FST (toAList live)) /\ MEM y (MAP FST (toAList live)) /\ (f x = f y) ==> (x = y)` THEN1 (
        rw [MEM_toAList, MEM_MAP, EXISTS_PROD] >>
        `x IN domain live /\ y IN domain live` by rw [domain_lookup] >>
        fs [INJ_DEF]
    ) >>
    metis_tac [ALL_DISTINCT_MAP_INJ, MAP_MAP_o, ALL_DISTINCT_MAP_FST_toAList]
QED

Theorem check_clash_tree_output:
      !f ct live flive livein flivein.
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV /\
    check_clash_tree f ct live flive = SOME (livein, flivein) ==>
    domain flivein = IMAGE f (domain livein) /\
    INJ f (domain livein) UNIV
Proof
    Induct_on `ct` >>
    simp [check_clash_tree_def]

    (* Delta *)
    THEN1 (
      rpt gen_tac >> strip_tac >>
      fs [case_eq_thms] >>
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
        fs [case_eq_thms] >> rveq
        THEN1 (
            `domain ft1_out = IMAGE f (domain t1_out)` by metis_tac [check_partial_col_IMAGE] >>
            `INJ f (domain t1_out) UNIV` by metis_tac [check_partial_col_success_INJ] >>
            strip_tac
            THEN1 metis_tac [check_partial_col_IMAGE]
            THEN1 metis_tac [check_partial_col_success_INJ]

        )
        THEN1 metis_tac [check_col_output]
    )
    (* Seq *)
    THEN1 (
        rpt gen_tac >> strip_tac >>
        fs [case_eq_thms] >> rveq >>
        `domain ft2_out = IMAGE f (domain t2_out) /\ INJ f (domain t2_out) UNIV` by metis_tac [] >>
        metis_tac []
    )
QED

Theorem get_live_tree_correct_lemma:
     !f live flive live' flive' ct livein' flivein'.
    IMAGE f (domain live) = domain flive /\ IMAGE f (domain live') = domain flive' ==>
    INJ f (domain live') UNIV ==>
    domain live SUBSET domain live' ==>
    check_live_tree f (get_live_tree ct) live' flive' = SOME (livein', flivein') ==>
    ?livein flivein. check_clash_tree f ct live flive = SOME (livein, flivein) /\
    domain livein SUBSET domain livein'
Proof
    Induct_on `ct`

    (* Delta *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        qabbrev_tac `lrd = l0` >> qabbrev_tac `lwr = l` >> rpt (qpat_x_assum `Abbrev _` kall_tac) >>
        fs [case_eq_thms] >> rveq >>
        `?v. check_partial_col f lwr live flive = SOME v` by metis_tac [check_partial_col_input_monotone] >>
        rw [] >>
        `INJ f (domain live) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
        `IMAGE f (domain (numset_list_delete lwr live)) = domain (numset_list_delete (MAP f lwr) flive)` by metis_tac [numset_list_delete_IMAGE] >>
        `IMAGE f (domain (numset_list_delete lwr live')) = domain (numset_list_delete (MAP f lwr) flive')` by metis_tac [numset_list_delete_IMAGE] >>
        sg `INJ f (domain (numset_list_delete lwr live')) UNIV` THEN1 (
          rw [domain_numset_list_delete] >>
          `(domain live' DIFF set lwr) SUBSET (domain live')` by fs [SUBSET_DIFF] >>
          metis_tac [SUBSET_DIFF, INJ_SUBSET, UNIV_SUBSET]
        ) >>
        `domain (numset_list_delete lwr live) SUBSET domain (numset_list_delete lwr live')` by fs [domain_numset_list_delete, SUBSET_DEF] >>
        `?live1' flive1'. check_partial_col f lrd (numset_list_delete lwr live) (numset_list_delete (MAP f lwr) flive) = SOME (live1', flive1')` by metis_tac [check_partial_col_input_monotone] >>
        rw [] >>
        imp_res_tac check_partial_col_domain >>
        fs [] >> fs [domain_numset_list_delete, SUBSET_DEF]
    )

    (* Set *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        imp_res_tac check_partial_col_domain >> fs [] >>
        imp_res_tac check_partial_col_success_INJ >> rfs [] >>
        `set (MAP FST (toAList s)) = domain s` by rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
        fs [] >>
        `domain s SUBSET domain s UNION domain live'` by fs [] >>
        `INJ f (domain s) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
        `?livein flivein. check_col f s = SOME (livein, flivein)` by metis_tac [check_col_success] >>
        rw [] >>
        fs [check_col_def]
    )

    (* Branch *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        Cases_on `o'` >> fs [check_live_tree_def] >>
        fs [case_eq_thms] >> rveq >>
        (* Try to get consistent names *)
        TRY (
          qabbrev_tac `cutset = x` >>
          qabbrev_tac `livemid = livein2'` >> qabbrev_tac `flivemid = flivein2'` >>
          rpt (qpat_x_assum `Abbrev _` kall_tac)
        ) >>
        qabbrev_tac `livein1' = livein1` >> qabbrev_tac `flivein1' = flivein1` >>
        qabbrev_tac `livein2' = livein2` >> qabbrev_tac `flivein2' = flivein2` >>
        rpt (qpat_x_assum `Abbrev _` kall_tac) >>
        `?livein1 flivein1. check_clash_tree f ct live flive = SOME (livein1, flivein1) /\ domain livein1 SUBSET domain livein1'` by metis_tac [] >>
        `?livein2 flivein2. check_clash_tree f ct' live flive = SOME (livein2, flivein2) /\ domain livein2 SUBSET domain livein2'` by metis_tac [] >>
        rw []
        THEN1 (
            imp_res_tac check_live_tree_success >> rfs [] >>
            `INJ f (set (MAP FST (toAList (difference livein2' livein1')))
             UNION domain livein1') UNIV` by
                metis_tac [check_partial_col_success_INJ] >>
            `set (MAP FST (toAList (difference livein2 livein1)))
             UNION domain livein1 SUBSET set
               (MAP FST (toAList (difference livein2' livein1')))
             UNION domain livein1'` by
               (REWRITE_TAC [branch_domain] >> fs [SUBSET_DEF]) >>
            `INJ f (set (MAP FST (toAList (difference livein2 livein1)))
             UNION domain livein1) UNIV` by
               metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
            `INJ f (domain live) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
            `domain flivein1 = IMAGE f (domain livein1)` by
               metis_tac [check_clash_tree_output] >>
            `?livein flivein. check_partial_col f
               (MAP FST (toAList (difference livein2 livein1)))
                 livein1 flivein1 = SOME (livein, flivein)` by
                    metis_tac [check_partial_col_success] >>
            rw [] >>
            `domain livein = set (MAP FST (toAList (difference livein2 livein1))) UNION domain livein1` by metis_tac [check_partial_col_domain, FST] >>
            `domain livein' = set (MAP FST (toAList (difference livein2' livein1'))) UNION domain livein1'` by metis_tac [check_partial_col_domain, FST] >>
            fs []
        )
        THEN1 (
            `domain flivein1' = IMAGE f (domain livein1') /\ INJ f (domain livein1') UNIV` by metis_tac [check_live_tree_success] >>
            `domain flivein2' = IMAGE f (domain livein2') /\ INJ f (domain livein2') UNIV` by metis_tac [check_live_tree_success] >>
            `domain flivemid = IMAGE f (domain livemid) /\ INJ f (domain livemid) UNIV` by metis_tac [check_partial_col_success_INJ, check_partial_col_IMAGE] >>
            `INJ f (domain livein') UNIV` by metis_tac [check_partial_col_success_INJ] >>
            `domain livein' = set (MAP FST (toAList cutset)) UNION domain livemid` by metis_tac [check_partial_col_domain, FST] >>
            `set (MAP FST (toAList cutset)) = domain cutset` by rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
            `domain cutset SUBSET domain livein'` by fs [] >>
            `INJ f (domain cutset) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
            `?livein flivein. check_col f cutset = SOME (livein, flivein)` by metis_tac [check_col_success] >>
            rw [] >>
            fs [check_col_def]
        )
    )

    (* Seq *)
    THEN1 (
        rw [check_clash_tree_def, get_live_tree_def, check_live_tree_def] >>
        fs [case_eq_thms] >> rveq >>
        `?t2_out ft2_out. check_clash_tree f ct' live flive = SOME (t2_out, ft2_out) /\ domain t2_out SUBSET domain livein2` by metis_tac [] >>
        `INJ f (domain live) UNIV` by metis_tac [INJ_SUBSET, UNIV_SUBSET] >>
        `IMAGE f (domain t2_out) = domain ft2_out` by metis_tac [check_clash_tree_output] >>
        simp [] >>
        `IMAGE f (domain livein2) = domain flivein2` by metis_tac [check_live_tree_success] >>
        `INJ f (domain livein2) UNIV` by metis_tac [check_live_tree_success] >>
        metis_tac []
    )
QED

Theorem get_live_tree_correct:
     !f live flive ct livein flivein.
    IMAGE f (domain live) = domain flive ==>
    INJ f (domain live) UNIV ==>
    check_live_tree f (get_live_tree ct) live flive = SOME (livein, flivein) ==>
    ?livein' flivein'. check_clash_tree f ct live flive = SOME (livein', flivein')
Proof
    metis_tac [get_live_tree_correct_lemma, SUBSET_REFL]
QED

Theorem get_live_tree_correct_LN:
     !f ct livein flivein.
    check_live_tree f (get_live_tree ct) LN LN = SOME (livein, flivein) ==>
    ?livein' flivein'. check_clash_tree f ct LN LN = SOME (livein', flivein')
Proof
    rw [get_live_tree_correct]
QED

Theorem check_partial_col_numset_list_insert:
     !f l live flive liveout fliveout.
    check_partial_col f l live flive = SOME (liveout, fliveout) ==>
    liveout = numset_list_insert l live
Proof
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
QED

Theorem check_live_tree_eq_get_live_backward:
     !f lt live flive liveout fliveout.
    check_live_tree f lt live flive = SOME (liveout, fliveout) ==>
    liveout = get_live_backward lt live
Proof
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
QED

Theorem fix_domination_fixes_domination:
     !lt. domain (get_live_backward (fix_domination lt) LN) = EMPTY
Proof
    rw [get_live_backward_def, fix_domination_def, domain_numset_list_delete] >>
    rw [EXTENSION, MEM_MAP, MEM_toAList, EXISTS_PROD, domain_lookup]
QED

Theorem fix_domination_check_live_tree:
     !f lt liveout fliveout.
    check_live_tree f (fix_domination lt) LN LN = SOME (liveout, fliveout) ==>
    ?liveout' fliveout'. check_live_tree f lt LN LN = SOME (liveout', fliveout')
Proof
    rw [check_live_tree_def, fix_domination_def] >>
    Cases_on `check_live_tree f lt LN LN` >> fs [] >>
    Cases_on `x` >> fs []
QED

Theorem size_of_live_tree_positive:
     !lt. 0 <= size_of_live_tree lt
Proof
    Induct_on `lt` >> rw [size_of_live_tree_def]
QED

Theorem check_number_property_strong_monotone_weak:
     !P Q lt n live.
    (!n' live'. P n' live' ==> Q n' live') /\
    check_number_property_strong P lt n live ==>
    check_number_property_strong Q lt n live
Proof
    Induct_on `lt` >>
    rw [check_number_property_strong_def] >>
    res_tac >> simp []
QED


Theorem check_number_property_strong_monotone:
     !P Q lt n live.
    (!n' live'. (n - size_of_live_tree lt) <= n' /\ P n' live' ==> Q n' live') /\
    check_number_property_strong P lt n live ==>
    check_number_property_strong Q lt n live
Proof
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
QED

Theorem check_number_property_strong_end:
     !P lt n live.
    check_number_property_strong P lt n live ==>
    P (n - size_of_live_tree lt) (get_live_backward lt live)
Proof
    Induct_on `lt` >>
    rw [check_number_property_strong_def, get_live_backward_def, size_of_live_tree_def] >>
    (* Seq *)
    res_tac >>
    `n - size_of_live_tree lt' - size_of_live_tree lt = n - (size_of_live_tree lt + size_of_live_tree lt')` by intLib.COOPER_TAC >>
    metis_tac []
QED

Theorem check_number_property_monotone_weak:
     !P Q lt n live.
    (!n' live'. P n' live' ==> Q n' live') /\
    check_number_property P lt n live ==>
    check_number_property Q lt n live
Proof
    Induct_on `lt` >>
    rw [check_number_property_def] >>
    res_tac >> simp []
QED


Theorem lookup_numset_list_add_if:
     !r l v s.
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
Proof
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
QED


Theorem lookup_numset_list_add_if_lt:
     !r l v s.
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
Proof
    simp [numset_list_add_if_lt_def] >>
    rw [lookup_numset_list_add_if]
QED

Theorem lookup_numset_list_add_if_gt:
     !r l v s.
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
Proof
    simp [numset_list_add_if_gt_def] >>
    rw [lookup_numset_list_add_if]
QED

Theorem domain_numset_list_add_if:
     !l v s P. domain (numset_list_add_if l v s P) = set l UNION domain s
Proof
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
QED

Theorem domain_numset_list_add_if_lt:
     !l v s. domain (numset_list_add_if_lt l v s) = set l UNION domain s
Proof
    rw [numset_list_add_if_lt_def, domain_numset_list_add_if]
QED

Theorem domain_numset_list_add_if_gt:
     !l v s. domain (numset_list_add_if_gt l v s) = set l UNION domain s
Proof
    rw [numset_list_add_if_gt_def, domain_numset_list_add_if]
QED

Theorem lookup_numset_list_delete:
     !l s x. lookup x (numset_list_delete l s) = if MEM x l then NONE else lookup x s
Proof
    Induct_on `l` >>
    rw [numset_list_delete_def, lookup_delete] >>
    fs []
QED

Theorem get_intervals_nout:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    n_out = n_in - (size_of_live_tree lt)
Proof
    Induct_on `lt` >>
    rw [get_intervals_def, size_of_live_tree_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n_out = n2 - (size_of_live_tree lt)` by metis_tac [] >>
    `n2 = n_in - (size_of_live_tree lt')` by metis_tac [] >>
    intLib.COOPER_TAC
QED

Theorem get_intervals_withlive_nout:
     !lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live ==>
    n_out = n_in - (size_of_live_tree lt)
Proof
    Induct_on `lt` >>
    rw [get_intervals_withlive_def, size_of_live_tree_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n_out = n2 - (size_of_live_tree lt)` by metis_tac [] >>
    `n2 = n_in - (size_of_live_tree lt')` by metis_tac [] >>
    rveq >> intLib.COOPER_TAC
QED


Theorem get_intervals_intend_augment:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    !r v. lookup r end_in = SOME v ==> (?v'. lookup r end_out = SOME v' /\ v <= v')
Proof
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
QED

Theorem check_number_property_intend:
     !end_out lt n_in live_in.
    check_number_property (\n (live : num_set). !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live_in ==>
    !r. r IN domain (get_live_backward lt live_in) ==> ?v. lookup r end_out = SOME v /\ n_in-(size_of_live_tree lt) <= v
Proof
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
QED

Theorem get_intervals_live_less_end:
     !lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r. r IN domain live_in ==> ?v. lookup r end_in = SOME v /\ n_in <= v) ==>
    check_number_property (\n (live : num_set). !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live_in
Proof
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
        sg `!n' (live' : num_set). (\n live. !r. r IN domain live ==>
            ?v. lookup r int_end2 = SOME v /\ n+1 <= v) n' live' ==>
            (\n live. !r. r IN domain live ==>
            ?v. lookup r end_out = SOME v /\ n+1 <= v) n' live'` THEN1 (
            rw [] >>
            `?v. lookup r int_end2 = SOME v /\ n'+1 <= v` by rw [] >>
            `?v'. lookup r end_out = SOME v' /\ v <= v'` by metis_tac [get_intervals_intend_augment] >>
            rw [] >> intLib.COOPER_TAC
        ) >>
        qspecl_then [`\n live. !r. r IN domain live ==> ?v. lookup r int_end2 = SOME v /\ n+1 <= v`,
          `\n live. !r. r IN domain live ==> ?v. lookup r end_out = SOME v /\ n+1 <= v`, `lt'`, `n_in`, `live_in`]
          assume_tac check_number_property_monotone_weak >>
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
QED

Theorem get_intervals_withlive_intbeg_reduce:
     !lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)
Proof
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
      `(!r. option_CASE (lookup r int_beg1) n1 (\x.x) <=
            option_CASE (lookup r (difference int_beg2 live)) n2 (\x.x)) /\
       (!r v. lookup r (difference int_beg2 live) = SOME v ==> n2 <= v) /\
       (!r v. lookup r int_beg1 = SOME v ==> n1 <= v)` by
         (res_tac >> metis_tac []) >>
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
          rfs [] >> fs [set_MAP_FST_toAList_eq_domain] >> rw [] >>
          rpt (qpat_x_assum `lookup _ _ = _` kall_tac) >>
          intLib.COOPER_TAC
      )
      THEN1 res_tac
    )
    (* Seq*)
    THEN1 (
      rpt (pairarg_tac >> fs []) >>
      `(!r. option_CASE (lookup r int_beg2) n2 (\x.x) <=
            option_CASE (lookup r beg_in) n_in (\x.x)) /\
       (!r v. lookup r beg_in = SOME v ==> n_in <= v) /\
       (!r v. lookup r int_beg2 = SOME v ==> n2 <= v)` by
           (res_tac >> metis_tac []) >>
      `(!r. option_CASE (lookup r int_beg1) n1 (\x.x) <=
            option_CASE (lookup r int_beg2) n2 (\x.x)) /\
       (!r v. lookup r int_beg2 = SOME v ==> n2 <= v) /\
       (!r v. lookup r int_beg1 = SOME v ==> n1 <= v)` by
         (res_tac >> metis_tac []) >>
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
QED

Theorem get_intervals_withlive_intbeg_nout:
     !lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)
Proof
    metis_tac [get_intervals_withlive_intbeg_reduce]
QED

Theorem get_intervals_intbeg_nout:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)
Proof
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
QED


Theorem get_intervals_withlive_live_intbeg:
     !lt n_in beg_in end_in live n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
    (!r. r IN domain live ==> r NOTIN domain beg_in) ==>
    (!r. r IN domain (get_live_backward lt live) ==> r NOTIN domain beg_out)
Proof
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
QED

Theorem get_intervals_withlive_beg_less_live:
     !lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) /\
    (!r. r IN domain live_in ==> r NOTIN domain beg_in) ==>
    check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) lt n_in live_in
Proof
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
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') - size_of_live_tree lt <= n /\
              (!r. r IN domain live ==> option_CASE (lookup r int_beg1)
                (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n) ==>
              (!r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
            rw [lookup_difference] >>
            rpt CASE_TAC >>
            first_x_assum (qspec_then `r` assume_tac) >>
            rfs [] >> intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==>
              option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`,
            `\n live. !r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union))
                 (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `lt`, `n_in - size_of_live_tree lt'`, `live_in`]
              assume_tac check_number_property_strong_monotone >>
          metis_tac []
        )
        THEN1 (
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') <= n /\ (!r. r IN domain live ==>
                 option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n) ==>
               (!r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union)) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
            rw [lookup_difference] >>
            rpt CASE_TAC
            THEN1 intLib.COOPER_TAC
            THEN1 (
              `!r. option_CASE (lookup r int_beg1) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <=
                   option_CASE (lookup r (difference int_beg2 live_in)) (n_in - size_of_live_tree lt') (\x.x)` by metis_tac [get_intervals_withlive_intbeg_reduce] >>
              rpt (last_x_assum (qspec_then `r` assume_tac)) >>
              rfs [lookup_difference] >>
              Cases_on `lookup r live_in` >> fs []
              THEN1 intLib.COOPER_TAC >>
              Cases_on `lookup r int_beg2` >> fs [] >>
              intLib.COOPER_TAC
            )
            THEN1 intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n`,
                       `\n live. !r. r IN domain live ==> option_CASE (lookup r (difference int_beg1 set_union))
            (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`, `lt'`, `n_in`, `live_in`] assume_tac check_number_property_strong_monotone >>
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
          sg `!n (live : num_set). (n_in - size_of_live_tree lt') <= n /\ (!r. r IN domain live ==>
                 option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x) <= n) ==>
               (!r. r IN domain live ==> option_CASE (lookup r int_beg1)
                   (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n)` THEN1 (
              rw [] >>
              `!r. option_CASE (lookup r beg_out) (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <=
                   option_CASE (lookup r int_beg2) (n_in - size_of_live_tree lt') (\x.x)` by metis_tac [get_intervals_withlive_intbeg_reduce] >>
              rpt (last_x_assum (qspec_then `r` assume_tac)) >> rfs [] >>
              Cases_on `lookup r beg_out` >> fs []
              THEN1 intLib.COOPER_TAC >>
              Cases_on `lookup r int_beg2` >> rfs [] >>
              intLib.COOPER_TAC
          ) >>
          qspecl_then [`\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg2)
                             (n_in - size_of_live_tree lt') (\x.x) <= n`,
                       `\n live. !r. r IN domain live ==> option_CASE (lookup r int_beg1)
                             (n_in - size_of_live_tree lt' - size_of_live_tree lt) (\x.x) <= n`,
                       `lt'`, `n_in`, `live_in`] assume_tac check_number_property_strong_monotone >>
          metis_tac []
        )
    )
QED

Theorem get_intervals_withlive_n_eq_get_intervals_n:
     !lt n beg end beg' end' n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end' live ==>
    n1 = n2
Proof
    Induct_on `lt` >>
    rw [get_intervals_def, get_intervals_withlive_def] >>
    rpt (pairarg_tac >> fs []) >>
    metis_tac []
QED

Theorem get_intervals_withlive_end_eq_get_intervals_end:
     !lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end live ==>
    end1 = end2
Proof
    Induct_on `lt` >>
    rw [get_intervals_def, get_intervals_withlive_def] >>
    rpt (pairarg_tac >> fs []) >>
    `n2' = n2''` by metis_tac [get_intervals_withlive_n_eq_get_intervals_n] >> rveq >>
    metis_tac []
QED

Theorem get_intervals_withlive_beg_eq_get_intervals_beg_when_some:
     !lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
    (n1, beg1, end1) = get_intervals lt n beg end /\
    (n2, beg2, end2) = get_intervals_withlive lt n beg' end live /\
    (!r v. lookup r beg = SOME v ==> n <= v) /\
    (!r v. lookup r beg' = SOME v ==> n <= v) /\
    (!r v1 v2. lookup r beg = SOME v1 /\ lookup r beg' = SOME v2 ==> v1 = v2)
    ==>
    !r v1 v2. lookup r beg1 = SOME v1 /\ lookup r beg2 = SOME v2 ==> v1 = v2
Proof
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
QED

Theorem get_intervals_withlive_beg_subset_get_intervals_beg:
     !lt n beg_in1 beg_in2 end n1 beg_out1 end1 n2 beg_out2 end2 live.
    (n1, beg_out1, end1) = get_intervals_withlive lt n beg_in1 end live /\
    (n2, beg_out2, end2) = get_intervals lt n beg_in2 end /\
    domain beg_in1 SUBSET domain beg_in2 ==>
    domain beg_out1 SUBSET domain beg_out2
Proof
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
QED

Theorem get_intervals_beg_subset_registers:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    domain beg_out SUBSET (domain beg_in UNION (live_tree_registers lt))
Proof
    Induct_on `lt` >>
    rw [get_intervals_def, live_tree_registers_def]
    THEN1 rw [domain_numset_list_add_if_lt]
    >>
    rpt (pairarg_tac >> fs []) >>
    `domain int_beg2 SUBSET (domain beg_in UNION (live_tree_registers lt'))` by metis_tac [] >>
    `domain beg_out SUBSET (domain int_beg2 UNION (live_tree_registers lt))` by metis_tac [] >>
    fs [SUBSET_DEF] >>
    metis_tac []
QED

(* This theorem looks like lipschitz continuity: it says something like f(x+y) <= f(x)+y *)
Theorem get_intervals_withlive_beg_lipschitz:
     !lt n1 beg1 end1 live n2 beg2 end2 (s : int num_map) nout1 begout1 endout1 nout2 begout2 endout2.
    (nout1, begout1, endout1) = get_intervals_withlive lt n1 beg1 end1 live /\
    (nout2, begout2, endout2) = get_intervals_withlive lt n2 beg2 end2 live /\
    domain beg2 SUBSET domain beg1 UNION domain s ==>
    domain begout2 SUBSET domain begout1 UNION domain s
Proof
    Induct_on `lt` >>
    rw [get_intervals_withlive_def]
    (* Writes *)
    THEN1 (
        fs [SUBSET_DEF] >>
        rw [domain_numset_list_add_if_lt, domain_union] >>
        metis_tac []
    )
    (* Reads *)
    THEN1 (
        fs [SUBSET_DEF] >>
        rw [domain_numset_list_delete, domain_union]
    )
    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain int_beg2 SUBSET domain int_beg2' UNION domain s` by metis_tac [] >>
        `domain (difference int_beg2 live) SUBSET domain (difference int_beg2' live) UNION domain s` by fs [domain_difference, SUBSET_DEF] >>
        `domain int_beg1 SUBSET domain int_beg1' UNION domain s` by metis_tac [] >>
        fs [domain_difference, SUBSET_DEF]
    )
    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain int_beg2 SUBSET domain int_beg2' UNION domain s` by metis_tac [] >>
        metis_tac []
    )
QED

Theorem get_intervals_withlive_registers_subset_beg:
     !lt n_in beg_in end_in n_out beg_out end_out live_in.
    domain end_in SUBSET domain beg_in UNION domain live_in /\
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in ==>
    domain end_out SUBSET domain beg_out UNION domain (get_live_backward lt live_in)
Proof
    Induct_on `lt` >>
    rw [get_intervals_withlive_def, get_live_backward_def]

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
        sg `?(live_typed : int num_map). domain (get_live_backward lt' live_in) = domain live_typed` THEN1 (
          qexists_tac `map (K 0) (get_live_backward lt' live_in)` >>
          simp [domain_map]
        ) >>
        fs [] >>
        sg `?n1' int_beg1' int_end1'. (n1', int_beg1', int_end1') = get_intervals_withlive lt n2 (union (difference int_beg2 live_in) live_typed) int_end2 live_in` THEN1 (
            `?x. x = get_intervals_withlive lt n2 (union (difference int_beg2 live_in) live_typed) int_end2 live_in` by rw [] >>
            PairCases_on `x` >>
            metis_tac []
        ) >>
        `int_end1' = int_end1` by (`?x. x = get_intervals lt n2 LN int_end2` by rw [] >> PairCases_on `x` >> metis_tac [get_intervals_withlive_end_eq_get_intervals_end]) >>
        rveq >>
        sg `domain int_end2 SUBSET domain (union (difference int_beg2 live_in) live_typed) UNION domain live_in` THEN1 (
            fs [domain_union, domain_difference, SUBSET_DEF] >>
            metis_tac []
        ) >>
        `domain end_out SUBSET domain int_beg1' UNION domain (get_live_backward lt live_in)` by metis_tac [] >>
        sg `domain int_beg1' SUBSET domain int_beg1 UNION domain live_typed` THEN1 (
            `domain (union (difference int_beg2 live_in) live_typed) SUBSET domain (difference int_beg2 live_in) UNION domain live_typed` by simp [domain_union] >>
            metis_tac [get_intervals_withlive_beg_lipschitz]
        ) >>
        simp [domain_difference, domain_union, domain_numset_list_insert, branch_domain] >>
        fs [SUBSET_DEF] >>
        metis_tac []
    )

    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain int_end2 SUBSET domain int_beg2 UNION domain (get_live_backward lt' live_in)` by metis_tac [] >>
        metis_tac []
    )
QED

Theorem get_intervals_withlive_live_tree_registers_subset_endout:
     !lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals_withlive lt n_in beg_in end_in live_in ==>
    domain end_in UNION live_tree_registers lt SUBSET domain end_out
Proof
    Induct_on `lt` >>
    simp [get_intervals_withlive_def, live_tree_registers_def] >>
    rpt (gen_tac ORELSE disch_tac)
    (* Writes *)
    THEN1 (
        fs [domain_numset_list_delete, domain_numset_list_add_if_gt, SUBSET_DEF]
    )
    (* Reads *)
    THEN1 (
        fs [domain_numset_list_insert, domain_numset_list_add_if_gt, SUBSET_DEF]
    )
    (* Branch *)
    THEN1 (
        rpt (pairarg_tac >> FULL_SIMP_TAC std_ss []) >>
        `domain end_in UNION live_tree_registers lt' SUBSET domain int_end2` by metis_tac [] >>
        `domain int_end2 UNION live_tree_registers lt SUBSET domain end_out` by metis_tac [] >>
        fs [SUBSET_DEF] >>
        rw []
    )
    (* Seq *)
    THEN1 (
        rpt (pairarg_tac >> FULL_SIMP_TAC std_ss []) >>
        `domain end_in UNION live_tree_registers lt' SUBSET domain int_end2` by metis_tac [] >>
        `domain int_end2 UNION live_tree_registers lt SUBSET domain int_end1` by metis_tac [] >>
        fs [SUBSET_DEF]
    )
QED

Theorem get_intervals_domain_eq_live_tree_registers:
     !lt n beg end.
    (n, beg, end) = get_intervals (fix_domination lt) 0 LN LN ==>
    domain beg = live_tree_registers (fix_domination lt) /\
    domain end = live_tree_registers (fix_domination lt)
Proof
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
QED

Theorem get_intervals_withlive_domain_eq_live_tree_registers:
     !lt n beg end.
    (n, beg, end) = get_intervals_withlive (fix_domination lt) 0 LN LN LN ==>
    domain beg = live_tree_registers (fix_domination lt) /\
    domain end = live_tree_registers (fix_domination lt)
Proof
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
QED

Theorem get_intervals_withlive_beg_eq_get_intervals_beg:
     !lt n beg end n' beg' end'.
    (n, beg, end) = get_intervals_withlive (fix_domination lt) 0 LN LN LN /\
    (n', beg', end') = get_intervals (fix_domination lt) 0 LN LN ==>
    !(r:num). lookup r beg = lookup r beg'
Proof
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
QED

Theorem get_intervals_end_increase:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    domain end_in SUBSET domain end_out
Proof
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
QED

Theorem check_number_property_subset_endout:
     !lt n_in beg_in end_in live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    domain live_in SUBSET domain end_in ==>
    check_number_property_strong (\n (live:num_set). domain live SUBSET domain end_out) lt n_in live_in
Proof
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
        imp_res_tac check_number_property_strong_end >> fs [] >>
        metis_tac []
    )
QED

Theorem get_intervals_beg_less_live:
     !lt live_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals (fix_domination lt) 0 LN LN ==>
    check_number_property_strong (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) (fix_domination lt) 0 LN
Proof
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
    `(\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) =
        (\n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out') n_out (\x.x) <= n)` by rw [EXTENSION] >>
    qabbrev_tac `P = \n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n` >>
    qabbrev_tac `Q = \n (live : num_set). !r. r IN domain live ==> option_CASE (lookup r beg_out') n_out (\x.x) <= n` >>
    rw []
QED

Theorem get_intervals_intbeg_reduce:
     !lt n_in beg_in end_in n_out beg_out end_out live.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    (!r. option_CASE (lookup r beg_out) n_out (\x.x) <= option_CASE (lookup r beg_in) n_in (\x.x)) /\
    (!r v. lookup r beg_out = SOME v ==> n_out <= v)
Proof
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
QED

Theorem check_startlive_prop_monotone:
     !lt beg ndef end beg' ndef' end' n_in.
    (!r. option_CASE (lookup r beg') ndef' (\x.x) <= option_CASE (lookup r beg) ndef (\x.x)) /\
    (!r v. lookup r end = SOME v ==> (?v'. lookup r end' = SOME v' /\ v <= v')) /\
    check_startlive_prop lt n_in beg end ndef ==>
    check_startlive_prop lt n_in beg' end' ndef'
Proof
    Induct_on `lt` >>
    rw [check_startlive_prop_def] >>
    (
      CASE_TAC ORELSE res_tac >>
      rpt (first_x_assum (qspec_then `r` assume_tac)) >>
      rfs [] >>
      intLib.COOPER_TAC
    )
QED

Theorem check_startlive_prop_augment_ndef:
     !lt n_in beg_out end_out ndef.
    check_startlive_prop lt n_in beg_out end_out ndef /\
    ndef  <= ndef' /\
    ndef' <= n_in - size_of_live_tree lt==>
    check_startlive_prop lt n_in beg_out end_out ndef'
Proof
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
QED

Theorem get_intervals_check_startlive_prop:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in /\
    (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
    check_startlive_prop lt n_in beg_out end_out n_out
Proof
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
QED

Theorem exists_point_inside_interval_interval_intersect:
     !l1 r1 l2 r2 v.
    point_inside_interval (l1, r1) v  /\ point_inside_interval (l2, r2) v ==>
    interval_intersect (l1, r1) (l2, r2)
Proof
    rw [point_inside_interval_def, interval_intersect_def] >>
    intLib.COOPER_TAC
QED

Theorem check_intervals_check_live_tree_lemma:
     !lt n_in beg_out end_out f live flive.
    check_startlive_prop lt n_in beg_out end_out (n_in - size_of_live_tree lt) /\
    check_number_property_strong (\n (live' : num_set). !r. r IN domain live' ==> option_CASE (lookup r beg_out) n_out (\x.x) <= n) lt n_in live  /\
    check_number_property (\n (live' : num_set). !r. r IN domain live' ==> ?v. lookup r end_out = SOME v /\ n+1 <= v) lt n_in live /\
    check_number_property_strong (\n (live' : num_set). domain live' SUBSET domain end_out) lt n_in live /\
    domain beg_out = domain end_out /\
    live_tree_registers lt SUBSET domain end_out /\
    check_intervals f beg_out end_out /\
    domain flive = IMAGE f (domain live) /\
    INJ f (domain live) UNIV ==>
    ?liveout fliveout. check_live_tree f lt live flive = SOME (liveout, fliveout)
Proof
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
        sg `!r. r IN domain (get_live_backward lt live) \/ r IN domain (get_live_backward lt' live) ==>
                point_inside_interval (THE (lookup r beg_out), THE (lookup r end_out)) (n_in - (size_of_live_tree lt + size_of_live_tree lt'))` THEN1 (
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
QED

Theorem check_intervals_check_live_tree:
     !lt n_out beg_out end_out f.
    (n_out, beg_out, end_out) = get_intervals (fix_domination lt) 0 LN LN /\
    check_intervals f beg_out end_out ==>
    ?liveout fliveout. check_live_tree f (fix_domination lt) LN LN = SOME (liveout, fliveout)
Proof
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
QED

Theorem get_intervals_ct_aux_live:
     !ct n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out.
    domain live_in = domain live_in' /\
    (n_out, beg_out, end_out, live_out) = get_intervals_ct_aux ct n_in beg_in end_in live_in ==>
    domain live_out = domain (get_live_backward (get_live_tree ct) live_in')
Proof
    Induct_on `ct` >>
    rw [get_live_backward_def, get_intervals_ct_aux_def, get_live_tree_def]
    THEN1 rw [domain_numset_list_insert, domain_numset_list_delete]
    THEN1 (
        rw [domain_numset_list_insert, branch_domain, domain_union] >>
        rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup]
    )
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `domain (get_live_backward (get_live_tree ct') live_in') = domain live2` by metis_tac [] >>
        `domain (get_live_backward (get_live_tree ct) live_in') = domain live1` by metis_tac [] >>
        CASE_TAC >> fs [] >>
        rw [get_live_backward_def, domain_numset_list_insert, branch_domain, domain_union] >>
        rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup]
    )
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        metis_tac []
    )
QED

Theorem get_intervals_ct_aux_int:
     !ct n_in beg_in end_in live_in n_out beg_out end_out live_out.
    (n_out, beg_out, end_out, live_out) = get_intervals_ct_aux ct n_in beg_in end_in live_in ==>
    (n_out, beg_out, end_out) = get_intervals (get_live_tree ct) n_in beg_in end_in
Proof
    Induct_on `ct` >>
    rw [get_intervals_ct_aux_def, get_live_tree_def, get_intervals_def]
    THEN1 intLib.COOPER_TAC
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        `get_intervals (get_live_tree ct') n_in beg_in end_in = (n2, int_beg2, int_end2)` by metis_tac [] >>
        `get_intervals (get_live_tree ct) n2 int_beg2 int_end2 = (n1, int_beg1, int_end1)` by metis_tac [] >>
        CASE_TAC >> fs [] >>
        rw [get_intervals_def]
    )
    THEN1 (
        rpt (pairarg_tac >> fs []) >>
        (* TODO generated names *)
        `get_intervals (get_live_tree ct') n_in beg_in end_in = (n2', int_beg2', int_end2')` by metis_tac [] >>
        fs [] >> rveq >>
        metis_tac []
    )
QED

Theorem get_intervals_ct_eq:
     !ct int_beg1 int_beg2 int_end1 int_end2 n1 n2.
    (n1, int_beg1, int_end1) = get_intervals_ct ct /\
    (n2, int_beg2, int_end2) = get_intervals (fix_domination (get_live_tree ct)) 0 LN LN ==>
    (!r. lookup r int_beg1 = lookup r int_beg2) /\
    (!r. lookup r int_end1 = lookup r int_end2)
Proof
    simp [get_intervals_def, fix_domination_def, get_intervals_ct_def] >>
    rpt gen_tac >> strip_tac >>
    rpt (pairarg_tac >> fs []) >>
    `get_intervals (get_live_tree ct) 0 LN LN = (n, int_beg, int_end)` by metis_tac [get_intervals_ct_aux_int] >>
    `domain live = domain (get_live_backward (get_live_tree ct) LN)` by metis_tac [get_intervals_ct_aux_live] >>
    Cases_on `get_live_backward (get_live_tree ct) LN = LN` >> fs [] >>
    fs [get_intervals_def] >>
    simp [lookup_numset_list_add_if_lt, lookup_numset_list_add_if_gt, set_MAP_FST_toAList_eq_domain]
QED

Theorem colors_sub_eqn[simp]:
    colors_sub n s =
  if n < LENGTH s.colors then
    (Success (EL n s.colors),s)
  else
    (Failure (Subscript),s)
Proof
  rw[colors_sub_def]>>
  fs[Marray_sub_def]
QED

Theorem update_colors_eqn[simp]:
    update_colors n t s =
  if n < LENGTH s.colors then
     (Success (),s with colors := LUPDATE t n s.colors)
  else
     (Failure (Subscript),s)
Proof
  rw[update_colors_def]>>
  fs[Marray_update_def]
QED

Theorem int_beg_sub_eqn[simp]:
   int_beg_sub n s =
  if n < LENGTH s.int_beg then
    (Success (EL n s.int_beg),s)
  else
    (Failure (Subscript),s)
Proof
  rw[int_beg_sub_def]>>
  fs[Marray_sub_def]
QED

Theorem update_int_beg_eqn[simp]:
   update_int_beg n t s =
  if n < LENGTH s.int_beg then
     (Success (),s with int_beg := LUPDATE t n s.int_beg)
  else
     (Failure (Subscript),s)
Proof
  rw[update_int_beg_def]>>
  fs[Marray_update_def]
QED

Theorem int_end_sub_eqn[simp]:
   int_end_sub n s =
  if n < LENGTH s.int_end then
    (Success (EL n s.int_end),s)
  else
    (Failure (Subscript),s)
Proof
  rw[int_end_sub_def]>>
  fs[Marray_sub_def]
QED

Theorem update_int_end_eqn[simp]:
   update_int_end n t s =
  if n < LENGTH s.int_end then
     (Success (),s with int_end := LUPDATE t n s.int_end)
  else
     (Failure (Subscript),s)
Proof
  rw[update_int_end_def]>>
  fs[Marray_update_def]
QED

Theorem sorted_regs_sub_eqn[simp]:
   sorted_regs_sub n s =
  if n < LENGTH s.sorted_regs then
    (Success (EL n s.sorted_regs),s)
  else
    (Failure (Subscript),s)
Proof
  rw[sorted_regs_sub_def]>>
  fs[Marray_sub_def]
QED

Theorem update_sorted_regs_eqn[simp]:
   update_sorted_regs n t s =
  if n < LENGTH s.sorted_regs then
     (Success (),s with sorted_regs := LUPDATE t n s.sorted_regs)
  else
     (Failure (Subscript),s)
Proof
  rw[update_sorted_regs_def]>>
  fs[Marray_update_def]
QED

Theorem sorted_moves_sub_eqn[simp]:
   sorted_moves_sub n s =
  if n < LENGTH s.sorted_moves then
    (Success (EL n s.sorted_moves),s)
  else
    (Failure (Subscript),s)
Proof
  rw[sorted_moves_sub_def]>>
  fs[Marray_sub_def]
QED

Theorem update_sorted_moves_eqn[simp]:
   update_sorted_moves n t s =
  if n < LENGTH s.sorted_moves then
     (Success (),s with sorted_moves := LUPDATE t n s.sorted_moves)
  else
     (Failure (Subscript),s)
Proof
  rw[update_sorted_moves_def]>>
  fs[Marray_update_def]
QED

val msimps = [st_ex_bind_def,st_ex_return_def];

val lookup_default_id_def = Define`
    lookup_default_id s x = option_CASE (lookup x s) x (\x.x)
`;

val find_reg_exchange_step_def = Define`
    find_reg_exchange_step colors r (exch, invexch) =
        let col1 = EL r colors in
        let fcol1 = r DIV 2 in
        let col2 = lookup_default_id invexch fcol1 in
        let fcol2 = lookup_default_id exch col1 in
        (insert col1 fcol1 (insert col2 fcol2 exch), insert fcol1 col1 (insert fcol2 col2 invexch))
`;

Theorem find_reg_exchange_FOLDL:
     !l colors exch invexch sth.
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    find_reg_exchange l exch invexch sth = (Success (FOLDL (\a b. find_reg_exchange_step sth.colors b a) (exch, invexch) l), sth)
Proof
    Induct_on `l` >>
    rw [FOLDL, find_reg_exchange_def, find_reg_exchange_step_def, lookup_default_id_def] >>
    rw msimps
QED

Theorem lookup_default_id_insert:
     !s k1 k2 v.
    lookup_default_id (insert k2 v s) k1 = if k1 = k2 then v else lookup_default_id s k1
Proof
    rw [lookup_default_id_def, lookup_insert]
QED

val id_def = Define `id x = x`

Theorem find_reg_exchange_FOLDR_correct:
     !l colors exch invexch k.
    ALL_DISTINCT (MAP (\r. EL r colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (exch, invexch) = FOLDR (\a b. find_reg_exchange_step colors a b) (LN, LN) l ==>
    ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.x) /\ (lookup_default_id invexch) o (lookup_default_id exch) = (\x.x)) /\
    (!r. MEM r l ==> lookup_default_id exch (EL r colors) = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r colors <=> k <= r DIV 2)) ==>
      (!c. id (k <= c <=> k <= lookup_default_id exch c))) /\
    ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!c. k <= c /\ (!r. MEM r l ==> c <> EL r colors) ==> k <= lookup_default_id exch c)) /\
    ((!r. MEM r l ==> (k <= EL r colors /\ k <= r DIV 2)) ==>
      (!c. c < k ==> lookup_default_id exch c = c))
Proof
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

    strip_tac THEN1 (
        rw [lookup_default_id_insert] >>
        every_case_tac >>
        fs [FUN_EQ_THM] >>
        metis_tac []
    ) >>
    strip_tac THEN1 (
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
    ) >>
    strip_tac THEN1 (
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
    ) >>
    strip_tac THEN1 (
        rpt strip_tac >>
        `h DIV 2 < k` by fs [] >>
        `~(k <= h DIV 2)` by simp [] >>
        simp [lookup_default_id_insert] >>
        `~(k <= col2 /\ (!r. MEM r l ==> col2 <> EL r colors))` by metis_tac [o_DEF] >>
        fs [] >>
        rpt CASE_TAC >>
        metis_tac []
    )
    THEN1 (
        rpt strip_tac >>
        simp [lookup_default_id_insert] >>
        `k <= EL h colors /\ k <= h DIV 2` by fs [] >>
        `k <= col1 /\ k <= fcol1` by fs [] >>
        `!r. MEM r l ==> k <= EL r colors /\ k <= r DIV 2` by simp [] >>
        fs [] >>
        rpt CASE_TAC >>
        `h DIV 2 < k` by metis_tac [FUN_EQ_THM, o_DEF] >>
        fs []
    )
QED

Theorem find_reg_exchange_correct:
     !l sth k.
    ALL_DISTINCT (MAP (\r. EL r sth.colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    ?exch invexch. find_reg_exchange l LN LN sth = (Success (exch, invexch), sth) /\
    ((lookup_default_id exch) o (lookup_default_id invexch) = (\x.x) /\ (lookup_default_id invexch) o (lookup_default_id exch) = (\x.x)) /\
    (!r. MEM r l ==> lookup_default_id exch (EL r sth.colors) = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors <=> k <= r DIV 2)) ==>
      (!c. id (k <= c <=> k <= lookup_default_id exch c))) /\
    ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!c. k <= c /\ (!r. MEM r l ==> c <> EL r sth.colors) ==> k <= lookup_default_id exch c)) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors /\ k <= r DIV 2)) ==>
      (!c. c < k ==> lookup_default_id exch c = c))
Proof
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
    qspecl_then [`l'`, `sth.colors`, `x0`, `x1`, `k`] assume_tac find_reg_exchange_FOLDR_correct >>
    rfs []
QED

Theorem MAP_colors_eq_lemma:
     !sth n f.
    n <= LENGTH sth.colors ==>
    ?sthout. (Success (), sthout) = MAP_colors f n sth /\
    LENGTH sth.colors = LENGTH sthout.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!n'. n' < n ==> EL n' sthout.colors = f (EL n' sth.colors)) /\
    (!n'. n <= n' ==> EL n' sthout.colors = EL n' sth.colors)
Proof
    Induct_on `n` >>
    rw [MAP_colors_def] >> rw msimps >>
    `?sth'. sth' = sth with colors := LUPDATE (f (EL n sth.colors)) n sth.colors` by rw [] >>
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
QED

Theorem MAP_colors_eq:
     !sth f.
    ?sthout. (Success (), sthout) = MAP_colors f (LENGTH sth.colors) sth /\
    (!n. n < LENGTH sth.colors ==> EL n sthout.colors = f (EL n sth.colors)) /\
    LENGTH sth.colors = LENGTH sthout.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end
Proof
    rw [] >>
    `LENGTH sth.colors <= LENGTH sth.colors` by rw [] >>
    metis_tac [MAP_colors_eq_lemma]
QED

Theorem apply_reg_exchange_correct:
     !l sth k.
    ALL_DISTINCT (MAP (\r. EL r sth.colors) l) /\
    (!r. MEM r l ==> is_phy_var r) /\
    (!r. MEM r l ==> r < LENGTH sth.colors) ==>
    ?sthout. (Success (), sthout) = apply_reg_exchange l sth /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r1 r2. r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors ==> EL r1 sthout.colors = EL r2 sthout.colors ==> EL r1 sth.colors = EL r2 sth.colors) /\
    (!r. MEM r l ==> EL r sthout.colors = r DIV 2) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors <=> k <= r DIV 2)) ==>
      (!r. r < LENGTH sth.colors ==> (k <= EL r sth.colors <=> k <= EL r sthout.colors))) /\
    ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!r. r < LENGTH sth.colors /\ k <= EL r sth.colors /\ (!r'. MEM r' l ==> EL r sth.colors <> EL r' sth.colors) ==> k <= EL r sthout.colors)) /\
    ((!r. MEM r l ==> (k <= EL r sth.colors /\ k <= r DIV 2)) ==>
      (!r. r < LENGTH sth.colors /\ EL r sth.colors < k ==> EL r sthout.colors = EL r sth.colors))
Proof
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
    simp [] >>
    strip_tac THEN1 (
      fs [FUN_EQ_THM] >>
      metis_tac []
    )
    THEN1 (
      rpt strip_tac >> fs [] >>
      `id (k <= EL r sth.colors <=> k <= lookup_default_id exch (EL r sth.colors))` by metis_tac [] >>
      qpat_x_assum `!c. id _` kall_tac >>
      fs [id_def]
    )
QED

val less_FST_def = Define`
    less_FST (x:int#num) y = (FST x <= FST y)
`;

Theorem transitive_less_FST:
     transitive less_FST
Proof
    rw [transitive_def, less_FST_def] >>
    intLib.COOPER_TAC
QED

val good_linear_scan_state_def = Define`
    good_linear_scan_state st sth l (pos:int) forced mincol = (
        LENGTH sth.int_beg = LENGTH sth.colors /\ LENGTH sth.int_end = LENGTH sth.colors /\
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
        EVERY (\r. EL r sth.int_beg <= pos) l /\
        EVERY (\r. ((pos <= EL r sth.int_end /\ EL r sth.colors < st.colormax) ==> (MEM (EL r sth.int_end, r) st.active))) l /\
        EVERY (\r. ((MEM (EL r sth.int_end, r) st.active) ==> (pos <= 1 + EL r sth.int_end))) l /\
        (!r1 r2. MEM r1 l /\ MEM r2 l /\
            interval_intersect (EL r1 sth.int_beg, EL r1 sth.int_end) (EL r2 sth.int_beg, EL r2 sth.int_end) /\
            EL r1 sth.colors = EL r2 sth.colors ==> r1 = r2
        ) /\
        SORTED less_FST st.active /\
        EVERY (\e,r. e = EL r sth.int_end) st.active /\
        EVERY (\e,r. MEM r l) st.active /\
        EVERY (\r1,r2. MEM r1 l /\ MEM r2 l /\ EL r1 sth.colors = EL r2 sth.colors ==> r1 = r2) forced /\
        mincol <= st.colornum /\
        EVERY (\c. mincol <= c) (st.colorpool ++ MAP (\r. EL r sth.colors) l)
    )
`;

val good_linear_scan_state_def' = let
  val inj_rwt = Q.prove(‘(f x = f y ==> x = y) ⇔ (f x = f y ⇔ x = y)’,
                        metis_tac[])
in
  good_linear_scan_state_def
    |> SIMP_RULE bool_ss [GSYM AND_IMP_INTRO, inj_rwt]
    |> SIMP_RULE bool_ss [AND_IMP_INTRO]
end

Theorem remove_inactive_intervals_invariants:
     !beg st sth l pos forced mincol.
    good_linear_scan_state st sth l pos forced mincol /\
    pos <= beg ==>
    ?stout. (Success stout, sth) = remove_inactive_intervals beg st sth /\
    good_linear_scan_state stout sth l beg forced mincol /\
    stout.colormax = st.colormax
Proof
    recInduct remove_inactive_intervals_ind >>
    rw [] >>
    once_rewrite_tac [remove_inactive_intervals_def] >>
    rw msimps >>
    Cases_on `st.active`

    THEN1 (
        rfs [good_linear_scan_state_def'] >>
        fs [EVERY_MEM] >> rw []
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
        THEN1 (
          CCONTR_TAC >> fs [] >>
          `pos <= EL r sth.int_end` by intLib.COOPER_TAC >>
          res_tac
        )
    ) >>

    PairCases_on `h` >>
    rename1 `st.active = (e,r)::activetail` >>
    rw []

    THEN1 (
        rfs [] >>
        `r < LENGTH sth.colors` by fs [EVERY_MEM, FORALL_PROD, good_linear_scan_state_def'] >>
        rfs [] >>
        first_x_assum (qspecl_then [`EL r sth.colors`, `sth`, `l`, `e+1`, `forced`, `mincol`] assume_tac) >>
        `e+1 <= beg` by intLib.COOPER_TAC >>
        sg `good_linear_scan_state (st with <| active := activetail; colorpool updated_by (\l. (EL r sth.colors)::l) |>) sth l (e+1) forced mincol` THEN1 (
            qpat_x_assum `good_linear_scan_state _ _ _ _ _ _ /\ _ ==> _` kall_tac >>
            fs [good_linear_scan_state_def'] >>
            `pos <= 1+e` by (fs [EVERY_MEM] >> metis_tac []) >>
            sg `!(h:num) l1 l2. PERM (l1 ++ h::l2) ((h::l1) ++ l2)` THEN1 (
              rw [] >>
              `PERM (l1 ++ [h]) ([h] ++ l1)` by simp [PERM_APPEND] >>
              `PERM (l1 ++ [h] ++ l2) ([h] ++ l1 ++ l2)` by simp [PERM_APPEND_IFF] >>
              rfs [] >>
              `l1 ++ h::l2 = (l1 ++ [h]) ++ l2` by simp [] >>
              simp []
            ) >>
            `ALL_DISTINCT ((EL r sth.colors :: st.colorpool) ++ MAP (λ(e,r). EL r sth.colors) activetail)` by metis_tac [ALL_DISTINCT_PERM] >>
            rfs [] >>
            fs [EVERY_MEM] >> rw []
            THEN1 (
              res_tac >>
              intLib.COOPER_TAC
            )
            THEN1 (
              `pos <= EL r' sth.int_end` by intLib.COOPER_TAC >>
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
            THEN1 (
                fs [MEM_MAP] >>
                metis_tac []
            )
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
          fs [good_linear_scan_state_def'] >>
          `less_FST (e,r) (e',r')` by imp_res_tac SORTED_EQ >>
          fs [less_FST_def] >>
          intLib.COOPER_TAC
        ) >>
        qpat_x_assum `st.active = _` kall_tac >>
        fs [good_linear_scan_state_def'] >>
        fs [EVERY_MEM] >> rw []
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
        THEN1 (
          `pos <= EL r sth.int_end` by intLib.COOPER_TAC >>
          metis_tac []
        )
        THEN1 (
          res_tac >>
          intLib.COOPER_TAC
        )
    )
QED

Theorem add_active_interval_output:
     !lin x lout.
    SORTED less_FST lin /\
    lout = add_active_interval (e,r) lin ==>
    SORTED less_FST lout /\
    ?l1 l2. lin = l1 ++ l2 /\ lout = l1 ++ (e,r)::l2
Proof
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
QED

Theorem find_color_in_list_output:
     !forbidden col l rest.
    find_color_in_list l forbidden = SOME (col, rest) ==>
    MEM col l /\ col NOTIN domain forbidden /\
    ?l1 l2. rest = l1 ++ l2 /\ l = l1 ++ col::l2
Proof
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
QED

Theorem find_color_in_colornum_invariants:
     !st forbidden sth l pos forced mincol.
    good_linear_scan_state st sth l pos forced mincol /\
    domain forbidden SUBSET {EL r sth.colors | r | MEM r l} /\
    find_color_in_colornum st forbidden = (stout, SOME col) ==>
    good_linear_scan_state (stout with colorpool updated_by (\l. col::l)) sth l pos forced mincol /\
    st.colornum <= col /\ col < stout.colornum /\
    st.colornum <= stout.colornum /\
    col NOTIN domain forbidden /\
    st = stout with <| colorpool := st.colorpool; colornum := st.colornum |>
Proof
    rw [find_color_in_colornum_def] >> rw []
    THEN1 (
      fs [good_linear_scan_state_def'] >>
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
      CCONTR_TAC >> fs [good_linear_scan_state_def'] >>
      `st.colornum IN {EL r sth.colors | r | MEM r l}` by fs [SUBSET_DEF] >>
      fs [EVERY_MEM] >>
      rpt (first_x_assum (qspec_then `r` assume_tac)) >>
      rfs []
    )
    THEN1 rw [linear_scan_state_component_equality]
QED

Theorem find_color_invariants:
     !st forbidden stout col sth l pos forced mincol.
    good_linear_scan_state st sth l pos forced mincol /\
    domain forbidden SUBSET {EL r sth.colors | r | MEM r l} /\
    find_color st forbidden = (stout, SOME col) ==>
    good_linear_scan_state (stout with colorpool updated_by (\l. col::l)) sth l pos forced mincol /\
    col < stout.colornum /\
    col NOTIN domain forbidden /\
    st = stout with <| colorpool := st.colorpool; colornum := st.colornum |>
Proof
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
      sg `ALL_DISTINCT (col::(l1++l2) ++ MAP (λ(e,r). EL r sth.colors) st.active)` THEN1 (
        FULL_SIMP_TAC pure_ss [good_linear_scan_state_def'] >>
        metis_tac [ALL_DISTINCT_PERM, PERM_APPEND_IFF]
      ) >>
      simp [linear_scan_state_component_equality] >>
      fs [good_linear_scan_state_def', EVERY_MEM] >>
      metis_tac []
    )
QED

Theorem update_color_active_colors_same:
     !e reg active regcol colors.
    MAP (\e,r. EL r (LUPDATE regcol reg colors)) (FILTER (\e,r. r <> reg) active) = MAP (\e,r. EL r colors) (FILTER (\e,r. r <> reg) active)
Proof
    Induct_on `active` >>
    rw [] >>
    pairarg_tac >>
    rw [EL_LUPDATE] >>
    fs []
QED

Theorem forced_update_stack_color_lemma:
     !(colors : num list) (stacknum : num) l r2 r1.
    EVERY (\r. EL r colors < stacknum) l /\
    MEM r2 l /\
    r1 < LENGTH colors /\
    EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum r1 colors) ==>
    r1 = r2
Proof
    (* recast injectivity to make simplifier (much!) faster *)
    ‘∀(colors:num list) stacknum l r2 r1.
      EVERY (λr. EL r colors < stacknum) l ∧ MEM r2 l ∧ r1 < LENGTH colors ⇒
      (EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum r1 colors) ⇔
       r1 = r2)’ suffices_by metis_tac[] >>
    Induct_on `l` >> rw []
    >- fs[EL_LUPDATE]
    >- metis_tac []
QED

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

Theorem FILTER_IS_SPARSE_SUBLIST:
     !l. IS_SPARSE_SUBLIST (FILTER P l) l
Proof
    Induct_on `l` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Cases_on `FILTER P l` >>
    rw [IS_SPARSE_SUBLIST_def]
QED

Theorem MEM_SPARSE_SUBLIST:
     !l1 l2 x. IS_SPARSE_SUBLIST l1 l2 /\ MEM x l1 ==> MEM x l2
Proof
    Induct_on `l1` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Induct_on `l2` >>
    fs [IS_SPARSE_SUBLIST_def] >> rw [] >>
    rw []
QED

Theorem IS_SPARSE_SUBLIST_APPEND_LEFT:
     !l1 l2 l. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (l ++ l1) (l ++ l2)
Proof
    Induct_on `l` >>
    rw [IS_SPARSE_SUBLIST_def]
QED

Theorem IS_SPARSE_SUBLIST_APPEND_RIGHT:
     !l1 l2 l. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (l1 ++ l) (l2 ++ l)
Proof
    Induct_on `l1` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Induct_on `l2` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    Induct_on `l` >>
    rw [IS_SPARSE_SUBLIST_def]
QED

Theorem MAP_IS_SPARSE_SUBLIST:
     !l1 l2. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (MAP f l1) (MAP f l2)
Proof
    Induct_on `l1` >>
    Induct_on `l2` >>
    rw [IS_SPARSE_SUBLIST_def] >>
    rfs []
QED

Theorem ALL_DISTINCT_IS_SPARSE_SUBLIST:
     !l1 l2. ALL_DISTINCT l2 /\ IS_SPARSE_SUBLIST l1 l2 ==> ALL_DISTINCT l1
Proof
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
QED

Theorem spill_register_FILTER_invariants_hidden:
     !st sth l pos forced reg mincol.
    id (~(is_phy_var reg) \/ ~(MEM reg l)) /\
    good_linear_scan_state st sth l pos forced mincol /\
    reg < LENGTH sth.colors /\
    EL reg sth.int_beg <= pos ==>
    ?stout sthout. (Success stout, sthout) = spill_register (st with active := FILTER (\e,r. r <> reg) st.active) reg sth /\
    good_linear_scan_state stout sthout (reg::l) pos forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    (!r. r <> reg ==> EL r sth.colors = EL r sthout.colors) /\
    stout.colormax = st.colormax /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    st.colormax <= EL reg sthout.colors
Proof
    rw [spill_register_def] >> rw msimps >>
    fs [good_linear_scan_state_def'] >>
    rpt strip_tac
    THEN1 ((* 24 *)
        rw [update_color_active_colors_same] >>
        metis_tac [FILTER_IS_SPARSE_SUBLIST, MAP_IS_SPARSE_SUBLIST, IS_SPARSE_SUBLIST_APPEND_LEFT, ALL_DISTINCT_IS_SPARSE_SUBLIST]
    )
    THEN1 (* 23 *) rw [EL_LUPDATE]
    THEN1 ((* 22 *)
        fs [EVERY_MEM, FORALL_PROD] >>
        rw [EL_LUPDATE] >>
        `EL r sth.colors < st.stacknum` by rw [] >>
        rw []
    )
    THEN1 ((* 21 *)
        rw [EXTENSION] >>
        eq_tac >>
        rw [] >>
        qexists_tac `r` >>
        rw [EL_LUPDATE] >>
        fs [EL_LUPDATE, id_def]
    )
    THEN1 ((* 20 *)
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
    THEN1 ((* 19 *)
        fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER] >>
        metis_tac []
    )
    THEN1 (* 18 *) fs [EL_LUPDATE]
    THEN1 (* 17 *) fs [EL_LUPDATE, EVERY_MEM]
    THEN1 (* 16 *) fs [EL_LUPDATE]
    THEN1 (* 15 *) fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 (* 14 *) fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 (* 13 *) fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 (* 12 *) rw []
    THEN1 (* 11 *) metis_tac [forced_update_stack_color_lemma]
    THEN1 (* 10 *) metis_tac [forced_update_stack_color_lemma]
    THEN1 ((* 9 *)
        fs [EL_LUPDATE] >>
        Cases_on `r1 = reg /\ reg < LENGTH sth.colors` >>
        Cases_on `r2 = reg /\ reg < LENGTH sth.colors` >>
        fs [EVERY_MEM] >>
        TRY (`EL r2 sth.colors < st.stacknum` by rw []) >>
        TRY (`EL r1 sth.colors < st.stacknum` by rw []) >>
        rw []
    )
    THEN1 (* 8 *) metis_tac [transitive_less_FST, SORTED_FILTER]
    THEN1 (* 7 *) fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER]
    THEN1 ((* 6 *)
        fs [EVERY_MEM, FORALL_PROD, EL_LUPDATE, MEM_FILTER] >>
        metis_tac []
    )
    THEN1 ((* 5 *)
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
    THEN1 (* 4 *) simp [EL_LUPDATE]
    THEN1 ((* 3 *)
        `mincol <= st.stacknum` by simp [] >>
        fs [EVERY_MEM, EL_LUPDATE, MEM_MAP] >>
        metis_tac []
    )
    THEN1 (* 2 *) simp [EL_LUPDATE]
    THEN1 (* 1 *) simp [EL_LUPDATE]
QED

val spill_register_FILTER_invariants =
  spill_register_FILTER_invariants_hidden
  |> REWRITE_RULE [id_def]
  |> curry save_thm "spill_register_FILTER_invariants"

Theorem FILTER_MEM_active:
     !(reg:num) l. (!(e:int). ~(MEM (e,reg) l)) ==> FILTER (\e,r. r <> reg) l = l
Proof
    Induct_on `l` >> rw [] >>
    pairarg_tac >> fs [] >>
    metis_tac []
QED

Theorem spill_register_invariants:
     !st sth l pos forced reg mincol.
    (!e. ~(MEM (e,reg) st.active)) /\
    (~(is_phy_var reg) \/ ~(MEM reg l)) /\
    good_linear_scan_state st sth l pos forced mincol /\
    reg < LENGTH sth.colors /\
    EL reg sth.int_beg <= pos ==>
    ?stout sthout. (Success stout, sthout) = spill_register st reg sth /\
    good_linear_scan_state stout sthout (reg::l) pos forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. r <> reg ==> EL r sth.colors = EL r sthout.colors) /\
    stout.colormax = st.colormax /\
    st.colormax <= EL reg sthout.colors
Proof
    rw [] >>
    `FILTER (\e,r. r <> reg) st.active = st.active` by simp [FILTER_MEM_active] >>
    `st = st with active := FILTER (\e,r. r <> reg) st.active` by simp [linear_scan_state_component_equality] >>
    metis_tac [spill_register_FILTER_invariants]
QED

val edges_to_adjlist_step_def = Define`
    edges_to_adjlist_step sth (a,b) acc =
      if a = b then
        acc
      else if ($< LEX $<=) (EL a sth.int_beg, a) (EL b sth.int_beg, b) then
        insert b (a::(the [] (lookup b acc))) acc
      else
        insert a (b::(the [] (lookup a acc))) acc
`;

Theorem edges_to_adjlist_FOLDL:
     !forced sth acc.
    EVERY (\r1,r2. r1 < LENGTH sth.int_beg /\ r2 < LENGTH sth.int_beg) forced ==>
    edges_to_adjlist forced acc sth = (Success (FOLDL (\acc pair. edges_to_adjlist_step sth pair acc) acc forced), sth)
Proof
    Induct_on `forced`
    THEN1 rw (edges_to_adjlist_def::msimps) >>
    rw [] >>
    PairCases_on `h` >> fs [] >>
    rw [edges_to_adjlist_def, edges_to_adjlist_step_def] >>
    fs [LEX_DEF] >>
    rw msimps >>
    every_case_tac
QED

val forbidden_is_from_forced_def = Define`
    forbidden_is_from_forced forced (int_beg : int list) reg forbidden =
        !reg2. (reg <> reg2 /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) /\
        ($< LEX $<=) (EL reg2 int_beg, reg2) (EL reg int_beg, reg)) <=> MEM reg2 forbidden
`;

val forbidden_is_from_forced_sublist_def = Define`
    forbidden_is_from_forced_sublist l forced (int_beg : int list) reg forbidden =
        !reg2. (reg <> reg2 /\ (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) /\
        ($< LEX $<=) (EL reg2 int_beg, reg2) (EL reg int_beg, reg)) <=> (MEM reg2 forbidden /\ MEM reg l)
`;

val forbidden_is_from_forced_list_def = Define`
    forbidden_is_from_forced_list forced l reg forbidden =
        !reg2. MEM reg2 l /\
               (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) ==>
               MEM reg2 forbidden
`;

val forbidden_is_from_map_color_forced_def = Define`
    forbidden_is_from_map_color_forced forced l colors reg (forbidden:num_set) =
        !reg2. MEM reg2 l /\
               (MEM (reg2, reg) forced \/ MEM (reg, reg2) forced) ==>
               EL reg2 colors IN domain forbidden
`;

Theorem edges_to_adjlist_FOLDR_output:
     !forced sth.
    !reg. forbidden_is_from_forced forced sth.int_beg reg (the [] (lookup reg (FOLDR (\pair acc. edges_to_adjlist_step sth pair acc) LN forced)))
Proof
    simp [forbidden_is_from_forced_def] >>
    Induct_on `forced`
    THEN1 rw [forbidden_is_from_forced_def, lookup_def, the_def] >>
    simp [] >>
    rpt gen_tac >>
    first_x_assum (qspec_then `sth` assume_tac) >>
    qabbrev_tac `adjlist = FOLDR (\pair acc. edges_to_adjlist_step sth pair acc) LN forced` >>
    qpat_x_assum `Abbrev _` kall_tac >>
    PairCases_on `h` >>
    eq_tac
    THEN1 (
      strip_tac
      THEN1 (
        fs [] >> rveq >>
        simp [edges_to_adjlist_step_def, the_def]
      )
      THEN1 (
        simp [edges_to_adjlist_step_def, the_def] >>
        rpt CASE_TAC >>
        rw [lookup_insert, the_def] >>
        rw [METIS_PROVE [] ``!a b. a \/ b <=> ~a ==> b``] >>
        metis_tac []
      )
      THEN1 (
        fs [] >> rveq >>
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
        rpt CASE_TAC >>
        rw [lookup_insert, the_def] >>
        rw [METIS_PROVE [] ``!a b. a \/ b <=> ~a ==> b``] >>
        metis_tac []
      )
    )
    THEN1 (
      simp [edges_to_adjlist_step_def] >>
      rpt strip_tac >>
      every_case_tac >>
      TRY (`($< LEX $<=) (EL h1 sth.int_beg, h1) (EL h0 sth.int_beg, h0)` by (fs [LEX_DEF] >> intLib.COOPER_TAC)) >>
      Cases_on `reg = h1` >>
      Cases_on `reg2 = h0` >>
      Cases_on `reg = h0` >>
      Cases_on `reg2 = h1` >>
      fs [lookup_insert, the_def] >> fs [] >>
      metis_tac []
    )
QED

Theorem edges_to_adjlist_output:
     !forced sth.
    EVERY (\r1,r2. r1 < LENGTH sth.int_beg /\ r2 < LENGTH sth.int_beg) forced ==>
    ?adjlist. edges_to_adjlist forced LN sth = (Success adjlist, sth) /\
    !reg. forbidden_is_from_forced forced sth.int_beg reg (the [] (lookup reg adjlist))
Proof
    rw [edges_to_adjlist_FOLDL, GSYM FOLDR_REVERSE] >>
    qspecl_then [`REVERSE forced`, `sth`, `reg`] assume_tac edges_to_adjlist_FOLDR_output >>
    fs [forbidden_is_from_forced_def]
QED

Theorem state_invariants_remove_head:
     !st sth reg l pos forced mincol.
    MEM reg l /\
    good_linear_scan_state st sth (reg::l) pos forced mincol ==>
    good_linear_scan_state st sth l pos forced mincol
Proof
    rw [] >>
    `!r. r = reg \/ MEM r l <=> MEM r l` by metis_tac [] >>
    rw [good_linear_scan_state_def'] >>
    fs [good_linear_scan_state_def'] >>
    every_case_tac >> fs []
QED

Theorem find_last_stealable_success:
     !forbidden sth active.
    EVERY (\e,r. r < LENGTH sth.colors) active ==>
    ?optout. find_last_stealable active forbidden sth = (Success optout, sth)
Proof
    NTAC 2 gen_tac >>
    Induct_on `active` >>
    rw [find_last_stealable_def] >> simp msimps >>
    fs [] >>
    every_case_tac >>
    PairCases_on `h` >>
    rfs []
QED

Theorem find_last_stealable_output:
     !forbidden sth active steal rest.
    find_last_stealable active forbidden sth = (Success (SOME (steal, rest)), sth) ==>
    ~is_phy_var (SND steal) /\ lookup (EL (SND steal) sth.colors) forbidden = NONE /\
    ?l1 l2. rest = l1 ++ l2 /\ active = l1 ++ steal::l2
Proof
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
QED

Theorem good_linear_scan_state_active_length_colors:
     !st sth l pos forced mincol.
    good_linear_scan_state st sth l pos forced mincol ==>
    EVERY (\e,r. r < LENGTH sth.colors) st.active
Proof
    rw [good_linear_scan_state_def', EVERY_MEM] >>
    res_tac >>
    rpt (pairarg_tac >> fs [])
QED

Theorem color_register_eq:
     !st reg col rend.
    color_register st reg col rend =
      do
        update_colors reg col;
        return (
          st with
            <| active  updated_by add_active_interval (rend, reg)
             ; phyregs := if is_phy_var reg then  (insert col ()) st.phyregs else st.phyregs
             |>
        )
      od
Proof
    rw [color_register_def] >> fs msimps >>
    rw [FUN_EQ_THM] >>
    every_case_tac >>
    simp [linear_scan_state_component_equality]
QED

Theorem color_register_invariants:
     !st sth l pos forced reg col forbidden mincol.
    good_linear_scan_state st sth l pos forced mincol /\
    forbidden_is_from_map_color_forced forced l sth.colors reg forbidden /\
    col NOTIN domain forbidden /\
    (is_phy_var reg ==> domain st.phyregs SUBSET domain forbidden) /\
    ~MEM col (st.colorpool ++ MAP (\(e,r). EL r sth.colors) st.active) /\
    EL reg sth.int_beg = pos /\
    EL reg sth.int_beg <= EL reg sth.int_end /\
    col < st.colornum /\
    mincol <= col /\
    reg < LENGTH sth.colors /\
    ~MEM reg l
    ==>
    ?stout sthout. (Success stout, sthout) = color_register st reg col (EL reg sth.int_end) sth /\
    good_linear_scan_state stout sthout (reg::l) pos forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. r <> reg ==> EL r sth.colors = EL r sthout.colors) /\
    stout.colormax = st.colormax
Proof
    rpt strip_tac >> simp [color_register_eq] >> simp msimps >>
    fs [good_linear_scan_state_def'] >>
    rpt strip_tac
    THEN1 (
      sg `!e. ~MEM (e,reg) st.active` THEN1 (
        strip_tac >> CCONTR_TAC >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD] >>
        res_tac
      ) >>
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
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
      rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
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
      rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs []
    )
    THEN1 (
      imp_res_tac add_active_interval_output >> fs [] >>
      rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
      fs [EVERY_MEM] >>
      rw [EL_LUPDATE]
    )
    THEN1 (
        intLib.COOPER_TAC
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs [] >>
        rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
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
        `MEM (EL r2 sth.int_end, r2) st.active` by rw [] >>
        fs [MEM_MAP, FORALL_PROD] >>
        metis_tac []
    )
    THEN1 (
        rveq >>
        CCONTR_TAC >>
        rfs [EL_LUPDATE] >>
        fs [interval_intersect_def, EVERY_MEM] >>
        `EL r1 sth.colors < st.colormax` by rw [] >>
        `MEM (EL r1 sth.int_end, r1) st.active` by rw [] >>
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
        rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD]
    )
    THEN1 (
        imp_res_tac add_active_interval_output >> fs [] >>
        rpt (first_x_assum (qspecl_then [`reg`, `EL reg sth.int_end`] assume_tac)) >> fs [] >>
        fs [EVERY_MEM, FORALL_PROD] >>
        metis_tac []
    )
    THEN1 (
        fs [EVERY_MEM, FORALL_PROD, forbidden_is_from_map_color_forced_def] >>
        rw [] >>
        rename1 `MEM (reg1, reg2) forced` >> eq_tac >> simp[] >> strip_tac
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
          Cases_on `reg2 = reg` >> FULL_SIMP_TAC bool_ss [] >> metis_tac[]
        )
    )
    THEN1 simp [EL_LUPDATE]
    THEN1 (
        fs [EVERY_MEM, MEM_MAP, EL_LUPDATE] >>
        metis_tac []
    )
    THEN1 simp [EL_LUPDATE]
QED

Theorem find_spill_invariants:
     !st sth l forbidden forced reg force mincol.
    ~MEM reg l /\
    good_linear_scan_state st sth l (EL reg sth.int_beg) forced mincol /\
    reg < LENGTH sth.colors /\
    forbidden_is_from_map_color_forced forced l sth.colors reg forbidden /\
    (is_phy_var reg ==> domain st.phyregs SUBSET domain forbidden) /\
    EL reg sth.int_beg <= EL reg sth.int_end ==>
    ?stout sthout. (Success stout, sthout) = find_spill st forbidden reg (EL reg sth.int_end) force sth /\
    good_linear_scan_state stout sthout (reg::l) (EL reg sth.int_beg) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r (reg::l)  ==> EL r sthout.colors = EL r sth.colors) /\
    (!r. MEM r l /\ is_phy_var r ==> EL r sthout.colors = EL r sth.colors) /\
    stout.colormax = st.colormax
Proof
    rw [find_spill_def] >> simp msimps >>
    `!e. ~(MEM (e,reg) st.active)` by (CCONTR_TAC >> fs [good_linear_scan_state_def', EVERY_MEM, FORALL_PROD]) >>
    imp_res_tac good_linear_scan_state_active_length_colors >>
    `?optsteal. find_last_stealable st.active forbidden sth = (Success optsteal, sth)` by metis_tac [find_last_stealable_success] >>
    simp [] >>
    CASE_TAC
    THEN1 (
      qspecl_then [`st`, `sth`, `l`, `EL reg sth.int_beg`, `forced`, `reg`, `mincol`] assume_tac spill_register_invariants >>
      rfs [] >>
      metis_tac [spill_register_invariants]
    ) >>
    PairCases_on `x` >>
    rename1 `find_last_stealable _ _ _ = (Success (SOME ((stealend, stealreg), rest)), _)` >>
    simp [] >>
    reverse CASE_TAC
    THEN1 (
      qspecl_then [`st`, `sth`, `l`, `EL reg sth.int_beg`, `forced`, `reg`, `mincol`] assume_tac spill_register_invariants >>
      rfs [] >>
      metis_tac [spill_register_invariants]
    ) >>
    qpat_x_assum `_ \/ _ < _` kall_tac >>
    imp_res_tac find_last_stealable_output >>
    `stealreg < LENGTH sth.colors` by fs [EVERY_MEM, FORALL_PROD] >>
    `MEM (stealend, stealreg) st.active` by rw [] >>
    `MEM stealreg l` by fs [good_linear_scan_state_def', EVERY_MEM, FORALL_PROD] >>
    rw [] >>
    FULL_SIMP_TAC pure_ss [SND] >>
    `(EL stealreg sth.colors) NOTIN domain forbidden` by fs [lookup_NONE_domain] >>
    `EL stealreg sth.colors < st.colornum` by fs [good_linear_scan_state_def'] >>
    sg `ALL_DISTINCT ([EL stealreg sth.colors] ++ st.colorpool ++ (MAP (\e,r. EL r sth.colors) l1) ++ (MAP (\e,r. EL r sth.colors) l2))` THEN1 (
        `ALL_DISTINCT (st.colorpool ++ MAP (\e,r. EL r sth.colors) st.active)` by rfs [good_linear_scan_state_def'] >>
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
        `ALL_DISTINCT (MAP (\e,r. EL r sth.colors) st.active)` by rfs [good_linear_scan_state_def', ALL_DISTINCT_APPEND] >>
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
        `EVERY (\e,r. e = EL r sth.int_end) (l1++l2)` by fs [good_linear_scan_state_def', EVERY_APPEND] >>
        fs [EVERY_APPEND] >>
        `stealend = EL stealreg sth.int_end` by fs [good_linear_scan_state_def', EVERY_MEM, FORALL_PROD] >>
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
    `mincol <= EL stealreg sth.colors` by (fs [good_linear_scan_state_def', EVERY_MEM, MEM_MAP] >> metis_tac []) >>
    `EL stealreg sth.int_beg <= EL reg sth.int_beg` by fs [good_linear_scan_state_def', EVERY_MEM] >>
    qspecl_then [`st`, `sth`, `l`, `EL reg sth.int_beg`, `forced`, `stealreg`, `mincol`] assume_tac (GSYM spill_register_FILTER_invariants) >>
    rfs [] >>
    imp_res_tac state_invariants_remove_head >>
    qspecl_then [`stout`, `sthout`, `l`, `EL reg sth.int_beg`, `forced`, `reg`, `EL stealreg sth.colors`, `forbidden`, `mincol`] assume_tac color_register_invariants >>
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
QED

Theorem linear_reg_alloc_step_aux_invariants:
     !st sth l preferred (forbidden:num_set) forced reg force mincol.
    ~MEM reg l /\
    good_linear_scan_state st sth l (EL reg sth.int_beg) forced mincol /\
    reg < LENGTH sth.colors /\
    forbidden_is_from_map_color_forced forced l sth.colors reg forbidden /\
    (is_phy_var reg ==> domain st.phyregs SUBSET domain forbidden) /\
    domain forbidden SUBSET {EL r sth.colors | r | MEM r l} /\
    EL reg sth.int_beg <= EL reg sth.int_end ==>
    ?stout sthout. (Success stout, sthout) = linear_reg_alloc_step_aux st forbidden preferred reg (EL reg sth.int_end) force sth /\
    good_linear_scan_state stout sthout (reg::l) (EL reg sth.int_beg) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r (reg::l)  ==> EL r sthout.colors = EL r sth.colors) /\
    (!r. MEM r l /\ is_phy_var r ==> EL r sthout.colors = EL r sth.colors) /\
    stout.colormax = st.colormax
Proof
    rw [linear_reg_alloc_step_aux_def] >>
    Cases_on `find_color_in_list (FILTER (\c. MEM c st.colorpool) preferred) forbidden` >> fs []
    THEN1 (
      Cases_on `find_color st forbidden` >> fs [] >>
      rename1 `_ = (stout, optcol)` >>
      Cases_on `optcol` >> fs []
      THEN1 (
        fs [find_color_def, find_color_in_colornum_def, case_eq_thms] >>
        Cases_on `st.colormax <= st.colornum` >> fs [] >>
        qspecl_then [`st`, `sth`, `l`, `forbidden`, `forced`, `reg`, `force`, `mincol`] assume_tac find_spill_invariants >>
        rfs [] >>
        metis_tac []
      )
      THEN1 (
        rename1 `_ = (stout, SOME col)` >>
        qspecl_then [`st`, `forbidden`, `stout`, `col`, `sth`, `l`, `EL reg sth.int_beg`, `forced`, `mincol`] assume_tac find_color_invariants >>
        rfs [linear_scan_state_component_equality] >>
        `~MEM col (stout.colorpool ++ MAP (\(e,r). EL r sth.colors) stout.active)` by fs [good_linear_scan_state_def'] >>
        `mincol <= col` by fs [good_linear_scan_state_def'] >>
        `good_linear_scan_state stout sth l (EL reg sth.int_beg) forced mincol` by fs [good_linear_scan_state_def'] >>
        metis_tac [color_register_invariants]
      )
    )
    THEN1 (
      PairCases_on `x` >>
      rename1 `_ = SOME (col, _)` >>
      simp [] >>
      imp_res_tac find_color_in_list_output >>
      fs [MEM_FILTER] >>
      sg `good_linear_scan_state (st with colorpool updated_by FILTER (\y. col <> y)) sth l (EL reg sth.int_beg) forced mincol` THEN1 (
        fs [good_linear_scan_state_def'] >>
        simp [EVERY_FILTER_IMP] >>
        metis_tac [FILTER_IS_SPARSE_SUBLIST, IS_SPARSE_SUBLIST_APPEND_RIGHT, ALL_DISTINCT_IS_SPARSE_SUBLIST]
      ) >>
      sg `~MEM col ((FILTER (\y. col <> y) st.colorpool) ++ MAP (\e,r. EL r sth.colors) st.active)` THEN1 (
        rw [MEM_FILTER] >>
        fs [good_linear_scan_state_def', ALL_DISTINCT_APPEND]
      ) >>
      `col < st.colornum` by fs [good_linear_scan_state_def', EVERY_MEM] >>
      `mincol <= col` by fs [good_linear_scan_state_def', EVERY_MEM, MEM_MAP] >>
      qspecl_then [`st with colorpool updated_by FILTER (\y. col <> y)`, `sth`, `l`, `EL reg sth.int_beg`,
                   `forced`, `reg`, `col`, `forbidden`, `mincol`] assume_tac color_register_invariants >>
      rfs [] >>
      metis_tac []
    )
QED

Theorem st_ex_MAP_colors_sub:
     !l sth.
    EVERY (\r. r < LENGTH sth.colors) l ==>
    st_ex_MAP colors_sub l sth = (Success (MAP (\r. EL r sth.colors) l), sth)
Proof
    Induct_on `l` >> rw (st_ex_MAP_def::msimps)
QED

val phystack_on_stack_def = Define`
    phystack_on_stack l st sth =
      !r. MEM r l /\ is_phy_var r /\ 2*st.colormax <= r ==> st.colormax <= EL r sth.colors
`;

Theorem linear_reg_alloc_step_pass1_invariants:
     !st sth l moves forced_adj forced reg pos mincol.
    ~MEM reg l /\
    good_linear_scan_state st sth l pos forced mincol /\
    pos <= (EL reg sth.int_beg) /\
    reg < LENGTH sth.colors /\
    forbidden_is_from_forced_list forced l reg (the [] (lookup reg forced_adj)) /\
    EVERY (\r. MEM r l) (the [] (lookup reg forced_adj)) /\
    EVERY (\r. r < LENGTH sth.colors) (the [] (lookup reg forced_adj)) /\
    EVERY (\r. r < LENGTH sth.colors) (the [] (lookup reg moves)) /\
    EL reg sth.int_beg <= EL reg sth.int_end ==>
    ?stout sthout. (Success stout, sthout) = linear_reg_alloc_step_pass1 forced_adj moves st reg sth /\
    good_linear_scan_state stout sthout (reg::l) (EL reg sth.int_beg) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r (reg::l)  ==> EL r sthout.colors = EL r sth.colors) /\
    (!r. MEM r l /\ is_phy_var r ==> EL r sthout.colors = EL r sth.colors) /\
    (phystack_on_stack l st sth ==> phystack_on_stack (reg::l) stout sthout) /\
    stout.colormax = st.colormax
Proof
    rw [linear_reg_alloc_step_pass1_def] >>
    simp msimps >>
    qspecl_then [`EL reg sth.int_beg`, `st`, `sth`, `l`, `pos`, `forced`, `mincol`] assume_tac remove_inactive_intervals_invariants >> rfs [] >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>
    `reg < LENGTH sth.int_beg /\ reg < LENGTH sth.int_end` by fs [good_linear_scan_state_def] >>
    Cases_on `is_stack_var reg` >>
    simp []
    THEN1 (
        `!e. ~MEM (e,reg) stout.active` by (CCONTR_TAC >> fs [good_linear_scan_state_def', EVERY_MEM, FORALL_PROD]) >>
        `!(x:int). x <= x` by rw [] >>
        simp [phystack_on_stack_def] >>
        `~is_phy_var reg` by metis_tac [convention_partitions] >>
        metis_tac [spill_register_invariants]
    ) >>

    imp_res_tac st_ex_MAP_colors_sub >>
    `?forbidden. fromAList (MAP (\c. (c,())) (MAP (\r. EL r sth.colors) (the [] (lookup reg forced_adj)))) = forbidden` by simp [] >>
    sg `forbidden_is_from_map_color_forced forced l sth.colors reg forbidden` THEN1 (
      fs [forbidden_is_from_map_color_forced_def, forbidden_is_from_forced_list_def] >>
      rw [domain_fromAList, MEM_MAP, EXISTS_PROD, domain_union] >>
      metis_tac []
    ) >>
    sg `domain forbidden SUBSET {EL r sth.colors | r | MEM r l}` THEN1 (
      rw [domain_fromAList, GSYM MAP_o] >>
      `FST o (\c:num. (c, ())) = I` by simp [FUN_EQ_THM] >>
      ASM_REWRITE_TAC [GSYM MAP_o |> REWRITE_RULE [FUN_EQ_THM, o_THM], o_ASSOC, I_o_ID] >>
      fs [SUBSET_DEF, LIST_TO_SET_MAP, EVERY_MEM] >>
      metis_tac []
    ) >>
    Cases_on `is_phy_var reg` >> simp []

    THEN1 (
      Cases_on `reg < 2*stout.colormax` >> simp []
      THEN1 (
        `domain stout.phyregs SUBSET domain (union stout.phyregs forbidden)` by simp [domain_union] >>
        `domain (union stout.phyregs forbidden) SUBSET {EL r sth.colors | r | MEM r l}` by (fs [domain_union, good_linear_scan_state_def', SUBSET_DEF] >> metis_tac []) >>
        `forbidden_is_from_map_color_forced forced l sth.colors reg (union stout.phyregs forbidden)` by (fs [forbidden_is_from_map_color_forced_def, domain_union] >> metis_tac []) >>
        qspecl_then [`stout`, `sth`, `l`, `[]`, `union stout.phyregs forbidden`, `forced`, `reg`, `T`] assume_tac linear_reg_alloc_step_aux_invariants >>
        rfs [] >>
        simp [phystack_on_stack_def] >>
        `~(2*st.colormax <= reg)` by rw [] >>
        metis_tac []
      )
      THEN1 (
        `!e. ~MEM (e,reg) stout.active` by (CCONTR_TAC >> fs [good_linear_scan_state_def', EVERY_MEM, FORALL_PROD]) >>
        `!(x:int). x <= x` by rw [] >>
        `2*st.colormax <= reg` by rw [] >>
        simp [phystack_on_stack_def] >>
        metis_tac [spill_register_invariants]
      )
    )
    THEN1 (
        qspecl_then [`stout`, `sth`, `l`, `MAP (\r. EL r sth.colors) (the [] (lookup reg moves))`,
                     `forbidden`, `forced`, `reg`, `F`, `mincol`] assume_tac linear_reg_alloc_step_aux_invariants >>
        rfs [] >>
        simp [phystack_on_stack_def] >>
        metis_tac []
    )
QED

Theorem linear_reg_alloc_step_pass2_invariants:
     !st sth l moves forced_adj forced reg pos mincol.
    ~MEM reg l /\
    good_linear_scan_state st sth l pos forced mincol /\
    pos <= (EL reg sth.int_beg) /\
    reg < LENGTH sth.colors /\
    forbidden_is_from_forced_list forced l reg (the [] (lookup reg forced_adj)) /\
    EVERY (\r. MEM r l) (the [] (lookup reg forced_adj)) /\
    EVERY (\r. r < LENGTH sth.colors) (the [] (lookup reg forced_adj)) /\
    EVERY (\r. r < LENGTH sth.colors) (the [] (lookup reg moves)) /\
    EL reg sth.int_beg <= EL reg sth.int_end ==>
    ?stout sthout. (Success stout, sthout) = linear_reg_alloc_step_pass2 forced_adj moves st reg sth /\
    good_linear_scan_state stout sthout (reg::l) (EL reg sth.int_beg) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r (reg::l) ==> EL r sthout.colors = EL r sth.colors) /\
    (!r. MEM r l /\ is_phy_var r ==> EL r sthout.colors = EL r sth.colors) /\
    stout.colormax = st.colormax
Proof
    rw [linear_reg_alloc_step_pass2_def] >>
    simp msimps >>
    qspecl_then [`EL reg sth.int_beg`, `st`, `sth`, `l`, `pos`, `forced`, `mincol`] assume_tac remove_inactive_intervals_invariants >> rfs [] >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>
    `reg < LENGTH sth.int_beg /\ reg < LENGTH sth.int_end` by fs [good_linear_scan_state_def] >>
    imp_res_tac st_ex_MAP_colors_sub >>
    `?forbidden. fromAList (MAP (\c. (c,())) (MAP (\r. EL r sth.colors) (the [] (lookup reg forced_adj)))) = forbidden` by simp [] >>
    sg `forbidden_is_from_map_color_forced forced l sth.colors reg forbidden` THEN1 (
      fs [forbidden_is_from_map_color_forced_def, forbidden_is_from_forced_list_def] >>
      rw [domain_fromAList, MEM_MAP, EXISTS_PROD, domain_union] >>
      metis_tac []
    ) >>
    sg `domain forbidden SUBSET {EL r sth.colors | r | MEM r l}` THEN1 (
      rw [domain_fromAList, GSYM MAP_o] >>
      `FST o (\c:num. (c, ())) = I` by simp [FUN_EQ_THM] >>
      ASM_REWRITE_TAC [GSYM MAP_o |> REWRITE_RULE [FUN_EQ_THM, o_THM], o_ASSOC, I_o_ID] >>
      fs [SUBSET_DEF, LIST_TO_SET_MAP, EVERY_MEM] >>
      metis_tac []
    ) >>
    Cases_on `is_phy_var reg` >> simp []

    THEN1 (
      `domain stout.phyregs SUBSET domain (union stout.phyregs forbidden)` by simp [domain_union] >>
      `domain (union stout.phyregs forbidden) SUBSET {EL r sth.colors | r | MEM r l}` by (fs [domain_union, good_linear_scan_state_def', SUBSET_DEF] >> metis_tac []) >>
      `forbidden_is_from_map_color_forced forced l sth.colors reg (union stout.phyregs forbidden)` by (fs [forbidden_is_from_map_color_forced_def, domain_union] >> metis_tac []) >>
      qspecl_then [`stout`, `sth`, `l`, `[]`, `union stout.phyregs forbidden`, `forced`, `reg`, `F`] assume_tac linear_reg_alloc_step_aux_invariants >>
      rfs []
    )
    THEN1 (
      qspecl_then [`stout`, `sth`, `l`, `MAP (\r. EL r sth.colors) (the [] (lookup reg moves))`,
                   `forbidden`, `forced`, `reg`, `F`] assume_tac linear_reg_alloc_step_aux_invariants >>
      rfs []
    )
QED

(* TODO: move *)
val intbeg_less_def = Define`
    intbeg_less (int_beg : int list) r1 r2 = ($< LEX $<=) (EL r1 int_beg, r1) (EL r2 int_beg, r2)
`;

Theorem intbeg_less_transitive:
     !int_beg. transitive (intbeg_less int_beg)
Proof
    rw [transitive_def, intbeg_less_def, LEX_DEF] >>
    intLib.COOPER_TAC
QED

Theorem intbeg_less_total:
     !int_beg. total (intbeg_less int_beg)
Proof
    rw [total_def, intbeg_less_def, LEX_DEF] >>
    intLib.COOPER_TAC
QED

Theorem st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma:
     !regl st sth l pos b moves forced_adj forced mincol.
    SORTED (intbeg_less sth.int_beg) regl /\
    (!r1 r2. MEM r1 l /\ MEM r2 regl ==> intbeg_less sth.int_beg r1 r2) /\
    ALL_DISTINCT regl /\
    EVERY (\r. ~MEM r regl) l /\
    good_linear_scan_state st sth l pos forced mincol /\
    EVERY (\r. pos <= (EL r sth.int_beg)) regl /\
    EVERY (\r. r < LENGTH sth.colors) regl /\
    (!r. forbidden_is_from_forced_sublist (l++regl) forced sth.int_beg r (the [] (lookup r forced_adj))) /\
    EVERY (\r1,r2. MEM r1 (l ++ regl) /\ MEM r2 (l ++ regl)) forced /\
    (!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 forced_adj))) /\
    (!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 moves))) /\
    EVERY (\r. EL r sth.int_beg <= EL r sth.int_end) regl ==>
    ?stout sthout posout. (Success stout, sthout) = st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
    good_linear_scan_state stout sthout ((REVERSE regl) ++ l) (posout) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r (l++regl) ==> EL r sthout.colors = EL r sth.colors) /\
    (b ==> (phystack_on_stack l st sth ==> phystack_on_stack ((REVERSE regl) ++ l) stout sthout)) /\
    stout.colormax = st.colormax
Proof
    Induct_on `regl`
    THEN1 (
        rw (st_ex_FOLDL_def::msimps) >>
        qexists_tac `pos` >>
        rw []
    ) >>
    rpt gen_tac >> strip_tac >>
    SIMP_TAC std_ss (st_ex_FOLDL_def::msimps) >>
    sg `?stmid sthmid. (if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves st h sth = (Success stmid, sthmid) /\
          good_linear_scan_state stmid sthmid (h::l) (EL h sth.int_beg) forced mincol /\
          LENGTH sthmid.colors = LENGTH sth.colors /\ sthmid.int_beg = sth.int_beg /\ sthmid.int_end = sth.int_end /\
          (!r. ~MEM r (h::l) ==> EL r sthmid.colors = EL r sth.colors) /\
          (b ==> (phystack_on_stack l st sth ==> phystack_on_stack (h::l) stmid sthmid)) /\ stmid.colormax = st.colormax` THEN1 (
        `~MEM h l` by (fs [EVERY_MEM] >> metis_tac []) >>
        sg `EVERY (\r. MEM r l) (the [] (lookup h forced_adj))` THEN1 (
          rw [EVERY_MEM] >>
          fs [forbidden_is_from_forced_sublist_def, GSYM intbeg_less_def] >>
          `r <> h /\ (MEM (r,h) forced \/ MEM (h,r) forced) /\ intbeg_less sth.int_beg r h` by metis_tac [] >>
          `MEM r (l++h::regl)` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>
          `transitive (intbeg_less sth.int_beg)` by simp [intbeg_less_transitive] >>
          fs [SORTED_EQ] >>
          `intbeg_less sth.int_beg h r` by fs [] >>
          CCONTR_TAC >>
          fs [intbeg_less_def, LEX_DEF] >>
          intLib.COOPER_TAC
        ) >>
        sg `forbidden_is_from_forced_list forced l h (the [] (lookup h forced_adj))` THEN1 (
          rw [forbidden_is_from_forced_list_def] >>
          fs [forbidden_is_from_forced_sublist_def, GSYM intbeg_less_def] >>
          `reg2 <> h` by fs [EVERY_MEM] >>
          metis_tac []
        ) >>
        rfs [] >>
        foldl (fn (th, acc) =>
          acc >> (qspecl_then [`st`, `sth`, `l`, `moves`, `forced_adj`, `forced`, `h`, `pos`, `mincol`] assume_tac th)
        ) all_tac [linear_reg_alloc_step_pass1_invariants,linear_reg_alloc_step_pass2_invariants] >>
        rfs [] >>
        metis_tac []
    ) >>
    simp [] >>
    SIMP_TAC pure_ss [GSYM APPEND_ASSOC, APPEND] >>
    `transitive (intbeg_less sth.int_beg)` by simp [intbeg_less_transitive] >>
    `SORTED (intbeg_less sth.int_beg) regl` by fs [SORTED_EQ] >>
    `intbeg_less sthmid.int_beg = intbeg_less sth.int_beg` by simp [FUN_EQ_THM, intbeg_less_def] >>
    `!l forced r adj. forbidden_is_from_forced_sublist l forced sthmid.int_beg r adj = forbidden_is_from_forced_sublist l forced sth.int_beg r adj` by simp [forbidden_is_from_forced_sublist_def] >>
    sg `!r1 r2. MEM r1 (h::l) /\ MEM r2 regl ==> intbeg_less sth.int_beg r1 r2` THEN1 (
        rw []
        THEN1 fs [SORTED_EQ]
        THEN1 (fs [] >> metis_tac [])
    ) >>
    `EVERY (\r. ~MEM r regl) l` by fs [EVERY_MEM] >>
    sg `EVERY (\r. EL h sth.int_beg <= EL r sth.int_beg) regl` THEN1 (
      fs [EVERY_MEM, intbeg_less_def, LEX_DEF] >>
      metis_tac [integerTheory.INT_LE_LT]
    ) >>
    `EVERY (\r1,r2. MEM r1 (h::l ++ regl) /\ MEM r2 (h::l ++ regl)) forced` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>
    `!r. forbidden_is_from_forced_sublist (h::(l ++ regl)) forced sth.int_beg r (the [] (lookup r forced_adj))` by (fs [forbidden_is_from_forced_sublist_def] >> metis_tac []) >>
    qabbrev_tac `toto = !r1 r2. (r1 = h \/ MEM r1 l) /\ MEM r2 regl ==> intbeg_less sth.int_beg r1 r2` >>
    first_x_assum (qspecl_then [`stmid`, `sthmid`, `h::l`, `EL h sth.int_beg`, `b`, `moves`, `forced_adj`, `forced`, `mincol`] assume_tac) >>
    rfs [] >> fs [] >> rfs [] >>
    metis_tac []
QED

Theorem st_ex_FOLDL_linear_reg_alloc_step_passn_invariants:
     !regl st sth pos b moves forced_adj forced mincol.
    SORTED (intbeg_less sth.int_beg) regl /\
    ALL_DISTINCT regl /\
    good_linear_scan_state st sth [] pos forced mincol /\
    EVERY (\r. pos <= (EL r sth.int_beg)) regl /\
    EVERY (\r. r < LENGTH sth.colors) regl /\
    (!r. forbidden_is_from_forced_sublist regl forced sth.int_beg r (the [] (lookup r forced_adj))) /\
    EVERY (\r1,r2. MEM r1 regl /\ MEM r2 regl) forced /\
    (!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 forced_adj))) /\
    (!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 moves))) /\
    EVERY (\r. EL r sth.int_beg <= EL r sth.int_end) regl ==>
    ?stout sthout posout. (Success stout, sthout) = st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2) forced_adj moves) st regl sth /\
    good_linear_scan_state stout sthout (REVERSE regl) (posout) forced mincol /\
    LENGTH sthout.colors = LENGTH sth.colors /\
    sthout.int_beg = sth.int_beg /\ sthout.int_end = sth.int_end /\
    (!r. ~MEM r regl ==> EL r sthout.colors = EL r sth.colors) /\
    (b ==> phystack_on_stack (REVERSE regl) stout sthout) /\
    stout.colormax = st.colormax
Proof
    rpt strip_tac >>
    qspecl_then [`regl`, `st`, `sth`, `[]`, `pos`, `b`] assume_tac st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma >>
    `phystack_on_stack [] st sth` by simp [phystack_on_stack_def] >>
    fs []
QED

Theorem swap_regs_eq:
     !sth i1 i2.
    i1 < LENGTH sth.sorted_regs /\ i2 < LENGTH sth.sorted_regs ==>
    ?sthout. swap_regs i1 i2 sth = (Success (), sthout) /\
    sthout = sth with sorted_regs := LUPDATE (EL i1 sth.sorted_regs) i2 (LUPDATE (EL i2 sth.sorted_regs) i1 sth.sorted_regs)
Proof
    rw (swap_regs_def::msimps)
QED

(* TODO: move *)
Theorem if_thm:
     !b x y z. (if b then x else y) = z <=> ((b /\ x = z) \/ (~b /\ y=z))
Proof
    rw []
QED

Theorem split_at_indice_sing:
     !l i.
    i < LENGTH l ==>
    ?l1 x l2. l = l1 ++ [x] ++ l2 /\ LENGTH l1 = i
Proof
    Induct_on `l` >>
    rw [] >>
    Cases_on `i` THEN1 (
        qexists_tac `[]` >>
        qexists_tac `h` >>
        qexists_tac `l` >>
        rw []
    ) >>
    fs [] >>
    first_x_assum (qspec_then `n` assume_tac) >>
    rfs [] >>
    qexists_tac `h::l1` >>
    qexists_tac `x` >>
    qexists_tac `l2` >>
    rw []
QED

Theorem split_at_indice:
     !l i.
    i <= LENGTH l ==>
    ?l1 l2. l = l1 ++ l2 /\ LENGTH l1 = i
Proof
    Induct_on `l` >>
    rw [] >>
    Cases_on `i` THEN1 (
        qexists_tac `[]` >>
        qexists_tac `h::l` >>
        rw []
    ) >>
    fs [] >>
    first_x_assum (qspec_then `n` assume_tac) >>
    rfs [] >>
    qexists_tac `h::l1` >>
    qexists_tac `l2` >>
    rw []
QED

Theorem swap_perm_lemma:
     !l i1 i2.
    i1 < LENGTH l /\
    i2 < LENGTH l ==>
    PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))
Proof
    rw [] >>
    Cases_on `i1 = i2`
    THEN1 fs [LUPDATE_SAME] >>
    rpt (first_x_assum mp_tac) >> simp [] >>
    wlog_tac `i1 < i2` []
    THEN1 (
        rw [] >>
        `i2 < i1` by rw [] >>
        `i2 < LENGTH l` by rw [] >>
        metis_tac [LUPDATE_commutes]
    ) >>
    rw [] >>
    `?l1 y l2. l = l1 ++ [y] ++ l2 /\ LENGTH l1 = i2` by rw [split_at_indice_sing] >>
    `?l11 x l12. l1 = l11 ++ [x] ++ l12 /\ LENGTH l11 = i1` by rw [split_at_indice_sing] >>
    rveq >>
    rfs [] >>
    REWRITE_TAC [GSYM APPEND_ASSOC] >>
    REWRITE_TAC [el_append3 |> REWRITE_RULE [GSYM APPEND_ASSOC]] >>
    REWRITE_TAC [lupdate_append2 |> REWRITE_RULE [GSYM APPEND_ASSOC]] >>
    REWRITE_TAC [APPEND_ASSOC] >>
    `LENGTH l11 + (LENGTH l12 + 1) = LENGTH (l11 ++ [x] ++ l12)` by rw [] >>
    ASM_REWRITE_TAC [] >>
    REWRITE_TAC [el_append3] >>
    `LENGTH (l11 ++ [x] ++ l12) = LENGTH (l11 ++ [y] ++ l12)` by REWRITE_TAC [LENGTH_APPEND, LENGTH] >>
    ASM_REWRITE_TAC [] >>
    REWRITE_TAC [lupdate_append2] >>
    metis_tac [PERM_APPEND, PERM_APPEND_IFF, APPEND_ASSOC]
QED

Theorem LUPDATE_TAKE:
     !n x y l. x < n /\ n <= LENGTH l ==> TAKE n (LUPDATE y x l) = LUPDATE y x (TAKE n l)
Proof
    Induct_on `l` >>
    rw [] >>
    simp [LIST_EQ_REWRITE] >>
    Cases >>
    rw [EL_TAKE, EL_LUPDATE]
QED

Theorem swap_regs_perm:
     !sth i1 i2 sthout.
    swap_regs i1 i2 sth = (Success (), sthout) ==>
    (!n. i1 < n /\ i2 < n /\ n <= LENGTH sth.sorted_regs ==> PERM (TAKE n sth.sorted_regs) (TAKE n sthout.sorted_regs))
Proof
    rw (swap_regs_def::msimps) >>
    fs [case_eq_thms] >> fs [if_thm] >>
    fs [linear_scan_hidden_state_component_equality] >>
    qpat_x_assum `_ = sthout.sorted_regs` (fn th => assume_tac (GSYM th)) >>
    `let l = TAKE n sth.sorted_regs in PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))` by simp [swap_perm_lemma] >>
    rfs [EL_TAKE, LUPDATE_TAKE]
QED

Theorem partition_regs_correct:
     !l rpiv begrpiv r sth.
    (!i. l <= i /\ i < r ==> EL i sth.sorted_regs < LENGTH sth.int_beg) /\
    l <= LENGTH sth.sorted_regs /\
    r <= LENGTH sth.sorted_regs ==>
    ?mid sthout. partition_regs l rpiv begrpiv r sth = (Success mid, sthout) /\
    sthout = sth with sorted_regs := sthout.sorted_regs /\
    LENGTH sthout.sorted_regs = LENGTH sth.sorted_regs /\
    (l <= r ==> l <= mid /\ mid <= r) /\
    (!n. l <= n /\ r <= n /\ n <= LENGTH sth.sorted_regs ==> PERM (TAKE n sth.sorted_regs) (TAKE n sthout.sorted_regs)) /\
    (!ind. ind < l \/ r <= ind ==> EL ind sthout.sorted_regs = EL ind sth.sorted_regs) /\
    (!ind. l <= ind /\ ind < mid ==>
        let reg = EL ind sthout.sorted_regs in
        ($< LEX $<=) (EL reg sth.int_beg, reg) (begrpiv, rpiv)) /\
    (!ind. mid <= ind /\ ind < r ==>
        let reg = EL ind sthout.sorted_regs in
        ($< LEX $<=) (begrpiv, rpiv) (EL reg sth.int_beg, reg))
Proof
    recInduct partition_regs_ind >>
    rpt strip_tac >>
    once_rewrite_tac [partition_regs_def] >>
    rw msimps
    THEN1 rw [linear_scan_hidden_state_component_equality] >>
    CASE_TAC
    THEN1 (
      fs [] >> (
        rpt (first_x_assum (qspecl_then [`EL (EL l sth.sorted_regs) sth.int_beg`, `EL l sth.sorted_regs`] assume_tac)) >>
        rfs [] >>
        first_x_assum (qspec_then `sth` assume_tac) >>
        rfs [] >>
        fs [linear_scan_hidden_state_component_equality] >>
        strip_tac >> gen_tac >>
        rpt (first_x_assum (qspec_then `ind` assume_tac))
        THEN1 rw []
        THEN1 (
          rpt strip_tac >>
          fs [LEX_DEF] >>
          Cases_on `l = ind` >>
          fs []
        )
      )
    )

    THEN1 (
      fs [] >> (
        rpt (first_x_assum (qspecl_then [`EL (EL l sth.sorted_regs) sth.int_beg`, `EL l sth.sorted_regs`] assume_tac)) >>
        rfs [] >>
        qspecl_then [`sth`, `l`, `r-1`] assume_tac swap_regs_eq >>
        rfs [] >>
        first_x_assum (qspec_then `sth with sorted_regs := LUPDATE (EL l sth.sorted_regs) (r-1) (LUPDATE (EL (r-1) sth.sorted_regs) l sth.sorted_regs)` mp_tac) >>
        impl_tac THEN1 rw [EL_LUPDATE] >>
        rw [] >>
        asm_exists_tac >> simp [] >>
        fs [linear_scan_hidden_state_component_equality] >>
        strip_tac THEN1 (
            rw [] >>
            imp_res_tac swap_regs_perm >>
            rpt (first_x_assum (qspec_then `n` assume_tac)) >>
            rfs [] >>
            metis_tac [PERM_TRANS]
        ) >>
        strip_tac >> gen_tac >>
        rpt (first_x_assum (qspec_then `ind` assume_tac))
        THEN1 fs [EL_LUPDATE]
        THEN1 (
          rpt strip_tac >>
          fs [LEX_DEF] >>
          reverse (Cases_on `ind = r-1`)
          THEN1 fs [] >>
          fs [EL_LUPDATE] >>
          rfs [] >>
          simp [] >>
          qabbrev_tac `a = EL (EL l sth.sorted_regs) sth.int_beg` >>
          intLib.COOPER_TAC
        )
      )
    )
QED

Theorem PERM_EVERY_EQ:
     !P l1 l2.
    PERM l1 l2 ==>
    (EVERY P l1 <=> EVERY P l2)
Proof
    rw [EVERY_MEM] >>
    eq_tac >> rw [] >>
    imp_res_tac PERM_MEM_EQ >>
    rw []
QED

Theorem qsort_regs_prop_lemma:
     !(P : num -> bool) l1 l2 l r.
    l <= LENGTH l1 /\
    r <= LENGTH l1 /\
    (!ind. ind < l \/ r <= ind ==> EL ind l2 = EL ind l1) /\
    (!ind. l <= ind /\ ind < r ==> P (EL ind l1)) /\
    PERM l1 l2 ==>
    (!ind. l <= ind /\ ind < r ==> P (EL ind l2))
Proof
    rpt gen_tac >> strip_tac >>
    imp_res_tac PERM_LENGTH >>
    reverse (Cases_on `l <= r`) THEN1 fs [] >>
    `?l1_12 l1_3. l1 = l1_12 ++ l1_3 /\ LENGTH l1_12 = r` by metis_tac [split_at_indice] >>
    `?l1_1 l1_2. l1_12 = l1_1 ++ l1_2 /\ LENGTH l1_1 = l` by metis_tac [split_at_indice] >>
    `?l2_12 l2_3. l2 = l2_12 ++ l2_3 /\ LENGTH l2_12 = r` by metis_tac [split_at_indice] >>
    `?l2_1 l2_2. l2_12 = l2_1 ++ l2_2 /\ LENGTH l2_1 = l` by metis_tac [split_at_indice] >>
    rveq >>
    fs [] >>
    sg `l1_1 = l2_1` THEN1 (
        rw [LIST_EQ_REWRITE] >>
        fs [EL_APPEND_EQN] >>
        rpt (first_x_assum (qspec_then `x` assume_tac)) >>
        rfs []
    ) >>
    sg `l1_3 = l2_3` THEN1 (
        rw [LIST_EQ_REWRITE] >>
        fs [EL_APPEND_EQN] >>
        rpt (first_x_assum (qspec_then `x + LENGTH l1_1 + LENGTH l2_2` assume_tac)) >>
        fs []
    ) >>
    rveq >> fs [] >>
    `PERM l1_2 l2_2` by metis_tac [PERM_APPEND_IFF] >>
    sg `EVERY P l1_2` THEN1 (
        rw [EVERY_EL] >>
        fs [EL_APPEND_EQN] >>
        first_x_assum (qspec_then `n + LENGTH l1_1` assume_tac) >>
        rfs []
    ) >>
    `EVERY P l2_2` by metis_tac [PERM_EVERY_EQ] >>
    fs [EVERY_EL] >>
    rw [] >>
    fs [EL_APPEND_EQN]
QED

Theorem qsort_regs_correct:
     !l r sth.
    (!i. l <= i /\ i < r ==> EL i sth.sorted_regs < LENGTH sth.int_beg) /\
    l <= LENGTH sth.sorted_regs /\
    r <= LENGTH sth.sorted_regs ==>
    ?sthout. qsort_regs l r sth = (Success (), sthout) /\
    sthout = sth with sorted_regs := sthout.sorted_regs /\
    LENGTH sthout.sorted_regs = LENGTH sth.sorted_regs /\
    (!n. l <= n /\ r <= n /\ n <= LENGTH sth.sorted_regs ==> PERM (TAKE n sth.sorted_regs) (TAKE n sthout.sorted_regs)) /\
    (!ind. ind < l \/ r <= ind ==> EL ind sthout.sorted_regs = EL ind sth.sorted_regs) /\
    (!i1 i2. l <= i1 /\ i1 <= i2 /\ i2 < r ==>
      let reg1 = EL i1 sthout.sorted_regs in
      let reg2 = EL i2 sthout.sorted_regs in
        ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)
    )
Proof
    recInduct qsort_regs_ind >>
    rpt strip_tac >>
    once_rewrite_tac [qsort_regs_def] >>
    rw msimps
    THEN1 rw [linear_scan_hidden_state_component_equality]
    THEN1 (
      `i1 = i2` by rw [] >>
      simp [LEX_DEF]
    ) >>
    imp_res_tac EVERY_EL >> fs [] >>
    qspecl_then [`l+1`, `EL l sth.sorted_regs`, `EL (EL l sth.sorted_regs) sth.int_beg`, `r`, `sth`] assume_tac partition_regs_correct >>
    rfs [] >>
    rename1 `partition_regs _ _ _ _ _ = (_, sthpart)` >>
    qspecl_then [`sthpart`, `l`, `mid-1`] assume_tac swap_regs_eq >>
    rfs [] >>

    `PERM sth.sorted_regs sthpart.sorted_regs` by (
        first_x_assum (qspec_then `LENGTH sth.sorted_regs` assume_tac) >>
        rfs [] >>
        metis_tac [TAKE_LENGTH_ID]
    ) >>
    sg `!i. l <= i /\ i < r ==> EL i sthpart.sorted_regs < LENGTH sth.int_beg` THEN1 (
      qspecl_then [`\reg. reg < LENGTH sth.int_beg`, `sth.sorted_regs`, `sthpart.sorted_regs`, `l`, `r`] mp_tac qsort_regs_prop_lemma >>
      impl_tac >> rw [] >> rw []
    ) >>

    simp [] >>
    `?sthswap. sthpart with sorted_regs := LUPDATE (EL l sth.sorted_regs) (mid - 1) (LUPDATE (EL (mid - 1) sthpart.sorted_regs) l sthpart.sorted_regs) = sthswap` by simp [] >>
    simp [] >> fs [linear_scan_hidden_state_component_equality] >>
    `LENGTH sthswap.sorted_regs = LENGTH sthpart.sorted_regs` by metis_tac[LENGTH_LUPDATE] >>

    NTAC 2 (last_x_assum (qspec_then `mid` assume_tac)) >>
    rfs [] >>

    sg `!i. l <= i /\ i < r ==> EL i sthswap.sorted_regs < LENGTH sth.int_beg` THEN1 (
        qpat_x_assum `_ = sthswap.sorted_regs` (fn th => assume_tac (GSYM th)) >>
        rw [EL_LUPDATE]
    ) >>
    imp_res_tac swap_regs_perm >> fs [] >>
    `PERM sthpart.sorted_regs sthswap.sorted_regs` by (
        first_x_assum (qspec_then `LENGTH sth.sorted_regs` assume_tac) >>
        rfs [] >>
        metis_tac [TAKE_LENGTH_ID]
    ) >>
    `PERM sth.sorted_regs sthswap.sorted_regs` by metis_tac [PERM_TRANS] >>
    last_x_assum (qspec_then `sthswap` assume_tac) >>
    rfs [] >>
    rename1 `qsort_regs _ _ _ = (_, sthqsort)` >>
    `PERM sthswap.sorted_regs sthqsort.sorted_regs` by (
        first_x_assum (qspec_then `LENGTH sth.sorted_regs` assume_tac) >>
        rfs [] >>
        metis_tac [TAKE_LENGTH_ID]
    ) >>

    sg `!i. l <= i /\ i < r ==> EL i sthqsort.sorted_regs < LENGTH sth.int_beg` THEN1 (
      qspecl_then [`\reg. reg < LENGTH sth.int_beg`, `sthswap.sorted_regs`, `sthqsort.sorted_regs`, `l`, `r`] mp_tac qsort_regs_prop_lemma >>
      impl_tac >> rw [] >> rw []
    ) >>
    `LENGTH sthqsort.sorted_regs = LENGTH sthswap.sorted_regs` by simp [PERM_LENGTH] >>
    last_x_assum (qspec_then `sthqsort` assume_tac) >>
    rfs [] >>

    `!ind. ind < l ==> ind < mid` by simp [] >>
    `!ind. r <= ind ==> mid <= ind+1` by simp [] >>
    `!ind. ind < l ==> ind < l+1` by simp [] >>
    sg `!ind. ind < l \/ r <= ind ==> EL ind sthpart.sorted_regs = EL ind sthswap.sorted_regs` THEN1 (
        qpat_x_assum `LUPDATE _ _ _ = sthswap.sorted_regs` (fn th => assume_tac (GSYM th)) >>
        rw [EL_LUPDATE]
    ) >>
    strip_tac
    THEN1 (
        rw [] >>
        rpt (first_x_assum (qspec_then `n` assume_tac)) >>
        rfs [] >>
        metis_tac [PERM_TRANS]
    ) >>
    strip_tac
    THEN1 metis_tac [] >>

    sg `
    let rpiv = EL (mid-1) sthswap.sorted_regs in
    let begrpiv = EL rpiv sthswap.int_beg in
    !ind.
    (l <= ind /\ ind < mid-1 ==>
        let reg = EL ind sthswap.sorted_regs in
        ($< LEX $<=) (EL reg sthswap.int_beg, reg) (begrpiv, rpiv)) /\
    (mid <= ind /\ ind < r ==>
        let reg = EL ind sthswap.sorted_regs in
        ($< LEX $<=) (begrpiv, rpiv) (EL reg sthswap.int_beg, reg))`
    THEN1 (
        simp [] >> gen_tac >>
        qpat_x_assum `LUPDATE _ _ _ = sthswap.sorted_regs` (fn th => assume_tac (GSYM th)) >>
        rw [EL_LUPDATE]
    ) >>
    fs [] >>
    `PERM sthqsort.sorted_regs sthout.sorted_regs` by (
        rpt (first_x_assum (qspec_then `LENGTH sth.sorted_regs` assume_tac)) >>
        rfs [] >>
        metis_tac [TAKE_LENGTH_ID]
    ) >>
    `LENGTH sthout.sorted_regs = LENGTH sthqsort.sorted_regs` by simp [PERM_LENGTH] >>

    sg `!ind. mid <= ind /\ ind < r ==>
        let reg1 = EL (mid-1) sthout.sorted_regs in
        let reg2 = EL ind sthout.sorted_regs in
          ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)`
    THEN1 (
      rw [] >>
      sg `
        let reg1 = EL (mid-1) sthqsort.sorted_regs in
        let reg2 = EL ind sthqsort.sorted_regs in
          ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)`
      THEN1 (
        rw [] >>
        `mid <= (mid-1)+1` by simp [] >>
        metis_tac []
      ) >>
      qspecl_then [`\reg. ($< LEX $<=) (EL (EL (mid-1) sthswap.sorted_regs) sthswap.int_beg, EL (mid-1) sthswap.sorted_regs) (EL reg sthswap.int_beg, reg)`,
                   `sthqsort.sorted_regs`, `sthout.sorted_regs`, `mid`, `r`] mp_tac qsort_regs_prop_lemma >>
      impl_tac THEN1 ( rw [] >> metis_tac [] ) >>
      rw []
    ) >>

    sg `!ind. l <= ind /\ ind < mid-1 ==>
        let reg1 = EL ind sthout.sorted_regs in
        let reg2 = EL (mid-1) sthout.sorted_regs in
          ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)`
    THEN1 (
      rw [] >>
      qspecl_then [`\reg. ($< LEX $<=) (EL reg sthswap.int_beg, reg) (EL (EL (mid-1) sthswap.sorted_regs) sthswap.int_beg, EL (mid-1) sthswap.sorted_regs)`,
                   `sthswap.sorted_regs`, `sthqsort.sorted_regs`, `l`, `mid-1`] mp_tac qsort_regs_prop_lemma >>
      impl_tac THEN1 ( rw [] >> metis_tac [] ) >>
      rw []
    ) >>

    rw [] >>
    Cases_on `i1 <= mid-1` >>
    Cases_on `i1 = mid-1` >>
    Cases_on `i2 <= mid-1` >>
    Cases_on `i2 = mid-1` >>
    fs []
    THEN1 simp [LEX_DEF]
    THEN1 rfs []
    THEN1 rfs []
    THEN1 (
      `i1 < mid-1` by simp [] >>
      `mid <= i2` by simp [] >>
      ` let reg1 = EL i1 sthqsort.sorted_regs in
        let reg2 = EL (mid-1) sthout.sorted_regs in
          ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)` by rfs [] >>
      ` let reg1 = EL (mid-1) sthout.sorted_regs in
        let reg2 = EL i2 sthout.sorted_regs in
          ($< LEX $<=) (EL reg1 sth.int_beg, reg1) (EL reg2 sth.int_beg, reg2)` by metis_tac [] >>
      fs [] >>
      qabbrev_tac `a = EL i1 sthqsort.sorted_regs` >>
      qabbrev_tac `b = EL (mid-1) sthout.sorted_regs` >>
      qabbrev_tac `c = EL i2 sthout.sorted_regs` >>
      rpt (qpat_x_assum `($< LEX $<=) _ _` mp_tac) >>
      rpt (first_x_assum kall_tac) >>
      rw [LEX_DEF] >>
      intLib.COOPER_TAC
    )
QED

Theorem swap_moves_eq:
     !sth i1 i2.
    i1 < LENGTH sth.sorted_moves /\ i2 < LENGTH sth.sorted_moves ==>
    ?sthout. swap_moves i1 i2 sth = (Success (), sthout) /\
    sthout = sth with sorted_moves := LUPDATE (EL i1 sth.sorted_moves) i2 (LUPDATE (EL i2 sth.sorted_moves) i1 sth.sorted_moves)
Proof
    rw (swap_moves_def::msimps)
QED

Theorem swap_moves_correct:
     !sth i1 i2.
    i1 < LENGTH sth.sorted_moves /\ i2 < LENGTH sth.sorted_moves ==>
    ?sthout. swap_moves i1 i2 sth = (Success (), sthout) /\
    sthout = sth with sorted_moves := sthout.sorted_moves /\
    LENGTH sthout.sorted_moves = LENGTH sth.sorted_moves /\
    (!n. i1 < n /\ i2 < n /\ n <= LENGTH sth.sorted_moves ==> PERM (TAKE n sth.sorted_moves) (TAKE n sthout.sorted_moves))
Proof
    rw (swap_moves_def::msimps) >>
    fs [case_eq_thms] >> fs [if_thm] >>
    `let l = TAKE n sth.sorted_moves in PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))` by simp [swap_perm_lemma] >>
    rfs [EL_TAKE, LUPDATE_TAKE]
QED

Theorem partition_moves_correct:
     !l ppiv r sth.
    l <= LENGTH sth.sorted_moves /\
    r <= LENGTH sth.sorted_moves ==>
    ?mid sthout. partition_moves l ppiv r sth = (Success mid, sthout) /\
    (l <= r ==> l <= mid /\ mid <= r) /\
    sthout = sth with sorted_moves := sthout.sorted_moves /\
    LENGTH sthout.sorted_moves = LENGTH sth.sorted_moves /\
    (!n. l <= n /\ r <= n /\ n <= LENGTH sth.sorted_moves ==> PERM (TAKE n sth.sorted_moves) (TAKE n sthout.sorted_moves))
Proof
    recInduct partition_moves_ind >>
    rw [] >>
    once_rewrite_tac [partition_moves_def] >>
    rw msimps
    THEN1 rw [linear_scan_hidden_state_component_equality] >>
    rpt (first_x_assum (qspec_then `EL l sth.sorted_moves` assume_tac)) >>
    rfs [] >>
    CASE_TAC >> fs []
    THEN1 (
      first_x_assum (qspec_then `sth` assume_tac) >>
      rfs []
    ) >>
    qspecl_then [`sth`, `l`, `r-1`] assume_tac swap_moves_correct >>
    rfs [] >>
    first_x_assum (qspec_then `sthout` assume_tac) >>
    rfs [] >>
    fs [linear_scan_hidden_state_component_equality] >>
    rw [] >>
    rpt (first_x_assum (qspec_then `n` assume_tac)) >>
    rfs [] >>
    metis_tac [PERM_TRANS]
QED

Theorem qsort_moves_correct:
     !l r sth.
    l <= LENGTH sth.sorted_moves /\
    r <= LENGTH sth.sorted_moves ==>
    ?sthout. qsort_moves l r sth = (Success (), sthout) /\
    sthout = sth with sorted_moves := sthout.sorted_moves /\
    LENGTH sthout.sorted_moves = LENGTH sth.sorted_moves /\
    (!n. l <= n /\ r <= n /\ n <= LENGTH sth.sorted_moves ==> PERM (TAKE n sth.sorted_moves) (TAKE n sthout.sorted_moves))
Proof
    recInduct qsort_moves_ind >>
    rw [] >>
    once_rewrite_tac [qsort_moves_def] >>
    rw msimps
    THEN1 rw [linear_scan_hidden_state_component_equality] >>
    qspecl_then [`l+1`, `FST (EL l sth.sorted_moves)`, `r`, `sth`] assume_tac partition_moves_correct >>
    rfs [] >>
    rename1 `partition_moves _ _ _ _ = (_, sthpart)` >>
    qspecl_then [`sthpart`, `l`, `mid-1`] assume_tac swap_moves_correct >>
    rfs [] >>
    rename1 `swap_moves _ _ _ = (_, sthswap)` >>
    rpt (qpat_x_assum `!m. _ /\ _ /\ _ ==> !sth. _` (qspec_then `mid` assume_tac)) >>
    rfs [] >>
    first_x_assum (qspec_then `sthswap` assume_tac) >>
    rfs [] >>
    rename1 `qsort_moves _ _ _ = (_, sthqsort)` >>
    first_x_assum (qspec_then `sthqsort` assume_tac) >>
    rfs [] >>
    fs [linear_scan_hidden_state_component_equality] >>
    rw [] >>
    rpt (first_x_assum (qspec_then `n` assume_tac)) >>
    rfs [] >>
    metis_tac [PERM_TRANS]
QED


Theorem list_minimum:
     !f (l:num list). ?(x:int). EVERY (\y. x <= f y) l
Proof
    gen_tac >> Induct_on `l` >>
    rw [] >>
    Cases_on `x <= f h`
    THEN1 (
      qexists_tac `x` >>
      rw []
    )
    THEN1 (
      qexists_tac `f h` >>
      fs [EVERY_MEM] >>
      rw [] >> res_tac >>
      intLib.COOPER_TAC
    )
QED

Theorem linear_reg_alloc_pass1_initial_state_invariants:
     !sth reglist forced k st.
    LENGTH sth.int_beg = LENGTH sth.colors /\ LENGTH sth.int_end = LENGTH sth.colors ==>
    ?pos.
    good_linear_scan_state (linear_reg_alloc_pass1_initial_state k) sth [] pos forced 0 /\
    EVERY (\r. pos <= EL r sth.int_beg) reglist
Proof
    rw [good_linear_scan_state_def', linear_reg_alloc_pass1_initial_state_def] >> rw [] >>
    qspecl_then [`\r. EL r sth.int_beg`, `reglist`] assume_tac list_minimum >>
    fs [] >>
    qexists_tac `x` >> rw [] >>
    Induct_on `forced` >> rw [] >>
    pairarg_tac >> rw []
QED

Theorem linear_reg_alloc_pass2_initial_state_invariants:
     !sth reglist forced k nreg st.
    LENGTH sth.int_beg = LENGTH sth.colors /\ LENGTH sth.int_end = LENGTH sth.colors ==>
    ?pos.
    good_linear_scan_state (linear_reg_alloc_pass2_initial_state k nreg) sth [] pos forced k /\
    EVERY (\r. pos <= EL r sth.int_beg) reglist
Proof
    rw [good_linear_scan_state_def', linear_reg_alloc_pass2_initial_state_def] >> rw [] >>
    qspecl_then [`\r. EL r sth.int_beg`, `reglist`] assume_tac list_minimum >>
    fs [] >>
    qexists_tac `x` >> rw [] >>
    Induct_on `forced` >> rw [] >>
    pairarg_tac >> rw []
QED

Theorem st_ex_FILTER_good_stack:
     !reglist sth k.
    EVERY (\r. r < LENGTH sth.colors) reglist ==>
    st_ex_FILTER_good (\r.
      do
        col <- colors_sub r;
        return (is_stack_var r \/ k <= col);
      od
    ) reglist sth =
    (Success (FILTER (\r. is_stack_var r \/ k <= EL r sth.colors) reglist), sth)
Proof
    simp msimps >>
    Induct_on `reglist` >>
    rw (st_ex_FILTER_good_def::msimps)
QED

Theorem lookup_fromAList_MAP_not_NONE:
     !r l. lookup r (fromAList (MAP (\r. (r,())) l)) <> NONE <=> MEM r l
Proof
    rw [] >>
    Cases_on `lookup r (fromAList (MAP (\r. (r,())) l))` >> fs []
    THEN1 fs [lookup_NONE_domain, domain_fromAList, MEM_MAP, FORALL_PROD]
    THEN1 (
      `r IN domain (fromAList (MAP (\r. (r,())) l))` by fs [domain_lookup] >>
      fs [domain_fromAList, MEM_MAP, EXISTS_PROD]
    )
QED

Theorem PERM_PARTITION:
     !P l. PERM l ((FILTER (\x. P x) l) ++ (FILTER (\x. ~P x) l))
Proof
    rw [PERM_DEF, FILTER_APPEND, FILTER_FILTER] >>
    simp [METIS_PROVE [] ``!a b. a=b /\ P b <=> a=b /\ P a``] >>
    Cases_on `P x` >>
    simp [] >>
    metis_tac [FUN_EQ_THM]
QED

Theorem forbidden_is_from_forced_take_sublist:
     EVERY (\r1,r2. MEM r1 l /\ MEM r2 l) forced /\
    (!r. forbidden_is_from_forced forced int_beg r (the [] (lookup r forced_adj))) ==>
    (!r. forbidden_is_from_forced_sublist l forced int_beg r (the [] (lookup r forced_adj)))
Proof
    rw [forbidden_is_from_forced_def, forbidden_is_from_forced_sublist_def, GSYM intbeg_less_def, EVERY_MEM, FORALL_PROD] >>
    metis_tac []
QED

Theorem good_linear_scan_state_REVERSE:
     !st sth l pos forced mincol.
    good_linear_scan_state st sth (REVERSE l) pos forced mincol <=>
    good_linear_scan_state st sth l pos forced mincol
Proof
    rw [good_linear_scan_state_def'] >>
    eq_tac >>
    rw [EVERY_REVERSE, FILTER_REVERSE, MAP_REVERSE, ALL_DISTINCT_REVERSE]
QED

Theorem phystack_on_stack_REVERSE:
     !l st sth. phystack_on_stack (REVERSE l) st sth <=> phystack_on_stack l st sth
Proof
    rw [phystack_on_stack_def]
QED

Theorem FILTER_remove_MEM_l:
     !P l. FILTER (\x. P x /\ MEM x l) l = FILTER (\x. P x) l
Proof
    sg `!P l1 l2. (!x. MEM x l1 ==> MEM x l2) ==> FILTER (\x. P x /\ MEM x l2) l1 = FILTER (\x. P x) l1` THEN1 (
        Induct_on `l1` >> rw []
    ) >>
    metis_tac []
QED

Theorem le_div_2:
     !k r. k <= r DIV 2 <=> 2*k <= r
Proof
    intLib.COOPER_TAC
QED

Theorem lt_div_2:
     !k r. r DIV 2 < k <=> r < 2*k
Proof
    intLib.COOPER_TAC
QED

Theorem list_to_sorted_regs_correct:
     !l n sth.
    n + LENGTH l <= LENGTH sth.sorted_regs ==>
    ?sthout. (Success (), sthout) = list_to_sorted_regs l n sth /\
    LENGTH sthout.sorted_regs = LENGTH sth.sorted_regs /\
    sthout = sth with sorted_regs := sthout.sorted_regs /\
    TAKE n sthout.sorted_regs = TAKE n sth.sorted_regs /\
    TAKE (LENGTH l) (DROP n sthout.sorted_regs) = l
Proof
    Induct_on `l` >>
    rw (linear_scan_hidden_state_component_equality::list_to_sorted_regs_def::msimps)
    THEN1 (
      qexists_tac `sth` >>
      rw []
    ) >>
    first_x_assum (qspecl_then [`n+1`, `sth with sorted_regs := LUPDATE h n sth.sorted_regs`] assume_tac) >>
    rfs [] >>
    asm_exists_tac >> simp [] >>
    strip_tac
    THEN1 fs [linear_scan_hidden_state_component_equality] >>
    strip_tac
    THEN1 (
      fs [LIST_EQ_REWRITE] >> rw [] >>
      rfs [EL_TAKE, EL_LUPDATE]
    )
    THEN1 (
      fs [LIST_EQ_REWRITE] >>
      rw [] >>
      Cases_on `x`
      THEN1 (
        rfs [EL_TAKE, EL_DROP, EL_LUPDATE]
      ) >>
      rename1 `SUC x < SUC (LENGTH l)` >>
      rpt (first_x_assum (qspec_then `x` assume_tac)) >>
      rfs [EL_TAKE, EL_DROP, ADD1]
    )
QED

Theorem sorted_regs_to_list_correct:
     !n last sth.
    last <= LENGTH sth.sorted_regs ==>
    sorted_regs_to_list n last sth = (Success (TAKE (last-n) (DROP n sth.sorted_regs)), sth)
Proof
    recInduct sorted_regs_to_list_ind >>
    rw [] >>
    once_rewrite_tac [sorted_regs_to_list_def] >>
    rw msimps >>
    fs [] >>
    first_x_assum (qspec_then `sth` assume_tac) >>
    rfs [] >>
    simp [LIST_EQ_REWRITE] >>
    Cases >>
    rw [EL_TAKE, EL_DROP, ADD1]
QED

Theorem list_to_sorted_moves_correct:
     !l n sth.
    n + LENGTH l <= LENGTH sth.sorted_moves ==>
    ?sthout. (Success (), sthout) = list_to_sorted_moves l n sth /\
    LENGTH sthout.sorted_moves = LENGTH sth.sorted_moves /\
    sthout = sth with sorted_moves := sthout.sorted_moves /\
    TAKE n sthout.sorted_moves = TAKE n sth.sorted_moves /\
    TAKE (LENGTH l) (DROP n sthout.sorted_moves) = l
Proof
    Induct_on `l` >>
    rw (linear_scan_hidden_state_component_equality::list_to_sorted_moves_def::msimps)
    THEN1 (
      qexists_tac `sth` >>
      rw []
    ) >>
    first_x_assum (qspecl_then [`n+1`, `sth with sorted_moves := LUPDATE h n sth.sorted_moves`] assume_tac) >>
    rfs [] >>
    asm_exists_tac >> simp [] >>
    strip_tac
    THEN1 fs [linear_scan_hidden_state_component_equality] >>
    strip_tac
    THEN1 (
      fs [LIST_EQ_REWRITE] >> rw [] >>
      rfs [EL_TAKE, EL_LUPDATE]
    )
    THEN1 (
      fs [LIST_EQ_REWRITE] >>
      rw [] >>
      Cases_on `x`
      THEN1 (
        rfs [EL_TAKE, EL_DROP, EL_LUPDATE]
      ) >>
      rename1 `SUC x < SUC (LENGTH l)` >>
      rpt (first_x_assum (qspec_then `x` assume_tac)) >>
      rfs [EL_TAKE, EL_DROP, ADD1]
    )
QED

Theorem sorted_moves_to_list_correct:
     !n last sth.
    last <= LENGTH sth.sorted_moves ==>
    sorted_moves_to_list n last sth = (Success (TAKE (last-n) (DROP n sth.sorted_moves)), sth)
Proof
    recInduct sorted_moves_to_list_ind >>
    rw [] >>
    once_rewrite_tac [sorted_moves_to_list_def] >>
    rw msimps >>
    fs [] >>
    first_x_assum (qspec_then `sth` assume_tac) >>
    rfs [] >>
    simp [LIST_EQ_REWRITE] >>
    Cases >>
    rw [EL_TAKE, EL_DROP, ADD1]
QED

Theorem linear_reg_alloc_intervals_correct:
     !k forced moves reglist_unsorted sth.
    EVERY (\r1,r2. MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted) forced /\
    EVERY (\r1,r2. r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors) (MAP SND moves) /\
    EVERY (\r. r < LENGTH sth.colors) reglist_unsorted /\
    EVERY (\r. EL r sth.int_beg <= EL r sth.int_end) reglist_unsorted /\
    ALL_DISTINCT reglist_unsorted /\
    EVERY (\r. r < LENGTH sth.int_beg) reglist_unsorted /\
    LENGTH sth.colors = LENGTH sth.int_beg /\
    LENGTH sth.int_end = LENGTH sth.int_beg /\
    LENGTH reglist_unsorted <= LENGTH sth.sorted_regs /\
    LENGTH moves <= LENGTH sth.sorted_moves ==>
    ?sthout. linear_reg_alloc_intervals k forced moves reglist_unsorted sth = (Success (), sthout) /\
    (!r1 r2. MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted /\
        interval_intersect (EL r1 sth.int_beg, EL r1 sth.int_end) (EL r2 sth.int_beg, EL r2 sth.int_end) /\
        EL r1 sthout.colors = EL r2 sthout.colors ==>
        r1 = r2
    ) /\
    EVERY (\r.
      if is_phy_var r then
        EL r sthout.colors = r DIV 2
      else if is_stack_var r then
        k <= EL r sthout.colors
      else
        T
    ) reglist_unsorted /\
    EVERY (\r1,r2. EL r1 sthout.colors = EL r2 sthout.colors ==> r1 = r2) forced /\
    LENGTH sthout.colors = LENGTH sth.colors
Proof
    rw (linear_reg_alloc_intervals_def::msimps) >>

    qspecl_then [`reglist_unsorted`, `0`, `sth`] assume_tac list_to_sorted_regs_correct >>
    rfs [linear_scan_hidden_state_component_equality] >>
    rename1 `(Success (), sthm3) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>

    qspecl_then [`0`, `LENGTH reglist_unsorted`, `sthm3`] mp_tac qsort_regs_correct >>
    impl_tac THEN1 (
        rw [] >>
        `EL i sthm3.sorted_regs = EL i (TAKE (LENGTH reglist_unsorted) sthm3.sorted_regs)` by simp [EL_TAKE] >>
        fs [EVERY_EL]
    ) >>
    strip_tac >>
    rename1 `qsort_regs _ _ _ = (Success (), sthm2)` >>
    qpat_x_assum `!n. _ ==> PERM _ _` (qspec_then `LENGTH reglist_unsorted` assume_tac) >>
    fs [] >>

    qspecl_then [`0`, `LENGTH reglist_unsorted`, `sthm2`] assume_tac sorted_regs_to_list_correct >>
    rfs [linear_scan_hidden_state_component_equality] >>
    `?reglist. TAKE (LENGTH reglist_unsorted) sthm2.sorted_regs = reglist` by simp [] >>
    fs [] >>

    qspecl_then [`moves`, `0`, `sthm2`] assume_tac list_to_sorted_moves_correct >>
    rfs [linear_scan_hidden_state_component_equality] >>
    rename1 `(Success (), sthm1) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>

    qspecl_then [`0`, `LENGTH moves`, `sthm1`] mp_tac qsort_moves_correct >>
    impl_tac THEN1 rw [] >>
    strip_tac >>
    rename1 `qsort_moves _ _ _ = (Success (), sth0)` >>
    qpat_x_assum `!n. _ ==> PERM _ _` (qspec_then `LENGTH moves` assume_tac) >>
    fs [] >>

    qspecl_then [`0`, `LENGTH moves`, `sth0`] assume_tac sorted_moves_to_list_correct >>
    rfs [linear_scan_hidden_state_component_equality] >>
    `?sorted_moves. TAKE (LENGTH moves) sth0.sorted_moves = sorted_moves` by simp [] >>
    fs [] >>

    qspecl_then [`(MAP SND sorted_moves)`, `sth0`] mp_tac edges_to_adjlist_output >>
    impl_tac THEN1 metis_tac [PERM_MAP, PERM_EVERY_EQ] >>
    strip_tac >>
    rename1 `edges_to_adjlist _ _ _ = (Success moves_adjlist, _)` >>
    simp [] >>

    qspecl_then [`forced`, `sth0`] mp_tac edges_to_adjlist_output >>
    impl_tac THEN1 (
      fs [EVERY_MEM] >> rw [] >>
      rpt (first_x_assum (qspec_then `e` assume_tac)) >>
      PairCases_on `e` >> rfs []
    ) >>
    strip_tac >>
    rename1 `edges_to_adjlist _ _ _ = (Success forced_adjlist, _)` >>
    rfs [] >>

    `?phyregs. FILTER is_phy_var reglist = phyregs` by simp [] >>
    `?phyphyregs. FILTER (\r. r < 2*k) phyregs = phyphyregs` by simp [] >>
    `?stackphyregs. FILTER (\r. 2*k <= r) phyregs = stackphyregs` by simp [] >>
    simp [] >>

    `?pos. good_linear_scan_state (linear_reg_alloc_pass1_initial_state k) sth0 [] pos forced 0 /\
           EVERY (\r. pos <= EL r sth0.int_beg) reglist` by simp [linear_reg_alloc_pass1_initial_state_invariants] >>
    rfs [] >>

    `!r. MEM r reglist_unsorted <=> MEM r reglist` by simp [PERM_MEM_EQ] >>
    `EVERY (\r. r < LENGTH sth.colors) reglist` by fs [EVERY_MEM] >>
    `EVERY (\r1,r2. MEM r1 reglist /\ MEM r2 reglist) forced` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>

    sg `SORTED (intbeg_less sth.int_beg) reglist` THEN1 (
        fs [GSYM intbeg_less_def] >>
        `transitive (intbeg_less sth.int_beg)` by simp [intbeg_less_transitive] >>
        simp [SORTED_EL_LESS] >>
        qpat_x_assum `_ = reglist` (fn th => assume_tac (GSYM th)) >>
        rw [EL_TAKE]
    ) >>
    (*`total (intbeg_less int_beg)` by simp [intbeg_less_total] >>*)
    `transitive (intbeg_less sth.int_beg)` by simp [intbeg_less_transitive] >>
     `ALL_DISTINCT reglist` by metis_tac [ALL_DISTINCT_PERM] >>
    (*`!r. forbidden_is_from_forced forced sth r (the [] (lookup r forced_adjlist))` by rw [edges_to_adjlist_output] >>*)
    `!r. forbidden_is_from_forced_sublist reglist forced sth.int_beg r (the [] (lookup r forced_adjlist))` by rw [forbidden_is_from_forced_take_sublist] >>
    sg `!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 forced_adjlist))` THEN1 (
      simp [EVERY_MEM] >> rpt strip_tac >>
      `MEM (r1,r2) forced \/ MEM (r2,r1) forced` by metis_tac [forbidden_is_from_forced_def] >>
      `MEM r2 reglist` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>
      fs [EVERY_MEM]
    ) >>
    sg `!r1. EVERY (\r2. r2 < LENGTH sth.colors) (the [] (lookup r1 moves_adjlist))` THEN1 (
      `!r. MEM r (MAP SND sorted_moves) <=> MEM r (MAP SND moves)` by (simp [MEM_MAP] >> metis_tac [PERM_MEM_EQ]) >>
      simp [EVERY_MEM] >> rpt strip_tac >>
      `MEM (r1,r2) (MAP SND sorted_moves) \/ MEM (r2,r1) (MAP SND sorted_moves)` by metis_tac [forbidden_is_from_forced_def] >>
      rfs [] >>
      fs [EVERY_MEM, FORALL_PROD] >>
      metis_tac []
    ) >>
    `EVERY (\r. EL r sth.int_beg <= EL r sth.int_end) reglist` by fs [EVERY_MEM] >>

    qspecl_then [`reglist`, `linear_reg_alloc_pass1_initial_state k`, `sth0`, `pos`, `T`, `moves_adjlist`,
                 `forced_adjlist`, `forced`, `0`] mp_tac st_ex_FOLDL_linear_reg_alloc_step_passn_invariants >>
    simp [] >> strip_tac >> rfs [] >>
    rename1 `(Success st1, sth1) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>

    `ALL_DISTINCT (MAP (\r. EL r sth1.colors) phyregs)` by (fs [good_linear_scan_state_REVERSE, good_linear_scan_state_def'] >> rw []) >>
    qspecl_then [`phyphyregs`, `sth1`, `k`] mp_tac apply_reg_exchange_correct >>
    impl_tac THEN1 (
        strip_tac THEN1 (
          metis_tac [FILTER_IS_SPARSE_SUBLIST, MAP_IS_SPARSE_SUBLIST, ALL_DISTINCT_IS_SPARSE_SUBLIST]
        ) >>
        strip_tac THEN1 (
          REWRITE_TAC [GSYM EVERY_MEM] >> rw [EVERY_FILTER]
        )
        THEN1 (
          rpt strip_tac >>
          `MEM r reglist` by metis_tac [MEM_FILTER] >>
          fs [EVERY_MEM]
        )
    ) >>
    strip_tac >>
    rename1 `(_, sth2) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>

    qspecl_then [`reglist`, `sth2`, `k`] assume_tac (st_ex_FILTER_good_stack |> REWRITE_RULE msimps) >>
    rfs [] >>

    `?stacklist. FILTER (\r. is_stack_var r \/ k <= EL r sth2.colors) reglist = stacklist` by simp [] >>
    `?stackset. fromAList (MAP (\r. (r,())) stacklist) = stackset` by simp [] >>
    `?forced_adjlist'. map (FILTER (\r. lookup r stackset <> NONE)) forced_adjlist = forced_adjlist'` by simp [] >>
    `?moves_adjlist'. map (FILTER (\r. lookup r stackset <> NONE)) moves_adjlist = moves_adjlist'` by simp [] >>
    `?forced'. FILTER (\r1,r2. MEM r1 stacklist /\ MEM r2 stacklist) forced = forced'` by simp [] >>
    simp [] >>

    `?pos2. good_linear_scan_state (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)) sth2 [] pos2 forced' k /\
            EVERY (\r. pos2 <= EL r sth2.int_beg) stacklist` by simp [linear_reg_alloc_pass2_initial_state_invariants] >>

    qspecl_then [`stacklist`, `linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)`, `sth2`, `pos2`, `F`, `moves_adjlist'`,
                 `forced_adjlist'`, `forced'`, `k`] mp_tac st_ex_FOLDL_linear_reg_alloc_step_passn_invariants >>
    impl_tac THEN1 (
      simp [] >>
      strip_tac THEN1 (
        rw [SORTED_FILTER]
      ) >>
      strip_tac THEN1 (
        rw [FILTER_ALL_DISTINCT]
      ) >>
      strip_tac THEN1 (
        rw [EVERY_FILTER_IMP]
      ) >>
      strip_tac THEN1 (
        fs [forbidden_is_from_forced_sublist_def] >>
        rpt strip_tac >>
        eq_tac
        THEN1 (
          strip_tac >> (
            `MEM reg2 stacklist` by (rveq >> fs [MEM_FILTER]) >>
            rveq >>
            simp [lookup_inter, lookup_map, the_OPTION_MAP, MEM_FILTER, lookup_fromAList_MAP_not_NONE] >>
            fs [MEM_FILTER] >>
            metis_tac []
          )
        )
        THEN1 (
          strip_tac >> rveq >>
          fs [lookup_map, the_OPTION_MAP, MEM_FILTER, lookup_fromAList_MAP_not_NONE]
        )
      ) >>
      strip_tac THEN1 (
        rveq >> fs [EVERY_MEM, FORALL_PROD, MEM_FILTER]
      ) >>
      strip_tac THEN1 (
        rveq >> fs [lookup_map, the_OPTION_MAP, EVERY_FILTER_IMP]
      ) >>
      strip_tac THEN1 (
        rveq >> fs [lookup_map, the_OPTION_MAP, EVERY_FILTER_IMP]
      )
      THEN1 (
        rw [EVERY_FILTER_IMP]
      )
    ) >>
    simp [] >> strip_tac >>
    rename1 `(Success st3, sth3) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>
    fs [good_linear_scan_state_REVERSE] >>
    fs [phystack_on_stack_REVERSE] >>
    rpt (qpat_x_assum `good_linear_scan_state _ _ (_ _) _ _ _ _ _` kall_tac) >>
    fs [linear_reg_alloc_pass1_initial_state_def] >>

    `EVERY (\r. k <= EL r sth3.colors) stacklist` by (FULL_SIMP_TAC pure_ss [good_linear_scan_state_def', EVERY_MEM, MEM_APPEND, MEM_MAP] >> metis_tac []) >>
    sg `ALL_DISTINCT (MAP (\r. EL r sth3.colors) phyregs)` THEN1 (
        `ALL_DISTINCT (MAP (\r. EL r sth3.colors) (FILTER is_phy_var stacklist))` by fs [good_linear_scan_state_def'] >>
        sg `ALL_DISTINCT (MAP (\r. EL r sth3.colors) (FILTER (\r. MEM r stacklist) phyregs))` THEN1 (
            rveq >>
            fs [FILTER_FILTER, MEM_FILTER] >>
            simp [METIS_PROVE [] ``!a b c. (a /\ b) /\ c <=> (a /\ c) /\ b``, FILTER_remove_MEM_l] >>
            simp [CONJ_COMM]
        ) >>
        sg `ALL_DISTINCT (MAP (\r. EL r sth2.colors) phyregs)` THEN1 (
            fs [EL_ALL_DISTINCT_EL_EQ] >>
            rpt strip_tac >>
            fs [EL_MAP] >>
            sg `!n. n < LENGTH phyregs ==> EL n phyregs < LENGTH sth.colors` THEN1 (
              rpt strip_tac >>
              `MEM (EL n phyregs) phyregs` by metis_tac [MEM_EL] >>
              `MEM (EL n phyregs) reglist` by (rveq >> fs [MEM_FILTER]) >>
              fs [EVERY_MEM]
            ) >>
            `EL n1 phyregs < LENGTH sth.colors /\ EL n2 phyregs < LENGTH sth.colors` by fs [] >>
            metis_tac []
        ) >>
        sg `ALL_DISTINCT (MAP (\r. EL r sth3.colors) (FILTER (\r. ~MEM r stacklist) phyregs))` THEN1 (
            sg `MAP (\r. EL r sth3.colors) (FILTER (\r. ~MEM r stacklist) phyregs) = MAP (\r. EL r sth2.colors) (FILTER (\r. ~MEM r stacklist) phyregs)` THEN1 (
                qpat_x_assum `!r. ~MEM r stacklist ==> EL r sth3.colors = EL r sth2.colors` mp_tac >>
                rpt (first_x_assum kall_tac) >>
                Induct_on `phyregs` >>
                rw []
            ) >>
            metis_tac [FILTER_IS_SPARSE_SUBLIST, MAP_IS_SPARSE_SUBLIST, ALL_DISTINCT_IS_SPARSE_SUBLIST]
        ) >>
        `!r. MEM r stacklist ==> k <= EL r sth3.colors` by fs [EVERY_MEM] >>
        sg `!r. MEM r reglist /\ ~MEM r stacklist ==> EL r sth3.colors < k` THEN1 (
            rpt strip_tac >>
            fs [] >> rveq >>
            fs [MEM_FILTER] >> fs []
        ) >>
        sg `ALL_DISTINCT (MAP (\r. EL r sth3.colors) (FILTER (\r. MEM r stacklist) phyregs) ++ MAP (\r. EL r sth3.colors) (FILTER (\r. ~MEM r stacklist) phyregs))` THEN1 (
            simp [ALL_DISTINCT_APPEND, MEM_MAP, MEM_FILTER] >>
            rpt strip_tac >>
            CCONTR_TAC >> fs [] >>
            `k <= EL r sth3.colors` by fs [] >>
            `MEM r' reglist` by (rveq >> fs [MEM_FILTER]) >>
            `EL r' sth3.colors < k` by fs [] >>
            fs []
        ) >>
        metis_tac [ALL_DISTINCT_PERM, PERM_PARTITION, PERM_MAP, MAP_APPEND]
    ) >>

    qspecl_then [`stackphyregs`, `sth3`, `k`] mp_tac apply_reg_exchange_correct >>
    impl_tac THEN1 (
        strip_tac THEN1 (
            metis_tac [FILTER_IS_SPARSE_SUBLIST, MAP_IS_SPARSE_SUBLIST, ALL_DISTINCT_IS_SPARSE_SUBLIST]
        ) >>
        strip_tac THEN1 (
            rveq >> fs [MEM_FILTER]
        ) >>
        strip_tac THEN1 (
            rveq >> fs [EVERY_MEM, MEM_FILTER]
        )
    ) >>
    simp [] >> strip_tac >>
    rename1 `(Success st4, sth4) = _` >>
    qpat_x_assum `(_,_) = _` (fn th => assume_tac (GSYM th)) >>
    simp [] >>

    sg `!r. MEM r stackphyregs ==> (k <= EL r sth3.colors <=> k <= r DIV 2)` THEN1 (
        rpt strip_tac >>
        `is_phy_var r` by (rveq >> fs [MEM_FILTER]) >>
        `~is_stack_var r` by metis_tac [convention_partitions] >>
        `2*k <= r` by (rveq >> fs [MEM_FILTER]) >>
        fs [GSYM le_div_2] >>
        Cases_on `MEM r stacklist` >> simp []
        THEN1 (
            fs [EVERY_MEM]
        )
        THEN1 (
            `MEM r reglist` by (rveq >> fs [MEM_FILTER]) >>
            `MEM r phyregs` by (rveq >> fs [MEM_FILTER]) >>
            `!r. MEM r phyphyregs ==> r DIV 2 < k` by (rveq >> rw [MEM_FILTER, lt_div_2]) >>
            fs [le_div_2] >>
            `k <= EL r sth1.colors` by rfs [phystack_on_stack_def] >>
            `r < LENGTH sth.colors` by fs [EVERY_MEM] >>
            sg `!r'. MEM r' phyphyregs ==> EL r sth1.colors <> EL r' sth1.colors` THEN1 (
                `~MEM r phyphyregs` by (rveq >> simp [MEM_FILTER]) >>
                rpt strip_tac >>
                `MEM r' phyregs` by (rveq >> fs [MEM_FILTER]) >>
                `r <> r'` by (CCONTR_TAC >> fs []) >>
                fs [EL_ALL_DISTINCT_EL_EQ, EL_MAP] >>
                fs [MEM_EL] >>
                metis_tac []
            ) >>
            metis_tac []
        )
    ) >>
    sg `!r. MEM r reglist /\ ~MEM r stacklist ==> EL r sth3.colors < k` THEN1 (
      fs [] >>
      rpt strip_tac >>
      `~MEM r (FILTER (\r. is_stack_var r \/ k <= EL r sth2.colors) reglist)` by (rveq >> simp []) >>
      fs [MEM_FILTER] >>
      fs []
    ) >>
    sg `!r. MEM r stackphyregs ==> k <= EL r sth3.colors /\ k <= r DIV 2` THEN1 (
        gen_tac >> strip_tac >>
        `k <= r DIV 2` by (rveq >> fs [MEM_FILTER, le_div_2]) >>
        fs []
    ) >>

    rpt strip_tac
    THEN1 (
        `r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors` by fs [EVERY_MEM] >>
        `EL r1 sth3.colors = EL r2 sth3.colors` by fs [] >>
        Cases_on `MEM r1 stacklist` >>
        Cases_on `MEM r2 stacklist`
        THEN1 (
            qpat_x_assum `good_linear_scan_state st3 _ _ _ _ _` mp_tac >>
            simp [good_linear_scan_state_def'] >> rpt strip_tac >>
            metis_tac []
        )
        THEN1 (
            fs [EVERY_MEM] >> res_tac >> fs []
        )
        THEN1 (
            fs [EVERY_MEM] >> res_tac >> fs []
        )
        THEN1 (
            qpat_x_assum `good_linear_scan_state st1 _ _ _ _ _` mp_tac >>
            simp [good_linear_scan_state_def'] >> rpt strip_tac >>
            metis_tac []
        )
    )
    THEN1 (
        simp [EVERY_MEM] >>
        rpt strip_tac >>
        Cases_on `is_phy_var r` >> simp [] THEN1 (
            `MEM r phyregs` by (rveq >> simp [MEM_FILTER]) >>
            Cases_on `r < 2*k`
            THEN1 (
                `MEM r phyphyregs` by (rveq >> simp [MEM_FILTER]) >>
                `EL r sth2.colors = r DIV 2` by fs [] >>
                sg `~MEM r stacklist` THEN1 (
                    rveq >>
                    fs [GSYM lt_div_2] >>
                    simp [MEM_FILTER] >>
                    metis_tac [convention_partitions]
                ) >>
                `r < LENGTH sth.colors` by fs [EVERY_MEM] >>
                `EL r sth3.colors < k` by fs [lt_div_2] >>
                metis_tac []
            )
            THEN1 (
                `2*k <= r` by simp [] >>
                `MEM r stackphyregs` by (rveq >> simp [MEM_FILTER]) >>
                fs []
            )
        ) >>
        strip_tac >>
        `MEM r stacklist` by (rveq >> simp [MEM_FILTER]) >>
        `k <= EL r sth3.colors` by (fs [EVERY_MEM] >> metis_tac []) >>
        `r < LENGTH sth.colors` by fs [EVERY_MEM] >>
        metis_tac []
    )
    THEN1 (
        simp [EVERY_MEM, FORALL_PROD] >>
        rpt strip_tac >>
        rename1 `MEM (r1,r2) forced` >>
        `MEM r1 reglist /\ MEM r2 reglist` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>
        `r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors` by fs [EVERY_MEM] >>
        `EL r1 sth3.colors = EL r2 sth3.colors` by fs [] >>
        Cases_on `MEM r1 stacklist` >>
        Cases_on `MEM r2 stacklist`
        THEN1 (
            `MEM (r1, r2) forced'` by (rveq >> fs [MEM_FILTER]) >>
            qpat_x_assum `good_linear_scan_state st3 _ _ _ _ _` mp_tac >>
            simp [good_linear_scan_state_def'] >> rpt strip_tac >>
            qpat_x_assum `EVERY _ forced'` mp_tac >>
            rpt (qpat_x_assum `MEM _ _` mp_tac) >>
            qpat_x_assum `EL _ _ = EL _ _` mp_tac >>
            rpt (first_x_assum kall_tac) >>
            rw [EVERY_MEM, FORALL_PROD] >>
            fs []
        )
        THEN1 (
            fs [EVERY_MEM] >> res_tac >> fs []
        )
        THEN1 (
            fs [EVERY_MEM] >> res_tac >> fs []
        )
        THEN1 (
            qpat_x_assum `good_linear_scan_state st1 _ _ _ _ _` mp_tac >>
            simp [good_linear_scan_state_def'] >> rpt strip_tac >>
            `EL r1 sth1.colors = EL r2 sth1.colors` by metis_tac [] >>
            qpat_x_assum `EVERY _ forced` mp_tac >>
            rpt (qpat_x_assum `MEM _ _` mp_tac) >>
            qpat_x_assum `EL _ _ = EL _ _` mp_tac >>
            rpt (first_x_assum kall_tac) >>
            rw [EVERY_MEM, FORALL_PROD] >>
            fs []
        )
    )
QED

val good_bijection_state_def = Define`
    good_bijection_state st regset = (
        regset = domain st.bij /\
        (
          sp_inverts st.bij st.invbij /\
          sp_inverts st.invbij st.bij
        ) /\ (
          (!r. r IN regset ==> (is_stack_var r <=> is_stack_var (the 0 (lookup r st.bij)))) /\
          (!r. r IN regset ==> (is_alloc_var r <=> is_alloc_var (the 0 (lookup r st.bij)))) /\
          (!r. r IN regset /\ is_phy_var r ==> r = (the 0 (lookup r st.bij)))
        ) /\
        (!r. r IN domain st.invbij /\ is_stack_var r ==> r < st.nstack) /\
        (!r. r IN domain st.invbij /\ is_alloc_var r ==> r < st.nalloc) /\
        (
          is_stack_var st.nstack /\
          is_alloc_var st.nalloc
        ) /\
        (!r. the 0 (lookup r st.bij) <= st.nmax)
    )
`;

Theorem convention_partitions_or:
     !r. ( is_phy_var r /\ ~is_stack_var r /\ ~is_alloc_var r) \/
         (~is_phy_var r /\  is_stack_var r /\ ~is_alloc_var r) \/
         (~is_phy_var r /\ ~is_stack_var r /\  is_alloc_var r)
Proof
    metis_tac [convention_partitions]
QED

Theorem find_bijection_invariants:
     !st r regset.
    good_bijection_state st regset ==>
    good_bijection_state (find_bijection_step st r) (r INSERT regset)
Proof
    simp [find_bijection_step_def] >>
    rpt strip_tac >>
    Cases_on `lookup r st.bij <> NONE` THEN1 (
      `r IN domain st.bij` by metis_tac [option_nchotomy, domain_lookup] >>
      fs [good_bijection_state_def] >>
      rw [INSERT_DEF, EXTENSION] >>
      metis_tac []
    ) >>
    fs [lookup_NONE_domain] >>
    fs [good_bijection_state_def] >>
    strip_tac THEN1 (
      qspec_then `r` assume_tac convention_partitions_or >> fs []
    ) >>
    strip_tac THEN1 (
      strip_tac >> (
        qspec_then `r` assume_tac convention_partitions_or >> fs []
        THEN1 (
          reverse (Cases_on `lookup r st.invbij`) THEN1 (
            rename1 `_ = SOME fr` >>
            `lookup fr st.bij = SOME r` by fs [sp_inverts_def] >>
            `fr IN domain st.bij` by fs [domain_lookup] >>
            qspec_then `fr` assume_tac convention_partitions_or >> fs []
            THEN1 (
              `fr = the 0 (lookup fr st.bij)` by fs [] >>
              `fr = r` by metis_tac [the_def] >>
              fs []
            ) >>
            `r = the 0 (lookup fr st.bij)` by fs [the_def] >>
            metis_tac []
          ) >>
          fs [lookup_NONE_domain] >>
          metis_tac [sp_inverts_insert]
        )
        THEN1 (
          reverse (Cases_on `lookup st.nstack st.invbij`) THEN1 (
            `st.nstack IN domain st.invbij` by fs [domain_lookup] >>
            `st.nstack < st.nstack` by fs [] >>
            fs []
          ) >>
          fs [lookup_NONE_domain] >>
          metis_tac [sp_inverts_insert]
        )
        THEN1 (
          reverse (Cases_on `lookup st.nalloc st.invbij`) THEN1 (
            `st.nalloc IN domain st.invbij` by fs [domain_lookup] >>
            `st.nalloc < st.nalloc` by fs [] >>
            fs []
          ) >>
          fs [lookup_NONE_domain] >>
          metis_tac [sp_inverts_insert]
        )
      )
    ) >>
    strip_tac THEN1 (
      rpt strip_tac >> (
        reverse (Cases_on `r = r'`) THEN1 (
          qspec_then `r` assume_tac convention_partitions_or >> fs [] >>
          simp [lookup_insert] >> rfs []
        ) >>
        rveq >>
        qspec_then `r` assume_tac convention_partitions_or >> fs [] >>
        rw [the_def] >>
        metis_tac [convention_partitions]
      )
    ) >>
    strip_tac THEN1 (
      rpt strip_tac >>
      qspec_then `r` assume_tac convention_partitions_or >> fs [] >> fs []
      THEN1 metis_tac [convention_partitions]
      THEN1 (
        `r' < st.nstack` by fs [] >>
        simp []
      )
      THEN1 metis_tac [convention_partitions]
    ) >>
    strip_tac THEN1 (
      rpt strip_tac >>
      qspec_then `r` assume_tac convention_partitions_or >> fs [] >> fs []
      THEN1 metis_tac [convention_partitions]
      THEN1 metis_tac [convention_partitions]
      THEN1 (
        `r' < st.nalloc` by fs [] >>
        simp []
      )
    ) >>
    strip_tac THEN1 (
      rpt strip_tac >>
      qspec_then `r` assume_tac convention_partitions_or >> fs [] >>
      fs [is_stack_var_def, is_alloc_var_def]
    )
    THEN1 (
      gen_tac >>
      qspec_then `r` assume_tac convention_partitions_or >> fs [] >>
      rw [the_def, lookup_insert]
    )
QED

Theorem FOLDL_find_bijection_invariants:
     !st l regset.
    good_bijection_state st regset ==>
    good_bijection_state (FOLDL find_bijection_step st l) (set l UNION regset)
Proof
    Induct_on `l` >>
    rw [] >>
    `good_bijection_state (find_bijection_step st h) (h INSERT regset)` by simp [find_bijection_invariants] >>
    first_x_assum (qspecl_then [`find_bijection_step st h`, `h INSERT regset`] assume_tac) >>
    rfs [] >>
    `(h INSERT set l) UNION regset = (set l UNION (h INSERT regset))` by (rw [EXTENSION] >> metis_tac []) >>
    simp []
QED

Theorem foldi_find_bijection_invariants:
     !st s regset.
    good_bijection_state st regset ==>
    good_bijection_state (foldi (\r v acc. find_bijection_step acc r) 0 st s) (domain s UNION regset)
Proof
    rw [foldi_FOLDR_toAList] >>
    `FOLDR (\(r,v) acc. find_bijection_step acc r) st (toAList s) = FOLDR (\r acc. find_bijection_step acc r) st (MAP FST (toAList s))` by simp [FOLDR_MAP, LAMBDA_PROD] >>
    `(\a b. find_bijection_step a b) = find_bijection_step` by rw [FUN_EQ_THM] >>
    fs [FOLDR_FOLDL_REVERSE] >>
    once_rewrite_tac [GSYM set_MAP_FST_toAList_eq_domain] >>
    once_rewrite_tac [GSYM LIST_TO_SET_REVERSE] >>
    simp [FOLDL_find_bijection_invariants]
QED

Theorem in_clash_tree_set_eq:
     (!w r. in_clash_tree (Delta w r) = set w UNION set r) /\
    (!names. in_clash_tree (Set names) = domain names) /\
    (!name_opt t1 t2.
      in_clash_tree (Branch name_opt t1 t2) =
      case name_opt of
          | SOME names => domain names UNION in_clash_tree t1 UNION in_clash_tree t2
          | NONE => in_clash_tree t1 UNION in_clash_tree t2
    ) /\
    (!t1 t2. in_clash_tree (Seq t1 t2) = in_clash_tree t1 UNION in_clash_tree t2)
Proof
    rw [in_clash_tree_def, EXTENSION, IN_DEF] >>
    CASE_TAC >>
    rw [UNION_DEF, IN_DEF] >>
    metis_tac []
QED

Theorem find_bijection_clash_tree_invariants:
     !st ct regset.
    good_bijection_state st regset ==>
    good_bijection_state (find_bijection_clash_tree st ct) (in_clash_tree ct UNION regset)
Proof
    Induct_on `ct` >>
    rw [find_bijection_clash_tree_def]
    THEN1 (
        simp [in_clash_tree_set_eq, GSYM UNION_ASSOC] >>
        simp [FOLDL_find_bijection_invariants]
    )
    THEN1 (
        simp [in_clash_tree_set_eq] >>
        simp [foldi_find_bijection_invariants]
    )
    THEN1 (
        `good_bijection_state (find_bijection_clash_tree (find_bijection_clash_tree st ct) ct') (in_clash_tree ct UNION in_clash_tree ct' UNION regset)` by metis_tac [UNION_COMM, UNION_ASSOC] >>
        simp [in_clash_tree_set_eq] >>
        CASE_TAC >> fs [GSYM UNION_ASSOC] >>
        simp [foldi_find_bijection_invariants]
    )
    THEN1 (
        simp [in_clash_tree_set_eq] >>
        metis_tac [UNION_COMM, UNION_ASSOC]
    )
QED

Theorem find_bijection_init_invariants:
     good_bijection_state find_bijection_init EMPTY
Proof
    simp [good_bijection_state_def, find_bijection_init_def, sp_inverts_def, lookup_def, is_stack_var_def, is_alloc_var_def, the_def]
QED

val sptree_eq_list_def = Define`
    sptree_eq_list (s : int num_map) l = !i.
      i < LENGTH l ==>
      (0 < EL i l <=> lookup i s = NONE) /\
      (EL i l <= 0 <=> lookup i s = SOME (EL i l))
`

Theorem numset_list_add_if_lt_monad_correct:
     !int_beg sth l v.
    v <= 0 /\
    sptree_eq_list int_beg sth.int_beg /\
    EVERY (\r. r < LENGTH sth.int_beg) l ==>
    ?sthout. numset_list_add_if_lt_monad l v sth = (Success (), sthout) /\
    sptree_eq_list (numset_list_add_if_lt l v int_beg) sthout.int_beg /\
    sthout = sth with int_beg := sthout.int_beg /\
    LENGTH sthout.int_beg = LENGTH sth.int_beg
Proof
    Induct_on `l` >>
    rw ([numset_list_add_if_lt_def, numset_list_add_if_def, numset_list_add_if_lt_monad_def] @ msimps) >>
    fs [GSYM numset_list_add_if_lt_def] >>
    `!(n : int). ~(0 < n) <=> n <= 0` by intLib.COOPER_TAC >>
    fs [sptree_eq_list_def, linear_scan_hidden_state_component_equality] >> (
      first_x_assum (qspecl_then [`insert h v int_beg`, `sth with int_beg := LUPDATE v h sth.int_beg`, `v`] mp_tac) >>
      impl_tac THEN1 rw [EL_LUPDATE, lookup_insert] >>
      rw []
    )
QED

Theorem numset_list_add_if_gt_monad_correct:
     !int_end sth l v.
    v <= 0 /\
    sptree_eq_list int_end sth.int_end /\
    EVERY (\r. r < LENGTH sth.int_end) l ==>
    ?sthout. numset_list_add_if_gt_monad l v sth = (Success (), sthout) /\
    sptree_eq_list (numset_list_add_if_gt l v int_end) sthout.int_end /\
    sthout = sth with int_end := sthout.int_end /\
    LENGTH sthout.int_end = LENGTH sth.int_end
Proof
    Induct_on `l` >>
    rw ([numset_list_add_if_gt_def, numset_list_add_if_def, numset_list_add_if_gt_monad_def] @ msimps) >>
    fs [GSYM numset_list_add_if_gt_def] >>
    `!(n : int). ~(0 < n) <=> n <= 0` by intLib.COOPER_TAC >>
    fs [sptree_eq_list_def, linear_scan_hidden_state_component_equality] >> (
      first_x_assum (qspecl_then [`insert h v int_end`, `sth with int_end := LUPDATE v h sth.int_end`, `v`] mp_tac) >>
      impl_tac THEN1 rw [EL_LUPDATE, lookup_insert] >>
      rw []
    )
QED

Theorem get_intervals_ct_monad_aux_correct:
     !ct sth live n int_beg int_end nout int_begout int_endout liveout.
    n <= 0 /\
    sptree_eq_list int_beg sth.int_beg /\
    sptree_eq_list int_end sth.int_end /\
    get_intervals_ct_aux ct n int_beg int_end live = (nout, int_begout, int_endout, liveout) /\
    LENGTH sth.int_end = LENGTH sth.int_beg /\
    (!r. in_clash_tree ct r ==> r < LENGTH sth.int_beg) /\
    (!r. r IN domain live ==> r < LENGTH sth.int_beg) ==>
    ?sthout. get_intervals_ct_monad_aux ct n live sth = (Success (nout, liveout), sthout) /\
    sptree_eq_list int_begout sthout.int_beg /\
    sptree_eq_list int_endout sthout.int_end /\
    LENGTH sthout.int_beg = LENGTH sth.int_beg /\
    LENGTH sthout.int_end = LENGTH sth.int_end /\
    (!r. r IN domain liveout ==> r < LENGTH sth.int_beg) /\
    sthout = sth with <| int_beg := sthout.int_beg ; int_end := sthout.int_end |> /\
    nout <= 0
Proof
    Induct_on `ct` >>
    rw ([get_intervals_ct_monad_aux_def, get_intervals_ct_aux_def] @ msimps)

    THEN1 (
        qspecl_then [`int_beg`, `sth`, `l`, `n`] mp_tac numset_list_add_if_lt_monad_correct >>
        impl_tac THEN1 fs [in_clash_tree_def, EVERY_MEM] >>
        strip_tac >> rw [] >>
        rename1 `_ = (Success (), sth1)` >>
        `?int_beg1. numset_list_add_if_lt l n int_beg = int_beg1` by simp [] >>
        fs [linear_scan_hidden_state_component_equality] >>

        qspecl_then [`int_end`, `sth1`, `l`, `n`] mp_tac numset_list_add_if_gt_monad_correct >>
        impl_tac THEN1 fs [in_clash_tree_def, EVERY_MEM] >>
        strip_tac >> rw [] >>
        rename1 `_ = (Success (), sth2)` >>
        `?int_end2. numset_list_add_if_gt l n int_end = int_end2` by simp [] >>
        fs [linear_scan_hidden_state_component_equality] >>

        qspecl_then [`int_end2`, `sth2`, `l0`, `n-1`] mp_tac numset_list_add_if_gt_monad_correct >>
        impl_tac THEN1 (
          fs [in_clash_tree_def, EVERY_MEM] >>
          intLib.COOPER_TAC
        ) >>
        strip_tac >> rw [] >>
        rename1 `_ = (Success (), sth3)` >>
        fs [linear_scan_hidden_state_component_equality, domain_numset_list_insert, domain_numset_list_delete, in_clash_tree_def] >>
        intLib.COOPER_TAC
    )

    THEN1 (
        qspecl_then [`int_end`, `sth`, `MAP FST (toAList s)`, `n`] mp_tac numset_list_add_if_gt_monad_correct >>
        impl_tac THEN1
        fs [in_clash_tree_def, EVERY_MEM, set_MAP_FST_toAList_eq_domain] >>
        strip_tac >> rw [] >>
        fs [linear_scan_hidden_state_component_equality, domain_union, in_clash_tree_def] >>
        intLib.COOPER_TAC
    )

    THEN1 (
        rename1 `Branch optcutset ct1 ct2` >>
        rpt (pairarg_tac >> fs []) >>
        Cases_on `optcutset` >> fs [] >> (
          first_x_assum (qspecl_then [`sth`, `live`, `n`, `int_beg`, `int_end`, `n2`, `int_beg2`, `int_end2`, `live2`] mp_tac) >>
          impl_tac THEN1 fs [in_clash_tree_def] >>
          strip_tac >> rw [] >>
          rename1 `_ = (Success _, sth2)` >>

          first_x_assum (qspecl_then [`sth2`, `live`, `n2`, `int_beg2`, `int_end2`, `n1`, `int_beg1`, `int_end1`, `live1`] mp_tac) >>
          impl_tac THEN1 fs [in_clash_tree_def] >>
          strip_tac >> rw [] >>
          rename1 `_ = (Success _, sth1)` >>
          rfs [linear_scan_hidden_state_component_equality, domain_union, in_clash_tree_def] >> (
            qspecl_then [`int_end1`, `sth1`, `MAP FST (toAList x)`, `n1`] mp_tac numset_list_add_if_gt_monad_correct >>
            impl_tac THEN1 fs [EVERY_MEM, in_clash_tree_def, domain_union, set_MAP_FST_toAList_eq_domain] >>
            strip_tac >> rw [] >>
            fs [linear_scan_hidden_state_component_equality] >>
            intLib.COOPER_TAC
          )
        )
    )

    THEN1 (
        rename1 `Seq ct1 ct2` >>
        rpt (pairarg_tac >> fs []) >>
        first_x_assum (qspecl_then [`sth`, `live`, `n`, `int_beg`, `int_end`, `n2`, `int_beg2`, `int_end2`, `live2`] mp_tac) >>
        impl_tac THEN1 fs [in_clash_tree_def] >>
        strip_tac >> rw [] >>
        rename1 `_ = (Success _, sth2)` >>

        first_x_assum (qspecl_then [`sth2`, `live2`, `n2`, `int_beg2`, `int_end2`, `nout`, `int_begout`, `int_endout`, `liveout`] mp_tac) >>
        impl_tac THEN1 fs [in_clash_tree_def] >>
        strip_tac >> rw [] >>
        rfs [linear_scan_hidden_state_component_equality]
    )
QED

Theorem get_intervals_ct_monad_correct:
     !ct sth n int_beg int_end.
    (!i. i < LENGTH sth.int_beg ==> 0 < EL i sth.int_beg) /\
    (!i. i < LENGTH sth.int_end ==> 0 < EL i sth.int_end) /\
    get_intervals_ct ct = (n, int_beg, int_end) /\
    LENGTH sth.int_end = LENGTH sth.int_beg /\
    (!r. in_clash_tree ct r ==> r < LENGTH sth.int_beg) ==>
    ?sthout. get_intervals_ct_monad ct sth = (Success n, sthout) /\
    sptree_eq_list int_beg sthout.int_beg /\
    sptree_eq_list int_end sthout.int_end /\
    LENGTH sthout.int_beg = LENGTH sth.int_beg /\
    LENGTH sthout.int_end = LENGTH sth.int_end /\
    sthout = sth with <| int_beg := sthout.int_beg ; int_end := sthout.int_end |>
Proof
    `!(n : int). ~(n <= 0) <=> 0 < n` by intLib.COOPER_TAC >>
    rw (get_intervals_ct_monad_def :: get_intervals_ct_def :: msimps) >>
    rpt (pairarg_tac >> fs []) >>
    rename1 `get_intervals_ct_aux _ _ _ _ _ = (n1, int_beg1, int_end1, live)` >>

    qspecl_then [`ct`, `sth`, `LN`, `0`, `LN`, `LN`, `n1`, `int_beg1`, `int_end1`, `live`] mp_tac get_intervals_ct_monad_aux_correct >>
    impl_tac THEN1 rw [sptree_eq_list_def, lookup_def] >>
    strip_tac >> rw [] >>
    rename1 `_ = (Success _, sth1)` >>

    qspecl_then [`int_beg1`, `sth1`, `MAP FST (toAList live)`, `n1`] mp_tac numset_list_add_if_lt_monad_correct >>
    impl_tac THEN1 rw [EVERY_MEM, set_MAP_FST_toAList_eq_domain] >>
    strip_tac >> rw [] >>
    rename1 `_ = (Success _, sth2)` >>
    fs [linear_scan_hidden_state_component_equality] >>

    qspecl_then [`int_end1`, `sth2`, `MAP FST (toAList live)`, `n1`] mp_tac numset_list_add_if_gt_monad_correct >>
    impl_tac THEN1 rw [EVERY_MEM, set_MAP_FST_toAList_eq_domain] >>
    strip_tac >> simp [] >>
    rename1 `_ = (Success _, sth2)` >>
    fs [linear_scan_hidden_state_component_equality]
QED

Theorem in_clash_tree_eq_live_tree_registers:
     !ct r. in_clash_tree ct r <=> r IN (live_tree_registers (get_live_tree ct))
Proof
    Induct_on `ct` >>
    rw [in_clash_tree_def, live_tree_registers_def, get_live_tree_def, set_MAP_FST_toAList_eq_domain]
    THEN1 metis_tac []
    THEN1 (
        Cases_on `o'` >>
        simp[live_tree_registers_def] >>
        simp [MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
        metis_tac []
    )
QED

Theorem get_live_backward_in_live_tree_registers:
     !lt live. domain (get_live_backward lt live) SUBSET domain live UNION live_tree_registers lt
Proof
    Induct_on `lt` >>
    simp [get_live_backward_def, live_tree_registers_def, domain_numset_list_delete, domain_numset_list_insert, branch_domain] >>
    fs [SUBSET_DEF] >>
    metis_tac []
QED

Theorem fix_domination_live_tree_registers:
     !lt. live_tree_registers (fix_domination lt) = live_tree_registers lt
Proof
    rw [fix_domination_def, live_tree_registers_def] >>
    `set (MAP FST (toAList (get_live_backward lt LN))) = domain (get_live_backward lt LN)` by rw [EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
    qspecl_then [`lt`, `LN`] assume_tac get_live_backward_in_live_tree_registers >>
    fs [SUBSET_DEF, EXTENSION] >>
    metis_tac []
QED

Theorem get_intervals_beg_less_end:
     !lt n_in beg_in end_in n_out beg_out end_out.
    (!r. r IN domain beg_in ==> the 0 (lookup r beg_in) <= the 0 (lookup r end_in)) /\
    domain beg_in SUBSET domain end_in /\
    (n_out, beg_out, end_out) = get_intervals lt n_in beg_in end_in ==>
    (!r. r IN domain beg_out ==> the 0 (lookup r beg_out) <= the 0 (lookup r end_out)) /\
    domain beg_out SUBSET domain end_out
Proof
    Induct_on `lt` >>
    simp [get_intervals_def] >>
    rpt gen_tac >> strip_tac
    THEN1 (
        strip_tac
        THEN1 (
            rw [lookup_numset_list_add_if_lt, lookup_numset_list_add_if_gt]
            THEN1 (
                every_case_tac >>
                simp [the_def] >>
                intLib.COOPER_TAC
            )
            THEN1 rfs [domain_numset_list_add_if_lt]
        )
        THEN1 (
            fs [domain_numset_list_add_if_lt, domain_numset_list_add_if_gt, SUBSET_DEF] >>
            metis_tac []
        )
    )
    THEN1 (
        strip_tac
        THEN1 (
            rw [lookup_numset_list_add_if_gt] >>
            res_tac >>
            every_case_tac
            THEN1 (
                `r NOTIN domain end_in` by fs [lookup_NONE_domain] >>
                rfs [SUBSET_DEF]
            )
            THEN1 (
                fs [the_def] >>
                intLib.COOPER_TAC
            )
        )
        THEN1 (
            simp [domain_numset_list_add_if_gt] >>
            fs [SUBSET_DEF]
        )
    ) >>
    rpt (pairarg_tac >> fs []) >>
    `!r. r IN domain int_beg2 ==> the 0 (lookup r int_beg2) <= the 0 (lookup r int_end2)` by metis_tac [] >>
    metis_tac []
QED

Theorem linear_reg_alloc_without_renaming_correct:
     !k moves ct forced.
    (!i. i < LENGTH sth.int_beg ==> 0 < EL i sth.int_beg) /\
    (!i. i < LENGTH sth.int_end ==> 0 < EL i sth.int_end) /\
    LENGTH sth.int_end = LENGTH sth.int_beg /\
    (!r. MEM r reglist_unsorted <=> in_clash_tree ct r) /\
    (!r. in_clash_tree ct r ==> r < LENGTH sth.int_beg) /\
    EVERY (\r1,r2. in_clash_tree ct r1 /\ in_clash_tree ct r2) forced /\
    EVERY (\r1,r2. r1 < LENGTH sth.colors /\ r2 < LENGTH sth.colors) (MAP SND moves) /\
    LENGTH reglist_unsorted <= LENGTH sth.sorted_regs /\
    LENGTH moves <= LENGTH sth.sorted_moves /\
    LENGTH sth.colors = LENGTH sth.int_beg /\
    LENGTH sth.int_end = LENGTH sth.int_beg /\
    ALL_DISTINCT reglist_unsorted
    ==>
    ?sthout livein flivein.
    do
      get_intervals_ct_monad ct;
      linear_reg_alloc_intervals k forced moves reglist_unsorted;
    od sth = (Success (), sthout) /\
    check_clash_tree (\r. EL r sthout.colors) ct LN LN = SOME (livein, flivein) /\
    (!r. in_clash_tree ct r ==>
      if is_phy_var r then
        EL r sthout.colors = r DIV 2
      else if is_stack_var r then
        k <= EL r sthout.colors
      else
        T
    ) /\
    EVERY (\r1,r2. EL r1 sthout.colors = EL r2 sthout.colors ==> r1 = r2) forced /\
    LENGTH sthout.colors = LENGTH sth.colors
Proof
    rw msimps >>
    `?n int_beg int_end. get_intervals_ct ct = (n, int_beg, int_end)` by simp [GSYM EXISTS_PROD] >>
    qspecl_then [`ct`, `sth`, `n`, `int_beg`, `int_end`] mp_tac get_intervals_ct_monad_correct >>
    impl_tac THEN1 rw [] >>
    strip_tac >> simp [] >>
    rename1 `_ = (Success _, sthint)` >>
    fs [linear_scan_hidden_state_component_equality] >>

    `?n' int_beg' int_end'. get_intervals (fix_domination (get_live_tree ct)) 0 LN LN = (n', int_beg', int_end')` by simp [GSYM EXISTS_PROD] >>
    qspecl_then [`ct`, `int_beg`, `int_beg'`, `int_end`, `int_end'`, `n`, `n'`] assume_tac get_intervals_ct_eq >>
    rfs [] >>

    qspecl_then [`fix_domination (get_live_tree ct)`, `0`, `LN`, `LN`, `n'`, `int_beg'`, `int_end'`] assume_tac get_intervals_beg_less_end >>
    rfs [] >>

    qspecl_then [`get_live_tree ct`, `n'`, `int_beg'`, `int_end'`] assume_tac get_intervals_domain_eq_live_tree_registers >>
    rfs [] >>

    `live_tree_registers (get_live_tree ct) = in_clash_tree ct` by simp [GSYM in_clash_tree_eq_live_tree_registers, EXTENSION, IN_DEF] >>
    rfs [fix_domination_live_tree_registers] >> fs [] >>

    sg `!r. in_clash_tree ct r ==> lookup r int_beg' = SOME (EL r sthint.int_beg) /\ lookup r int_end' = SOME (EL r sthint.int_end)` THEN1 (
        gen_tac >> strip_tac >> fs [sptree_eq_list_def] >>
        rpt (first_x_assum (qspec_then `r` assume_tac)) >>
        `lookup r int_end' <> NONE /\ lookup r int_beg' <> NONE` by (CCONTR_TAC >> rfs [lookup_NONE_domain, IN_DEF]) >>
        `~(0 < EL r sthint.int_end) /\ ~(0 < EL r sthint.int_beg)` by fs [] >>
        fs [intLib.COOPER_PROVE ``!(n : int). ~(0 < n) <=> n <= 0``]
    ) >>

    qspecl_then [`k`, `forced`, `moves`, `reglist_unsorted`, `sthint`] mp_tac linear_reg_alloc_intervals_correct >>
    impl_tac THEN1 (
        rw [] >> fs [EVERY_MEM, FORALL_PROD] >>
        rw [] >> fs [IN_DEF] >>
        rpt (first_x_assum (qspec_then `r` assume_tac)) >>
        rfs [the_def]
    ) >>
    strip_tac >> simp [] >>

    sg `check_intervals (\r. EL r sthout.colors) int_beg' int_end'` THEN1 (
        rw [check_intervals_def] >>
        rename1 `r1 = r2` >>
        first_x_assum (qspecl_then [`r1`, `r2`] mp_tac) >>
        reverse impl_tac THEN1 simp [] >>
        fs [sptree_eq_list_def, IN_DEF] >>
        qpat_assum `!r. _ ==> lookup _ _ = SOME _ /\ lookup _ _ = SOME _`(qspec_then `r2` assume_tac) >>
        rfs []
    ) >>

    qspecl_then [`get_live_tree ct`, `n'`, `int_beg'`, `int_end'`, `\r. EL r sthout.colors`] mp_tac check_intervals_check_live_tree >>
    impl_tac THEN1 rw [] >>
    strip_tac >>

    qspecl_then [`\r. EL r sthout.colors`, `get_live_tree ct`, `liveout`, `fliveout`] mp_tac fix_domination_check_live_tree >>
    impl_tac THEN1 rw [] >>
    strip_tac >>

    qspecl_then [`\r. EL r sthout.colors`, `ct`, `liveout'`, `fliveout'`] mp_tac get_live_tree_correct_LN >>
    impl_tac THEN1 rw [] >>
    strip_tac >> rw [] >>
    fs [EVERY_MEM]
QED

Theorem check_col_apply_bijection:
     !(cutset:num_set) livein flivein f.
    (!r. r IN bijdom ==> (appbij r) IN bijcodom /\ appinvbij (appbij r) = r) /\
    (!r. r IN bijcodom ==> (appinvbij r) IN bijdom /\ appbij (appinvbij r) = r) /\
    domain cutset SUBSET bijdom /\
    check_col f (foldi (\r _ acc. insert (appbij r) () acc) 0 LN cutset) = SOME (livein, flivein) ==>
    ?livein' flivein'. check_col (\r. f (appbij r)) cutset = SOME (livein', flivein') /\
    domain livein' = IMAGE appinvbij (domain livein)
Proof
    simp [check_col_def] >>
    rpt gen_tac >> strip_tac >>
    fs [MAP_o, foldi_FOLDR_toAList] >>
    `FOLDR (\(r,_) acc. insert (appbij r) () acc) LN (toAList cutset) = FOLDR (\r acc. insert (appbij r) () acc) LN (MAP FST (toAList cutset))` by rw [FOLDR_MAP, LAMBDA_PROD] >>
    fs [] >> first_x_assum kall_tac >>
    imp_res_tac ALL_DISTINCT_INJ_MAP >> fs [] >>
    qpat_x_assum `ALL_DISTINCT _` kall_tac >>
    `ALL_DISTINCT (MAP FST (toAList cutset))` by simp [ALL_DISTINCT_MAP_FST_toAList] >>
    `domain cutset = set (MAP FST (toAList cutset))` by simp [set_MAP_FST_toAList_eq_domain] >>
    qabbrev_tac `l = MAP FST (toAList cutset)` >> qpat_x_assum `Abbrev _` kall_tac >>
    `domain (FOLDR (\r acc. insert (appbij r) () acc) LN l) = IMAGE appbij (set l)` by (rpt (first_x_assum kall_tac) >> Induct_on `l` >> rw []) >>
    fs [set_MAP_FST_toAList_eq_domain] >> first_x_assum kall_tac >>
    strip_tac
    THEN1 (
        qpat_x_assum `domain cutset = set l` kall_tac >>
        Induct_on `l` >>
        rw [] >> fs [INJ_INSERT] >>
        rw [MEM_MAP] >>
        Cases_on `MEM r l` >> simp [] >>
        metis_tac [SUBSET_DEF]
    )
    THEN1 (
        rw [EXTENSION] >>
        metis_tac [SUBSET_DEF]
    )
QED


Theorem check_partial_col_apply_bijection:
     !l live flive live' flive' livein flivein.
    (!r. r IN bijdom ==> (appbij r) IN bijcodom /\ appinvbij (appbij r) = r) /\
    (!r. r IN bijcodom ==> (appinvbij r) IN bijdom /\ appbij (appinvbij r) = r) /\
    (set l) SUBSET bijdom /\
    (domain live) SUBSET bijcodom /\
    domain flive = IMAGE f (domain live) /\
    domain flive' = IMAGE (f o appbij) (domain live') /\
    domain live' = IMAGE appinvbij (domain live) /\
    INJ f (domain live) UNIV /\
    check_partial_col f (MAP appbij l) live flive = SOME (livein, flivein) ==>
    ?livein' flivein'. check_partial_col (\r. f (appbij r)) l live' flive' = SOME (livein', flivein') /\
    domain livein' = IMAGE appinvbij (domain livein)
Proof
    Induct_on `l` >>
    rw [check_partial_col_def] >>
    `domain flive' = domain flive` by (rw [EXTENSION] >> fs [] >> metis_tac [SUBSET_DEF]) >>
    fs [case_eq_thms]
    THEN1 (
        first_x_assum (qspecl_then [`insert (appbij h) () live`, `insert (f (appbij h)) () flive`, `insert h () live'`, `insert (f (appbij h))() flive'`, `livein`, `flivein`] mp_tac) >>
        impl_tac THEN1 (
            rw [INJ_INSERT] >>
            `(f y) IN domain flive` by fs [] >>
            fs [domain_lookup]
        ) >>
        rw [] >>
        qexists_tac `livein'` >> qexists_tac `flivein'` >>
        rw [] >> disj1_tac >>
        FULL_SIMP_TAC pure_ss [lookup_NONE_domain] >>
        strip_tac
        THEN1 (fs [] >> metis_tac [SUBSET_DEF])
        THEN1 metis_tac []
    )
    THEN1 (
        first_x_assum (qspecl_then [`live`, `flive`, `live'`, `flive'`, `livein`, `flivein`] mp_tac) >>
        impl_tac THEN1 rw [] >>
        rw [] >>
        qexists_tac `livein'` >> qexists_tac `flivein'` >>
        rw [] >> disj2_tac >> rw [] >>
        `appbij h IN domain live` by simp [domain_lookup] >>
        `appinvbij (appbij h) IN domain live'` by (fs [] >> metis_tac []) >>
        rfs [domain_lookup]
    )
QED

Theorem check_clash_tree_output_subset:
     !ct live flive livein flivein.
    check_clash_tree f ct live flive = SOME (livein, flivein) ==>
    domain livein SUBSET domain live UNION in_clash_tree ct
Proof
    Induct_on `ct` >>
    rw [check_clash_tree_def, in_clash_tree_set_eq] >>
    fs [case_eq_thms]
    THEN1 (
        imp_res_tac check_partial_col_domain >>
        fs [SUBSET_DEF, domain_numset_list_delete] >>
        metis_tac []
    )
    THEN1 fs [check_col_def]
    THEN1 (
        imp_res_tac check_partial_col_domain >>
        fs [branch_domain] >>
        fs [SUBSET_DEF] >>
        metis_tac []
    )
    THEN1 (
        fs [check_col_def, SUBSET_DEF]
    )
    THEN1 (
        fs [SUBSET_DEF] >>
        metis_tac []
    )
QED

Theorem domain_apply_bij_set:
     !s bij. domain (foldi (λr _ acc. insert (the 0 (lookup r bij)) () acc) 0 LN s) = IMAGE (\r. the 0n (lookup r bij)) (domain s)
Proof
    rw [foldi_FOLDR_toAList] >>
    `FOLDR (\(r,_) acc. insert (the 0 (lookup r bij)) () acc) LN (toAList s) = FOLDR (\r acc. insert (the 0 (lookup r bij)) () acc) LN (MAP FST (toAList s))` by rw [FOLDR_MAP, LAMBDA_PROD] >>
    simp [] >>
    `domain s = set (MAP FST (toAList s))` by simp [set_MAP_FST_toAList_eq_domain] >>
    qabbrev_tac `l = MAP FST (toAList s)` >>
    qpat_x_assum `Abbrev _` kall_tac >>
    qpat_x_assum `FOLDR _ _ _ = FOLDR _ _ _` kall_tac >>
    simp [] >>
    qpat_x_assum `domain _ = set _` kall_tac >>
    Induct_on `l` >>
    rw []
QED

Theorem in_clash_tree_apply_bij:
     !bij ct.
    in_clash_tree ct SUBSET domain bij ==>
    in_clash_tree (apply_bij_on_clash_tree ct bij) = IMAGE (\r. the 0n (lookup r bij)) (in_clash_tree ct)
Proof
    Induct_on `ct` >>
    rw [apply_bij_on_clash_tree_def, in_clash_tree_set_eq, LIST_TO_SET_MAP]
    THEN1 (
        simp [domain_apply_bij_set]
    )
    THEN1 (
        CASE_TAC >>
        fs [OPTION_MAP_DEF] >>
        simp [domain_apply_bij_set] >>
        fs []
    )
QED

Theorem check_clash_tree_apply_bijection:
     !bij invbij f ct live flive live' flive' livein flivein.
    sp_inverts bij invbij /\
    sp_inverts invbij bij /\
    in_clash_tree ct SUBSET domain bij /\
    domain live SUBSET domain invbij /\
    domain flive = IMAGE f (domain live) /\
    domain flive' = IMAGE (\r. f (the 0n (lookup r bij))) (domain live') /\
    domain live' = IMAGE (\r. the 0n (lookup r invbij)) (domain live) /\
    INJ f (domain live) UNIV /\
    check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive = SOME (livein, flivein) ==>
    ?livein' flivein'. check_clash_tree (\r. f (the 0n (lookup r bij))) ct live' flive' = SOME (livein', flivein') /\
    domain livein' = IMAGE (\r. the 0n (lookup r invbij)) (domain livein)
Proof
    NTAC 3 gen_tac >>
    Induct_on `ct` >>
    rw [apply_bij_on_clash_tree_def, check_clash_tree_def] >> (
        TRY (rename1 `Branch optcutset ct1 ct2`) >>
        TRY (rename1 `Seq ct1 ct2`) >>
        sg `(!r. r IN domain bij ==> (the 0n (lookup r bij)) IN domain invbij /\ the 0n (lookup (the 0n (lookup r bij)) invbij) = r) /\
            (!r. r IN domain invbij ==> (the 0n (lookup r invbij)) IN domain bij /\ the 0n (lookup (the 0n (lookup r invbij)) bij) = r)` THEN1 (
            rw [] >> fs [domain_lookup, sp_inverts_def] >>
            res_tac >> simp [the_def]
        ) >>
        qspec_then `bij` assume_tac in_clash_tree_apply_bij >>
        qspec_then `invbij` assume_tac in_clash_tree_apply_bij >>
        qabbrev_tac `appbij = \r. the 0 (lookup r bij)` >>
        qabbrev_tac `appinvbij = \r. the 0 (lookup r invbij)` >>
        qabbrev_tac `bijdom = domain bij` >>
        qabbrev_tac `bijcodom = domain invbij` >>
        `!r. the 0 (lookup r bij) = appbij r` by simp [] >>
        `!r. the 0 (lookup r invbij) = appinvbij r` by simp [] >>
        fs [] >>
        rpt (qpat_x_assum `!r. the 0 (lookup r _) = _ r` kall_tac) >>
        rpt (qpat_x_assum `Abbrev _` kall_tac) >>
        fs [in_clash_tree_set_eq]
    )

    THEN1 (
        fs [case_eq_thms] >>
        PairCases_on `v` >>
        qspecl_then [`l`, `live`, `flive`, `live'`, `flive'`, `v0`, `v1`] mp_tac check_partial_col_apply_bijection >>
        impl_tac THEN1 rw [o_DEF] >>
        strip_tac >>
        qspecl_then [`l0`, `numset_list_delete (MAP appbij l) live`, `numset_list_delete (MAP f (MAP appbij l)) flive`, `numset_list_delete l live'`,
                     `numset_list_delete (MAP (\r. f (appbij r)) l) flive'`, `livein`, `flivein`] mp_tac check_partial_col_apply_bijection >>
        impl_tac
        THEN1 (
            simp [domain_numset_list_delete] >>
            strip_tac THEN1 fs [SUBSET_DEF] >>
            reverse (rw []) THEN1 metis_tac [DIFF_SUBSET, INJ_SUBSET, UNIV_SUBSET] >>
            `INJ f (set (MAP appbij l) UNION domain live) UNIV` by imp_res_tac check_partial_col_success_INJ_lemma >>
            qpat_x_assum `INJ f (domain live) UNIV` kall_tac >>
            simp [EXTENSION] >>
            rpt (pop_assum mp_tac) >>
            rewrite_tac [INJ_DEF, SUBSET_DEF, MEM_MAP, IN_UNION] >>
            metis_tac [MEM_MAP]
        ) >>
        rw []
    )

    THEN1 (
        qspecl_then [`s`, `livein`, `flivein`, `f`] mp_tac check_col_apply_bijection >>
        impl_tac THEN1 rw [] >>
        strip_tac >> asm_exists_tac >> rw []
    )

    THEN1 (
        fs [case_eq_thms] >> fs [] >>
        last_x_assum (qspecl_then [`live`, `flive`, `live'`, `flive'`, `t1_out`, `ft1_out`] assume_tac) >>
        rfs [] >>
        rename1 `check_clash_tree _ _ _ _ = SOME (livein1, flivein1)` >>
        last_x_assum (qspecl_then [`live`, `flive`, `live'`, `flive'`, `t2_out`, `ft2_out`] assume_tac) >>
        rfs [] >>
        rename1 `check_clash_tree _ _ _ _ = SOME (livein2, flivein2)`
        THEN1 (
            `INJ (\r. f (appbij r)) (domain live') UNIV` by (fs [INJ_DEF, EXTENSION, SUBSET_DEF] >> metis_tac []) >>
            `domain ft1_out = IMAGE f (domain t1_out)` by metis_tac [check_clash_tree_output] >>
            `domain flivein1 = IMAGE (\r. f (appbij r)) (domain livein1)` by metis_tac [check_clash_tree_output] >>
            imp_res_tac check_clash_tree_output_subset >> rfs [] >>

            sg `set (MAP appbij (MAP FST (toAList (difference livein2 livein1)))) UNION domain t1_out = domain t1_out UNION domain t2_out` THEN1 (
                rw [LIST_TO_SET_MAP, domain_difference, set_MAP_FST_toAList_eq_domain] >>
                `IMAGE appinvbij (domain t2_out) DIFF IMAGE appinvbij (domain t1_out) = IMAGE appinvbij (domain t2_out DIFF domain t1_out)` by (rfs [EXTENSION, SUBSET_DEF] >> metis_tac []) >>
                `domain t2_out SUBSET bijcodom` by (fs [SUBSET_DEF] >> metis_tac []) >>
                `IMAGE appbij (IMAGE appinvbij (domain t2_out DIFF domain t1_out)) = domain t2_out DIFF domain t1_out` by (rfs [EXTENSION, SUBSET_DEF] >> metis_tac []) >>
                `domain t2_out DIFF domain t1_out UNION domain t1_out = domain t1_out UNION domain t2_out` by (rw [EXTENSION] >> metis_tac []) >>
                simp []
            ) >>

            sg `?brlivein fbrlivein. check_partial_col f (MAP appbij (MAP FST (toAList (difference livein2 livein1)))) t1_out ft1_out = SOME (brlivein,fbrlivein)` THEN1 (
                qspecl_then [`MAP appbij (MAP FST (toAList (difference livein2 livein1)))`, `t1_out`, `ft1_out`, `f`] mp_tac check_partial_col_success >>
                impl_tac THEN1 (
                    simp [] >>
                    `INJ f (domain t1_out) UNIV` by imp_res_tac check_clash_tree_output >>
                    imp_res_tac check_partial_col_success_INJ_lemma >>
                    fs [branch_domain]
                ) >>
                strip_tac >> asm_exists_tac >> rw []
            ) >>
            sg `domain brlivein = domain livein` THEN1 (
                imp_res_tac check_partial_col_domain >>
                rfs [set_MAP_FST_toAList_eq_domain] >>
                simp [domain_difference, EXTENSION] >>
                metis_tac []
            ) >>
            qspecl_then [`MAP FST (toAList (difference livein2 livein1))`, `t1_out`, `ft1_out`, `livein1`, `flivein1`, `brlivein`, `fbrlivein`] mp_tac check_partial_col_apply_bijection >>
            impl_tac >>
            rw []
            THEN1 (
                rfs [SUBSET_DEF, domain_difference, set_MAP_FST_toAList_eq_domain] >>
                metis_tac []
            )
            THEN1 (
                fs [SUBSET_DEF, EXTENSION] >>
                metis_tac []
            )
            THEN1 (
                fs [EXTENSION] >> metis_tac []
            )
            THEN1 (
                imp_res_tac check_clash_tree_output
            )
        )
        THEN1 (
            qspecl_then [`z`, `livein`, `flivein`, `f`] assume_tac check_col_apply_bijection >>
            rfs []
        )
    )

    THEN1 (
        fs [case_eq_thms] >>
        first_x_assum (qspecl_then [`live`, `flive`, `live'`, `flive'`, `t2_out`, `ft2_out`] assume_tac) >>
        rfs [] >> fs [] >>
        imp_res_tac check_clash_tree_output_subset >> rfs [] >>
        first_x_assum (qspecl_then [`t2_out`, `ft2_out`, `livein''`, `flivein''`, `livein`, `flivein`] mp_tac) >>
        impl_tac THEN1 (
            rw []
            THEN1 (
                fs [SUBSET_DEF] >> metis_tac []
            )
            THEN1 (
                imp_res_tac check_clash_tree_output
            )
            THEN1 (
                `INJ (\r. f (appbij r)) (domain live') UNIV` by (fs [INJ_DEF, EXTENSION, SUBSET_DEF] >> metis_tac []) >>
                imp_res_tac check_clash_tree_output >>
                simp []
            )
            THEN1 (
                imp_res_tac check_clash_tree_output
            )
        ) >>
        rw []
    )
QED

Theorem extract_coloration_output:
     !bij invbij sth l acc.
    sp_inverts bij invbij /\
    sp_inverts invbij bij /\
    EVERY (\r. r IN domain invbij) l /\
    EVERY(\r. r < LENGTH sth.colors) l ==>
    ?col. extract_coloration invbij l acc sth = (Success col, sth) /\
    (!r. r IN domain bij ==>
      if MEM (the 0 (lookup r bij)) l then
        lookup r col = SOME (EL (the 0 (lookup r bij)) sth.colors)
      else
        lookup r col = lookup r acc) /\
    domain col SUBSET domain bij UNION domain acc
Proof
    NTAC 3 gen_tac >>
    Induct_on `l` >>
    rw [extract_coloration_def] >> simp msimps >>
    fs [] >>
    first_x_assum (qspec_then `insert (the 0 (lookup h invbij)) (EL h sth.colors) acc` assume_tac) >>
    fs [] >>
    rw []
    THEN1 (
        last_x_assum (qspec_then `r` assume_tac) >>
        every_case_tac >>
        fs [lookup_insert] >>
        sg `r = the 0 (lookup (the 0 (lookup r bij)) invbij)` THEN1 (
            `?ir. lookup r bij = SOME ir` by fs [domain_lookup] >>
            simp [the_def] >>
            `lookup ir invbij = SOME r` by fs [sp_inverts_def] >>
            simp [the_def]
        ) >>
        simp []
    )
    THEN1 metis_tac []
    THEN1 (
        fs [] >>
        last_x_assum (qspec_then `r` assume_tac) >>
        `lookup r col = lookup r (insert (the 0 (lookup h invbij)) (EL h sth.colors) acc)` by metis_tac [] >>
        simp [lookup_insert] >>
        rw [] >>
        `?ih. lookup h invbij = SOME ih` by fs [domain_lookup] >>
        fs [the_def] >>
        `lookup ih bij = SOME h` by fs [sp_inverts_def] >>
        fs [the_def]
    )
    THEN1 (
        `?ih. lookup h invbij = SOME ih` by fs [domain_lookup] >>
        `lookup ih bij = SOME h` by fs [sp_inverts_def] >>
        `ih IN domain bij` by fs [domain_lookup] >>
        fs [the_def, SUBSET_DEF] >>
        metis_tac []
    )
QED

(* TODO: move *)
Theorem LENGTH_toAList:
     !s. LENGTH (toAList s) = size s
Proof
    sg `!s l n. LENGTH (foldi (\k v a. (k,v)::a) n l s) = size s + LENGTH l` THEN1 (
        Induct_on `s` >>
        rw [foldi_def]
    ) >>
    rw [toAList_def]
QED

Theorem check_col_equal_col:
     !s f1 f2.
    (!r. r IN domain s ==> f1 r = f2 r) ==>
    check_col f1 s = check_col f2 s
Proof
    rpt strip_tac >>
    sg `MAP (f1 o FST) (toAList s) = MAP (f2 o FST) (toAList s)` THEN1 (
        simp [LIST_EQ_REWRITE] >>
        rw [EL_MAP] >>
        first_x_assum match_mp_tac >>
        imp_res_tac EL_MEM >>
        `MEM (FST (EL x (toAList s))) (MAP FST (toAList s))` by (simp [MEM_MAP, EXISTS_PROD] >> metis_tac [PAIR]) >>
        fs [set_MAP_FST_toAList_eq_domain]
    ) >>
    simp [check_col_def]
QED

Theorem check_partial_col_equal_col:
     !l live flive f1 f2.
    (!r. MEM r l ==> f1 r = f2 r) ==>
    check_partial_col f1 l live flive = check_partial_col f2 l live flive
Proof
    Induct_on `l` >>
    rw [check_partial_col_def] >>
    metis_tac []
QED

Theorem check_clash_tree_equal_col:
     !f1 f2 ct live flive.
    (!r. r IN in_clash_tree ct ==> f1 r = f2 r) /\
    (!r. r IN domain live ==> f1 r = f2 r) ==>
    check_clash_tree f1 ct live flive = check_clash_tree f2 ct live flive
Proof
    NTAC 2 gen_tac >>
    Induct_on `ct` >>
    rw [] >> TRY (rename1 `Branch optcutset ct1 ct2`) >> TRY (rename1 `Seq ct1 ct2`) >>

    fs [check_clash_tree_def, in_clash_tree_set_eq]
    THEN1 (
        `!r. MEM r l ==> f1 r = f2 r` by simp [] >>
        `!r. MEM r l0 ==> f1 r = f2 r` by simp [] >>
        imp_res_tac check_partial_col_equal_col >>
        sg `MAP f1 l = MAP f2 l` THEN1 (
            rw [LIST_EQ_REWRITE, EL_MAP] >>
            imp_res_tac EL_MEM >>
            fs []
        ) >>
        simp []
    )
    THEN1 (
        simp [check_col_equal_col]
    )
    THEN1 (
        rpt (first_x_assum (qspecl_then [`live`, `flive`] assume_tac)) >>
        Cases_on `optcutset` >> fs [] >> rfs [] >>
        rpt CASE_TAC
        THEN1 (
            rename1 `check_clash_tree _ ct2 _ _ = SOME (livein2, flivein2)` >>
            rename1 `check_clash_tree _ ct1 _ _ = SOME (livein1, flivein1)` >>
            match_mp_tac check_partial_col_equal_col >>
            rw [MEM_MAP, EXISTS_PROD, MEM_toAList, lookup_difference] >>
            imp_res_tac check_clash_tree_output_subset >>
            `r IN domain livein2` by simp [domain_lookup] >>
            fs [SUBSET_DEF] >>
            metis_tac []
        )
        THEN1 (
            simp [check_col_equal_col]
        )
    )
    THEN1 (
        first_x_assum (qspecl_then [`live`, `flive`] assume_tac) >>
        rpt CASE_TAC >>
        rename1 `check_clash_tree _ _ _ _ = SOME (livein2, flivein2)` >>
        first_x_assum (qspecl_then [`livein2`, `flivein2`] assume_tac) >>
        imp_res_tac check_clash_tree_output_subset >>
        fs [SUBSET_DEF] >>
        metis_tac []
    )
QED


Theorem linear_scan_reg_alloc_correct:
     !k moves ct forced.
    EVERY (\r1,r2. in_clash_tree ct r1 /\ in_clash_tree ct r2) forced ==>
    ?col livein flivein.
    linear_scan_reg_alloc k moves ct forced = Success col /\
    check_clash_tree (sp_default col) ct LN LN = SOME (livein, flivein) /\
    (!r. in_clash_tree ct r ==>
      r IN domain col /\
      if is_phy_var r then
        sp_default col r = r DIV 2
      else if is_stack_var r then
        k <= (sp_default col r)
      else
        T
    ) /\
    (!r. r IN domain col ==> in_clash_tree ct r) /\
    EVERY (\r1,r2. (sp_default col) r1 = (sp_default col) r2 ==> r1 = r2) forced
Proof
    rpt strip_tac >>
    simp [linear_scan_reg_alloc_def, run_linear_reg_alloc_intervals_def, run_i_linear_scan_hidden_state_def, run_def, linear_reg_alloc_and_extract_coloration_def] >>

    `?bijstate. find_bijection_clash_tree find_bijection_init ct = bijstate` by simp [] >>
    `?ct'. apply_bij_on_clash_tree ct bijstate.bij = ct'` by simp [] >>
    `?forced'. MAP (\r1,r2. (the 0 (lookup r1 bijstate.bij), the 0 (lookup r2 bijstate.bij))) forced = forced'` by simp [] >>
    `?moves'. MAP (\p,(r1,r2). (p,(the 0 (lookup r1 bijstate.bij), the 0 (lookup r2 bijstate.bij)))) moves = moves'` by simp [] >>
    `?reglist_unsorted. (MAP SND (toAList bijstate.bij)) = reglist_unsorted` by simp [] >>
    `?sth. linear_scan_hidden_state (REPLICATE (bijstate.nmax + 1) 0) (REPLICATE (bijstate.nmax + 1) 1)
                                    (REPLICATE (bijstate.nmax + 1) 1) (REPLICATE (bijstate.nmax + 1) 0)
                                    (REPLICATE (LENGTH moves) (0, 0, 0)) = sth` by simp [] >>
    simp msimps >>
    qspecl_then [`find_bijection_init`, `ct`, `EMPTY`] mp_tac find_bijection_clash_tree_invariants >>
    impl_tac THEN1 simp [find_bijection_init_invariants] >>
    simp [] >> strip_tac >>

    qspecl_then [`bijstate.bij`, `ct`] mp_tac in_clash_tree_apply_bij >>
    impl_tac THEN1 fs [good_bijection_state_def] >>
    strip_tac >> rfs [] >>

    sg `ALL_DISTINCT reglist_unsorted` THEN1 (
        simp [EL_ALL_DISTINCT_EL_EQ] >>
        qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
        simp [] >> rpt strip_tac >>
        simp [EL_MAP] >>
        eq_tac >> strip_tac >> simp [] >>
        `!(p1 : num#num) (p2 : num#num). SND p1 = SND p2 <=> (?a b c. p1 = (a,c) /\ p2 = (b,c))` by (simp [FORALL_PROD] >> metis_tac []) >>
        fs [] >>
        imp_res_tac EL_MEM >>
        rfs [MEM_toAList] >>
        fs [good_bijection_state_def, sp_inverts_def] >>
        `a = b` by metis_tac [SOME_11] >>
        `ALL_DISTINCT (MAP FST (toAList bijstate.bij))` by simp [ALL_DISTINCT_MAP_FST_toAList] >>
        `ZIP (MAP FST (toAList bijstate.bij), MAP SND (toAList bijstate.bij)) = toAList bijstate.bij` by simp [ZIP_MAP_FST_SND_EQ] >>
        `ALL_DISTINCT (ZIP (MAP FST (toAList bijstate.bij), MAP SND (toAList bijstate.bij)))` by fs [ALL_DISTINCT_ZIP] >>
        rfs [EL_ALL_DISTINCT_EL_EQ] >>
        metis_tac []
    ) >>

    qspecl_then [`k`, `moves'`, `ct'`, `forced'`] mp_tac (linear_reg_alloc_without_renaming_correct |> REWRITE_RULE msimps) >>
    impl_tac THEN1 (
        simp [] >>
        strip_tac THEN1 rw [EL_REPLICATE] >>
        strip_tac THEN1 rw [EL_REPLICATE] >>
        strip_tac THEN1 rw [] >>
        strip_tac THEN1 (
            `!r. (?v. lookup r bijstate.bij = SOME v) <=> in_clash_tree ct r` by (simp [GSYM domain_lookup] >> fs [good_bijection_state_def, EXTENSION, IN_DEF]) >>
            rw [MEM_MAP, EXISTS_PROD, MEM_toAList] >>
            fs [IN_DEF] >>
            metis_tac [the_def]
        ) >>
        strip_tac THEN1 (
            fs [good_bijection_state_def] >>
            rw [in_clash_tree_apply_bij] >>
            rw [intLib.COOPER_PROVE ``!(a : num) b. a < b+1 <=> a <= b``]
        ) >>
        strip_tac THEN1 (
            fs [EVERY_MEM, FORALL_PROD] >>
            rw [MEM_MAP, EXISTS_PROD] >>
            fs [IN_DEF] >>
            metis_tac []
        ) >>
        strip_tac THEN1 (
            rw [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD] >>
            fs [good_bijection_state_def] >>
            rw [intLib.COOPER_PROVE ``!(a : num) b. a < b+1 <=> a <= b``]
        ) >>
        strip_tac THEN1 (
            fs [good_bijection_state_def] >>
            `LENGTH reglist_unsorted = LENGTH (toAList bijstate.bij)` by rw [] >>
            `LENGTH (toAList bijstate.bij) = CARD (domain bijstate.bij)` by simp [LENGTH_toAList, size_domain] >>
            `LENGTH sth.sorted_regs = bijstate.nmax+1` by rw [] >>
            sg `INJ (\r. the 0 (lookup r bijstate.bij)) (domain bijstate.bij) (set (GENLIST (\x.x) (bijstate.nmax + 1)))` THEN1 (
                simp [INJ_DEF] >>
                strip_tac THEN1 (
                    simp [MEM_GENLIST, intLib.COOPER_PROVE ``!(a : num) b. a < b+1 <=> a <= b``]
                ) >>
                rpt strip_tac >>
                fs [domain_lookup] >>
                rfs [the_def, sp_inverts_def] >>
                metis_tac [SOME_11]
            ) >>
            imp_res_tac INJ_CARD >> fs [] >>
            `!n. ALL_DISTINCT (GENLIST (\x.x) n)` by simp [ALL_DISTINCT_GENLIST] >>
            `!n. CARD (set (GENLIST (\x.x) n)) = n` by simp [ALL_DISTINCT_CARD_LIST_TO_SET] >>
            fs []
        ) >>
        rw []
    ) >>
    strip_tac >> fs [case_eq_thms] >>

    qspecl_then [`bijstate.bij`, `bijstate.invbij`, `sthout`, `reglist_unsorted`, `LN`] mp_tac extract_coloration_output >>
    impl_tac THEN1 (
        fs [good_bijection_state_def] >>
        strip_tac
        THEN1 (
            qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
            simp [EVERY_MEM, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup] >>
            fs [sp_inverts_def] >>
            metis_tac []
        )
        THEN1 (
            qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
            `LENGTH sth.colors = bijstate.nmax+1` by rw [] >>
            simp [EVERY_MEM, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup, intLib.COOPER_PROVE ``!(a : num) b. a < b+1 <=> a <= b``] >>
            metis_tac [the_def]
        )
    ) >>
    strip_tac >> simp [] >> fs [lookup_def] >>

    qspecl_then [`bijstate.bij`, `bijstate.invbij`, `\r. EL r sthout.colors`, `ct`, `LN`, `LN`, `LN`, `LN`, `livein`, `flivein`] mp_tac check_clash_tree_apply_bijection >>
    impl_tac THEN1 fs [good_bijection_state_def] >>
    simp [] >> strip_tac >>

    sg `!r. in_clash_tree ct r ==> sp_default col r = EL (the 0 (lookup r bijstate.bij)) sthout.colors` THEN1 (
        rpt strip_tac >>
        `r IN domain bijstate.bij` by rfs [good_bijection_state_def, IN_DEF] >>
        sg `MEM (the 0 (lookup r bijstate.bij)) reglist_unsorted` THEN1 (
            qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
            simp [MEM_MAP, EXISTS_PROD, MEM_toAList] >>
            fs [domain_lookup, the_def] >>
            asm_exists_tac >> simp []
        ) >>
        first_x_assum (qspec_then `r` assume_tac) >>
        rfs [] >>
        simp [sp_default_def]
    ) >>

    qspecl_then [`sp_default col`, `\r. EL (the 0 (lookup r bijstate.bij)) sthout.colors`, `ct`, `LN`, `LN`] mp_tac check_clash_tree_equal_col >>
    impl_tac THEN1 simp [IN_DEF] >>
    strip_tac >> simp [] >>

    strip_tac THEN1 (
        rpt strip_tac
        THEN1 (
            `r IN domain bijstate.bij` by rfs [good_bijection_state_def, EXTENSION, IN_DEF] >>
            sg `MEM (the 0 (lookup r bijstate.bij)) reglist_unsorted` THEN1 (
                qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
                simp [MEM_MAP, EXISTS_PROD, MEM_toAList] >>
                `r IN domain bijstate.bij` by rfs [good_bijection_state_def, EXTENSION, IN_DEF] >>
                fs [domain_lookup, the_def] >>
                asm_exists_tac >> simp []
            ) >>
            `lookup r col = SOME (EL (the 0 (lookup r bijstate.bij)) sthout.colors)` by metis_tac [] >>
            simp [domain_lookup]
        )
        THEN1 (
            sg `in_clash_tree ct' (the 0 (lookup r bijstate.bij))` THEN1 (
                simp [IN_DEF] >>
                qexists_tac `r` >> simp []
            ) >>
            CASE_TAC
            THEN1 (
                sg `is_phy_var (the 0 (lookup r bijstate.bij))` THEN1 (
                    fs [good_bijection_state_def] >>
                    metis_tac [IN_DEF]
                ) >>
                fs [good_bijection_state_def] >>
                qpat_x_assum `!r. r IN in_clash_tree ct /\ is_phy_var r ==> _` (qspec_then `r` mp_tac) >>
                impl_tac THEN1 rfs [IN_DEF] >>
                strip_tac >>
                qpat_x_assum `!r. in_clash_tree ct' r ==> if _ then _ else _` (qspec_then `the 0 (lookup r bijstate.bij)` assume_tac) >>
                rfs [] >> metis_tac []
            )
            THEN1 (
                strip_tac >>
                sg `is_stack_var (the 0 (lookup r bijstate.bij))` THEN1 (
                    fs [good_bijection_state_def] >>
                    metis_tac [IN_DEF]
                ) >>
                `~is_phy_var (the 0 (lookup r bijstate.bij))` by metis_tac [convention_partitions] >>
                fs [good_bijection_state_def] >>
                qpat_x_assum `!r. in_clash_tree ct' r ==> if _ then _ else _` (qspec_then `the 0 (lookup r bijstate.bij)` assume_tac) >>
                rfs []
            )
        )
    ) >>

    strip_tac THEN1 (
        rpt strip_tac >>
        `r IN domain bijstate.bij` by fs [SUBSET_DEF] >>
        fs [good_bijection_state_def, IN_DEF]
    )

    THEN1 (
        simp [EVERY_MEM, FORALL_PROD] >>
        rpt strip_tac >>
        rename1 `MEM (r1, r2) forced` >>
        `in_clash_tree ct r1 /\ in_clash_tree ct r2` by (fs [EVERY_MEM, FORALL_PROD] >> metis_tac []) >>
        `r1 IN domain bijstate.bij /\ r2 IN domain bijstate.bij` by (fs [good_bijection_state_def, IN_DEF, EXTENSION] >> metis_tac []) >>
        sg `MEM (the 0 (lookup r1 bijstate.bij)) reglist_unsorted /\ MEM (the 0 (lookup r2 bijstate.bij)) reglist_unsorted` THEN1 (
            strip_tac >>
            qpat_x_assum `_ = reglist_unsorted` (fn th => assume_tac (GSYM th)) >>
            simp [MEM_MAP, EXISTS_PROD, MEM_toAList] >>
            fs [domain_lookup, the_def] >>
            metis_tac []
        ) >>
        `lookup r1 col = SOME (EL (the 0 (lookup r1 bijstate.bij)) sthout.colors) /\ lookup r2 col = SOME (EL (the 0 (lookup r2 bijstate.bij)) sthout.colors)` by metis_tac [] >>
        fs [sp_default_def] >>
        `MEM (the 0 (lookup r1 bijstate.bij), the 0 (lookup r2 bijstate.bij)) forced'` by (rw [MEM_MAP, EXISTS_PROD] >> metis_tac []) >>
        `the 0 (lookup r1 bijstate.bij) = the 0 (lookup r2 bijstate.bij)` by fs [EVERY_MEM, FORALL_PROD] >>
        fs [domain_lookup] >> rfs [the_def, good_bijection_state_def, sp_inverts_def] >>
        metis_tac [SOME_11]
    )
QED

val _ = export_theory ();
