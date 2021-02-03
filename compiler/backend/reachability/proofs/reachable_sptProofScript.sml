(*
  Proof of correctness of closure operation over num_set num_maps
*)

open preamble reachable_sptTheory

val _ = new_theory "reachable_sptProof";


(**************************** num_set_tree_union *****************************)

Theorem num_set_tree_union_empty:
     ∀ t1 t2 . isEmpty (num_set_tree_union t1 t2) ⇔ isEmpty t1 ∧ isEmpty t2
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

Theorem lookup_num_set_tree_union:
  ∀t1 t2 n.
    lookup n (num_set_tree_union t1 t2) =
    case lookup n t1 of
      SOME x => (
        case lookup n t2 of
          SOME y => SOME (union x y)
        | NONE => SOME x)
    | NONE => lookup n t2
Proof
  Induct >> rw[] >> gvs[lookup_def]
  >- simp[num_set_tree_union_def] >>
  IF_CASES_TAC >> gvs[lookup_def] >>
  Cases_on `t2` >> gvs[lookup_def, num_set_tree_union_def] >>
  EVERY_CASE_TAC >> gvs[]
QED


(**************************** OTHER LEMMAS *****************************)

Theorem wf_closure_spt:
  ∀ reachable tree.
    wf reachable ∧
    (∀ n x . lookup n tree = SOME x ⇒ wf x)
  ⇒ wf (closure_spt reachable tree)
Proof
    recInduct closure_spt_ind >> rw[] >>
    once_rewrite_tac [closure_spt_def] >> rw[] >> fs[] >>
    last_x_assum irule >> goal_assum drule >>
    irule wf_union >> simp[] >>
    irule wf_spt_fold_union_num_set >> simp[wf_def, lookup_inter] >>
    rw[] >> EVERY_CASE_TAC >> gvs[] >> res_tac
QED


(************************** ADJACENCY/REACHABILITY ***************************)

Theorem adjacent_domain:
     ∀ tree x y . is_adjacent tree x y ⇒ x ∈ domain tree
Proof
    rw[is_adjacent_def] >> rw[domain_lookup]
QED

Theorem reachable_domain:
     ∀ tree x y . is_reachable tree x y
  ⇒ (x = y ∨ x ∈ domain tree)
Proof
    simp[is_reachable_def] >> strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
    metis_tac[adjacent_domain]
QED

Theorem reachable_LHS_NOTIN:
  ∀tree n x. is_reachable tree n x ∧ n ∉ domain tree ⇒ n = x
Proof
  rw[is_reachable_def] >> gvs[Once RTC_CASES1, is_adjacent_def, domain_lookup]
QED

Theorem rtc_is_adjacent:
  (∀ k . k ∈ t ⇒ ∀ n . (is_adjacent fullTree k n ⇒ n ∈ t)) ⇒
  ∀ x y . RTC(is_adjacent fullTree) x y ⇒ x ∈ t ⇒ y ∈ t
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  fs[SUBSET_DEF] >> metis_tac []
QED

Theorem is_adjacent_num_set_tree_union:
  ∀ t1 t2 n m .
    is_adjacent t1 n m ⇒ is_adjacent (num_set_tree_union t1 t2) n m
Proof
  rw[is_adjacent_def, lookup_num_set_tree_union] >> simp[] >>
  EVERY_CASE_TAC >> gvs[lookup_union]
QED

Theorem is_reachable_num_set_tree_union:
  ∀ t1 t2 n m .
    is_reachable t1 n m
  ⇒ is_reachable (num_set_tree_union t1 t2) n m
Proof
  simp[is_reachable_def] >> strip_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
  simp[Once RTC_CASES2] >> disj2_tac >>
  goal_assum drule >> irule is_adjacent_num_set_tree_union >> simp[]
QED


(**************************** MAIN LEMMAS *****************************)

Theorem closure_spt_lemma:
  ∀ reachable tree closure (roots : num set).
    closure_spt reachable tree = closure ∧
    roots ⊆ domain reachable ∧
    (∀k. k ∈ domain reachable ⇒ ∃n. n ∈ roots ∧ is_reachable tree n k)
  ⇒ domain closure = {a | ∃n. n ∈ roots ∧ is_reachable tree n a}
Proof
  recInduct closure_spt_ind >> rw[] >>
  once_rewrite_tac[closure_spt_def] >> simp[] >>
  IF_CASES_TAC >> gvs[]
  >- (
    gvs[subspt_domain, domain_spt_fold_union_num_set, EXTENSION,
        SUBSET_DEF, PULL_EXISTS] >>
    rw[] >> eq_tac >> rw[] >>
    irule rtc_is_adjacent >>
    gvs[is_reachable_def] >>
    goal_assum (drule_at Any) >> gvs[] >> rw[] >>
    first_x_assum irule >>
    gvs[lookup_inter, is_adjacent_def, domain_lookup] >>
    qexistsl_tac [`aSetx`,`k`] >> simp[]
    ) >>
  first_x_assum irule >> simp[] >> rw[] >> gvs[domain_union, SUBSET_DEF] >>
  gvs[domain_spt_fold_union_num_set, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[domain_lookup] >>
  first_x_assum drule >> strip_tac >>
  goal_assum drule >> gvs[is_reachable_def] >>
  irule (iffRL RTC_CASES2) >> DISJ2_TAC >>
  goal_assum drule >> simp[is_adjacent_def]
QED

Theorem closure_spt_thm:
  ∀ tree start.
    domain (closure_spt start tree) =
      {a | ∃n. n ∈ domain start ∧ is_reachable tree n a}
Proof
  rw[] >> irule closure_spt_lemma >>
  irule_at Any EQ_REFL >> simp[] >> rw[] >>
  goal_assum drule >> simp[is_reachable_def]
QED


val _ = export_theory();
