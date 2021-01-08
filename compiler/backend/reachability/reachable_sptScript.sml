(*
  Implementation of various closure operations for num_map and num_set
*)

open preamble sptreeTheory

val _ = new_theory "reachable_spt";

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
       | BN t1' t2' =>
            BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2')
       | BS t1' a t2' =>
        BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')) ∧
  (num_set_tree_union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS b => BS t1 (union a b) t2
       | BN t1' t2' =>
            BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')
       | BS t1' b t2' =>
            BS (num_set_tree_union t1 t1') (union a b)
                (num_set_tree_union t2 t2'))
`;

val superdomain_def = Define `
    superdomain (t:num_set num_map) = spt_fold union LN t
`

val mk_wf_set_tree_def = Define `
    mk_wf_set_tree t =
        let t' = union t (map (K LN) (superdomain t)) in mk_wf (map (mk_wf) t')
`

Theorem superdomain_rewrite:
  ∀tree.
    domain (superdomain tree) =
    {n | ∃k aSet. lookup k tree = SOME aSet ∧ n ∈ domain aSet}
Proof
  rw[EXTENSION] >> eq_tac >> rw[] >>
  fs[superdomain_def, domain_lookup,
     lookup_spt_fold_union_STRONG, lookup_def] >>
  goal_assum drule >> simp[]
QED

Theorem domain_spt_fold_union_eq:
  ∀y tree. domain (spt_fold union y tree) = domain y ∪ domain (superdomain tree)
Proof
  simp[superdomain_rewrite] >>
  rw[EXTENSION, domain_lookup, lookup_spt_fold_union_STRONG]
QED

Definition closure_spt_def:
  closure_spt (reachable: num_set) tree =
    let sets = inter tree reachable in
    let nodes = spt_fold union LN sets in
    if subspt nodes reachable then reachable
    else closure_spt (union reachable nodes) tree
Termination
  WF_REL_TAC `measure (λ (r,t). size (difference (superdomain t) r))` >> rw[] >>
  gvs[subspt_domain, SUBSET_DEF] >>
  irule size_diff_less >>
  fs[domain_union, domain_difference, domain_spt_fold_union_eq,
     GSYM MEMBER_NOT_EMPTY] >>
  goal_assum drule >> simp[] >>
  gvs[superdomain_rewrite, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[] >> goal_assum drule >> simp[]
End

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

val is_adjacent_def = Define `
    is_adjacent tree x y =
    ∃ aSetx.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () )
`;

val is_reachable_def = Define `
    is_reachable tree = RTC (is_adjacent tree)
`;

val _ = export_theory();
