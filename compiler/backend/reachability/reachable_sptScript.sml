(*
  Implementation of closure operation over num_set num_maps
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

Definition closure_spt_def:
  closure_spt (reachable: num_set) tree =
    let sets = inter tree reachable in
    let nodes = spt_fold union LN sets in
    if subspt nodes reachable then reachable
    else closure_spt (union reachable nodes) tree
Termination
  WF_REL_TAC `measure (λ (r,t). size (difference (spt_fold union LN t) r))` >>
  rw[] >>
  gvs[subspt_domain, SUBSET_DEF] >>
  irule size_diff_less >>
  gvs[domain_union, domain_spt_fold_union_num_set, lookup_inter] >>
  EVERY_CASE_TAC >> gvs[] >>
  simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
  goal_assum drule >> goal_assum drule >> simp[] >>
  goal_assum (drule_at Any) >>
  qexists_tac `k` >> simp[]
End

val is_adjacent_def = Define `
    is_adjacent tree x y =
    ∃ aSetx.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () )
`;

val is_reachable_def = Define `
    is_reachable tree = RTC (is_adjacent tree)
`;

val _ = export_theory();
