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

val close_spt_def = tDefine "close_spt" `
    close_spt (reachable :num_set) (seen :num_set) (tree :num_set spt) =
        let to_look = difference seen reachable in
        let new_sets = inter tree to_look in
            if new_sets = LN then reachable else
                let new_set = spt_fold union LN new_sets in
                    close_spt (union reachable to_look) (union seen new_set)
                        tree
    `
    (
        WF_REL_TAC `measure (λ (r, _, t) . size (difference t r))` >>
        rw[] >>
        match_mp_tac size_diff_less >>
        fs[domain_union, domain_difference] >>
        fs[inter_eq_LN, IN_DISJOINT, domain_difference] >>
        qexists_tac `x` >>
        fs[]
    )

val close_spt_ind = theorem "close_spt_ind";

val closure_spt_def = Define
    `closure_spt start tree = close_spt LN start tree`;

val wf_set_tree_def = Define `
    wf_set_tree tree ⇔
        (∀ x  y . (lookup x tree = SOME y) ⇒ domain y ⊆ domain tree) ∧
        (∀ n x . lookup n tree = SOME x ⇒ wf x) ∧
        wf tree
`

val is_adjacent_def = Define `
    is_adjacent tree x y =
    ∃ aSetx aSety.
        ( lookup x tree = SOME aSetx ) ∧ ( lookup y aSetx = SOME () ) ∧
        ( lookup y tree = SOME aSety )
`;

val is_reachable_def = Define `
    is_reachable tree = RTC (is_adjacent tree)
`;

val _ = export_theory();
