(*

  A heap-sort variant that builds a list of exactly-balanced heaps.

  This is prototyped and verified as a standard recursive functional program.

  It is also presented as an in-array algorithm, where the list of heaps are
  placed in segments of an array.

  This allows the one algorithm to be evaluated either via its pure functional
  instance or as an in-place algorithm in CakeML.

  The heap segments all point in the correct direction, so, unlike a standard
  in-array heap-sort, sorting a sorted array requires linear-time comparisons
  and no data moves.
*)

Theory heap_list_sort
Ancestors
   list rich_list sorting container bag

Datatype:
  simple_tree = Empty_Tree | Node 'a simple_tree simple_tree
End

Definition tree_top_less_def:
  tree_top_less R Empty_Tree y = T /\
  tree_top_less R (Node x _ _) y = R x y
End

(* Invariant that a tree encodes a heap. *)
Definition heap_tree_inv_def:
  (heap_tree_inv R n Empty_Tree = (n = 0)) /\
  (heap_tree_inv R n (Node y l r) = (n > 0 /\
    heap_tree_inv R (n - 1) l /\ tree_top_less R l y /\
    heap_tree_inv R (n - 1) r /\ tree_top_less R r y
  ))
End

Theorem heap_tree_inv_empty_eq_eq[local]:
  heap_tree_inv R n t ==> ((t = Empty_Tree) = (n = 0))
Proof
  Cases_on `t` \\ simp [heap_tree_inv_def]
QED

(* Invariant for a list of trees. *)
Definition heaps_tree_inv_def:
  heaps_tree_inv R xs = (EVERY (\(t, n). heap_tree_inv R n t /\ n > 0) xs /\
    SORTED (\(t1, _) (t2, _). case t1 of Empty_Tree => F | Node x _ _ =>
        (case t2 of Empty_Tree => F | Node y _ _ => R y x)) xs
  )
End

Theorem heaps_tree_inv_rec_def:
  (heaps_tree_inv R [] = T) /\
  (heaps_tree_inv R (x :: xs) = (heap_tree_inv R (SND x) (FST x) /\ SND x > 0 /\
    ((xs <> []) ==> tree_top_less R (FST (HD xs)) (case x of (Node y _ _, _) => y)) /\
    heaps_tree_inv R xs))
Proof
  simp [heaps_tree_inv_def]
  \\ Cases_on `x` \\ simp []
  \\ Cases_on `xs` \\ simp []
  \\ rpt (pairarg_tac \\ fs [])
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [hd (CONJUNCTS heap_tree_inv_def)]
  \\ simp [tree_top_less_def]
  \\ EQ_TAC \\ rw [] \\ simp []
QED

Definition tree_to_bag_def:
  tree_to_bag Empty_Tree = {||} /\
  tree_to_bag (Node x l r) = BAG_INSERT x (BAG_UNION (tree_to_bag l) (tree_to_bag r))
End

(* Insert a value, replacing the top value of a balanced heap/tree, and moving
   the new value down the heap as necessary to maintain the invariant. *)
Definition insert_tree_inv_def:
  insert_tree_inv R Empty_Tree x = Empty_Tree /\
  insert_tree_inv R (Node _ l r) x = (case l of Empty_Tree => Node x l r
    | Node lx _ _ => (case r of Empty_Tree => Node x l r
    | Node rx _ _ => if R lx x /\ R rx x then Node x l r
    else if R lx rx then Node rx l (insert_tree_inv R r x)
    else Node lx (insert_tree_inv R l x) r
  ))
End

Theorem insert_tree_inv_size:
  simple_tree_size (K 0) (insert_tree_inv R t x) =
  simple_tree_size (K 0) t
Proof
  Induct_on `t`
  \\ simp [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
QED

(* Insert similarly into a list of heap/trees. *)
Definition insert_trees_inv_def:
  (insert_trees_inv R [] x = []) /\
  (insert_trees_inv R ((t1, n1) :: ts) x = (case ts of
    | [] => [(insert_tree_inv R t1 x, n1)]
    | (t2, n2) :: tl_ts =>
        (case t1 of Empty_Tree =>
            (* won't happen, leave list the same *) ((t1, n1) :: ts)
        | Node _ l r => (case t2 of Empty_Tree =>
            (* won't happen, leave list the same *) ((t1, n1) :: ts)
        | Node t2x _ _ => if ~ (R t2x x) /\
            ~ (case l of Empty_Tree => F | Node lx _ _ => R t2x lx) /\
            ~ (case r of Empty_Tree => F | Node rx _ _ => R t2x rx)
        then (Node t2x l r, n1) :: insert_trees_inv R ts x
        else (insert_tree_inv R t1 x, n1) :: ts
  ))))
End

Theorem insert_trees_inv_size:
  MAP (simple_tree_size (K 0) o FST) (insert_trees_inv R ts x) =
  MAP (simple_tree_size (K 0) o FST) ts
Proof
  measureInduct_on `LENGTH ts`
  \\ Cases_on `ts`
  \\ simp [insert_trees_inv_def]
  \\ Cases_on `h`
  \\ simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_tree_inv_size]
QED

Theorem insert_trees_inv_length =
  Q.AP_TERM `LENGTH` insert_trees_inv_size |> REWRITE_RULE [LENGTH_MAP]

(* Add a new value, assembling two heaps into a larger heap if needed. *)
Definition add_to_heaps_step1_def:
  add_to_heaps_step1 ts x = (case ts of
    (t1, n1) :: (t2, n2) :: ts2 => if n1 = n2
        then (Node x t2 t1, n1 + 1) :: ts2
        else (Node x Empty_Tree Empty_Tree, 1) :: ts
  | _ => (Node x Empty_Tree Empty_Tree, 1) :: ts
  )
End

Definition add_to_heaps_def:
  add_to_heaps R ts x = insert_trees_inv R (add_to_heaps_step1 ts x) x
End

Definition add_values_to_heaps_def:
  add_values_to_heaps R ts [] = ts /\
  add_values_to_heaps R ts (x :: xs) =
    add_values_to_heaps R (add_to_heaps R ts x) xs
End

Definition add_heap_to_heaps_def:
  add_heap_to_heaps R ts t n = (case t of
    Empty_Tree => ts
  | Node x l r => (let ord = (case ts of ((Node y _ _, _) :: _) => R y x | _ => T)
    in if ord then (t, n) :: ts
        else insert_trees_inv R ((t, n) :: ts) x
  ))
End

Theorem add_heap_to_heaps_size:
  SUM (MAP (\t_n. simple_tree_size (K 0) (FST t_n)) (add_heap_to_heaps R ts t n)) =
    simple_tree_size (K 0) t + SUM (MAP (\t_n. simple_tree_size (K 0) (FST t_n)) ts)
Proof
  simp [add_heap_to_heaps_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [REWRITE_RULE [combinTheory.o_DEF] insert_trees_inv_size]
QED

Definition heaps_to_list_def:
  heaps_to_list R [] acc = acc /\
  heaps_to_list R ((Empty_Tree, _) :: ts) acc = acc /\
  heaps_to_list R ((Node x l r, n) :: ts) acc =
    let ts2 = add_heap_to_heaps R ts l (n - 1);
        ts3 = add_heap_to_heaps R ts2 r (n - 1)
    in heaps_to_list R ts3 (x :: acc)
Termination
  WF_REL_TAC `measure (\(R, ts, acc). SUM (MAP (simple_tree_size (K 0) o FST) ts))`
  \\ rw []
  \\ simp [add_heap_to_heaps_size]
End

Definition heap_list_sort_def:
  heap_list_sort R xs = heaps_to_list R (add_values_to_heaps R [] xs) []
End

(* Invariant preservation. *)
Theorem insert_tree_inv_less[local]:
  (case t of Node _ l r => tree_top_less R l y /\ tree_top_less R r y | _ => T) ==>
  R x y ==>
  transitive R ==> total R ==>
  tree_top_less R (insert_tree_inv R t x) y
Proof
  Cases_on `t` \\ simp [insert_tree_inv_def, tree_top_less_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_top_less_def]
QED

Theorem total_lemma[local]:
  total R ==> ~ R x y ==> R y x
Proof
  metis_tac [relationTheory.total_def]
QED

Theorem transitive_lemma[local] = hd (RES_CANON relationTheory.transitive_def)

Theorem insert_tree_inv:
  heap_tree_inv R n t ==>
  transitive R ==> total R ==>
  heap_tree_inv R n (insert_tree_inv R t x)
Proof
  qid_spec_tac `n`
  \\ Induct_on `t`
  \\ rw [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ gs [heap_tree_inv_def, tree_top_less_def]
  \\ irule_at Any insert_tree_inv_less
  \\ simp []
  \\ metis_tac [total_lemma, transitive_lemma]
QED

Theorem insert_tree_inv_greater[local]:
  R x y \/ (case l of Node ly _ _ => R x ly | _ => F) \/
      (case r of Node ry _ _ => R x ry | _ => F) ==>
  transitive R ==> total R ==>
  ((l = Empty_Tree) = (r = Empty_Tree)) ==>
  R x (case insert_tree_inv R (Node x_old l r) y of
    Empty_Tree => Anything | Node z _ _ => z)
Proof
  simp [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_top_less_def]
  \\ metis_tac [transitive_lemma, total_lemma]
QED

Theorem insert_tree_inv_contents:
  tree_to_bag (insert_tree_inv R t x) = (case t of Empty_Tree => {||}
    | Node _ l r => tree_to_bag (Node x l r))
Proof
  Induct_on `t`
  \\ simp [insert_tree_inv_def, tree_to_bag_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes]
QED

Theorem tree_top_less_mono:
  tree_top_less R t x ==> R x y ==>
  transitive R ==>
  tree_top_less R t y
Proof
  Cases_on `t`
  \\ simp [tree_top_less_def]
  \\ metis_tac [transitive_lemma]
QED

Theorem tree_top_less_neg[local]:
  (~ (case t of Empty_Tree => F | Node y _ _ => R x y)) ==>
  total R ==>
  tree_top_less R t x
Proof
  BasicProvers.EVERY_CASE_TAC \\ simp [tree_top_less_def]
  \\ metis_tac [total_lemma]
QED

Theorem heap_tree_inv_mono:
  heap_tree_inv R n (Node x l r) ==>
  R x y ==> transitive R ==>
  heap_tree_inv R n (Node y l r)
Proof
  simp [heap_tree_inv_def]
  \\ metis_tac [tree_top_less_mono]
QED

Theorem insert_trees_inv_less[local]:
  (case ts of [] => F | (Empty_Tree, _) :: _ => F | ((Node _ l r, _) :: ts2) =>
    tree_top_less R l y /\ tree_top_less R r y /\
    (ts2 <> [] ==> FST (HD (ts2)) <> Empty_Tree /\
        tree_top_less R (FST (HD ts2)) y)) ==>
  R x y ==>
  transitive R ==> total R ==>
  tree_top_less R (FST (HD (insert_trees_inv R ts x))) y
Proof
  BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ rw []
  \\ fs [tree_top_less_def, insert_tree_inv_less]
QED

Theorem insert_trees_inv:
  heaps_tree_inv R ts ==>
  transitive R ==> total R ==>
  heaps_tree_inv R (insert_trees_inv R ts x)
Proof
  Induct_on `ts`
  \\ simp [insert_trees_inv_def, pairTheory.FORALL_PROD, heaps_tree_inv_rec_def]
  \\ rpt gen_tac
  \\ ntac 2 BasicProvers.TOP_CASE_TAC
  \\ simp [insert_tree_inv, heaps_tree_inv_rec_def]
  \\ ntac 2 BasicProvers.TOP_CASE_TAC
  \\ simp [insert_tree_inv, heaps_tree_inv_rec_def]
  \\ fs [hd (CONJUNCTS heap_tree_inv_def)]
  \\ csimp []
  \\ rw [heaps_tree_inv_rec_def]
  \\ simp [insert_tree_inv]
  >- (
    fs [heap_tree_inv_def, tree_top_less_def]
    \\ rpt (dxrule tree_top_less_neg)
    \\ simp []
  )
  >- (
    irule insert_trees_inv_less
    \\ fs [heap_tree_inv_def, tree_top_less_def]
    \\ fsrw_tac [SFY_ss] [total_lemma]
    \\ rpt strip_tac
    \\ Cases_on `t` \\ fs []
    \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  )
  >- (
    simp [tree_top_less_def]
    \\ irule insert_tree_inv_greater
    \\ fs [heap_tree_inv_def]
    \\ rpt (dxrule heap_tree_inv_empty_eq_eq)
    \\ simp []
  )
QED

Theorem insert_trees_inv_contents:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (insert_trees_inv R ts x)) =
    (case ts of [] => {||}
      | (Node _ l r, _) :: ts => BAG_UNION (tree_to_bag (Node x l r))
          (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)))
  )
Proof
  Induct_on `ts`
  \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def, tree_to_bag_def]
  \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ gs []
  \\ simp [insert_tree_inv_contents, tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes]
QED

Theorem insert_trees_non_empty:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  EVERY (\p. FST p <> Empty_Tree) (insert_trees_inv R ts x)
Proof
  Induct_on `ts`
  \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ gs []
  \\ rw [insert_tree_inv_def]
QED

Theorem add_values_to_heaps_contents:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (add_values_to_heaps R ts xs)) =
  BAG_UNION (LIST_TO_BAG xs) (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)) /\
  EVERY (\p. FST p <> Empty_Tree) (add_values_to_heaps R ts xs)
Proof
  qid_spec_tac `ts`
  \\ Induct_on `xs`
  \\ rw [add_values_to_heaps_def]
  \\ simp [add_to_heaps_def, add_to_heaps_step1_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ fs []
  \\ simp [insert_trees_inv_contents, insert_trees_non_empty, tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes, ASSOC_BAG_UNION, COMM_BAG_UNION]
QED

Theorem insert_tree_inv_adj[local]:
  insert_tree_inv R (Node x_dc l r) x =
  insert_tree_inv R (Node y_dc l r) x
Proof
  simp [insert_tree_inv_def]
QED

Theorem insert_tree_adj_inv[local]:
  heap_tree_inv R n (insert_tree_inv R (Node x l r) x)
  ==>
  heap_tree_inv R n (insert_tree_inv R (Node x_dc l r) x)
Proof
  simp [insert_tree_inv_def]
QED

Theorem insert_trees_adj_inv1[local]:
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x) ==>
  heaps_tree_inv R (insert_trees_inv R ((Node y_dc l r, n) :: ts) x)
Proof
  simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_tree_inv_def]
  \\ csimp [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem insert_trees_adj_inv2[local]:
  heaps_tree_inv R ts ==>
  heap_tree_inv R n (Node x_dc l r) ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x)
Proof
  Cases_on `heaps_tree_inv R ((Node x_dc l r, n) :: ts)`
  \\ simp [insert_trees_inv]
  \\ rw []
  \\ irule insert_trees_adj_inv1
  \\ qexists_tac `case HD ts of (Node x _ _, _) => x`
  \\ irule insert_trees_inv
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ Cases_on `FST (HD ts)` \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ fs [tree_top_less_def]
  \\ simp [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ fs [relationTheory.reflexive_def]
  \\ rw []
  \\ drule_then irule tree_top_less_mono
  \\ simp []
  \\ metis_tac [total_lemma]
QED

Theorem insert_trees_adj_inv3[local]:
  heaps_tree_inv R ts ==>
  heap_tree_inv R (n - 1) l ==>
  heap_tree_inv R (n - 1) r ==>
  n > 0 ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x)
Proof
  Cases_on `heap_tree_inv R n (Node (case l of Node y _ _ => y) l r) \/
      heap_tree_inv R n (Node (case r of Node y _ _ => y) l r)`
  >- (
    rw [] \\ fs []
    \\ irule insert_trees_adj_inv1
    \\ irule_at Any insert_trees_adj_inv2
    \\ simp []
    \\ first_x_assum (irule_at Any)
  )
  >- (
    rw [] \\ fs []
    \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [tree_top_less_def]
    \\ gs [relationTheory.reflexive_def]
    \\ irule insert_trees_adj_inv1
    \\ irule_at Any insert_trees_adj_inv2
    \\ simp [heap_tree_inv_def, relationTheory.reflexive_def, tree_top_less_def]
    \\ metis_tac [total_lemma]
  )
QED

Theorem add_values_to_heaps_inv:
  heaps_tree_inv R ts ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (add_values_to_heaps R ts xs)
Proof
  qid_spec_tac `ts`
  \\ Induct_on `xs`
  \\ rw [add_values_to_heaps_def]
  \\ simp [add_to_heaps_def, add_to_heaps_step1_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp []
  \\ first_x_assum irule
  \\ simp []
  \\ irule insert_trees_adj_inv3
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
QED

Theorem add_heap_to_heaps_contents[local]:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (add_heap_to_heaps R ts t n)) =
  BAG_UNION (tree_to_bag t) (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts))
Proof
  simp [add_heap_to_heaps_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_to_bag_def]
  \\ simp [insert_trees_inv_contents, insert_trees_non_empty, tree_to_bag_def]
QED

Theorem add_heap_to_heaps_not_empty[local]:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  EVERY (\p. FST p <> Empty_Tree) (add_heap_to_heaps R ts t n)
Proof
  simp [add_heap_to_heaps_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_trees_non_empty]
QED

Theorem add_heap_to_heaps_inv[local]:
  (t <> Empty_Tree ==> heap_tree_inv R n t) ==>
  heaps_tree_inv R ts ==>
  total R /\ transitive R /\ reflexive R ==>
  heaps_tree_inv R (add_heap_to_heaps R ts t n)
Proof
  simp [add_heap_to_heaps_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ csimp [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ rw []
  \\ irule insert_trees_adj_inv3
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem add_heap_to_heaps_less[local]:
  (ts <> [] ==> tree_top_less R (FST (HD ts)) x) ==>
  tree_top_less R t x ==>
  total R ==> transitive R ==>
  (add_heap_to_heaps R ts t n <> []) ==>
  heaps_tree_inv R ts ==>
  heap_tree_inv R n t ==>
  tree_top_less R (FST (HD (add_heap_to_heaps R ts t n))) x
Proof
  simp [add_heap_to_heaps_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ rw []
  \\ irule insert_trees_inv_less
  \\ fs [tree_top_less_def]
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ fsrw_tac [SFY_ss] [tree_top_less_mono]
  \\ CCONTR_TAC
  \\ Cases_on `ts`
  \\ gs [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem heaps_to_list_contents:
  ! R ts acc. EVERY (\p. FST p <> Empty_Tree) ts ==>
  LIST_TO_BAG (heaps_to_list R ts acc) =
  BAG_UNION (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)) (LIST_TO_BAG acc)
Proof
  recInduct heaps_to_list_ind
  \\ rw []
  \\ simp [heaps_to_list_def, tree_to_bag_def]
  \\ simp [add_heap_to_heaps_contents, add_heap_to_heaps_not_empty]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes, ASSOC_BAG_UNION, COMM_BAG_UNION]
QED

Theorem heaps_to_list_sorted:
  ! R ts acc. heaps_tree_inv R ts ==>
  transitive R ==> total R ==> reflexive R ==>
  SORTED R acc ==>
  ((ts <> []) ==> (acc <> []) ==> tree_top_less R (FST (HD ts)) (HD acc)) ==>
  SORTED R (heaps_to_list R ts acc)
Proof
  recInduct heaps_to_list_ind
  \\ rw [] \\ fs []
  \\ simp [heaps_to_list_def]
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ gs []
  \\ first_x_assum irule
  \\ simp [add_heap_to_heaps_inv]
  \\ rw []
  \\ simp [add_heap_to_heaps_less, add_heap_to_heaps_inv]
  \\ Cases_on `acc`
  \\ fs []
QED

Theorem heap_list_sort_sorted:
  reflexive R ==> transitive R ==> total R ==>
  SORTED R (heap_list_sort R xs)
Proof
  rw [heap_list_sort_def]
  \\ irule heaps_to_list_sorted
  \\ simp []
  \\ irule add_values_to_heaps_inv
  \\ simp [heaps_tree_inv_def]
QED

Theorem heap_list_sort_contents:
  LIST_TO_BAG (heap_list_sort R xs) = LIST_TO_BAG xs
Proof
  rw [heap_list_sort_def]
  \\ simp [heaps_to_list_contents, add_values_to_heaps_contents]
QED

Theorem heap_list_sort_PERM:
  PERM (heap_list_sort R xs) xs
Proof
  simp [GSYM PERM_LIST_TO_BAG, heap_list_sort_contents]
QED

