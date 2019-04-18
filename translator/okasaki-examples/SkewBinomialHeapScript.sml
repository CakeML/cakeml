(*
  Bootstraped Skew Binomial Heaps, based on Purely Functional Data Structures
  sections 9.3.2 and 10.2.2 (Chris Okasaki)
*)

open preamble
open bagTheory bagLib ml_translatorLib okasaki_miscTheory ml_translatorLib ListProgTheory;

val _ = new_theory "SkewBinomialHeap";

val _ = translation_extends "ListProg";

(* Definition of a Skew Binomial Tree *)
Datatype `sbTree = Sbnode 'a num ('a list) (sbTree list)`;

val leaf_def = Define `leaf x = (Sbnode x 0 [] [])`;
val root_def = Define `root (Sbnode x r a c) = x`;
val rank_def = Define `rank (Sbnode _ r _ _) = r`;
val aux_def = Define `aux (Sbnode _ _ a _) = a`;
val children_def = Define `children (Sbnode _ _ _ c) = c`;

val tree_link_def = Define `
  tree_link geq (Sbnode x1 r1 a1 c1) (Sbnode x2 r2 a2 c2) =
    if geq x1 x2
    then (Sbnode x2 (r2+1) a2 ((Sbnode x1 r1 a1 c1)::c2))
    else (Sbnode x1 (r1+1) a1 ((Sbnode x2 r2 a2 c2)::c1))
`;

val skew_link_def = Define `
  skew_link geq x t1 t2 =
    let l = tree_link geq t1 t2
    in let x' = root l
      and r = rank l
      and a = aux l
      and c = children l
      in
        (if geq x' x
         then (Sbnode x r (x'::a) c)
         else (Sbnode x' r (x::a) c))
  `;

val tree_to_bag_def = Define `
  (tree_to_bag (Sbnode x r a []) = (BAG_INSERT x (list_to_bag a))) /\
  (tree_to_bag (Sbnode x r a (c::cs)) =
    (BAG_UNION (tree_to_bag c) (tree_to_bag (Sbnode x r a cs))))
`;

val is_tree_ordered_def = Define `
      (is_tree_ordered geq (Sbnode x _ a []) = (BAG_EVERY (\y. geq y x) (list_to_bag a))) /\
      (is_tree_ordered geq (Sbnode x r a (c::cs)) =
         ((is_tree_ordered geq c) /\
         (BAG_EVERY (\y. geq y x) (tree_to_bag c)) /\
	 (is_tree_ordered geq (Sbnode x r a cs))))
`;

(* Definition of a Skew Binomial Heap *)

val _ = type_abbrev("sbHeap", ``:'a sbTree list``);

val is_empty_def = Define `is_empty h = (h = [])`;

val heap_to_bag_def = Define `
  (heap_to_bag [] = {||}) /\
  (heap_to_bag (t::ts) = BAG_UNION (tree_to_bag t) (heap_to_bag ts))
`;

val is_heap_ordered_def = Define `
  (is_heap_ordered geq [] = T) /\
  (is_heap_ordered geq (t::ts) = ((is_tree_ordered geq t) /\ (is_heap_ordered geq ts)))
`;

(* Insertion *)
val insert_def = Define `
  (insert geq x (y::y'::ys) =
    (if (rank y) = (rank y')
     then (skew_link geq x y y')::ys
     else (leaf x)::y::y'::ys)) /\
  (insert _ x ys = (leaf x)::ys)
`;

val insert_list_def = Define `
  (insert_list _ [] h = h) /\
  (insert_list geq (e::es) h =
    (insert geq e (insert_list geq es h)))
`;

(* findMin *)
val find_min_def = Define `
  (find_min _ [] = NONE) /\
  (find_min _ [x] = SOME (root x)) /\
  (find_min geq (x::xs) =
    let firstroot = (root x)
    in
      case (find_min geq xs) of
	NONE => NONE
      | (SOME minrest) => SOME (if (geq minrest firstroot) then firstroot else minrest))
`;

(* Merge *)
val binomial_insert_def = Define `
  (binomial_insert geq t [] = [t]) /\
  (binomial_insert geq t (t2::rest) =
    if (rank t) < (rank t2)
    then t::(t2::rest)
    else (binomial_insert geq (tree_link geq t t2) rest))
`;

val normalize_def = Define `
  (normalize geq [] = []) /\
  (normalize geq (t::ts) = (binomial_insert geq t ts))
`;

val merge_tree_def = Define `
  (merge_tree geq t [] = t) /\
  (merge_tree geq [] t = t) /\
  (merge_tree geq (x1::t1) (x2::t2) =
    if (rank x1) > (rank x2)
    then x2::(merge_tree geq (x1::t1) t2)
    else if (rank x2) > (rank x1)
         then x1::(merge_tree geq t1 (x2::t2))
         else (binomial_insert geq (tree_link geq x1 x2) (merge_tree geq t1 t2)))
`;

val merge_def = Define `
  merge geq t1 t2 = (merge_tree geq (normalize geq t1) (normalize geq t2))
`;

(* DeleteMin *)
val get_min_def = Define `
  (get_min geq [t] = (t,[])) /\
  (get_min geq (t::ts) =
    let (t', ts') = (get_min geq ts)
    in if (geq (root t') (root t))
       then (t, ts)
       else (t', t::ts'))
`;

val delete_min_def = Define `
  (delete_min geq [] = NONE) /\
  (delete_min geq ts =
    let (min, ts') = (get_min geq ts)
    in SOME (insert_list geq (aux min) (merge_tree geq (REVERSE (children min)) (normalize geq ts'))))
`;

(* Bootstraping Skew Binomial Heaps *)
Datatype `bsbHeap = Bsbempty | Bsbheap 'a (bsbHeap sbHeap)`;

val b_root_def = Define `
  (b_root (Bsbheap r _) = r)
`;

val b_children_def = Define `
  (b_children (Bsbheap _ c) = c)
`;

val b_is_empty_def = Define `
  (b_is_empty Bsbempty = T) /\
  (b_is_empty _ = F)
`;

(*
Create a comparison function for bootstraped binomial heaps
from a comparison function for their roots
*)
val b_heap_comparison = Define `
  (b_heap_comparison geq (Bsbheap r1 _) (Bsbheap r2 _) = geq r1 r2)
`;

val b_merge_def = Define `
  (b_merge _ Bsbempty h = h) /\
  (b_merge _ h Bsbempty = h) /\
  (b_merge geq (Bsbheap r1 c1) (Bsbheap r2 c2) =
    if geq r1 r2
    then (Bsbheap r2 (insert (b_heap_comparison geq) (Bsbheap r1 c1) c2))
    else (Bsbheap r1 (insert (b_heap_comparison geq) (Bsbheap r2 c2) c1)))
`;

val b_insert_def = Define `
  (b_insert geq e h = b_merge geq (Bsbheap e []) h)
`;

val b_find_min_def = Define `
  (b_find_min Bsbempty = NONE) /\
  (b_find_min (Bsbheap r _) = SOME r)
`;

val b_delete_min_def = Define `
  (b_delete_min _ Bsbempty = NONE) /\
  (b_delete_min geq (Bsbheap _ c) =
    if c = [] then (SOME Bsbempty) else
    let min = THE (find_min (b_heap_comparison geq) c) in
    let rest = THE (delete_min (b_heap_comparison geq) c) in
    let smallest_root = b_root min in
    let smallest_children = b_children min in
    SOME (Bsbheap smallest_root (merge (b_heap_comparison geq) rest smallest_children)))
`;

val b_heap_to_bag_def = Define `
  (b_heap_to_bag _ Bsbempty = {||}) /\
  (b_heap_to_bag geq (Bsbheap r c) = BAG_INSERT r (b_heap_to_bag1 geq c)) /\
  (b_heap_to_bag1 geq [] = {||}) /\
  (b_heap_to_bag1 geq (t::ts) = BAG_UNION (b_heap_to_bag2 geq t) (b_heap_to_bag1 geq ts)) /\
  (b_heap_to_bag2 geq (Sbnode x r a c) =
     BAG_UNION (b_heap_to_bag geq x) (BAG_UNION (b_heap_to_bag3 geq a) (b_heap_to_bag4 geq c))) /\
  (b_heap_to_bag3 geq [] = {||}) /\
  (b_heap_to_bag3 geq (e::es) = BAG_UNION (b_heap_to_bag geq e) (b_heap_to_bag3 geq es)) /\
  (b_heap_to_bag4 geq [] = {||}) /\
  (b_heap_to_bag4 geq (t::ts) = BAG_UNION (b_heap_to_bag2 geq t) (b_heap_to_bag4 geq ts))
`;

val is_b_heap_ordered_def = Define `
  (is_b_heap_ordered geq Bsbempty = T) /\
  (is_b_heap_ordered geq (Bsbheap r c) = ((BAG_EVERY (\y. geq y r) (b_heap_to_bag1 geq c)) /\
                                          (is_b_heap_ordered1 geq c))) /\
  (is_b_heap_ordered1 geq [] = T) /\
  (is_b_heap_ordered1 geq (t::ts) = (is_b_heap_ordered2 geq t /\ is_b_heap_ordered1 geq ts)) /\
  (is_b_heap_ordered2 geq (Sbnode x r a c) =
    (is_b_heap_ordered geq x /\ is_b_heap_ordered3 geq a /\ is_b_heap_ordered4 geq c)) /\
  (is_b_heap_ordered3 geq [] = T) /\
  (is_b_heap_ordered3 geq (e::es) = (is_b_heap_ordered geq e /\ is_b_heap_ordered3 geq es)) /\
  (is_b_heap_ordered4 geq [] = T) /\
  (is_b_heap_ordered4 geq (t::ts) = (is_b_heap_ordered2 geq t /\ is_b_heap_ordered4 geq ts))
`;

(* Useful lemmas *)
Theorem rank_irrelevance_bag:
  !root r1 r2 aux ch. tree_to_bag (Sbnode root r1 aux ch) = tree_to_bag (Sbnode root r2 aux ch)
Proof
  Induct_on `ch` \\ rw[tree_to_bag_def]
QED;

Theorem root_in_tree_bag:
  !t. BAG_IN (root t) (tree_to_bag t)
Proof
  Cases_on `t` \\
  Induct_on `l`
  >- rw[tree_to_bag_def, root_def]
  >- (rw[tree_to_bag_def, root_def] \\
      DISJ2_TAC \\
      fs[root_def])
QED;

Theorem root_smallest:
  !geq t y. WeakLinearOrder geq /\
            is_tree_ordered geq t /\
            BAG_IN y (tree_to_bag t)==>
            geq y (root t)
Proof
  rpt strip_tac \\
  fs[WeakLinearOrder, WeakOrder] \\
  Cases_on `t` \\
  Induct_on `l` \\
  rw[is_tree_ordered_def, tree_to_bag_def, root_def, BAG_EVERY] \\
  fs[root_def] \\
  metis_tac[reflexive_def]
QED;

Theorem children_order:
  !geq t. WeakLinearOrder geq /\
          is_tree_ordered geq t ==>
          is_heap_ordered geq (children t)
Proof
  rpt strip_tac \\
  Cases_on `t` \\
  Induct_on `l` \\
  fs[children_def,is_heap_ordered_def, is_tree_ordered_def]
QED;

Theorem app_heap_order:
  !geq h1 h2. WeakLinearOrder geq /\
              is_heap_ordered geq h1 /\
              is_heap_ordered geq h2 ==>
              is_heap_ordered geq (APPEND h1 h2)
Proof
  rpt strip_tac \\
  Induct_on `h1` \\
  rw[APPEND_NIL, is_heap_ordered_def]
QED;

Theorem reverse_heap_order:
  !geq h. WeakLinearOrder geq /\
          is_heap_ordered geq h ==>
          is_heap_ordered geq (REVERSE h)
Proof
  rpt strip_tac \\
  Induct_on `h` \\
  rw[REVERSE_DEF,is_heap_ordered_def, app_heap_order]
QED;

Theorem heap_to_bag_app:
  !l1 l2. heap_to_bag (l1++l2) = BAG_UNION (heap_to_bag l1)
					  (heap_to_bag l2)
Proof
  Induct_on `l1`
  >- rw[APPEND, heap_to_bag_def]
  >- metis_tac [APPEND, heap_to_bag_def, COMM_BAG_UNION, ASSOC_BAG_UNION]
QED;

Theorem tree_to_bag_general:
  !r n l0 l. tree_to_bag (Sbnode r n l0 l) = {|r|} ⊎ (list_to_bag l0) ⊎ (heap_to_bag l)
Proof
  Induct_on `l`
  >- rw[tree_to_bag_def, heap_to_bag_def, BAG_INSERT_UNION]
  >- (rw[tree_to_bag_def, heap_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION])
QED;

Theorem reverse_bag:
  !h. heap_to_bag (REVERSE h) = heap_to_bag h
Proof
  Induct_on `h`
  >- rw[REVERSE, heap_to_bag_def]
  >- rw[REVERSE_DEF, heap_to_bag_def, heap_to_bag_app, COMM_BAG_UNION]
QED;

Theorem merge_tree_left_cancel:
  !geq h. merge_tree geq [] h = h
Proof
  Cases_on `h` \\
  rw[merge_tree_def]
QED;

Theorem merge_left_cancel:
  !geq h. merge geq [] h = (normalize geq h)
Proof
  Cases_on `h` \\
  rw[merge_def, normalize_def, merge_tree_left_cancel]
QED;

Theorem merge_right_cancel:
  !geq h. merge geq h [] = (normalize geq h)
Proof
  Cases_on `h` \\
  rw[merge_def, normalize_def, merge_tree_def]
QED;

(* For both kinds of links, linking preserve the elements in the trees *)
Theorem tree_link_bag:
  !geq t1 t2. tree_to_bag (tree_link geq t1 t2) = BAG_UNION (tree_to_bag t1) (tree_to_bag t2)
Proof
  strip_tac \\
  rpt Cases \\
  rw[tree_link_def,tree_to_bag_def] \\
  Induct_on `l'` \\
  srw_tac [BAG_ss] [tree_to_bag_def] \\
  Induct_on `l` \\
  srw_tac [BAG_ss] [tree_to_bag_def]
QED;

Theorem skew_link_bag:
  !geq x y z. tree_to_bag (skew_link geq x y z) =
              BAG_INSERT x (BAG_UNION (tree_to_bag y) (tree_to_bag z))
Proof
  ntac 2 strip_tac \\
  ntac 2 Cases \\
  rw[tree_to_bag_def, skew_link_def, tree_link_def,
     root_def, aux_def, children_def, rank_def] \\
  fs[root_def]
  >- (Induct_on `l'` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION,
                (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION,
                (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l'` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION,
                (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION,
                (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
QED;

(* for both kinds of links, linking preserve the ordering of the elements *)
Theorem tree_link_order:
  !geq t1 t2.
    WeakLinearOrder geq /\
    is_tree_ordered geq t1 /\
    is_tree_ordered geq t2 ==>
    is_tree_ordered geq (tree_link geq t1 t2)
Proof
  strip_tac \\
  ntac 2 Cases \\
  rw[WeakLinearOrder, WeakOrder, tree_link_def,
     is_tree_ordered_def, BAG_EVERY, tree_to_bag_def]
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      fs[is_tree_ordered_def, BAG_EVERY] \\
      metis_tac[transitive_def])
  >- (Induct_on `l'` \\
      rw[is_tree_ordered_def])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      fs[is_tree_ordered_def, BAG_EVERY] \\
      Induct_on `l'` \\
      rw[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      metis_tac[transitive_def, reflexive_def,antisymmetric_def, trichotomous])
  >- (Induct_on `l` \\ rw[is_tree_ordered_def])
QED;

Theorem skew_link_order:
  !geq x t1 t2. WeakLinearOrder geq /\
                is_tree_ordered geq t1 /\
                is_tree_ordered geq t2 ==>
                is_tree_ordered geq (skew_link geq x t1 t2)
Proof
  ntac 2 strip_tac \\
  ntac 2 Cases \\
  rw[WeakLinearOrder, WeakOrder, skew_link_def, tree_link_def,
     is_tree_ordered_def, BAG_EVERY, tree_to_bag_def] \\
  fs[root_def, aux_def, children_def, rank_def] \\
  Induct_on `l` \\
  Induct_on `l'` \\
  rw[is_tree_ordered_def, BAG_EVERY, tree_to_bag_def, list_to_bag_def] \\
  fs[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
  metis_tac[transitive_def, reflexive_def, antisymmetric_def, trichotomous]
QED;

(*
Inserting an element effectively inserts the element to the collection
and preserves the ordering.
*)
Theorem binomial_insert_bag:
  !geq t h. heap_to_bag (binomial_insert geq t h) = BAG_UNION (tree_to_bag t) (heap_to_bag h)
Proof
  Induct_on `h`
  >- rw [heap_to_bag_def, binomial_insert_def, tree_link_def]
  >- (Cases_on `t` \\ Cases_on `h'` \\
      srw_tac [BAG_ss] [heap_to_bag_def, tree_link_def,
			binomial_insert_def, tree_to_bag_def, BAG_INSERT_UNION] \\
      rw[rank_irrelevance_bag])
QED;

Theorem binomial_insert_order:
  !geq t h. WeakLinearOrder geq /\
            is_heap_ordered geq h /\
            is_tree_ordered geq t ==>
            is_heap_ordered geq (binomial_insert geq t h)
Proof
  Induct_on `h`
  >- rw[is_heap_ordered_def, is_tree_ordered_def, binomial_insert_def]
  >- (Induct_on `h`
      >- (rw[is_heap_ordered_def, is_tree_ordered_def, binomial_insert_def] \\
          Cases_on `rank t < rank h` \\
          rw[is_heap_ordered_def, tree_link_order])
      >- (rw[is_heap_ordered_def, is_tree_ordered_def, binomial_insert_def] \\
          Cases_on `rank t < rank h''` \\
          rw[is_heap_ordered_def, tree_link_order]))
QED;

Theorem insert_bag:
  !geq e h. heap_to_bag (insert geq e h) = BAG_INSERT e (heap_to_bag h)
Proof
  rpt strip_tac \\
  Cases_on `h`
  >- rw[insert_def, heap_to_bag_def, leaf_def, tree_to_bag_def, list_to_bag_def]
  >- (Cases_on `t`
      >- rw[insert_def, heap_to_bag_def, leaf_def,
	    tree_to_bag_def, list_to_bag_def, BAG_INSERT_UNION]
      >- (rw[insert_def, heap_to_bag_def, leaf_def,
	     tree_to_bag_def, list_to_bag_def, skew_link_bag]
          >- metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION,
                (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL]
          >- rw[BAG_INSERT_UNION]))
QED;

Theorem insert_order:
  !geq e h. WeakLinearOrder geq /\
            is_heap_ordered geq h ==>
            is_heap_ordered geq (insert geq e h)
Proof
  Cases_on `h`
  >- rw[is_heap_ordered_def, insert_def,leaf_def,
        is_tree_ordered_def, BAG_EVERY, list_to_bag_def]
  >- (Cases_on `t` \\
      rw[is_heap_ordered_def, insert_def,leaf_def,
         is_tree_ordered_def, BAG_EVERY, list_to_bag_def,
	 skew_link_order])
QED;

Theorem insert_list_order:
  !geq es h. WeakLinearOrder geq /\
             is_heap_ordered geq h ==>
             is_heap_ordered geq (insert_list geq es h)
Proof
  rpt strip_tac \\
  Induct_on `es` \\
  rw[insert_list_def, insert_order]
QED;

Theorem insert_list_bag:
  !geq es h. heap_to_bag (insert_list geq es h) =
             BAG_UNION (list_to_bag es) (heap_to_bag h)
Proof
  Induct_on `es`
  >- rw[insert_list_def, list_to_bag_def]
  >- metis_tac [insert_list_def, list_to_bag_def, (GSYM insert_bag),
                ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_UNION_INSERT]
QED;


Theorem insert_list_empty_heap_bag:
  !geq l. heap_to_bag (insert_list geq l []) = list_to_bag l
Proof
  Induct_on `l` \\
  rw[insert_list_def, heap_to_bag_def, list_to_bag_def, insert_bag]
QED;

Theorem insert_list_app_bag:
  !geq l l1 l2. heap_to_bag (insert_list geq l (l1++l2)) =
                BAG_UNION (heap_to_bag l2) (heap_to_bag (insert_list geq l l1))
Proof
  rpt strip_tac \\
  rw[insert_list_bag, heap_to_bag_app] \\
  metis_tac [COMM_BAG_UNION, ASSOC_BAG_UNION]
QED;

(*
Merging two heaps creates a heap containing the elements of both heaps
which is ordered if the two merged heaps are ordered.
*)

Theorem normalize_bag:
  !geq h. heap_to_bag (normalize geq h) = heap_to_bag h
Proof
  Induct_on `h` \\ rw[normalize_def, heap_to_bag_def, binomial_insert_bag]
QED;

Theorem normalize_order:
  !geq h. WeakLinearOrder geq /\
          is_heap_ordered geq h ==>
          is_heap_ordered geq (normalize geq h)
Proof
  Cases_on `h` \\
  rw[is_heap_ordered_def, normalize_def, binomial_insert_order]
QED;

Theorem merge_tree_bag:
  !geq t1 t2. heap_to_bag (merge_tree geq t1 t2) =
              BAG_UNION (heap_to_bag t1) (heap_to_bag t2)
Proof
  Induct_on `t2` \\
  rw[merge_tree_def, heap_to_bag_def] \\
  Induct_on `t1` \\
  srw_tac [BAG_ss] [merge_tree_def, heap_to_bag_def,
	            binomial_insert_bag, tree_link_bag]
QED;

Theorem merge_tree_order:
  !geq t1 t2. WeakLinearOrder geq /\
              is_heap_ordered geq t1 /\
              is_heap_ordered geq t2 ==>
              is_heap_ordered geq (merge_tree geq t1 t2)
Proof
  Induct_on `t2`
  >- rw[is_heap_ordered_def, merge_tree_def]
  >- (Induct_on `t1`
      >- rw[is_heap_ordered_def, merge_tree_def]
      >- (rw[merge_tree_def]
	  >- fs[is_heap_ordered_def]
	  >- fs[is_heap_ordered_def]
	  >- (fs[is_heap_ordered_def] \\
              `is_tree_ordered geq (tree_link geq h h')`
               by rw[tree_link_order] \\
              `is_heap_ordered geq (merge_tree geq t1 t2)`
               by rw[] \\
              rw[binomial_insert_order])))
QED;

Theorem merge_bag:
  !geq h1 h2. heap_to_bag (merge geq h1 h2) = BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
  rpt strip_tac \\
  Induct_on `h2` \\
  rw[heap_to_bag_def, merge_def, merge_tree_bag,
     normalize_def, normalize_bag, binomial_insert_bag]
QED;

Theorem merge_order:
  !geq h1 h2. WeakLinearOrder geq /\
              is_heap_ordered geq h1 /\
              is_heap_ordered geq h2 ==>
              is_heap_ordered geq (merge geq h1 h2)
Proof
  Cases_on `h2`
  >- rw[is_heap_ordered_def, merge_def, normalize_def,
	merge_tree_def, normalize_order]
  >- (rw[is_heap_ordered_def, merge_def, normalize_def,
	merge_tree_def, normalize_def] \\
      `is_heap_ordered geq (normalize geq h1)`
       by rw[normalize_order] \\
      `is_heap_ordered geq (binomial_insert geq h t)`
       by rw[binomial_insert_order] \\
       rw[merge_tree_order])
QED;

(*
find_min returns the smallest element with the highest
priority of the heap.
*)
Theorem find_min_exists:
  !geq h. h <> [] ==>
          (find_min geq h) <> NONE
Proof
  Induct_on `h`
  >- rw[]
  >- (Cases_on `h` \\
     rw[find_min_def] \\
     Cases_on `find_min geq (h'::t)`
     >- res_tac
     >- rw[])
QED;

Theorem find_min_bag:
  !geq h. WeakLinearOrder geq /\
          h <> [] /\
	  is_heap_ordered geq h ==>
          BAG_IN (THE (find_min geq h)) (heap_to_bag h)
Proof
  Induct_on `h`
  >- rw[]
  >- (rw[is_heap_ordered_def, heap_to_bag_def, find_min_def] \\
      Cases_on `h`
      >- (DISJ1_TAC \\
          rw[THE_DEF, tree_to_bag_def, find_min_def, root_in_tree_bag])
      >- (rw[find_min_def] \\
          Cases_on `find_min geq (h''::t)`
          >- `find_min geq (h''::t) <> NONE`
             by rw[find_min_exists]
	  >- (rw[]
              >- (DISJ1_TAC \\
                  rw[root_in_tree_bag])
              >- (DISJ2_TAC \\
                  fs[is_heap_ordered_def] \\
                  res_tac \\
                  metis_tac[THE_DEF]))))
QED;

Theorem find_min_correct:
  !geq h. WeakLinearOrder geq /\
          h <> [] /\
	  is_heap_ordered geq h ==>
          !y. (BAG_IN y (heap_to_bag h)) ==> (geq y (THE (find_min geq h)))
Proof
  Induct_on `h`
  >- rw[]
  >- (rpt strip_tac \\
      rw[heap_to_bag_def] \\
      Cases_on `h`
      >- (Cases_on `h'` \\
          Induct_on `l`
          >- (rw[is_heap_ordered_def, heap_to_bag_def, find_min_def,
		THE_DEF, root_def, tree_to_bag_def, is_tree_ordered_def] \\
              fs[WeakLinearOrder, WeakOrder, reflexive_def, BAG_EVERY])
	  >- (rw[is_heap_ordered_def, heap_to_bag_def, find_min_def,
		THE_DEF, root_def, tree_to_bag_def, is_tree_ordered_def,
	        BAG_EVERY] \\
              fs[is_heap_ordered_def, heap_to_bag_def, find_min_def, root_def]))
      >- (rw[find_min_def] \\
          Cases_on `find_min geq (h''::t)`
          >- `find_min geq (h''::t) <> NONE`
             by rw[find_min_exists]
	  >- (rw[]
	      >- (fs[heap_to_bag_def, is_heap_ordered_def]
	          >- metis_tac[root_smallest]
		  >- (res_tac \\ `geq y (THE (SOME x))` by metis_tac[] \\
                      fs[THE_DEF, WeakOrder, WeakLinearOrder] \\
                      metis_tac[transitive_def])
		  >- (res_tac \\ `geq y (THE (SOME x))` by metis_tac[] \\
                      fs[THE_DEF, WeakOrder, WeakLinearOrder] \\
                      metis_tac[transitive_def]))
	      >- (fs[heap_to_bag_def, is_heap_ordered_def]
		  >- (`geq y (root h')` by rw[root_smallest] \\
                      fs[WeakOrder, WeakLinearOrder] \\
                      metis_tac[transitive_def, trichotomous])
		  >- (res_tac \\ `geq y (THE (SOME x))` by metis_tac[] \\
                      fs[THE_DEF, WeakOrder, WeakLinearOrder] \\
                      metis_tac[transitive_def])
		  >- (res_tac \\ `geq y (THE (SOME x))` by metis_tac[] \\
                      fs[THE_DEF, WeakOrder, WeakLinearOrder] \\
                      metis_tac[transitive_def])))))
QED;

(*
delete_min deletes the smallest element with
the highest priority of the heap
*)
Theorem get_min_bag:
  !geq smallest rest h. h <> [] /\
          (smallest,rest) = get_min geq h ==>
          (heap_to_bag h) = BAG_UNION
                             (tree_to_bag smallest)
                             (heap_to_bag rest)
Proof
  Induct_on `h`
  >- rw[]
  >- (Cases_on `h`
      >- rw[get_min_def, heap_to_bag_def, tree_to_bag_def]
      >- (rw[get_min_def, heap_to_bag_def, tree_to_bag_def] \\
          Cases_on `get_min geq (h'::t)` \\
          fs[] \\
	  Cases_on `geq (root q) (root h)`
          >- fs[heap_to_bag_def]
          >- (fs[heap_to_bag_def] \\
              `(q,r) = get_min geq (h'::t)` by
              rw[] \\
              res_tac \\
              metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION])))
QED;

Theorem get_min_order:
  !geq h smallest rest. WeakLinearOrder geq /\
                         h <> [] /\
                         is_heap_ordered geq h /\
                         (smallest, rest) = get_min geq h ==>
                         is_tree_ordered geq smallest /\
                         is_heap_ordered geq rest
Proof
  Induct_on `h`
  >- rw[]
  >- (Cases_on `h`
      >- rw[is_heap_ordered_def, get_min_def]
      >- (rw[is_heap_ordered_def, get_min_def] \\
          Cases_on `get_min geq (h'::t)` \\
          fs[] \\
          `(q,r) = get_min geq (h'::t)` by rw[]
          >- (Cases_on `geq (root q) (root h)`
              >- fs[]
              >- (fs[] \\
                  res_tac))
          >- (Cases_on `geq (root q) (root h)`
              >- fs[is_heap_ordered_def]
              >- (res_tac \\
                  fs[is_heap_ordered_def]))))
QED;

Theorem get_min_correct:
  !geq h smallest rest. WeakLinearOrder geq /\
                        h <> [] /\
                        is_heap_ordered geq h /\
                        (smallest,rest) = get_min geq h ==>
			(root smallest) = THE (find_min geq h)
Proof
  Induct_on `h`
  >- rw[]
  >- (Cases_on `h`
      >- (rw[find_min_def] \\
          fs[get_min_def])
      >- (rw[find_min_def] \\
          `find_min geq (h'::t) <> NONE` by rw[find_min_exists] \\
      	  Cases_on `find_min geq (h'::t)`
	  >- rw[]
	  >- (rw[] \\
              fs[get_min_def] \\
              Cases_on `get_min geq (h'::t)` \\
              fs[] \\
              `(q,r) = get_min geq (h'::t)` by rw[] \\
              fs[is_heap_ordered_def] \\
	      `is_heap_ordered geq (h'::t)` by rw[is_heap_ordered_def] \\
              res_tac \\
              fs[])))
QED;

Theorem delete_min_order:
  !geq h. WeakLinearOrder geq /\
           h <> [] /\
           is_heap_ordered geq h ==>
           is_heap_ordered geq (THE (delete_min geq h))
Proof
  Induct_on `h`
  >- rw[]
  >- (rw[delete_min_def] \\
      Cases_on `get_min geq (h'::h)` \\
      `(q,r) = get_min geq (h'::h)` by rw[] \\
      `(h'::h) <> []` by rw[] \\
      imp_res_tac get_min_order \\
      simp[] \\
      metis_tac [normalize_order, children_order, reverse_heap_order,
		 merge_tree_order, insert_list_order])
QED;

Theorem delete_min_correct:
  !geq h. WeakLinearOrder geq /\
           h <> [] /\
           is_heap_ordered geq h ==>
	   heap_to_bag h = BAG_UNION
                            (heap_to_bag (THE (delete_min geq h)))
                            {| THE (find_min geq h) |}
Proof
  Induct_on `h`
  >- rw[]
  >- (rw[delete_min_def] \\
      Cases_on `get_min geq (h'::h)` \\
      rw[] \\
      `(q,r) = get_min geq (h'::h)` by rw[] \\
      `(h'::h) <> []` by rw[] \\
      imp_res_tac get_min_correct \\
      imp_res_tac get_min_bag \\
      rw[insert_list_bag, merge_tree_bag, reverse_heap_order,
	 normalize_bag] \\
      Cases_on `q` \\
      fs[root_def, children_def, aux_def] \\
      rw[tree_to_bag_general] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION, reverse_bag])
QED;

(* Functional correctness of merge *)
Theorem b_bag_of_link:
  !geq t t1 t2. tree_link (b_heap_comparison geq) t1 t2 = t ==>
                b_heap_to_bag2 geq t = BAG_UNION (b_heap_to_bag2 geq t1) (b_heap_to_bag2 geq t2)
Proof
  rw[] \\
  Cases_on `t1` \\
  Cases_on `t2` \\
  rw[tree_link_def] \\
  srw_tac [BAG_ss] [b_heap_to_bag_def]
QED;

Theorem b_bag_of_skew:
  !geq x t1 t2. b_heap_to_bag2 geq (skew_link (b_heap_comparison geq) x t1 t2) =
                BAG_UNION (b_heap_to_bag geq x)
                          (BAG_UNION (b_heap_to_bag2 geq t1)
                                     (b_heap_to_bag2 geq t2))
Proof
  Cases_on `t1` \\
  Cases_on `t2` \\
  rw[skew_link_def] \\
  Cases_on `tree_link (b_heap_comparison geq) (Sbnode a n l0 l) (Sbnode a' n' l0' l')` \\
  rw[root_def, rank_def, aux_def, children_def, b_heap_to_bag_def] \\
  imp_res_tac b_bag_of_link \\
  fs[b_heap_to_bag_def] \\
  metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION]
QED;

Theorem b_bag_of_insert:
  !geq h l. b_heap_to_bag1 geq (insert (b_heap_comparison geq) h l) =
            BAG_UNION (b_heap_to_bag geq h)
                      (b_heap_to_bag1 geq l)
Proof
  Cases_on `l`
  >- rw[insert_def, b_heap_to_bag_def, leaf_def]
  >- (Cases_on `t`
      >- rw[insert_def, b_heap_to_bag_def, leaf_def]
      >- (rw[insert_def]
          >- (rw[b_heap_to_bag_def, b_bag_of_skew] \\ metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION])
          >- (rw[b_heap_to_bag_def, leaf_def])))
QED;

Theorem b_merge_bag:
  !geq h1 h2. b_heap_to_bag geq (b_merge geq h1 h2) =
              BAG_UNION (b_heap_to_bag geq h1) (b_heap_to_bag geq h2)
Proof
  Cases_on `h1` \\
  Cases_on `h2`
  >- rw[b_heap_to_bag_def, b_merge_def]
  >- rw[b_heap_to_bag_def, b_merge_def]
  >- rw[b_heap_to_bag_def, b_merge_def]
  >- (rw[b_heap_to_bag_def, b_merge_def]
      >- (rw[b_bag_of_insert, BAG_INSERT_UNION, b_heap_to_bag_def] \\
          metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION])
      >- (rw[b_bag_of_insert, BAG_INSERT_UNION, b_heap_to_bag_def] \\
          metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION]))
QED;

Theorem link_b_order:
  !geq t t1 t2. tree_link (b_heap_comparison geq) t1 t2 = t ==>
                (is_b_heap_ordered2 geq t1 /\ is_b_heap_ordered2 geq t2 ==> is_b_heap_ordered2 geq t)
Proof
  rw[] \\
  Cases_on `t1` \\
  Cases_on `t2` \\
  rw[tree_link_def]
  >- fs[is_b_heap_ordered_def]
  >- fs[is_b_heap_ordered_def]
QED;

Theorem skew_b_order:
  !geq b t1 t2. WeakLinearOrder geq /\
                is_b_heap_ordered2 geq t1 /\
                is_b_heap_ordered2 geq t2 /\
                is_b_heap_ordered geq b ==>
                is_b_heap_ordered2 geq (skew_link (b_heap_comparison geq) b t1 t2)
Proof
  Cases_on `t1` \\
  Cases_on `t2` \\
  rw[skew_link_def] \\
  Cases_on `tree_link (b_heap_comparison geq) (Sbnode a n l0 l) (Sbnode a' n' l0' l')` \\
  rw[root_def, rank_def, aux_def, children_def, is_b_heap_ordered_def] \\
  imp_res_tac link_b_order \\
  fs[is_b_heap_ordered_def]
QED;

Theorem insert_b_order:
  !geq b h. WeakLinearOrder geq /\
            is_b_heap_ordered1 geq h /\
            is_b_heap_ordered geq b ==>
            is_b_heap_ordered1 geq (insert (b_heap_comparison geq) b h)
Proof
  rpt strip_tac \\
  Cases_on `h`
  >- rw[insert_def, leaf_def, is_b_heap_ordered_def]
  >- (Cases_on `t`
      >- rw[insert_def, leaf_def, is_b_heap_ordered_def]
      >- (fs[insert_def, is_b_heap_ordered_def] \\
          rw[]
          >- rw[is_b_heap_ordered_def, skew_b_order]
          >- rw[leaf_def, is_b_heap_ordered_def]))
QED;

Theorem b_merge_order:
!geq h1 h2. WeakLinearOrder geq /\
              is_b_heap_ordered geq h1 /\
              is_b_heap_ordered geq h2 ==>
              is_b_heap_ordered geq (b_merge geq h1 h2)
Proof
  Cases_on `h1` \\
  Cases_on `h2`
  >- rw[is_b_heap_ordered_def, b_merge_def]
  >- rw[is_b_heap_ordered_def, b_merge_def]
  >- rw[is_b_heap_ordered_def, b_merge_def]
  >- (rw[b_merge_def]
    >- (rw[is_b_heap_ordered_def, b_bag_of_insert]
      >- (fs[b_heap_to_bag_def, is_b_heap_ordered_def, BAG_EVERY] \\
          rw[] \\
          res_tac \\
          fs[WeakLinearOrder, WeakOrder] \\
          metis_tac[transitive_def, reflexive_def, trichotomous])
      >- (fs[is_b_heap_ordered_def, BAG_EVERY])
      >- (`is_b_heap_ordered1 geq l'` by fs[is_b_heap_ordered_def] \\
          imp_res_tac insert_b_order))
    >- (rw[is_b_heap_ordered_def, b_bag_of_insert]
      >- (fs[b_heap_to_bag_def, is_b_heap_ordered_def, BAG_EVERY] \\
          rw[] \\
          res_tac \\
          fs[WeakLinearOrder, WeakOrder] \\
          metis_tac[transitive_def, reflexive_def, trichotomous])
      >- (fs[is_b_heap_ordered_def, BAG_EVERY])
      >- (`is_b_heap_ordered1 geq l` by fs[is_b_heap_ordered_def] \\
          imp_res_tac insert_b_order)))
QED;

(* functional correctness of insertion *)
Theorem b_insert_bag:
  !geq e h. b_heap_to_bag geq (b_insert geq e h) = BAG_INSERT e (b_heap_to_bag geq h)
Proof
  rw[b_insert_def, b_merge_bag, BAG_INSERT_UNION, b_heap_to_bag_def]
QED;

Theorem b_insert_order:
  !geq e h. WeakLinearOrder geq /\
            is_b_heap_ordered geq h ==>
            is_b_heap_ordered geq (b_insert geq e h)
Proof
  rw[b_insert_def] \\
  `is_b_heap_ordered geq (Bsbheap e [])`
  by rw[is_b_heap_ordered_def, BAG_EVERY, b_heap_to_bag_def] \\
  imp_res_tac b_merge_order
QED;

(* Translations *)
val _ = translate leaf_def;
val _ = translate root_def;
val _ = translate rank_def;
val _ = translate aux_def;
val _ = translate children_def;
val _ = translate tree_link_def;
val _ = translate skew_link_def;
val _ = translate is_empty_def;
val _ = translate insert_def;
val _ = translate insert_list_def;
val _ = translate find_min_def;
val _ = translate binomial_insert_def;
val _ = translate normalize_def;
val _ = translate merge_tree_def;
val _ = translate merge_def;
val _ = translate get_min_def;
val _ = translate delete_min_def;
val _ = translate b_root_def;
val _ = translate b_children_def;
val _ = translate b_is_empty_def;
val _ = translate b_heap_comparison_def;
val _ = translate b_merge_def;
val _ = translate b_insert_def;
val _ = translate b_find_min_def;
val _ = translate b_delete_min_def;

val _ = export_theory ();
