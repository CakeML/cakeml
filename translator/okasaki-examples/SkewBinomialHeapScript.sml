(*
  Bootstraped Skew Binomial Heaps, based on Purely Functional Data Structures
  sections 9.3.2 and 10.2.2
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

(* Useful lemmas *)
Theorem rank_irrelevance_bag:
  !root r1 r2 aux ch. tree_to_bag (Sbnode root r1 aux ch) = tree_to_bag (Sbnode root r2 aux ch)
Proof
  Induct_on `ch` \\ rw[tree_to_bag_def]
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
    ((WeakLinearOrder geq) /\
     (is_tree_ordered geq t1) /\
     (is_tree_ordered geq t2)) ==> (is_tree_ordered geq (tree_link geq t1 t2))
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
  !geq x t1 t2.
    ((WeakLinearOrder geq) /\
     (is_tree_ordered geq t1) /\
     (is_tree_ordered geq t2)) ==> (is_tree_ordered geq (skew_link geq x t1 t2))
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

Theorem insert_bag:
  !geq e h. BAG_INSERT e (heap_to_bag h) = heap_to_bag (insert geq e h)
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
  `!geq e h. ((WeakLinearOrder geq) /\
             (is_heap_ordered geq h)) ==> (is_heap_ordered geq (insert geq e h))`
Proof
  Cases_on `h`
  >- rw[is_heap_ordered_def, insert_def,leaf_def,
        is_tree_ordered_def, BAG_EVERY, list_to_bag_def]
  >- (Cases_on `t` \\
      rw[is_heap_ordered_def, insert_def,leaf_def,
         is_tree_ordered_def, BAG_EVERY, list_to_bag_def,
	 skew_link_order])
QED;

(* Merging two heaps creates a heap containing the elements of both heaps *)

Theorem normalize_bag:
  !geq h. (heap_to_bag h) = heap_to_bag (normalize geq h)
Proof
  Induct_on `h` \\ rw[normalize_def, heap_to_bag_def, binomial_insert_bag]
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

Theorem merge_bag:
  !geq h1 h2. BAG_UNION (heap_to_bag h1) (heap_to_bag h2) =
               heap_to_bag (merge geq h1 h2)
Proof
  rpt strip_tac \\
  Induct_on `h2` \\
  rw[heap_to_bag_def, merge_def, merge_tree_bag,
     normalize_def, normalize_bag, binomial_insert_bag]
QED;

(* findMin returns the smallest element of the heap *)
Theorem find_min_correct:

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

val _ = export_theory ();
