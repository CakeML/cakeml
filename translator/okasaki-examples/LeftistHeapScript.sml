(*
  This is an example of applying the translator to the Leftist
  Heap algorithm from Chris Okasaki's book.
*)
open preamble
open bagTheory bagLib okasaki_miscTheory;
open ml_translatorLib ListProgTheory;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "LeftistHeap"

val _ = translation_extends "ListProg";

(* Okasaki page 20 *)

val _ = Datatype`
  heap = Empty | Tree num 'a heap heap`;

val heap_to_bag_def = Define `
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree _ x h1 h2) =
  BAG_INSERT x (BAG_UNION (heap_to_bag h1) (heap_to_bag h2)))`;

val rank_def = mlDefine `
(rank Empty = 0) ∧
(rank (Tree r _ _ _) = r)`;

val is_heap_ordered_def = Define `
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree _ x h1 h2) <=>
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h2) ∧
  rank h1 ≥ rank h2)`;

val make_node_def = mlDefine `
make_node x a b =
  if rank a >= rank b then
    Tree (rank b + 1) x a b
  else
    Tree (rank a + 1) x b a`;

val _ = mlDefine `
empty = Empty`;

val is_empty_def = mlDefine `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = mlDefine `
(merge get_key leq h Empty = h) ∧
(merge get_key leq Empty h = h) ∧
(merge get_key leq (Tree n1 x a1 b1) (Tree n2 y a2 b2) =
  if leq (get_key x) (get_key y) then
    make_node x a1 (merge get_key leq b1 (Tree n2 y a2 b2))
  else
    make_node y a2 (merge get_key leq (Tree n1 x a1 b1) b2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = mlDefine `
insert get_key leq x h = merge get_key leq (Tree 1 x Empty Empty) h`;

val find_min_def = mlDefine `
find_min (Tree _ x _ _) = x`;

val delete_min_def = mlDefine `
delete_min get_key leq (Tree _ x a b) = merge get_key leq a b`;


(* Functional correctness proof *)

Theorem merge_bag:
 !get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_ss]
        [merge_def, heap_to_bag_def, make_node_def, BAG_INSERT_UNION]
QED

Theorem merge_heap_ordered:
 !get_key leq h1 h2.
  WeakLinearOrder leq ∧
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2
  ⇒
  is_heap_ordered get_key leq (merge get_key leq h1 h2)
Proof
HO_MATCH_MP_TAC merge_ind >>
rw [merge_def, is_heap_ordered_def, make_node_def, merge_bag] >>
rw [heap_to_bag_def] >>
fs [BAG_EVERY] >|
[metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 decide_tac,
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 decide_tac]
QED

Theorem insert_bag:
 !h get_key leq x.
  heap_to_bag (insert get_key leq x h) = BAG_INSERT x (heap_to_bag h)
Proof
rw [insert_def, merge_bag, heap_to_bag_def,
    BAG_INSERT_UNION]
QED

Theorem insert_heap_ordered:
 !get_key leq x h.
  WeakLinearOrder leq ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)
Proof
rw [insert_def] >>
`is_heap_ordered get_key leq (Tree 1 x Empty Empty)`
         by rw [is_heap_ordered_def, heap_to_bag_def] >>
metis_tac [merge_heap_ordered]
QED

Theorem find_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ is_heap_ordered get_key leq h
  ⇒
  BAG_IN (find_min h) (heap_to_bag h) ∧
  (!y. BAG_IN y (heap_to_bag h) ⇒ leq (get_key (find_min h)) (get_key y))
Proof
rw [] >>
cases_on `h` >>
fs [find_min_def, heap_to_bag_def, is_heap_ordered_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]
QED

Theorem delete_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (delete_min get_key leq h) ∧
  (heap_to_bag (delete_min get_key leq h) =
   BAG_DIFF (heap_to_bag h) (EL_BAG (find_min h)))
Proof
rw [] >>
cases_on `h` >>
fs [delete_min_def, is_heap_ordered_def, merge_bag] >-
metis_tac [merge_heap_ordered] >>
rw [heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]
QED


(* Simplify the side conditions on the generated certificate theorems *)

val delete_min_side_def = fetch "-" "delete_min_side_def"
val find_min_side_def = fetch "-" "find_min_side_def"

val delete_min_side = Q.prove (
`!get_key leq h. delete_min_side get_key leq h = (h ≠ Empty)`,
rw [delete_min_side_def] >>
eq_tac >>
rw [] >>
cases_on `h` >>
rw []);

val find_min_side = Q.prove (
`!h. find_min_side h = (h ≠ Empty)`,
rw [find_min_side_def] >>
eq_tac >>
rw [] >>
cases_on `h` >>
rw []);

val _ = export_theory ();
