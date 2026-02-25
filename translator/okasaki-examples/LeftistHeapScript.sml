(*
  This is an example of applying the translator to the Leftist
  Heap algorithm from Chris Okasaki's book.
*)
Theory LeftistHeap
Ancestors
  bag okasaki_misc ListProg
Libs
  preamble bagLib ml_translatorLib

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = translation_extends "ListProg";

(* Okasaki page 20 *)

Datatype:
  heap = Empty | Tree num 'a heap heap
End

Definition heap_to_bag_def:
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree _ x h1 h2) =
  BAG_INSERT x (BAG_UNION (heap_to_bag h1) (heap_to_bag h2)))
End

Definition rank_def:
(rank Empty = 0) ∧
(rank (Tree r _ _ _) = r)
End
val r = translate rank_def;

Definition is_heap_ordered_def:
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree _ x h1 h2) <=>
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h2) ∧
  rank h1 ≥ rank h2)
End

Definition make_node_def:
make_node x a b =
  if rank a >= rank b then
    Tree (rank b + 1) x a b
  else
    Tree (rank a + 1) x b a
End
val r = translate make_node_def;

Definition empty_def:
  empty = Empty
End
val r = translate empty_def;

Definition is_empty_def:
(is_empty Empty = T) ∧
(is_empty _ = F)
End
val r = translate is_empty_def;

Definition merge_def:
(merge get_key leq h Empty = h) ∧
(merge get_key leq Empty h = h) ∧
(merge get_key leq (Tree n1 x a1 b1) (Tree n2 y a2 b2) =
  if leq (get_key x) (get_key y) then
    make_node x a1 (merge get_key leq b1 (Tree n2 y a2 b2))
  else
    make_node y a2 (merge get_key leq (Tree n1 x a1 b1) b2))
End
val r = translate merge_def;

val merge_ind = fetch "-" "merge_ind"

Definition insert_def:
insert get_key leq x h = merge get_key leq (Tree 1 x Empty Empty) h
End
val r = translate insert_def;

Definition find_min_def:
find_min (Tree _ x _ _) = x
End
val r = translate find_min_def;

Definition delete_min_def:
delete_min get_key leq (Tree _ x a b) = merge get_key leq a b
End
val r = translate delete_min_def;


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

Theorem delete_min_side[local]:
  !get_key leq h. delete_min_side get_key leq h = (h ≠ Empty)
Proof
  rw [delete_min_side_def] >>
eq_tac >>
rw [] >>
cases_on `h` >>
rw []
QED

Theorem find_min_side[local]:
  !h. find_min_side h = (h ≠ Empty)
Proof
  rw [find_min_side_def] >>
eq_tac >>
rw [] >>
cases_on `h` >>
rw []
QED

