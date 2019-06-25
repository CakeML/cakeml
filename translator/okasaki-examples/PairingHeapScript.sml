(*
  This is an example of applying the translator to the Pairing
  Heap algorithm from Chris Okasaki's book.
*)
open preamble
open bagTheory bagLib okasaki_miscTheory ml_translatorLib ListProgTheory

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "PairingHeap"

val _ = translation_extends "ListProg";

(* Okasaki page 54 *)

val _ = Datatype`
  heap = Empty | Tree 'a (heap list)`;

val heap_to_bag_def = Define `
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree x hs) =
  BAG_INSERT x (heaps_to_bag hs)) ∧

(heaps_to_bag [] = {||}) ∧
(heaps_to_bag (h::hs) =
  BAG_UNION (heap_to_bag h) (heaps_to_bag hs))`;

val is_heap_ordered_def = tDefine "is_heap_ordered" `
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree x hs) <=>
  EVERY (is_heap_ordered get_key leq) hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heaps_to_bag hs))`
(wf_rel_tac `measure (\(_,_,h). (heap_size (\x.1) h))` >>
rw [] >>
induct_on `hs` >>
rw [fetch "-" "heap_size_def"] >>
fs [] >>
decide_tac);

val empty_def = mlDefine `
empty = Empty`;

val is_empty_def = mlDefine `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val merge_def = mlDefine `
(merge get_key leq h Empty = h) ∧
(merge get_key leq Empty h = h) ∧
(merge get_key leq (Tree x hs1) (Tree y hs2) =
  if leq (get_key x) (get_key y) then
    Tree x (Tree y hs2 :: hs1)
  else
    Tree y (Tree x hs1 :: hs2))`;

val merge_ind = fetch "-" "merge_ind"

val insert_def = mlDefine `
insert get_key leq x h = merge get_key leq (Tree x []) h`;

val merge_pairs_def = mlDefine `
(merge_pairs get_key leq [] = Empty) ∧
(merge_pairs get_key leq [h] = h) ∧
(merge_pairs get_key leq (h1::h2::hs) =
  merge get_key leq (merge get_key leq h1 h2) (merge_pairs get_key leq hs))`;

val merge_pairs_ind = fetch "-" "merge_pairs_ind"

val find_min_def = mlDefine `
find_min (Tree x _) = x`;

val delete_min_def = mlDefine `
delete_min get_key leq (Tree x hs) = merge_pairs get_key leq hs`;


(* Functional correctness proof *)

Theorem merge_bag:
 !get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_AC_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION]
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
rw [merge_def, is_heap_ordered_def, heap_to_bag_def] >>
fs [BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]
QED

Theorem insert_bag:
 !h get_key leq x.
  heap_to_bag (insert get_key leq x h) = BAG_INSERT x (heap_to_bag h)
Proof
rw [insert_def, merge_bag, heap_to_bag_def, BAG_INSERT_UNION]
QED

Theorem insert_heap_ordered:
 !get_key leq x h.
  WeakLinearOrder leq ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)
Proof
rw [insert_def] >>
`is_heap_ordered get_key leq (Tree x [])`
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

val merge_pairs_bag = Q.prove (
`!get_key leq hs. heap_to_bag (merge_pairs get_key leq hs) = heaps_to_bag hs`,
recInduct merge_pairs_ind >>
srw_tac [BAG_ss] [merge_pairs_def, heap_to_bag_def, merge_bag]);

val merge_pairs_heap_ordered = Q.prove (
`!get_key leq hs.
  WeakLinearOrder leq ∧ EVERY (is_heap_ordered get_key leq) hs
  ⇒
  is_heap_ordered get_key leq (merge_pairs get_key leq hs)`,
recInduct merge_pairs_ind >>
rw [merge_pairs_def, is_heap_ordered_def, merge_heap_ordered]);

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
fs [delete_min_def, is_heap_ordered_def, merge_pairs_bag] >-
metis_tac [merge_pairs_heap_ordered] >>
rw [heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]
QED

(* Simplify the side conditions on the generated certificate theorems *)

val delete_min_side_def = fetch "-" "delete_min_side_def"
val find_min_side_def = fetch "-" "find_min_side_def"

val delete_min_side = Q.prove (
`!get_key leq h. delete_min_side get_key leq h = (h ≠ Empty)`,
cases_on `h` >>
rw [delete_min_side_def]);

val find_min_side = Q.prove (
`!h. find_min_side h = (h ≠ Empty)`,
cases_on `h` >>
rw [find_min_side_def]);

val _ = export_theory ()
