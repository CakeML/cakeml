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

Datatype:
  heap = Empty | Tree 'a (heap list)
End

Definition heap_to_bag_def:
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree x hs) =
  BAG_INSERT x (heaps_to_bag hs)) ∧

(heaps_to_bag [] = {||}) ∧
(heaps_to_bag (h::hs) =
  BAG_UNION (heap_to_bag h) (heaps_to_bag hs))
End

Definition is_heap_ordered_def:
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree x hs) <=>
  EVERY (is_heap_ordered get_key leq) hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heaps_to_bag hs))
Termination
  wf_rel_tac `measure (\(_,_,h). (heap_size (\x.1) h))` >>
rw [] >>
induct_on `hs` >>
rw [fetch "-" "heap_size_def"] >>
fs [] >>
decide_tac
End

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
(merge get_key leq (Tree x hs1) (Tree y hs2) =
  if leq (get_key x) (get_key y) then
    Tree x (Tree y hs2 :: hs1)
  else
    Tree y (Tree x hs1 :: hs2))
End
val r = translate merge_def;

val merge_ind = fetch "-" "merge_ind"

Definition insert_def:
insert get_key leq x h = merge get_key leq (Tree x []) h
End
val r = translate insert_def;

Definition merge_pairs_def:
(merge_pairs get_key leq [] = Empty) ∧
(merge_pairs get_key leq [h] = h) ∧
(merge_pairs get_key leq (h1::h2::hs) =
  merge get_key leq (merge get_key leq h1 h2) (merge_pairs get_key leq hs))
End
val r = translate merge_pairs_def;

val merge_pairs_ind = fetch "-" "merge_pairs_ind"

Definition find_min_def:
find_min (Tree x _) = x
End
val r = translate find_min_def;

Definition delete_min_def:
delete_min get_key leq (Tree x hs) = merge_pairs get_key leq hs
End
val r = translate delete_min_def;


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

Triviality merge_pairs_bag:
  !get_key leq hs. heap_to_bag (merge_pairs get_key leq hs) = heaps_to_bag hs
Proof
  recInduct merge_pairs_ind >>
srw_tac [BAG_ss] [merge_pairs_def, heap_to_bag_def, merge_bag]
QED

Triviality merge_pairs_heap_ordered:
  !get_key leq hs.
  WeakLinearOrder leq ∧ EVERY (is_heap_ordered get_key leq) hs
  ⇒
  is_heap_ordered get_key leq (merge_pairs get_key leq hs)
Proof
  recInduct merge_pairs_ind >>
rw [merge_pairs_def, is_heap_ordered_def, merge_heap_ordered]
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
fs [delete_min_def, is_heap_ordered_def, merge_pairs_bag] >-
metis_tac [merge_pairs_heap_ordered] >>
rw [heap_to_bag_def, find_min_def, BAG_DIFF_INSERT2]
QED

(* Simplify the side conditions on the generated certificate theorems *)

val delete_min_side_def = fetch "-" "delete_min_side_def"
val find_min_side_def = fetch "-" "find_min_side_def"

Triviality delete_min_side:
  !get_key leq h. delete_min_side get_key leq h = (h ≠ Empty)
Proof
  cases_on `h` >>
rw [delete_min_side_def]
QED

Triviality find_min_side:
  !h. find_min_side h = (h ≠ Empty)
Proof
  cases_on `h` >>
rw [find_min_side_def]
QED

val _ = export_theory ()
