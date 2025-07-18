(*
  This is an example of applying the translator to the Lazy Pairing
  Heap algorithm from Chris Okasaki's book.
*)
open preamble
open bagTheory bagLib okasaki_miscTheory ml_translatorLib ListProgTheory

val _ = set_grammar_ancestry ["bag", "okasaki_misc", "ListProg"];

val _ = new_theory "LazyPairingHeap"

val _ = translation_extends "ListProg";

(* Okasaki page 80 *)

(* Note, we're following Chargueraud and just cutting out the laziness since it
 * shouldn't affect functional correctness *)

Datatype:
  heap = Empty | Tree 'a heap heap
End

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val heap_size_def = fetch "-" "heap_size_def"

Definition heap_to_bag_def:
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree x h1 h2) =
  BAG_INSERT x (BAG_UNION (heap_to_bag h1) (heap_to_bag h2)))
End

Definition is_heap_ordered_def:
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree x h1 h2) <=>
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h2))
End

Definition empty_def:
empty = Empty
End
val r = translate empty_def;

Definition is_empty:
(is_empty Empty = T) ∧
(is_empty _ = F)
End
val r = translate is_empty;

(*
Definition merge_def:
(merge get_key leq a Empty = a) ∧
(merge get_key leq Empty b = b) ∧
(merge get_key leq (Tree x h1 h2) (Tree y h1' h2') =
  if leq (get_key x) (get_key y) then
    link get_key leq (Tree x h1 h2) (Tree y h1' h2')
  else
    link get_key leq (Tree y h1' h2') (Tree x h1 h2)) ∧

(link get_key leq (Tree x Empty m) a = Tree x a m) ∧
(link get_key leq (Tree x b m) a =
  Tree x Empty (merge get_key leq (merge get_key leq a b) m))
End
*)

(* Without mutual recursion, and with size constraints to handle the nested
 * recursion *)

Definition merge_def:
 (merge get_key leq a Empty = a) /\
 (merge get_key leq Empty b = b) /\
 (merge get_key leq (Tree x h1 h2) (Tree y h1' h2') =
        if leq (get_key x) (get_key y) then
          case h1 of
          | Empty => Tree x (Tree y h1' h2') h2
          | _ =>
            (let h3 = merge get_key leq (Tree y h1' h2') h1 in
               if heap_size (\x.0) h3 <
                  heap_size (\x.0) h1' + heap_size (\x.0) h2' +
                  heap_size (\x.0) h1 + 2 then
                 Tree x Empty (merge get_key leq h3 h2)
               else
                 Empty)
        else
          case h1' of
          | Empty => Tree y (Tree x h1 h2) h2'
          | _ =>
            (let h3 = merge get_key leq (Tree x h1 h2) h1' in
               if heap_size (\x.0) h3 <
                  heap_size (\x.0) h1 + heap_size (\x.0) h2 +
                  heap_size (\x.0) h1' + 2 then
                 Tree y Empty (merge get_key leq h3 h2')
               else
                 Empty))
End

Triviality merge_size:
  !get_key leq h1 h2.
  heap_size (\x.0) (merge get_key leq h1 h2) =
  heap_size (\x.0) h1 + heap_size (\x.0) h2
Proof
  recInduct (fetch "-" "merge_ind") >>
srw_tac [ARITH_ss] [merge_def, heap_size_def] >|
[cases_on `h1`, cases_on `h1'`] >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
srw_tac [ARITH_ss] [merge_def,heap_size_def] >>
Q.UNABBREV_TAC `h3` >>
full_simp_tac (srw_ss()++ARITH_ss) [heap_size_def] >>
cases_on `leq (get_key y) (get_key a)` >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
cases_on `leq (get_key x) (get_key a)` >>
full_simp_tac (srw_ss()++numSimps.ARITH_AC_ss) [heap_size_def, merge_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []
QED

Triviality merge_size_lem:
  (heap_size (\x.0) (merge get_key leq (Tree x h1 h2) h1') <
  heap_size (\x.0) h1 + heap_size (\x.0) h2 + heap_size (\x.0) h1' + 2) = T
Proof
  rw [merge_size, heap_size_def] >>
decide_tac
QED

(* Remove the size constraints *)

val merge_def = SIMP_RULE (srw_ss()) [merge_size_lem, LET_THM] merge_def;
Theorem merge_def[compute,allow_rebind] =
  merge_def

val merge_ind =
  SIMP_RULE (srw_ss()) [merge_size_lem, LET_THM] (fetch "-" "merge_ind");
Theorem merge_ind[allow_rebind] =
  merge_ind

Triviality merge_thm:
  merge get_key leq a b =
    case (a,b) of
    | (a,Empty) => a
    | (Empty,b) => b
    | (Tree x h1 h2, Tree y h1' h2') =>
        if leq (get_key x) (get_key y) then
          case h1 of
          | Empty => Tree x (Tree y h1' h2') h2
          | _ =>
            Tree x Empty (merge get_key leq
                         (merge get_key leq (Tree y h1' h2') h1) h2)
        else
          case h1' of
          | Empty => Tree y (Tree x h1 h2) h2'
          | _ =>
            Tree y Empty (merge get_key leq
                         (merge get_key leq (Tree x h1 h2) h1') h2')
Proof
  Cases_on `a` THEN Cases_on `b` THEN SIMP_TAC (srw_ss()) [merge_def]
QED

val _ = translate merge_thm;

Definition insert_def:
insert get_key leq x a = merge get_key leq (Tree x Empty Empty) a
End
val r = translate insert_def;

Definition find_min_def:
find_min (Tree x _ _) = x
End
val r = translate find_min_def;

Definition delete_min_def:
delete_min get_key leq (Tree _ a b) = merge get_key leq a b
End
val r = translate delete_min_def;

(* Functional correctness *)

Theorem merge_bag:
 !get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION] >|
[cases_on `h1`,cases_on `h1'`] >>
fs [] >>
srw_tac [BAG_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION]
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
rw [merge_def, is_heap_ordered_def, merge_bag] >|
[cases_on `h1`,cases_on `h1'`] >>
rw [is_heap_ordered_def, heap_to_bag_def, BAG_EVERY, merge_def] >>
fs [BAG_EVERY, is_heap_ordered_def, merge_bag, heap_to_bag_def] >|
[metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 cases_on `leq (get_key y) (get_key a)` >>
     fs [],
 cases_on `h1'` >>
     fs [heap_to_bag_def, merge_bag] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 cases_on `leq (get_key y) (get_key a)` >>
     fs [],
 cases_on `h` >>
     fs [heap_to_bag_def, merge_bag] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg],
 cases_on `leq (get_key x) (get_key a)` >>
     fs [],
 cases_on `h1` >>
     fs [heap_to_bag_def, merge_bag] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def,
                WeakLinearOrder_neg],
 cases_on `leq (get_key x) (get_key a)` >>
     fs [],
 cases_on `h` >>
     fs [heap_to_bag_def, merge_bag] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def,
                WeakLinearOrder_neg]]
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
`is_heap_ordered get_key leq (Tree x Empty Empty)`
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

val _ = export_theory ();
