(*
  This file contains parts of the Splay Heap and Implicit Queue
  examples.  This file has been used to generate benchmark programs.
*)
open HolKernel Parse boolLib bossLib;
open bagTheory relationTheory bagLib miscTheory ml_translatorLib;
open preamble
open listTheory arithmeticTheory ml_translatorLib ListProgTheory;

val _ = new_theory "benchmark";

val _ = translation_extends "ListProg";

val _ = Globals.interactive := false;

(* copied from ImplicitQueueScript *)

Datatype:
  times = Once 'a | Twice times times
End

Datatype:
  digit = Zero | One ('a times) | Two ('a times) ('a times)
End

Datatype:
  queue = Shallow ('a digit)
        | Deep ('a digit) queue ('a digit)
End

Definition empty_def:
  empty = Shallow Zero
End
val r = translate empty_def;

Definition is_empty_def:
  (is_empty (Shallow Zero) = T) /\
  (is_empty _ = F)
End
val r = translate is_empty_def;

Definition snoc_def:
  (snoc (Shallow Zero) y = Shallow (One y)) /\
  (snoc (Shallow (One x)) y = Deep (Two x y) empty Zero) /\
  (snoc (Deep f m Zero) y = Deep f m (One y)) /\
  (snoc (Deep f m (One x)) y = Deep f (snoc m (Twice x y)) Zero)
End
val r = translate snoc_def;

Definition head_def:
  (head (Shallow (One x)) = x) /\
  (head (Deep (One x) m r) = x) /\
  (head (Deep (Two x y) m r) = x)
End
val r = translate head_def;

Definition tail_def:
  (tail (Shallow (One x)) = empty) /\
  (tail (Deep (Two x y) m r) = Deep (One y) m r) /\
  (tail (Deep (One x) q r) =
     if is_empty q then Shallow r else
       case head q of Twice y z => Deep (Two y z) (tail q) r)
End
val r = translate tail_def;


Definition use_queue_def:
(use_queue 0 q ⇔ q) ∧
(use_queue (SUC n) q ⇔
  use_queue n (tail (snoc (snoc q (Once n)) (Once n))))
End
val r = translate use_queue_def;

Definition run_queue_def:
run_queue ⇔ head (use_queue 1000 empty)
End
val r = translate run_queue_def;


(* Copied from SplayHeapScript *)

Datatype:
  heap = Empty | Tree heap 'a heap
End

Definition heap_to_bag_def:
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree h1 x h2) =
  BAG_INSERT x (BAG_UNION (heap_to_bag h1) (heap_to_bag h2)))
End

Definition is_heap_ordered_def:
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree h1 x h2) <=>
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key y) (get_key x)) (heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h2))
End

Definition empty'_def:
  empty' = Empty
End
val r = translate empty'_def;

Definition is_empty'_def:
(is_empty' Empty = T) ∧
(is_empty' _ = F)
End
val r = translate is_empty'_def;

Definition partition_def:
(partition get_key leq pivot Empty = (Empty, Empty)) ∧
(partition get_key leq pivot (Tree a x b) =
  if leq (get_key x) (get_key pivot) then
    (case b of
        Empty => (Tree a x b, Empty)
      | Tree b1 y b2 =>
          if leq (get_key y) (get_key pivot) then
            let (small, big) = partition get_key leq pivot b2 in
              (Tree (Tree a x b1) y small, big)
          else
            let (small, big) = partition get_key leq pivot b1 in
              (Tree a x small, Tree big y b2))
  else
    (case a of
        Empty => (Empty, Tree a x b)
      | Tree a1 y a2 =>
          if leq (get_key y) (get_key pivot) then
            let (small, big) = partition get_key leq pivot a2 in
              (Tree a1 y small, Tree big x b)
          else
            let (small, big) = partition get_key leq pivot a1 in
              (small, Tree big y (Tree a2 x b))))
End
val r = translate partition_def;

val partition_ind = fetch "-" "partition_ind"
val heap_size_def = fetch "-" "heap_size_def"

Triviality partition_size:
  !get_key leq p h1 h2 h3.
  ((h2,h3) = partition get_key leq p h1)
  ⇒
  heap_size f h2 ≤ heap_size f h1 ∧ heap_size f h3 ≤ heap_size f h1
Proof
  recInduct partition_ind >>
rw [heap_size_def, partition_def] >>
every_case_tac >>
fs [] >>
rw [heap_size_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM] >>
rw [heap_size_def] >>
decide_tac
QED

Definition insert_def:
insert get_key leq x t =
  let (a, b) = partition get_key leq x t in
    Tree a x b
End
val r = translate insert_def;

Definition merge_def:
(merge get_key leq Empty h2 = h2) ∧
(merge get_key leq (Tree a x b) h2 =
  let (ta, tb) = partition get_key leq x h2 in
    Tree (merge get_key leq ta a) x (merge get_key leq tb b))

Termination
  WF_REL_TAC `measure (\(_,x,y,z).  heap_size (\_.1) y + heap_size (\_.1) z)` >>
 rw [] >>
 imp_res_tac partition_size >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [partition_size]
End

val _ = translate merge_def

val merge_ind = fetch "-" "merge_ind"

Definition find_min_def:
(find_min (Tree Empty x b) = x) ∧
(find_min (Tree a x b) = find_min a)
End
val r = translate find_min_def;

val find_min_ind = fetch "-" "find_min_ind"

Definition delete_min_def:
(delete_min (Tree Empty x b) = b) ∧
(delete_min (Tree (Tree Empty x b) y c) = Tree b y c) ∧
(delete_min (Tree (Tree a x b) y c) = Tree (delete_min a) x (Tree b y c))
End
val r = translate delete_min_def;

val delete_min_ind = fetch "-" "delete_min_ind"

Definition use_heap_def:
(use_heap 0 h ⇔ h) ∧
(use_heap (SUC n) h ⇔
  use_heap n (insert (\x.x) ((\x y. x < y) :num->num->bool) n (delete_min (insert (\x.x) ((\x y. x < y) :num->num->bool) (n + 400000) h))))
End
val r = translate use_heap_def;

Definition run_heap:
run_heap ⇔ find_min (use_heap 1000 empty')
End
val r = translate run_heap;

val _ = export_theory ();
