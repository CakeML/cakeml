open HolKernel Parse boolLib bossLib;
open bagTheory relationTheory bagLib miscTheory ml_translatorLib mini_preludeTheory;
open preamble

val _ = new_theory "benchmark";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;

val _ = translation_extends "mini_prelude";

(* copied from ImplicitQueueScript *)
val _ = Hol_datatype `times = Once of 'a | Twice of times => times`;
val _ = Hol_datatype `digit = Zero | One of 'a times | Two of 'a times => 'a times`;
val _ = Hol_datatype `queue = Shallow of 'a digit
                            | Deep of 'a digit => queue => 'a digit`;

val empty_def = mlDefine `
  empty = Shallow Zero`;

val is_empty_def = mlDefine `
  (is_empty (Shallow Zero) = T) /\
  (is_empty _ = F)`;

val snoc_def = mlDefine `
  (snoc (Shallow Zero) y = Shallow (One y)) /\
  (snoc (Shallow (One x)) y = Deep (Two x y) empty Zero) /\
  (snoc (Deep f m Zero) y = Deep f m (One y)) /\
  (snoc (Deep f m (One x)) y = Deep f (snoc m (Twice x y)) Zero)`

val head_def = mlDefine `
  (head (Shallow (One x)) = x) /\
  (head (Deep (One x) m r) = x) /\
  (head (Deep (Two x y) m r) = x)`;

val tail_def = mlDefine `
  (tail (Shallow (One x)) = empty) /\
  (tail (Deep (Two x y) m r) = Deep (One y) m r) /\
  (tail (Deep (One x) q r) =
     if is_empty q then Shallow r else
       case head q of Twice y z => Deep (Two y z) (tail q) r)`


val use_queue_def = mlDefine `
(use_queue 0 q ⇔ q) ∧
(use_queue (SUC n) q ⇔
  use_queue n (tail (snoc (snoc q (Once n)) (Once n))))`;

val run_queue_def = mlDefine `
run_queue ⇔ head (use_queue 1000 empty)`;


(* Copied from SplayHeapScript *)

val _ = Hol_datatype `
heap = Empty | Tree of heap => 'a => heap`;

val heap_to_bag_def = Define `
(heap_to_bag Empty = {||}) ∧
(heap_to_bag (Tree h1 x h2) =
  BAG_INSERT x (BAG_UNION (heap_to_bag h1) (heap_to_bag h2)))`;

val is_heap_ordered_def = Define `
(is_heap_ordered get_key leq Empty <=> T) ∧
(is_heap_ordered get_key leq (Tree h1 x h2) <=>
  is_heap_ordered get_key leq h1 ∧
  is_heap_ordered get_key leq h2 ∧
  BAG_EVERY (\y. leq (get_key y) (get_key x)) (heap_to_bag h1) ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag h2))`;

val _ = mlDefine `
empty = Empty`;

val is_empty_def = mlDefine `
(is_empty Empty = T) ∧
(is_empty _ = F)`;

val partition_def = mlDefine `
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
              (small, Tree big y (Tree a2 x b))))`;

val partition_ind = fetch "-" "partition_ind"
val heap_size_def = fetch "-" "heap_size_def"

val partition_size = Q.prove (
`!get_key leq p h1 h2 h3.
  ((h2,h3) = partition get_key leq p h1)
  ⇒
  heap_size f h2 ≤ heap_size f h1 ∧ heap_size f h3 ≤ heap_size f h1`,
recInduct partition_ind >>
rw [heap_size_def, partition_def] >>
every_case_tac >>
fs [] >>
rw [heap_size_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM] >>
rw [heap_size_def] >>
decide_tac);

val insert_def = mlDefine `
insert get_key leq x t =
  let (a, b) = partition get_key leq x t in
    Tree a x b`;

val merge_def = tDefine "merge" `
(merge get_key leq Empty h2 = h2) ∧
(merge get_key leq (Tree a x b) h2 =
  let (ta, tb) = partition get_key leq x h2 in
    Tree (merge get_key leq ta a) x (merge get_key leq tb b))`
(WF_REL_TAC `measure (\(_,x,y,z).  heap_size (\_.1) y + heap_size (\_.1) z)` >>
 rw [] >>
 imp_res_tac partition_size >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 pop_assum (MP_TAC o Q.SPEC `(λ_.1)`) >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [partition_size]);

val _ = translate merge_def

val merge_ind = fetch "-" "merge_ind"

val find_min_def = mlDefine `
(find_min (Tree Empty x b) = x) ∧
(find_min (Tree a x b) = find_min a)`;

val find_min_ind = fetch "-" "find_min_ind"

val delete_min_def = mlDefine `
(delete_min (Tree Empty x b) = b) ∧
(delete_min (Tree (Tree Empty x b) y c) = Tree b y c) ∧
(delete_min (Tree (Tree a x b) y c) = Tree (delete_min a) x (Tree b y c))`;

val delete_min_ind = fetch "-" "delete_min_ind"

val use_heap_def = mlDefine `
(use_heap 0 h ⇔ h) ∧
(use_heap (SUC n) h ⇔
  use_heap n (insert (\x.x) ((\x y. x < y) :num->num->bool) n (delete_min (insert (\x.x) ((\x y. x < y) :num->num->bool) (n + 400000) h))))`

val run_heap = mlDefine `
run_heap ⇔ find_min (use_heap 1000 empty)`;



val _ = export_theory ();
