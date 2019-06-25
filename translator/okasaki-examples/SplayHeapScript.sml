(*
  This is an example of applying the translator to the Splay
  Heap algorithm from Chris Okasaki's book.
*)
open preamble
open bagTheory relationTheory bagLib okasaki_miscTheory ml_translatorLib ListProgTheory;

val rw = srw_tac []
val fs = full_simp_tac (srw_ss())

val _ = new_theory "SplayHeap"

val _ = translation_extends "ListProg";

(* Okasaki page 50 *)

val _ = Datatype`
  heap = Empty | Tree heap 'a heap`;

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


(* Functional correctnes proof *)

val partition_bags = Q.prove (
`!get_key leq p h1 h2 h3.
  ((h2,h3) = partition get_key leq p h1)
  ⇒
  (heap_to_bag h1 = BAG_UNION (heap_to_bag h2) (heap_to_bag h3))`,
recInduct partition_ind >>
rw [partition_def, heap_to_bag_def] >>
every_case_tac >>
fs [] >>
rw [heap_to_bag_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM] >>
rw [heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]);

val partition_split = Q.prove (
`!get_key leq p h1 h2 h3.
  transitive leq ∧
  trichotomous leq ∧
  ((h2,h3) = partition get_key leq p h1) ∧
  is_heap_ordered get_key leq h1
  ⇒
  BAG_EVERY (\y. leq (get_key y) (get_key p)) (heap_to_bag h2) ∧
  BAG_EVERY (\y. ¬leq (get_key y) (get_key p)) (heap_to_bag h3)`,
recInduct partition_ind >>
rw [partition_def, heap_to_bag_def, is_heap_ordered_def] >>
every_case_tac >>
fs [] >>
rw [] >>
fs [is_heap_ordered_def, heap_to_bag_def] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM, heap_to_bag_def] >>
rw [] >>
fs [BAG_EVERY, transitive_def, trichotomous] >>
metis_tac []);

val partition_heap_ordered_lem = Q.prove (
`!get_key leq p h1 h2 h3.
  (partition get_key leq p h1 = (h2, h3)) ⇒
  BAG_EVERY P (heap_to_bag h1) ⇒
  BAG_EVERY P (heap_to_bag h2) ∧ BAG_EVERY P (heap_to_bag h3)`,
rw [] >>
`heap_to_bag h1 =
 BAG_UNION (heap_to_bag h2) (heap_to_bag h3)`
          by metis_tac [partition_bags] >>
rw [] >>
fs [BAG_EVERY_UNION] >>
rw []);

val partition_heap_ordered = Q.prove (
`!get_key leq p h1 h2 h3.
  WeakLinearOrder leq ∧
  ((h2,h3) = partition get_key leq p h1) ∧
  is_heap_ordered get_key leq h1
  ⇒
  is_heap_ordered get_key leq h2 ∧ is_heap_ordered get_key leq h3`,
recInduct partition_ind >>
RW_TAC pure_ss [] >-
fs [partition_def, is_heap_ordered_def] >-
fs [partition_def, is_heap_ordered_def] >>
cases_on `leq (get_key x) (get_key pivot)` >>
fs [partition_def, is_heap_ordered_def] >>
every_case_tac >>
fs [] >>
rw [] >>
cases_on `partition get_key leq pivot h0` >>
cases_on `partition get_key leq pivot h` >>
fs [LET_THM, is_heap_ordered_def, heap_to_bag_def] >>
rw [] >-
(fs [BAG_EVERY] >>
 metis_tac [transitive_def, WeakLinearOrder, WeakOrder]) >-
metis_tac [partition_heap_ordered_lem] >-
metis_tac [partition_heap_ordered_lem] >-
metis_tac [partition_heap_ordered_lem] >-
metis_tac [partition_heap_ordered_lem] >-
metis_tac [partition_heap_ordered_lem] >-
metis_tac [partition_heap_ordered_lem] >-
(fs [BAG_EVERY] >>
 metis_tac [transitive_def, WeakLinearOrder, WeakOrder]));

Theorem insert_bag:
 !h get_key leq x.
  heap_to_bag (insert get_key leq x h) =
  BAG_INSERT x (heap_to_bag h)
Proof
induct_on `h` >>
rw [heap_to_bag_def, insert_def] >>
rw [heap_to_bag_def] >>
fs [insert_def] >>
imp_res_tac (GSYM partition_bags) >>
fs [heap_to_bag_def]
QED

Theorem insert_heap_ordered:
 !get_key leq x h.
  WeakLinearOrder leq ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)
Proof
rw [insert_def, is_heap_ordered_def] >>
rw [is_heap_ordered_def] >-
metis_tac [partition_heap_ordered] >-
metis_tac [partition_heap_ordered] >-
metis_tac [WeakLinearOrder, WeakOrder, partition_split] >-
(`BAG_EVERY (\y. ¬leq (get_key y) (get_key x)) (heap_to_bag b)`
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg])
QED

Theorem merge_bag:
 !get_key leq h1 h2.
  (heap_to_bag (merge get_key leq h1 h2) =
    BAG_UNION (heap_to_bag h1) (heap_to_bag h2))
Proof
recInduct merge_ind >>
rw [merge_def, heap_to_bag_def] >>
cases_on `partition get_key leq x h2` >>
fs [] >>
imp_res_tac (GSYM partition_bags) >>
rw [heap_to_bag_def, BAG_UNION_INSERT] >>
metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]
QED

Theorem merge_heap_ordered:
 !get_key leq h1 h2.
  WeakLinearOrder leq ∧ is_heap_ordered get_key leq h1 ∧ is_heap_ordered get_key leq h2
  ⇒
  is_heap_ordered get_key leq (merge get_key leq h1 h2)
Proof
recInduct merge_ind >>
rw [merge_def, is_heap_ordered_def] >>
rw [is_heap_ordered_def, merge_bag] >-
metis_tac [partition_heap_ordered] >-
metis_tac [partition_heap_ordered] >-
metis_tac [partition_split, WeakLinearOrder, WeakOrder] >-
(`BAG_EVERY (\y. ¬leq (get_key y) (get_key x)) (heap_to_bag tb)`
           by metis_tac [partition_split, WeakLinearOrder, WeakOrder] >>
 fs [BAG_EVERY] >>
 metis_tac [WeakLinearOrder_neg])
QED

Theorem find_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ Empty) ∧ is_heap_ordered get_key leq h
  ⇒
  BAG_IN (find_min h) (heap_to_bag h) ∧
  (!y. BAG_IN y (heap_to_bag h) ⇒
       leq (get_key (find_min h)) (get_key y))
Proof
recInduct find_min_ind >>
rw [heap_to_bag_def, find_min_def] >>
fs [is_heap_ordered_def, heap_to_bag_def, BAG_EVERY] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, reflexive_def]
QED

Theorem delete_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧
  (h ≠ Empty) ∧
  is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (delete_min h) ∧
  (heap_to_bag (delete_min h) =
   BAG_DIFF (heap_to_bag h) (EL_BAG (find_min h)))
Proof
HO_MATCH_MP_TAC delete_min_ind >>
srw_tac [bagLib.BAG_ss]
        [delete_min_def, is_heap_ordered_def, heap_to_bag_def,
         find_min_def, BAG_INSERT_UNION] >|
[res_tac >>
     rw [] >>
     match_mp_tac BAG_EVERY_DIFF >>
     rw [],
 fs [BAG_EVERY_EL],
 fs [BAG_EVERY_EL] >>
     fs [BAG_EVERY] >>
     metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
 res_tac >>
     srw_tac [BAG_AC_ss] [] >>
     `is_heap_ordered get_key leq (Tree v6 v7 v8)` by rw [is_heap_ordered_def] >>
     `BAG_IN (find_min (Tree v6 v7 v8)) (heap_to_bag (Tree v6 v7 v8))`
          by metis_tac [find_min_correct, fetch "-" "heap_distinct"] >>
     fs [heap_to_bag_def] >>
     `SUB_BAG (EL_BAG (find_min (Tree v6 v7 v8)))
              (EL_BAG v7 ⊎ (heap_to_bag v6 ⊎ heap_to_bag v8))`
                by rw [SUB_BAG_EL_BAG] >>
     rw [BAG_UNION_DIFF, SUB_BAG_UNION] >>
     srw_tac [BAG_AC_ss] []]
QED


(* Simplify the side conditions on the generated certificate theorems *)

val delete_min_side_def = fetch "-" "delete_min_side_def"
val find_min_side_def = fetch "-" "find_min_side_def"

val delete_min_side = Q.prove (
`!h. delete_min_side h = (h ≠ Empty)`,
recInduct delete_min_ind THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [delete_min_side_def] THEN SRW_TAC [] []);

val find_min_side = Q.prove (
`!h. find_min_side h = (h ≠ Empty)`,
recInduct find_min_ind THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [find_min_side_def] THEN SRW_TAC [] []);

val _ = export_theory()
