(*
  This is an example of applying the translator to the Binomial Heap
  algorithm from Chris Okasaki's book.
*)
open preamble
open bagTheory bagLib okasaki_miscTheory ml_translatorLib ListProgTheory;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "BinomialHeap"

val _ = translation_extends "ListProg";

(* Okasaki page 24 *)

Datatype:
  tree = Node num 'a (tree list)
End

Type heap = ``:'a tree list``

Definition heap_to_bag_def:
(heap_to_bag [] = {||}) ∧
(heap_to_bag (h::hs) =
  BAG_UNION (tree_to_bag h) (heap_to_bag hs)) ∧

(tree_to_bag (Node _ x hs) =
  BAG_INSERT x (heap_to_bag hs))
End

Definition is_heap_ordered_def:
(is_heap_ordered get_key leq [] <=> T) ∧
(is_heap_ordered get_key leq (t::ts) <=>
  is_heap_ordered_tree get_key leq t ∧ is_heap_ordered get_key leq ts) ∧

(is_heap_ordered_tree get_key leq (Node _ x hs) <=>
  is_heap_ordered get_key leq hs ∧
  BAG_EVERY (\y. leq (get_key x) (get_key y)) (heap_to_bag hs))
End

Definition empty_def:
empty = []
End
val r = translate empty_def;

Definition is_empty_def:
(is_empty [] = T) ∧
(is_empty _ = F)
End
val r = translate is_empty_def;

Definition rank_def:
rank (Node r x c) = r
End
val r = translate rank_def;

Definition root_def:
root (Node r x c) = x
End
val r = translate root_def;

Definition link_def:
link get_key leq (Node r x1 c1) (Node r' x2 c2) =
  if leq (get_key x1) (get_key x2) then
    Node (r+1) x1 ((Node r' x2 c2)::c1)
  else
    Node (r+1) x2 ((Node r x1 c1)::c2)
End
val r = translate link_def;

Definition ins_tree_def:
(ins_tree get_key leq t [] = [t]) ∧
(ins_tree get_key leq t (t'::ts') =
  if rank t < rank t' then
    t::t'::ts'
  else
    ins_tree get_key leq (link get_key leq t t') ts')
End
val r = translate ins_tree_def;

Definition insert_def:
insert get_key leq x ts = ins_tree get_key leq (Node 0 x []) ts
End
val r = translate insert_def;

Definition merge_def:
(merge get_key leq ts [] = ts) ∧
(merge get_key leq [] ts = ts) ∧
(merge get_key leq (t1::ts1) (t2::ts2) =
  if rank t1 < rank t2 then
    t1 :: merge get_key leq ts1 (t2::ts2)
  else if rank t2 < rank t1 then
    t2 :: merge get_key leq (t1::ts1) ts2
  else
    ins_tree get_key leq (link get_key leq t1 t2) (merge get_key leq ts1 ts2))
End
val r = translate merge_def;

val merge_ind = fetch "-" "merge_ind";

Definition remove_min_tree_def:
(remove_min_tree get_key leq [t] = (t,[])) ∧
(remove_min_tree get_key leq (t::ts) =
  let (t',ts') = remove_min_tree get_key leq ts in
    if leq (get_key (root t)) (get_key (root t')) then
      (t,ts)
    else
      (t',t::ts'))
End
val r = translate remove_min_tree_def;

Definition find_min_def:
find_min get_key leq ts =
  let (t,ts') = remove_min_tree get_key leq ts in
    root t
End
val r = translate find_min_def;

Definition delete_min_def:
delete_min get_key leq ts =
  case remove_min_tree get_key leq ts of
    | (Node _ x ts1, ts2) => merge get_key leq (REVERSE ts1) ts2
End
val r = translate delete_min_def;


(* Functional correctness proof *)

Triviality ins_bag:
  !get_key leq t h.
  heap_to_bag (ins_tree get_key leq t h) =
  BAG_UNION (tree_to_bag t) (heap_to_bag h)
Proof
  induct_on `h` >>
rw [heap_to_bag_def, ins_tree_def, link_def] >>
cases_on `t` >>
cases_on `h'` >>
srw_tac [BAG_ss] [heap_to_bag_def, ins_tree_def, link_def, BAG_INSERT_UNION]
QED

Triviality ins_heap_ordered:
  !get_key leq t h.
  WeakLinearOrder leq ∧
  is_heap_ordered_tree get_key leq t ∧
  is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (ins_tree get_key leq t h)
Proof
  induct_on `h` >>
rw [is_heap_ordered_def, ins_bag, ins_tree_def] >>
cases_on `t` >>
cases_on `h'` >>
rw [link_def] >>
fs [] >>
Q.PAT_X_ASSUM `!get_key leq t. P get_key leq t` match_mp_tac >>
rw [is_heap_ordered_def] >>
fs [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]
QED

Theorem insert_bag:
 !get_key leq s h.
  heap_to_bag (insert get_key leq s h) = BAG_INSERT s (heap_to_bag h)
Proof
rw [insert_def, ins_bag, heap_to_bag_def, BAG_INSERT_UNION]
QED

Theorem insert_heap_ordered:
 !get_key leq x h.
  WeakLinearOrder leq ∧
  is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (insert get_key leq x h)
Proof
rw [insert_def, is_heap_ordered_def] >>
match_mp_tac ins_heap_ordered >>
rw [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def]
QED

Theorem merge_bag:
 !get_key leq h1 h2.
  heap_to_bag (merge get_key leq h1 h2) =
  BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
HO_MATCH_MP_TAC merge_ind >>
srw_tac [BAG_ss] [merge_def, heap_to_bag_def, BAG_INSERT_UNION, ins_bag] >>
cases_on `t1` >>
cases_on `t2` >>
srw_tac [BAG_ss] [link_def, heap_to_bag_def, BAG_INSERT_UNION]
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
fs [] >>
match_mp_tac ins_heap_ordered >>
rw [] >>
cases_on `t1` >>
cases_on `t2` >>
rw [link_def, is_heap_ordered_def, BAG_EVERY] >>
fs [is_heap_ordered_def, BAG_EVERY, heap_to_bag_def] >>
metis_tac [WeakLinearOrder, WeakOrder, transitive_def, WeakLinearOrder_neg]
QED

Triviality remove_min_tree:
  ∀get_key leq h t h'.
  WeakLinearOrder leq ∧
  (h ≠ []) ∧
  is_heap_ordered get_key leq h ∧
  ((t,h') = remove_min_tree get_key leq h)
  ⇒
  is_heap_ordered get_key leq h' ∧
  is_heap_ordered_tree get_key leq t ∧
  (heap_to_bag h = BAG_UNION (heap_to_bag h') (tree_to_bag t)) ∧
  (!y. BAG_IN y (heap_to_bag h') ⇒ leq (get_key (root t)) (get_key y))
Proof
  induct_on `h` >>
rw [heap_to_bag_def] >>
cases_on `h` >>
cases_on `t` >>
full_simp_tac (srw_ss()++BAG_ss)
              [root_def, remove_min_tree_def, heap_to_bag_def] >>
rw [is_heap_ordered_def] >>
fs [LET_THM, is_heap_ordered_def] >>
cases_on `remove_min_tree get_key leq (h'''::t')` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [] >>
full_simp_tac (srw_ss()++BAG_ss)
              [root_def, is_heap_ordered_def, heap_to_bag_def,
               BAG_INSERT_UNION] >|
[
  metis_tac [is_heap_ordered_def],

 metis_tac [is_heap_ordered_def],

 `tree_to_bag h''' ⊎ heap_to_bag t' = heap_to_bag r ⊎ tree_to_bag (Node n a l)`
              by metis_tac [] >>
     simp[Once COMM_BAG_UNION] >>
     srw_tac [BAG_ss] [heap_to_bag_def, BAG_INSERT_UNION],

 `BAG_IN y (tree_to_bag q) ∨ BAG_IN y (heap_to_bag r)`
        by metis_tac [BAG_IN_BAG_UNION] >|
     [`is_heap_ordered_tree get_key leq q` by metis_tac [] >>
          `leq (get_key (root q)) (get_key y)`
                  by (cases_on `q` >>
                      fs [BAG_EVERY, is_heap_ordered_def, root_def,
                          heap_to_bag_def] >>
                      metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]) >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
      fs [BAG_EVERY] >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def]],

 `BAG_IN y (tree_to_bag q) ∨ BAG_IN y (heap_to_bag r)`
        by metis_tac [BAG_IN_BAG_UNION] >|
     [`is_heap_ordered_tree get_key leq q` by metis_tac [] >>
          `leq (get_key (root q)) (get_key y)`
                  by (cases_on `q` >>
                      fs [BAG_EVERY, is_heap_ordered_def, root_def,
                          heap_to_bag_def] >>
                      metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]) >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def],
      fs [BAG_EVERY] >>
          metis_tac [WeakLinearOrder, WeakOrder, transitive_def]],

 cases_on `h'` >>
     fs [root_def, is_heap_ordered_def, heap_to_bag_def, BAG_EVERY] >>
     metis_tac [WeakLinearOrder, WeakOrder, WeakLinearOrder_neg,
                transitive_def],

 metis_tac [WeakLinearOrder, WeakOrder, WeakLinearOrder_neg, root_def,
            transitive_def]
]
QED

Theorem find_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ []) ∧ is_heap_ordered get_key leq h
  ⇒
  BAG_IN (find_min get_key leq h) (heap_to_bag h) ∧
  (!y. BAG_IN y (heap_to_bag h)
       ⇒
       leq (get_key (find_min get_key leq h)) (get_key y))
Proof
rw [find_min_def] >>
`(heap_to_bag h = BAG_UNION (heap_to_bag ts') (tree_to_bag t)) ∧
 (∀y. y ⋲ heap_to_bag ts' ⇒ leq (get_key (root t)) (get_key y)) ∧
 (is_heap_ordered_tree get_key leq t)`
        by metis_tac [remove_min_tree] >>
cases_on `t` >>
fs [BAG_EVERY, heap_to_bag_def, root_def, is_heap_ordered_def] >>
metis_tac [WeakLinearOrder, WeakOrder, reflexive_def]
QED

Triviality reverse_heap_ordered:
  !get_key leq l.
  is_heap_ordered get_key leq l ⇒ is_heap_ordered get_key leq (REVERSE l)
Proof
  induct_on `l` >>
rw [is_heap_ordered_def] >>
res_tac >>
POP_ASSUM MP_TAC >>
Q.SPEC_TAC (`REVERSE l`, `l'`) >>
rw [] >>
induct_on `l'` >>
rw [is_heap_ordered_def]
QED

Triviality append_bag:
  !h1 h2. heap_to_bag (h1++h2) = BAG_UNION (heap_to_bag h1) (heap_to_bag h2)
Proof
  induct_on `h1` >>
srw_tac [BAG_ss] [heap_to_bag_def]
QED

Triviality reverse_bag:
  !l. heap_to_bag (REVERSE l) = heap_to_bag l
Proof
  induct_on `l` >>
srw_tac [BAG_ss] [append_bag, heap_to_bag_def]
QED

Theorem delete_min_correct:
 !h get_key leq.
  WeakLinearOrder leq ∧ (h ≠ []) ∧ is_heap_ordered get_key leq h
  ⇒
  is_heap_ordered get_key leq (delete_min get_key leq h) ∧
  (heap_to_bag (delete_min get_key leq h) =
   BAG_DIFF (heap_to_bag h) (EL_BAG (find_min get_key leq h)))
Proof
rw [delete_min_def] >>
every_case_tac >>
rw [merge_bag, reverse_bag] >-
metis_tac [reverse_heap_ordered, merge_heap_ordered, remove_min_tree,
           is_heap_ordered_def] >>
rw [find_min_def, root_def] >>
rw [root_def] >>
`(heap_to_bag h = BAG_UNION (heap_to_bag r) (tree_to_bag (Node n a l)))`
           by metis_tac [remove_min_tree] >>
rw [heap_to_bag_def, BAG_DIFF, BAG_INSERT, EL_BAG, FUN_EQ_THM, EMPTY_BAG,
    BAG_UNION] >>
cases_on `x = a` >>
srw_tac [ARITH_ss] []
QED


(* Verify size and shape invariants *)

Definition heap_size_def:
(heap_size [] = 0) ∧
(heap_size (t::ts) = heap_tree_size t + heap_size ts) ∧
(heap_tree_size (Node _ _ trees) = (1:num) + heap_size trees)
End

Definition is_binomial_tree_def:
(is_binomial_tree (Node r x []) <=> (r = 0)) ∧
(is_binomial_tree (Node r x (t::ts)) <=>
  SORTED ($> : num->num->bool) (MAP rank (t::ts)) ∧
  (r ≠ 0) ∧
  is_binomial_tree t ∧
  (rank t = r - 1) ∧
  is_binomial_tree (Node (r - 1) x ts))
End

val is_binomial_tree_ind = fetch "-" "is_binomial_tree_ind";

Triviality exp2_mod2:
  !x. x ≠ 0 ⇒ (2 ** x MOD 2 = 0)
Proof
  induct_on `x` >>
rw [] >>
cases_on `x = 0`>>
fs [arithmeticTheory.ADD1, arithmeticTheory.EXP_ADD,
    arithmeticTheory.MOD_EQ_0]
QED

Theorem is_binomial_tree_size:
 !t. is_binomial_tree t ⇒ (heap_tree_size t = 2 ** rank t)
Proof
recInduct is_binomial_tree_ind >>
rw [heap_size_def, rank_def, is_binomial_tree_def] >>
fs [] >>
`1 + (2 ** (r − 1) + heap_size ts) = 2 ** (r − 1) + (1 + heap_size ts)`
           by decide_tac >>
rw [] >>
`1 ≤ r` by decide_tac >>
rw [arithmeticTheory.EXP_SUB, GSYM arithmeticTheory.TIMES2,
    bitTheory.DIV_MULT_THM2, exp2_mod2]
QED

Definition is_binomial_heap_def:
is_binomial_heap h <=>
  EVERY is_binomial_tree h ∧ SORTED ($< : num->num->bool) (MAP rank h)
End

Triviality trans_less:
  transitive ($< : num->num->bool)
Proof
  rw [transitive_def] >>
decide_tac
QED

Triviality trans_great:
  transitive ($> : num->num->bool)
Proof
  rw [transitive_def] >>
decide_tac
QED

Triviality link_binomial_tree:
  !get_key leq t1 t2.
  is_binomial_tree t1 ∧ is_binomial_tree t2 ∧ (rank t1 = rank t2)
  ⇒
  is_binomial_tree (link get_key leq t1 t2) ∧
  (rank (link get_key leq t1 t2) = rank t1 + 1)
Proof
  cases_on `t1` >>
cases_on `t2` >>
rw [link_def, is_binomial_tree_def, rank_def] >>
cases_on `l` >>
cases_on `l'` >>
fs [is_binomial_tree_def, SORTED_EQ, SORTED_DEF, trans_great] >>
rw [] >>
res_tac >>
decide_tac
QED

Triviality ins_binomial_heap:
  !get_key leq t h.
  is_binomial_tree t ∧
  is_binomial_heap h ∧
  (!t'. MEM t' h ⇒ rank t ≤ rank t')
  ⇒
  is_binomial_heap (ins_tree get_key leq t h) ∧
  (!r. (r < rank t) ⇒ EVERY (\t'. r < rank t') (ins_tree get_key leq t h))
Proof
  induct_on `h` >>
rw [is_binomial_heap_def, trans_less, SORTED_EQ, SORTED_DEF, ins_tree_def] >>
`rank t ≤ rank h'` by metis_tac [] >-
decide_tac >-
(fs [EVERY_MEM] >>
 metis_tac [arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
`rank t = rank h'` by decide_tac >>
fs [is_binomial_heap_def, MEM_MAP] >>
`is_binomial_tree (link get_key leq t h') ∧
 (rank (link get_key leq t h') = rank t + 1)`
              by metis_tac [link_binomial_tree] >>
metis_tac [DECIDE ``!(x:num) y . x < y ==> x < y + 1``,
           DECIDE ``!(x:num) y . x < y ==> x + 1 ≤ y``]
QED

Theorem merge_binomial_heap:
 !get_key leq h1 h2.
  is_binomial_heap h1 ∧ is_binomial_heap h2
  ⇒
  is_binomial_heap (merge get_key leq h1 h2) ∧
  (!r.
    EVERY (\t. r < rank t) h1 ∧ EVERY (\t. r < rank t) h2
    ⇒
    EVERY (\t. r < rank t) (merge get_key leq h1 h2))
Proof
recInduct merge_ind >>
rw [is_binomial_heap_def, merge_def, trans_less, SORTED_EQ,
    is_binomial_tree_def] >>
fs [MEM_MAP, EVERY_MEM] >>
rw [] >-
metis_tac [trans_less, transitive_def] >-
metis_tac [trans_less, transitive_def] >>
`rank t1 = rank t2` by decide_tac >>
fs [] >>
`is_binomial_tree (link get_key leq t1 t2) ∧
 (rank (link get_key leq t1 t2) = rank t1 + 1)`
            by metis_tac [link_binomial_tree] >>
`is_binomial_heap (merge get_key leq ts1 ts2)`
            by metis_tac [EVERY_MEM, is_binomial_heap_def] >>
`!t'. MEM t' (merge get_key leq ts1 ts2) ⇒ rank (link get_key leq t1 t2) ≤ rank t'`
           by metis_tac [DECIDE ``!(x:num) y. x < y ⇔ x + 1 ≤ y``] >-
metis_tac [is_binomial_heap_def, EVERY_MEM, ins_binomial_heap] >-
metis_tac [is_binomial_heap_def, EVERY_MEM, ins_binomial_heap] >>
`!r. (r < rank (link get_key leq t1 t2)) ⇒
     EVERY (\t'. r < rank t')
           (ins_tree get_key leq (link get_key leq t1 t2)
           (merge get_key leq ts1 ts2))`
     by metis_tac [ins_binomial_heap] >>
fs [EVERY_MEM] >>
metis_tac [DECIDE ``!(x:num) y . x < y ==> x < y + 1``]
QED

Theorem insert_binomial_heap:
 !get_key leq x h.
  is_binomial_heap h ⇒ is_binomial_heap (insert get_key leq x h)
Proof
rw [insert_def] >>
`is_binomial_tree (Node 0 x [])` by rw [is_binomial_tree_def] >>
metis_tac [ins_binomial_heap, rank_def, DECIDE ``!(x:num). 0 ≤ x``]
QED

Triviality remove_min_binomial_heap:
  !get_key leq h t h'.
  (h ≠ []) ∧ is_binomial_heap h ∧ ((t,h') = remove_min_tree get_key leq h)
  ⇒
  PERM (t::h') h ∧ is_binomial_tree t ∧ is_binomial_heap h'
Proof
  induct_on `h` >>
rw [remove_min_tree_def] >>
cases_on `h` >>
fs [remove_min_tree_def, is_binomial_heap_def, LET_THM, SORTED_DEF] >>
cases_on `remove_min_tree get_key leq (h'''::t')` >>
fs [] >>
every_case_tac >>
rw [] >-
metis_tac [PERM_SWAP_AT_FRONT, PERM_MONO, PERM_REFL, PERM_TRANS] >-
metis_tac [] >-
metis_tac [] >>
fs [trans_less, SORTED_EQ] >>
rw [] >-
metis_tac [] >>
`MEM y (MAP rank (q::r))` by metis_tac [MEM_MAP, MEM] >>
`MEM y (MAP rank (h'''::t'))` by metis_tac [PERM_MEM_EQ, PERM_MAP] >>
fs [] >>
metis_tac [MEM_MAP, trans_less, transitive_def]
QED

Triviality delete_lem:
  !n a l. is_binomial_tree (Node n a l) ⇒ is_binomial_heap (REVERSE l)
Proof
  induct_on `l` >>
rw [is_binomial_tree_def, is_binomial_heap_def, SORTED_DEF] >>
fs [is_binomial_heap_def, rich_listTheory.ALL_EL_REVERSE, trans_great,
    SORTED_EQ] >-
metis_tac [] >>
fs [SORTED_APPEND] >>
rw [trans_less, SORTED_DEF, sorted_reverse, rich_listTheory.MAP_REVERSE,
    GSYM arithmeticTheory.GREATER_DEF] >>
`(\(x:num) y. x > y) = $>` by metis_tac [] >>
rw []
QED

Theorem delete_min_binomial_heap:
 !get_key leq h.
  (h ≠ []) ∧ is_binomial_heap h
  ⇒
  is_binomial_heap (delete_min get_key leq h)
Proof
rw [delete_min_def] >>
cases_on `remove_min_tree get_key leq h` >>
rw [] >>
cases_on `q` >>
rw [] >>
metis_tac [delete_lem, merge_binomial_heap, remove_min_binomial_heap]
QED


(* Simplify the side conditions on the generated certificate theorems *)

val remove_min_tree_side_def = fetch "-" "remove_min_tree_side_def"

Triviality remove_min_tree_side:
  !get_key leq h. remove_min_tree_side get_key leq h = (h ≠ [])
Proof
  Induct_on `h`
THEN SIMP_TAC std_ss [Once remove_min_tree_side_def]
THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) []
QED

val _ = export_theory ();
