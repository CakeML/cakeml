(*
  This is an example of applying the translator to the Unbalanced
  Set algorithm from Chris Okasaki's book.
*)
open preamble
open okasaki_miscTheory pred_setTheory pred_setSimps
open ml_translatorLib ListProgTheory;

val _ = new_theory "UnbalancedSet"

val _ = translation_extends "ListProg";

(* Okasaki page 14 *)

val _ = Hol_datatype `
tree = Empty | Tree of tree => 'a => tree`;

val tree_to_set_def = Define `
(tree_to_set Empty = {}) ∧
(tree_to_set (Tree t1 x t2) = {x} ∪ tree_to_set t1 ∪ tree_to_set t2)`;

(* That the tree is a binary search tree *)
val is_bst_def = Define `
(is_bst lt Empty <=> T) ∧
(is_bst lt (Tree t1 x t2) <=>
  is_bst lt t1 ∧
  is_bst lt t2 ∧
  (!y. y ∈ tree_to_set t1 ⇒ lt y x) ∧
  (!y. y ∈ tree_to_set t2 ⇒ lt x y))`;

val empty_def = mlDefine `
empty = Empty`;

val member_def = mlDefine `
(member lt x Empty = F) ∧
(member lt x (Tree a y b) =
  if lt x y then
    member lt x a
  else if lt y x then
    member lt x b
  else
    T)`;

val insert_def = mlDefine `
(insert lt x Empty = Tree Empty x Empty) ∧
(insert lt x (Tree a y b) =
  if lt x y then
    Tree (insert lt x a) y b
  else if lt y x then
    Tree a y (insert lt x b)
  else
    Tree a y b)`;


(* Correctness proof *)

Theorem member_correct:
 !lt t x.
  StrongLinearOrder lt ∧ is_bst lt t
  ⇒
  (member lt x t <=> x ∈ tree_to_set t)
Proof
strip_tac >> induct_on `t` >>
rw [member_def, is_bst_def, tree_to_set_def] >> fs [] >>
fs [StrongLinearOrder, StrongOrder, irreflexive_def, transitive_def,
    trichotomous] >>
metis_tac []
QED

Theorem insert_set:
 ∀lt x t.
  StrongLinearOrder lt
  ⇒
  (tree_to_set (insert lt x t) = {x} ∪ tree_to_set t)
Proof
induct_on `t` >>
srw_tac [PRED_SET_AC_ss] [insert_def, tree_to_set_def] >>
`x = a` by (fs [StrongLinearOrder, StrongOrder, irreflexive_def,
                transitive_def, trichotomous] >>
            metis_tac []) >>
rw []
QED

Theorem insert_is_bst:
 !lt x t.
  StrongLinearOrder lt ∧ is_bst lt t
  ⇒
  is_bst lt (insert lt x t)
Proof
induct_on `t` >>
rw [is_bst_def, insert_def, tree_to_set_def, insert_set] >>
metis_tac []
QED

val _ = export_theory ();
