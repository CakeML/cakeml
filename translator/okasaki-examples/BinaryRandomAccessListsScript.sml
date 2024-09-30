(*
  This is an example of applying the translator to the Binary Random
  Access Lists algorithm from Chris Okasaki's book.
*)
open preamble
open okasaki_miscTheory ml_translatorLib ListProgTheory;

val _ = new_theory "BinaryRandomAccessLists"

val _ = translation_extends "ListProg";

(* Okasaki page 123 *)

Datatype:
  tree = Leaf 'a | Node num tree tree
End

Datatype:
  digit = Zero | One ('a tree)
End

Type rlist = ``:'a digit list``

Definition empty_def:
empty = []
End
val r = translate empty_def;

Definition is_empty_def:
(is_empty [] = T) ∧
(is_empty _ = F)
End
val r = translate is_empty_def;

Definition size_def:
(size (Leaf _) = 1) ∧
(size (Node w _ _) = w)
End
val r = translate size_def;

Definition link_def:
(link t1 t2 = Node (size t1 + size t2) t1 t2)
End
val r = translate link_def;

Definition cons_tree_def:
(cons_tree t [] = [One t]) ∧
(cons_tree t (Zero :: ts) = One t :: ts) ∧
(cons_tree t1 (One t2 :: ts) = Zero :: cons_tree (link t1 t2) ts)
End
val r = translate cons_tree_def;

Definition uncons_tree_def:
(uncons_tree [One t] = (t, [])) ∧
(uncons_tree (One t::ts) = (t, Zero :: ts)) ∧
(uncons_tree (Zero :: ts) =
  case uncons_tree ts of
    | (Node _ t1 t2, ts') => (t1, One t2 :: ts'))
End
val r = translate uncons_tree_def;

Definition cons_def:
cons x ts = cons_tree (Leaf x) ts
End
val r = translate cons_def;

Definition head_def:
head ts =
  case uncons_tree ts of
    | (Leaf x, _) => x
End
val r = translate head_def;

Definition tail_def:
tail ts = let (x,ts') = uncons_tree ts in ts'
End
val r = translate tail_def;

Definition lookup_tree_def:
(lookup_tree i (Leaf x) = if i = 0 then x else ARB) ∧
(lookup_tree i (Node w t1 t2) =
  if i < w DIV 2  then
    lookup_tree i t1
  else
    lookup_tree (i - w DIV 2) t2)
End
val r = translate lookup_tree_def;

Definition update_tree_def:
(update_tree i y (Leaf x) = if i = 0 then Leaf y else ARB) ∧
(update_tree i y (Node w t1 t2) =
  if i < w DIV 2 then
    Node w (update_tree i y t1) t2
  else
    Node w t1 (update_tree (i - w DIV 2) y t2))
End
val r = translate update_tree_def;

Definition def:
(lookup i (Zero::ts) = lookup i ts) ∧
(lookup i (One t::ts) =
  if i < size t then
    lookup_tree i t
  else
    lookup (i - size t) ts)
End

Definition update_def:
(update i y (Zero::ts) = Zero::update i y ts) ∧
(update i y (One t::ts) =
  if i < size t then
    One (update_tree i y t) :: ts
  else
    One t :: update (i - size t) y ts)
End
val r = translate update_def;

val _ = export_theory ();
