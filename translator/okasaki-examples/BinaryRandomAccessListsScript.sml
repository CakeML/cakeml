open preamble
open miscTheory ml_translatorLib mini_preludeTheory;

val _ = new_theory "BinaryRandomAccessLists"

val _ = translation_extends "mini_prelude";

(* Okasaki page 123 *)

val _ = Hol_datatype `
tree = Leaf of 'a | Node of num => tree => tree`;

val _ = Hol_datatype `
digit = Zero | One of 'a tree`;

val _ = type_abbrev ("rlist", ``:'a digit list``);

val empty_def = mlDefine `
empty = []`;

val is_empty_def = mlDefine `
(is_empty [] = T) ∧
(is_empty _ = F)`;

val size_def = mlDefine `
(size (Leaf _) = 1) ∧
(size (Node w _ _) = w)`;

val link_def = mlDefine `
(link t1 t2 = Node (size t1 + size t2) t1 t2)`;

val cons_tree_def = mlDefine `
(cons_tree t [] = [One t]) ∧
(cons_tree t (Zero :: ts) = One t :: ts) ∧
(cons_tree t1 (One t2 :: ts) = Zero :: cons_tree (link t1 t2) ts)`;

val uncons_tree_def = mlDefine `
(uncons_tree [One t] = (t, [])) ∧
(uncons_tree (One t::ts) = (t, Zero :: ts)) ∧
(uncons_tree (Zero :: ts) =
  case uncons_tree ts of
    | (Node _ t1 t2, ts') => (t1, One t2 :: ts'))`;

val cons_def = mlDefine `
cons x ts = cons_tree (Leaf x) ts`;

val head_def = mlDefine `
head ts =
  case uncons_tree ts of
    | (Leaf x, _) => x`;

val tail_def = mlDefine `
tail ts = let (x,ts') = uncons_tree ts in ts'`;

val lookup_tree_def = mlDefine `
(lookup_tree i (Leaf x) = if i = 0 then x else ARB) ∧
(lookup_tree i (Node w t1 t2) =
  if i < w DIV 2  then
    lookup_tree i t1
  else
    lookup_tree (i - w DIV 2) t2)`;

val update_tree_def = mlDefine `
(update_tree i y (Leaf x) = if i = 0 then Leaf y else ARB) ∧
(update_tree i y (Node w t1 t2) =
  if i < w DIV 2 then
    Node w (update_tree i y t1) t2
  else
    Node w t1 (update_tree (i - w DIV 2) y t2))`;

val lookup_def = mlDefine `
(lookup i (Zero::ts) = lookup i ts) ∧
(lookup i (One t::ts) =
  if i < size t then
    lookup_tree i t
  else
    lookup (i - size t) ts)`;

val update_def = mlDefine `
(update i y (Zero::ts) = Zero::update i y ts) ∧
(update i y (One t::ts) =
  if i < size t then
    One (update_tree i y t) :: ts
  else
    One t :: update (i - size t) y ts)`;

val _ = export_theory ();
