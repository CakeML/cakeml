open preamble
open bagTheory bagLib ml_translatorLib okasaki_miscTheory ml_translatorLib ListProgTheory;

val _ = new_theory "SkewBinomialHeap";

val _ = translation_extends "ListProg";

(* Definition of a Skew Binomial Tree *)
Datatype `sbTree = Sbnode 'a num ('a list) (sbTree list)`;

val root_def = Define `root (Sbnode x r a c) = x`;

val rank_def = Define `rank (Sbnode _ r _ _) = r`;

val aux_def = Define `aux (Sbnode _ _ a _) = a`;

val children_def = Define `children (Sbnode _ _ _ c) = c`;

val link_def = Define `
  link geq (Sbnode x1 r1 a1 c1) (Sbnode x2 r2 a2 c2) =
    if geq x1 x2
    then (Sbnode x2 (r2+1) a2 ((Sbnode x1 r1 a1 c1)::c2))
    else (Sbnode x1 (r1+1) a1 ((Sbnode x2 r2 a2 c2)::c1))
`;

val skew_link_def = Define `
  skew_link geq x t1 t2 =
    let l = link geq t1 t2
    in let x' = root l
      and r = rank l
      and a = aux l
      and c = children l
      in
        (if geq x' x
         then (Sbnode x r (x'::a) c)
         else (Sbnode x' r (x::a) c))
  `;

val tree_to_bag_def = Define `
  (tree_to_bag (Sbnode x r a []) = (BAG_INSERT x (list_to_bag a))) /\
  (tree_to_bag (Sbnode x r a (c::cs)) = (BAG_UNION (tree_to_bag c) (tree_to_bag (Sbnode x r a cs))))
`;

val is_tree_ordered_def = Define `
      (is_tree_ordered geq (Sbnode x _ a []) = (BAG_EVERY (\y. geq y x) (list_to_bag a))) /\
      (is_tree_ordered geq (Sbnode x r a (c::cs)) =
         ((is_tree_ordered geq c) /\
         (BAG_EVERY (\y. geq y x) (tree_to_bag c)) /\
	 (is_tree_ordered geq (Sbnode x r a cs))))
`;

(* For both kinds of links, linking preserve the elements in the trees *)
Theorem link_bag:
  !geq t1 t2. BAG_UNION (tree_to_bag t1) (tree_to_bag t2) = tree_to_bag (link geq t1 t2)
Proof
  strip_tac \\
  rpt Cases \\
  rw[link_def,tree_to_bag_def] \\
  Induct_on `l'` \\
  rw[tree_to_bag_def, COMM_BAG_UNION, BAG_UNION_LEFT_CANCEL] \\
  Induct_on `l` \\
  metis_tac[tree_to_bag_def, BAG_UNION_LEFT_CANCEL, COMM_BAG_UNION ,ASSOC_BAG_UNION]
QED;

Theorem skew_link_bag:
  !geq x y z. tree_to_bag (skew_link geq x y z) = BAG_INSERT x (BAG_UNION (tree_to_bag y) (tree_to_bag z))
Proof
  ntac 2 strip_tac \\
  ntac 2 Cases \\
  rw[tree_to_bag_def, skew_link_def, link_def, root_def, aux_def, children_def, rank_def] \\
  fs[root_def]
  >- (Induct_on `l'` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION, (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION, (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l'` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION, (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def] \\
      metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION, (GSYM BAG_UNION_INSERT), BAG_UNION_LEFT_CANCEL])
QED;

(* for both kinds of links, linking preserve the ordering of the elements *)
Theorem link_order:
  !geq t1 t2.
    ((WeakLinearOrder geq) /\
     (is_tree_ordered geq t1) /\
     (is_tree_ordered geq t2)) ==> (is_tree_ordered geq (link geq t1 t2))
Proof
  strip_tac \\
  ntac 2 Cases \\
  rw[WeakLinearOrder, WeakOrder, link_def, is_tree_ordered_def, BAG_EVERY, tree_to_bag_def]
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, list_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      fs[is_tree_ordered_def, BAG_EVERY] \\
      metis_tac[transitive_def])
  >- (Induct_on `l'` \\
      rw[is_tree_ordered_def])
  >- (Induct_on `l` \\
      rw[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      fs[is_tree_ordered_def, BAG_EVERY] \\
      Induct_on `l'` \\
      rw[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
      metis_tac[transitive_def, reflexive_def,antisymmetric_def, trichotomous])
  >- (Induct_on `l` \\ rw[is_tree_ordered_def])
QED;

Theorem skew_link_order:
  !geq x t1 t2.
    ((WeakLinearOrder geq) /\
     (is_tree_ordered geq t1) /\
     (is_tree_ordered geq t2)) ==> (is_tree_ordered geq (skew_link geq x t1 t2))
Proof
  ntac 2 strip_tac \\
  ntac 2 Cases \\
  rw[WeakLinearOrder, WeakOrder, skew_link_def, link_def, is_tree_ordered_def, BAG_EVERY, tree_to_bag_def] \\
  fs[root_def, aux_def, children_def, rank_def] \\
  Induct_on `l` \\
  Induct_on `l'` \\
  rw[is_tree_ordered_def, BAG_EVERY, tree_to_bag_def, list_to_bag_def] \\
  fs[tree_to_bag_def, is_tree_ordered_def, BAG_EVERY] \\
  metis_tac[transitive_def, reflexive_def, antisymmetric_def, trichotomous]
QED;

(* Translations *)
val _ = translate root_def;
val _ = translate rank_def;
val _ = translate aux_def;
val _ = translate children_def;
val _ = translate link_def;
val _ = translate skew_link_def;


val _ = export_theory ();
