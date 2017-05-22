(*
  Splay Tree definition, verification, and application.

  Part of an extended worked example on using HOL and CakeML to write verified
  programs, presented as a tutorial on CakeML at PLDI and ICFP in 2017.

  This file defines a datatype for binary search trees, some basic operations
  over it, and then splay tree versions of those operations.
  It also proves functional correctness properties for all these operations.

  TODO: maybe this should just be for basic binary trees (no splaying, no
  balancing, etc.), then one can switch to the balanced_bst example from HOL
  for balancing, then a separate new copy for splaying which has the new ideas
  in it like keeping track of the size and how balanced it is?
*)

(*
  A script file begins with a descriptive comment like the above, then opens
  the structures whose contents will be used. When working within the CakeML
  repository, it is usually sufficient to open preamble. Otherwise, one would
  typically open HolKernel boolLib bossLib and Parse (at least). CakeML's
  preamble wrapper includes all of those structures and more.
*)

open preamble
(* TODO: should this not be by default? or done in preamble? *)
val _ = ParseExtras.temp_tight_equality();
(* -- *)

(*
  Create the logical theory in which we will work. Its name should match the name
  of this file, before the "Script.sml" suffix.
*)

val _ = new_theory "splaytree";

(*
  Define the binary tree type.
  It is polymorphic with two type variables, 'k for the key type and 'v for the
  value type.
*)

val _ = Datatype`
  btree = Leaf | Node 'k 'v btree btree`;

(*
Try, for example
type_of ``Node``;
*)

(*
  Now we define basic binary search tree operations (without splaying).

  The operations are parameterised by a comparison function on the tree data,
  which is of type 'a -> 'a -> cpn. The cpn type is an enumeration of three
  constructors: Less, Equal, Greater; it is predefined in totoTheory (included
  within preamble).

  Try, for example
  TypeBase.constructors_of``:cpn``;
*)

val singleton_def = Define`
  singleton k v = Node k v Leaf Leaf`;

val insert_def = Define`
  insert cmp k v Leaf = singleton k v ∧
  insert cmp k v (Node k' v' l r) =
    case cmp k k' of
    | Less => Node k' v' (insert cmp k v l) r
    | Greater => Node k' v' l (insert cmp k v r)
    | Equal => Node k' v l r`;

val lookup_def = Define`
  lookup cmp k Leaf = NONE ∧
  lookup cmp k (Node k' v' l r) =
    case cmp k k' of
    | Less => lookup cmp k l
    | Greater => lookup cmp k r
    | Equal => SOME v'`;

val extract_min_def = Define`
  extract_min Leaf = NONE ∧
  extract_min (Node k v l r) =
    case extract_min l of
    | NONE => SOME (k,v,r)
    | SOME (k',v',r') => SOME (k',v',Node k v l r')`;

val delete_def = Define`
  delete cmp k Leaf = Leaf ∧
  delete cmp k (Node k' v' l r) =
    case cmp k k' of
    | Less => Node k' v' (delete cmp k l) r
    | Greater => Node k' v' l (delete cmp k r)
    | Equal =>
      case extract_min r of
      | NONE => l
      | SOME (k'',v'',r'') => Node k'' v'' l r''`;

(*
  Since we are working with an abstract comparison function, different keys (k,
  k') may be considered equivalent (cmp k k' = Equal).
  We will assume good_cmp of about the comparison function cmp.
  Try:
  DB.find"good_cmp";
  which reveals that this is defined in comparisonTheory
  TODO: something about equivalence classes
*)

val key_set_def = Define`
  key_set cmp k = { k' | cmp k k' = Equal } `;

(*
  Now let us define the (abstract) finite map from key-equivalence-classes to
  values, obtained by considering every (key,value) pair in a tree. This is the
  standard against which we can verify correctness of the operations.
*)

val to_fmap_def = Define`
  to_fmap cmp Leaf = FEMPTY ∧
  to_fmap cmp (Node k v l r) =
  to_fmap cmp l ⊌ to_fmap cmp r |+ (key_set cmp k, v)`;

(*
  Now some proofs about the basic tree operations.
*)


(*
  We start by defining what a predicate on trees indicating
  whether they have the binary search tree property
*)
val key_ordered_def = Define`
  (key_ordered cmp k Leaf res ⇔ T) ∧
  (key_ordered cmp k (Node k' _ l r) res ⇔
   cmp k k' = res ∧
   key_ordered cmp k l res ∧
   key_ordered cmp k r res)`;
val _ = export_rewrites["key_ordered_def"];
(* TODO: explain export_rewrites and why we use it here *)

val wf_tree_def = Define`
  (wf_tree cmp Leaf ⇔ T) ∧
  (wf_tree cmp (Node k _ l r) ⇔
   key_ordered cmp k l Greater ∧
   key_ordered cmp k r Less ∧
   wf_tree cmp l ∧
   wf_tree cmp r)`;
val _ = export_rewrites["wf_tree_def"];

(*
  We can prove that all the operations preserve wf_tree

  For pedagogy, the aim here is to prove:
    - wf_tree_singleton
    - wf_tree_insert
    - wf_tree_delete
  Figuring out the lemmas required along the way
  should probably be part of the exercise
*)

(* TODO: explain why store_thm takes a string. explain the [simp] annotation *)

val wf_tree_singleton = Q.store_thm("wf_tree_singleton[simp]",
  `wf_tree cmp (singleton k v)`, EVAL_TAC);

val key_ordered_singleton = Q.store_thm("key_ordered_singleton[simp]",
  `cmp k k' = res ⇒
   key_ordered cmp k (singleton k' v') res`, EVAL_TAC);

val key_ordered_insert = Q.store_thm("key_ordered_insert[simp]",
  `∀t.
   key_ordered cmp k t res ∧ cmp k k' = res ⇒
   key_ordered cmp k (insert cmp k' v' t) res`,
  Induct \\ rw[insert_def] \\
  CASE_TAC \\ fs[]);

val wf_tree_insert = Q.store_thm("wf_tree_insert[simp]",
  `good_cmp cmp ⇒
   ∀t k v. wf_tree cmp t ⇒ wf_tree cmp (insert cmp k v t)`,
  strip_tac \\
  Induct \\
  rw[insert_def] \\
  CASE_TAC \\ fs[] \\
  match_mp_tac key_ordered_insert \\ rw[] \\
  metis_tac[comparisonTheory.good_cmp_def]);

(*
val wf_tree_delete = Q.store_thm("wf_tree_delete",
);
*)

(*
  Now the splay-ing auto-balancing version of the operations.
  Splay trees are designed as mutable data structures, so the pure functional
  implementation here may seem a bit strange: for example, lookup needs to
  return the new modified tree as well as the result.
*)

val _ = export_theory();
