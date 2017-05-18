(*
  Splay Tree definition, verification, and application.

  Part of an extended worked example on using HOL and CakeML to write verified
  programs, presented as a tutorial on CakeML at PLDI and ICFP in 2017.

  This file defines a datatype for binary search trees, some basic operations
  over it, and then splay tree versions of those operations.
  It also proves functional correctness properties for all these operations.
*)

(*
  A script file begins with a descriptive comment like the above, then opens
  the structures whose contents will be used. When working within the CakeML
  repository, it is usually sufficient to open preamble. Otherwise, one would
  typically open HolKernel boolLib bossLib and Parse (at least). CakeML's
  preamble wrapper includes all of those structures and more.
*)

open preamble

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
*)

val singleton_def = Define`
  singleton k v = Node k v Leaf Leaf`;

val insert_def = Define`
  (insert cmp k v Leaf = singleton k v) ∧
  (insert cmp k v (Node k' v' l r) =
     case cmp k k' of
     | Less => Node k' v' (insert cmp k v l) r
     | Greater => Node k' v' l (insert cmp k v r)
     | Equal => Node k' v l r)`;

val lookup_def = Define`
  (lookup cmp k Leaf = NONE) ∧
  (lookup cmp k (Node k' v' l r) =
     case cmp k k' of
     | Less => lookup cmp k l
     | Greater => lookup cmp k r
     | Equal => SOME v')`;

(* TODO: should this not be on by default?
val () = patternMatchesLib.ENABLE_PMATCH_CASES()
*)

val extract_min_def = Define`
  (extract_min Leaf = NONE) ∧
  (extract_min (Node k v l r) =
   case extract_min l of
   | NONE => SOME (k,v,r)
   | SOME (k',v',r') => SOME (k',v',Node k v l r'))`;

val delete_def = Define`
  (delete cmp k Leaf = Leaf) ∧
  (delete cmp k (Node k' v' l r) =
   case cmp k k' of
   | Less => Node k' v' (delete cmp k l) r
   | Greater => Node k' v' l (delete cmp k r)
   | Equal =>
     case extract_min r of
     | NONE => l
     | SOME (k'',v'',r'') => Node k'' v'' l r'')`;

(*
  Now some basic proofs about these operations.
  We assume good_cmp of about the comparison function cmp.
  DB.find"good_cmp" reveals that this is defined in comparisonTheory
*)


(*
  Now the splay-ing auto-balancing version of the operations.
  Splay trees are designed as mutable data structures, so the pure functional
  implementation here may seem a bit strange: for example, lookup needs to
  return the new modified tree as well as the result.
*)

val _ = export_theory();
