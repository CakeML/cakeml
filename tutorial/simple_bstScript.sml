(*
  Simple binary search tree.

  This file defines a datatype for binary search trees, plus insert and lookup
  operations It then proves functional correctness of these operations.

  It is a simplified version of the balanced binary tree example found in
  $HOLDIR/examples/balanced_bst
*)

(*
  A script file begins with a descriptive comment like the above, then opens
  the structures whose contents will be used. When working within the CakeML
  repository, it is usually sufficient to open preamble. Otherwise, one would
  typically open HolKernel boolLib bossLib and Parse (at least). CakeML's
  preamble wrapper includes all of those structures and more.
*)

open preamble comparisonTheory

(*
  Create the logical theory in which we will work. Its name should match the name
  of this file, before the "Script.sml" suffix.
*)

val _ = new_theory "simple_bst";

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
  Now we define some basic binary search tree operations.

  The operations are parameterised by a comparison function on the tree data,
  which is of type 'a -> 'a -> cpn. The cpn type is an enumeration of three
  constructors: Less, Equal, Greater; it is predefined in totoTheory (included
  within preamble).

  Try, for example
  TypeBase.constructors_of``:cpn``;
*)

val singleton_def = Define`
  singleton k v = Node k v Leaf Leaf`;

val lookup_def = Define`
  lookup cmp k Leaf = NONE ∧
  lookup cmp k (Node k' v' l r) =
    case cmp k k' of
    | Less => lookup cmp k l
    | Greater => lookup cmp k r
    | Equal => SOME v'`;

val insert_def =
(* EXERCISE: fill in your definition here *)

(*
  Since we are working with an abstract comparison function, different keys (k,
  k') may be considered equivalent (cmp k k' = Equal).
  We will assume good_cmp of the comparison function cmp.
  Try:
  DB.find"good_cmp";
  which reveals that this is defined in comparisonTheory
*)

val key_set_def = Define`
  key_set cmp k = { k' | cmp k k' = Equal } `;

(*
  For a good comparison function cmp, the key_set cmp relation should be an
  equivalence relation (reflexive, symmetric, and transitive): this is because
  key_set cmp k is supposed to be the set of keys equivalent to k under cmp.
  Let's prove this.
*)

val key_set_equiv = Q.store_thm ("key_set_equiv",
  `∀cmp.
    good_cmp cmp
    ⇒
    (∀k. k ∈ key_set cmp k) ∧
    (∀k1 k2. k1 ∈ key_set cmp k2 ⇒ k2 ∈ key_set cmp k1) ∧
    (∀k1 k2 k3. k1 ∈ key_set cmp k2 ∧ k2 ∈ key_set cmp k3 ⇒ k1 ∈ key_set cmp k3)`,
  rw [key_set_def] >>
  metis_tac [good_cmp_def]);

(* A corollary of this: if two keys have the same key_set, they must be
   equivalent *)

val key_set_eq = Q.store_thm ("key_set_eq",
  `∀cmp k1 k2.
    good_cmp cmp
    ⇒
    (key_set cmp k1 = key_set cmp k2 ⇔ cmp k1 k2 = Equal)`,
  (* EXERCISE: prove this *)
  (* hint: consider the tactics used above *)
  (* hint: remember DB.match and DB.find to find useful theorems *)
  (* hint: set extensionality theorem is called EXTENSION *)

);

(* A helper theorem, expanding out the definition of key_set, for use with
   metis_tac later. *)
val IN_key_set = save_thm("IN_key_set",
  ``k' ∈ key_set cmp k`` |> SIMP_CONV (srw_ss()) [key_set_def]);

(*
  Now let us define the (abstract) finite map from key-equivalence-classes to
  values, obtained by considering every (key,value) pair in a tree. This is the
  standard against which we can verify correctness of the operations.
*)

val to_fmap_def = Define`
  to_fmap cmp Leaf = FEMPTY ∧
  to_fmap cmp (Node k v l r) =
  to_fmap cmp l ⊌ to_fmap cmp r |+ (key_set cmp k, v)`;

val to_fmap_key_set = Q.store_thm ("to_fmap_key_set",
  `∀ks t.
    ks ∈ FDOM (to_fmap cmp t) ⇒ ∃k. ks = key_set cmp k`,
   Induct_on `t` >>
   (* EXERCISE: finish this proof *)
   (* hint: the same tactic probably works for both subgoals *)
);

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

(* We make this definition an automatic rewrite, so it is expanded
   automatically by simplification tactics (such as rw, fs, and simp) *)
val _ = export_rewrites["key_ordered_def"];

val wf_tree_def = Define`
  (wf_tree cmp Leaf ⇔ T) ∧
  (wf_tree cmp (Node k _ l r) ⇔
   key_ordered cmp k l Greater ∧
   key_ordered cmp k r Less ∧
   wf_tree cmp l ∧
   wf_tree cmp r)`;

(*
  We can prove that all the operations preserve wf_tree

  The aim here is to prove:
    - wf_tree_singleton
    - wf_tree_insert
  Figuring out the lemmas required along the way
  should probably be part of the exercise
*)


val wf_tree_singleton = Q.store_thm("wf_tree_singleton[simp]",
  `wf_tree cmp (singleton k v)`, EVAL_TAC);

(* The [simp] annotation above is equivalent to calling
   export_rewrites["wf_tree_singleton"] after storing this theorem. *)

val key_ordered_singleton = Q.store_thm("key_ordered_singleton[simp]",
  (* EXERCISE: you might want to prove a lemma about key_ordered and singleton *)
  (* skip ahead to wf_tree_insert first *)


val key_ordered_insert = Q.store_thm("key_ordered_insert[simp]",
(* `∀t. ????? ⇒ *)
         key_ordered cmp k (insert cmp k' v' t) res`,
  (* EXERCISE: you might want to prove a lemma about key_ordered and insert *)
  (* skip ahead to wf_tree_insert first *)
  (* hint: this lemma might need induction *)
);

val wf_tree_insert = Q.store_thm("wf_tree_insert[simp]",
  `good_cmp cmp ⇒
   ∀t k v. wf_tree cmp t ⇒ wf_tree cmp (insert cmp k v t)`,
  strip_tac \\
  Induct \\
  rw[insert_def] \\
  CASE_TAC \\ fs[wf_tree_def] \\
  (* EXERCISE: fill in the rest of the proof *)
  (* hint: you might want to prove the key_ordered_insert lemma above at this point
     then you can continue with:
    match_mp_tac key_ordered_insert
    ( or: match_mp_tac (MP_CANON key_ordered_insert) )*)

);

(*
  Correctness of lookup
*)

val key_ordered_to_fmap = Q.store_thm("key_ordered_to_fmap",
  `good_cmp cmp ⇒
   ∀t k res. key_ordered cmp k t res ⇔
       (∀ks k'. ks ∈ FDOM (to_fmap cmp t) ∧ k' ∈ ks ⇒ cmp k k' = res)`,
  strip_tac \\
  Induct \\
  rw[to_fmap_def] \\
  eq_tac \\ rw[] \\
  metis_tac[IN_key_set,cmp_thms]);

val wf_tree_Node_imp = Q.store_thm("wf_tree_Node_imp",
  `good_cmp cmp ∧
   wf_tree cmp (Node k v l r) ⇒
   DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) ∧
   (∀x. key_set cmp x ∈ FDOM (to_fmap cmp l) ⇒ cmp k x = Greater) ∧
   (∀x. key_set cmp x ∈ FDOM (to_fmap cmp r) ⇒ cmp k x = Less)`,
  rw[IN_DISJOINT,wf_tree_def] \\
  spose_not_then strip_assume_tac \\
  imp_res_tac to_fmap_key_set \\
  imp_res_tac key_ordered_to_fmap \\
  metis_tac[cmp_thms,IN_key_set]);

val lookup_to_fmap = Q.store_thm("lookup_to_fmap",
  `good_cmp cmp ⇒
   ∀t k. wf_tree cmp t ⇒
     lookup cmp k t = FLOOKUP (to_fmap cmp t) (key_set cmp k)`,
  strip_tac \\
  Induct \\
  rw[lookup_def,to_fmap_def] \\
  fs[] \\
  (*
    Try, for example,
    DB.match[] ``FLOOKUP (_ |+ _)``;
    DB.match[] ``FLOOKUP (_ ⊌ _)``;
  *)
  (* EXERCISE: fill in the rest of this proof *)

);

val _ = export_theory();
