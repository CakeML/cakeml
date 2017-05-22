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

open preamble comparisonTheory

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

val member_def = Define`
  (member cmp k Leaf ⇔ F) ∧
  (member cmp k (Node k' _ l r) =
    case cmp k k' of
    | Less => member cmp k l
    | Greater => member cmp k r
    | Equal => T)`;

(* TODO: possibly want to leave these definitions out as extension exercises? *)

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

(* -- *)

(*
  Since we are working with an abstract comparison function, different keys (k,
  k') may be considered equivalent (cmp k k' = Equal).
  We will assume good_cmp of about the comparison function cmp.
  Try:
  DB.find"good_cmp";
  which reveals that this is defined in comparisonTheory
*)

val key_set_def = Define`
  key_set cmp k = { k' | cmp k k' = Equal } `;

(*
  TODO: something about equivalence classes
  TODO: something about these proofs
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

val key_set_eq = Q.store_thm ("key_set_eq",
  `∀cmp k1 k2.
    good_cmp cmp
    ⇒
    (key_set cmp k1 = key_set cmp k2 ⇔ cmp k1 k2 = Equal)`,
  rw [key_set_def, EXTENSION] >>
  metis_tac [cmp_thms, key_set_equiv]);

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
   rw [to_fmap_def] >>
   metis_tac []);

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
  CASE_TAC \\ fs[wf_tree_def] \\
  match_mp_tac key_ordered_insert \\ rw[] \\
  metis_tac[good_cmp_def]);

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

val key_ordered_to_fmap = Q.store_thm("key_ordered_to_fmap",
  `good_cmp cmp ⇒
   ∀t k res. key_ordered cmp k t res ⇔
       (∀ks k'. ks ∈ FDOM (to_fmap cmp t) ∧ k' ∈ ks ⇒ cmp k k' = res)`,
  strip_tac \\
  Induct \\
  rw[to_fmap_def] \\
  eq_tac \\ rw[] \\
  metis_tac[IN_key_set,cmp_thms]);

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
  simp[FLOOKUP_UPDATE,FLOOKUP_FUNION] \\
  imp_res_tac wf_tree_Node_imp \\
  fs[wf_tree_def,key_set_eq] \\
  simp[FLOOKUP_DEF] \\
  every_case_tac \\ fs[] \\
  metis_tac[cmp_thms] );

val member_lookup = Q.store_thm("member_lookup",
  `∀t k. member cmp k t ⇔ IS_SOME (lookup cmp k t)`,
  Induct \\ rw[member_def,lookup_def] \\
  CASE_TAC \\ rw[]);

val member_to_fmap = Q.store_thm("member_to_fmap",
  `good_cmp cmp ∧ wf_tree cmp t ⇒
   (member cmp k t ⇔ key_set cmp k ∈ FDOM (to_fmap cmp t))`,
  (* TODO: this would make a good exercise, hint: one line proof *)
  rw[member_lookup,lookup_to_fmap,FLOOKUP_DEF]);

(*
val key_ordered_extract_min = Q.store_thm("key_ordered_extract_min",
  `∀t k v t'. extract_min t = SOME (k,v,t')

val wf_tree_extract_min = Q.store_thm("wf_tree_extract_min",
  `∀t k v t'. wf_tree cmp t ∧ extract_min t = SOME (k,v,t') ⇒
              key_ordered cmp k t' Less ∧ wf_tree cmp t'`,
  Induct \\
  rw[extract_min_def] \\
  every_case_tac \\ fs[] \\ rw[] \\ rfs[]
  key_ordered_def

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
