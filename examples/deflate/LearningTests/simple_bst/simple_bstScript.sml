(*
  Example on simple BST
*)

open preamble comparisonTheory;

val _ = new_theory "simple_bst";

Datatype:
  btree = Leaf | Node 'k 'v btree btree
End

Definition singleton_def:
  singleton k v = Node k v Leaf Leaf
End

Definition key_set_def:
  key_set cmp k = { k' | cmp k k' = Equal } (*Either new k or one we previously had?*)
End

Definition lookup_def:
  lookup cmp k Leaf = NONE ∧
  lookup cmp k (Node k' v' l r) =
    case cmp k k' of
    | Less => lookup cmp k l
    | Greater => lookup cmp k r
    | Equal => SOME v'
End

Theorem key_set_equiv:
  ∀cmp.
    good_cmp cmp
    ⇒
    (∀k. k ∈ key_set cmp k) ∧
    (∀k1 k2. k1 ∈ key_set cmp k2 ⇒ k2 ∈ key_set cmp k1) ∧
    (∀k1 k2 k3. k1 ∈ key_set cmp k2 ∧ k2 ∈ key_set cmp k3 ⇒ k1 ∈ key_set cmp k3)
Proof
  rw [key_set_def]
  \\ metis_tac [good_cmp_def]
QED

Theorem key_set_eq:
  ∀cmp k1 k2.
    good_cmp cmp
    ⇒
    (key_set cmp k1 = key_set cmp k2 ⇔ cmp k1 k2 = Equal)
Proof
  rw [key_set_def, EXTENSION]
  \\ metis_tac [good_cmp_def]
QED

Definition to_fmap_def:
  to_fmap cmp Leaf = FEMPTY ∧
  to_fmap cmp (Node k v l r) =
  to_fmap cmp ∪ to_fmap cmp r |+ (key_set cmp k, v)
End

Theorem to_fmap_key_set:
   ∀ks t.
    ks ∈ FDOM (to_fmap cmp t) ⇒ ∃k. ks = key_set cmp k
Proof
   Induct_on `t` >>
   (* EXERCISE: finish this proof *)
   (* hint: the same tactic probably works for both subgoals *)
QED

val _ = export_theory();
