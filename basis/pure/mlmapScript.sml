(*
  Pure functions for the Map module.

  This file defines a wrapper around the balanced_map type. The new
  type is essentially a pair that carries the compare functions next
  to the tree so that users don't have to provide the compare function
  as an explicit argument everywhere.
*)
open preamble balanced_mapTheory

val _ = set_grammar_ancestry ["balanced_map"];
val _ = ParseExtras.tight_equality();

val _ = new_theory"mlmap"

(* implementation definitions *)

val _ = Datatype `
  map = Map ('a -> 'a -> ordering) (('a, 'b) balanced_map)`;

val lookup_def = Define `
  lookup (Map cmp t) k = balanced_map$lookup cmp k t`

val insert_def = Define `
  insert (Map cmp t) k v = Map cmp (balanced_map$insert cmp k v t)`

val delete_def = Define `
  delete (Map cmp t) k = Map cmp (balanced_map$delete cmp k t)`

val null_def = Define `
  null (Map cmp t) = balanced_map$null t`

val empty_def = Define `
  empty cmp = Map cmp balanced_map$empty`

val union_def = Define `
  union (Map cmp t1) (Map _ t2) = Map cmp (balanced_map$union cmp t1 t2)`

val foldrWithKey_def = Define `
  foldrWithKey f x (Map cmp t) = balanced_map$foldrWithKey f x t`;

val map_def = Define `
  map f (Map cmp t) = Map cmp (balanced_map$map f t)`;

val toAscList_def = Define `
  toAscList (Map cmp t) = balanced_map$toAscList t`;

val fromList_def = Define `
  fromList cmp l = Map cmp (balanced_map$fromList cmp l)`;

val isSubmapBy_def = Define `
  isSubmapBy f (Map cmp t1) (Map _ t2) = balanced_map$isSubmapOfBy cmp f t1 t2`

val isSubmap_def = Define `
  isSubmap m1 m2 = isSubmapBy (=) m1 m2`;

(* definitions for proofs *)

val map_ok_def = Define `
  map_ok (Map cmp t) <=> balanced_map$invariant cmp t /\ good_cmp cmp /\ TotOrd cmp`;

val cmp_of_def = Define `
  cmp_of (Map cmp t) = cmp`;

(* theorems *)

Theorem lookup_insert
  `map_ok t ==>
   lookup (insert t k1 v) k2 = if k1 = k2 then SOME v else lookup t k2`
 (Cases_on `t`
  \\ fs [map_ok_def,balanced_mapTheory.lookup_insert,lookup_def,insert_def]
  \\ metis_tac [totoTheory.TotOrd])

val to_fmap_def = Define `
  to_fmap (Map cmp Tip) = FEMPTY /\
  to_fmap (Map cmp (Bin s k v l r)) =
    ((to_fmap (Map cmp l) ⊌ to_fmap (Map cmp r)) |+ (k,v))`;

Theorem cmp_of_insert[simp]
  `cmp_of (insert t k v) = cmp_of t`
  (Cases_on `t` \\ fs [insert_def,cmp_of_def]);

Theorem cmp_of_empty[simp]
  `cmp_of (empty cmp) = cmp`
  (fs [empty_def,cmp_of_def]);

Theorem insert_thm
  `map_ok t ==>
   map_ok (insert t k v) /\
   to_fmap (insert t k v) = (to_fmap t |+ (k, v))`
  cheat;

Theorem empty_thm
  `(map_ok (empty cmp) = TotOrd cmp) /\ to_fmap (empty cmp) = FEMPTY`
  (fs [empty_def,map_ok_def,balanced_mapTheory.empty_thm,
      to_fmap_def,balanced_mapTheory.empty_def] \\ cheat)

Theorem MAP_FST_toAscList
  `map_ok t ⇒
   SORTED (λx y. cmp_of t x y = Less) (MAP FST (toAscList t)) ∧
   FDOM (to_fmap t) = set (MAP FST (toAscList t))`
  cheat;

Theorem MEM_toAscList
  `map_ok t /\ MEM (k,v) (toAscList t) ==> FLOOKUP (to_fmap t) k = SOME v`
  cheat;

Theorem lookup_thm
  `map_ok t ==> lookup t k = FLOOKUP (to_fmap t) k`
  cheat;

val _ = export_theory()
