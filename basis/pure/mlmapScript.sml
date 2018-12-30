(*
  Pure functions for the Map module.

  This file defines a wrapper around the balanced_map type. The new
  type is essentially a pair that carries the compare functions next
  to the tree so that users don't have to provide the compare function
  as an explicit argument everywhere.
*)
open preamble balanced_mapTheory

val _ = new_theory"mlmap"

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

val _ = export_theory()
