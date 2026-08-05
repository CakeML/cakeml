(*
  Pure functions for the Set module.
  This file defines a wrapper around the balanced_map type.
*)
Theory mlset
Ancestors
  balanced_map
Libs
  preamble

(* The type :set would collide with :pred_set$set *)
Datatype:
  mlset = Set ('a -> 'a -> ordering) (('a,unit) balanced_map)
End

Definition empty_def:
  empty cmp = Set cmp balanced_map$empty
End

Definition singleton_def:
  singleton cmp x = Set cmp (balanced_map$singleton x ())
End

Definition member_def:
  member x (Set cmp s) = balanced_map$member cmp x s
End

Definition insert_def:
  insert x (Set cmp s) = Set cmp (balanced_map$insert cmp x () s)
End

Definition delete_def:
  delete x (Set cmp s) = Set cmp (balanced_map$delete cmp x s)
End

Definition union_def:
  union (Set cmp s) (Set _ t) = Set cmp (balanced_map$union cmp s t)
End

Definition isSubset_def:
  isSubset (Set cmp s) (Set _ t) = balanced_map$isSubmapOf cmp s t
End

Definition compare_def:
  compare (Set cmp s) (Set _ t) = balanced_map$compare cmp (\x y. Equal) s t
End

Definition all_def:
  all f (Set cmp s) = balanced_map$every (\k _. f k) s
End

Definition exists_def:
  exists f (Set cmp s) = balanced_map$exists (\k _. f k) s
End

Definition translate_def:
  translate f cmp (Set _ s) =
    Set cmp (balanced_map$foldrWithKey
              (\k _ t. balanced_map$insert cmp (f k) () t)
              balanced_map$empty s)
End

Definition map_def:
  map f (Set cmp s) = translate f cmp (Set cmp s)
End

Definition filter_def:
  filter f (Set cmp s) = Set cmp (balanced_map$filterWithKey (\k (). f k) s)
End

Definition fromList_def:
  fromList cmp xs =
    Set cmp (FOLDL (\t k. balanced_map$insert cmp k () t)
                   balanced_map$empty xs)
End

Definition null_def:
  null (Set cmp s) = balanced_map$null s
End

Definition size_def:
  size (Set cmp s) = balanced_map$size s
End

Definition toList_def:
  toList (Set cmp s) = balanced_map$foldrWithKey (\k _ xs. k::xs) [] s
End

Definition fold_def:
  fold f e (Set cmp s) = balanced_map$foldrWithKey (\k _ t. f k t) e s
End

