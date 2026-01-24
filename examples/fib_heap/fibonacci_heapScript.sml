(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep
Libs
  wordsLib

(*      s             e
  a -> | | -> ... -> | | <- e
  p <- | | <- ... <- | | -> s *)
Definition double_linked_list_seg_def:
  (dllseg a p [] s e = emp * cond ( p <> 0w /\ a = s /\ e = p )) /\
  (dllseg a p (x::xs) s e =
    SEP_EXISTS b.
      one (a:'a word, x:'a word) *
      one (a + bytes_in_word, p) *
      one (a + 2w * bytes_in_word, b) *
      dllseg b a xs s e)
End

Definition double_linked_list_def:
  (dll s [] = emp * cond (s = 0w)) /\
  (dll s (x::xs) = SEP_EXISTS e a. 
	one (s:'a word, x:'a word) * 
	one (s + bytes_in_word, e) * 
	one (s + 2w * bytes_in_word, a) * 
	dllseg a s xs s e )
End

(* The Fibtree is just a dll. Each key k holds its one tree.
 Key: 
 k |-> v,b,n,_,p,c,rm where
 v = value 				0
 b = element before			1
 n = element next			2
 _ = flag (inside tree)			3
 p = parent				4
 c = children -> again a Fibtree	5
 rm = rank + marked			6
*)
Definition fibonacci_tree_def:
  (Fibtree k [] = one (k:'a + 5w * bytes_in_word, 0w) /\
  (Fibtree k (x::xs) = one (k:'a + 5w * bytes_in_word, x) * Fibtree x xs 
End

Definition fibonacci_heap_def:
  (Fibheap k [] = dll k []) /\
  (Fibheap k list = dll k list)
End
  
