(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep
Libs
  wordsLib

(* The Fibtree is just a dll. Each key k holds its one tree.
 Key: 
 k |-> v,b,n,e,f,p,c,rm where
 v = value 				0
 b = element before			1
 n = element next			2
 e = edges				3
 f = flag (inside tree)			4
 p = parent				5
 c = children -> again a Fibtree	6
 rm = rank + mark			7
*)
Definition value_def:
  value = 0w
End

Definition previous_def:
  previous = bytes_in_word
End

Definition next_def:
  next = 2w * bytes_in_word
End

Definition edges_def:
  edges = 3w * byes_in_word
End

Definition flag_def:
  flag = 4w * bytes_in_word
End

Definition parent_def:
  parent = 5w * bytes_in_word
End

Definition child_def:
  child = 6w * bytes_in_word
End

Definition rank_mark_def:
  rm = 7w * bytes_in_word
End 

(*      s             e
  a -> | | -> ... -> | | -> s
  p <- | | <- ... <- | | <- e *)
(* Definition double_linked_list_seg_def:
  (dllseg a p [] s e = emp * cond ( p <> 0w /\ a = s /\ e = p )) /\
  (dllseg a p (x::xs) s e =
    SEP_EXISTS b.
      one (a:'a word, x:'a word) *
      one (a + bytes_in_word, p) *
      one (a + 2w * bytes_in_word, b) *
      dllseg b a xs s e)
End*)

Definition implicit_dll_seg_def:
  (dllseg a p a p = emp * cond (p <> 0w) /\
  (dllseg a p s e = SEP_EXISTS b.
	one (a + previous, p) *
	one (a + next, b) * 
	dllseg b a s e)
End

(*
Definition double_linked_list_def:
  (dll s [] = emp * cond (s = 0w)) /\
  (dll s (x::xs) = SEP_EXISTS e a. 
	one (s:'a word, x:'a word) * 
	one (s + bytes_in_word, e) * 
	one (s + 2w * bytes_in_word, a) * 
	dllseg a s xs s e )
End
*)

Definition implicit_dll_def:
  (dll 0w = emp) /\
  (dll s = SEP_EXISTS b n.
	one (s:'a word + previous, b) * 
	one (s + next, n) *
	dllseg n s s b
End

(* The Fibtree is just a dll. Each key k holds its one tree.
 Key: 
 k |-> v,b,n,e,f,p,c,rm where
 v = value 				0
 b = element before			1
 n = element next			2
 e = edges				3
 f = flag (inside tree)			4
 p = parent				5
 c = children -> again a Fibtree	6
 rm = rank + mark			7
*)

Definition fibonacci_child_def:
  (FibChild k 0w = \td. emp) /\
  (FibChild k c = \td. SEP_EXISTS cc. one(c:'a word + child, cc) * td c cc)
End

(* FibSib traverses the implicit dll  and terminates on e=k. *)
Definition fibonacci_sib_def:
  (FibSib k k = \td. SEP_EXISTS kc. 
	one(k:'a word + child, kc) * FibChild k kc td) /\
  (FibSib k e = \td. SEP_EXISTS s.
	one(k:'a word + next, s) * FibSib s e td * (*Recursion Siblings*)
	FibSib k k td )(*ks' Children*)
	(* = one(k:'a word + 6w * bytes_in_word, kc) * FibChild k kc td *)
End

(*k is the parent of all other nodes. c is the first child of (possibly) many.*)
Definition fibonacci_tree_def:
  (FibTree k 0w = (FibChild k 0w FibTree)) /\
  (FibTree k c = SEP_EXISTS s. one(c:'a word + next, s) * (FibSib s c FibTree))
End
  
