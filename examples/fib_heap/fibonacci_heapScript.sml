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
 v = value                          0
 b = element before                 1
 n = element next                   2
 e = edges                          3
 f = flag (inside tree)             4
 p = parent                         5
 c = children -> again a Fibtree    6
 rm = rank + mark                   7
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
  edges = 3w * bytes_in_word
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

Datatype:
  ft = FibTree 'k 'v (ft list)
End

(*
Need to provide polymorphic types to ft.
This does not crash with an exception, but there is also no output.
*)
Type fts = ``:('k,'v)ft list``;

Definition FibTree_Mem_def:
  (FibTreeMem (FibTree (k:'a word) (v:'a word) []) = one(k + child, 0w)) /\
  (FibTreeMem (FibTree (k:'a word) (v:'a word) (FibTree h w ys::xs)) =
    one(h + parent, k) * FibTreeMem(FibTree h w ys) *
    FibTreeMem(FibTree k v xs))
End

Definition FibTree_Min_def:
  (FibTreeMin (FibTree(k:'a word) (v:'a word) list) = v)
End


Datatype:
  fh = FibHeap 'k (('k,'v) ft)
End

Definition FibHeap_Root_def:
  (FibHeapRoot (FibTree (k:'a word) (v:'a word) []) = emp) /\
  (FibHeapRoot (FibTree (k:'a word) (v:'a word) (FibTree h w ys::xs)) =
    one(k + next, h) * (FibTreeMem (FibTree h w ys)) *
    (FibHeapRoot (FibTree h w xs)))
End

Definition FibHeap_Mem_def:
  (FibHeapMem (p:'a word) [] = emp * cond (p = 0w)) /\
  (FibHeapMem (p:'a word) (FibTree h m ys::xs) =
    cond(p = h) * one(h, m:'a word) * (FibTreeMem (FibTree h m ys)) *
    (FibHeapRoot (FibTree h m xs)))
End

Definition FibHeap_Min_def:
  (FibHeapMin (p:'a word) [] = 0w) /\
  (FibHeapMin (p:'a word) (x::xs) = FibTreeMin x)
End

(* Double Linked List:
        s             e
  a -> | | -> ... -> | | -> s
  p <- | | <- ... <- | | <- e *)
Definition dll_seg_def:
  (dllseg a p [] s e = emp * cond (p <> 0w /\ a = s /\ e = p)) /\
  (dllseg a p (x::xs) s e = SEP_EXISTS b.
    one (a + value, x) *
    one (a + previous, p) *
    one (a + next, b) *
    dllseg b a xs s e)
End

Definition dll_def:
  (dll s []  = emp * cond (s = 0w)) /\
  (dll s (x::xs) = SEP_EXISTS b n.
    one (s + value, x)
    one (s + previous, b) *
    one (s + next, n) *
    dllseg n s xs s b)
End


