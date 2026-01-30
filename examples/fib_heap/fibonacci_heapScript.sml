(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep
Libs
  wordsLib

(*-------------------------------------------------------------------*
   Heading here
 *-------------------------------------------------------------------*)

Datatype:
  ft = FibTree 'k 'v (ft list)
End

(*
Need to provide polymorphic types to ft.
This does not crash with an exception, but there is also no output.
*)
Type fts = “:('k,'v) ft list”;

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

Datatype:
  node_data = <| value : 'a word ;
                 edges : 'a word (* TODO: improve *) ;
                 flag  : bool ;
                 mark  : bool |>
End

Datatype:
  annotated_node_data =
    <| data       : 'a node_data ;
       before_ptr : 'a word ;
       next_ptr   : 'a word ;
       parent_ptr : 'a word ;
       child_ptr  : 'a word ;
       rank       : num |>
End

Definition annotate_def:  (* TODO: needs helper functions *)
  annotate ((FibTree k n ts)    : ('a word, 'a node_data) ft) =
            (FibTree k ARB ARB) : ('a word, 'a annotated_node_data) ft
End

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

Definition ones_def:
  ones a [] = emp ∧
  ones (a:'a word) ((w:'a word)::ws) =
    one (a,w) * ones (a + bytes_in_word) ws
End

val test =
  “ones 400w [x;y;z;e;r;t;y;u:word64]”
  |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];

Definition b2w_def:
  b2w b = if b then 1w else 0w : 'a word
End

Definition fts_in_mem_def:
  fts_in_mem [] = emp ∧
  fts_in_mem (((FibTree k v ts) : ('a word, 'a annotated_node_data) ft) :: rest) =
    ones k [v.data.value;
            v.data.edges;
            b2w v.data.flag;
            n2w v.rank] *
    fts_in_mem ts *
    fts_in_mem rest
End

Datatype:
  fh = FibHeap 'k (('k,'v) ft)
End

Definition FibTree_Mem_def:
  (FibTreeMem (FibTree (k:'a word) (v:'a word) []) = one(k + child, 0w)) /\
  (FibTreeMem (FibTree (k:'a word) (v:'a word) (FibTree h w ys::xs)) =
    one(h + parent, k) * FibTreeMem(FibTree h w ys) *
    FibTreeMem(FibTree k v xs))
End

(*Is there a way to make this definition not use equality with T?*)
Definition FibTree_Min_def:
  (FibTreeMin (m:'a word) [] = T) /\
  (FibTreeMin (m:'a word) (FibTree v k ys::xs) =
    ((m <= v) /\
     (FibTreeMin m xs) /\
     (FibTreeMin m ys)))
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
    one(h, m:'a word) * (FibTreeMem (FibTree h m ys)) *
    (FibHeapRoot (FibTree h m xs)) *
    cond(p = h /\ (FibTreeMin m ys) /\ (FibTreeMin m xs)))
End

val ft_tm = “FibTree (60w:word64) (6w:word64)
               [FibTree (70w:word64) (7w:word64) [];
                FibTree (80w:word64) (8w:word64) []]”;

val test =
  “FibTreeMem ^ft_tm”
  |> SCONV [FibTree_Min_def, FibTree_Mem_def];

(*

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

(* Need to proof termination, but how?*)
(* s+next is not dereferenced -> so this is incorrect?*)
Definition implicit_dll_to_list_def:
  cdll s e = if s = e then
    []
    else
    (s::(cdll (s+next) e))
End

*)
