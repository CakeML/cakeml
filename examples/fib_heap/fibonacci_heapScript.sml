(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep pair
Libs
  wordsLib

(*-------------------------------------------------------------------*
   Datatypes
 *-------------------------------------------------------------------*)

Datatype:
  ft = FibTree 'k 'v (ft list)
End

Type fts = “:('k,'v) ft list”;

Datatype:
  node_data = <| value : 'a word ;
                 edges : ('a word # ('a word # num) list);
                 flag  : bool ;
                 mark  : bool |>
End

Datatype:
  annotated_node =
    <| data       : 'a node_data ;
       before_ptr : 'a word ;
       next_ptr   : 'a word ;
       parent_ptr : 'a word ;
       child_ptr  : 'a word ;
       rank       : num |>
End

(*-------------------------------------------------------------------*
   Node Annotation
 *-------------------------------------------------------------------*)

(*
Definition annotate_def:  (* TODO: needs helper functions *)
  annotate ((FibTree k n ts)    : ('a word, 'a node_data) ft) =
            (FibTree k ARB ARB) : ('a word, 'a annotated_node_data) ft
End
*)
Definition child_key_def:
  (child_key [] = 0w) /\
  (child_key ((FibTree k _ _)::xs) = k)
End

Definition next_key_def:
  (next_key (s:'a word) [] = s) /\
  (next_key s ((FibTree (k:'a word) (v:'a node_data) ys)::xs) = k)
End

Definition last_key_def:
  last_key i xs = next_key i (REVERSE xs)
End

(*
Annotates a list of FibTrees. The function does two recursive calls for a list of fts = (t:ts).
First, it calls itself for all cs where cs are the child trees of t.
Second, it calls itself for all ts where the parent and starting node of the dll stay the same.

p = parent
s = first element of the list
b = previous element
*)
Definition annotate_fts_seg_def:
  (annotate_fts_seg p s b [] = []) /\
  (annotate_fts_seg p s b ((FibTree k n ys)::xs) =
    ((FibTree k
        (<| data       := n ;
            before_ptr := b ;
            next_ptr   := next_key s xs ;
            parent_ptr := p ;
            child_ptr  := child_key ys ;
            rank       := LENGTH ys |>)
        (annotate_fts_seg k (next_key 0w ys) (last_key 0w ys) ys))
    ::(annotate_fts_seg p s k xs)))
End

Definition annotate_fts_def:
  (annotate_fts ([]:('a word, 'a node_data) fts) = []) /\
  (annotate_fts (FibTree k n ts::xs) =
    annotate_fts_seg 0w k (last_key k xs) (FibTree k n ts::xs))
End

(*
Currently, unused definition.
Annotates a single tree that is not part of any list and does not have a parent.
*)
Definition annotate_ft_def:
  annotate_ft (FibTree k n xs) =
    FibTree k (annotated_node n 0w 0w 0w (next_key 0w xs) (LENGTH xs))
        (annotate_fts_seg k (next_key 0w xs) (last_key (next_key 0w xs) xs) xs)
End

(*-------------------------------------------------------------------*
   Heap Mappings (Separation Logic)
 *-------------------------------------------------------------------*)

Definition ones_def:
  ones a [] = emp ∧
  ones (a:'a word) ((w:'a word)::ws) =
    one (a,w) * ones (a + bytes_in_word) ws
End

Definition b2w_def:
  b2w b = if b then 1w else 0w : 'a word
End

Definition edges_ones_def:
  (edges_ones off [] = one(off,0w)) /\
  (edges_ones off ((ptr,value)::xs) =
    one(off,ptr) * one(off + bytes_in_word,n2w value) * (edges_ones (off + 2w * bytes_in_word) xs))
End

Definition ft_seg_def:
  ft_seg ((FibTree k n _): ('a word, 'a annotated_node) ft) =
    (ones k [n.data.value;
            FST n.data.edges;
            b2w n.data.flag;
            b2w n.data.mark;
            n.before_ptr;
            n.next_ptr;
            n.parent_ptr;
            n.child_ptr;
            n2w n.rank]) *  (edges_ones (FST n.data.edges) (SND n.data.edges))
End

Definition fts_mem_def:
  (fts_mem [] = emp ) /\
  (fts_mem (FibTree k n ts::xs) =
    (ft_seg $ FibTree k n ts) * (fts_mem ts) * (fts_mem xs))
End

(*-------------------------------------------------------------------*
   Memory Tests
 *-------------------------------------------------------------------*)

val test_fts_mem = “fts_mem (annotate_fts [
    FibTree 10w (
    node_data 10w (1000w, [(50w,10)]) true false) [];
    FibTree 50w (
    node_data 50w (2000w, [(10w,50)]) true false) [
        FibTree 100w
        (node_data 100w (3000w, []) true false) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,annotate_fts_def,annotate_fts_seg_def,next_key_def,child_key_def,last_key_def,REVERSE_DEF,ft_seg_def,ones_def,edges_ones_def,LENGTH,b2w_def]

val test =
    “ones 400w [x;y;z;e;r;t;y;u:word64]”
    |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];


(*-------------------------------------------------------------------*
   FTs Operation: Insert Element
 *-------------------------------------------------------------------*)

Definition tail_head_def:
  (tail_head s [] = s) /\
  (tail_head s xs = HD xs)
End

(* Updates a node k with new siblings where
    b = node before k
    n = next node
 *)
Definition upd_sib_def:
  upd_sib b n (FibTree k a ts) = FibTree k (annotated_node a.data b n a.parent_ptr a.child_ptr a.rank) ts
End

(* Inserts a ft new_k between k1 and k2.*)
Definition dll_insert_def:
  dll_insert ((FibTree k1 n1 ts1): ('a word, 'a annotated_node) ft)
             ((FibTree new_k new_n new_ts): ('a word, 'a annotated_node) ft)
             ((FibTree k2 n2 ts2): ('a word, 'a annotated_node) ft)  = (
    upd_sib n1.before_ptr new_k (FibTree k1 n1 ts1), (*next = new*)
    upd_sib k1 k2 (FibTree new_k new_n new_ts), (*insert new*)
    upd_sib new_k n2.next_ptr (FibTree k2 n2 ts2)) (*before = new*)
End

Definition new_min_def:
  new_min (t1, new, t2) tl = [new;t1] ++ tl ++ [t2]
End

Definition get_key_def:
  get_key (FibTree k1 n1 t1) = k1
End

Definition less_than_def:
  less_than (FibTree k1 n1 ts1) (FibTree k2 n2 ts2) = (n1.data.value < n2.data.value)
End

Definition old_min_def:
  old_min (min, new, next) tl =
    if (get_key min) = (get_key next) then
        [min;new]
    else
        [min;new;next] ++ tl
End

Definition add_tree_def:
  (add_tree (new_t:('a word, 'a annotated_node) ft) [] = [new_t]) /\
  (add_tree new_t (t::ts) =
    if less_than new_t t then
        new_min (dll_insert (LAST (t::ts)) new_t t) (REVERSE (TL (REVERSE ts)))
    else
        old_min (dll_insert t new_t (tail_head t ts)) (TL ts))
End

Definition new_node_def:
  new_node v e = (node_data v e T F)
End

(*
Inserts a new node of the graph into the fts.
k = identifier (a pointer)
v = current min value
e = edges (so, a pair of a pointer and a list of the edges of k)
*)
Definition insert_node_def:
  insert_node k v e (heap: ('a word, 'a annotated_node) fts) =
    (add_tree (annotate_ft (FibTree k (new_node v e) [])) heap)
End

(*-------------------------------------------------------------------*
   FTs Operation: Update Element
 *-------------------------------------------------------------------*)



(*-------------------------------------------------------------------*
   Correctness of Heap Operations
 *-------------------------------------------------------------------*)


(*
What we need to prove for 'insert node':
{P} code {Q}
P = heap before operation

- new element
- maybe new heap pointer -> case distinction
- besides that heap unchangeched

Q = heap after operation

*)

(*
What we need to prove for 'update node':
{P} code {Q}
P = heap before operation

- modify node
- cascading cut for nodes -> case distinction
- Induction on the cascading cut operation?

Q = heap after operation
*)

(*
What we need to prove for 'extract minimum':
{P} code {Q}
P = heap before operation

- root list only holds trees with different ranks
- new minimum is the heap pointer

Q = heap after operation
*)
