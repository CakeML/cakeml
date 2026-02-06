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
Definition head_key_def:
  (head_key [] = 0w) /\
  (head_key ((FibTree k _ _)::xs) = k)
End

Definition next_key_def:
  (next_key (s:'a word) [] = s) /\
  (next_key s ((FibTree (k:'a word) (v:'a node_data) ys)::xs) = k)
End

Definition last_key_def:
  last_key xs = head_key (REVERSE xs)
End

Definition fill_dnode_def:
  fill_dnode v e f m =
    <|  value := v;
        edges := e;
        flag  := f;
        mark  := m |>
End

Definition fill_anode_def:
  fill_anode d b n p c r =
    <|  data        := d;
        before_ptr  := b;
        next_ptr    := n;
        parent_ptr  := p;
        child_ptr   := c;
        rank        := r |>
End

(*
Annotates a list of FibTrees. The function does two recursive calls for a list of fts = (t:ts).
First, it calls itself for all cs where cs are the child trees of t.
Second, it calls itself for all ts where the parent and starting node of the dll stay the same.

p = parent
s = first element of the list
b = previous element
*)
Definition ann_fts_seg_def:
  (ann_fts_seg p s b [] = []) /\
  (ann_fts_seg p s b ((FibTree k n ys)::xs) =
    (FibTree k
        (fill_anode n b (next_key s xs) p (head_key ys) (LENGTH ys))
        (ann_fts_seg k (head_key ys) (last_key ys) ys)
    ::(ann_fts_seg p s k xs)))
End

Definition ann_fts_def:
  ann_fts fts =
    ann_fts_seg 0w (head_key fts) (last_key fts) fts
End

(*
Currently, unused definition.
Annotates a single tree that is not part of any list and does not have a parent.
*)
Definition annotate_ft_def:
  annotate_ft (FibTree k n xs) =
    FibTree k (fill_anode n 0w 0w 0w (head_key xs) (LENGTH xs))
        (ann_fts_seg k (head_key xs) (last_key xs) xs)
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
    ones off [ptr; n2w value] *
    edges_ones (off + 2w * bytes_in_word) xs)
End

Definition ft_seg_def:
  ft_seg ((FibTree k n _): ('a word, 'a annotated_node) ft) =
    ones k [n.data.value;
            FST n.data.edges;
            b2w n.data.flag;
            b2w n.data.mark;
            n.before_ptr;
            n.next_ptr;
            n.parent_ptr;
            n.child_ptr;
            n2w n.rank] *
    edges_ones (FST n.data.edges) (SND n.data.edges)
End

Definition fts_mem_def:
  (fts_mem [] = emp ) /\
  (fts_mem (FibTree k n ts::xs) =
    (ft_seg $ FibTree k n ts) * (fts_mem ts) * (fts_mem xs))
End

(*-------------------------------------------------------------------*
   Memory Tests
 *-------------------------------------------------------------------*)

val test_fts_mem = “fts_mem (ann_fts [
    FibTree 10w (
    fill_dnode 11w (1000w, [(50w,10)]) true false) [];
    FibTree 50w (
    fill_dnode 51w (2000w, [(10w,50)]) true false) [
        FibTree 100w
        (fill_dnode 101w (3000w, []) true false) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,next_key_def,head_key_def,last_key_def,REVERSE_DEF,ft_seg_def,ones_def,edges_ones_def,LENGTH,b2w_def]

val test =
    “ones 400w [x;y;z;e;r;t;y;u:word64]”
    |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];

(*-------------------------------------------------------------------*
   FibHeap assertion
 *-------------------------------------------------------------------*)

Type fib_heap = “: 'a word |-> 'a word # ('a word # ('a word # num) list) ”;

Inductive fts_has:
[~first:]
  fts_has k v (FibTree k v ts :: rest)
[~rest:]
  fts_has k v rest ⇒
  fts_has k v (FibTree k1 v1 ts :: rest)
[~child:]
  fts_has k v ts ⇒
  fts_has k v (FibTree k1 v1 ts :: rest)
End

Definition fts_min_def:
  fts_min_value fts = head_key fts
End

Definition fts_is_min_def:
  (fts_is_min _ [] = T) /\
  (fts_is_min v (FibTree _ n ts::rest) =
    ((v <= n.data.value) /\ (fts_is_min v ts) /\ (fts_is_min v rest)))
End

Definition fib_heap_inv_def:
  fib_heap_inv fh fts ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\ (*k is null*)
    (∀k v. FLOOKUP fh k = SOME v ⇔ ?b n p c r m. fts_has k
        (fill_anode (fill_dnode (FST v) (SND v) T m) b n p c r) fts) /\
        (*sem. equiv. of fh and fts*)
    (!k. FLOOKUP fh k = NONE <=> fts = []) /\ (*empty heap*)
    (!k v. (FLOOKUP fh k = SOME v) /\ k = head_key fts
        ==> fts_is_min (FST v) fts) (*min element*)
    (* TODO: more *)
End

Definition fib_heap_def:
  fib_heap a fh =
    SEP_EXISTS fts.
      fts_mem fts *
      cond (fib_heap_inv fh fts /\ a = head_key fts)
End

Definition fib_heap_append_def:
  fib_heap_append
    (k1:'a word, k2:'a word, m:'a word -> 'a word, dm :'a word set)
  =
    (k1, m, T)
End

Definition fib_heap_insert_def:
  fib_heap_insert
    (a:'a word, k:'a word, m:'a word -> 'a word, dm :'a word set)
  =
    (* load value at k *)
    let c = (k ∈ dm) in
    let v_of_k = m k in
    (* load value at a *)
    let c = (a ∈ dm ∧ c) in
    let v_of_a = m a in
      (* check whether k goes first *)
      if v_of_k <=+ v_of_a then
        fib_heap_append (k, a, m, dm)
      else
        fib_heap_append (a, k, m, dm)
End

Theorem fib_heap_insert:
  ∀frame k v fh.
    (empty_node k v * fib_heap a fh * frame) (fun2set (m,dm)) ∧
    fib_heap_insert (a, k, m, dm) = (a', m', b) ⇒
    (fib_heap a' (fh |+ (k,v)) * frame) (fun2set (m',dm)) ∧ b
Proof
  cheat
QED

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
