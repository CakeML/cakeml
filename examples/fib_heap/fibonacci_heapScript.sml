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

Definition rank_def:
  (rank [] = 0:num) /\
  (rank (FibTree _ _ ts::xs) = if (1 + rank ts) > (rank xs) then
    1 + rank ts
    else
    rank xs)
End

(*
Annotates a list of FibTrees. The function does two recursive calls for a list of fts = (t:ts).
First, it calls itself for all cs where cs are the child trees of t.
Second, it calls itself for all ts where the parent and starting node of the dll stay the same.

p = parent
s = first element of the list
b = previous element
*)
Definition annotate_fts_def:
  (annotate_fts p s b [] = []) /\
  (annotate_fts p s b ((FibTree k n ys)::xs) =
    ((FibTree k (annotated_node n b (next_key s xs) p (child_key ys) (rank ys))
        (annotate_fts k (next_key 0w ys) (last_key 0w ys) ys))
    ::(annotate_fts p s k xs)))
End

(*
Annotates a single tree that is not part of any list and does not have a parent.
*)
Definition annotate_ft_def:
  annotate_ft (FibTree k n xs) =
    FibTree k (annotated_node n 0w 0w 0w (next_key 0w xs) (rank xs))
        (annotate_fts k (next_key 0w xs) (last_key (next_key 0w xs) xs) xs)
End

(*-------------------------------------------------------------------*
   Heap Mappings (Separation Logic)
 *-------------------------------------------------------------------*)


Definition value_def:
  value = 0w
End

Definition edges_def:
  edges = 1w * bytes_in_word
End

Definition flag_def:
  flag = 2w * bytes_in_word
End

Definition rank_mark_def:
  rm = 3w * bytes_in_word
End

Definition previous_def:
  previous = 4w * bytes_in_word
End

Definition next_def:
  next = 5w * bytes_in_word
End

Definition parent_def:
  parent = 6w * bytes_in_word
End

Definition child_def:
  child = 7w * bytes_in_word
End

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

val test_fts_mem = “fts_mem (annotate_fts 0w 10w 50w [
    FibTree 10w (
    node_data 10w (1000w, [(50w,10)]) true false) [];
    FibTree 50w (
    node_data 50w (2000w, [(10w,50)]) true false) [
        FibTree 100w
        (node_data 100w (3000w, []) true false) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,annotate_fts_def,next_key_def,child_key_def,last_key_def,REVERSE_DEF,ft_seg_def,ones_def,edges_ones_def,rank_def]

val test =
    “ones 400w [x;y;z;e;r;t;y;u:word64]”
    |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];


(*-------------------------------------------------------------------*
   Example Operation: Insert Element
 *-------------------------------------------------------------------*)

Definition head_def:
  (head s [] = s) /\
  (head s xs = HD xs)
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
  dll_insert (FibTree k1 n1 ts1)
             (FibTree new_k new_n new_ts)
             (FibTree k2 n2 ts2)  = (
    upd_sib n1.before_ptr new_k (FibTree k1 n1 ts1), (*next = new*)
    upd_sib k1 k2 (FibTree new_k new_n new_ts), (*insert new*)
    upd_sib new_k n2.next_ptr (FibTree k2 n2 ts2)) (*before = new*)
End

Definition new_min_def:
  new_min (t1, new, t2) tl = [new;t1] ++ tl ++ [t2]
End

Definition old_min_def:
  old_min (FibTree k1 n1 t1, new, FibTree k2 n2 t2) tl =
    if k1 = k2 then
        [FibTree k1 n1 t1;new]
    else
        [FibTree k1 n1 t1;new; FibTree k2 n2 t2] ++ tl
End

(*
Some type error
Definition insert_tree_def:
  (meld (new_t:('a word, 'a annotated_node) ft) ([]:('a word, 'a annotated_node) fts) = [new_t]) /\
  (meld (FibTree new_k new_n new_ts) (FibTree k n ts::xs) =
    if new_n.value < n.value then
        new_min (dll_insert (LAST (FibTree k n ts::xs))
                            (FibTree new_k new_n new_ts)
                            (FibTree k n ts))
                (REVERSE (TL (REVERSE xs)))
    else
        old_min (dll_insert (FibTree k n ts)
                            (FibTree new_k new_n new_ts)
                            (head (FibTree k n ts) xs))
                (TL xs))
End
*)






(*-------------------------------------------------------------------*
   Correctness of Heap Operations
 *-------------------------------------------------------------------*)



(*
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
*)

