(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep pair finite_map
Libs
  wordsLib helperLib

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
Definition ann_ft_def:
  ann_ft (FibTree k n xs) =
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

Definition empty_node_def:
  empty_node k v =
    fts_mem [ann_ft $ FibTree k (fill_dnode (FST v) (SND v) F F) []]
End

(*-------------------------------------------------------------------*
   Memory Tests
 *-------------------------------------------------------------------*)

Definition test_build_fts_def:
  (test_build_fts _   (0:num)  edges = []) /\
  (test_build_fts mem (SUC amount) edges =
    (FibTree mem (fill_dnode (mem + 1w) (HD edges) F F)[]
    :: test_build_fts (mem + 100w * bytes_in_word) (amount) (TL edges)))
End

Definition test_build_ft_def:
  test_build_ft mem children edges =
    (FibTree mem (fill_dnode (mem + 1w) (HD edges) F T)
        (test_build_fts (mem + 10w * bytes_in_word) children (TL edges)))
End

Definition test_list_edges_def:
  (test_list_edges _ (0:num) = [])/\
  (test_list_edges mem nodes =
    ((mem,nodes)::(test_list_edges (mem + 8w * bytes_in_word) (nodes - 1))))
End

Definition test_full_conn_def:
  (test_full_conn _ _ (0:num) = []) /\
  (test_full_conn mem nodes count =
    (((mem * 100w * bytes_in_word),test_list_edges mem nodes)
    :: test_full_conn mem nodes (count-1)))
End

val test_fts_mem = “fts_mem (ann_fts [
    FibTree 10w (
    fill_dnode 11w (1000w, [(50w,10)]) T F) [];
    FibTree 50w (
    fill_dnode 51w (2000w, [(10w,50)]) T F) [
        FibTree 100w
        (fill_dnode 101w (3000w, []) T F) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,next_key_def,head_key_def,last_key_def,REVERSE_DEF,ft_seg_def,ones_def,edges_ones_def,LENGTH,b2w_def,fill_anode_def,fill_dnode_def];
(*
val tfc = “test_full_conn (10000w:word64) 3 3” |> SCONV [test_full_conn_def];
*)
val test_large_fts_mem = “fts_mem (ann_fts [
    test_build_ft (1000w:word64) 2 (test_full_conn 10000w 3 3)
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,test_full_conn_def,
    next_key_def,head_key_def,last_key_def,REVERSE_DEF,ft_seg_def,
    ones_def,edges_ones_def,LENGTH,b2w_def,fill_anode_def,fill_dnode_def,
    test_build_ft_def, test_build_fts_def, test_list_edges_def,
    TL_DEF, HD, FST, byteTheory.bytes_in_word_def];

val test =
    “ones 400w [x;y;z;e;r;t;y;u:word64]”
    |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];

(*-------------------------------------------------------------------*
   FibHeap assertion
 *-------------------------------------------------------------------*)

Definition edges_off_def:
  edges_off = 1w * bytes_in_word
End

Definition flag_off_def:
  flag_off = 2w * bytes_in_word
End

Definition mark_off_def:
  mark_off = 3w * bytes_in_word
End

Definition before_off_def:
  before_off = 4w * bytes_in_word
End

Definition next_off_def:
  next_off = 5w * bytes_in_word
End

Definition parent_off_def:
  parent_off = 6w * bytes_in_word
End

Definition child_off_def:
  child_off = 7w * bytes_in_word
End

Definition rank_off_def:
  rank_off = 8w * bytes_in_word
End



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
    ((v <= n.value) /\ (fts_is_min v ts) /\ (fts_is_min v rest)))
End

Definition fib_heap_size_def:
  (fib_heap_size [] = 0:num) /\
  (fib_heap_size (FibTree _ _ ts::rest) = 1 + fib_heap_size ts + fib_heap_size rest)
End

Definition fib_num_def:
  fib_num n:num =
    if n < 2 then
    n
    else
    fib_num(n-1) + fib_num(n-2)
End

(*See paper S_k >= F_{k+2} >= k-decandants *)
Definition fib_heap_shape_ok_def:
  (fib_heap_shape_ok [] = T) /\
  (fib_heap_shape_ok ((FibTree k v ys)::ts) <=>
    (fib_num ((LENGTH ys) + 2) <= 1 + fib_heap_size ys) /\
    fib_heap_shape_ok ys /\
    fib_heap_shape_ok ts)
End


Definition fib_heap_inv_def:
  fib_heap_inv fh (fts: ('a word, 'a node_data) fts) ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\
    (∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
             ? m. fts_has k (fill_dnode v e T m) fts) /\
    (!k v e.
      (FLOOKUP fh k = SOME (v,e)) /\ k = head_key fts ==>
      fts_is_min v fts) /\
    (fib_heap_shape_ok fts)
(*Everything else should be valid by annotation, construction of the heap,
  or is an individual assertion for a heap operation.
*)
End

Definition fib_heap_def:
  fib_heap a fh =
    SEP_EXISTS fts.
      fts_mem (ann_fts fts) *
      cond (fib_heap_inv fh fts /\ a = head_key fts)
End


Definition fib_heap_empty_append_def:
  fib_heap_empty_append (k:'a word, m:'a word -> 'a word, dm:'a word set,c: bool) =
    let c = (k + next_off IN dm /\ c) in
    let m = ((k + next_off) =+ k) m in
    let c = (k + before_off IN dm /\ c) in
    let m = ((k + before_off) =+ k)m in
      (k,m,c)
End

Definition fib_heap_append_def:
  fib_heap_append
    (k1:'a word, k2:'a word, fst:'a word, m:'a word -> 'a word, dm :'a word set, c: bool)
  =
    (*load last elem*)
    let c = (fst + before_off IN dm /\ c) in
    let last = m (fst + before_off) in
    (*load sec elem*)
    let c = (fst + next_off IN dm /\ c) in
    let sec = m (fst + next_off) in
    (*Ensure values in heap *)
    let c = (last + next_off IN dm /\ c) in
    let c = (sec + before_off IN dm /\ c) in
    (*put k1 as fst element and k2 as new last - order important!*)
    if fst = sec then
      (*only one element in the list *)
      let m = ((k1 + next_off) =+ k2) m in
      let m = ((k1 + before_off) =+ k2) m in
      let m = ((k2 + next_off) =+ k1) m in
      let m = ((k2 + before_off) =+ k1) m in
        (k1, m, c)
    else
      let m = ((k2 + before_off) =+ last) m in
      let m = ((k2 + next_off) =+ k1) m in
      let m = ((k1 + before_off) =+ k2) m in
      let m = ((k1 + next_off) =+ sec) m in
      let m = ((sec + before_off) =+ k1) m in
      let m = ((last + next_off) =+ k2) m in
        (k1, m, c)
End

Definition fib_heap_insert_def:
  fib_heap_insert
    (a:'a word, k:'a word, m:'a word -> 'a word, dm :'a word set)
  =
    (* load value at k *)
    let c = (k ∈ dm) in
    let v_of_k = m k in
    let c = (k + flag_off IN dm /\ c) in
    let m = ((k + flag_off) =+ b2w T) m in
    if a = 0w then
        fib_heap_empty_append (k, m, dm, c)
    else
        (* load value at a *)
        let c = (a ∈ dm ∧ c) in
        let v_of_a = m a in
        (* check whether k goes first *)
        if v_of_k <=+ v_of_a then
            fib_heap_append (k, a, a, m, dm, c)
        else
            fib_heap_append (a, k, a, m, dm, c)
End

Theorem lemma_empty_heap:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts = 0w) ==>
      (fts = [] /\ fh = FEMPTY)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs[fib_heap_inv_def] >>
  first_x_assum (qspecl_then [`0w`, `v`, `e`] assume_tac) >> fs[] >>
  Cases_on `FLOOKUP fh 0w` >> full_simp_tac std_ss [] >> gvs[] >>
  first_x_assum (qspec_then `m` assume_tac) >>
  cheat

(*
  Induct_on `fts` >>
  fs[Once fts_has_cases] >>


  Cases_on `fts` >> full_simp_tac std_ss [head_key_def] >>
  rfs[head_key_def] >>
  last_x_assum (qspec_then `ts` assume_tac) >>
  last_x_assum(qspecl_then [`rest`, `ts`] assume_tac) >>





Cases_on `fh` >>

*)
QED




Theorem fib_heap_insert:
  ∀frame k v fh.
    (empty_node k v * fib_heap a fh * frame) (fun2set (m,dm)) ∧
    fib_heap_insert (a, k, m, dm) = (a', m', b) ⇒
    (fib_heap a' (fh |+ (k,v)) * frame) (fun2set (m',dm)) ∧ b
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  simp [fib_heap_insert_def] >>
  fs[empty_node_def, ann_ft_def, fts_mem_def, fill_anode_def,
     fill_dnode_def, head_key_def, last_key_def, ann_fts_seg_def,
     ft_seg_def, ones_def, SEP_CLAUSES, flag_off_def] >>
  SEP_R_TAC >>
  IF_CASES_TAC
  >- (
    `fts = [] /\ fh = FEMPTY` by cheat >>
    gvs[] >>
    fs[fib_heap_empty_append_def,before_off_def, next_off_def] >>
    SEP_R_TAC >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    PairCases_on `v` >>
    rename1 `(a',v,e)` >>
    qexists `[FibTree a' (fill_dnode v e T F) []]` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    gvs[] >>
    fs[fib_heap_inv_def,fib_heap_shape_ok_def,fib_heap_size_def] >>
    simp[Ntimes fib_num_def 3] >>
    simp[Once fib_num_def] >>
(*
    rpt conj_tac >>
    strip_tac >>
    gvs[]
    fs[head_key_def, fts_is_min_def,fill_dnode_def] >>
*)
    cheat)
>> cheat
QED

(*FAPPLY_FUPDATE_THM not working -> not found by hol? *)

