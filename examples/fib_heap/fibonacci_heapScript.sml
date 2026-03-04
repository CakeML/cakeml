(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list set_sep pair finite_map combin
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
                 mark  : bool |>
End

val node_data_component_equality = fetch "-" "node_data_component_equality";


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
(*[simp] *)
Definition head_key_def:
  (head_key [] = 0w) /\
  (head_key ((FibTree k _ _)::xs) = k)
End

Theorem head_key_append_thm:
  !xs ys. xs <> [] ==> head_key (xs ++ ys) = head_key (xs)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[] >>
  Cases_on `h` >> simp[head_key_def]
QED

Definition next_key_def:
  (next_key (s:'a word) [] = s) /\
  (next_key s xs = head_key xs)
End

Theorem next_key_append_thm:
  !s xs ys. xs <> [] ==> next_key s (xs ++ ys) = next_key s xs
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[] >>
  Cases_on `h` >> simp[next_key_def,head_key_def]
QED


Theorem next_key_pull_last_thm:
  !xs xk xv xts d.
    next_key d (xs ++ [FibTree xk xv xts]) = next_key xk xs
Proof
  Cases_on `xs` >> simp[next_key_def,head_key_def] >>
  Cases_on `h` >> simp[head_key_def]
QED



Definition last_key_t_def:
  (last_key_t d [] = d) /\
  (last_key_t d xs = head_key (REVERSE xs))
End

Theorem last_key_t_append_thm:
  !xs ys d. ys <> [] ==> last_key_t d (xs ++ ys) = last_key_t d ys
Proof
  rpt strip_tac >>
  Cases_on `ys` using SNOC_CASES >> fs[] >>
  Cases_on `x` >> simp[SNOC_APPEND,REVERSE_APPEND] >>
  Cases_on `l` >> Cases_on `xs` >> simp[last_key_t_def,REVERSE_APPEND,head_key_def]
QED

Theorem lemma_head_key_eq_last_key_t:
  !xs xk xv xts.
     head_key (REVERSE xs ++ [FibTree xk xv xts]) = last_key_t xk xs
Proof
  Induct
  >- simp[head_key_def,last_key_t_def] >>
  Cases_on `h` >>
  simp[REVERSE_APPEND,head_key_append_thm] >>
  simp[last_key_t_def]
QED


Theorem last_key_t_pull_thm:
  !xs x. last_key_t _ (xs ++ [x]) = head_key [x]
Proof
  Cases_on `xs` >>  simp[last_key_t_def] >>
  simp[head_key_append_thm, REVERSE_APPEND] >>
  Cases_on `x` >> simp[head_key_def]
QED





Definition last_key_def:
  last_key xs = last_key_t 0w xs
End

Theorem last_key_append_thm:
  !xs ys. ys <> [] ==> last_key (xs ++ ys) = last_key ys
Proof
  simp[last_key_def, last_key_t_append_thm]
QED


Definition fill_dnode_def:
  fill_dnode v e m =
    <|  value := v;
        edges := e;
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
n = next key
*)
Definition ann_fts_seg_def:
  (ann_fts_seg p s b n [] = []) /\
  (ann_fts_seg p s b n ((FibTree k v ys)::xs) =
    (FibTree k
        (fill_anode v b n p (head_key ys) (LENGTH ys))
        (ann_fts_seg k (head_key ys) (last_key ys)
            (next_key (head_key ys) (TL ys))
            ys)
    ::(ann_fts_seg p s k (next_key s (TL xs)) xs)))
End


Theorem ann_fts_seg_append_thm:
  !p s b xs ys.
    ys <> [] ==>
    ann_fts_seg p s b (next_key s (TL (xs ++ ys))) (xs ++ ys) =
    (ann_fts_seg p (head_key ys) b (next_key (head_key ys) (TL xs)) xs) ++
    (ann_fts_seg p s (last_key_t b xs) (next_key s (TL ys)) ys)
Proof
  Induct_on `xs` >> fs[]
  >- (
    Cases_on `ys` >> fs[] >>
    Cases_on `h` >>
    simp[head_key_def, next_key_def] >>
    simp[ann_fts_seg_def, last_key_t_def]
    ) >>
  rpt strip_tac >>
  Cases_on `h` >>
  simp[ann_fts_seg_def] >>
  Cases_on `xs` using SNOC_CASES >> simp[]
  >- (
    simp[ann_fts_seg_def,last_key_t_def,head_key_def] >>
    Cases_on `ys` >> fs[] >>
    Cases_on `h` >> simp[head_key_def, next_key_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  fs[last_key_t_def,head_key_def,next_key_append_thm] >>
  rename [`(next_key s (xs ++ [FibTree xk xv xl]))`] >>
  Cases_on `xs` >> simp[next_key_def,last_key_t_def,head_key_def]
QED



Definition ann_fts_def:
  (ann_fts [] = []) /\
  (ann_fts (x::xs) =
    ann_fts_seg 0w (head_key [x]) (last_key (x::xs)) (next_key (head_key [x]) xs)
    (x::xs))
End

Theorem ann_fts_append_thm:
  !xs ys.
    xs <> [] /\ ys <> [] ==>
    ann_fts (xs ++ ys) =
    (ann_fts_seg 0w (head_key ys) (last_key ys)
      (next_key (head_key xs)  (TL xs ++ ys)) xs) ++
    (ann_fts_seg 0w (head_key xs) (last_key xs)
      (next_key (head_key xs) (TL ys)) ys)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[ann_fts_def] >>
  mp_tac ann_fts_seg_append_thm >>
  disch_then (qspecl_then [`0w`, `(head_key [h])`, `(last_key (h::(t ++ ys)))`,
                            `(h::t)`, `ys`] assume_tac) >>
  Cases_on `h` >>
  fs[ann_fts_seg_def,head_key_def,last_key_def] >>
  Cases_on `ys` using SNOC_CASES >> fs[] >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  fs[REVERSE_APPEND, head_key_def,last_key_t_def] >>
  fs[last_key_t_append_thm,last_key_t_def,head_key_def]
QED



(*
Currently, unused definition.
Annotates a single tree that is not part of any list and does not have a parent.
*)
Definition ann_ft_def:
  ann_ft (FibTree k n xs) =
    FibTree k (fill_anode n 0w 0w 0w (head_key xs) (LENGTH xs))
        (ann_fts_seg k (head_key xs) (last_key xs) (next_key (head_key xs) (TL xs)) xs)
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
            b2w T;
            b2w n.data.mark;
            n.before_ptr;
            n.next_ptr;
            n.parent_ptr;
            n.child_ptr;
            n2w n.rank] *
    edges_ones (FST n.data.edges) (SND n.data.edges) * cond(k <> 0w)
End

Definition fts_mem_def:
  (fts_mem [] = emp ) /\
  (fts_mem (FibTree k n ts::xs) =
    (ft_seg $ FibTree k n ts) * (fts_mem ts) * (fts_mem xs))
End

Theorem fts_mem_append_thm:
  !xs ys. fts_mem (xs ++ ys) = fts_mem xs * fts_mem ys
Proof
  Induct >>
  fs[APPEND_def, fts_mem_def, SEP_CLAUSES] >>
  Cases_on `h` >>
  fs[fts_mem_def] >>
  strip_tac >>
  simp[STAR_ASSOC]
QED

(*The outside world already set the flag to T!*)
Definition empty_node_def:
  empty_node k (v,e) = ones k [v; FST e; b2w T; b2w F;k;k;0w;0w; n2w 0] *
    edges_ones (FST e) (SND e) * cond(k <> 0w)
End

(*-------------------------------------------------------------------*
   Memory Tests
 *-------------------------------------------------------------------*)

Definition test_build_fts_def:
  (test_build_fts _   (0:num)  edges = []) /\
  (test_build_fts mem (SUC amount) edges =
    (FibTree mem (fill_dnode (mem + 1w) (HD edges) F)[]
    :: test_build_fts (mem + 100w * bytes_in_word) (amount) (TL edges)))
End

Definition test_build_ft_def:
  test_build_ft mem children edges =
    (FibTree mem (fill_dnode (mem + 1w) (HD edges) T)
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
    fill_dnode 11w (1000w, [(50w,10)]) F) [];
    FibTree 50w (
    fill_dnode 51w (2000w, [(10w,50)]) F) [
        FibTree 100w
        (fill_dnode 101w (3000w, []) F) []
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

Theorem fts_has_append_thm:
  !k n xs ys.
    fts_has k n (xs ++ ys) = (fts_has k n xs \/ fts_has k n ys)
Proof
  Induct_on `xs`
  >- (
    simp[] >>
    rpt strip_tac >>
    iff_tac >>
    rpt strip_tac >>
    fs[Once fts_has_cases] >>
    simp[Once fts_has_cases]
    ) >>
  rpt strip_tac >>
  Cases_on `h` >>
  iff_tac >> strip_tac >>
  simp[Once fts_has_cases] >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  disch_tac >> fs[]
QED



Definition fts_min_def:
  (fts_min ([] : ('a word, 'a node_data) fts) = -1w ) /\
  (fts_min (FibTree k v _::_) = v.value)
End

Definition fts_is_min_def:
  (fts_is_min _ [] = T) /\
  (fts_is_min v (FibTree _ n ts::rest) =
    ((v <=+ n.value) /\ (fts_is_min v ts) /\ (fts_is_min v rest)))
End

Theorem fts_is_min_append_thm:
  !v xs ys. fts_is_min v (xs ++ ys) <=> fts_is_min v xs /\ fts_is_min v ys
Proof
  Induct_on `xs` >>
  fs[fts_is_min_def] >>
  Cases_on `h` >>
  fs[fts_is_min_def,CONJ_ASSOC]
QED

Theorem fts_is_min_TL_HD_thm:
  !v fts. fts <> [] ==> (fts_is_min v fts <=> fts_is_min v (TL fts ++ [HD fts]))
Proof
  Cases_on `fts`>> fs[] >>
  Cases_on `h` >>
  fs[fts_is_min_append_thm,fts_is_min_def] >>
  strip_tac >>
  iff_tac >> strip_tac >> simp[]
QED


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


Theorem fib_heap_shape_ok_append_thm:
  !xs ys.
    fib_heap_shape_ok (xs ++ ys) <=> (fib_heap_shape_ok xs /\ fib_heap_shape_ok ys)
Proof
  Induct
  >- fs[fib_heap_shape_ok_def] >>
  Cases_on `h` >>
  strip_tac >>
  iff_tac >> strip_tac
  >- (
    fs[fib_heap_shape_ok_def] >>
    first_x_assum (qspec_then `ys` assume_tac) >>
    fs[EQ_IMP_THM]
    ) >>
  fs[fib_heap_shape_ok_def]
QED




Definition fib_heap_inv_def:
  fib_heap_inv fh (fts: ('a word, 'a node_data) fts) ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\
    (∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
      ? m. fts_has k (fill_dnode v e m) fts) /\
    (!k v e.
      (FLOOKUP fh k = SOME (v,e)) /\ k = head_key fts ==>
      fts_is_min v fts) /\
    (fib_heap_shape_ok fts)
(*Everything else should be valid by annotation, construction of the heap,
  or is an individual assertion for a heap operation.
*)
End

Theorem lemma_fts_has_ul:
  !k' v' e xs ys.
    (∃m. fts_has k' (fill_dnode v' e m) (xs ++ ys)) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) (ys ++ xs)
Proof
  Induct_on `xs` >> simp[] >>
  rpt strip_tac >>
  Cases_on `h` >>
  iff_tac >> strip_tac
  >- (
    qexists `m` >>
    simp[fts_has_append_thm, DISJ_COMM] >>
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    simp[fts_has_append_thm] >>
    strip_tac >> simp[] >>
    disj2_tac >> simp[Once fts_has_cases]
    ) >>
  qexists `m` >>
  simp[Once fts_has_cases] >>
  simp[fts_has_append_thm, DISJ_COMM] >>
  pop_assum mp_tac >>
  simp[fts_has_append_thm] >>
  strip_tac >> simp[] >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  strip_tac >> simp[]
QED


Theorem lemma_fib_heap_inv_ul:
  !fh k v l xs ys.
    fib_heap_inv fh (FibTree k v l::(xs ++ ys)) ==>
    fib_heap_inv fh (FibTree k v l::(ys ++ xs))
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  rpt strip_tac
  >- (
    iff_tac >> strip_tac >>
    qexists `m` >> simp[Once fts_has_cases] >>
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    simp[fts_has_append_thm] >>
    strip_tac >> simp[]
    )
  >- (
    simp[fts_is_min_def] >>
    simp[fts_is_min_append_thm] >>
    fs[head_key_def] >>
    first_x_assum(qspecl_then [`k`, `v'`, `e`] assume_tac) >>
    fs[EQ_IMP_THM] >>
    fs[PULL_EXISTS] >>
    first_x_assum(qspec_then `m` assume_tac) >> rfs[] >>
    first_x_assum(qspecl_then [`v'`,`e`] assume_tac) >> rfs[] >>
    fs[fts_is_min_def] >>
    fs[fts_is_min_append_thm]
    ) >>
  fs[fib_heap_shape_ok_def] >>
  fs[fib_heap_shape_ok_append_thm]
QED

Theorem fib_heap_inv_ul_thm:
 !fh k v l xs ys.
    fib_heap_inv fh (FibTree k v l::(xs ++ ys)) <=>
    fib_heap_inv fh (FibTree k v l::(ys ++ xs))
Proof
  rpt strip_tac >>
  assume_tac lemma_fib_heap_inv_ul >>
  iff_tac >> simp[]
QED


Definition fib_heap_def:
  fib_heap a fh =
    SEP_EXISTS fts.
      fts_mem (ann_fts fts) *
      cond (fib_heap_inv fh fts /\ a = head_key fts)
End


(*-------------------------------------------------------------------*
   Fib Heap Insert Definition and Verification
 *-------------------------------------------------------------------*)




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
    let c = (last IN dm /\ c) in
    let c = (last + next_off IN dm /\ c) in
    let c = (sec IN dm /\ c) in
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

(*

*)

Theorem lemma_empty_list:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts = 0w) ==> fts = []
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  Cases_on `fts` >> rw[] >> Cases_on `h` >>
  rename [`FibTree k v l`] >>
  last_x_assum (qspecl_then [`0w`, `v.value`, `v.edges`] assume_tac) >>
  Cases_on `FLOOKUP fh 0w` >> fs[] >>
  fs[Once fts_has_cases] >>
  first_x_assum (qspec_then `v.mark` assume_tac) >> rfs[head_key_def, fill_dnode_def] >>
  fs[node_data_component_equality]
QED

Theorem lemma_non_empty_list:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts <> 0w) ==> fts <> []
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  Cases_on `fts` >>
  fs[head_key_def]
QED

Theorem lemma_empty_heap:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts = 0w) ==>
      (fts = [] /\ fh = FEMPTY)
Proof
  assume_tac lemma_empty_list >>
  rpt gen_tac >>
  strip_tac >>
  first_x_assum (qspecl_then [`fh`, `fts`] assume_tac) >> rfs[] >>
  fs[fib_heap_inv_def] >>
  Cases_on `fh` >> rw[] >>
  Cases_on `y` >>
  rename1 `x,(v,e)` >>
  last_x_assum (qspecl_then [`x`,`v`,`e`] assume_tac) >>
  fs[Once fts_has_cases, FLOOKUP_DEF]
QED

Theorem lemma_non_empty_heap:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts <> 0w) ==>
    (fts <> [] /\ fh <> FEMPTY)
Proof
  assume_tac lemma_non_empty_list >>
  rpt strip_tac >>
  first_assum (qspecl_then [`fh`, `fts`] assume_tac) >> rfs[] >>
  Cases_on `fts` >> gvs[head_key_def] >>
  fs[fib_heap_inv_def] >>
  Cases_on `h` >>
  first_assum (qspecl_then [`k`, `v.value`, `v.edges`, `v.mark`] assume_tac) >>
  fs[Once fts_has_cases,fill_dnode_def,node_data_component_equality]
QED

Theorem fib_heap_empty_append_inv:
  !a' v e.
    a' <> 0w ==>
    fib_heap_inv (FEMPTY |+ (a',v, e))
        [FibTree a' (fill_dnode v e F) []]
Proof
  rw[fib_heap_inv_def]
  >- fs[FLOOKUP_DEF]
  >- (
    rpt strip_tac >>
    iff_tac >> strip_tac
    >- (
      qexists `F` >>
      fs[Once fts_has_cases, FLOOKUP_DEF, fill_dnode_def]
      ) >>
    fs[Once fts_has_cases, FLOOKUP_DEF, fill_dnode_def] >>
    fs[Once fts_has_cases]
    )
  >- (
    rpt strip_tac >> fs[fts_is_min_def] >>
    fs[head_key_def, FLOOKUP_DEF, fill_dnode_def]
    )
  >> fs[fib_heap_shape_ok_def] >>
  simp[Ntimes fib_num_def 3] >>
  simp[Once fib_num_def]
QED

Theorem lemma_fib_heap_new_min:
  !v v' fts. v <=+ v' /\ fts_is_min v' fts ==> fts_is_min v fts
Proof
  gen_tac >>
  ho_match_mp_tac fts_is_min_ind >>
  simp[fts_is_min_def] >>
  rpt strip_tac >>
  imp_res_tac WORD_LOWER_EQ_TRANS
QED


(* New smallest elemet *)
Theorem lemma_insert_new_min_inv:
  !fh fts k v e.
    k <> 0w /\
    FLOOKUP fh k = NONE /\
    fib_heap_inv fh fts /\
    (v <=+ fts_min fts) ==>
    fib_heap_inv (fh |+ (k,v,e)) (FibTree k (fill_dnode v e F) []::fts)
Proof
  fs[fib_heap_inv_def] >>
  rpt strip_tac
  >- gvs[FLOOKUP_DEF]
  >- (
    iff_tac >>
    strip_tac >>
    last_x_assum (qspecl_then [`k'`, `v'`, `e'`] assume_tac) >>
    Cases_on `k = k'`
    >- (
      fs[Once FLOOKUP_DEF] >>
      qexists `F` >>
      fs[Once fts_has_cases]
      )
    >- (
        fs[FLOOKUP_SIMP] >>
        qexists `m` >>
        simp[Once fts_has_cases]
      )
    >- (
      fs[Once fts_has_cases]
      >- fs[fill_dnode_def, FLOOKUP_SIMP]
      >- (
        qpat_assum `fts_has k' (fill_dnode v' e' m) fts` mp_tac >>
        pure_rewrite_tac[Once fts_has_cases] >>
        disch_tac >>
        rfs[] >>
        first_assum (qspec_then `m` assume_tac) >>
        fs[]
        )
      >> fs[Once fts_has_cases]
      )
    >- (
      qpat_assum `fts_has k' (fill_dnode v' e' m)
                    (FibTree k (fill_dnode v e F) []::fts)` mp_tac >>
      pure_rewrite_tac[Once fts_has_cases] >>
      rfs[] >>
      simp[DISJ_SYM] >>
      simp[Once fts_has_cases] >>
      strip_tac >>
      fs[FLOOKUP_SIMP] >> qexists `m` >> gvs[]
      )
    )
  >- (
    fs[head_key_def, FLOOKUP_SIMP, fts_is_min_def] >>
    simp[fill_dnode_def] >>
    Cases_on `fts`
    >- fs[fts_is_min_def] >>
    Cases_on `h` >>
    last_x_assum (qspecl_then [`k'`, `v''.value`, `v''.edges`] assume_tac ) >>
    fs[EQ_IMP_THM]>>
    fs[PULL_EXISTS] >>
    first_assum (qspec_then `v''.mark` assume_tac) >>
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    simp[fill_dnode_def,node_data_component_equality] >>
    strip_tac >>
    last_assum (qspecl_then [`v''.value`, `v''.edges`] assume_tac) >>
    gvs[head_key_def] >>
    fs[fts_min_def] >>
    dxrule_all lemma_fib_heap_new_min >> simp[]
  ) >>
  fs[fib_heap_shape_ok_def] >>
  simp[fib_heap_size_def, Ntimes fib_num_def 3] >>
  simp[Once fib_num_def]
QED

Theorem lemma_insert_old_min_inv:
  !fh fts k v e.
    k <> 0w /\
    FLOOKUP fh k = NONE /\
    fib_heap_inv fh fts /\
    ~(v <=+ fts_min fts) ==>
    fib_heap_inv (fh |+ (k,v,e)) (fts ++ [FibTree k (fill_dnode v e F) []])
Proof
  fs[fib_heap_inv_def] >>
  rpt strip_tac
  >- gvs[FLOOKUP_SIMP]
  >- (
    iff_tac >>
    strip_tac >>
    last_x_assum (qspecl_then [`k'`, `v'`, `e'`] assume_tac) >>
    Cases_on `k = k'`
    >- (
      qexists `F` >>
      simp[fts_has_append_thm] >>
      fs[FLOOKUP_SIMP] >>
      disj2_tac >>
      simp[Once fts_has_cases]
      )
    >- (
      fs[FLOOKUP_SIMP] >>
      qexists `m` >>
      simp[fts_has_append_thm]
      )
    >- (
      qpat_x_assum `fts_has k' (fill_dnode v' e' m)
                    (fts ++ [FibTree k (fill_dnode v e F) []])` mp_tac >>
      simp[fts_has_append_thm] >>
      disch_tac >> gvs[] >>
      pop_assum mp_tac >> simp[Once fts_has_cases] >>
      disch_tac >> fs[]
      >- fs[fill_dnode_def,FLOOKUP_SIMP] >>
      fs[Once fts_has_cases]
      ) >>
    simp[FLOOKUP_SIMP] >>
    qexists `m` >>
    fs[fts_has_append_thm] >>
    qpat_x_assum `fts_has k' (fill_dnode v' e' m)
                  [FibTree k (fill_dnode v e F) []]` mp_tac >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases]
    )
  >- (
    simp[fts_is_min_append_thm] >>
    strip_tac
    >- (
      Cases_on `fts`
      >- simp[fts_is_min_def] >>
      fs[head_key_append_thm] >>
      Cases_on `h` >>
      fs[head_key_def,fts_min_def] >>
      Cases_on `k = k'`
      >- (
        first_x_assum(qspecl_then [`k'`,`v''.value`,`v''.edges`] assume_tac) >>
        gvs[FLOOKUP_SIMP] >>
        first_x_assum(qspec_then `v''.mark` assume_tac) >>
        fs[Once fts_has_cases] >>
        fs[fill_dnode_def,node_data_component_equality]
        ) >>
      fs[FLOOKUP_SIMP]
      ) >>
    Cases_on `fts`
    >- (
       fs[head_key_def,FLOOKUP_SIMP] >>
       simp[fts_is_min_def,fill_dnode_def]
       ) >>
    Cases_on `h` >>
    fs[head_key_def,fts_min_def] >>
    Cases_on `k = k'`
    >- fs[FLOOKUP_SIMP, fts_is_min_def,fill_dnode_def] >>
    first_x_assum(qspecl_then [`v'`,`e'`] assume_tac) >>
    rfs[fts_is_min_def] >>
    simp[fill_dnode_def] >>
    first_x_assum (qspecl_then [`k'`,`v'`,`e'`] assume_tac) >>
    fs[FLOOKUP_SIMP] >>
    fs[PULL_EXISTS] >>
    first_x_assum (qspec_then `m` assume_tac) >> rfs[] >>
    mp_tac WORD_LOWER_EQ_CASES >>
    disch_then (qspecl_then [`v`,`v''.value`] assume_tac) >> rfs[] >>
    mp_tac WORD_LOWER_EQ_TRANS >>
    disch_then (qspecl_then [`v'`,`v''.value`,`v`] assume_tac) >>
    simp[]
    ) >>
  simp[fib_heap_shape_ok_append_thm] >>
  simp[fib_heap_shape_ok_def] >>
  simp[Ntimes fib_num_def 3, fib_heap_size_def] >>
  simp[Once fib_num_def]
QED



Theorem fib_heap_insert:
  ∀frame k v fh.
    (empty_node k v * fib_heap a fh * frame * cond(FLOOKUP fh k = NONE))
      (fun2set (m,dm)) ∧
    fib_heap_insert (a, k, m, dm) = (a', m', b) ⇒
    (fib_heap a' (fh |+ (k,v)) * frame) (fun2set (m',dm)) ∧ b
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  PairCases_on `v` >>
  rename [`empty_node k (v,e)`] >>
  fs[empty_node_def, ones_def] >>
  fs[SEP_EXISTS_THM, SEP_CLAUSES, STAR_ASSOC] >>
  simp [fib_heap_insert_def] >>
  SEP_R_TAC >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  IF_CASES_TAC
  >- (
    assume_tac lemma_empty_heap >>
    first_x_assum (qspecl_then [`fh`, `fts`] assume_tac) >> gvs[] >>
    fs[fib_heap_empty_append_def,before_off_def, next_off_def,
       child_off_def, parent_off_def] >>
    SEP_R_TAC >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' (fill_dnode v e F) []]` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    gvs[] >>
    assume_tac fib_heap_empty_append_inv >>
    gs[fill_dnode_def]
    ) >>
  assume_tac lemma_non_empty_heap >>
  first_x_assum (qspecl_then [`fh`, `fts`] assume_tac) >>
  Cases_on `fts` >> gvs[] >>
  Cases_on `h` >>
  Cases_on `t` using SNOC_CASES >>
  fs[SNOC_APPEND,head_key_def]
  >- (
    fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    `k + 2w * bytes_in_word <> k'` by SEP_NEQ_TAC >> simp[] >>
    SEP_R_TAC >>
    IF_CASES_TAC
    >- (
      fs[fib_heap_append_def,before_off_def,next_off_def] >>
      fs[head_key_def,last_key_def,last_key_t_def] >>
      SEP_R_TAC >>
      IF_CASES_TAC >> fs[] >>
      SEP_R_TAC >> simp[] >>
      strip_tac >> gvs[] >>
      SEP_W_TAC >>
      qexists `[FibTree a' (fill_dnode v e F) []; FibTree k' v' l]` >>
      simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
           SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
           fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
      mp_tac lemma_insert_new_min_inv >>
      disch_then (qspecl_then
          [`fh`, `[FibTree k' v' l]`, `a'`, `v`, `e`] assume_tac) >>
      fs[fts_min_def,fill_dnode_def]
      ) >>
    fs[fib_heap_append_def,before_off_def,next_off_def] >>
    SEP_R_TAC >>
    IF_CASES_TAC >> fs[] >>
    fs[head_key_def,last_key_def,last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' v' l; FibTree k (fill_dnode v e F) []]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    fs[AC STAR_COMM STAR_ASSOC] >>
    fs[STAR_ASSOC] >>
    mp_tac lemma_insert_old_min_inv >>
    disch_then (qspecl_then [`fh`, `[FibTree a' v' l]`,`k`,`v`,`e`] assume_tac) >>
    fs[fts_min_def, fill_dnode_def]
   ) >>
  Cases_on `x` >>
  rename [`fib_heap_inv fh (FibTree k' v' l::(l' ++ [FibTree lk lv ts]))`] >>
  Cases_on `l'` >>
  fs[head_key_def, next_key_def]
  >- (
    fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    `k' <> lk` by SEP_NEQ_TAC >> simp[] >>
    SEP_R_TAC >>
    IF_CASES_TAC
    >- (
      simp[fib_heap_append_def,before_off_def,next_off_def] >>
      SEP_R_TAC >>
      fs[last_key_def,head_key_def,last_key_t_def] >>
      SEP_R_TAC >> simp[] >>
      strip_tac >> gvs[] >>
      SEP_W_TAC >>
      qexists `[FibTree a' (fill_dnode v e F) []; FibTree lk lv ts;
                FibTree k' v' l]` >>
      simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
           SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
           fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
      fs[AC STAR_COMM STAR_ASSOC] >>
      fs[STAR_ASSOC] >>
      qspecl_then [`fh`, `[FibTree k' v' l;FibTree lk lv ts]`, `a'`,
                               `v`,`e`] assume_tac lemma_insert_new_min_inv >>
      rfs[fts_min_def] >>
      qspecl_then [`fh |+ (a',v,e)`,`a'`,`(fill_dnode v e F)`,`[]`,
        `[FibTree k' v' l]`,`[FibTree lk lv ts]`] assume_tac fib_heap_inv_ul_thm >>
      rfs[fill_dnode_def]
      ) >>
    simp[fib_heap_append_def,before_off_def,next_off_def] >>
    fs[last_key_def,head_key_def,last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' v' l; FibTree lk lv ts;
              FibTree k (fill_dnode v e F) []]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    fs[AC STAR_COMM STAR_ASSOC] >>
    fs[STAR_ASSOC] >>
    mp_tac lemma_insert_old_min_inv >>
    disch_then (qspecl_then [`fh`, `[FibTree a' v' l; FibTree lk lv ts]`,
                             `k`,`v`,`e`] assume_tac) >>
    fs[fts_min_def, fill_dnode_def]
   ) >>
  qspecl_then [`FibTree k' v' l::h::t`, `[FibTree lk lv ts]`]
    assume_tac ann_fts_append_thm >>
  fs[] >>
  pop_assum kall_tac >>
  Cases_on `h` >>
  fs[head_key_def, next_key_def] >>
  fs[fts_mem_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
     fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  rename [`fib_heap_inv fh (FibTree fk fv fts::FibTree sk sv sts::
           (t ++ [FibTree lk lv lts]))`] >>
  SEP_R_TAC >>
  `fk <> sk` by SEP_NEQ_TAC >>
  IF_CASES_TAC
  >- (
    simp[fib_heap_append_def,before_off_def,next_off_def] >>
    fs[last_key_def,head_key_def, last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' (fill_dnode v e F) []; FibTree sk sv sts] ++
              t ++ [FibTree lk lv lts] ++ [FibTree fk fv fts]` >>
    fs[head_key_def,next_key_def,last_key_def,head_key_append_thm] >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    simp[ann_fts_seg_append_thm,fts_mem_append_thm, STAR_ASSOC] >>
    simp[next_key_append_thm] >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    fs[last_key_t_def,head_key_def,REVERSE_APPEND] >>
    fs[lemma_head_key_eq_last_key_t] >>
    fs[next_key_pull_last_thm,last_key_t_pull_thm,head_key_def] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    fs[STAR_ASSOC] >>
    qspecl_then [`fh`, `(FibTree fk fv fts::FibTree sk sv sts::t) ++
      [FibTree lk lv lts]`, `a'`, `v`,`e`] assume_tac lemma_insert_new_min_inv >>
    rfs[fts_min_def] >>
    qspecl_then [`fh |+ (a',v,e)`,`a'`,`(fill_dnode v e F)`,`[]`,
      `[FibTree fk fv fts]`,`(FibTree sk sv sts::t) ++ [FibTree lk lv lts]`]
      assume_tac fib_heap_inv_ul_thm >>
    rfs[fill_dnode_def]
    ) >>
  simp[fib_heap_append_def,before_off_def,next_off_def] >>
  fs[last_key_def, head_key_def, last_key_t_def] >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  SEP_W_TAC >>
  qexists `[FibTree a' fv fts; FibTree sk sv sts] ++ t ++
           [FibTree lk lv lts; FibTree k (fill_dnode v e F) []]` >>
  fs[head_key_def,next_key_def,last_key_def,head_key_append_thm] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  simp[ann_fts_seg_append_thm,fts_mem_append_thm, ann_fts_append_thm, STAR_ASSOC] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  fs[next_key_append_thm, last_key_t_def, head_key_def, REVERSE_APPEND] >>
  fs[lemma_head_key_eq_last_key_t]>>
  qspecl_then[`t ++ [FibTree lk lv lts]`,`k`,`(fill_dnode v e F)`, `[]`]
    mp_tac next_key_pull_last_thm >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  disch_tac >> fs[fill_dnode_def] >>
  simp[next_key_pull_last_thm] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  qspecl_then[`fh`, `(FibTree a' fv fts::FibTree sk sv sts::t) ++
    [FibTree lk lv lts]`, `k`, `v`, `e`] assume_tac lemma_insert_old_min_inv >>
  rfs[fts_min_def,fill_dnode_def] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  disch_tac >> simp[]
QED

(*-------------------------------------------------------------------*
   Fib Heap Extract Minimum Definition and Verification
 *-------------------------------------------------------------------*)

Definition find_min_def:
  find_min (k:num)
    (min_n:'a word, s:'a word, t:'a word,
     m:'a word -> 'a word, dm: 'a word set, c: bool)
  =
    if k = 0 then (min_n,m,F) else
    let c = (t IN dm /\ c) in
    if s = t then
      (*balance root list or do it in a separate step *)
      (min_n,m,c)
    else
      let c = (min_n IN dm /\ c) in
      let v = m min_n in
      let c = (t + next_off IN dm /\ c) in
      let v_t = m t in
      let t_n = m (t + next_off) in
      if v_t <=+ v then
        find_min (k-1) (v_t,s,t_n,m,dm,c)
      else
        find_min (k-1) (min_n,s,t_n,m,dm,c)
End

Definition list_in_mem_def:
  list_in_mem (k:num)
    (t:'a word, s:'a word, m:'a word -> 'a word, dm: 'a word set,c: bool)
  =
    if k = 0 then F else
    if t = s then
      c
    else
      let t_n = (t + next_off IN dm /\ c) in
      let n = m (t + next_off) in
        list_in_mem (k-1) (n,s,m,dm,c)
End


Theorem lemma_list_in_mem:
  !xs frame k h n.
    (LENGTH xs < k) /\
      (head_key xs = h) /\ (next_key h (TL xs) = n) /\
      (fts_mem (ann_fts xs) * frame) (fun2set(m,dm)) ==>
    list_in_mem k (n,h,m,dm,T)
Proof
  Induct_on `k`
  >- (
    rpt strip_tac >>
    Cases_on `xs` >> fs[LENGTH]
    ) >>
  simp[Once list_in_mem_def] >>
  rpt strip_tac >>
  Cases_on `xs` >> simp[next_key_def,head_key_def] >>
  Cases_on `h` >> simp[head_key_def] >>
  Cases_on `t` >> simp[next_key_def] >>
  Cases_on `h` >> simp[head_key_def] >>
  rename [`LENGTH (FibTree k1 v1 l1::FibTree k2 v2 l2::xs)`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
     fill_dnode_def, next_key_def, ones_def, STAR_ASSOC,
     fts_mem_append_thm,ann_fts_seg_append_thm,next_key_pull_last_thm] >>
  `k1 <> k2` by SEP_NEQ_TAC >> simp[] >>
  simp[next_off_def] >>
  SEP_R_TAC >>
  Cases_on `xs`
  >- (
    simp[next_key_def] >>
    fs[LENGTH] >>
    simp[Once list_in_mem_def]
    ) >>
  Cases_on `h`>> simp[next_key_def,head_key_def] >>
  fs[REVERSE_APPEND,head_key_def] >>
  first_x_assum(qspec_then `(FibTree k2 v2 l2::FibTree k' v l::t) ++
    [FibTree k1 v1 l1]` assume_tac) >>
  fs[LENGTH] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
     fill_dnode_def, next_key_def, ones_def, STAR_ASSOC,
     fts_mem_append_thm,ann_fts_seg_append_thm,next_key_pull_last_thm] >>
  rfs[] >>
  cheat
QED


(*assumption: both heads are the smallest element*)
Definition fib_heap_insert_list_def:
  fib_heap_insert_list (k:num)
    (a:'a word,t:'a word,m:'a word -> 'a word, dm: 'a word set)
  =
    if t = 0w then (a,m,T) else
    let c = (t IN dm) in
    let c = (t + next_off IN dm /\ c) in
    let t_n = m (t + next_off) in
    if a = 0w then (*list a is empty*)
      (t,m,c)
    else
      let c = (a IN dm /\ c) in

      let c = (a + before_off IN dm /\ c) in
      let l_a = m (a + before_off) in
      let c = (l_a + next_off IN dm /\ c) in

      let c = (t + before_off IN dm /\ c) in
      let l_t = m (t + before_off) in
      let c = (l_t + next_off IN dm /\ c) in

      let m = ((l_a + next_off) =+ t) m in
      let m = ((t + before_off) =+ l_a) m in
      let m = ((l_t + next_off) =+ a) m in
      let m = ((a + before_off) =+ l_t) m in

      let v_t = m t in
      let v_a = m a in
      if v_t <=+ v_a then
        (t,m,c)
      else
        (a,m,c)
End


Definition list_not_in_heap_def:
  (list_not_in_heap fh [] <=> T) /\
  (list_not_in_heap fh (FibTree k n ts::rest) <=>
    FLOOKUP fh k = NONE /\ list_not_in_heap fh ts /\ list_not_in_heap fh rest)
End

Definition to_map_upd_list_def:
  (to_map_upd_list [] = []) /\
  (to_map_upd_list (FibTree k v ts::rest) =
    [(k,v.value,v.edges)] ++ to_map_upd_list rest ++ to_map_upd_list ts)
End


Theorem lemma_write_to_heap_new_min:
  !frame xs fts v v'.
    (fts_mem (ann_fts xs) * fts_mem (ann_fts fts) * frame *
     cond(head_key xs = k /\ head_key fts = a /\ n > LENGTH xs))
      (fun2set (m,dm)) /\ fib_heap_insert_list n (a, k, m, dm) = (a', m', b) ==>
    ?fts'.
    (fts_mem(ann_fts (fts')) * frame * cond(a' = head_key (fts')))
      (fun2set (m',dm)) /\ b
Proof
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    fs[to_map_upd_list_def, fts_mem_def, ann_fts_def,SEP_CLAUSES,head_key_def] >>
    simp[fib_heap_insert_list_def] >>
    strip_tac >>
    qexists `fts` >> gvs[]
    ) >>
  Cases_on `h`>> gvs[head_key_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
     fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  Cases_on `fts` >> simp[head_key_def,next_off_def,before_off_def] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR]
  >- (
    fs[fib_heap_insert_list_def,next_off_def] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    qexists `(FibTree a' v l::t)` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC]
    ) >>
  Cases_on `t` using SNOC_CASES
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    fs[fib_heap_insert_list_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    cheat
    ) >>
  cheat
(*
    >- (
      SEP_R_TAC >> simp[next_off_def] >>
      simp[Once list_in_mem_def] >>
      strip_tac >>
      qexists `[FibTree k v l]` >>
      fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC]
      ) >>
    Cases_on `h` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC]
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    `k <> k'` by SEP_NEQ_TAC >> simp[] >>
    Cases_on `t` using SNOC_CASES >>
    simp[last_key_t_def,head_key_def]
    >- (
       IF_CASES_TAC >>
       SEP_R_TAC >> simp[Once list_in_mem_def] >>
       strip_tac >> gvs[] >>
       SEP_W_TAC >>
       SEP_R_TAC >> gvs[]
       >- (
         qexists `[FibTree a' v l; FibTree k' v' l']` >>
         fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
            SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
            fill_dnode_def, next_key_def, ones_def, STAR_ASSOC]
        ) >>
       qexists `[FibTree a' v' l';FibTree k v l]` >>
       fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
          SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
          fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
       fs[AC STAR_COMM STAR_ASSOC]
     ) >>
    Cases_on `x` >> fs[SNOC_APPEND] >>
    fs[REVERSE_APPEND,head_key_def] >>
    rename [`last_key_t 0w (FibTree fk fv fts::(list ++ [FibTree lk lv lts]))`]
    fs[fts_mem_append_thm,ann_fts_seg_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
    IF_CASES_TAC >>
    SEP_R_TAC >> simp[Once list_in_mem_def] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    >- (
      qexists `[FibTree a' v l] ++ (FibTree fk fv fts::(list ++
               [FibTree lk lv lts]))`>>
      fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
         fill_dnode_def, next_key_def, ones_def, STAR_ASSOC,
         fts_mem_append_thm,ann_fts_seg_append_thm,next_key_pull_last_thm] >>
      fs[REVERSE_APPEND,head_key_def]
      ) >>
    qexists `(FibTree a' fv fts::(list ++ [FibTree lk lv lts])) ++
             [FibTree k v l]` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC,
       fts_mem_append_thm,ann_fts_seg_append_thm,next_key_pull_last_thm] >>
       fs[REVERSE_APPEND,head_key_def,last_key_t_pull_thm] >>
       fs[AC STAR_COMM STAR_ASSOC]
   ) >>
  Cases_on `x` >> fs[SNOC_APPEND,last_key_t_def,head_key_def,REVERSE_APPEND] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
     fill_dnode_def, next_key_def, ones_def, STAR_ASSOC,
     fts_mem_append_thm,ann_fts_seg_append_thm,next_key_pull_last_thm] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_insert_list_def] >>
  Cases


*)
QED


Theorem fib_heap_insert_list:
  ∀frame xs fh n.
    (fts_mem (ann_fts xs) * fib_heap a fh * frame *
     cond(list_not_in_heap fh xs /\ n > LENGTH xs /\ head_key xs = k))
      (fun2set (m,dm)) ∧
    fib_heap_insert_list n (a, k, m, dm) = (a', m', b) ⇒
    (fib_heap a' (fh |++ (to_map_upd_list xs)) * frame) (fun2set (m',dm)) ∧ b
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    fs[to_map_upd_list_def, fts_mem_def, ann_fts_def,SEP_CLAUSES,head_key_def] >>
    simp[fib_heap_insert_list_def] >>
    simp[FUPDATE_LIST] >>
    strip_tac >>
    qexists `fts` >> gvs[]
    ) >>
  Cases_on `h`>> gvs[head_key_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  Cases_on `t` using SNOC_CASES
  >- (
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_seg_def, fill_anode_def,
       fill_dnode_def, next_key_def, ones_def, STAR_ASSOC] >>
  fs[fib_heap_insert_list_def] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  cheat ) >>
  cheat
QED



(*
Definition fib_heap_rebalancing_def:
  fib_heap_rebalancing
    (a:'a word, t:'a word, m:'a word -> 'a word, dm:'a word set)
   let c = (a IN dm) in
   let


   (m,c)
End
*)

Definition fib_heap_extract_min_def:
  fib_heap_extract_min
    (a:'a word, m:'a word -> 'a word, dm :'a word set)
  =
    let c = (a IN dm) in
    let c = (a + next_off IN dm /\ c) in
    let sec = m (a + next_off) in
    if a = sec then
      let c = (a + child_off IN dm /\ c) in
      let a_child = m (a + child_off) in
        (a_child,m,c)
    else
      let c = (a + before_off IN dm /\ c) in
      let lst = m (a + before_off) in
      let c = (lst + next_off IN dm /\ c) in
      let c = (sec + before_off IN dm /\ c) in
      let m = ((lst + next_off) =+ sec) m in
      let m = ((sec + before_off) =+ lst) m in
      let c = (sec IN dm /\ c) in
      let sec_n = (sec + next_off IN dm /\ c) in
        (*find_new_min(sec,sec,sec_n,m,dm,c)*)
        (0w,m,c)
End
