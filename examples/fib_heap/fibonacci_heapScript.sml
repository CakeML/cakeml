(*
  Separation logic assertions for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list alist set_sep pair finite_map combin pred_set rich_list
Libs
  wordsLib helperLib

(*-------------------------------------------------------------------*
   Auxilary Helper Functions
 *-------------------------------------------------------------------*)

Theorem lemma_cons_eq_append:
  (x::xs) = [x] ++ xs
Proof
  simp[]
QED


(*-------------------------------------------------------------------*
   Datatypes
 *-------------------------------------------------------------------*)

Datatype:
  ft = FibTree 'k 'v (ft list)
End

Type fts = “:('k,'v) ft list”;


(* TODO: Refactor data_node to data_node *)
Datatype:
  data_node = <| value : 'a word ;
                 edges : ('a word # ('a word # num) list);
                 mark  : bool |>
End

val data_node_component_equality = fetch "-" "data_node_component_equality";


Theorem lemma_data_node_cases:
  <|value := v.value; edges := v.edges; mark := v.mark|> = v
Proof
  simp [data_node_component_equality]
QED


Datatype:
  annotated_node =
    <| data       : 'a data_node ;
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
  annotate ((FibTree k n ts)    : ('a word, 'a data_node) ft) =
            (FibTree k ARB ARB) : ('a word, 'a annotated_data_node) ft
End
*)
(*[simp] *)

Definition head_key_t_def:
  (head_key_t (s:'a word) [] = s) /\
  (head_key_t s (FibTree k n ts::xs) = k)
End

Theorem head_key_t_append_thm:
  !s xs ys. xs <> [] ==> head_key_t s (xs ++ ys) = head_key_t s xs
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[] >>
  Cases_on `h` >> simp[head_key_t_def]
QED

Theorem head_key_t_pull_last_thm:
  !xs xk xv xts d.
    head_key_t d (xs ++ [FibTree xk xv xts]) = head_key_t xk xs
Proof
  Cases_on `xs` >> simp[head_key_t_def] >>
  Cases_on `h` >> simp[head_key_t_def]
QED



Definition head_key_def:
  (head_key xs = head_key_t 0w xs)
End

Theorem head_key_append_thm:
  !xs ys. xs <> [] ==> head_key (xs ++ ys) = head_key (xs)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[] >>
  Cases_on `h` >> simp[head_key_def,head_key_t_def]
QED





Definition last_key_t_def:
  (last_key_t d [] = d) /\
  (last_key_t d xs = head_key_t d (REVERSE xs))
End

Theorem last_key_t_append_thm:
  !xs ys d. ys <> [] ==> last_key_t d (xs ++ ys) = last_key_t d ys
Proof
  rpt strip_tac >>
  Cases_on `ys` using SNOC_CASES >> fs[] >>
  Cases_on `x` >> simp[SNOC_APPEND,REVERSE_APPEND] >>
  Cases_on `l` >> Cases_on `xs` >>
  simp[last_key_t_def,REVERSE_APPEND,head_key_def, head_key_t_def]
QED


Theorem last_key_t_pull_thm:
  !xs x.
    last_key_t _ (xs ++ [x]) = head_key [x] /\
    last_key_t _ (xs ++ [x]) = head_key_t _ [x]
Proof
  Cases_on `xs` >>  simp[last_key_t_def,head_key_def]
  >- (
    Cases_on `x` >>
    simp[head_key_t_def]
    ) >>
  simp[head_key_append_thm, REVERSE_APPEND] >>
  Cases_on `x` >> simp[head_key_t_def]
QED


Theorem lemma_head_keys_eq_last_key_t:
  !xs xk xv xts.
     head_key (REVERSE xs ++ [FibTree xk xv xts]) = last_key_t xk xs /\
     head_key_t _ (REVERSE xs ++ [FibTree xk xv xts]) = last_key_t xk xs
Proof
  Induct
  >- simp[head_key_def,head_key_t_def,last_key_t_def] >>
  Cases_on `h` >>
  simp[REVERSE_APPEND,head_key_append_thm] >>
  Cases_on `xs` using SNOC_CASES
  >- simp[last_key_t_def,head_key_def,head_key_t_def] >>
  Cases_on `x` >> simp[SNOC_APPEND] >>
  simp[last_key_t_def,head_key_t_append_thm] >>
  rename [`last_key_t k (xs ++ [FibTree x v l])`] >>
  Cases_on `xs `
  >- simp[head_key_t_def,last_key_t_def,head_key_def] >>
  Cases_on `h` >>
  simp[head_key_t_def,last_key_t_def,head_key_def,REVERSE_APPEND]
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
            (head_key_t (head_key ys) (TL ys))
            ys)
    ::(ann_fts_seg p s k (head_key_t s (TL xs)) xs)))
End


Theorem ann_fts_seg_append_thm:
  !p s b xs ys.
    ys <> [] ==>
    ann_fts_seg p s b (head_key_t s (TL (xs ++ ys))) (xs ++ ys) =
    (ann_fts_seg p (head_key_t s ys) b (head_key_t (head_key ys) (TL xs)) xs) ++
    (ann_fts_seg p s (last_key_t b xs) (head_key_t s (TL ys)) ys)
Proof
  Induct_on `xs` >> fs[]
  >- (
    Cases_on `ys` >> fs[] >>
    Cases_on `h` >>
    simp[head_key_def, head_key_t_def] >>
    simp[ann_fts_seg_def, last_key_t_def]
    ) >>
  rpt strip_tac >>
  Cases_on `h` >>
  simp[ann_fts_seg_def] >>
  Cases_on `xs` using SNOC_CASES >> simp[]
  >- (
    simp[ann_fts_seg_def,last_key_t_def,head_key_def] >>
    Cases_on `ys` >> rpt gen_tac >> pop_assum mp_tac >> simp[] >>
    Cases_on `h` >> simp[head_key_def, head_key_t_def, last_key_t_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  fs[last_key_t_def,head_key_def,head_key_t_def,head_key_t_append_thm] >>
  rpt gen_tac >>
  rename [`(head_key_t s (xs ++ [FibTree xk xv xl]))`] >>
  Cases_on `xs` >> simp[head_key_t_def,last_key_t_def,head_key_def]
  >- (Cases_on `ys` >> fs[] >> Cases_on `h` >> simp[head_key_t_def]) >>
  Cases_on `h` >>
  simp[head_key_t_def] >>
  Cases_on `ys` >> fs[] >> Cases_on `h` >> simp[head_key_t_def]
QED



Definition ann_fts_def:
  (ann_fts p [] = []) /\
  (ann_fts p (x::xs) =
    ann_fts_seg p (head_key [x]) (last_key (x::xs))
      (head_key_t (head_key [x]) xs)
    (x::xs))
End

Theorem ann_fts_append_thm:
  !xs ys p.
    xs <> [] /\ ys <> [] ==>
    ann_fts p (xs ++ ys) =
    (ann_fts_seg p (head_key ys) (last_key ys)
      (head_key_t (head_key xs)  (TL xs ++ ys)) xs) ++
    (ann_fts_seg p (head_key xs) (last_key xs)
      (head_key_t (head_key xs) (TL ys)) ys)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> fs[ann_fts_def] >>
  mp_tac ann_fts_seg_append_thm >>
  disch_then (qspecl_then [`p`, `(head_key [h])`, `(last_key (h::(t ++ ys)))`,
                            `(h::t)`, `ys`] assume_tac) >>
  Cases_on `h` >>
  fs[ann_fts_seg_def,head_key_def,head_key_t_def,last_key_def] >>
  simp[last_key_t_def] >>
  simp[lemma_head_keys_eq_last_key_t] >>
  Cases_on `t`
  >- (
    simp[ann_fts_seg_def] >>
    Cases_on `ys` >> fs[] >>
    Cases_on `h` >> simp[head_key_t_append_thm] >>
    simp[head_key_t_def] >>
    Cases_on `t` using SNOC_CASES >> simp[last_key_t_def,head_key_t_def] >>
    Cases_on `x` >> simp[SNOC_APPEND] >>
    simp[lemma_head_keys_eq_last_key_t]
    ) >>
  Cases_on `ys` using SNOC_CASES >> fs[] >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  simp[head_key_t_pull_last_thm] >>
  Cases_on `h` >>
  simp[last_key_t_def] >>
  simp[head_key_t_append_thm,head_key_t_def] >>
  simp[last_key_t_pull_thm, REVERSE_APPEND,head_key_t_def,head_key_def]
QED


Definition ann_ft_def:
  ann_ft p (FibTree k n xs) =
    FibTree k (fill_anode n k k p (head_key xs) (LENGTH xs))
        (ann_fts_seg k (head_key xs) (last_key xs) (head_key_t (head_key xs) (TL xs)) xs)
End

Definition ann_fts_as_singl_def:
  (ann_fts_as_singl p [] = [] ) /\
  (ann_fts_as_singl p (x::xs) =
    [ann_ft p x] ++ ann_fts_as_singl p xs)
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

Definition ft_mem_def:
  ft_mem ((FibTree k n _): ('a word, 'a annotated_node) ft) =
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
    (ft_mem $ FibTree k n ts) * (fts_mem ts) * (fts_mem xs))
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


Theorem fts_mem_ann_sym_thm:
  fts_mem (ann_fts p (xs ++ ys)) = fts_mem (ann_fts p (ys ++ xs))
Proof
  Cases_on `xs` >> Cases_on `ys` >> fs[]>>
  Cases_on `h` >> Cases_on `h'` >>
  pure_rewrite_tac[GSYM (cj 2 APPEND)] >>
  qspecl_then [`(FibTree k v l::t)`,`(FibTree k' v' l'::t')`,`p`]
    assume_tac ann_fts_append_thm >>
  qspecl_then [`(FibTree k' v' l'::t')`,`(FibTree k v l::t)`,`p`]
    assume_tac ann_fts_append_thm >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pure_rewrite_tac[Once (GSYM APPEND_ASSOC),APPEND] >> disch_tac >>
  pure_rewrite_tac[Once (GSYM APPEND_ASSOC),APPEND] >> disch_tac >>
  simp[] >>
  simp[fts_mem_append_thm] >>
  simp[head_key_def,head_key_t_def] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[head_key_t_append_thm,head_key_t_pull_last_thm] >>
  simp[AC STAR_ASSOC STAR_COMM]
QED


Theorem lemma_ann_fts_seg_MEM:
  !fts x v l p s b n frame.
    (fts_mem (ann_fts_seg p s b n fts) * frame) (fun2set(m,dm))  /\
    MEM (FibTree x v l) fts ==>
    ?t1 t2. fts = t1 ++ [FibTree x v l] ++ t2
Proof
  Induct >> fs[] >>
  rpt strip_tac >>
  Cases_on `h` >> gvs[]
  >- (qexistsl [`[]`,`fts`] >> simp[] ) >>
  fs[fts_mem_def,ann_fts_seg_def] >>
  res_tac >>
  first_x_assum(qspecl_then [`s`,`p`,`(head_key_t s (TL fts))`,
    `ft_mem(FibTree k (fill_anode v' b n p (head_key l') (LENGTH l'))
      (ann_fts_seg k (head_key l') (last_key l')
      (head_key_t (head_key l') (TL l')) l')) *
     fts_mem
      (ann_fts_seg k (head_key l') (last_key l')
      (head_key_t (head_key l') (TL l')) l') * frame`, `k`] assume_tac) >>
  rfs[AC STAR_ASSOC STAR_COMM] >>
  qexistsl [`(FibTree k v' l'::t1)`,`t2`] >> simp[]
QED

(*The outside world already set the flag to T!*)
Definition empty_node_def:
  empty_node k (v,e) = ones k [v; FST e; b2w T; b2w F;k;k;0w;0w; n2w 0] *
    edges_ones (FST e) (SND e) * cond(k <> 0w)
End

Definition full_node_def:
  full_node k (v,e) =
   if k = 0w then emp else
   SEP_EXISTS m b n p c r.
   ones k [v; FST e; b2w T;b2w m;b;n;p;c;r] *
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

val test_fts_mem = “fts_mem (ann_fts 0w [
    FibTree 10w (
    fill_dnode 11w (1000w, [(50w,10)]) F) [];
    FibTree 50w (
    fill_dnode 51w (2000w, [(10w,50)]) F) [
        FibTree 100w
        (fill_dnode 101w (3000w, []) F) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,head_key_t_def,head_key_def,last_key_def,REVERSE_DEF,ft_mem_def,ones_def,edges_ones_def,LENGTH,b2w_def,fill_anode_def,fill_dnode_def];
(*
val tfc = “test_full_conn (10000w:word64) 3 3” |> SCONV [test_full_conn_def];
*)
val test_large_fts_mem = “fts_mem (ann_fts 0w [
    test_build_ft (1000w:word64) 2 (test_full_conn 10000w 3 3)
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,test_full_conn_def,
    head_key_t_def,head_key_def,last_key_def,REVERSE_DEF,ft_mem_def,
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






(*-------------------------------------------------------------------*

   Old Definitions and Thereoms. Maybe delete at the end!

 *-------------------------------------------------------------------*)


(*
Currently, not in use!




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
    fs[head_key_def,head_key_t_def] >>
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
      fts_mem (ann_fts 0w fts) *
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

    Allow insertion of 0w -> just return the old list!
    Makes related operations easier!
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

*)

(*

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
  first_x_assum (qspec_then `v.mark` assume_tac) >> rfs[head_key_def,
    head_key_t_def, fill_dnode_def] >>
  fs[data_node_component_equality]
QED

Theorem lemma_non_empty_list:
  !fh fts. (fib_heap_inv fh fts /\ head_key fts <> 0w) ==> fts <> []
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  Cases_on `fts` >>
  fs[head_key_def,head_key_t_def]
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
  fs[Once fts_has_cases,fill_dnode_def,data_node_component_equality]
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

*)

(*

Lemmas for logical verification of inserting one elment into the heap.
Currently, not in use!

(* New smallest elemet *)
Theorem lemma_insert_new_min_inv:
  !fh fts k v e.
    k <> 0w /\
    FLOOKUP fh k = NONE /\
    fib_heap_inv fh fts /\
    (v <=+ fts_hd_value fts) ==>
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
    fs[head_key_def, head_key_t_def,FLOOKUP_SIMP, fts_is_min_def] >>
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
    simp[fill_dnode_def,data_node_component_equality] >>
    strip_tac >>
    last_assum (qspecl_then [`v''.value`, `v''.edges`] assume_tac) >>
    gvs[head_key_def,head_key_t_def] >>
    fs[fts_hd_value_def] >>
    dxrule_all lemma_lower_eq_fts_is_min >> simp[]
  ) >>
  fs[fib_heap_shape_ok_def] >>
  simp[fts_size_def, Ntimes fib_num_def 3] >>
  simp[Once fib_num_def]
QED

Theorem lemma_insert_old_min_inv:
  !fh fts k v e.
    k <> 0w /\
    FLOOKUP fh k = NONE /\
    fib_heap_inv fh fts /\
    ~(v <=+ fts_hd_value fts) ==>
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
      fs[head_key_def,head_key_t_def,fts_hd_value_def] >>
      Cases_on `k = k'`
      >- (
        first_x_assum(qspecl_then [`k'`,`v''.value`,`v''.edges`] assume_tac) >>
        gvs[FLOOKUP_SIMP] >>
        first_x_assum(qspec_then `v''.mark` assume_tac) >>
        fs[Once fts_has_cases] >>
        fs[fill_dnode_def,data_node_component_equality]
        ) >>
      fs[FLOOKUP_SIMP]
      ) >>
    Cases_on `fts`
    >- (
       fs[head_key_def,head_key_t_def,FLOOKUP_SIMP] >>
       simp[fts_is_min_def,fill_dnode_def]
       ) >>
    Cases_on `h` >>
    fs[head_key_def,fts_hd_value_def,head_key_t_def] >>
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
  simp[Ntimes fib_num_def 3, fts_size_def] >>
  simp[Once fib_num_def]
QED

*)

(*

Inserts a single element into a list of FTS.
Currently, not in use!

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
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    gvs[] >>
    assume_tac fib_heap_empty_append_inv >>
    gs[fill_dnode_def]
    ) >>
  assume_tac lemma_non_empty_heap >>
  first_x_assum (qspecl_then [`fh`, `fts`] assume_tac) >>
  Cases_on `fts` >> gvs[] >>
  Cases_on `h` >>
  Cases_on `t` using SNOC_CASES >>
  fs[SNOC_APPEND,head_key_def,head_key_t_def]
  >- (
    fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    `k + 2w * bytes_in_word <> k'` by SEP_NEQ_TAC >> simp[] >>
    SEP_R_TAC >>
    IF_CASES_TAC
    >- (
      fs[fib_heap_append_def,before_off_def,next_off_def] >>
      fs[head_key_def,last_key_def,last_key_t_def,head_key_t_def] >>
      SEP_R_TAC >>
      IF_CASES_TAC >> fs[] >>
      SEP_R_TAC >> simp[] >>
      strip_tac >> gvs[] >>
      SEP_W_TAC >>
      qexists `[FibTree a' (fill_dnode v e F) []; FibTree k' v' l]` >>
      simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
           fts_mem_def, SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
           fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
      mp_tac lemma_insert_new_min_inv >>
      disch_then (qspecl_then
          [`fh`, `[FibTree k' v' l]`, `a'`, `v`, `e`] assume_tac) >>
      fs[fts_hd_value_def,fill_dnode_def]
      ) >>
    fs[fib_heap_append_def,before_off_def,next_off_def] >>
    SEP_R_TAC >>
    IF_CASES_TAC >> fs[] >>
    fs[head_key_def, head_key_t_def,last_key_def,last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' v' l; FibTree k (fill_dnode v e F) []]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[AC STAR_COMM STAR_ASSOC] >>
    fs[STAR_ASSOC] >>
    mp_tac lemma_insert_old_min_inv >>
    disch_then (qspecl_then [`fh`, `[FibTree a' v' l]`,`k`,`v`,`e`]
      assume_tac) >>
    fs[fts_hd_value_def, fill_dnode_def]
   ) >>
  Cases_on `x` >>
  rename [`fib_heap_inv fh (FibTree k' v' l::(l' ++ [FibTree lk lv ts]))`] >>
  Cases_on `l'` >>
  fs[head_key_def, head_key_t_def]
  >- (
    fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    `k' <> lk` by SEP_NEQ_TAC >> simp[] >>
    SEP_R_TAC >>
    IF_CASES_TAC
    >- (
      simp[fib_heap_append_def,before_off_def,next_off_def] >>
      SEP_R_TAC >>
      fs[last_key_def,head_key_def,head_key_t_def,last_key_t_def] >>
      SEP_R_TAC >> simp[] >>
      strip_tac >> gvs[] >>
      SEP_W_TAC >>
      qexists `[FibTree a' (fill_dnode v e F) []; FibTree lk lv ts;
                FibTree k' v' l]` >>
      simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
           fts_mem_def, SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
           fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
      fs[AC STAR_COMM STAR_ASSOC] >>
      fs[STAR_ASSOC] >>
      qspecl_then [`fh`, `[FibTree k' v' l;FibTree lk lv ts]`, `a'`,
                               `v`,`e`] assume_tac lemma_insert_new_min_inv >>
      rfs[fts_hd_value_def] >>
      qspecl_then [`fh |+ (a',v,e)`,`a'`,`(fill_dnode v e F)`,`[]`,
        `[FibTree k' v' l]`,`[FibTree lk lv ts]`] assume_tac fib_heap_inv_ul_thm >>
      rfs[fill_dnode_def]
      ) >>
    simp[fib_heap_append_def,before_off_def,next_off_def] >>
    fs[last_key_def,head_key_def,head_key_t_def,last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' v' l; FibTree lk lv ts;
              FibTree k (fill_dnode v e F) []]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[AC STAR_COMM STAR_ASSOC] >>
    fs[STAR_ASSOC] >>
    mp_tac lemma_insert_old_min_inv >>
    disch_then (qspecl_then [`fh`, `[FibTree a' v' l; FibTree lk lv ts]`,
                             `k`,`v`,`e`] assume_tac) >>
    fs[fts_hd_value_def, fill_dnode_def]
   ) >>
  qspecl_then [`FibTree k' v' l::h::t`, `[FibTree lk lv ts]`]
    assume_tac ann_fts_append_thm >>
  fs[] >>
  pop_assum kall_tac >>
  Cases_on `h` >>
  fs[head_key_def, head_key_t_def] >>
  fs[fts_mem_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  rename [`fib_heap_inv fh (FibTree fk fv fts::FibTree sk sv sts::
           (t ++ [FibTree lk lv lts]))`] >>
  SEP_R_TAC >>
  `fk <> sk` by SEP_NEQ_TAC >>
  IF_CASES_TAC
  >- (
    simp[fib_heap_append_def,before_off_def,next_off_def] >>
    fs[last_key_def,head_key_def,head_key_t_def,last_key_t_def] >>
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    qexists `[FibTree a' (fill_dnode v e F) []; FibTree sk sv sts] ++
              t ++ [FibTree lk lv lts] ++ [FibTree fk fv fts]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    simp[ann_fts_seg_append_thm,fts_mem_append_thm, STAR_ASSOC,
         head_key_t_def,head_key_def] >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[last_key_t_def,head_key_def,REVERSE_APPEND,head_key_t_def] >>
    fs[head_key_t_append_thm,lemma_head_keys_eq_last_key_t] >>
    fs[head_key_t_pull_last_thm] >>
    simp[last_key_t_append_thm,last_key_t_def,head_key_t_def] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    fs[STAR_ASSOC] >>
    qspecl_then [`fh`, `(FibTree fk fv fts::FibTree sk sv sts::t) ++
      [FibTree lk lv lts]`, `a'`, `v`,`e`] assume_tac lemma_insert_new_min_inv >>
    rfs[fts_hd_value_def] >>
    qspecl_then [`fh |+ (a',v,e)`,`a'`,`(fill_dnode v e F)`,`[]`,
      `[FibTree fk fv fts]`,`(FibTree sk sv sts::t) ++ [FibTree lk lv lts]`]
      assume_tac fib_heap_inv_ul_thm >>
    rfs[fill_dnode_def]
    ) >>
  simp[fib_heap_append_def,before_off_def,next_off_def] >>
  fs[last_key_def, head_key_def, head_key_t_def,last_key_t_def] >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  SEP_W_TAC >>
  qexists `[FibTree a' fv fts; FibTree sk sv sts] ++ t ++
           [FibTree lk lv lts; FibTree k (fill_dnode v e F) []]` >>
  fs[head_key_def,head_key_t_def,last_key_def,head_key_append_thm] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_append_thm, STAR_ASSOC] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[head_key_t_append_thm, last_key_t_def, head_key_t_def,
     head_key_def, REVERSE_APPEND] >>
  fs[lemma_head_keys_eq_last_key_t]>>
  qspecl_then[`t ++ [FibTree lk lv lts]`,`k`,`(fill_dnode v e F)`, `[]`]
    mp_tac head_key_t_pull_last_thm >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  disch_tac >> fs[fill_dnode_def] >>
  simp[head_key_t_pull_last_thm] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  qspecl_then[`fh`, `(FibTree a' fv fts::FibTree sk sv sts::t) ++
    [FibTree lk lv lts]`, `k`, `v`, `e`] assume_tac lemma_insert_old_min_inv >>
  rfs[fts_hd_value_def,fill_dnode_def] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  disch_tac >> simp[]
QED

*)







(*
Theorem lemma_fib_heap_insert_mem:
  !frame xs fts k a.
    (fts_mem (ann_fts xs) * fts_mem (ann_fts fts) * frame *
     cond(head_key xs = k /\ head_key fts = a))
      (fun2set (m,dm)) /\ fib_heap_merge (a, k, m, dm) = (a', m', b) ==>
    ?fts'.
    (fts_mem(ann_fts (fts')) * frame * cond(a' = head_key (fts')))
      (fun2set (m',dm)) /\ b
Proof
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    fs[flat_fts_def, fts_mem_def, ann_fts_def,SEP_CLAUSES,head_key_def] >>
    simp[fib_heap_merge_def] >>
    strip_tac >>
    qexists `fts` >> gvs[]
    ) >>
  Cases_on `h`>> gvs[head_key_def] >>
  Cases_on `fts` >> simp[head_key_def,next_off_def,before_off_def]
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    fs[fib_heap_merge_def] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    qexists `(FibTree a' v l::t)` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    ) >>
  Cases_on `t` using SNOC_CASES
  >- (
    qspecl_then [`frame`,`FibTree k v l`,`h::t'`,`k`,`head_key(h::t')`]
      assume_tac lemma_fib_heap_insert_1intoN >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    rfs[] >>
    fs[head_key_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  rename [`(fts_mem (ann_fts (FibTree xk xv xl::(xs ++ [FibTree xk' xv' xl']))) *
         fts_mem (ann_fts (h::fts)) * frame) (fun2set (m,dm))`] >>
  Cases_on `fts` using SNOC_CASES
  >- (
    qspecl_then [`frame`,`(FibTree xk xv xl::(xs ++ [FibTree xk' xv' xl']))`,
      `h`, `xk`, `head_key [h]`] assume_tac lemma_fib_heap_insert_Ninto1 >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    rfs[] >>
    fs[head_key_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  Cases_on `h` >>
  rename [`fib_heap_merge (head_key (FibTree fk fv fl::(fts ++
    [FibTree lk lv ll])),xk,m,dm)`] >>
  simp[head_key_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
     head_key_t_def, ones_def, STAR_ASSOC,REVERSE_APPEND,
     fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_merge_def,before_off_def,next_off_def,
       last_key_t_def,head_key_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  SEP_W_TAC >>
  strip_tac >> gvs[]
  >- (
    qexists `(FibTree a' xv xl::xs) ++ [FibTree xk' xv' xl'] ++
             (FibTree fk fv fl::fts) ++ [FibTree lk lv ll]` >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
         head_key_t_def, ones_def, STAR_ASSOC, REVERSE_APPEND,
         fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
    simp[last_key_t_append_thm,head_key_t_append_thm] >>
    simp[head_key_t_pull_last_thm] >>
    simp[last_key_t_def,lemma_head_key_eq_last_key_t] >>
    simp[head_key_def]
    ) >>
  qexists `(FibTree a' fv fl::fts) ++ [FibTree lk lv ll] ++
           (FibTree xk xv xl::xs) ++ [FibTree xk' xv' xl']` >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
       head_key_t_def, ones_def, STAR_ASSOC, REVERSE_APPEND,
       fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
  simp[last_key_t_append_thm,head_key_t_append_thm] >>
  simp[head_key_t_pull_last_thm] >>
  simp[last_key_t_def,lemma_head_key_eq_last_key_t] >>
  simp[head_key_def] >>
  fs[AC STAR_COMM STAR_ASSOC]
QED

*)


(*
Currently, not used.

Definition list_keys_not_null_def:
  (list_keys_not_null [] <=> T) /\
  (list_keys_not_null (FibTree k v xs::rest) <=>
    k <> 0w /\ list_keys_not_null xs /\ list_keys_not_null rest)
End



Theorem fts_key_not_null:
  !n fts k. list_keys_not_null fts /\ fts_has k n fts ==> k <> 0w
Proof
  strip_tac >>
  ho_match_mp_tac list_keys_not_null_ind >>
  rpt strip_tac
  >- fs[Once fts_has_cases] >>
  fs[list_keys_not_null_def] >>
  qpat_x_assum `fts_has 0w n (FibTree k fts fts'::fts'')` mp_tac >>
  simp[Once fts_has_cases]
QED


*)



(*---------------------------------------------------------

  FH invariant + theorems and lemmas for its properties

-----------------------------------------------------------*)

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


Theorem fts_has_sym_thm:
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






Definition fts_hd_value_def:
  (fts_hd_value ([] : ('a word, 'a data_node) fts) = -1w ) /\
  (fts_hd_value (FibTree k v _::_) = v.value)
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






Definition fts_size_def:
  (fts_size [] = 0:num) /\
  (fts_size (FibTree _ _ ts::rest) = 1 + fts_size ts + fts_size rest)
End

Theorem fts_size_append_thm:
  !xs ys.
  fts_size (xs ++ ys) = (fts_size xs) + (fts_size ys)
Proof
  ho_match_mp_tac fts_size_ind >>
  rpt strip_tac >> simp[fts_size_def]
QED





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
    (fib_num ((LENGTH ys) + 2) <= 1 + fts_size ys) /\
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






Definition fts_has_inj_def:
  fts_has_inj fts <=>
    !k v v'. fts_has k v fts /\ fts_has k v' fts ==> v = v'
End


Theorem fts_has_inj_append:
  fts_has_inj (xs ++ ys) <=>
    fts_has_inj xs /\ fts_has_inj ys /\
    !k v v'. fts_has k v xs /\ fts_has k v' ys ==> v = v'
Proof
  simp[fts_has_inj_def] >>
  simp[fts_has_append_thm] >>
  iff_tac
  >- (rpt strip_tac >> res_tac) >>
  rpt strip_tac >> res_tac >> simp[]
QED


Theorem fts_has_inj_append_sym:
  fts_has_inj (xs ++ ys) <=> fts_has_inj (ys ++ xs)
Proof
  simp[fts_has_inj_def,fts_has_inj_append] >>
  iff_tac >> rpt strip_tac >> res_tac >> simp[]
QED



Theorem lemma_fts_has_inj_ts:
  !k v l xs.
  fts_has_inj (FibTree k v l::xs) ==>
  fts_has_inj l /\
  fts_has_inj xs
Proof
  rpt strip_tac >>
  fs[fts_has_inj_def] >>
  rpt strip_tac >>
  first_x_assum(qspecl_then [`k'`,`v'`,`v''`] assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases]
QED



Theorem lemma_fts_has_inj_sym_succ:
  fts_has_inj (FibTree k v (xs ++ ys)::rest) ==>
  fts_has_inj (FibTree k v (ys ++ xs)::rest)
Proof
  fs[fts_has_inj_def] >>
  rpt strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >> once_rewrite_tac[fts_has_cases] >>
  simp[] >>
  rpt strip_tac >> gvs[]
  >- (
    first_x_assum (qspecl_then [`k`,`v`,`v''`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[]
    )
  >- (
    first_x_assum (qspecl_then [`k`,`v`,`v''`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    fs[fts_has_append_thm]
    )
  >- (
    first_x_assum (qspecl_then [`k`,`v`,`v'`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[]
    )
  >- (
    fs[GSYM fts_has_inj_def] >>
    imp_res_tac lemma_fts_has_inj_ts >>
    fs[fts_has_inj_def] >> res_tac
    )
  >- (
    first_x_assum (qspecl_then [`k'`,`v'`,`v''`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    fs[fts_has_append_thm]
    )
  >- (
    first_x_assum (qspecl_then [`k`,`v`,`v'`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    fs[fts_has_append_thm]
    )
  >- (
    first_x_assum (qspecl_then [`k'`,`v'`,`v''`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    fs[fts_has_append_thm]
    ) >>
  first_x_assum (qspecl_then [`k'`,`v'`,`v''`] assume_tac) >>
  pop_assum mp_tac >>
  once_rewrite_tac[fts_has_cases] >> simp[] >>
  fs[fts_has_append_thm]
QED



Definition fts_all_dist_def:
  (fts_all_dist [] <=> T) /\
  (fts_all_dist (FibTree k v ts::fts) <=>
    fts_has_inj (FibTree k v ts::fts) /\
    (!v. ~fts_has k v ts /\ ~fts_has k v fts) /\
    (fts_all_dist ts) /\ (fts_all_dist fts) /\
    (!k v. fts_has k v ts ==> ~fts_has k v fts))
End


Theorem lemma_fts_all_dist_append_rl:
  !xs ys.
    fts_has_inj (xs ++ ys) /\
    fts_all_dist xs /\ fts_all_dist ys /\
    (!k v. fts_has k v xs ==> ~fts_has k v ys) ==>
    fts_all_dist (xs ++ ys)
Proof
  ho_match_mp_tac fts_all_dist_ind >>
  rpt strip_tac >> fs[] >>
  fs[fts_all_dist_def] >>
  rpt strip_tac >>
  rename [`(FibTree k n l::xs)`]
  >- (
    fs[fts_has_append_thm]
    >- res_tac >>
    qpat_x_assum `fts_has_inj (FibTree k n l::(xs ++ ys))` mp_tac >>
    pure_rewrite_tac[cj 2 (GSYM APPEND)] >>
    strip_tac >>
    fs[fts_has_inj_append] >>
    fs[Once MONO_NOT_EQ] >>
    `~fts_has k v (FibTree k n l::xs)` by res_tac >>
    pop_assum mp_tac >> pure_rewrite_tac[Once fts_has_cases] >>
    spose_not_then assume_tac >>
    first_x_assum(qspecl_then [`k`,`n`,`v`] assume_tac) >>
    rfs[] >>
    pop_assum mp_tac >>
    pure_rewrite_tac[Once fts_has_cases] >>
    simp[]
    )
  >- (
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    strip_tac >> fs[] >>
    qspecl_then [`k`,`n`, `l`,`xs ++ ys`] assume_tac lemma_fts_has_inj_ts >>
    `fts_has_inj (xs ++ ys)` by res_tac >>
    `(!k v. fts_has k v xs ⇒ ¬fts_has k v ys)
     ⇒ fts_all_dist (xs ++ ys)` by res_tac >>
    fs[]
    ) >>
  fs[fts_has_append_thm]
  >- res_tac >>
  first_x_assum (qspecl_then [`k'`,`v`] assume_tac) >>
  qpat_x_assum `fts_has k' v (FibTree k n l::xs) ⇒
    ¬fts_has k' v ys` mp_tac >>
  pure_rewrite_tac[Once fts_has_cases] >>
  strip_tac >> fs[] >>
  res_tac
QED


Theorem lemma_fts_all_dist_append_lr:
  !xs ys.
    fts_all_dist (xs ++ ys) ==>
    (fts_has_inj (xs ++ ys) /\
    fts_all_dist xs /\ fts_all_dist ys /\
    (!k v. fts_has k v xs ==> ~fts_has k v ys))
Proof
  ho_match_mp_tac fts_all_dist_ind >>
  rpt strip_tac >> fs[]
  >- (
    Cases_on `ys`
    >- fs[fts_has_inj_def, Once fts_has_cases] >>
    Cases_on `h` >> fs[fts_all_dist_def]
    )
  >- simp[fts_all_dist_def]
  >- fs[Once fts_has_cases]
  >- fs[fts_all_dist_def]
  >- (
    fs[fts_all_dist_def] >>
    res_tac >> simp[] >>
    fs[fts_has_append_thm] >>
    qpat_x_assum `fts_has_inj (FibTree k xs xs'::(xs'' ++ ys))` mp_tac >>
    pure_rewrite_tac[cj 2 (GSYM APPEND)] >>
    strip_tac >>
    fs[fts_has_inj_append]
    )
  >- fs[fts_all_dist_def] >>
  fs[fts_all_dist_def] >>
  fs[PULL_FORALL] >>
  qpat_x_assum `fts_has k' v (FibTree k xs xs'::xs'')` mp_tac >>
  pure_rewrite_tac[Once fts_has_cases] >> simp[] >>
  rpt strip_tac
  >- gvs[fts_has_append_thm]
  >- res_tac >>
  res_tac >>
  qpat_x_assum `¬fts_has k' v (xs'' ++ ys)` mp_tac >>
  once_rewrite_tac[IMP_F] >>
  once_rewrite_tac[NOT_CLAUSES] >>
  pure_rewrite_tac[fts_has_append_thm] >>
  simp[]
QED


Theorem fts_all_dist_append_thm:
  !xs ys.
    fts_all_dist (xs ++ ys) <=>
    (fts_has_inj (xs ++ ys) /\
    fts_all_dist xs /\ fts_all_dist ys /\
    (!k v. fts_has k v xs ==> ~fts_has k v ys))
Proof
  rpt gen_tac >>
  iff_tac
  >- (
    strip_tac >>
    drule_all lemma_fts_all_dist_append_lr >>
    rpt strip_tac >> fs[] >> res_tac
    ) >>
 fs[lemma_fts_all_dist_append_rl]
QED


Theorem fts_all_dist_sym_thm:
  !xs ys. fts_all_dist (xs ++ ys) <=> fts_all_dist (ys ++ xs)
Proof
  simp[fts_all_dist_append_thm] >>
  rpt strip_tac >>
  fs[fts_has_inj_append] >> rpt strip_tac >> res_tac >> simp[] >>
  res_tac >> simp[] >>
  iff_tac
  >- (
    disch_tac >>
    simp[AC CONJ_ASSOC CONJ_COMM] >> fs[] >>
    pop_assum mp_tac >>
    rpt strip_tac >> res_tac >> simp[]
    ) >>
  disch_tac >>
  simp[AC CONJ_ASSOC CONJ_COMM] >> fs[] >>
  pop_assum mp_tac >>
  rpt strip_tac >> res_tac >> simp[]
QED


Theorem lemma_fts_all_dist_sym_succ:
  fts_all_dist (FibTree k v (xs ++ ys)::rest) ==>
  fts_all_dist (FibTree k v (ys ++ xs)::rest)
Proof
  fs[fts_all_dist_def] >>
  rpt strip_tac
  >- fs[lemma_fts_has_inj_sym_succ]
  >- (fs[fts_has_append_thm] >> res_tac)
  >- fs[fts_all_dist_sym_thm] >>
  fs[fts_has_append_thm] >> res_tac
QED



Definition fts_head_is_min_def:
  (fts_head_is_min [] <=> T) /\
  (fts_head_is_min (FibTree _ v _::fts) <=>
    !k n l. MEM (FibTree k n l) fts ==> v.value <=+ n.value )
End

Theorem fts_head_is_min_append_thm:
  !xs ys.
    fts_hd_value xs <=+ fts_hd_value ys /\
    fts_head_is_min xs /\ fts_head_is_min ys ==>
    fts_head_is_min(xs ++ ys)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> simp[fts_hd_value_def,fts_head_is_min_def] >>
  Cases_on `ys` >> simp[fts_hd_value_def,fts_head_is_min_def] >>
  Cases_on `h` >>
  Cases_on `h'` >>
  rpt strip_tac >>
  fs[fts_head_is_min_def] >>
  rpt strip_tac
  >- res_tac
  >- gvs[fts_hd_value_def] >>
  fs[fts_hd_value_def] >>
  res_tac >>
  dxrule_all WORD_LOWER_EQ_TRANS >>
  simp[]
QED






Definition fts_parent_lower_eq_def:
  (fts_parent_lower_eq [] <=> T) /\
  (fts_parent_lower_eq (FibTree k v l::ts) <=>
    (fts_is_min v.value l) /\ fts_parent_lower_eq ts)
End


Theorem fts_parent_lower_eq_append_thm:
  !xs.
  fts_parent_lower_eq (xs ++ ys) <=> fts_parent_lower_eq xs /\ fts_parent_lower_eq ys
Proof
  ho_match_mp_tac fts_parent_lower_eq_ind >>
  rpt strip_tac
  >- fs[fts_parent_lower_eq_def] >>
  simp[fts_parent_lower_eq_def] >>
  simp[CONJ_ASSOC]
QED

Theorem fts_parent_lower_eq_sym_thm:
  fts_parent_lower_eq (xs ++ ys) <=> fts_parent_lower_eq (ys ++ xs)
Proof
  simp[fts_parent_lower_eq_append_thm] >>
  simp[CONJ_COMM]
QED




Definition every_fts_def:
  every_fts P xs <=>
    P xs /\ !k v l. MEM(FibTree k v l) xs ==> every_fts P l
End



Theorem lemma_every_fts_parent_lower_eq_sym:
  every_fts fts_parent_lower_eq (xs ++ ys) <=>
  every_fts fts_parent_lower_eq (ys ++ xs)
Proof
  once_rewrite_tac[every_fts_def] >>
  simp[fts_parent_lower_eq_sym_thm] >>
  iff_tac >> rpt strip_tac >> fs[] >> res_tac >> simp[]
QED


Definition fib_heap_inv_def:
  fib_heap_inv fh (fts: ('a word, 'a data_node) fts) ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\
    (∀k v e. FLOOKUP fh k = SOME (v,e) <=>
      ?m. fts_has k (fill_dnode v e m) fts) /\
    (fts_all_dist fts) /\
    (fts_is_min (fts_hd_value fts) fts) /\
    (every_fts fts_parent_lower_eq fts) /\
    (*(every_fts fts_head_is_min fts) /\*)
    (fib_heap_shape_ok fts)
End

Theorem lemma_flookup_funion_comm:
  !fh1 fh2 k.
    DISJOINT (FDOM fh1) (FDOM fh2) ==>
    FLOOKUP (FUNION fh1 fh2) k = FLOOKUP (FUNION fh2 fh1) k
Proof
  rpt strip_tac >>
  simp[FLOOKUP_SIMP] >>
  Cases_on `k IN (FDOM fh1)`
  >- (
    fs[FLOOKUP_DEF] >>
    fs[DISJOINT_ALT]
    ) >>
  fs[FLOOKUP_DEF] >>
  Cases_on `k IN (FDOM fh2)` >> fs[]
QED


Theorem fib_heap_inv_comm_thm:
  !fh1 fh2 xs.
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    fib_heap_inv (FUNION fh1 fh2) xs
    ==>
    fib_heap_inv (FUNION fh2 fh1) xs
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  drule_all lemma_flookup_funion_comm >> strip_tac >>
  rpt strip_tac
  >- (first_x_assum (qspec_then `0w` assume_tac) >> gvs[]) >>
  first_x_assum (qspec_then `k` assume_tac) >>
  iff_tac >> strip_tac >> gvs[]
  >- (qexists `m` >> simp[]) >>
  res_tac >> gvs[]
QED



Theorem lemma_empty_list2:
  !fh fts.  (fib_heap_inv fh fts /\ head_key fts = 0w) ==> fts = []
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  Cases_on `fts` >> fs[] >>
  Cases_on `h` >>
  Cases_on `FLOOKUP fh 0w` >> fs[] >>
  last_x_assum (qspecl_then [`k`, `v.value`, `v.edges`] assume_tac) >>
  gvs[head_key_def,head_key_t_def] >>
  fs[Once fts_has_cases] >>
  first_x_assum (qspec_then `v.mark` assume_tac) >>
  rfs[head_key_def, head_key_t_def, fill_dnode_def] >>
  fs[data_node_component_equality]
QED


Theorem lemma_empty_map:
  !fh. (!k v e. FLOOKUP fh k <> SOME (v,e)) ==> fh = FEMPTY
Proof
  Cases_on `fh`
  >- simp[] >>
  rpt strip_tac >>
  PairCases_on `y` >>
  first_x_assum(qspecl_then [`x`,`y0`,`y1`] assume_tac) >>
  fs[FLOOKUP_SIMP]
QED


Theorem lemma_empty_heap:
  fib_heap_inv fh [] ==> fh = FEMPTY
Proof
  simp[fib_heap_inv_def] >>
  rpt strip_tac >>
  fs[Once fts_has_cases] >>
  Cases_on `fh` >> fs[] >>
  first_x_assum(qspecl_then [`x`,`FST y`,`SND y`] assume_tac) >>
  fs[FLOOKUP_SIMP]
QED


Theorem lemma_empty_heap2:
  !fh fts.
  (fib_heap_inv fh fts /\ head_key fts = 0w) ==>
      (fts = [] /\ fh = FEMPTY)
Proof
  assume_tac lemma_empty_list2 >>
  rpt gen_tac >>
  strip_tac >>
  res_tac >> gvs[] >>
  fs[fib_heap_inv_def] >>
  Cases_on `fh` >> rw[] >>
  Cases_on `y` >>
  rename [`x,(v,e)`] >>
  last_x_assum (qspecl_then [`x`,`v`,`e`] assume_tac) >>
  fs[Once fts_has_cases, FLOOKUP_DEF]
QED

Theorem fib_heap_inv_empty_thm:
  fib_heap_inv FEMPTY []
Proof
  simp[fib_heap_inv_def] >>
  simp[Once fts_has_cases, fts_all_dist_def,fts_is_min_def,Once every_fts_def,
       fts_parent_lower_eq_def, fib_heap_shape_ok_def]
QED



Definition fib_heap_def:
  fib_heap a fh =
    SEP_EXISTS fts.
      fts_mem (ann_fts 0w fts) *
      cond (fib_heap_inv fh fts /\ a = head_key fts)
End






(* ------------------------------------------------------

  Logical FTS merge. (High-Level implementation)

--------------------------------------------------------*)


Definition fts_merge_def:
  (fts_merge [] ys = ys) /\
  (fts_merge xs [] = xs) /\
  (fts_merge (FibTree k1 v1 l1::xs) (FibTree k2 v2 l2::ys) =
    if v1.value <=+ v2.value then
      (FibTree k1 v1 l1::(xs ++ (FibTree k2 v2 l2::ys)))
    else
      (FibTree k2 v2 l2::(ys ++ (FibTree k1 v1 l1::xs))))
End




Theorem lemma_lower_eq_fts_is_min:
  !v v' fts. v <=+ v' /\ fts_is_min v' fts ==> fts_is_min v fts
Proof
  gen_tac >>
  ho_match_mp_tac fts_is_min_ind >>
  simp[fts_is_min_def] >>
  rpt strip_tac >>
  imp_res_tac WORD_LOWER_EQ_TRANS
QED




Theorem lemma_merge_heaps_new_min:
  fts_hd_value xs <=+ fts_hd_value ys /\
  fts_is_min (fts_hd_value ys) ys /\
  fts_is_min (fts_hd_value xs) xs ==>
  fts_is_min (fts_hd_value (xs ++ ys)) (xs ++ ys)
Proof
  simp[fts_is_min_append_thm] >>
  Cases_on `xs` >> simp[fts_is_min_def] >>
  Cases_on `h` >>
  simp[fts_hd_value_def] >>
  rpt strip_tac >>
  pop_assum kall_tac >>
  drule_all lemma_lower_eq_fts_is_min >> simp[]
QED




Theorem lemma_merge_all_dist:
  (!k v e. FLOOKUP fh1 k = SOME (v,e) ⇔ ∃m. fts_has k (fill_dnode v e m) xs) /\
  (∀k v e. FLOOKUP fh2 k = SOME (v,e) ⇔ ∃m. fts_has k (fill_dnode v e m) ys) /\
  fts_all_dist xs /\
  fts_all_dist ys /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  fts_all_dist (xs ++ ys)
Proof
  simp[fts_all_dist_append_thm] >>
  Cases_on `xs` >>
  rpt strip_tac >> fs[]
  >- (
    Cases_on `ys` >> fs[fts_has_inj_def]
    >- simp[Once fts_has_cases] >>
    Cases_on `h` >> fs[fts_all_dist_def,fts_has_inj_def]
    )
  >- fs[Once fts_has_cases]
  >- (
    Cases_on `h` >>
    pure_rewrite_tac[GSYM(cj 2 APPEND)] >>
    simp[fts_has_inj_append] >>
    fs[fts_all_dist_def] >>
    strip_tac
    >- (
      Cases_on `ys` >> fs[fts_has_inj_def]
      >- simp[Once fts_has_cases] >>
      Cases_on `h` >>
      fs[fts_all_dist_def,fts_has_inj_def]
      ) >>
    rpt strip_tac >>
    fs[EQ_IMP_THM] >>
    first_x_assum $ qspecl_then [`k'`,`v''.value`,`v''.edges`] assume_tac >>
    first_x_assum $ qspecl_then [`k'`,`v'.value`,`v'.edges`] assume_tac >>
    fs[] >>
    fs[PULL_EXISTS] >>
    first_x_assum $ qspec_then `v'.mark` assume_tac >>
    first_x_assum $ qspec_then `v''.mark` assume_tac >>
    fs[fill_dnode_def] >>
    rfs[lemma_data_node_cases] >>
    fs[FLOOKUP_DEF] >>
    fs[DISJOINT_ALT] >>
    res_tac
    ) >>
  pop_assum mp_tac >> simp[] >>
  Cases_on `h` >>
  last_assum(qspecl_then [`k`,`v.value`,`v.edges`] assume_tac) >>
  fs[EQ_IMP_THM] >>
  fs[PULL_EXISTS] >>
  first_x_assum (qspec_then `v.mark` assume_tac) >> fs[] >>
  pop_assum mp_tac >>
  simp[fill_dnode_def, data_node_component_equality] >>
  strip_tac >>
  rfs[lemma_data_node_cases] >>
  pop_assum mp_tac >>
  simp[FLOOKUP_DEF] >>
  strip_tac >>
  fs[DISJOINT_ALT] >>
  `k ∉ FDOM fh2` by res_tac >>
  first_x_assum $ qspecl_then [`k`,`v.value`,`v.edges`] assume_tac >>
  pop_assum mp_tac >>
  simp[FLOOKUP_DEF] >>
  strip_tac >>
  first_x_assum $ qspec_then `v.mark` assume_tac >>
  fs[fill_dnode_def,lemma_data_node_cases]
QED

Theorem lemma_merge_fts_has:
  (∀k v e. FLOOKUP fh1 k = SOME (v,e) ⇔ ∃m. fts_has k (fill_dnode v e m) xs) /\
  (∀k v e. FLOOKUP fh2 k = SOME (v,e) ⇔ ∃m. fts_has k (fill_dnode v e m) ys) /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  (FLOOKUP (fh1 ⊌ fh2) k = SOME (v,e) ⇔
  ∃m. fts_has k (fill_dnode v e m) (ys ++ xs))

Proof
  disch_tac >>
  iff_tac >> strip_tac
  >- (
    fs[FLOOKUP_FUNION] >>
    Cases_on `FLOOKUP fh1 k` >> gvs[] >>
    simp[fts_has_append_thm] >>
    res_tac >>
    qexists `m` >> simp[]
    ) >>
  fs[fts_has_append_thm] >> res_tac
  >- (
    drule_all lemma_flookup_funion_comm >> strip_tac >>
    res_tac >>
    first_x_assum $ qspec_then `k` assume_tac >>
    fs[FLOOKUP_SIMP] >>
    Cases_on `FLOOKUP fh2 k` >> gvs[]
    ) >>
  simp[FLOOKUP_SIMP]
QED




Theorem lemma_merge_heaps_inv:
  !fh1 fh2 xs ys.
  (fib_heap_inv fh1 xs) /\
  (fib_heap_inv fh2 ys) /\
  (DISJOINT (FDOM fh1) (FDOM fh2)) /\
  (fts_hd_value ys <=+ fts_hd_value xs) ==>
  (fib_heap_inv (FUNION fh1 fh2) (ys ++ xs))
Proof
  fs[fib_heap_inv_def] >>
  rpt strip_tac
  >- (
    fs[FLOOKUP_FUNION] >>
    Cases_on `FLOOKUP fh1 0w` >> fs[]
    )
  >- (imp_res_tac lemma_merge_fts_has >> simp[])
  >- (
    drule_all lemma_merge_all_dist >>
    strip_tac >>
    fs[fts_all_dist_sym_thm]
    )
  >- (drule_all lemma_merge_heaps_new_min >> simp[])
  >- (
    fs[Once every_fts_def] >>
    simp[fts_parent_lower_eq_append_thm] >>
    rpt strip_tac >> res_tac >> simp[]
    ) >>
  (*>- (
    simp[Once every_fts_def] >>
    qpat_x_assum `every_fts fts_head_is_min fts` mp_tac >>
    simp[Once every_fts_def] >> strip_tac >>
    qpat_x_assum `every_fts fts_head_is_min xs` mp_tac >>
    simp[Once every_fts_def] >> strip_tac >>
    simp[fts_head_is_min_append_thm] >>
    rpt strip_tac >> res_tac >> simp[]
    ) >> *)
  simp[fib_heap_shape_ok_append_thm]
QED


Theorem fts_merge:
  !fhx xs fhy ys fts.
  fib_heap_inv fhx xs /\
  fib_heap_inv fhy ys /\
  DISJOINT (FDOM fhx) (FDOM fhy) /\
  fts_merge xs ys = fts ==>
  fib_heap_inv (FUNION fhx fhy) fts
Proof
  rpt strip_tac >>
  Cases_on `xs` >> Cases_on `ys`
  >- (
    fs[fts_merge_def] >>
    simp[fib_heap_inv_def] >>
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fib_heap_inv_def]
    )
  >- (
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fts_merge_def]
    )
  >- (
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fts_merge_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  fs[fts_merge_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC
  >- (
    disch_tac >> gvs[] >>
    qspecl_then [`fhy`,`fhx`,`(FibTree k' v' l'::t')`,`(FibTree k v l::t)`]
      assume_tac lemma_merge_heaps_inv >>
    fs[fts_hd_value_def] >>
    fs[FUNION_COMM,DISJOINT_SYM] >>
    gvs[] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[APPEND] >>
    simp[]
    ) >>
  disch_tac >> gvs[] >>
  fs[WORD_NOT_LOWER_EQUAL] >>
  drule_all WORD_LOWER_IMP_LOWER_OR_EQ >>
  disch_tac >> gvs[] >>
  qspecl_then [`fhx`,`fhy`,`(FibTree k v l::t)`,`(FibTree k' v' l'::t')`]
    assume_tac lemma_merge_heaps_inv >>
  fs[fts_hd_value_def] >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[APPEND] >>
  simp[]
QED

(*--------------------------------------------------

  Memory Level Verification of Merging Heaps

--------------------------------------------------*)


(*assumption: both heads are the smallest element*)
Definition fib_heap_merge_def:
  fib_heap_merge
    (a1:'a word,a2:'a word,m:'a word -> 'a word, dm: 'a word set)
  =
    if a2 = 0w then (a1,m,T) else
    let c = (a2 IN dm) in
    if a1 = 0w then (*list a is empty*)
      (a2,m,c)
    else
      let c = (a1 IN dm /\ c) in

      let c = (a1 + before_off IN dm /\ c) in
      let l_a1 = m (a1 + before_off) in
      let c = (l_a1 + next_off IN dm /\ c) in

      let c = (a2 + before_off IN dm /\ c) in
      let l_a2 = m (a2 + before_off) in
      let c = (l_a2 + next_off IN dm /\ c) in

      let m = m (| (l_a1 + next_off) |-> a2|) in
      let m = m (| (a2 + before_off) |-> l_a1|) in
      let m = m (| (l_a2 + next_off) |-> a1|) in
      let m = m (| (a1 + before_off) |-> l_a2|) in

      let v_a2 = m a2 in
      let v_a1 = m a1 in
      if v_a2 <=+ v_a1 then
        (a2,m,c)
      else
        (a1,m,c)
End


Theorem lemma_fib_heap_insert_1into1:
  !frame x t p a' m dm m' b.
    (fts_mem (ann_fts p [x]) * fts_mem (ann_fts p [t]) * frame) (fun2set (m,dm)) /\
    fib_heap_merge(head_key [x],head_key [t],m,dm) = (a',m',b) ==>
    (fts_mem(ann_fts p ([x] ++ [t])) * frame)
    (fun2set (m',dm)) /\ b
Proof
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `x` >>
  gvs[head_key_def] >>
  Cases_on `t` >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_merge_def,before_off_def,next_off_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  SEP_W_TAC >>
  strip_tac >> gvs[]
QED


Theorem lemma_fib_heap_insert_1intoN:
  !frame x fts p m dm m' b.
    (fts_mem (ann_fts p [x]) * fts_mem (ann_fts p fts) * frame) (fun2set (m,dm)) /\
    fib_heap_merge(head_key [x],head_key fts,m,dm) = (a',m',b) ==>
    (fts_mem(ann_fts p ([x] ++ fts)) * frame)
    (fun2set (m',dm)) /\ b
Proof
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `x` >>
  gvs[head_key_def] >>
  Cases_on `fts`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    simp[fib_heap_merge_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[]
    ) >>
  Cases_on `h`>>
  Cases_on `t`using SNOC_CASES
  >- (
    qspecl_then [`frame`, `FibTree k v l`, `FibTree k' v' l'`,
      `p`,`a'`,`m`,`dm`,`m'`,`b`] assume_tac lemma_fib_heap_insert_1into1 >>
    strip_tac >>
    fs[head_key_t_def,head_key_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  rename [`FibTree fk fv fl::(fts ++ [FibTree lk lv ll])`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
     head_key_t_def, ones_def, STAR_ASSOC, REVERSE_APPEND,
     fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_merge_def,before_off_def,next_off_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  SEP_W_TAC >>
  strip_tac >> gvs[]
QED




Theorem lemma_fib_heap_insert_Ninto1:
  !frame xs y p m dm m' b.
    (fts_mem (ann_fts p xs) * fts_mem (ann_fts p [y]) * frame) (fun2set (m,dm)) /\
    fib_heap_merge(head_key xs,head_key [y],m,dm) = (a',m',b) ==>
    (fts_mem(ann_fts p (xs ++ [y])) * frame)
    (fun2set (m',dm)) /\ b
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `y` >>
  gvs[head_key_def] >>
  Cases_on `xs`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    simp[fib_heap_merge_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[]
    ) >>
  Cases_on `h`>>
  Cases_on `t`using SNOC_CASES
  >- (
    qspecl_then [`frame`, `FibTree k' v' l'`, `FibTree k v l`,
      `p`,`a'`,`m`,`dm`,`m'`,`b`] assume_tac lemma_fib_heap_insert_1into1 >>
    strip_tac >>
    fs[head_key_t_def,head_key_def]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND] >>
  rename [`FibTree fk fv fl::(fts ++ [FibTree lk lv ll])`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
     head_key_t_def, ones_def, STAR_ASSOC, REVERSE_APPEND,
     fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_merge_def,before_off_def,next_off_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  SEP_W_TAC >> fs[last_key_t_append_thm,last_key_t_def,head_key_t_def] >>
  strip_tac >> gvs[]
QED


Theorem lemma_fib_heap_insert_empty:
  !frame xs p m dm a' m' b.
    (fts_mem (ann_fts p xs) * fts_mem (ann_fts p []) * frame) (fun2set (m,dm)) /\
    fib_heap_merge (head_key xs, head_key [],m,dm) = (a',m',b) ⇒
    (fts_mem (ann_fts p (xs)) * frame) (fun2set (m',dm)) ∧ b
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    simp[fib_heap_merge_def] >>
    strip_tac >> gvs[]
    ) >>
  Cases_on`h` >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[fib_heap_merge_def] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  strip_tac >> gvs[] >>
  SEP_R_TAC
QED



Theorem lemma_fib_heap_insert_NintoN:
  !frame xs ys p m dm a' m' b.
    (fts_mem (ann_fts p xs) * fts_mem (ann_fts p ys) * frame)(fun2set (m,dm)) /\
    fib_heap_merge (head_key xs, head_key ys, m, dm) = (a', m', b) ==>
    (fts_mem(ann_fts p (xs ++ ys)) * frame)
      (fun2set (m',dm)) /\ b
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  Cases_on `ys`
  >- (
    qspecl_then [`frame`,`xs`,`p`,`m`,`dm`,`a'`,`m'`,`b`]
      assume_tac lemma_fib_heap_insert_empty >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    ) >>
  Cases_on `xs`
  >- (
    qspecl_then [`frame`,`(h::t)`,`p`,`m`,`dm`,`a'`,`m'`,`b`]
      assume_tac lemma_fib_heap_insert_empty >>
    gvs[AC STAR_ASSOC STAR_COMM] >>
    Cases_on `h` >>
    fs[head_key_t_def,head_key_def] >>
    simp[fib_heap_merge_def] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    strip_tac >> gvs[] >>
    SEP_R_TAC
    ) >>
  Cases_on `t'` using SNOC_CASES
  >- (
    qspecl_then [`frame`, `h'`,`(h::t)`,`p`,`m`,`dm`,`m'`,`b`]
      assume_tac lemma_fib_heap_insert_1intoN >>
    gvs[]
    ) >>
  fs[SNOC_APPEND] >>
  Cases_on `t` using SNOC_CASES
  >- (
    qspecl_then [`frame`,`(h'::(l ++ [x]))`,`h`,`p`,`m`,`dm`,`m'`,`b`]
      assume_tac lemma_fib_heap_insert_Ninto1 >>
    gvs[]
    ) >>
  fs[SNOC_APPEND]>>
  Cases_on `h` >> Cases_on `h'` >> Cases_on `x` >> Cases_on `x'` >>
  simp[head_key_def,head_key_t_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,fill_dnode_def,
     head_key_t_def, ones_def, STAR_ASSOC,REVERSE_APPEND,
     fts_mem_append_thm,ann_fts_seg_append_thm,head_key_t_pull_last_thm] >>
  fs[head_key_t_append_thm] >>
  fs[head_key_t_pull_last_thm] >>
  fs[last_key_t_append_thm] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  simp[fib_heap_merge_def,next_off_def,before_off_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  SEP_W_TAC >> fs[last_key_t_append_thm,last_key_t_def,head_key_t_def] >>
  strip_tac >> gvs[]
QED







(* TODO: Verify invariant. *)
Theorem fib_heap_merge_heaps:
  ∀frame.
    (fib_heap a fh1 * fib_heap b fh2 * frame)
      (fun2set (m,dm)) ∧
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    fib_heap_merge (a, b, m, dm) = (a', m', c) ⇒
    (fib_heap a' (FUNION fh1 fh2) * frame) (fun2set (m',dm)) ∧ c
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  Cases_on `fts'`
  >- (
    fs[head_key_def,head_key_t_def] >>
    qspecl_then [`fh2`,`[]`] assume_tac lemma_empty_heap2 >>
    fs[fts_mem_def, ann_fts_def,SEP_CLAUSES,head_key_def,head_key_t_def] >>
    simp[fib_heap_merge_def] >>
    strip_tac >>
    qexists `fts` >> gvs[]
    ) >>
  Cases_on `h`>> gvs[head_key_def,head_key_t_def] >>
  Cases_on `fts`
  >- (
    qspecl_then [`frame`,`[]`,`(FibTree b v l::t)`,`0w`,`m`,`dm`,`a'`,`m'`,`c`]
      assume_tac lemma_fib_heap_insert_NintoN >>
    qspecl_then [`fh1`,`[]`] assume_tac lemma_empty_heap2 >>
    gvs[head_key_def,head_key_t_def] >>
    strip_tac >> gvs[] >>
    qexists `(FibTree b v l::t)` >> simp[] >>
    pop_assum mp_tac >>
    simp[fib_heap_merge_def] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR]
    ) >>
  qspecl_then [`frame`,`(h::t')`,`(FibTree b v l::t)`,`0w`,`m`,`dm`,`a'`,`m'`,`c`]
    assume_tac lemma_fib_heap_insert_NintoN >>
  strip_tac >>
  rfs[head_key_def,head_key_t_def] >>
  pop_assum mp_tac >>
  Cases_on `h` >>
  fs[fib_heap_merge_def] >>
  fs[before_off_def, next_off_def, head_key_t_def, head_key_def] >>
  pop_assum mp_tac >>
  cheat
(*
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  SEP_R_TAC >>
  IF_CASES_TAC >>
  Cases_on `t` using SNOC_CASES >>
  Cases_on `t'` using SNOC_CASES >>
  fs[last_key_t_def,head_key_t_def] >> SEP_R_TAC
  >- (
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    SEP_R_TAC >>

  qspecl_then [`frame`,`(h::t')`,`(FibTree b v l::t)`,`0w`,`m`,`dm`,`a'`,`m'`,`c`]
    assume_tac lemma_fib_heap_insert_NintoN >>
  rfs[head_key_def,head_key_t_def] >>

(* TODO: WORKING *)




  strip_tac >> gvs[] >>
  cheat*)
QED


(*---------------------------------------------------------

  FH insert. Proves that a single element is a valid FH!

-----------------------------------------------------------*)



Theorem fib_heap_insert:
  !frame k v e.
    (empty_node k (v,e) * frame) (fun2set(m,dm)) ==>
    (fib_heap k (FEMPTY |+ (k,v,e)) * frame) (fun2set(m,dm))
Proof
  rpt strip_tac >>
  fs[fib_heap_def, empty_node_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  fs[ones_def,STAR_ASSOC] >>
  qexists `[FibTree k (fill_dnode v e F) []]` >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[fib_heap_inv_def] >>
  rpt strip_tac
  >- fs[FLOOKUP_SIMP]
  >- (
    Cases_on `k = k'` >> gvs[]
    >- (
      simp[FLOOKUP_SIMP] >>
      iff_tac >> strip_tac >> gvs[]
      >- (
        qexists `F` >>
        simp[Once fts_has_cases,data_node_component_equality, fill_dnode_def]
        ) >>
      fs[Once fts_has_cases] >>
      fs[data_node_component_equality, fill_dnode_def] >>
      fs[Once fts_has_cases]
     ) >>
    simp[FLOOKUP_SIMP] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases]
    )
  >- (
    fs[fts_all_dist_def,fts_has_inj_def] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases]
    )
  >- fs[fts_is_min_def,fts_hd_value_def]
  >- fs[every_fts_def,fts_parent_lower_eq_def,fts_is_min_def] >>
  (*>- fs[every_fts_def, fts_head_is_min_def] >>*)
  fs[fib_heap_shape_ok_def, fts_size_def, Ntimes fib_num_def 2] >>
  fs[Once fib_num_def]
QED






(* -------------------------------------------------------

  Rebalancing of FTS

----------------------------------------------------------*)

Definition fib_heap_inv_strong_def:
  fib_heap_inv_strong fh (fts: ('a word, 'a data_node) fts) ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\
    (!k v e. FLOOKUP fh k = SOME (v,e) <=>
      ?m. fts_has k (fill_dnode v e m) fts) /\
    fts_all_dist fts /\
    every_fts fts_parent_lower_eq fts /\
    fib_heap_shape_ok fts
End



Definition fts_rm_min_def:
  (fts_rm_min [] = (0w,[])) /\
  (fts_rm_min (FibTree k v l::ts) =
    (k,fts_merge l ts))
End


Theorem lemma_fts_all_dist_rm_hd:
  fts_all_dist
    (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'') ==>
  fts_all_dist (FibTree k' v' l::(t' ++ [FibTree k'' v'' l'] ++ t''))
Proof
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
  once_rewrite_tac[GSYM APPEND] >>
  disch_tac >>
  simp[fts_all_dist_append_thm] >>
  fs[] >>
  fs[fts_all_dist_def] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
  once_rewrite_tac[GSYM APPEND] >>
  fs[fts_has_inj_append] >>
  rpt strip_tac >>
  fs[fts_has_inj_def] >>
  rename [`v3 = v4`, `fts_has k3 v3 (FibTree k' v' l::t')`,
    `fts_has k3 v4 (FibTree k'' v'' l'::t'')`] >>
  last_x_assum (qspecl_then [`k3`,`v3`,`v4`] assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases]
QED


Theorem lemma_fts_parent_lower_eq_rm_hd:
  every_fts fts_parent_lower_eq
    (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'') ==>
  every_fts fts_parent_lower_eq
    (FibTree k' v' l::(t' ++ [FibTree k'' v'' l'] ++ t''))
Proof
  disch_tac >>
  fs[Once every_fts_def] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
  once_rewrite_tac[GSYM APPEND] >>
  simp[fts_parent_lower_eq_append_thm] >>
  rpt strip_tac
  >- (
    first_x_assum(qspecl_then[`k`,`v`,`(FibTree k' v' l::t')`] assume_tac) >>
    fs[Once every_fts_def]
    )
  >- (
    qpat_x_assum `fts_parent_lower_eq
      (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'')` mp_tac >>
    pure_rewrite_tac[Once lemma_cons_eq_append] >>
    simp[fts_parent_lower_eq_append_thm]
    )
  >- (
    gvs[] >>
    first_x_assum(qspecl_then[`k`,`v`,`(FibTree k' v' l::t')`] assume_tac) >> fs[] >>
    pop_assum mp_tac >> simp[Once every_fts_def]
    )
  >- (
    first_x_assum(qspecl_then[`k`,`v`,`(FibTree k' v' l::t')`] assume_tac) >> fs[] >>
     pop_assum mp_tac >> simp[Once every_fts_def] >>
    rpt strip_tac >>
    res_tac
    )
  >- gvs[] >>
  res_tac
QED




Theorem lemma_fh_eq_fts_has_rm_hd:
  (!k3 v3 e.
    FLOOKUP fhx k3 = SOME (v3,e) ⇔
    ∃m. fts_has k3 (fill_dnode v3 e m)
      (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'')) /\
    fts_all_dist
      (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'')
  ==>
  !k3 v e. FLOOKUP (fhx \\ k) k3 = SOME (v,e) ⇔
    ∃m. fts_has k3 (fill_dnode v e m)
      (FibTree k' v' l::(t' ++ [FibTree k'' v'' l'] ++ t''))
Proof
  rpt strip_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
  once_rewrite_tac[GSYM APPEND] >>
  simp[fts_has_append_thm] >>
  simp[DOMSUB_FLOOKUP_THM] >>
  pure_rewrite_tac[Once lemma_cons_eq_append] >>
  simp[fts_has_append_thm] >>
  iff_tac
  >- (
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    disch_tac >> gvs[] >> qexists `m` >> simp[]
    ) >>
  disch_tac >>
  conj_tac
  >- (spose_not_then assume_tac >> gvs[fts_all_dist_def]) >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases] >>
  fs[] >> qexists `m` >> simp[]
QED




Theorem fts_rm_min:
  fib_heap_inv fhx xs /\
  fts_rm_min xs = (min,ys) ==>
  ?fhy. fib_heap_inv_strong fhy ys
Proof
  Cases_on `xs`
  >- (
    simp[fts_rm_min_def] >>
    rpt strip_tac >>
    fs[fib_heap_inv_strong_def,fib_heap_inv_def] >>
    simp[Once fts_has_cases] >>
    rpt gen_tac >>
    fs[Once fts_has_cases] >>
    qexists `fhx` >>
    simp[]
    ) >>
  Cases_on `h` >>
  fs[fib_heap_inv_def,fib_heap_inv_strong_def] >>
  rpt strip_tac >>
  fs[fts_rm_min_def] >>
  Cases_on `l` >> Cases_on `t`>> fs[fts_merge_def]
  >- (
    simp[every_fts_def, fts_parent_lower_eq_def, fts_all_dist_def] >>
    simp[fib_heap_shape_ok_def, Once fts_has_cases] >>
    qexists `FEMPTY` >> simp[FLOOKUP_SIMP]
    )
  >- (
    Cases_on `h` >> gvs[] >>
    qexists `fhx \\ k` >>
    rpt strip_tac
    >- (
      pop_assum mp_tac >> simp[] >>
      simp[DOMSUB_FLOOKUP_THM]
      )
    >- (
      simp[DOMSUB_FLOOKUP_THM] >>
      simp[Once fts_has_cases] >>
      iff_tac >> rpt strip_tac
      >- (qexists `m` >> simp[])
      >- (pop_assum mp_tac >> simp[Once fts_has_cases])
      >- (
        fs[fts_all_dist_def] >>
        last_x_assum(qspec_then `fill_dnode v'' e m` assume_tac) >> fs[]
        ) >>
      qexists `m` >> simp[]
     )
    >- fs[fts_all_dist_def]
    >- (
      fs[Once every_fts_def,fts_parent_lower_eq_def] >>
      rpt gen_tac >>
      rpt strip_tac >> res_tac >> simp[]
      ) >>
    fs[fib_heap_shape_ok_def]
   )
  >- (
    Cases_on `h` >>
    qexists `fhx \\ k` >>
    rpt strip_tac
    >- fs[DOMSUB_FLOOKUP_THM]
    >- (
      simp[DOMSUB_FLOOKUP_THM] >>
      iff_tac
      >- (
        simp[Once fts_has_cases] >>
        simp[Once fts_has_cases] >>
        disch_tac >> gvs[] >>
        qexists `m` >> simp[]
        ) >>
      disch_tac >> fs[] >>
      fs[fts_all_dist_def] >>
      strip_tac
      >- (spose_not_then assume_tac >> gvs[]) >>
      qexists `m` >> simp[Once fts_has_cases]
      )
    >- fs[fts_all_dist_def]
    >- fs[Once every_fts_def] >>
    fs[fib_heap_shape_ok_def]
    ) >>
  qexists `fhx \\ k` >>
  Cases_on `h` >> Cases_on `h'` >>
  fs[fts_merge_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> strip_tac >> gvs[]
  >- (
    rpt conj_tac
    >- simp[DOMSUB_FLOOKUP_THM]
    >- (imp_res_tac lemma_fh_eq_fts_has_rm_hd >> simp[])
    >- imp_res_tac lemma_fts_all_dist_rm_hd
    >- imp_res_tac lemma_fts_parent_lower_eq_rm_hd >>
    fs[fib_heap_shape_ok_def] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC] >>
    simp[fib_heap_shape_ok_append_thm] >>
    simp[fib_heap_shape_ok_def]
  ) >>
  rpt conj_tac
  >- simp[DOMSUB_FLOOKUP_THM]
  >- (
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_has_sym_thm] >>
    imp_res_tac lemma_fh_eq_fts_has_rm_hd >> fs[] >>
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
    simp[]
    )
  >- (
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_all_dist_sym_thm] >>
    imp_res_tac lemma_fts_all_dist_rm_hd >>
    pop_assum mp_tac >>
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
    simp[]
    )
  >- (
    imp_res_tac lemma_fts_parent_lower_eq_rm_hd >>
    pop_assum mp_tac >>
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    pure_rewrite_tac[GSYM lemma_cons_eq_append] >>
    once_rewrite_tac[GSYM APPEND] >>
    pure_rewrite_tac[Once lemma_every_fts_parent_lower_eq_sym] >>
    simp[]
    ) >>
  fs[fib_heap_shape_ok_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[fib_heap_shape_ok_append_thm] >>
  simp[fib_heap_shape_ok_def]
QED










Definition flat_fts_def:
  (flat_fts [] = []) /\
  (flat_fts (FibTree k v ts::rest) =
    [(k,v.value,v.edges)] ++ flat_fts ts ++ flat_fts rest)
End


Theorem flat_fts_append_thm:
  !xs ys.
  flat_fts (xs ++ ys) = (flat_fts xs) ++ (flat_fts ys)
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def] >>
  simp[flat_fts_def]
QED





(*
Maybe add:
!k v e. FLOOKUP fh k = SOME(v,e) <=> ?m. fts_has k (fill_dnode v e m) fts

*)
Definition all_disjoint_def:
  (all_disjoint [] <=> T ) /\
  (all_disjoint ((fh,fts)::rest) <=>
    all_disjoint rest /\ EVERY (\(x,y). DISJOINT (FDOM fh) (FDOM x)) rest)
End



Theorem all_disjoint_append_thm:
  !xs ys. all_disjoint (xs ++ ys) <=>
    all_disjoint xs /\ all_disjoint ys /\
    !x y. MEM x xs /\ MEM y ys ==> DISJOINT (FDOM (FST x)) (FDOM (FST y))
Proof
  Induct >> fs[all_disjoint_def] >>
  Cases_on `h` >>
  gen_tac >> iff_tac
  >- (
    strip_tac >>
    fs[all_disjoint_def] >>
    first_assum(qspec_then `ys` assume_tac) >> fs[] >>
    rpt strip_tac >> gvs[] >>
    fs[EVERY_MEM] >>
    res_tac >>
    pairarg_tac >> gvs[] >>
    first_x_assum(qspec_then `(x,y')` assume_tac) >> fs[]
    ) >>
  rpt strip_tac >>
  fs[all_disjoint_def] >>
  fs[EVERY_MEM] >>
  rpt strip_tac >>
  first_x_assum(qspecl_then [`(q,r)`,`e`] assume_tac) >>
  gvs[] >>
  pairarg_tac >> gvs[]
QED


Theorem lemma_genlist_append:
  (GENLIST f (n + 1)) = GENLIST f n ++ [f n]
Proof
  qspecl_then [`f`,`1`,`n`] assume_tac GENLIST_APPEND >>
  gvs[]
QED


Theorem lemma_less_add_one_imp_less_eq:
  (i: num) < n + 1 ==> i <= n
Proof
  strip_tac >>
  fs[GSYM SUC_ONE_ADD]
QED



Theorem lemma_mem_genlist_imp_disjoint:
  i < n /\
  (!x. MEM x (GENLIST f n) ==> DISJOINT (FDOM (FST x)) (FDOM (FST (f n)))) ==>
  DISJOINT (FDOM (FST (f i))) (FDOM (FST (f n)))
Proof
  strip_tac >>
  first_x_assum(qspec_then `f i` assume_tac) >>
  fs[MEM_GENLIST] >>
  res_tac >> fs[DISJOINT_SYM]
QED



Theorem all_disjoint_genlist_thm:
  !n f.
  all_disjoint (GENLIST f n) <=>
  !i j.
    i < n /\ j < n /\ i <> j ==>
    DISJOINT (FDOM (FST (f i))) (FDOM (FST (f j)))
Proof
  Induct >> rpt strip_tac >> fs[]
  >- simp[all_disjoint_def] >>
  iff_tac >> rpt strip_tac
  >- (
    fs[SUC_ONE_ADD] >>
    fs[lemma_genlist_append] >>
    fs[all_disjoint_append_thm] >>
    imp_res_tac lemma_less_add_one_imp_less_eq >>
    Cases_on `j < n` >> Cases_on `i < n` >> gvs[NOT_LESS] >>
    drule_all LESS_EQUAL_ANTISYM >> strip_tac
    >- (
      imp_res_tac lemma_mem_genlist_imp_disjoint >>
      gvs[DISJOINT_SYM]
      ) >>
    imp_res_tac lemma_mem_genlist_imp_disjoint >>
    gvs[DISJOINT_SYM]
    ) >>
  simp[SUC_ONE_ADD] >>
  simp[lemma_genlist_append] >>
  simp[all_disjoint_append_thm] >>
  rpt strip_tac
  >- (
    Cases_on `[f n]` >> fs[all_disjoint_def] >>
    Cases_on `h` >> simp[all_disjoint_def]
    ) >>
  Cases_on `x` >>
  fs[MEM_GENLIST] >>
  first_x_assum(qspecl_then[`m`,`n`] assume_tac) >> gvs[SUC_ONE_ADD] >>
  drule EQ_SYM >> strip_tac >>
  qpat_x_assum `(q,r) = f m` kall_tac >>
  gvs[]
QED


Theorem all_disjoint_el_thm:
  !list i j.
  i < LENGTH list /\
  j < LENGTH list /\
  i <> j /\
  all_disjoint list ==>
  DISJOINT (FDOM (FST (EL i list))) (FDOM (FST (EL j list)))
Proof
  Induct >> rpt strip_tac
  >- fs[LENGTH] >>
  Cases_on `h` >>
  rename [`all_disjoint ((m,ts)::list)`] >>
  pop_assum mp_tac >> once_rewrite_tac[lemma_cons_eq_append] >>
  simp[all_disjoint_append_thm] >>
  strip_tac >> fs[] >>
  Cases_on `i = 0` >> Cases_on `j = 0` >> fs[]
  >- (Cases_on `j` >> fs[EL_MEM])
  >- (Cases_on `i` >> fs[EL_MEM,DISJOINT_SYM]) >>
  Cases_on `j` >> Cases_on `i` >> fs[]
QED



Theorem lemma_every_true:
  !list. EVERY (\(x,y). T) list = T
Proof
 Induct >> fs[EVERY_DEF]
QED




Theorem all_disjoint_split_thm:
  !fh xs ys rest.
  all_disjoint ((fh,xs ++ ys)::rest) <=>
  ?fhx fhy.
  all_disjoint ((fhx,xs)::(fhy,ys)::rest) /\ fh = FUNION fhx fhy
Proof
  rpt strip_tac >>
  iff_tac >> strip_tac
  >- (
    fs[all_disjoint_def] >>
    qexistsl [`fh`,`FEMPTY`] >> fs[] >>
    simp[lemma_every_true]
  ) >>
  fs[all_disjoint_def] >>
  fs[EVERY_MEM] >>
  rpt strip_tac >>
  res_tac >>
  pairarg_tac >> fs[]
QED



Definition fh_union_def:
  (fh_union [] = FEMPTY) /\
  (fh_union ((fh,fts)::rest) =
    FUNION fh (fh_union rest))
End


Theorem lemma_fh_union_empty_ind_IH:
  (!x. x < SUC (LENGTH list) ==> EL x (h::list) = (FEMPTY,NONE))
  ==>
  !x. x < LENGTH list ==> EL x list = (FEMPTY,NONE)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC x` assume_tac) >>
  gvs[]
QED


Theorem fh_union_empty_thm:
  !list.
  (!x. x < LENGTH list ==> EL x list = (FEMPTY,NONE))
  ==>
  fh_union list = FEMPTY
Proof
  Induct >> fs[]
  >- simp[fh_union_def] >>
  rpt strip_tac >>
  Cases_on `h` >>
  first_assum (qspec_then `0` assume_tac) >> fs[] >>
  drule lemma_fh_union_empty_ind_IH >>
  strip_tac >>
  res_tac >>
  simp[fh_union_def]
QED




Theorem fh_union_replicate_empty_thm:
  !x.
  fh_union (REPLICATE x (FEMPTY,NONE)) = FEMPTY
Proof
  Induct
  >- simp[fh_union_def] >>
  simp[fh_union_def]
QED




Theorem fh_union_append_thm:
  !xs ys.
  fh_union (xs ++ ys) =
    FUNION (fh_union xs) (fh_union ys)
Proof
  ho_match_mp_tac fh_union_ind >> fs[] >>
  rpt strip_tac
  >- simp[fh_union_def] >>
  simp[fh_union_def] >>
  simp[FUNION_ASSOC]
QED



Theorem fh_union_mem_submap_thm:
  !list m x.
  MEM (m, SOME x) list /\
  all_disjoint list
  ==> m SUBMAP fh_union list
Proof
  Induct >> rpt strip_tac >> fs[] >> Cases_on `h` >> fs[fh_union_def]
  >- simp[SUBMAP_FUNION] >>
  pop_assum mp_tac >> once_rewrite_tac[lemma_cons_eq_append] >>
  simp[all_disjoint_append_thm] >> rpt strip_tac >>
  res_tac >> fs[] >>
  fs[SUBMAP_FUNION,DISJOINT_SYM]
QED



Theorem fh_union_genlist_thm:
  !n f.
  fh_union (GENLIST f n) = FOLDL (\acc (fh,ts). FUNION acc fh) FEMPTY (GENLIST f n)
Proof
  Induct >> rpt strip_tac
  >- simp[fh_union_def] >>
  simp[GENLIST] >>
  simp[SNOC_APPEND] >>
  simp[fh_union_append_thm] >>
  simp[rich_listTheory.FOLDL_APPEND] >>
  Cases_on `(f n)` >> simp[] >>
  simp[fh_union_def]
QED


Theorem lemma_fh_union_foldl_acc:
  !list acc.
  FUNION acc (fh_union list) =
  (FOLDL (\acc (fh,ts). FUNION acc fh) acc list)
Proof
  Induct >> rpt strip_tac >> fs[fh_union_def] >>
  Cases_on `h` >>
  fs[fh_union_def] >>
  first_assum (qspec_then `q` assume_tac) >>
  first_x_assum (qspec_then `FUNION acc q` assume_tac) >>
  fs[GSYM FUNION_ASSOC]>>
  gvs[]
QED


Theorem fh_union_foldl_thm:
  !list.
  fh_union list = FOLDL (\acc (fh,ts). FUNION acc fh) FEMPTY list
Proof
  Induct >> fs[fh_union_def] >>
  strip_tac >>
  Cases_on `h` >>
  drule EQ_SYM >> strip_tac >>
  qpat_x_assum `fh_union list =
    FOLDL (\acc (fh,ts). FUNION acc fh) FEMPTY list` kall_tac >>
  gvs[fh_union_def] >>
  irule lemma_fh_union_foldl_acc
QED



Theorem fh_union_foldr_thm:
  !list. fh_union list = FOLDR FUNION FEMPTY (MAP FST list)
Proof
  Induct >>  fs[fh_union_def] >>
  gen_tac >>
  Cases_on `h` >> fs[fh_union_def]
QED




Theorem lemma_fh_union_mem_disjoint:
  !ys.
    (!y. MEM y ys ==> DISJOINT (FDOM q) (FDOM (FST y)))
    ==>
    DISJOINT (FDOM q) (FDOM (fh_union ys))
Proof
  Induct >> rpt strip_tac
  >- simp[fh_union_def] >>
  Cases_on `h` >> fs[] >>
  first_x_assum(qspec_then `(q',r)` assume_tac) >> fs[] >>
  simp[fh_union_def] >>
  fs[DISJOINT_SYM]
QED


Theorem lemma_fh_union_disjoint:
  !xs ys.
  all_disjoint xs /\
  all_disjoint ys /\
  (∀x y. MEM x xs ∧ MEM y ys ==> DISJOINT (FDOM (FST x)) (FDOM (FST y))) ==>
  DISJOINT (FDOM (fh_union xs)) (FDOM (fh_union ys))
Proof
  Induct >> fs[fh_union_def] >>
  rpt strip_tac >>
  Cases_on `h`>> fs[fh_union_def] >>
  fs[all_disjoint_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `(q,r)` assume_tac) >> fs[] >>
  fs[lemma_fh_union_mem_disjoint]
QED



Theorem lemma_list_length_intro:
  list = xs ++ ys ==> LENGTH list = LENGTH (xs ++ ys)
Proof
  simp[]
QED

Theorem lemma_list_el_intro:
  i < LENGTH list /\ list = ys ==> (EL i list) = (EL i ys)
Proof
  simp[]
QED


Theorem lemma_el_index_split:
  !list i.
  i < LENGTH list ==>
  ?xs ys. list = xs ++ (EL i list)::ys /\ LENGTH xs = i
Proof
  strip_tac >> Induct >> strip_tac
  >- (
    qexistsl [`[]`,`TL list`] >> fs[] >>
    Cases_on `list` >> fs[]
    ) >>
  fs[] >>
  Cases_on `ys` >> fs[]
  >- (
    gvs[] >>
    drule lemma_list_length_intro >> strip_tac >>
    gvs[]
    ) >>
  qexistsl [`xs ++ [EL i list]`,`t`] >>
  simp[] >>
  Cases_on `h = EL (SUC i) list` >> gvs[] >>
  drule_all lemma_list_el_intro >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  fs[EL_APPEND_EQN] >> strip_tac >>
  qspecl_then [`list`,`LENGTH xs`] assume_tac (cj 2 EL) >>
  gvs[]
QED

Theorem lemma_lupdate_intro:
  i < LENGTH list /\
  list = ys ==>
  LUPDATE x i list = LUPDATE x i ys
Proof
  simp[]
QED





Definition fib_heap_inv_union_def:
  fib_heap_inv_union fh fh_fts ⇔
    EVERY (\(fh,fts). fib_heap_inv_strong fh fts) fh_fts /\
    (all_disjoint fh_fts) /\
    (fh = fh_union fh_fts)
End



Theorem fib_heap_inv_union_append_thm:
  !fh xs ys.
    fib_heap_inv_union fh (xs ++ ys) <=>
    ?fhx fhy. fib_heap_inv_union fhx xs /\ fib_heap_inv_union fhy ys /\
    all_disjoint (xs ++ ys) /\
    (fh = FUNION fhx fhy)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
  simp[fh_union_append_thm] >>
  simp[all_disjoint_append_thm] >>
  iff_tac >> fs[]
QED


Definition fib_heap_inv_union2_def:
  fib_heap_inv_union2 fh fh_ft <=>
    EVERY (\(fh,O_ft).
      case O_ft of
       |NONE => fib_heap_inv fh []
       |SOME(ft) => fib_heap_inv fh [ft]
      ) fh_ft /\
    (all_disjoint fh_ft) /\
    (fh = fh_union fh_ft) /\
  !n map k v l. n < LENGTH fh_ft /\ EL n fh_ft = (map,SOME(FibTree k v l))
    ==> LENGTH l = n
End


Theorem fib_heap_inv_union2_empty_thm:
  !x.
  fib_heap_inv_union2 FEMPTY (REPLICATE x (FEMPTY,NONE))
Proof
  Induct
  >- simp[fib_heap_inv_union2_def,fh_union_def,all_disjoint_def] >>
  simp[fib_heap_inv_union2_def] >>
  simp[fh_union_def,fh_union_replicate_empty_thm,fib_heap_inv_empty_thm] >>
  simp[all_disjoint_def] >>
  fs[fib_heap_inv_union2_def] >>
  rpt strip_tac >>
  Cases_on `n` >> fs[] >>
  gvs[rich_listTheory.EL_REPLICATE]
QED


Definition fib_heap_inv_list_def:
  fib_heap_inv_list fh ftss <=>
    ?fh_fts. fib_heap_inv_union fh fh_fts /\ ftss = MAP SND fh_fts
End


(*
Theorem fib_heap_inv_strong_split_last_thm:
  all_disjoint ((fhx,xs)::(fhy,[y])::rest) /\
  fib_heap_inv_strong (FUNION fhx fhy) (xs ++ [y]) ==>
  fib_heap_inv_strong (FUNION fhx fhy) (xs ++ [y]) =
  fib_heap_inv_strong fhx xs /\ fib_heap_inv_strong fhy [y]
Proof
  fs[fib_heap_inv_strong_def] >>
  fs[all_disjoint_def] >>
  rpt strip_tac >>

  cheat
QED
*)



Theorem lemma_fh_union_split:
  !fhx xs fhy y rest.
  all_disjoint ((fhx,xs)::(fhy, [y])::rest) ==>
  fh_union ((FUNION fhx fhy, xs ++ [y])::rest)  =
  fh_union ((fhx,xs)::(fhy,[y])::rest)
Proof
  rpt gen_tac >>
  simp[all_disjoint_def] >>
  strip_tac >>
  simp[fh_union_def] >>
  simp[FUNION_ASSOC]
QED



(*
Theorem lemma_fts_finite_map_split_last:
  !fh xs y.
  (!k v e. FLOOKUP fh k = SOME (v,e) ⇔
  ∃m. fts_has k (fill_dnode v e m) (xs ++ [y])) ==>
  ?fhx fhy.
    (!k v e. FLOOKUP fhx k = SOME (v,e) <=>
     ?m. fts_has k (fill_dnode v e m) xs) /\
    (!k v e. FLOOKUP fhy k = SOME (v,e) <=>
     ?m. fts_has k (fill_dnode v e m) [y]) /\
    fh = FUNION fhx fhy /\
    DISJOINT (FDOM fhx) (FDOM fhy)
Proof
  rpt strip_tac >>
  fs[fts_has_append_thm] >>
  qexistsl [`map_from_fts xs`,`map_from_fts [y]`] >>
  rpt strip_tac >>
  cheat

QED
*)




Theorem lemma_mem_eq_fts_has:
 !fts k v e.
    MEM (k,v,e) (flat_fts fts) <=>
    ?m. fts_has k (fill_dnode v e m) fts
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac >> fs[flat_fts_def]
  >- simp[Once fts_has_cases] >>
  iff_tac >> rpt strip_tac
  >- (
    qexists `fts.mark` >>
    simp[Once fts_has_cases,fill_dnode_def,data_node_component_equality]
    )
  >- (qexists `m` >> simp[Once fts_has_cases])
  >- (qexists `m` >> simp[Once fts_has_cases]) >>
  pop_assum mp_tac >> simp[Once fts_has_cases] >>
  disch_tac >> fs[]
  >- fs[fill_dnode_def, data_node_component_equality]
  >- (disj2_tac >> disj2_tac >> qexists `m` >> simp[]) >>
  disj2_tac >> disj1_tac >> qexists `m` >> simp[]
QED


Theorem lemma_flat_fts_mem_eq_fst:
  !xs k.
    (?v e. MEM (k,v,e) (flat_fts xs)) <=>
    MEM k (MAP FST (flat_fts xs))
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def] >>
  simp[flat_fts_def] >>
  iff_tac >> rpt strip_tac
  >- simp[]
  >- (
    last_x_assum(qspec_then `k'` assume_tac) >>
    fs[EQ_IMP_THM] >> fs[PULL_EXISTS] >>
    res_tac >> simp[]
    )
  >- (
    last_x_assum(qspec_then `k'` assume_tac) >>
    fs[EQ_IMP_THM] >> fs[PULL_EXISTS] >>
    res_tac >> simp[]
    )
  >- (qexistsl [`xs.value`,`xs.edges`] >> simp[]) >>
  res_tac >> qexistsl [`v`,`e`] >> simp[]
QED


Theorem lemma_fts_has_inj_imp_mem_upd_inj:
  fts_has_inj xs ==>
  (MEM(k,v) (flat_fts xs) /\
   MEM(k,v') (flat_fts xs) ==>
   v = v')
Proof
  rpt strip_tac >>
  Cases_on `xs`
  >- fs[flat_fts_def] >>
  Cases_on `h` >>
  rpt strip_tac >>
  Cases_on `v` >> Cases_on `v'` >>
  imp_res_tac lemma_mem_eq_fts_has >>
  fs[fts_has_inj_def] >>
  res_tac >>
  fs[fill_dnode_def]
QED

(*
Theorem lemma_fts_all_dist_imp_flat_fts_all_dist:
  !xs.
  fts_all_dist xs ==>
  ALL_DISTINCT (flat_fts xs) /\
  (!k v v'. MEM (k,v) (flat_fts xs) /\ MEM (k,v') (flat_fts xs) ==>
    v = v')
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def]
  >- fs[flat_fts_def]
  >- (
    fs[fts_all_dist_def,flat_fts_def] >>
    rpt strip_tac
    >- (
      qspecl_then [`xs'`,`k`,`xs.value`,`xs.edges`]
        assume_tac lemma_mem_eq_fts_has >> rfs[]
      )
    >- (
      qspecl_then [`xs''`,`k`,`xs.value`,`xs.edges`]
        assume_tac lemma_mem_eq_fts_has >> rfs[]
      ) >>
    simp[ALL_DISTINCT_APPEND] >>
    rpt strip_tac >>
    Cases_on `e` >> Cases_on `r` >>
    rename [`MEM (k,v,e) (flat_fts xs')`] >>
    imp_res_tac lemma_mem_eq_fts_has >>
    fs[fts_has_inj_def] >>
    first_x_assum (qspecl_then [`k`,`(fill_dnode v e m)`,`(fill_dnode v e m')`]
      assume_tac) >>
    pop_assum mp_tac >>
    pure_rewrite_tac[Once fts_has_cases] >> disch_tac >> rfs[] >>
    pop_assum mp_tac >>
    pure_rewrite_tac[Once fts_has_cases] >> disch_tac >> rfs[] >>
    gvs[]
  ) >>
  fs[fts_all_dist_def] >>
  imp_res_tac lemma_fts_has_inj_imp_mem_upd_inj
QED
*)


Theorem lemma_flat_fts_all_distinct:
  !xs.
  fts_all_dist xs ==>
  ALL_DISTINCT (MAP FST (flat_fts xs))
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def] >>
  simp[flat_fts_def] >>
  fs[fts_all_dist_def] >>
  rpt conj_tac
  >- (
    spose_not_then assume_tac >>
    imp_res_tac lemma_flat_fts_mem_eq_fst >>
    imp_res_tac lemma_mem_eq_fts_has >>
    rfs[]
    )
  >- (
    spose_not_then assume_tac >>
    imp_res_tac lemma_flat_fts_mem_eq_fst >>
    imp_res_tac lemma_mem_eq_fts_has >>
    rfs[]
    ) >>
  simp[ALL_DISTINCT_APPEND] >>
  rpt strip_tac >>
  rename [`MEM k' (MAP FST (flat_fts xs'))`] >>
  imp_res_tac lemma_flat_fts_mem_eq_fst >>
  imp_res_tac lemma_mem_eq_fts_has >>
  qpat_x_assum `fts_has_inj (FibTree k xs xs''::xs')` mp_tac >>
  pure_rewrite_tac[fts_has_inj_def] >>
  disch_tac >>
  first_x_assum (qspecl_then [`k'`,`(fill_dnode v e m')`,`(fill_dnode v' e' m)`]
    assume_tac) >>
  pop_assum mp_tac >>
  pure_rewrite_tac[Once fts_has_cases] >> disch_tac >> rfs[] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[Once fts_has_cases] >> disch_tac >> rfs[] >>
  gvs[]
QED



Theorem lemma_disjoint_alist_imp_disjoint_fmap:
  DISJOINT (set $ MAP FST xs) (set $ MAP FST ys) ==>
  DISJOINT (FDOM $ alist_to_fmap xs) (FDOM $ alist_to_fmap ys)
Proof
  simp[IN_DISJOINT]
QED


Theorem lemma_alist_to_fmap_disjoint:
  fts_all_dist (xs ++ ys) ==>
  DISJOINT (FDOM $ alist_to_fmap $ flat_fts xs)
           (FDOM $ alist_to_fmap $ flat_fts ys)
Proof
  strip_tac >>
  irule lemma_disjoint_alist_imp_disjoint_fmap >>
  imp_res_tac lemma_flat_fts_all_distinct >>
  fs[flat_fts_append_thm] >>
  fs[ALL_DISTINCT_APPEND']
QED


Theorem lemma_alookup_eq_mem:
  !k v e xs.
  fts_all_dist xs ==>
  (ALOOKUP (flat_fts xs) k = SOME (v,e) <=> MEM(k,v,e) (flat_fts xs))
Proof
  gen_tac >> gen_tac >> gen_tac >>
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def] >>
  rename [`fts_all_dist (FibTree k1 v1 l1::xs)`] >>
  fs[fts_all_dist_def] >>
  iff_tac >> strip_tac
  >- fs[ALOOKUP_MEM] >>
  pop_assum mp_tac >>
  simp[flat_fts_def] >>
  rpt strip_tac >> fs[]
  >- (
    fs[lemma_mem_eq_fts_has] >>
    Cases_on `k1 = k` >> gvs[] >>
    simp[ALOOKUP_APPEND]
    ) >>
  fs[lemma_mem_eq_fts_has] >>
  Cases_on `k1 = k` >> gvs[] >>
  simp[ALOOKUP_APPEND] >>
  fs[Once MONO_NOT_EQ] >>
  res_tac >>
  Cases_on `ALOOKUP (flat_fts l1) k` >> fs[] >>
  `MEM (k,x) (flat_fts l1)` by imp_res_tac ALOOKUP_MEM >>
  Cases_on `x` >>
  fs[lemma_mem_eq_fts_has] >>
  fs[fts_all_dist_def,fts_has_inj_def] >>
  last_x_assum (qspecl_then [`k`,`fill_dnode v e m`,`fill_dnode q r m'`]
    assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases] >>
  simp[fill_dnode_def,data_node_component_equality] >>
  strip_tac >> fs[]
QED



Theorem lemma_alookup_eq_fts_has:
  !xs k v e.
  fts_all_dist xs ==>
  (ALOOKUP (flat_fts xs) k = SOME (v,e) <=> ?m. fts_has k (fill_dnode v e m) xs)
Proof
  rpt strip_tac >>
  iff_tac >> strip_tac
  >- (
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac lemma_mem_eq_fts_has >>
    qexists `m` >> simp[]
    ) >>
  simp[lemma_alookup_eq_mem] >>
  imp_res_tac lemma_mem_eq_fts_has
QED


Theorem lemma_key_not_in_fts:
  ~MEM x (MAP FST (flat_fts xs)) ==>
  !v e m. ~fts_has x (fill_dnode v e m) xs
Proof
  rpt strip_tac >>
  fs[MEM_MAP] >>
  imp_res_tac lemma_mem_eq_fts_has >>
  first_x_assum(qspec_then `(x,v,e)` assume_tac) >>
  fs[]
QED


Theorem lemma_flookup_in_split:
  fts_all_dist xs /\
  (∀v e. FLOOKUP fh x = SOME (v,e) ⇔
    ∃m. fts_has x (fill_dnode v e m) (xs ++ ys)) /\
  ALOOKUP (flat_fts xs) x = SOME x' ==>
  FLOOKUP fh x = SOME x'
Proof
  rpt strip_tac >>
  Cases_on `x'` >>
  rename [`FLOOKUP fh x = SOME (v,e)`] >>
  first_x_assum(qspecl_then [`v`,`e`] assume_tac) >>
  `MEM (x,v,e) (flat_fts xs)` by imp_res_tac lemma_alookup_eq_mem >>
  imp_res_tac lemma_mem_eq_fts_has >>
  fs[fts_has_append_thm] >>
  qexists `m` >>
  simp[]
QED


Theorem lemma_finite_map_split:
  fts_all_dist (xs ++ ys) /\
  (∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) (xs ++ ys)) ==>
  fh = alist_to_fmap (flat_fts xs) ⊌ alist_to_fmap (flat_fts ys)
Proof
  rpt strip_tac >>
  pure_rewrite_tac[fmap_eq_flookup] >>
  gen_tac >>
  simp[FLOOKUP_SIMP] >>
  first_x_assum(qspecl_then [`x`] assume_tac) >>
  gvs[] >>
  Cases_on `ALOOKUP (flat_fts xs) x` >> fs[]
  >- (
    Cases_on `ALOOKUP (flat_fts ys) x`
    >- (
      fs[fts_all_dist_append_thm] >>
      fs[ALOOKUP_NONE] >>
      imp_res_tac lemma_key_not_in_fts >>
      fs[fts_has_append_thm] >>
      Cases_on `FLOOKUP fh x` >> fs[] >>
      Cases_on `x'` >>
      first_x_assum(qspecl_then [`q`,`r`] assume_tac) >> fs[]
      ) >>
    qpat_x_assum `∀v e. FLOOKUP fh x = SOME (v,e) ⇔
      ∃m. fts_has x (fill_dnode v e m) (xs ++ ys)` mp_tac >>
    once_rewrite_tac[fts_has_sym_thm] >>
    disch_tac >>
    fs[fts_all_dist_append_thm] >>
    imp_res_tac lemma_flookup_in_split
   )>>
  fs[fts_all_dist_append_thm] >>
  imp_res_tac lemma_flookup_in_split
QED



Theorem lemma_fts_split:
  !xs ys fh.
  fts_all_dist (xs ++ ys) /\
  (!k v e. FLOOKUP fh k = SOME(v,e) <=> ?m. fts_has k (fill_dnode v e m) (xs ++ ys))
  <=>
  ?fhx fhy.
    (!k v e. FLOOKUP fhx k = SOME(v,e) <=> ?m. fts_has k (fill_dnode v e m) xs) /\
    fts_all_dist xs /\
    (!k v e. FLOOKUP fhy k = SOME(v,e) <=> ?m. fts_has k (fill_dnode v e m) ys) /\
    fts_all_dist ys /\
    DISJOINT (FDOM fhx) (FDOM fhy) /\ fh = FUNION fhx fhy
Proof
  rpt gen_tac >>
  iff_tac
  >- (
    rpt strip_tac >>
    qexistsl [`alist_to_fmap (flat_fts xs)`,`alist_to_fmap (flat_fts ys)`] >>
    simp[lemma_alist_to_fmap_disjoint] >>
    conj_tac
    >- (
      fs[fts_all_dist_append_thm] >>
      imp_res_tac lemma_alookup_eq_fts_has >> simp[]
      ) >>
    conj_tac
    >- fs[fts_all_dist_append_thm] >>
    conj_tac
    >- (
      imp_res_tac fts_all_dist_sym_thm >>
      qpat_x_assum `∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
        ∃m. fts_has k (fill_dnode v e m) (xs ++ ys)` mp_tac >>
      fs[fts_has_append_thm] >>
      pure_rewrite_tac[Once DISJ_COMM] >>
      simp[GSYM fts_has_append_thm] >>
      disch_tac >>
      fs[fts_all_dist_append_thm] >>
      imp_res_tac lemma_alookup_eq_fts_has >> simp[]
      ) >>
    conj_tac
    >- fs[fts_all_dist_append_thm] >>
    imp_res_tac lemma_finite_map_split
    ) >>
  disch_tac >> fs[] >>
  `fts_all_dist (xs ++ ys)` by imp_res_tac lemma_merge_all_dist >> simp[] >>
  rpt gen_tac >>
  drule_all lemma_merge_fts_has >>
  simp[Once fts_has_sym_thm]
QED



Theorem lemma_fib_heap_inv_strong_split:
  !x xs fh.
  fib_heap_inv_strong fh (x::xs) ==>
  ?fh1 fh2.
  fib_heap_inv_strong fh1 [x]  /\ fib_heap_inv_strong fh2 xs /\
  fh = FUNION fh1 fh2 /\ DISJOINT (FDOM fh1) (FDOM fh2)
Proof
  rpt gen_tac >>
  simp[fib_heap_inv_strong_def] >>
  rpt strip_tac >>
  qpat_x_assum `fts_all_dist(x::xs)` mp_tac >>
  pure_rewrite_tac[Once lemma_cons_eq_append] >>
  disch_tac >>
  qpat_x_assum `∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) (x::xs)` mp_tac >>
  pure_rewrite_tac[Once lemma_cons_eq_append] >>
  disch_tac >>
  qspecl_then [`[x]`,`xs`,`fh`] assume_tac lemma_fts_split >>
  gvs[] >>
  rename [`DISJOINT (FDOM fh1) (FDOM fh2)`] >>
  qexistsl [`fh1`,`fh2`] >>
  simp[] >>
  rpt conj_tac
  >- (Cases_on `FLOOKUP fh1 0w`>> fs[FLOOKUP_SIMP])
  >- (Cases_on `x` >> fs[Once every_fts_def, fts_parent_lower_eq_def])
  >- (Cases_on `x` >> fs[fib_heap_shape_ok_def])
  >- (
    imp_res_tac lemma_flookup_funion_comm >>
    Cases_on `FLOOKUP fh2 0w` >> fs[FLOOKUP_SIMP] >>
    first_x_assum(qspec_then `0w` assume_tac) >> rfs[]
    )
  >- (
    Cases_on `x` >> fs[Once every_fts_def, fts_parent_lower_eq_def] >>
    rpt strip_tac >> res_tac
    ) >>
  Cases_on `x` >> fs[fib_heap_shape_ok_def]
QED


Theorem lemma_fib_heap_union_split:
  fib_heap_inv_union fh ((fh_xys,[x] ++ ys)::rest) ==>
    ?fh1 fh2. fib_heap_inv_union fh ((fh1,[x])::(fh2,ys)::rest)
Proof
  fs[fib_heap_inv_union_def] >>
  rpt strip_tac >>
  drule lemma_fib_heap_inv_strong_split >>
  strip_tac >> gvs[] >>
  qexistsl [`fh1`,`fh2`] >>
  fs[all_disjoint_def,fh_union_def] >>
  fs[FUNION_ASSOC] >>
  fs[EVERY_MEM,FORALL_PROD] >>
  metis_tac[]
QED


Theorem lemma_all_disjoint_split_first:
  !ys fh x.
  all_disjoint([(fh,x)] ++ ys) ==>
  DISJOINT (FDOM fh) (FDOM (fh_union ys))
Proof
  Induct >> rpt strip_tac
  >- fs[all_disjoint_def,fh_union_def] >>
  Cases_on `h` >>
  fs[all_disjoint_append_thm] >>
  simp[fh_union_def] >>
  first_assum (qspec_then `(q,r)` assume_tac) >> fs[] >>
  first_x_assum (qspecl_then [`fh`,`x`] assume_tac) >>
  rfs[all_disjoint_def] >>
  fs[DISJOINT_SYM]
QED



Theorem lemma_mem_imp_disjoint_gen:
  (!x y. MEM x ys /\ (y = (fh,x') \/ MEM y zs) ==>
    DISJOINT (FDOM (FST x)) (FDOM (FST y)))
  ==>
  !x. MEM x ys ==> DISJOINT (FDOM (FST x)) (FDOM fh)
Proof
  rpt strip_tac >>
  first_x_assum(qspecl_then [`x`,`(fh,x')`] assume_tac) >>
  gvs[]
QED


Theorem lemma_all_disjoint_split:
  !ys fh x zs.
  all_disjoint (ys ++ (fh,x)::zs) ==>
  DISJOINT (FDOM fh) (FDOM (fh_union (ys ++ zs)))
Proof
  rpt strip_tac >>
  fs[all_disjoint_append_thm] >>
  simp[fh_union_append_thm] >>
  strip_tac >>
  qpat_x_assum `all_disjoint ((fh,x)::zs)` mp_tac >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  strip_tac >>
  imp_res_tac lemma_all_disjoint_split_first >>
  fs[DISJOINT_SYM] >>
  qspecl_then [`ys`,`fh`,`x`] mp_tac lemma_all_disjoint_split_first  >>
  simp[all_disjoint_append_thm] >>
  strip_tac >>
  fs[all_disjoint_def] >>
  imp_res_tac lemma_mem_imp_disjoint_gen >>
  pop_assum mp_tac >> simp[Once DISJOINT_SYM]
QED





Theorem fib_heap_inv_union2_rm_thm:
  !fh1 ys fht t zs.
  fib_heap_inv_union2 fh1 (ys ++ (fht,SOME(t))::zs) ==>
  ?fh2.
    fib_heap_inv_union2 fh2 (ys ++ (FEMPTY,NONE)::zs) /\
    fib_heap_inv fht [t] /\
    DISJOINT (FDOM fht) (FDOM fh2)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  imp_res_tac lemma_all_disjoint_split >>
  fs[EVERY_MEM] >>
  Cases_on `t` >> fs[] >>
  simp[fib_heap_inv_empty_thm] >>
  fs[fh_union_append_thm] >>
  simp[fh_union_def] >> gvs[] >>
  rpt strip_tac
  >- (
    fs[all_disjoint_append_thm] >>
    fs[all_disjoint_def] >>
    simp[lemma_every_true] >>
    rpt strip_tac >> gvs[]
    ) >>
  first_x_assum(qspecl_then [`n`,`map'`,`k'`,`v'`,`l'`] assume_tac) >>
  rfs[EL_APPEND_EQN] >>
  Cases_on `n < LENGTH ys` >> gvs[] >>
  Cases_on `n - LENGTH ys` >> fs[EL]
QED




(*-----------------------------------------------------------
Invariant conversions!
-------------------------------------------------------------*)



Theorem lemma_inv_imp_inv_strong:
  fib_heap_inv fh xs ==> fib_heap_inv_strong fh xs
Proof
  simp[fib_heap_inv_def,fib_heap_inv_strong_def]
QED


Theorem lemma_inv_strong_imp_inv:
  fib_heap_inv_strong fh [x] ==> fib_heap_inv fh [x]
Proof
  Cases_on `x` >> fs[fib_heap_inv_strong_def, fib_heap_inv_def] >>
  rpt strip_tac >>
  simp[fts_is_min_def] >>
  fs[Once every_fts_def,fts_parent_lower_eq_def] >>
  simp[fts_hd_value_def]
QED



Theorem lemma_strong_inv_imp_inv_union:
  fib_heap_inv_strong fh xs ==> fib_heap_inv_union fh [(fh,xs)]
Proof
  strip_tac >>
  fs[fib_heap_inv_strong_def,fib_heap_inv_union_def] >>
  simp[all_disjoint_def,fh_union_def]
QED


(*
  first_x_assum $ irule_at $ Pos hd >>
  first_x_assum $ irule_at $ Pos hd >>
  fs[EVERY_MEM,FORALL_PROD] >>
  metis_tac[]
*)


Theorem lemma_fib_heap_union_merge:
  fib_heap_inv_union fh ((fhx,xs)::(fhy,ys)::rest) ==>
    fib_heap_inv_union fh (((FUNION fhx fhy),xs ++ ys)::rest)
Proof
  cheat
QED




Theorem lemma_fib_heap_union_reord:
  fib_heap_inv_union fh (cs ++ xs ++ ms ++ ys ++ qs) ==>
  fib_heap_inv_union fh (cs ++ ys ++ ms ++ xs ++ qs)
Proof
  fs[fib_heap_inv_union_def] >>
  fs[fh_union_append_thm,all_disjoint_append_thm] >>
  rpt strip_tac >> fs[] >> res_tac >> fs[DISJOINT_SYM] >>
  fs[GSYM EVERY_MEM] >>
  cheat
QED


(*-------------------------------------------------------------------
 Rebalancing of Trees
-------------------------------------------------------------------*)


Definition fts_merge_trees_def:
  fts_merge_trees (FibTree k1 v1 l1) (FibTree k2 v2 l2) =
    if v1.value <=+ v2.value then
      FibTree k1 v1 (fts_merge l1 [FibTree k2 v2 l2])
    else
      FibTree k2 v2 (fts_merge l2 [FibTree k1 v1 l1])
End


Theorem lemma_alookup_in_disjoint:
  fts_all_dist (FibTree k3 v3 l::t) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v (FibTree k3 v3 l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) /\
  fts_has k'' (fill_dnode v'' e m) [FibTree k' v' ys] /\
  ALOOKUP (flat_fts (FibTree k3 v3 l::t)) k'' = SOME x ==>
  F
Proof
  strip_tac >>
  res_tac >> pop_assum mp_tac >>
  pure_rewrite_tac[flookup_thm] >>
  strip_tac >>
  fs[DISJOINT_ALT] >>
  fs[Once MONO_NOT_EQ] >>
  last_x_assum (qspec_then `k''` assume_tac) >> rfs[] >>
  Cases_on `x` >>
  last_x_assum (qspecl_then [`k''`,`q`,`r`] assume_tac) >> fs[] >>
  rfs[FLOOKUP_DEF] >>
  `fts_all_dist (FibTree k3 v3 l::t)` by fs[fts_all_dist_def] >>
  pop_assum mp_tac >> pure_rewrite_tac[Once fts_has_cases] >>
  strip_tac >> fs[] >>
  imp_res_tac lemma_alookup_eq_fts_has >>
  first_x_assum (qspec_then `m'''` assume_tac) >> fs[]
QED



Theorem lemma_fts_has_merge_trees_lr:
  !xs ys fh1 fh2 k v k' v'.
  fts_all_dist [FibTree k v xs] /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e) ==>
    ∃m. fts_has k'' (fill_dnode v'' e m)
      [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    simp[FLOOKUP_SIMP] >> CASE_TAC
    >- (
      strip_tac >>
      simp[fts_merge_def] >>
      res_tac >>
      qexists `m` >> simp[Once fts_has_cases]
      ) >>
    strip_tac >> gvs[] >>
    qexists `m` >> simp[fts_merge_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    simp[Once fts_has_cases]
    ) >>
  Cases_on `h` >>
  simp[fts_merge_def] >>
  simp[FLOOKUP_SIMP] >> CASE_TAC
  >- (
    strip_tac >> res_tac >>
    qexists `m` >>
    IF_CASES_TAC
    >- (
      simp[Once fts_has_cases] >>
      once_rewrite_tac[GSYM APPEND] >>
      simp[fts_has_append_thm]
    ) >>
    simp[Once fts_has_cases] >>
    pure_rewrite_tac[Once lemma_cons_eq_append] >>
    simp[fts_has_append_thm]
  ) >>
  strip_tac >> gvs[] >>
  qexists `m` >>
  IF_CASES_TAC
  >- (
    simp[Once fts_has_cases] >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_has_append_thm] >>
    fs[Once fts_has_cases]
  ) >>
  simp[Once fts_has_cases] >>
  pure_rewrite_tac[Once lemma_cons_eq_append] >>
  simp[fts_has_append_thm] >>
  fs[Once fts_has_cases]
QED



Theorem lemma_fts_has_merge_trees_rl:
  !xs ys fh1 fh2 k v k' v'.
  fts_all_dist [FibTree k v xs] /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    (∃m. fts_has k'' (fill_dnode v'' e m)
      [FibTree k v (fts_merge xs [FibTree k' v' ys])]) ==>
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e)
Proof
  rpt strip_tac >>
  Cases_on `xs`
  >- (
    fs[fts_merge_def] >>
    pop_assum mp_tac >> simp[Once fts_has_cases] >> strip_tac
    >- (
      gvs[] >>
      simp[FLOOKUP_SIMP] >> CASE_TAC
      >- (
        last_x_assum(qspecl_then [`k`,`v''`,`e`] assume_tac) >> gvs[] >>
        first_x_assum(qspec_then `m` assume_tac) >> fs[Once fts_has_cases]
        ) >>
      Cases_on `x` >>
      res_tac >>
      fs[Once fts_has_cases,fill_dnode_def,data_node_component_equality] >>
      fs[Once fts_has_cases]
      )
    >- fs[Once fts_has_cases] >>
    res_tac >>
    simp[FLOOKUP_SIMP] >> CASE_TAC >>
    fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
    ) >>
  Cases_on `h` >> fs[fts_merge_def] >>
  pop_assum mp_tac >> IF_CASES_TAC
  >- (
    simp[Once fts_has_cases] >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_has_append_thm] >>
    simp[Once fts_has_cases] >>
    strip_tac
    >- (
      gvs[] >>
      simp[FLOOKUP_SIMP] >> CASE_TAC
      >- (
        last_x_assum(qspecl_then [`k`,`v''`,`e`] assume_tac) >> gvs[] >>
        first_x_assum(qspec_then `m` assume_tac) >> fs[Once fts_has_cases]
        ) >>
      Cases_on `x` >> gvs[] >>
      pop_assum mp_tac >>
      simp[Once fts_has_cases] >>
      simp[Once fts_has_cases] >>
      strip_tac
      >- fs[fill_dnode_def,data_node_component_equality] >>
      fs[fts_all_dist_def] >> res_tac
      )
    >- (
      simp[FLOOKUP_SIMP] >> CASE_TAC
      >- (
        last_x_assum(qspecl_then [`k''`,`v''`,`e`] assume_tac) >> gvs[] >>
        first_x_assum(qspec_then `m` assume_tac) >> fs[Once fts_has_cases]
        ) >>
      Cases_on `x` >>
      rfs[] >>
      rename [`fts_all_dist [FibTree k v (FibTree k3 v3 l::t)]`] >>
      `fts_has_inj [FibTree k v (FibTree k3 v3 l::t)]` by fs[fts_all_dist_def] >>
      fs[fts_has_inj_def] >>
      first_x_assum(qspecl_then [`k''`,`(fill_dnode q r m')`,`(fill_dnode v'' e m)`]
        assume_tac) >>
      rfs[] >>
      pop_assum mp_tac >> simp[Once fts_has_cases] >>
      simp[fill_dnode_def,data_node_component_equality]
      ) >>
    res_tac >>
    simp[FLOOKUP_SIMP] >> CASE_TAC >>
    fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
  ) >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[fts_has_append_thm] >>
  strip_tac
  >- (
    gvs[] >>
    simp[FLOOKUP_SIMP] >> CASE_TAC
    >- (
      last_x_assum(qspecl_then [`k`,`v''`,`e`] assume_tac) >> gvs[] >>
      first_x_assum(qspec_then `m` assume_tac) >> fs[Once fts_has_cases]
      ) >>
    Cases_on `x` >> res_tac >>
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    strip_tac
    >- fs[fill_dnode_def,data_node_component_equality] >>
    fs[fts_all_dist_def] >>
    res_tac
   )
  >- (
    res_tac >>
    simp[FLOOKUP_SIMP] >> CASE_TAC >>
    fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
    ) >>
  simp[FLOOKUP_SIMP] >> CASE_TAC
  >- (
    last_x_assum(qspecl_then [`k''`,`v''`,`e`] assume_tac) >> gvs[] >>
    first_x_assum(qspec_then `m` assume_tac) >> fs[Once fts_has_cases]
    ) >>
  Cases_on `x` >> res_tac >>
  rename [`fts_all_dist [FibTree k v (FibTree k3 v3 l::t)]`] >>
  `fts_has_inj [FibTree k v (FibTree k3 v3 l::t)]` by fs[fts_all_dist_def] >>
  fs[fts_has_inj_def] >>
  first_x_assum(qspecl_then [`k''`,`(fill_dnode q r m')`,`(fill_dnode v'' e m)`]
    assume_tac) >>
  rfs[] >>
  pop_assum mp_tac >> simp[Once fts_has_cases] >>
  simp[fill_dnode_def,data_node_component_equality]
QED




Theorem lemma_fts_has_merge_trees:
  !xs ys fh1 fh2 k v k' v'.
  fts_all_dist [FibTree k v xs] /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e) ⇔
    ∃m. fts_has k'' (fill_dnode v'' e m)
      [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  rpt strip_tac >>
  iff_tac
  >- (imp_res_tac lemma_fts_has_merge_trees_lr >> fs[]) >>
  imp_res_tac lemma_fts_has_merge_trees_rl >> fs[]
QED


Theorem lemma_fts_is_min_merge_trees:
  v.value <=+ v'.value /\
  fts_is_min v.value xs /\
  fts_is_min v'.value ys ==>
  fts_is_min v.value (fts_merge xs [FibTree k' v' ys])
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_merge_def] >>
    simp[fts_is_min_def] >>
    drule_all lemma_lower_eq_fts_is_min >> fs[]
    ) >>
  Cases_on `h` >>
  simp[fts_merge_def] >>
  IF_CASES_TAC
  >- (
    fs[fts_is_min_def] >>
    simp[fts_is_min_append_thm] >>
    simp[fts_is_min_def] >>
    irule lemma_lower_eq_fts_is_min >>
    qexists `v'.value` >> fs[]
    ) >>
  once_rewrite_tac[fts_is_min_def] >>
  drule_all lemma_lower_eq_fts_is_min >> fs[]
QED


Theorem lemma_fts_parent_lower_eq_merge_trees:
  every_fts fts_parent_lower_eq [FibTree k v xs] /\
  every_fts fts_parent_lower_eq [FibTree k' v' ys] /\
  v.value ≤₊ v'.value ==>
  every_fts fts_parent_lower_eq
   [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  fs[Once every_fts_def] >>
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_merge_def] >>
    fs[Once every_fts_def] >>
    fs[Once every_fts_def,fts_parent_lower_eq_def] >>
    simp[Once every_fts_def,fts_is_min_def] >>
    gvs[fts_is_min_def] >>
    imp_res_tac lemma_lower_eq_fts_is_min >> fs[] >>
    rpt strip_tac >> res_tac
    ) >>
  Cases_on `h` >> simp[fts_merge_def] >>
  IF_CASES_TAC
  >- (
    fs[Once every_fts_def,fts_parent_lower_eq_def] >>
    fs[fts_is_min_def] >>
    simp[fts_is_min_append_thm] >>
    simp[fts_is_min_def] >>
    conj_tac
    >- (irule lemma_lower_eq_fts_is_min >> qexists `v'.value` >> fs[]) >>
    simp[Once every_fts_def,fts_parent_lower_eq_def] >>
    simp[fts_parent_lower_eq_append_thm] >>
    simp[fts_parent_lower_eq_def] >>
    rpt strip_tac >> gvs[] >>
    res_tac
    ) >>
  fs[Once every_fts_def,fts_parent_lower_eq_def] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[fts_is_min_append_thm] >>
  simp[fts_is_min_def] >>
  conj_tac
  >- (irule lemma_lower_eq_fts_is_min >> qexists `v'.value` >> fs[]) >>
  simp[Once every_fts_def,fts_parent_lower_eq_def] >>
  rpt strip_tac >> gvs[] >>
  res_tac
QED


Theorem lemma_arithm_add_tree:
  LENGTH t + 1 = LENGTH ys /\
  fib_num (LENGTH t + 3) ≤ fts_size l + (fts_size t + 2) /\
  fib_num (LENGTH ys + 2) ≤ fts_size ys + 1 ==>
  fib_num (LENGTH ys + 3) ≤
  fts_size l + (fts_size t + (fts_size ys + 3))
Proof
  strip_tac >>
  imp_res_tac EQ_SYM >>
  qpat_x_assum `LENGTH t + 1 = LENGTH ys` kall_tac >>
  simp[Once fib_num_def] >> gvs[] >>
  qpat_x_assum `fib_num (LENGTH t + 3) ≤ fts_size t + (fts_size l + 2)` mp_tac >>
  simp[Once fib_num_def]
QED



Theorem lemma_fib_heap_shape_ok_merge_trees:
  LENGTH xs = LENGTH ys /\
  fib_heap_shape_ok [FibTree k v xs] /\
  fib_heap_shape_ok [FibTree k' v' ys] ==>
  fib_heap_shape_ok [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_merge_def] >>
    fs[fib_heap_shape_ok_def] >>
    simp[fts_size_def] >>
    simp[Ntimes fib_num_def 5] >>
    simp[Once fib_num_def] >>
    simp[Once fib_num_def]
    ) >>
  Cases_on `h` >>
  simp[fts_merge_def] >>
  IF_CASES_TAC
  >- (
    fs[fib_heap_shape_ok_def] >>
    simp[fib_heap_shape_ok_append_thm] >>
    fs[fib_heap_shape_ok_def] >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_size_append_thm] >>
    fs[SUC_ONE_ADD] >>
    fs[fts_size_def] >>
    imp_res_tac lemma_arithm_add_tree
    ) >>
  fs[fib_heap_shape_ok_def] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[fts_size_append_thm] >>
  fs[fts_size_def] >>
  fs[SUC_ONE_ADD] >>
  imp_res_tac lemma_arithm_add_tree
QED




Theorem lemma_fts_has_first:
  (FLOOKUP fh k = SOME (v.value,v.edges) ⇔
   ∃m. fts_has k (fill_dnode v.value v.edges m) (FibTree k v l::rest))
  ==>
  FLOOKUP fh k = SOME (v.value,v.edges)
Proof
  strip_tac >>
  fs[fts_all_dist_def] >>
  Cases_on `?m. fts_has k (fill_dnode v.value v.edges m) (FibTree k v l::rest)` >>
  fs[]
  >- (qexists `m` >> simp[]) >>
  first_x_assum(qspec_then `v.mark` assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases,fill_dnode_def,data_node_component_equality]
QED



Theorem lemma_fts_has_in_map:
  (!k' v' e'. FLOOKUP fh k' = SOME (v',e') ⇔
   ∃m. fts_has k' (fill_dnode v' e' m) xs) /\
  fts_has k' v' xs
  ==>
  FLOOKUP fh k' = SOME (v'.value,v'.edges)
Proof
  strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum(qspecl_then [`k'`,`v'.value`,`v'.edges`] assume_tac) >>
  fs[] >>
  first_x_assum(qspec_then `v'.mark` assume_tac) >>
  fs[fill_dnode_def,lemma_data_node_cases]
QED




Theorem lemma_fts_has_both_maps_first_contra:
  fts_has k v2 ys /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) ys) /\
  fts_all_dist ys /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  F
Proof
  strip_tac >>
  `FLOOKUP fh2 k = SOME (v2.value,v2.edges)` by
    imp_res_tac lemma_fts_has_in_map >>
  last_x_assum(qspecl_then [`k`,`v.value`,`v.edges`] assume_tac) >>
  imp_res_tac lemma_fts_has_first >>
  fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
QED


Theorem lemma_fts_has_child_in_map:
  fts_has k3 v3 (FibTree k2 v2 l::t) /\
  (∀k' v' e. FLOOKUP fh k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v (FibTree k2 v2 l::t)]) ==>
  FLOOKUP fh k3 = SOME (v3.value,v3.edges)
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum(qspecl_then [`k3`,`v3.value`,`v3.edges`] assume_tac) >> fs[] >>
  first_x_assum(qspec_then `v3.mark` assume_tac) >>
  fs[fill_dnode_def,lemma_data_node_cases] >>
  pop_assum mp_tac >> simp[Once fts_has_cases]
QED


Theorem lemma_fts_has_both_maps_child_contra:
  fts_has k3 v3 (FibTree k2 v2 l::t) /\
  fts_has k3 v4 ys /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v (FibTree k2 v2 l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) ys) ==>
  F
Proof
  rpt strip_tac >>
  imp_res_tac lemma_fts_has_child_in_map >>
  imp_res_tac lemma_fts_has_in_map >>
  fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
QED




Theorem lemma_fts_has_inj_merge_succ:
  fts_all_dist [FibTree k v (FibTree k'' v'' l::t)] /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v (FibTree k'' v'' l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  fts_has_inj [FibTree k v (FibTree k'' v'' l::(t ++ [FibTree k' v' ys]))]
Proof
  strip_tac >>
  simp[fts_has_inj_def] >> rpt gen_tac >>
  once_rewrite_tac[fts_has_cases] >> simp[] >>
  simp[Once fts_has_cases] >>
  rename[`(k = k3 ∧ v = v3 ∨ fts_has k3 v3
    (FibTree k2 v2 l::(t ++ [FibTree k' v' ys]))) ∧
    (k = k3 ∧ v = v4 ∨ fts_has k3 v4 [] ∨
     fts_has k3 v4 (FibTree k2 v2 l::(t ++ [FibTree k' v' ys])))`] >>
  rpt strip_tac >> gvs[]
  >- fs[Once fts_has_cases]
  >- (
    pop_assum mp_tac >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_has_append_thm] >>
    rpt strip_tac
    >- (fs[fts_all_dist_def] >> res_tac) >>
    imp_res_tac lemma_fts_has_both_maps_first_contra
    )
  >- (
    pop_assum mp_tac >>
    once_rewrite_tac[GSYM APPEND] >>
    simp[fts_has_append_thm] >>
    rpt strip_tac
    >- (fs[fts_all_dist_def] >> res_tac) >>
    imp_res_tac lemma_fts_has_both_maps_first_contra
    )
  >- fs[Once fts_has_cases] >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  once_rewrite_tac[GSYM APPEND] >>
  simp[fts_has_append_thm] >>
  rpt strip_tac
  >- (
    `fts_has_inj [FibTree k v (FibTree k2 v2 l::t)]` by fs[fts_all_dist_def] >>
    fs[fts_has_inj_def] >>
    first_x_assum(qspecl_then [`k3`,`v3`,`v4`] assume_tac) >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[]
    )
  >- imp_res_tac lemma_fts_has_both_maps_child_contra
  >- imp_res_tac lemma_fts_has_both_maps_child_contra >>
  `fts_has_inj [FibTree k' v' ys]` by fs[fts_all_dist_def] >>
  fs[fts_has_inj_def] >>
  first_x_assum(qspecl_then [`k3`,`v3`,`v4`] assume_tac) >> res_tac
QED


Theorem lemma_fts_all_dist_merge_succ:
  fts_all_dist [FibTree k v (FibTree k'' v'' l::t)] /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v (FibTree k'' v'' l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  fts_all_dist [FibTree k v (FibTree k'' v'' l::(t ++ [FibTree k' v' ys]))]
Proof
  strip_tac >> simp[fts_all_dist_def] >>
  rpt conj_tac
  >- imp_res_tac lemma_fts_has_inj_merge_succ
  >- (
    gen_tac >>
    once_rewrite_tac[GSYM APPEND] >> simp[fts_has_append_thm] >>
    rpt conj_tac
    >- fs[fts_all_dist_def]
    >- (
      spose_not_then assume_tac >>
      imp_res_tac lemma_fts_has_both_maps_first_contra
      ) >>
    fs[fts_all_dist_def]
    )
  >- (
    once_rewrite_tac[GSYM APPEND] >> simp[fts_has_inj_append] >>
    `fts_has_inj [FibTree k' v' ys]` by fs[fts_all_dist_def] >>
    `fts_has_inj (FibTree k'' v'' l::t)` by fs[fts_all_dist_def] >>
    fs[] >> rpt strip_tac >>
    imp_res_tac lemma_fts_has_both_maps_child_contra
    )
  >- (
    gen_tac >>
    simp[fts_has_append_thm] >>
    rpt conj_tac
    >- fs[fts_all_dist_def]
    >- fs[fts_all_dist_def] >>
    spose_not_then assume_tac >>
    qspecl_then [`k''`, `v''`,`t`,`l`] assume_tac (cj 1 fts_has_rules) >>
    imp_res_tac lemma_fts_has_both_maps_child_contra
    )
  >- fs[fts_all_dist_def]
  >- (
    simp[fts_all_dist_append_thm] >>
    simp[fts_has_inj_append] >>
    rpt strip_tac
    >- (fs[fts_all_dist_def] >> imp_res_tac lemma_fts_has_inj_ts)
    >- fs[fts_all_dist_def]
    >- (
      rename [`fts_has k3 v3 t`,`fts_has k3 v4 [FibTree k' v' ys]`] >>
      qspecl_then [`k3`,`v3`,`k''`,`t`,`l`,`v''`] assume_tac (cj 2 fts_has_rules) >>
      res_tac >>
      imp_res_tac lemma_fts_has_both_maps_child_contra
      )
    >- fs[fts_all_dist_def] >>
    rename [`fts_has k3 v3 t`,`fts_has k3 v4 [FibTree k' v' ys]`] >>
    qspecl_then [`k3`,`v4`,`k''`,`t`,`l`,`v''`] assume_tac (cj 2 fts_has_rules) >>
    res_tac >>
    imp_res_tac lemma_fts_has_both_maps_child_contra
    )
  >- (
    rpt strip_tac >>
    pop_assum mp_tac >> simp[fts_has_append_thm] >>
    rpt strip_tac
    >- (fs[fts_all_dist_def] >> res_tac) >>
    rename [`fts_has k3 v3 l`,`fts_has k3 v4 [FibTree k' v' ys]`] >>
    qspecl_then [`k3`,`v4`,`k''`,`t`,`l`,`v''`] assume_tac (cj 3 fts_has_rules) >>
    res_tac >>
    imp_res_tac lemma_fts_has_both_maps_child_contra
    ) >>
  rpt strip_tac >> fs[Once fts_has_cases]
QED




Theorem lemma_cons_eq_append_nested_fts:
  (FibTree k v l::FibTree k' v' l'::rest) =
  [FibTree k v l] ++ (FibTree k' v' l'::rest)
Proof
  simp[]
QED




Theorem lemma_fts_all_dist_merge_trees:
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (fill_dnode v' e m) [FibTree k v xs]) /\
  fts_all_dist [FibTree k v xs] /\
  (∀k v e.
     FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' ys]) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  fts_all_dist [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_merge_def] >>
    simp[fts_all_dist_def] >>
    rpt conj_tac
    >- (
      simp[fts_has_inj_def] >> rpt gen_tac >>
      once_rewrite_tac[fts_has_cases] >> simp[] >>
      simp[Once fts_has_cases] >>
      rename[`(k = k2 ∧ v = v2 ∨ fts_has k2 v2 [FibTree k' v' ys]) ∧
        (k = k2 ∧ v = v3 ∨ fts_has k2 v3 [] ∨
         fts_has k2 v3 [FibTree k' v' ys])`] >>
      rpt strip_tac >> gvs[]
      >- fs[Once fts_has_cases]
      >- imp_res_tac lemma_fts_has_both_maps_first_contra
      >- imp_res_tac lemma_fts_has_both_maps_first_contra
      >- fs[Once fts_has_cases] >>
      fs[fts_all_dist_def,fts_has_inj_def] >>
      res_tac
      )
    >- (
      rpt strip_tac
      >- imp_res_tac lemma_fts_has_both_maps_first_contra >>
      fs[Once fts_has_cases]
      ) >>
    rpt strip_tac >>
    fs[Once fts_has_cases]
    ) >>
  Cases_on `h` >> simp[fts_merge_def] >>
  IF_CASES_TAC
  >- imp_res_tac lemma_fts_all_dist_merge_succ >>
  once_rewrite_tac[lemma_cons_eq_append_nested_fts] >>
  irule lemma_fts_all_dist_sym_succ >>
  simp[] >>
  imp_res_tac lemma_fts_all_dist_merge_succ
QED



Theorem logical_fts_merge_trees:
  !xs ys fh1 fh2 k v k' v'.
  LENGTH xs = LENGTH ys /\
  fib_heap_inv fh1 [FibTree k v xs] /\
  fib_heap_inv fh2 [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  v.value <=+ v'.value ==>
  fib_heap_inv (FUNION fh1 fh2) [FibTree k v (fts_merge xs [FibTree k' v' ys])]
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_def] >>
  drule_all lemma_fts_has_merge_trees >>
  strip_tac >>
  fs[] >>
  simp[FLOOKUP_SIMP] >>
  CASE_TAC >> fs[] >>
  fs[fts_is_min_def,fts_hd_value_def] >>
  fs[lemma_lower_eq_fts_is_min] >>
  fs[lemma_fts_is_min_merge_trees] >>
  fs[lemma_fts_parent_lower_eq_merge_trees] >>
  fs[lemma_fib_heap_shape_ok_merge_trees] >>
  imp_res_tac lemma_fts_all_dist_merge_trees
QED



Theorem fts_merge_trees:
  !fh1 fh2 k v l k' v' l'.
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv fh2 [FibTree k' v' l'] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH l = LENGTH l' ==>
  fib_heap_inv (FUNION fh1 fh2) [fts_merge_trees (FibTree k v l) (FibTree k' v' l')]
Proof
  rpt strip_tac >>
  fs[fts_merge_trees_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> strip_tac >> gvs[]
  >- (irule logical_fts_merge_trees >> fs[]) >>
  fs[WORD_NOT_LOWER_EQUAL] >>
  imp_res_tac WORD_LOWER_IMP_LOWER_OR_EQ >>
  qspecl_then [`l'`,`l`,`fh2`,`fh1`,`k'`,`v'`,`k`,`v`]
    assume_tac logical_fts_merge_trees >>
  gvs[DISJOINT_SYM] >>
  imp_res_tac FUNION_COMM >>
  cheat
QED



Definition fts_link_trees_def:
  fts_link_trees (c: num) rl (FibTree k v l) =
    if c = 0 then (rl,F) else
    if 196 <= (LENGTH l) then (rl,F) else
    case EL (LENGTH l) rl of
     |SOME(FibTree k' v' l') =>
        fts_link_trees (c - 1) (LUPDATE NONE (LENGTH l) rl)
          (fts_merge_trees (FibTree k v l) (FibTree k' v' l'))
     |NONE =>
        (LUPDATE (SOME(FibTree k v l)) (LENGTH l) rl,T)
End


Theorem lemma_fts_merge_suc_length:
  LENGTH (fts_merge l [FibTree k' v' l']) = if l = [] then 1 else LENGTH l + 1
Proof
  Cases_on `l` >> gvs[fts_merge_def] >>
  Cases_on `h` >> gvs[fts_merge_def] >>
  rw[]
QED



Definition fts_link_trees2_def:
  fts_link_trees2 rl (FibTree k v l) =
    if 196 <= (LENGTH l) then (rl,F) else
    case EL (LENGTH l) rl of
     |SOME(FibTree k' v' l') =>
        if LENGTH l <> LENGTH l' then (rl,F) else
        fts_link_trees2 (LUPDATE NONE (LENGTH l) rl)
          (fts_merge_trees (FibTree k v l) (FibTree k' v' l'))
     |NONE =>
        (LUPDATE (SOME(FibTree k v l)) (LENGTH l) rl,T)
Termination
  WF_REL_TAC `measure $ \(rl,ft). case ft of FibTree k v l => 196 - LENGTH l` >>
  rw[] >>
  CASE_TAC >> gvs[] >>
  fs[fts_merge_trees_def,AllCaseEqs()] >> gvs[] >>
  rw[lemma_fts_merge_suc_length] >> gvs[]
End


Definition fhts_to_ts_def:
  fhts_to_ts fhts = GENLIST (\n. SND (EL n fhts)) (LENGTH fhts)
End


Definition ts_to_fhts_def:
  ts_to_fhts ts =
    GENLIST
      (\n. case EL n ts of
             |NONE => (FEMPTY,NONE)
             |SOME(t) => (alist_to_fmap (flat_fts [t]), SOME(t)))
      (LENGTH ts)
End


Theorem lemma_ts_to_fhts_to_map:
  ts_to_fhts ts =
    MAP
      (\n. case n of
             |NONE => (FEMPTY,NONE)
             |SOME(t) => (alist_to_fmap (flat_fts [t]), SOME(t)))
      ts
Proof
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[LIST_EQ_REWRITE] >>
  simp[EL_MAP]
QED


(*
Theorem lemma_nested_ts_to_fhts_fhts_to_ts:
  (ts_to_fhts (LUPDATE (SOME(FibTree k v l)) (LENGTH l) (fhts_to_ts list)) =
  *)

Theorem lemma_inv_imp_alist_to_fmap_inv:
  fib_heap_inv fh fts ==>
  fib_heap_inv (alist_to_fmap (flat_fts fts)) fts
Proof
  strip_tac >>
  Cases_on `fts`
  >- fs[alist_to_fmap_def,flat_fts_def,fib_heap_inv_empty_thm] >>
  Cases_on `h` >>
  fs[fib_heap_inv_def] >>
  rpt strip_tac
  >- (
    Cases_on `v'` >>
    imp_res_tac lemma_alookup_eq_fts_has >>
    res_tac >> gvs[]
    ) >>
  fs[lemma_alookup_eq_fts_has]
QED




Theorem lemma_fts_has_eq_mem_fst_flat_fts:
  !fts.
   (?v. fts_has k v fts) <=> MEM k (MAP FST (flat_fts fts))
Proof
  ho_match_mp_tac flat_fts_ind >> rpt strip_tac
  >- simp[Once fts_has_cases,flat_fts_def] >>
  fs[MEM_MAP] >>
  rename [`(FibTree k' v' l'::fts)`] >>
  iff_tac >> strip_tac
  >- (
    pop_assum mp_tac >> simp[Once fts_has_cases] >> strip_tac
    >- (
      qexistsl [`(k,v.value,v.edges)`] >>
      fs[lemma_mem_eq_fts_has] >>
      qexists `v.mark` >>
      simp[Once fts_has_cases,fill_dnode_def,data_node_component_equality]
      )
    >- (
      res_tac >>
      Cases_on `y` >> Cases_on `r` >>
      gvs[] >>
      rename [`MEM (k,v'',e'') (flat_fts fts)`] >>
      qexists `(k,v'',e'')` >> fs[] >>
      simp[flat_fts_def]
      ) >>
    res_tac >>
    Cases_on `y` >> Cases_on `r` >>
    gvs[] >>
    rename [`MEM (k,v'',e'') (flat_fts fts)`] >>
    qexists `(k,v'',e'')` >> fs[] >>
    simp[flat_fts_def]
    ) >>
  Cases_on `y` >> Cases_on `r` >>  gvs[] >>
  rename [`MEM (k,v'',e'') (flat_fts (FibTree k' v' l'::fts))`] >>
  fs[lemma_mem_eq_fts_has] >>
  qexists `(fill_dnode v'' e'' m)`>> simp[]
QED




Theorem lemma_fdom_fh_eq_fdom_alist_to_fmap:
  !fh fts.
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (fill_dnode v e m) fts)
    ==>
    (FDOM fh) = (FDOM (alist_to_fmap (flat_fts fts)))
Proof
  rpt strip_tac >>
  simp[EXTENSION] >>
  strip_tac >>
  Cases_on `FLOOKUP fh x`
  >- (
    fs[FLOOKUP_DEF] >>
    first_x_assum (qspec_then `x` assume_tac) >> rfs[] >>
    spose_not_then assume_tac >>
    imp_res_tac lemma_fts_has_eq_mem_fst_flat_fts >>
    first_x_assum (qspecl_then [`v.value`,`v.edges`,`v.mark`] assume_tac) >>
    fs[fill_dnode_def,data_node_component_equality,lemma_data_node_cases]
    ) >>
  Cases_on `x'` >>
  rename [`FLOOKUP fh x = SOME (v,e)`] >>
  fs[FLOOKUP_DEF] >>
  res_tac >>
  imp_res_tac lemma_fts_has_eq_mem_fst_flat_fts
QED



Theorem lemma_alist_to_fmap_flookup:
  !fts x.
  MEM x (MAP FST (flat_fts fts)) ==>
  ?y.  FLOOKUP (alist_to_fmap (flat_fts fts)) x = y
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- fs[flat_fts_def] >>
  fs[]
QED



Theorem lemma_fh_submap_alist_to_fmap:
  !fh fts.
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (fill_dnode v e m) fts) /\
    fts_all_dist fts
    ==>
    fh SUBMAP (alist_to_fmap (flat_fts fts))
Proof
  rpt strip_tac >>
  simp[TO_FLOOKUP] >>
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  dep_rewrite.DEP_REWRITE_TAC[GSYM MEM_ALOOKUP] >>
  simp[lemma_flat_fts_all_distinct] >>
  simp[lemma_mem_eq_fts_has] >>
  pop_assum $ irule_at Any
QED



Theorem lemma_inv_union_el:
  i < LENGTH list /\
  (EL i list) = (m,SOME(x)) /\
  (EVERY (λ(fh,O_ft). case O_ft of
    |NONE => fib_heap_inv fh []
    | SOME ft => fib_heap_inv fh [ft]) list)
  ==>
  fib_heap_inv m [x]
Proof
  rpt strip_tac >>
  fs[EVERY_EL] >>
  res_tac >>
  Cases_on `EL i list` >> gvs[]
QED





Theorem lemma_inv_union_el_submap:
  i < LENGTH list /\
  (EL i list) = (m,SOME (x)) /\
  fh1 = fh_union list /\
  all_disjoint list ==>
  m SUBMAP (fh_union list)
Proof
  strip_tac >>
  Cases_on `list`
  >- fs[] >>
  Cases_on `h` >> fs[fh_union_def] >>
  Cases_on `i = 0`
  >- fs[SUBMAP_FUNION] >>
  fs[EL_CONS_IF] >>
  fs[PRE_SUB1] >>
  fs[all_disjoint_def] >>
  fs[EVERY_EL] >>
  Cases_on `i` >> fs[] >>
  res_tac >>
  Cases_on `EL n t` >> fs[] >>
  drule_all EL_MEM >> strip_tac >>
  gvs[] >>
  drule_all fh_union_mem_submap_thm >> strip_tac >>
  fs[SUBMAP_FUNION,DISJOINT_SYM]
QED


Theorem fib_heap_inv_union2_el_thm:
  !i list m x fh1.
  i < LENGTH list /\
  (EL i list) = (m,SOME(x)) /\
  fib_heap_inv_union2 fh1 list ==>
  ?fh2. fib_heap_inv fh2 [x] /\ fh2 SUBMAP fh1
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  drule_all lemma_inv_union_el >> strip_tac >>
  drule_all EL_MEM >> strip_tac >>
  gvs[] >>
  qexists `m` >> fs[] >>
  imp_res_tac fh_union_mem_submap_thm
QED


Theorem lemma_fh_union_el_snd:
  i < LENGTH list /\
  SND (EL i list) = SOME(x) /\
  fib_heap_inv_union2 (fh_union list) list
  ==>
  ?fh. fib_heap_inv fh [x] /\ fh SUBMAP (fh_union list)
Proof
  strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  Cases_on `EL i list` >> gvs[] >>
  drule_all lemma_inv_union_el >> strip_tac >>
  drule_all EL_MEM >> strip_tac >>
  gvs[] >>
  qexists `q` >> fs[] >>
  imp_res_tac fh_union_mem_submap_thm
QED


Theorem lemma_fts_link_list_upd_all_disjoint_lupdate:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (MAP SND rl)❲i❳ = SOME x /\
  i < LENGTH rl
  ==>
  DISJOINT (set (MAP FST (flat_fts [x])))
    (set (MAP FST (flat_fts [FibTree k v l])))
Proof
  strip_tac >>
  fs[EL_MAP] >>
  fs[fib_heap_inv_strong_def] >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >> gvs[] >>
  imp_res_tac lemma_fh_union_el_snd >>
  fs[fib_heap_inv_union2_def] >> gvs[] >>
  imp_res_tac SUBMAP_FDOM_SUBSET >>
  imp_res_tac DISJOINT_SUBSET >>
  qpat_x_assum `fib_heap_inv fh [x]` mp_tac >>
  simp[fib_heap_inv_def] >> strip_tac >>
  drule lemma_fdom_fh_eq_fdom_alist_to_fmap >>
  strip_tac >> fs[DISJOINT_SYM]
QED


Theorem lemma_fts_link_list_upd_all_disjoint:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = 196 /\
  ¬(196 ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  all_disjoint
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)
Proof
  strip_tac >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  pure_rewrite_tac[fhts_to_ts_def] >>
  pure_rewrite_tac[GENLIST_EL_MAP] >>
  pure_rewrite_tac[ts_to_fhts_def] >>
  pure_rewrite_tac[LENGTH_LUPDATE,LENGTH_MAP] >>
  pure_rewrite_tac[all_disjoint_genlist_thm] >>
  rpt strip_tac >> simp[] >>
  qpat_abbrev_tac `xs = (MAP SND rl)❲LENGTH l ↦ SOME (FibTree k v l)❳` >>
  Cases_on `EL i xs` >> Cases_on `EL j xs` >> simp[] >>
  Cases_on `i = LENGTH l` >> Cases_on `j = LENGTH l` >> fs[] >>
  unabbrev_all_tac
  >- (
    `j < LENGTH rl` by gvs[] >>
    fs[EL_LUPDATE] >>
    drule_all lemma_fts_link_list_upd_all_disjoint_lupdate >>
    gvs[DISJOINT_SYM]
    )
  >- (
    `i < LENGTH rl` by gvs[] >>
    fs[EL_LUPDATE] >>
    drule_all lemma_fts_link_list_upd_all_disjoint_lupdate >>
    gvs[DISJOINT_SYM]
    ) >>
  fs[EL_LUPDATE] >>
  rfs[EL_MAP] >>
  Cases_on `EL i rl` >> Cases_on `EL j rl` >> gvs[] >>
  fs[fib_heap_inv_union2_def] >>
  `i < LENGTH rl /\ j < LENGTH rl` by gvs[] >>
  drule_all all_disjoint_el_thm >>
  strip_tac >> gvs[] >>
  fs[fib_heap_inv_strong_def] >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >> gvs[] >>
  imp_res_tac lemma_fh_union_el_snd >>
  `i < LENGTH rl /\ j < LENGTH rl` by gvs[] >>
  imp_res_tac lemma_inv_union_el >>
  fs[fib_heap_inv_def] >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >>
  gvs[]
QED



Theorem lemma_fh_eq_alist_to_fmap:
  !fh fts.
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (fill_dnode v e m) fts) /\
    fts_all_dist fts
    ==>
    fh = alist_to_fmap (flat_fts fts)
Proof
  rpt strip_tac >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >>
  imp_res_tac lemma_fh_submap_alist_to_fmap >>
  imp_res_tac EQ_FDOM_SUBMAP
QED


Theorem lemma_fts_link_list_upd_inv:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = 196 /\
  ¬(196 ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  EVERY
    (λ(fh,O_ft).
         case O_ft of
           NONE => fib_heap_inv fh []
         | SOME ft => fib_heap_inv fh [ft])
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)
Proof
  pure_rewrite_tac[fhts_to_ts_def] >>
  pure_rewrite_tac[GENLIST_EL_MAP] >>
  pure_rewrite_tac[ts_to_fhts_def] >>
  pure_rewrite_tac[EVERY_GENLIST] >>
  rpt strip_tac >>
  simp[] >>
  CASE_TAC
  >- simp[fib_heap_inv_empty_thm] >>
  simp[] >>
  Cases_on `x` >>
  fs[EL_LUPDATE] >>
  pop_assum mp_tac >> IF_CASES_TAC >> fs[]
  >- (
    strip_tac >> gvs[] >>
    imp_res_tac lemma_inv_strong_imp_inv >>
    irule lemma_inv_imp_alist_to_fmap_inv >>
    qexists `fh1` >> simp[]
    ) >>
  strip_tac >>
  rfs[EL_MAP] >>
  fs[fib_heap_inv_union2_def] >>
  fs[EVERY_EL] >>
  res_tac >>
  Cases_on `EL i rl` >> fs[] >>
  gvs[] >>
  `∀k v e. FLOOKUP q k = SOME (v,e) ⇔
    ∃m. fts_has k (fill_dnode v e m) [FibTree k' v' l']` by fs[fib_heap_inv_def] >>
  `fts_all_dist [FibTree k' v' l']` by fs[fib_heap_inv_def] >>
  drule lemma_fh_eq_alist_to_fmap >> strip_tac >>
  gvs[]
QED






Theorem lemma_fh_union_eq_fh_union_alist_to_fmap:
  (EVERY (λ(fh,O_ft).
    case O_ft of
     | NONE => fib_heap_inv fh []
     | SOME ft => fib_heap_inv fh [ft]) list) /\
  all_disjoint list
  ==>
  fh_union list = fh_union
    (MAP (\n. case n of
      |NONE => (FEMPTY,NONE)
      |SOME t => (alist_to_fmap(flat_fts [t]) ,SOME t))
    (MAP SND list))
Proof
  strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  simp[MAP_MAP_o] >>
  simp[fh_union_foldl_thm] >>
  simp[rich_listTheory.FOLDL_MAP] >>
  irule FOLDL_CONG >> rpt strip_tac >> fs[] >>
  Cases_on `x` >> fs[] >>
  rename [`MEM (m,t) list`] >>
  Cases_on `t` >> fs[]
  >- ( imp_res_tac EVERY_MEM >> fs[lemma_empty_heap]) >>
  imp_res_tac EVERY_MEM >>
  fs[] >>
  qsuff_tac `m = alist_to_fmap (flat_fts [x])` >> gvs[] >>
  fs[fib_heap_inv_def] >>
  imp_res_tac lemma_fh_eq_alist_to_fmap
QED



Theorem lemma_fh_union_disjoint_rm_fst:
  (∀x y.
    MEM x ys1 ∧ (y = (FEMPTY,NONE) ∨ MEM y ys2) ⇒
    DISJOINT (FDOM (FST x)) (FDOM (FST y)))
  ==>
  (∀x y.
    MEM x ys1 ∧ MEM y ys2 ⇒
    DISJOINT (FDOM (FST x)) (FDOM (FST y)))
Proof
  rpt strip_tac >>
  res_tac
QED


Theorem lemma_fts_link_list_upd_fh_union:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = 196 /\
  ¬(196 ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  fh1 ⊌ fh2 =
  fh_union (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)
Proof
  strip_tac >>
  pure_rewrite_tac[fhts_to_ts_def] >>
  pure_rewrite_tac[GENLIST_EL_MAP] >>
  pure_rewrite_tac[lemma_ts_to_fhts_to_map] >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  drule LESS_LENGTH >> strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  `LENGTH l = LENGTH (MAP SND ys1)` by simp[] >>
  asm_rewrite_tac[LUPDATE_LENGTH] >>
  asm_rewrite_tac[MAP_APPEND,MAP] >>
  simp[fh_union_append_thm,fh_union_def] >>
  fs[fib_heap_inv_union2_def] >>
  simp[fh_union_append_thm] >>
  qpat_x_assum `EL (LENGTH ys) (fhts_to_ts(ys1 ++ y::ys2)) = NONE` mp_tac >>
  rewrite_tac[fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  rewrite_tac[MAP_APPEND] >>
  simp[EL_APPEND_EQN] >>
  strip_tac >>
  Cases_on `y` >> fs[] >>
  imp_res_tac lemma_empty_heap >> gvs[] >>
  fs[fh_union_append_thm] >>
  fs[fh_union_def] >>
  fs[all_disjoint_append_thm,all_disjoint_def] >>
  imp_res_tac lemma_fh_union_eq_fh_union_alist_to_fmap >>
  fs[fib_heap_inv_strong_def] >>
  imp_res_tac lemma_fh_eq_alist_to_fmap >> gvs[] >>
  qpat_abbrev_tac `ys' = (MAP (λn.
    case n of
      NONE => (FEMPTY,NONE)
     | SOME t => (alist_to_fmap (flat_fts [t]),SOME t))
  (MAP SND ys1))` >>
  qpat_abbrev_tac `ys'' = (MAP (λn.
    case n of
      NONE => (FEMPTY,NONE)
     | SOME t => (alist_to_fmap (flat_fts [t]),SOME t))
  (MAP SND ys2))` >>
  drule lemma_fh_union_disjoint_rm_fst >> strip_tac >>
  drule_all lemma_fh_union_disjoint >> strip_tac >>
  gvs[] >>
  qpat_x_assum `DISJOINT (FDOM (fh_union ys'))
    (set (MAP FST (flat_fts [FibTree k v l])))` mp_tac >>
  qpat_x_assum `DISJOINT (FDOM (fh_union ys''))
    (set (MAP FST (flat_fts [FibTree k v l])))` mp_tac >>
  rewrite_tac[GSYM FDOM_alist_to_fmap] >>
  once_rewrite_tac[DISJOINT_SYM] >>
  rpt strip_tac >>
  simp[FUNION_ASSOC] >>
  qspecl_then [`alist_to_fmap (flat_fts [FibTree k v l])`,`fh_union ys'`]
    assume_tac FUNION_COMM >>
  res_tac >>
  simp[]
QED


Theorem lemma_length_fhts_tofrom_ts:
  LENGTH (ts_to_fhts (LUPDATE x n (fhts_to_ts list))) = LENGTH list
Proof
  rewrite_tac[fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[LENGTH_GENLIST] >>
  simp[LENGTH_MAP]
QED



Theorem lemma_fts_link_list_upd_array_inv:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = 196 /\
  ¬(196 ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  (∀n map k' v' l'.
    (n < LENGTH (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)) /\
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)❲n❳ =
    (map,SOME (FibTree k' v' l')) ⇒
    LENGTH l' = n)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  pop_assum mp_tac >>
  rewrite_tac[fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  rewrite_tac[ts_to_fhts_def] >>
  pop_assum mp_tac >>
  rewrite_tac[lemma_length_fhts_tofrom_ts] >>
  strip_tac >>
  rewrite_tac[LENGTH_LUPDATE,LENGTH_MAP] >>
  simp[EL_GENLIST] >>
  CASE_TAC >>
  strip_tac >> gvs[] >>
  `n < LENGTH rl` by gvs[] >>
  fs[EL_LUPDATE,AllCaseEqs()] >>
  fs[EL_MAP] >>
  Cases_on `EL n rl` >> gvs[]
QED


Theorem lemma_fts_link_list_upd:
  fib_heap_inv_strong fh1 [FibTree k v l] /\
  fib_heap_inv_union2 fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = 196 /\
  ¬(196 ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  fib_heap_inv_union2 (fh1 ⊌ fh2)
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)
Proof
  strip_tac >>
  simp[fib_heap_inv_union2_def] >>
  rpt conj_tac
  >- imp_res_tac lemma_fts_link_list_upd_inv
  >- imp_res_tac lemma_fts_link_list_upd_all_disjoint
  >- imp_res_tac lemma_fts_link_list_upd_fh_union >>
  rpt strip_tac >>
  imp_res_tac lemma_fts_link_list_upd_array_inv
QED








Theorem lemma_disjoint_lupdate':
  !list i fh x.
  i < LENGTH list /\
  DISJOINT (FDOM fh) (FDOM (fh_union (LUPDATE x i list))) ==>
  DISJOINT (FDOM fh) (FDOM (FST (EL i (LUPDATE x i list))))
Proof
  Induct >> rpt strip_tac >> fs[] >>
  Cases_on `h` >> fs[] >>
  Cases_on `i` >> fs[]
  >- (
    fs[LUPDATE_DEF] >>
    Cases_on `x` >>
    fs[fh_union_def] >>
    fs[DISJOINT_SYM]
    ) >>
  fs[EL_LUPDATE] >>
  pop_assum mp_tac >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[LUPDATE_APPEND] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[fh_union_append_thm] >>
  strip_tac >>
  metis_tac[DISJOINT_SYM]
QED



Theorem lemma_disjoint_lupdate'':
  !fh x list i.
  i < LENGTH list /\
  DISJOINT (FDOM fh) (FDOM (fh_union (LUPDATE x i list))) ==>
  (!n.
    n < LENGTH list /\
    n <> i ==>
    DISJOINT (FDOM fh) (FDOM (FST (EL n (LUPDATE x i list)))))
Proof
  gen_tac >> gen_tac >>
  Induct >> rpt strip_tac >> fs[] >>
  Cases_on `h` >> fs[] >>
  Cases_on `n` >> fs[]
  >- (
    fs[LUPDATE_DEF] >>
    fs[fh_union_def] >>
    fs[DISJOINT_SYM]
    ) >>
  fs[EL_LUPDATE] >>
  Cases_on `i` >> fs[LUPDATE_DEF]
  >- (
    Cases_on `x` >> fs[fh_union_def] >>
    first_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
    Cases_on `list` >> fs[] >>
    Cases_on `h` >>
    fs[LUPDATE_DEF,fh_union_def] >>
    gvs[] >>
    Cases_on `n' = 0` >> fs[DISJOINT_SYM]
    ) >>
  fs[PULL_FORALL] >>
  first_x_assum (qspecl_then [`n`,`n'`] assume_tac)>>
  gvs[fh_union_def,DISJOINT_SYM]
QED





Theorem lemma_all_disjoint_lupdate:
  i < LENGTH list /\
  all_disjoint list /\
  EL i list = (fh,(SOME (FibTree k v l))) ==>
  DISJOINT (FDOM fh) (FDOM (fh_union (LUPDATE (FEMPTY,NONE) i list)))
Proof
  strip_tac >> fs[] >>
  drule lemma_el_index_split >>
  strip_tac >>
  gvs[] >>
  simp[lupdate_append2] >>
  simp[fh_union_append_thm,fh_union_def] >>
  qpat_x_assum `all_disjoint (xs ++ [(fh,SOME (FibTree k v l))] ++ ys)` mp_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  once_rewrite_tac[GSYM lemma_cons_eq_append] >>
  strip_tac >>
  drule lemma_all_disjoint_split >>
  simp[fh_union_append_thm,DISJOINT_SYM]
QED




Theorem lemma_fib_heap_inv_union2_el:
  !l fh rl k v.
  LENGTH l < LENGTH rl /\
  fib_heap_inv_union2 fh rl /\
  (fhts_to_ts rl)❲LENGTH l❳ = SOME (FibTree k v l)
  ==>
  ?fh.
    fib_heap_inv fh [FibTree k v l] /\
    DISJOINT (FDOM fh) (FDOM (fh_union (LUPDATE (FEMPTY,NONE) (LENGTH l) rl))) /\
    fh SUBMAP (fh_union rl)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  pop_assum mp_tac >>
  rewrite_tac[fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  simp[EL_MAP] >> strip_tac >>
  fs[EVERY_EL] >>
  res_tac >>
  Cases_on `EL (LENGTH l) rl` >>
  gvs[] >>
  last_x_assum (qspec_then `LENGTH l` assume_tac) >>
  rfs[] >>
  drule_all lemma_all_disjoint_lupdate >> strip_tac >>
  imp_res_tac EL_MEM >> gvs[] >>
  drule fh_union_mem_submap_thm >> strip_tac >> rfs[] >>
  qexists `q` >> simp[]
QED

Theorem lemma_fhts_to_ts_el:
  i < LENGTH rl /\
  (EL i (fhts_to_ts rl)) = (SOME x)
  ==>
  ?m. (EL i rl) = (m,SOME x)
Proof
  strip_tac >>
  fs[fhts_to_ts_def] >>
  rfs[EL_GENLIST] >>
  Cases_on `EL i rl` >> gvs[]
QED


Theorem lemma_fh_union_lupdate_fempty_submap:
  x < LENGTH list /\
  all_disjoint list
  ==>
  fh_union (LUPDATE (FEMPTY,NONE) x list) SUBMAP fh_union list
Proof
  strip_tac >>
  drule lemma_el_index_split >> strip_tac >> gvs[] >>
  drule_all lemma_lupdate_intro >> strip_tac >>
  first_x_assum(qspec_then `(FEMPTY,NONE)` assume_tac) >>
  gvs[] >>
  simp[lupdate_append2] >>
  simp[fh_union_append_thm] >>
  simp[fh_union_def] >>
  Cases_on `EL (LENGTH xs) list` >> gvs[] >>
  qpat_x_assum `all_disjoint(xs ++ [(q,r)] ++ ys)` mp_tac >>
  simp[fh_union_append_thm] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  once_rewrite_tac[GSYM lemma_cons_eq_append] >>
  strip_tac >> drule lemma_all_disjoint_split >> strip_tac >>
  fs[fh_union_append_thm] >>
  simp[TO_FLOOKUP] >>
  rpt gen_tac >>
  fs[FLOOKUP_SIMP] >>
  Cases_on `FLOOKUP (fh_union xs) k` >> simp[] >>
  CASE_TAC >> strip_tac >>
  fs[fh_union_def] >>
  fs[FLOOKUP_DEF,DISJOINT_ALT] >>
  res_tac
QED



Theorem lemma_fh_union_disjoint_fempty_upd:
  !x fh rl.
  x < LENGTH rl /\
  all_disjoint rl /\
  DISJOINT (FDOM fh) (FDOM (fh_union rl)) ==>
  DISJOINT (FDOM fh) (FDOM (fh_union (LUPDATE (FEMPTY,NONE) x rl)))
Proof
  rpt strip_tac >>
  drule lemma_fh_union_lupdate_fempty_submap >>
  strip_tac >> rfs[] >>
  imp_res_tac SUBMAP_FDOM_SUBSET >>
  irule DISJOINT_SUBSET >>
  qexists `FDOM (fh_union rl)` >>
  simp[]
QED


Theorem lemma_all_disjoint_lupdate_fempty:
  x < LENGTH list /\
  all_disjoint list ==>
  all_disjoint (LUPDATE (FEMPTY,NONE) x list)
Proof
  strip_tac >>
  drule lemma_el_index_split >> strip_tac >> fs[] >>
  drule_all lemma_lupdate_intro >> strip_tac >>
  first_x_assum(qspec_then `(FEMPTY,NONE)` assume_tac) >>
  gvs[] >>
  pop_assum mp_tac >> rewrite_tac[GSYM APPEND_ASSOC] >>
  once_rewrite_tac[GSYM lemma_cons_eq_append] >>
  strip_tac >>
  Cases_on `EL (LENGTH xs) list` >>
  fs[lupdate_append2] >>
  fs[all_disjoint_append_thm,all_disjoint_def] >>
  simp[lemma_every_true] >>
  rpt strip_tac >> gvs[]
QED




Theorem lemma_fib_heap_inv_union2_imp_lupdate_fempty:
  x < LENGTH rl /\
  fib_heap_inv_union2 (fh_union rl) rl ==>
  fib_heap_inv_union2 (fh_union (LUPDATE (FEMPTY,NONE) x rl))
    (LUPDATE (FEMPTY,NONE) x rl)
Proof
  strip_tac >>
  gvs[] >>
  fs[fib_heap_inv_union2_def] >>
  simp[EL_LUPDATE] >>
  drule lemma_all_disjoint_lupdate_fempty >> strip_tac >> rfs[] >>
  rpt strip_tac
  >- (
    irule IMP_EVERY_LUPDATE >>
    simp[] >>
    simp[fib_heap_inv_empty_thm]
    ) >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs[]
QED



Theorem lemma_fhts_to_ts_empty_upd:
  x < LENGTH list ==>
  (LUPDATE (NONE) x (fhts_to_ts list)) = fhts_to_ts (LUPDATE (FEMPTY,NONE) x list)
Proof
  strip_tac >>
  simp[fhts_to_ts_def] >>
  rewrite_tac[LUPDATE_GENLIST] >>
  fs[GENLIST_FUN_EQ] >>
  rpt strip_tac >>
  simp[EL_LUPDATE] >>
  Cases_on `n = x` >> fs[] >>
  simp[APPLY_UPDATE_THM]
QED





Theorem fts_link_trees:
  !c rl fh1 fh2 k v l.
    fib_heap_inv_strong fh1 [FibTree k v l] /\
    fib_heap_inv_union2 fh2 rl /\
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    LENGTH rl = 196 /\
    fts_link_trees c (fhts_to_ts rl)
      (FibTree k v l) =
      (rl',T)
    ==>
    ?fh. fib_heap_inv_union2 fh (ts_to_fhts rl')
Proof
  Induct >> rpt strip_tac
  >- fs[Once fts_link_trees_def] >>
  pop_assum mp_tac >>
  simp[Once fts_link_trees_def] >>
  IF_CASES_TAC >> fs[] >>
  CASE_TAC
  >- (
    strip_tac >> gvs[]  >>
    qexists `FUNION fh1 fh2` >>
    irule lemma_fts_link_list_upd >> fs[]
    ) >>
  CASE_TAC >> strip_tac >>
  Cases_on `fts_merge_trees (FibTree k v l) (FibTree k' v' l')` >>
  gvs[] >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  `∀n map k3 v3 l3. n < 196 ∧ rl❲n❳ = (map,SOME (FibTree k3 v3 l3)) ⇒
    LENGTH l3 = n` by fs[fib_heap_inv_union2_def] >>
  drule_all lemma_fhts_to_ts_el >> strip_tac >>
  first_x_assum(qspecl_then [`LENGTH l`,`m`,`k'`,`v'`,`l'`] assume_tac) >>
  gvs[] >>
  `LENGTH l' < LENGTH rl` by gvs[] >>
  qspecl_then [`l'`,`fh2`,`rl`,`k'`,`v'`] assume_tac lemma_fib_heap_inv_union2_el >>
  gvs[] >>
  `fh2 = fh_union rl` by fs[fib_heap_inv_union2_def] >>
  gvs[] >>
  drule SUBMAP_FDOM_SUBSET >>
  strip_tac >>
  qspecl_then [`FDOM fh1`,`FDOM (fh_union rl)`,`FDOM fh`]
    assume_tac DISJOINT_SUBSET >> rfs[] >>
  drule lemma_inv_strong_imp_inv >> strip_tac >>
  qspecl_then [`fh1`,`fh`,`k`,`v`,`l`,`k'`,`v'`,`l'`] assume_tac fts_merge_trees >>
  rfs[] >>
  drule lemma_inv_imp_inv_strong >> strip_tac >>
  first_x_assum(qspecl_then [`LUPDATE (FEMPTY,NONE) (LENGTH l) rl`,`FUNION fh1 fh`,
    `fh_union (LUPDATE (FEMPTY,NONE) (LENGTH l) rl)`, `k''`,`v''`,`l''` ]
    assume_tac) >>
  gvs[] >>
  qpat_x_assum `fib_heap_inv_union2 (fh_union rl) rl` assume_tac >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  drule lemma_fib_heap_inv_union2_imp_lupdate_fempty >>
  strip_tac >> gvs[lemma_fhts_to_ts_empty_upd] >>
  first_x_assum irule >>
  irule lemma_fh_union_disjoint_fempty_upd >> simp[] >>
  fs[fib_heap_inv_union2_def]
QED




Definition fts_link_root_list_def:
  (fts_link_root_list rl [] = (rl,T)) /\
  (fts_link_root_list rl (FibTree k v l::fts) =
    let (n_rl,flag) = (fts_link_trees 196 rl (FibTree k v l)) in
      if flag = F then (n_rl,F) else
      fts_link_root_list rl fts)
End


(*TODO: ?fh should be FUNION fh1 fh2*)
Theorem fts_link_root_list:
  !rl' rl fts fh1 fh2.
  fib_heap_inv_strong fh1 fts /\
  fib_heap_inv_union2 fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  fts_link_root_list rl fts = (rl',T)
  ==>
  ?fh. fib_heap_inv_union2 fh (ts_to_fhts rl') /\ LENGTH rl = LENGTH rl'
Proof
  strip_tac >> ho_match_mp_tac fts_link_root_list_ind >>
  rpt strip_tac
  >- (
    fs[fts_link_root_list_def] >>
    qexists `fh2` >> gvs[]
    ) >>
  rename [`fib_heap_inv_strong fh1 (FibTree k arr l::fts)`] >>
  imp_res_tac lemma_fib_heap_inv_strong_split >> gvs[] >>
  qpat_x_assum `fts_link_root_list rl (FibTree k arr l::fts) = (rl',T)`
    mp_tac >>
  fs[fts_link_root_list_def] >>
  Cases_on `fts_link_trees 196 rl (FibTree k arr l)` >> simp[] >>
  IF_CASES_TAC >> gvs[] >>
  strip_tac >>
  first_x_assum(qspecl_then [`fh2'`,`fh2`] assume_tac) >>
  gvs[] >>
  qexists `fh` >> simp[]
QED




Definition fts_collect_array_def:
  fts_collect_array (r:num) rl acc =
    if r = 0 then
      case EL r rl of
       |SOME (FibTree k v l) => (fts_merge [FibTree k v l] acc,(LUPDATE NONE r rl))
       |NONE => (acc,rl)
    else
      case EL r rl of
       |SOME (FibTree k v l) =>
          fts_collect_array (r-1) (LUPDATE (NONE) r rl)
            (fts_merge [FibTree k v l] acc)
       |NONE => fts_collect_array (r-1) rl acc
End


Theorem lemma_hd_ts_to_fhts:
  LENGTH rl = 196 /\
  HD rl = SOME (FibTree k v l) /\
  fib_heap_inv_union2 fh1 (ts_to_fhts rl)
  ==>
  ?fh2. fib_heap_inv fh2 [FibTree k v l] /\ fh2 SUBMAP fh1
Proof
  strip_tac >>
  irule fib_heap_inv_union2_el_thm >>
  qexistsl [`0`,`(ts_to_fhts rl)`,`alist_to_fmap(flat_fts [FibTree k v l])`] >>
  simp[] >>
  `0 < LENGTH rl` by fs[] >>
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[LENGTH_GENLIST] >>
  dep_rewrite.DEP_REWRITE_TAC[HD_GENLIST_COR] >>
  simp[]
QED


Theorem lemma_suc_ts_to_fhts:
  LENGTH rl = 196 /\
  SUC r < LENGTH rl /\
  EL (SUC r) rl = SOME (FibTree k v l) /\
  fib_heap_inv_union2 fh1 (ts_to_fhts rl)
  ==>
  ?fh2. fib_heap_inv fh2 [FibTree k v l] /\ fh2 SUBMAP fh1
Proof
  strip_tac >>
  irule fib_heap_inv_union2_el_thm >>
  qexistsl [`SUC r`,`(ts_to_fhts rl)`,
    `alist_to_fmap(flat_fts [FibTree k v l])`] >>
  simp[] >>
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[LENGTH_GENLIST] >>
  dep_rewrite.DEP_REWRITE_TAC[EL_GENLIST] >>
  simp[]
QED


Theorem lemma_ts_to_fhts_lookup:
  x < LENGTH list /\
  EL x list = SOME t
  ==>
  ?m. EL x (ts_to_fhts list) = (m,SOME t)
Proof
  strip_tac >>
  rewrite_tac[ts_to_fhts_def] >>
  dep_rewrite.DEP_REWRITE_TAC[EL_GENLIST] >> simp[]
QED





Theorem lemma_ts_to_fhts_lupdate_none:
  !x rl.
  x < LENGTH rl
  ==>
  ts_to_fhts (LUPDATE NONE x rl) = (LUPDATE (FEMPTY,NONE) x (ts_to_fhts rl))
Proof
  strip_tac >>
  rewrite_tac[lemma_ts_to_fhts_to_map] >>
  simp[LUPDATE_MAP]
QED



Theorem lemma_inv_union_lupdate_none_submap:
  !x list fh1 fh2.
  x < LENGTH list /\
  fib_heap_inv_union2 fh1 list /\
  fib_heap_inv_union2 fh2 (LUPDATE (FEMPTY,NONE) x list)
  ==>
  fh2 SUBMAP fh1
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  irule lemma_fh_union_lupdate_fempty_submap >>
  simp[]
QED


Theorem lemma_rl_ind_lupdate_none:
  (!x. x < 196 /\ SUC r < x ==> EL x rl = NONE) /\
  EL (SUC r) rl = NONE
  ==>
  !x. x < 196 /\ r < x ==> EL x rl = NONE
Proof
  rpt strip_tac >>
  res_tac >>
  Cases_on `SUC r < x` >> fs[] >>
  `x = SUC r` by fs[] >>
  simp[]
QED


Theorem lemma_rl_ind_lupdate_some:
  LENGTH rl = 196 /\
  (!x. x < 196 /\ SUC r < x ==> EL x rl = NONE) /\
  EL (SUC r) rl = SOME t
  ==>
  !x. x < 196 /\ r < x ==> EL x (LUPDATE NONE (SUC r) rl) = NONE
Proof
  rpt strip_tac >>
  res_tac >>
  Cases_on `SUC r < x` >> fs[]
  >- simp[EL_LUPDATE] >>
  `x = SUC r` by fs[] >>
  simp[EL_LUPDATE]
QED





Theorem lemma_rl_all_none_0:
  LENGTH rl = 196 /\
  (!x. x < 196 /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = NONE
  ==>
  !x. x < LENGTH rl ==> EL x rl = NONE
Proof
  rpt strip_tac >> fs[] >>
  Cases_on `x` >> fs[]
QED



Theorem lemma_rl_all_none_lupdate_0:
  LENGTH rl = 196 /\
  (!x. x < 196 /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = SOME x
  ==>
  !x. x < LENGTH rl ==> EL x (LUPDATE NONE 0 rl) = NONE
Proof
  rpt strip_tac >>
  simp[EL_LUPDATE]
QED


Theorem lemma_rl_all_none_imp_ts_to_fhts_fempty:
  (!x. x < LENGTH rl ==> EL x rl = NONE)
  ==>
  !x. x < LENGTH (ts_to_fhts rl) ==> EL x (ts_to_fhts rl) = (FEMPTY,NONE)
Proof
  rpt strip_tac >>
  fs[lemma_ts_to_fhts_to_map] >>
  simp[EL_MAP]
QED



Theorem lemma_rl_ts_to_fhts_empty:
  (!x. x < LENGTH rl /\ r < x ==> EL x rl = NONE)
  ==>
  !x. x < LENGTH rl /\ r < x ==> EL x (ts_to_fhts rl) = (FEMPTY,NONE)
Proof
  rpt strip_tac >>
  fs[lemma_ts_to_fhts_to_map] >>
  simp[EL_MAP]
QED


Theorem lemma_ts_to_fhts_split_empty:
  (∀x. x < LENGTH (xs ++ [t] ++ ys) ∧ LENGTH xs < x ⇒
    (ts_to_fhts (xs ++ [t] ++ ys))❲x❳ = (FEMPTY,NONE))
  ==>
  !y. y < LENGTH (ts_to_fhts ys) ==>
    EL y (ts_to_fhts ys) = (FEMPTY,NONE)
Proof
  rpt strip_tac >>
  first_x_assum(qspec_then `y + LENGTH xs + 1` assume_tac) >> gvs[] >>
  Cases_on `ys`
  >- fs[ts_to_fhts_def] >>
  pop_assum mp_tac >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map] >>
  rewrite_tac[MAP_APPEND] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[EL_APPEND] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,LENGTH_MAP] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,LENGTH_MAP] >>
  simp[] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,LENGTH_MAP] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,LENGTH_MAP] >>
  simp[] >>
  pop_assum mp_tac >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,LENGTH_MAP] >>
  simp[]
QED



Theorem lemma_ts_to_fhts_tail_empty_imp_fh_union:
  !r rl xs t ys.
  rl = xs ++ [t] ++ ys /\
  LENGTH xs = r /\
  (!x. x < LENGTH rl /\ r < x ==> EL x rl = NONE)
  ==>
  fh_union (ts_to_fhts rl) =
  FUNION (fh_union (ts_to_fhts xs)) (fh_union (ts_to_fhts [t]))
Proof
  rpt strip_tac >>
  drule lemma_rl_ts_to_fhts_empty >> strip_tac >> simp[] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map] >>
  rewrite_tac[MAP_APPEND] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[fh_union_append_thm] >>
  gvs[Excl "LENGTH", Excl "LENGTH_APPEND"] >>
  drule lemma_ts_to_fhts_split_empty >> strip_tac >>
  drule fh_union_empty_thm >> simp[]
QED



Theorem lemma_rl_none_except_hd_eq_fh:
  LENGTH rl = 196 /\
  (!x. x < LENGTH rl /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = SOME t /\
  fib_heap_inv_union2 fh1 (ts_to_fhts rl)
  ==>
  ?fh2. HD (ts_to_fhts rl) = (fh2,SOME t) /\ fh1 = fh2
Proof
  rpt strip_tac >>
  `0 < LENGTH rl` by fs[] >>
  imp_res_tac lemma_el_index_split >>
  qpat_x_assum `rl = xs ++ ((EL 0 rl)::ys)` mp_tac >>
  simp[Once lemma_cons_eq_append] >> strip_tac >>
  drule_all lemma_ts_to_fhts_tail_empty_imp_fh_union >> strip_tac >>
  gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[lemma_ts_to_fhts_to_map] >> simp[fh_union_def] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map]  >>
  strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  gvs[] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,MAP_APPEND] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[fh_union_append_thm] >>
  simp[Once ts_to_fhts_def,fh_union_def]
QED


Theorem lemma_fib_heap_inv_union2_fmap_split:
  (!x. x < LENGTH (xs ++ [SOME t] ++ ys) /\
     r < x ==> EL x (xs ++ [SOME t] ++ ys) = NONE) /\
  fib_heap_inv_union2 fh (ts_to_fhts (xs ++ [SOME t] ++ ys)) /\
  LENGTH xs = r
  ==>
  fh = FUNION (fh_union (ts_to_fhts (xs))) (alist_to_fmap (flat_fts [t]))
Proof
  strip_tac >>
  drule lemma_rl_ts_to_fhts_empty >> strip_tac >>
  gvs[Excl "LENGTH", Excl "LENGTH_APPEND"] >>
  drule lemma_ts_to_fhts_split_empty >> strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map] >>
  rewrite_tac[MAP_APPEND] >>
  simp[] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[fh_union_append_thm,fh_union_def] >>
  drule fh_union_empty_thm >>
  simp[]
QED



Theorem lemma_fib_heap_inv_union2_split_empty:
  (!x. x < LENGTH (xs ++ [y] ++ ys) /\
    LENGTH xs < x ==> EL x (xs ++ [y] ++ ys) = NONE) /\
  fib_heap_inv_union2 fh (ts_to_fhts xs ++ ((FEMPTY,NONE)::(ts_to_fhts ys)))
  ==>
  fh = fh_union (ts_to_fhts xs)
Proof
  strip_tac >>
  drule lemma_rl_ts_to_fhts_empty >> strip_tac >>
  drule lemma_ts_to_fhts_split_empty >> strip_tac >>
  drule fh_union_empty_thm >> strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  simp[fh_union_append_thm, fh_union_def]
QED






Theorem lemma_ts_to_fhts_rm:
  LENGTH rl = 196 /\
  (!x. x < LENGTH rl /\ r < x ==> EL x rl = NONE) /\
  r < LENGTH rl /\
  EL r rl = SOME (FibTree k v l) /\
  fib_heap_inv_union2 fh (ts_to_fhts rl)
  ==>
  ?fh1 fh2.
    fib_heap_inv fh1 [FibTree k v l] /\
    fib_heap_inv_union2 fh2 (ts_to_fhts (LUPDATE NONE r rl)) /\
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    fh = FUNION fh1 fh2
Proof
  strip_tac >>
  qspecl_then [`ts_to_fhts rl`,`r`] assume_tac lemma_el_index_split >>
  Cases_on `LENGTH rl <> LENGTH (ts_to_fhts rl)`
  >- (
    pop_assum mp_tac >>
    rewrite_tac[Once ts_to_fhts_def,LENGTH_GENLIST]
    ) >>
  drule lemma_el_index_split >> strip_tac >>
  `rl =  xs ++ [SOME (FibTree k v l)] ++ ys` by gvs[] >>
  gvs[Excl "LENGTH", Excl "LENGTH_APPEND"] >>
  `∀x. x < LENGTH (xs ++ [SOME (FibTree k v l)] ++ ys) ∧ LENGTH xs < x ⇒
            (xs ++ [SOME (FibTree k v l)] ++ ys)❲x❳ = NONE` by fs[] >>
  drule lemma_fib_heap_inv_union2_fmap_split >> strip_tac >>
  first_x_assum(qspec_then `fh` assume_tac) >> gvs[] >>
  qabbrev_tac `fh = FUNION (fh_union (ts_to_fhts xs))
    (alist_to_fmap (flat_fts [FibTree k v l]))` >>
  qpat_x_assum `fib_heap_inv_union2 fh
    (ts_to_fhts (xs ++ [SOME (FibTree k v l)] ++ ys))` mp_tac >>
  simp[Once lemma_ts_to_fhts_to_map] >>
  simp[GSYM lemma_ts_to_fhts_to_map] >>
  rewrite_tac[GSYM APPEND_ASSOC,Once (GSYM lemma_cons_eq_append)] >>
  strip_tac >>
  drule_all fib_heap_inv_union2_rm_thm >> strip_tac >>
  qabbrev_tac `fh1 = (alist_to_fmap (flat_fts [FibTree k v l]))` >>
  qexistsl [`fh1`,`fh2`] >> simp[] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map] >>
  rewrite_tac[LUPDATE_MAP,MAP_APPEND] >>
  simp[LUPDATE_APPEND] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[LUPDATE_DEF] >>
  rewrite_tac[GSYM APPEND_ASSOC,Once (GSYM lemma_cons_eq_append)] >> simp[] >>
  unabbrev_all_tac >>
  `∀x. x < LENGTH (xs ++ [SOME (FibTree k v l)] ++ ys) ∧ LENGTH xs < x ⇒
            (xs ++ [SOME (FibTree k v l)] ++ ys)❲x❳ = NONE` by fs[] >>
  drule_all lemma_fib_heap_inv_union2_split_empty >> strip_tac >>
  simp[FUNION_COMM]
QED







Theorem lemma_fib_heap_inv_union2_imp_hd_fib_heap_inv:
  LENGTH rl = 196 /\
  HD (ts_to_fhts rl) = (fh1, SOME (FibTree k v l)) /\
  fib_heap_inv_union2 fh2 (ts_to_fhts rl)
  ==>
  fib_heap_inv fh1 [FibTree k v l]
Proof
  strip_tac >>
  pop_assum mp_tac >>
  simp[fib_heap_inv_union2_def] >>
  simp[Once lemma_ts_to_fhts_to_map] >>
  simp[EVERY_MAP] >>
  Cases_on `rl` >> fs[] >>
  pop_assum mp_tac >>
  simp[Once lemma_ts_to_fhts_to_map]
QED



Theorem fts_collect_array:
  !fts rl' r rl fh2 fh1 acc.
    fib_heap_inv fh1 acc /\
    fib_heap_inv_union2 fh2 (ts_to_fhts rl) /\
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    LENGTH rl = 196 /\
    r < LENGTH rl /\
    (!x. x < LENGTH rl /\ r < x ==> EL x rl = NONE) /\
    fts_collect_array r rl acc = (fts,rl')
    ==>
    fib_heap_inv (FUNION fh1 fh2) fts /\
    (!x. x < LENGTH rl' ==> EL x rl' = NONE) /\
    LENGTH rl = LENGTH rl'
Proof
  strip_tac >> strip_tac >>
  Induct >> rpt gen_tac >> disch_tac >> fs[]
  >- (
    pop_assum mp_tac >>
    simp[Once fts_collect_array_def] >>
    CASE_TAC
    >- (
      strip_tac >> gvs[] >>
      imp_res_tac lemma_rl_all_none_0 >>
      imp_res_tac lemma_rl_all_none_imp_ts_to_fhts_fempty >>
      drule_all fh_union_empty_thm >> strip_tac >>
      fs[fib_heap_inv_union2_def]
      ) >>
    CASE_TAC >> strip_tac >>
    drule_all lemma_rl_none_except_hd_eq_fh >> strip_tac >>
    qspecl_then [`fh2`,`[FibTree k v l]`,`fh1`,`acc`,`fts`]
      assume_tac fts_merge >> gvs[] >>
    rfs[DISJOINT_SYM] >>
    drule_all lemma_fib_heap_inv_union2_imp_hd_fib_heap_inv >> strip_tac >>
    fs[] >>
    qspecl_then [`fh2`,`fh1`,`(fts_merge [FibTree k v l] acc)`]
      assume_tac fib_heap_inv_comm_thm >> rfs[DISJOINT_SYM] >>
    rpt strip_tac >>
    res_tac >>
    Cases_on `x` >> fs[]
    >- (Cases_on `rl` >> fs[LUPDATE_DEF]) >>
    simp[EL_LUPDATE]
    ) >>
  pop_assum mp_tac >>
  simp[Once fts_collect_array_def] >>
  CASE_TAC
  >- (
    strip_tac >>
    `r < LENGTH rl` by fs[] >>
    first_x_assum(qspecl_then [`rl`,`fh2`,`fh1`,`acc`] assume_tac) >> rfs[] >>
    first_x_assum irule >>
    drule lemma_rl_ind_lupdate_none >> strip_tac >> fs[]
    ) >>
  CASE_TAC >> strip_tac >>
  drule_all lemma_ts_to_fhts_rm >> strip_tac >>
  qspecl_then [`fh1'`,`[FibTree k v l]`,`fh1`,`acc`,
    `fts_merge [FibTree k v l] acc`] assume_tac fts_merge >>
  gvs[] >>
  first_x_assum(qspecl_then [`LUPDATE NONE (SUC r) rl`,`fh2'`,
    `FUNION fh1 fh1'`,`fts_merge [FibTree k v l] acc`] assume_tac) >>
  rfs[DISJOINT_SYM,fib_heap_inv_comm_thm] >>
  simp[FUNION_ASSOC] >>
  first_x_assum irule >>
  simp[lemma_rl_ind_lupdate_some]
QED


Definition alg_rl_def:
  alg_rl = REPLICATE 196 NONE
End


Definition fts_reb_def:
  fts_reb rl fts =
    let (l_rl,flag) = fts_link_root_list rl fts in
    let (fts',e_rl) = fts_collect_array (LENGTH l_rl - 1) l_rl [] in
      (fts',e_rl,flag)
End





Theorem lemma_fib_heap_inv_union2_replicate_imp_fempty:
  fib_heap_inv_union2 fh2 (ts_to_fhts alg_rl)
  ==>
  fh2 = FEMPTY
Proof
  simp[alg_rl_def,lemma_ts_to_fhts_to_map] >>
  strip_tac >>
  fs[fib_heap_inv_union2_def] >>
  simp[fh_union_replicate_empty_thm]
QED


Theorem lemma_list_ind_suc_imp_no_suc:
  (!x. x < SUC (LENGTH list) ==> EL x (h::list) = NONE)
  ==>
  (!x. x < LENGTH list ==> EL x list = NONE)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC x` assume_tac) >>
  Cases_on `x` >> fs[]
QED


Theorem lemma_e_rl_eq_replicate:
  !list.
    (!x. x < LENGTH list ==> EL x list = NONE)
    ==>
    list = REPLICATE (LENGTH list) NONE
Proof
  Induct >> fs[] >>
  rpt strip_tac
  >- (first_x_assum (qspec_then `0` assume_tac) >> fs[]) >>
  imp_res_tac lemma_list_ind_suc_imp_no_suc >>
  res_tac
QED


Theorem fts_reb:
  !fh1 fts fh2.
    fib_heap_inv_strong fh1 fts /\
    fib_heap_inv_union2 fh2 (ts_to_fhts alg_rl) /\
    fts_reb alg_rl fts = (fts',e_rl,T)
    ==>
    fib_heap_inv fh1 fts' /\ e_rl = alg_rl
Proof
  rpt gen_tac >> disch_tac >>
  pop_assum mp_tac >>
  simp[fts_reb_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule lemma_fib_heap_inv_union2_replicate_imp_fempty >> strip_tac >>
  drule fts_link_root_list >> strip_tac >>
  first_x_assum(qspecl_then [`l_rl`,`alg_rl`,`FEMPTY`] assume_tac) >>
  gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,alg_rl_def] >>
  rewrite_tac[rich_listTheory.map_replicate] >>
  simp[fib_heap_inv_union2_empty_thm] >>
  strip_tac >> fs[] >>
  qspecl_then [`fts'`,`e_rl`,`195`,`l_rl`,`fh`,`FEMPTY`,`[]`]
    assume_tac fts_collect_array >> rfs[fib_heap_inv_empty_thm] >>
  imp_res_tac lemma_e_rl_eq_replicate >> gvs[] >>

  cheat

(*TODO: keep union of fh until this point to prove that all
  elements are still there*)

(*
  fts_link_root_list
  fts_collect_array
*)
QED


(*

Currently, not used!

Theorem lemma_map_update_not_null:
  !fts fh.
    list_keys_not_null fts /\ (FLOOKUP fh 0w = NONE) ==>
    FLOOKUP (fh |++ flat_fts fts) 0w = NONE
Proof
  ho_match_mp_tac flat_fts_ind >>
  simp[Once list_keys_not_null_def] >>
  simp[Once flat_fts_def] >>
  rpt strip_tac
  >- simp[FUPDATE_LIST] >>
  fs[list_keys_not_null_def] >>
  pure_rewrite_tac[flat_fts_def] >>
  simp[FUPDATE_LIST_APPEND] >>
  simp[GSYM FUPDATE_EQ_FUPDATE_LIST] >>
  rename [`(k,v,e)`] >>
  Cases_on `FLOOKUP (fh |+ (k,v,e)) 0w = NONE`
  >- (
    first_x_assum(qspec_then `(fh |+ (k,v,e))` assume_tac) >>
    rfs[]
    ) >>
  fs[FLOOKUP_SIMP]
QED

*)





Theorem lemma_mem_flat_fts_eq_flookup:
  !fts k v e.
  fts_all_dist fts ==>
  (MEM (k,v,e) (flat_fts fts) <=>
  FLOOKUP (FEMPTY |++ flat_fts fts) k = SOME (v,e))
Proof
  cheat
QED



Theorem lemma_flat_fts_eq_fts_has:
  !fts k v e.
    fts_all_dist fts ==>
    (FLOOKUP (FEMPTY |++ (flat_fts fts)) k = SOME (v,e)  <=>
    ?m. fts_has k (fill_dnode v e m) fts)
Proof
  rpt strip_tac >>
  iff_tac >>
  rpt strip_tac
  >- (
  gvs[miscTheory.flookup_update_list_some] >>
  imp_res_tac ALOOKUP_MEM >> fs[] >>
  assume_tac lemma_mem_eq_fts_has >>
  res_tac >>
  pop_assum $ irule_at Any
   ) >>
  cheat
QED

(*
Theorem lemma_flookup_list_append_update:
  !x xs ys fh.
    FLOOKUP (fh |++ (x::(xs ++ ys))) = FLOOKUP (fh |+ x |++ xs |++ ys)
Proof
  pure_rewrite_tac[Once (GSYM APPEND)] >>
  simp[FUPDATE_LIST_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_EQ_CONS] >>
  simp[FUPDATE_LIST_THM]
QED



Theorem lemma_flookup_fts_is_none:
  !fts fh k.
    (FLOOKUP fh k = NONE /\ !n. ~fts_has k n fts)  ==>
    FLOOKUP (fh |++ flat_fts fts) k = NONE
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- simp[flat_fts_def,FUPDATE_LIST] >>
  simp[flat_fts_def] >>
  simp[lemma_flookup_list_append_update] >>
  rename [`!n. ~fts_has k n (FibTree k' n' fts'::fts'')`] >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  rpt strip_tac >>
  fs[FORALL_AND_THM] >>
  last_assum (qspecl_then [`(fh |+ (k',n'.value,n'.edges))`, `k`]
    assume_tac) >>
  Cases_on `FLOOKUP (fh |+ (k',n'.value,n'.edges)) k = NONE` >> fs[] >>
  fs[FLOOKUP_SIMP]
QED




Theorem lemma_apply_list_upd:
  !xs fh x v e.
    fts_all_dist xs /\ FLOOKUP (fh |++ flat_fts xs) x = SOME (v,e) /\
    FLOOKUP fh x = NONE ==>
    FLOOKUP (fh |+ (x,v,e)) x = SOME(v,e)
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- (
    fs[flat_fts_def,FUPDATE_LIST]
    ) >>
  rename [`(FibTree k n xs'::xs'')`] >>
  qpat_x_assum `FLOOKUP (fh |++ flat_fts (FibTree k n xs'::xs'')) x =
    SOME (v,e)` mp_tac >>
  fs[fts_all_dist_def] >>
  simp[flat_fts_def] >>
  simp[lemma_flookup_list_append_update] >>
  fs[FORALL_AND_THM] >>
  simp[FLOOKUP_SIMP]
QED
*)

(*
Theorem lemma_map_extract_head:
  !fts fh k n l v e.
    fts_all_dist (FibTree k n l::fts) /\ FLOOKUP fh k = NONE /\
    FLOOKUP (fh |++ flat_fts (FibTree k n l::fts)) k = SOME(v,e) ==>
    n.value = v /\ n.edges = e
Proof
  rpt strip_tac >>
  drule_all lemma_flat_fts_eq_fts_has >>
  strip_tac >> fs[] >>
  fs[fts_all_dist_def] >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  strip_tac >>
  fs[fill_dnode_def,data_node_component_equality]
QED
*)


(*

Currently, not used!

Theorem lemma_list_upd_not_null:
  !fts fh.
    list_keys_not_null fts /\ FLOOKUP fh 0w = NONE ==>
    FLOOKUP (fh |++ flat_fts fts) 0w = NONE
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- (fs[flat_fts_def,FUPDATE_LIST]) >>
  rename [`list_keys_not_null (FibTree k n l::fts)`] >>
  simp[flat_fts_def,lemma_flookup_list_append_update] >>
  fs[list_keys_not_null_def] >>
  Cases_on `FLOOKUP (fh |+ (k,n.value,n.edges)) 0w = NONE`
  >- (first_x_assum(qspec_then `(fh |+ (k,n.value,n.edges))` assume_tac) >> rfs[]) >>
  fs[FLOOKUP_SIMP]
QED


*)
(*
Theorem lemma_flookup_in_map_or_upd:
  !fts fh k v e.
    FLOOKUP(fh |++ flat_fts fts) k = SOME (v,e) ==>
      FLOOKUP fh k = SOME (v,e) \/ MEM (k,v,e) (flat_fts fts)
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac
  >- fs[flat_fts_def,FUPDATE_LIST] >>
  simp[flat_fts_def] >>
  pop_assum mp_tac >>
  simp[Once flat_fts_def] >>
  pure_rewrite_tac[lemma_flookup_list_append_update] >>
  strip_tac >>
  rename[`fh |+ (k,n.value,n.edges)`] >>
  last_x_assum(qspecl_then [`(fh |+ (k,n.value,n.edges) |++ flat_fts fts')`,
    `k'`,`v`,`e`] assume_tac) >>
  rfs[] >>
  first_x_assum(qspecl_then[`(fh |+ (k,n.value,n.edges))`,`k'`,`v`,`e`] assume_tac) >>
  rfs[] >>
  Cases_on `k = k'` >> fs[FLOOKUP_SIMP]
QED
*)
(*
Theorem lemma_insert_list_new_min_inv:
  !fts fh fh2 xs.
    (fib_heap_inv( fh fts) /\
    (fib_heap_inv fh2 xs) /\
    (fts_all_dist (fts ++ xs)) /\
    (list_keys_not_null xs) /\
    (fts_hd_value xs <=+ fts_hd_value fts) ==>
    (fib_heap_inv (fh |++ flat_fts xs) (xs ++ fts))
Proof
  rpt strip_tac >>
  Cases_on `fts`
  >- (
    fs[fib_heap_inv_def] >>
    qpat_x_assum `∀k v e.FLOOKUP fh k = SOME (v,e) ==>
                  ∃m. fts_has k (fill_dnode v e m) []` mp_tac >>
    simp[Once fts_has_cases] >>
    strip_tac >>
    fs[lemma_empty_map] >>
    Cases_on `xs`
    >- fs[flat_fts_def,FUPDATE_LIST] >>
    Cases_on `h` >>
    gvs[fts_is_min_def,fts_hd_value_def,head_key_def] >>
    rpt strip_tac
    >- (dxrule lemma_map_update_not_null >> strip_tac >>fs[])
    >- (
      qspecl_then [`(FibTree k v l::t)`,`FEMPTY`,`k'`, `v'`, `e`]
        assume_tac lemma_flat_fts_eq_fts_has >> fs[]
      )
   ) >>
  Cases_on `h` >>
  fs[fib_heap_inv_def] >>
  Cases_on `xs`
  >- (rpt strip_tac >> fs[] >> fs[flat_fts_def,FUPDATE_LIST]) >>
  Cases_on `h` >>
  rpt strip_tac
  >- (
    qspecl_then [`(FibTree k' v' l'::t')`, `fh`] assume_tac lemma_list_upd_not_null >>
    rfs[] >>
    pop_assum mp_tac >>
    Cases_on `FLOOKUP fh 0w` >> fs[]
    )
  >- (
    simp[fts_has_append_thm] >>
    qspecl_then [`(FibTree k' v' l'::t')`,`fh`,`k''`,`v''`,`e`]
      assume_tac lemma_flookup_in_map_or_upd >> rfs[]
    >- (res_tac >> qexists `m` >> simp[]) >>
    fs[lemma_mem_eq_fts_has] >>
    qexists `m` >> simp[]
    )
  >- (
    qpat_x_assum `fts_all_dist (FibTree k v l::(t ++ FibTree k' v' l'::t'))` mp_tac >>
    simp[fts_all_dist_append_thm] >>
    simp[fts_all_dist_def] >>
    cheat
    ) >>
    cheat
QED
*)






(*---------------------------------------------------------*

  Definition of 'Remove Element' from a fib heap list!

*----------------------------------------------------------*)

(* Weakend invariant? *)
(*
Definition fib_heap_inv_def:
  fib_heap_inv fh (fts: ('a word, 'a data_node) fts) ⇔
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
*)


Definition fts_remove_def:
  (fts_remove x acc [] = acc) /\
  (fts_remove x acc (FibTree k v l::rest) =
    if x = k then
      acc ++ rest
    else
      acc ++ [FibTree k v (fts_remove x [] l)] ++ rest)
End

Theorem fts_remove:
  !x fts fh.
    fib_heap_inv_weak (fh,fts) /\ (?n. fts_has x n fts) /\
    fts_remove x [] fts = fts' ==>
    ?fh1 fh2.
    (!k v l. MEM (FibTree k v l) fts' ==>
             fib_heap_inv_strong fh1 [FibTree k v l]) /\
    (!v l. fib_heap_inv_strong fh2 [FibTree x v l])
Proof
  cheat
QED


(*
Requires that x is in the list!

Definition fib_heap_remove_def:
  fib_heap_remove (i:num)
  (a:'a word, x:'a word, min:'a word)
  (m: 'a word -> 'a word, dm: 'a word set,b: bool) =
    if i = 0 then (x,min,m,F) else
    let c = (a IN dm) in
    let c = (x IN dm /\ c) in
    if a = x then
      let c = (x + next_off IN dm /\ c) in
      let x_n = m (x + next_off) in
      let c = (x + before_off IN dm /\ c) in
      let x_b = m (x + before_off) in
      let c = (x_b + next_off IN dm /\ c) in
      let m = ((x_b + next_off) =+ x_n) m in
      let c = (x_n + before_off IN dm /\ c) in
      let m = ((x_n + before_off) =+ x_b) m in
      let m = ((x + next_off) =+ x) m in
      let m = ((x + before_off) =+ x) m in
        (x,min,m,c)
    else
      let c = (a + next_off IN dm /\ c) in
      let a_n = m (a + next_off) in
      let c = (min IN dm /\ c) in
      if m a <=+ m min then
        fib_heap_remove (i-1) (a_n,x,  a) (m,dm,c)
      else
        fib_heap_remove (i-1) (a_n,x,min) (m,dm,c)
End



(*
    if x = 0w then (0w,0w,m,T) else

    let c = (x IN dm) in
    let c = ((x + next_off) IN dm /\ c) in
    let x_n = m (x + next_off) in
    let c = ((x + before_off) IN dm /\ c) in
    let x_b = m (x + before_off) in

    let c = ((x_b + next_off) IN dm /\ c) in
    let m = ((x_b + next_off) =+ x_n) m in

    let c = ((x_n + before_off) IN dm /\ c) in
    let m = ((x_n + before_off) =+ x_b) m in

    let m = ((x + next_off) =+ x) m in
    let m = ((x + before_off) =+ x) m in

    let c = ((x + parent_off) IN dm /\ c) in
    let x_p = m (x + parent_off) in

    (*maybe set new child for parent*)
    if x_p = 0w then
      (*TODO: find new min if x_n <> x*)
      if x_n = x then (x,0w,m,c) else (x,x_n,m,c)
    else

    let c = ((x_p + child_off) IN dm /\ c) in
    let p_c = m (x_p + child_off) in
    if p_c = x then
      if x = x_n then
        let m = (p_c =+ 0w) m in
          (x,0w,m,c)
      else
        (*TODO: need to find new minimum! *)
        let m = (p_c =+ x_n) m in
          (x,x_n,m,c)
    else
      (x,x_n,m,c)   *)



Theorem fib_heap_remove:
  !frame fh fts p x n l e.
    (fts_mem(ann_fts p fts) * frame)
      (fun2set(m,dm)) /\
    fib_heap_inv_weak fh fts /\
    MEM (FibTree x n l) fts /\
    LENGTH fts < i /\
    fib_heap_remove i (x,m,dm) = (x,a',m',b) ==>
    ?fts.
    (fts_mem(ann_fts p fts) * full_node x (v,e) * frame)
    (fun2set (m',dm)) /\ b /\
    fib_heap_inv_weak fh fts /\
    a' = head_key fts /\
    !m l. ~fts_has x (fill_dnode v e m) l
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  fs[full_node_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  Cases_on `x = 0w`
  >- fs[fib_heap_inv_weak_def,FLOOKUP_SIMP] >>
  simp[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  simp[PULL_EXISTS] >>
  Cases_on `fts`
  >- (
    fs[fib_heap_inv_weak_def] >>
    first_x_assum(qspecl_then [`x`,`v`,`e`] assume_tac) >>
    fs[Once fts_has_cases, FLOOKUP_SIMP]
    ) >>
  Cases_on `h` >>
  cheat
QED
*)



(*---------------------------------------------------------*

  Definition of 'Extract Minimum' from fib heap list!

*----------------------------------------------------------*)


Definition fts_find_min_def:
  (fts_find_min min [] = min) /\
  (fts_find_min (FibTree k v l) (FibTree k' v' l'::fts) =
    if v.value <=+ v'.value then
      fts_find_min (FibTree k v l) fts
    else
      fts_find_min (FibTree k' v' l') fts )
End



Definition fts_set_min_hd_def:
  (fts_set_min_hd min rest [] = []) /\ (* This case should be impossible *)
  (fts_set_min_hd (FibTree mk mv ml) rest (FibTree k v l::fts) =
    if mk = k then
      (FibTree k v l::fts) ++ rest
    else
      fts_set_min_hd (FibTree mk mv ml) (rest ++ [FibTree k v l]) fts)
End




Definition fts_ext_min_def:
  (fts_ext_min [] = []) /\
  (fts_ext_min (FibTree k v l::rest) =
    fts_set_min_hd (fts_find_min (HD rest) rest) [] rest)
End



Definition fib_heap_parent_to_null_def:
  fib_heap_parent_to_null (n:num)
    (a:'a word, l:'a word) (m:'a word -> 'a word, dm:'a word set, c: bool)
  =
    if n = 0 then (m,F) else
    let c = (a IN dm /\ c) in
    let c = (a + parent_off IN dm /\ c) in
    let m = ((a + parent_off) =+ 0w) m in
    let c = (a + next_off IN dm /\ c) in
    let a_n = m (a + next_off) in
    if a = l then
      (m,c)
    else
      fib_heap_parent_to_null (n-1) (a_n,l) (m,dm,c)
End

Definition fib_heap_find_min_def:
  fib_heap_find_min (i:num)
    (min_n:'a word, l:'a word, t:'a word)
    (m:'a word -> 'a word, dm: 'a word set, c: bool)
  =
    if i = 0 then (min_n,m,F) else
    if l = t then
      let c = ((l IN dm) /\ c) in
      if m min_n <=+ m l then
        (min_n,m,c)
      else
        (l,m,c)
    else
      let c = (min_n IN dm /\ c) in
      let v = m min_n in
      let c = (t + next_off IN dm /\ c) in
      let v_t = m t in
      let t_n = m (t + next_off) in
      if v_t <=+ v then
        fib_heap_find_min (i-1) (t,l,t_n) (m,dm,c)
      else
        fib_heap_find_min (i-1) (min_n,l,t_n) (m,dm,c)
End


Theorem fib_heap_find_min:
  !i frame fts p x n l.
    (fts_mem (ann_fts p fts) * frame) (fun2set(m,dm)) /\
    LENGTH fts < i /\
    MEM (FibTree x n l) fts /\
    list_keys_not_null fts /\
    fib_heap_find_min i (x, last_key_t (head_key fts) fts, head_key fts)
      (m,dm,T) = (a',m,b) ==>
    ?fts'.
    (fts_mem (ann_fts p fts') * frame) (fun2set(m,dm)) /\ b /\
    head_key fts' = a' /\ fts_head_is_min fts' /\
    !k n. fts_has k n fts ==> fts_has k n fts'
Proof
  Induct
  >- (Cases_on `fts` >> fs[]) >>
  rpt gen_tac >>
  Cases_on `fts`
  >- simp[] >>
  Cases_on `h` >>
  Cases_on `t` using SNOC_CASES
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, last_key_t_def,ones_def, STAR_ASSOC] >>
    rpt strip_tac >> gvs[] >>
    pop_assum mp_tac >>
    simp[Once fib_heap_find_min_def] >>
    SEP_R_TAC >>
    rpt strip_tac >> gvs[] >>
    qexists `[FibTree a' n l]` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
         fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    simp[fts_head_is_min_def]
    ) >>
  Cases_on `x'` >> simp[SNOC_APPEND] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[Once fib_heap_find_min_def] >>
  rpt strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  cheat
QED





Definition fib_heap_extract_min_def:
  fib_heap_extract_min (n: num)
    (a:'a word, m:'a word -> 'a word, dm :'a word set)
  =
    let c = (a IN dm) in
    let c = (a + child_off IN dm /\ c) in
    let a_child = m (a + child_off) in
    let c = (a_child + before_off IN dm /\ c) in
    let b_child = m (a_child + before_off) in
    let (m,c) = (fib_heap_parent_to_null n (a_child,b_child) (m,dm,c)) in
    let (min,m,c) = (fib_heap_find_min n (a_child,b_child,a_child) (m,dm,c)) in
    let c = (a + next_off IN dm /\ c) in
    let sec = m (a + next_off) in
    if a = sec then
      let (a',m,c') = fib_heap_merge(0w,min,m,dm) in
        (a,a',m,c' /\ c)
    else
      let c = (a + before_off IN dm /\ c) in
      let a_b = m (a + before_off) in
      let (min2,m,c) = (fib_heap_find_min n (a,a_b,a) (m,dm,c)) in
      let (a',m,c') = fib_heap_merge(min2,min,m,dm) in
        (a,a',m, c' /\ c)
End


(*TODO: finish proof. Ask about n?*)
Theorem fib_heap_extract_min:
  !frame fh.
  (fib_heap a fh * frame * cond(n = w2n (-1w)))
    (fun2set (m,dm)) /\
  fib_heap_extract_min n (a,m,dm) = (a,a',m',b) ==>
  ?fts. ((fts_mem (ann_fts 0w (fts_ext_min fts))) * frame *
    cond(a' = head_key fts /\ fib_heap_inv fh fts))
    (fun2set (m,dm)) /\ b
Proof
cheat
QED


(*--------------------------------------------------------*

Definition of 'Rebalancing' (separated from extract minimum

*---------------------------------------------------------*)



Definition map_mem_empty_def:
  map_mem_empty (a:'a word) (n:num) =
    ones a (REPLICATE (n+1) 0w)
End

(* TODO: Maybe good start with supervior!*)
Theorem lemma_map_mem_expand_thm:
  !i n a. (0 < i /\ i < n) ==>
    ones a (REPLICATE (n + 1) 0w) =
    ones a (REPLICATE (i - 1) 0w) *
    ones (a + bytes_in_word * n2w i) (REPLICATE (n + 1) 0w)
Proof
  cheat
QED

Definition map_mem_empty_v_def:
  map_mem_empty (a:'a word) (n:num) =
    SEP_EXISTS x.
    if n = 0 then
      one(a, x)
    else
      one(a + bytes_in_word * n2w n, x) * map_mem_empty a (n-1)
End

Definition map_lookup_def:
  map_lookup mp n =
    case FLOOKUP mp n of
    | SOME(k,_,_) => k
    | NONE        => 0w
End

(*Array when filled up with a map 'mp'  *)
Definition map_mem_def:
  map_mem a (n:num) mp =
    ones a (GENLIST (map_lookup mp) (n+1))
End






Definition merge_trees_def:
  merge_trees (n:num)
    (a:'a word, k: 'a word, m: 'a word -> 'a word, dm: 'a word set, c: bool)
  =
    if n = 0 then (m,F) else
    let c = (k + rank_off IN dm /\ c) in
    let k_r = m (k + rank_off) in

    let off = a + bytes_in_word * k_r in
    let c = (off IN dm /\ c) in
    let t = m off in

    if t = 0w then
    (* no entry -> just insert new element *)
      let m = (off =+ k) m in
        (m,c)
    else
    (* compare both entries -> insert entry with smaller value *)
      let c = (k IN dm /\ c) in
      let k_v = m k in
      let c = (t IN dm /\ c) in
      let t_v = m t in
      if k_v <=+ t_v then
        let c = (k + child_off IN dm /\ c) in
        let k_c = m (k + child_off) in
        let (_,m,c') = fib_heap_merge(k_c,t,m,dm) in
        let c = (c' /\ c) in
        let m = ((k + rank_off) =+ n2w(w2n k_r + 1)) m in
        let m = (off =+ 0w) m in
          merge_trees (n-1) (a,k,m,dm,c)
      else
        let c = (t + child_off IN dm /\ c) in
        let t_c = m (k + child_off) in
        let (_,m,c') = fib_heap_merge(t_c,k,m,dm) in
        let c = (c' /\ c) in
        let c = (t + rank_off IN dm /\ c) in
        let t_r = m (t + rank_off) in
        let m = ((t + rank_off) =+ n2w(w2n t_r + 1)) m in
        let m = (off =+ 0w) m in
          merge_trees (n-1) (a,t,m,dm,c)
End



(* TODO: finish proof
  - check correct construction of statement
 *)
Theorem merge_trees:
  !i n fh v p xs frame.
  (map_mem a n fh * fts_mem(ann_fts 0w [FibTree x v xs]) * frame)
    (fun2set (m,dm)) /\
  (n < i /\ LENGTH xs < n) /\
  (x <> 0w /\ FLOOKUP fh n = NONE) /\
  merge_trees i (a,x,m,dm,T) = (m',b) ==>
  ?fh.
    (map_mem a n fh * frame)
    (fun2set (m',dm)) /\ b
Proof
  Induct
  >- fs[] >>
  rpt gen_tac >>
  simp[map_mem_def] >>
  Cases_on `n` >> fs[] >>
  simp[map_lookup_def,ones_def] >>
  simp[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  Cases_on `x = 0w` >> fs[] >>
  simp[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  simp[PULL_EXISTS] >>
  rpt strip_tac >> pop_assum mp_tac >>
  cheat
QED




(*
Low-level code.
Adjust after high-level code has been proven!

Definition fib_heap_build_rarray_def:
  fib_heap_build_rarray (n:num) (max_r:num)
    (array: 'a word, a:'a word,
     m:'a word -> 'a word, dm:'a word set, c: bool)
  =
    if n = 0 then (m,F) else
    if a = 0w then (m,c) else
    let (x,a',m,c) = fib_heap_remove(a,m,dm) in
    let (m,c) = merge_trees max_r (array,x,m,dm,c) in
      fib_heap_build_rarray (n-1) max_r (array,a',m,dm,c)
End






Definition fib_heap_collect_array_def:
  fib_heap_collect_array (n:num)
    (a:'a word, k:'a word, m:'a word -> 'a word, dm:'a word set, c:bool)
  =
    let off = a + bytes_in_word * (n2w n) in
    let c = (off IN dm /\ c) in
    let a_n = m off in
    let (k,m,c') = fib_heap_insert(k,a_n,m,dm) in
    let c = (c' /\ c) in
    let m = (off =+ 0w) m in
    if n = 0 then
      (k,m,c)
    else
      fib_heap_collect_array (n-1) (a,k,m,dm,c)
End

(* TODO: Finish proof -
 - finish Theorem construction first!
Theorem fib_heap_collect_array_inv:
  !frame fts c k.
    (fib_heap_inv fh fts) /\
    (map_mem_empty_v c n * frame) (fun2set (m,dm)) /\
    (k <=+ n) /\
    (m k <> 0w) ==>
    SEP_EXISTS x n.
      (one(c + bytes_in_word * k, x)) (fun2set (m,dm)) /\
      (x IN dm) /\
      (fts_has x n fts)
Proof
  cheat
QED
*)





Definition fib_heap_reb_def:
  fib_heap_reb (n:num)
    (a:'a word, array: 'a word, m: 'a word -> 'a word, dm: 'a word set)
  =
    let (m,c) = fib_heap_build_rarray n n (array,a,m,dm,T) in
    let (a,m,c) = fib_heap_collect_array (n-1) (array,0w,m,dm,c) in
    let c = (a + next_off IN dm /\ c) in
    let a_n = m (a + next_off) in
      find_min n (a,a,a_n,m,dm,c)
End

(*
 Main question: what is the fib_heap_build_rarray invariant!
*)



(* TODO: finish proof
- finish sub proofs first!
*)
Theorem fib_heap_reb:
  !frame fh.
  (fib_heap a fh * map_mem_empty c n * frame * cond(n = w2n (-1w)))
    (fun2set (m,dm)) /\
  fib_heap_reb n (a,c,m,dm) = (a,m',b) ==>
  ?fts. (fts_mem (ann_fts 0w (fts_reb n fts)) * map_mem_empty c n * frame *
    cond(a = head_key fts /\ fib_heap_inv fh fts))
    (fun2set (m,dm)) /\ b
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  pop_assum mp_tac >>
  simp[fib_heap_reb_def] >>
  cheat
QED
*)






