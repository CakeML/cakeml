(*
  Algorithm Level Verification for Fibonacci heap
*)
Theory fibonacci_heap
Ancestors
  misc words arithmetic list alist set_sep pair finite_map combin pred_set rich_list
  panSem
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
  ft = FibTree 'a 'b (ft list)
End

Type fts = “:('a,'b) ft list”;


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
   Constants
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

Definition max_rank_def[simp]:
  max_rank = (185: num)
End

Definition emp_rl_def:
  emp_rl = REPLICATE max_rank NONE
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

Theorem head_key_t_eq_head_key_thm:
  !list d.
  list <> [] ==>  (head_key_t d list = head_key list)
Proof
  Cases_on `list` >> fs[] >>
  Cases_on `h` >> simp[head_key_t_def,head_key_def]
QED


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


Theorem last_key_t_pull_first_thm:
  !x xs.
  (last_key_t _ (x::xs)) = last_key_t (head_key [x]) xs
Proof
  rpt strip_tac >>
  Cases_on `x` >>
  simp[last_key_t_def,head_key_def,head_key_t_def] >>
  simp[lemma_head_keys_eq_last_key_t]
QED





Definition last_key_def:
  last_key xs = last_key_t 0w xs
End


Theorem last_key_append_thm:
  !xs ys. ys <> [] ==> last_key (xs ++ ys) = last_key ys
Proof
  simp[last_key_def, last_key_t_append_thm]
QED

Theorem last_key_t_eq_last_key_thm:
  !list d.
  list <> [] ==> last_key_t d list = last_key list
Proof
  Cases_on `list` using SNOC_CASES >> fs[] >>
  Cases_on `x` >> simp[SNOC_APPEND] >>
  simp[last_key_t_def,last_key_def] >>
  gen_tac >>
  simp[last_key_t_append_thm,last_key_t_def,head_key_t_def]
QED

Theorem head_key_eq_last_key_thm:
  !list.
  list <> [] ==> head_key (REVERSE list) = last_key list
Proof
  Cases_on `list` using SNOC_CASES >> simp[] >>
  Cases_on `x` >> simp[SNOC_APPEND] >>
  simp[last_key_def,REVERSE_APPEND] >>
  simp[head_key_def,head_key_t_def,last_key_t_def,last_key_t_append_thm]
QED



Definition new_dnode_def:
  new_dnode v e m =
    <|  value := v;
        edges := e;
        mark  := m |>
End

Definition new_anode_def:
  new_anode d b n p c r =
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
        (new_anode v b n p (head_key ys) (LENGTH ys))
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


Theorem ann_fts_append2_thm:
  !p xs ys.
  ann_fts p (xs ++ ys) =
    (ann_fts_seg p (head_key_t (head_key xs) ys) (last_key_t (last_key xs) ys)
      (head_key_t (head_key xs) (TL xs ++ ys)) xs) ++
    (ann_fts_seg p (head_key_t (head_key ys) xs) (last_key_t (last_key ys) xs)
      (head_key_t (head_key_t (head_key ys) xs) (TL ys)) ys)
Proof
  rpt strip_tac >>
  Cases_on `xs` >> Cases_on `ys`
  >- (
    simp[head_key_def,last_key_def,head_key_t_def,last_key_t_def] >>
    simp[ann_fts_def,ann_fts_seg_def]
    )
  >- (
    simp[head_key_def,last_key_def,head_key_t_def,last_key_t_def] >>
    simp[ann_fts_seg_def] >>
    Cases_on `h` >>
    simp[ann_fts_def] >>
    simp[head_key_def,head_key_t_def,last_key_def] >>
    simp[lemma_head_keys_eq_last_key_t] >>
    simp[last_key_t_pull_first_thm,head_key_def,head_key_t_def]
    )
  >- (
    simp[ann_fts_seg_def] >>
    Cases_on `h` >>
    simp[head_key_def,last_key_def,head_key_t_def,last_key_t_def] >>
    simp[ann_fts_def] >>
    simp[head_key_def,last_key_def,head_key_t_def,last_key_t_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  qspecl_then [`(FibTree a b l::t)`,`(FibTree a' b' l'::t')`,`p`]
    assume_tac ann_fts_append_thm >>
  gvs[] >>
  simp[head_key_def,last_key_def,head_key_t_def,last_key_t_def] >>
  simp[lemma_head_keys_eq_last_key_t]
QED


Theorem lemma_ann_fts_arb_list:
  ann_fts p list =
    ann_fts_seg p (head_key list) (last_key list)
      (head_key_t (head_key list) (TL list)) list
Proof
  Cases_on `list`
  >- simp[ann_fts_def,ann_fts_seg_def] >>
  Cases_on `h` >>
  simp[ann_fts_def,head_key_def,head_key_t_def]
QED




Definition ann_ft_def:
  ann_ft p (FibTree k n xs) =
    FibTree k (new_anode n k k p (head_key xs) (LENGTH xs))
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
    one (a,Word w) * ones (a + bytes_in_word) ws
End

Definition b2w_def:
  b2w b = if b then 1w else 0w : 'a word
End

Definition edges_ones_def:
  (edges_ones off [] = one(off,Word 0w)) /\
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
    edges_ones (FST n.data.edges) (SND n.data.edges) *
    cond(k <> 0w /\ (n.rank < max_rank))
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
  !p xs ys.
  fts_mem (ann_fts p (xs ++ ys)) = fts_mem (ann_fts p (ys ++ xs))
Proof
  rpt strip_tac >>
  Cases_on `xs` >> Cases_on `ys` >> fs[]>>
  Cases_on `h` >> Cases_on `h'` >>
  pure_rewrite_tac[GSYM (cj 2 APPEND)] >>
  qspecl_then [`(FibTree a b l::t)`,`(FibTree a' b' l'::t')`,`p`]
    assume_tac ann_fts_append_thm >>
  qspecl_then [`(FibTree a' b' l'::t')`,`(FibTree a b l::t)`,`p`]
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
    `ft_mem(FibTree a (new_anode b' b n p (head_key l') (LENGTH l'))
      (ann_fts_seg a (head_key l') (last_key l')
      (head_key_t (head_key l') (TL l')) l')) *
     fts_mem
      (ann_fts_seg a (head_key l') (last_key l')
      (head_key_t (head_key l') (TL l')) l') * frame`, `a`] assume_tac) >>
  rfs[AC STAR_ASSOC STAR_COMM] >>
  qexistsl [`(FibTree a b' l'::t1)`,`t2`] >> simp[]
QED

(*The outside world already set the flag to T!*)
Definition empty_node_def:
  empty_node k (v,e) =
    if k = 0w then emp else
    ones k [v; FST e; b2w T; b2w F;k;k;0w;0w; n2w 0] *
    edges_ones (FST e) (SND e) * cond(k <> 0w)
End


Definition empty_node2_def:
  empty_node2 key p t =
    if key = 0w then emp else
    fts_mem(ann_fts p [t])
End

Theorem lemma_empty_node2_eq_fts_mem:
  k <> 0w ==> empty_node2 k p t = fts_mem(ann_fts p [t])
Proof
  simp[empty_node2_def]
QED


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
    (FibTree mem (new_dnode (mem + 1w) (HD edges) F)[]
    :: test_build_fts (mem + 100w * bytes_in_word) (amount) (TL edges)))
End

Definition test_build_ft_def:
  test_build_ft mem children edges =
    (FibTree mem (new_dnode (mem + 1w) (HD edges) T)
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
    new_dnode 11w (1000w, [(50w,10)]) F) [];
    FibTree 50w (
    new_dnode 51w (2000w, [(10w,50)]) F) [
        FibTree 100w
        (new_dnode 101w (3000w, []) F) []
    ]
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,head_key_t_def,head_key_def,last_key_def,REVERSE_DEF,ft_mem_def,ones_def,edges_ones_def,LENGTH,b2w_def,new_anode_def,new_dnode_def];
(*
val tfc = “test_full_conn (10000w:word64) 3 3” |> SCONV [test_full_conn_def];
*)
val test_large_fts_mem = “fts_mem (ann_fts 0w [
    test_build_ft (1000w:word64) 2 (test_full_conn 10000w 3 3)
    ])”
    |> SCONV [fts_mem_def,STAR_ASSOC,ann_fts_def,ann_fts_seg_def,test_full_conn_def,
    head_key_t_def,head_key_def,last_key_def,REVERSE_DEF,ft_mem_def,
    ones_def,edges_ones_def,LENGTH,b2w_def,new_anode_def,new_dnode_def,
    test_build_ft_def, test_build_fts_def, test_list_edges_def,
    TL_DEF, HD, FST, byteTheory.bytes_in_word_def];

val test =
    “ones 400w [x;y;z;e;r;t;y;u:word64]”
    |> SCONV [ones_def,STAR_ASSOC,byteTheory.bytes_in_word_def];



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
    (∃m. fts_has k' (new_dnode v' e m) (xs ++ ys)) ⇔
    ∃m. fts_has k' (new_dnode v' e m) (ys ++ xs)
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



Theorem lemma_length_less_eq_fts_size:
  ! fts.
  LENGTH fts <= fts_size fts
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
      ?m. fts_has k (new_dnode v e m) fts) /\
    (fts_all_dist fts) /\
    (fts_is_min (fts_hd_value fts) fts) /\
    (every_fts fts_parent_lower_eq fts) /\
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
  rename [`FibTree k v l::t`] >>
  last_x_assum (qspecl_then [`k`, `v.value`, `v.edges`] assume_tac) >>
  gvs[head_key_def,head_key_t_def] >>
  fs[Once fts_has_cases] >>
  first_x_assum (qspec_then `v.mark` assume_tac) >>
  rfs[head_key_def, head_key_t_def, new_dnode_def] >>
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

(*----------------------------------------------------------------
  fib_heap_inv weakend
------------------------------------------------------------------*)


Definition fib_heap_inv_weak_def:
  fib_heap_inv_weak fh (fts: ('a word, 'a data_node) fts) ⇔
    (!k v. FLOOKUP fh k = SOME v ==> k <> 0w) /\
    (!k v e. FLOOKUP fh k = SOME (v,e) <=>
      ?m. fts_has k (new_dnode v e m) fts) /\
    fts_all_dist fts /\
    every_fts fts_parent_lower_eq fts /\
    fib_heap_shape_ok fts
End

Theorem fib_heap_inv_weak_empty_thm:
  fib_heap_inv_weak FEMPTY []
Proof
  simp[fib_heap_inv_weak_def] >>
  simp[Once fts_has_cases, fts_all_dist_def,Once every_fts_def,
       fts_parent_lower_eq_def, fib_heap_shape_ok_def]
QED

Theorem lemma_fib_heap_inv_weak_empty_fts_imp_empty_map:
  !fh.
    fib_heap_inv_weak fh [] ==> fh = FEMPTY
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_weak_def] >>
  fs[Once fts_has_cases] >>
  Cases_on `fh` >> fs[] >>
  Cases_on `y` >>
  first_x_assum (qspecl_then [`x`,`q`,`r`] assume_tac) >>
  fs[FLOOKUP_SIMP]
QED


Theorem lemma_fib_heap_inv_weak_child:
  !fh k v l.
    fib_heap_inv fh [FibTree k v l]
    ==>
    fib_heap_inv_weak (fh \\ k) l /\
    k IN (FDOM fh)
Proof
  rpt gen_tac >> disch_tac >>
  fs[fib_heap_inv_def,fib_heap_inv_weak_def] >>
  `fts_all_dist l` by fs[fts_all_dist_def] >>
  `fib_heap_shape_ok l` by fs[fib_heap_shape_ok_def] >>
  qpat_x_assum `every_fts fts_parent_lower_eq [FibTree k v l]` mp_tac >>
  simp[Once every_fts_def,fts_parent_lower_eq_def] >>
  strip_tac >>
  conj_tac >> rpt strip_tac
  >- fs[DOMSUB_FLOOKUP_THM] >>
  Cases_on `k = k'` >>
  fs[DOMSUB_FLOOKUP_THM]
  >- fs[fts_all_dist_def] >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases] >>
  gvs[] >>
  first_x_assum (qspecl_then [`k`,`v.value`,`v.edges`] assume_tac) >>
  spose_not_then assume_tac >>
  fs[FLOOKUP_DEF] >>
  first_x_assum (qspec_then `v.mark` assume_tac) >>
  fs[Once fts_has_cases,new_dnode_def,data_node_component_equality]
QED



(* ------------------------------------------------------
  Logical FTS merge. (High-Level implementation)
--------------------------------------------------------*)

Definition fts_meld_def:
  (fts_meld [] fts2 = fts2) /\
  (fts_meld (ft1::fts1) [] = (ft1::fts1)) /\
  (fts_meld (FibTree k1 v1 l1::fts1) (FibTree k2 v2 l2::fts2) =
    if v1.value <=+ v2.value then
      (FibTree k1 v1 l1::(fts1 ++ (FibTree k2 v2 l2::fts2)))
    else
      (FibTree k2 v2 l2::(fts2 ++ (FibTree k1 v1 l1::fts1))))
End


Theorem lemma_fts_meld_length:
  LENGTH(fts_meld xs ys) = LENGTH (xs ++ ys)
Proof
  Cases_on `xs` >> Cases_on `ys` >> simp[fts_meld_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[fts_meld_def] >>
  IF_CASES_TAC >> simp[]
QED

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
  (!k v e. FLOOKUP fh1 k = SOME (v,e) ⇔ ∃m. fts_has k (new_dnode v e m) xs) /\
  (∀k v e. FLOOKUP fh2 k = SOME (v,e) ⇔ ∃m. fts_has k (new_dnode v e m) ys) /\
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
    rename [`FibTree k v l::t`] >>
    rpt strip_tac >>
    fs[EQ_IMP_THM] >>
    first_x_assum $ qspecl_then [`k'`,`v''.value`,`v''.edges`] assume_tac >>
    first_x_assum $ qspecl_then [`k'`,`v'.value`,`v'.edges`] assume_tac >>
    fs[] >>
    fs[PULL_EXISTS] >>
    first_x_assum $ qspec_then `v'.mark` assume_tac >>
    first_x_assum $ qspec_then `v''.mark` assume_tac >>
    fs[new_dnode_def] >>
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
  simp[new_dnode_def, data_node_component_equality] >>
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
  fs[new_dnode_def,lemma_data_node_cases]
QED




Theorem lemma_merge_fts_has:
  (∀k v e. FLOOKUP fh1 k = SOME (v,e) ⇔ ∃m. fts_has k (new_dnode v e m) xs) /\
  (∀k v e. FLOOKUP fh2 k = SOME (v,e) ⇔ ∃m. fts_has k (new_dnode v e m) ys) /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  (FLOOKUP (fh1 ⊌ fh2) k = SOME (v,e) ⇔
  ∃m. fts_has k (new_dnode v e m) (xs ++ ys))

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
  fs[fts_has_append_thm] >> res_tac >> fs[FLOOKUP_SIMP] >>
  Cases_on `FLOOKUP fh1 k` >> gvs[] >>
  res_tac >>
  fs[FLOOKUP_DEF,DISJOINT_DEF,EXTENSION] >>
  first_x_assum (qspec_then `k` assume_tac) >> gvs[]
QED




Theorem lemma_logical_meld:
  !fh1 fh2 xs ys.
  (fib_heap_inv fh1 xs) /\
  (fib_heap_inv fh2 ys) /\
  (DISJOINT (FDOM fh1) (FDOM fh2)) /\
  (fts_hd_value xs <=+ fts_hd_value ys) ==>
  (fib_heap_inv (FUNION fh1 fh2) (xs ++ ys))
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

Theorem fts_meld:
  !fh1 fts1 fh2 fts2 fts'.
  fib_heap_inv fh1 fts1 /\
  fib_heap_inv fh2 fts2 /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  fts_meld fts1 fts2 = fts' ==>
  fib_heap_inv (FUNION fh1 fh2) fts'
Proof
  rpt strip_tac >>
  Cases_on `fts1` >> Cases_on `fts2`
  >- (
    fs[fts_meld_def] >>
    simp[fib_heap_inv_def] >>
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fib_heap_inv_def]
    )
  >- (
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fts_meld_def]
    )
  >- (
    drule_all lemma_empty_heap >>
    disch_tac >> gvs[] >>
    fs[fts_meld_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  rename [`fts_meld (FibTree k v l::t) (FibTree k' v' l'::t') = fts'`] >>
  fs[fts_meld_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC
  >- (
    disch_tac >> gvs[] >>
    rewrite_tac[GSYM (cj 2 APPEND)] >>
    rewrite_tac[GSYM APPEND_ASSOC,GSYM lemma_cons_eq_append] >>
    irule lemma_logical_meld >> simp[fts_hd_value_def]
    ) >>
  disch_tac >> gvs[] >>
  fs[WORD_NOT_LOWER_EQUAL] >>
  drule_all WORD_LOWER_IMP_LOWER_OR_EQ >>
  disch_tac >> gvs[] >>
  rewrite_tac[GSYM (cj 2 APPEND)] >>
  rewrite_tac[GSYM APPEND_ASSOC,GSYM lemma_cons_eq_append] >>
  qspecl_then [`fh2`,`fh1`,`(FibTree k' v' l'::t')`,`(FibTree k v l::t)`]
    assume_tac lemma_logical_meld >>
  rfs[DISJOINT_SYM,fts_hd_value_def] >>
  metis_tac[DISJOINT_SYM,FUNION_COMM]
QED

Theorem logical_meld_fib_heap_inv_weak:
  !fh1 fh2 fts1 fts2.
  (fib_heap_inv_weak fh1 fts1) /\
  (fib_heap_inv_weak fh2 fts2) /\
  (DISJOINT (FDOM fh1) (FDOM fh2))
  ==>
  (fib_heap_inv_weak (FUNION fh1 fh2) (fts1 ++ fts2))
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_weak_def] >>
  rpt conj_tac
  >- (
    fs[FLOOKUP_FUNION] >>
    Cases_on `FLOOKUP fh1 0w` >> fs[]
    )
  >- (irule lemma_merge_fts_has >> simp[])
  >- (
    drule_all lemma_merge_all_dist >>
    strip_tac >>
    fs[fts_all_dist_sym_thm]
    )
  >- (
    fs[Once every_fts_def] >>
    simp[fts_parent_lower_eq_append_thm] >>
    rpt strip_tac >> res_tac >> simp[]
    ) >>
  simp[fib_heap_shape_ok_append_thm]
QED




Theorem fts_meld_weak:
  !fhx xs fhy ys fts.
  fib_heap_inv_weak fhx xs /\
  fib_heap_inv_weak fhy ys /\
  DISJOINT (FDOM fhx) (FDOM fhy) /\
  fts_meld xs ys = fts ==>
  fib_heap_inv_weak (FUNION fhx fhy) fts
Proof
  rpt strip_tac >>
  Cases_on `xs` >> Cases_on `ys`
  >- (
    fs[fts_meld_def] >>
    simp[fib_heap_inv_weak_def] >>
    drule_all lemma_fib_heap_inv_weak_empty_fts_imp_empty_map >>
    disch_tac >> gvs[] >>
    fs[fib_heap_inv_weak_def]
    )
  >- (
    drule_all lemma_fib_heap_inv_weak_empty_fts_imp_empty_map >>
    disch_tac >> gvs[] >>
    fs[fts_meld_def]
    )
  >- (
    drule_all lemma_fib_heap_inv_weak_empty_fts_imp_empty_map >>
    disch_tac >> gvs[] >>
    fs[fts_meld_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  rename [`fts_meld (FibTree k v l::t) (FibTree k' v' l'::t') = fts`] >>
  fs[fts_meld_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> disch_tac >> gvs[]
  >- (
    pure_rewrite_tac[GSYM (cj 2 APPEND)] >>
    rewrite_tac[GSYM APPEND_ASSOC,GSYM lemma_cons_eq_append] >>
    irule logical_meld_fib_heap_inv_weak >> simp[]
    ) >>
  fs[WORD_NOT_LOWER_EQUAL] >>
  drule_all WORD_LOWER_IMP_LOWER_OR_EQ >>
  disch_tac >> gvs[] >>
  pure_rewrite_tac[GSYM (cj 2 APPEND)] >>
  rewrite_tac[GSYM APPEND_ASSOC,GSYM lemma_cons_eq_append] >>
  qspecl_then [`fhy`,`fhx`,`(FibTree k' v' l'::t')`,`(FibTree k v l::t)`]
    assume_tac logical_meld_fib_heap_inv_weak >>
  metis_tac[DISJOINT_SYM,FUNION_COMM]
QED

(*--------------------------------------------------
  Memory Level Verification of Merging Heaps
--------------------------------------------------*)

Definition is_Word_def[simp]:
  is_Word (Word _ : 'a word_lab) = T
End

Theorem is_Word_read_apply_thm[simp]:
  is_Word (m (|x |-> Word w|) y) = is_Word (m y)
Proof
  simp[APPLY_UPDATE_THM] >>
  Cases_on `x = y` >> fs[] >>
  Cases_on `m y`>>
  simp[is_Word_def]
QED

Theorem is_Word_Word_thm[simp]:
  !x.
  is_Word(Word x)
Proof
  simp[]
QED


Definition get_Word_def[simp]:
  get_Word (Word w : 'a word_lab) = w
End

Definition in_mem_def[simp]:
  in_mem addr dm = (addr IN dm)
End

Definition read_mem_def:
  read_mem addr m dm c =
    let c' = in_mem addr dm in
    let w  = m addr in
    (get_Word w, c /\ c' /\ is_Word w)
End

Definition write_mem_def:
  write_mem addr w m dm c =
    let c' = in_mem addr dm in
    let m' = m (| addr |-> Word w |) in
    (m',c /\ c')
End


(*
Definition fib_heap_meld_def:
  fib_heap_meld
    (a1:'a word,a2:'a word,m:'a word -> 'a word_lab, dm: 'a word set)
  =
    if a2 = 0w then (a1,m,T) else
(*    let c = in_mem a2 dm in *)
    if a1 = 0w then (*list a is empty*)
      (a2,m,T)
    else
      let (l_a1,c) = read_mem (a1 + before_off) m dm T in
      let (l_a2,c) = read_mem (a2 + before_off) m dm c in

      let (m,c) = write_mem (l_a1 + next_off) a2   m dm c in
      let (m,c) = write_mem (a2 + before_off) l_a1 m dm c in
      let (m,c) = write_mem (l_a2 + next_off) a1   m dm c in
      let (m,c) = write_mem (a1 + before_off) l_a2 m dm c in

      let (v_a2,c) = read_mem a2 m dm c in
      let (v_a1,c) = read_mem a1 m dm c in
      if v_a1 <=+ v_a2 then
        (a1,m,c)
      else
        (a2,m,c)
End
*)

Theorem fib_heap_insert:
  !frame k v e.
    k <> 0w ==>
    ((empty_node k (v,e) * frame) (fun2set(m,dm)) ==>
    (fts_mem(ann_fts 0w [FibTree k (new_dnode v e F) []]) * frame) (fun2set(m,dm)) /\
    fib_heap_inv (FEMPTY |+ (k,v,e)) [FibTree k (new_dnode v e F) []])
Proof
  rpt strip_tac >>
  fs[empty_node_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  fs[ones_def,STAR_ASSOC] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[fib_heap_inv_def] >>
  gvs[] >>
  rpt strip_tac
  >- fs[FLOOKUP_SIMP]
  >- (
    Cases_on `k = k'` >> gvs[]
    >- (
      simp[FLOOKUP_SIMP] >>
      iff_tac >> strip_tac >> gvs[]
      >- (
        qexists `F` >>
        simp[Once fts_has_cases,data_node_component_equality, new_dnode_def]
        ) >>
      fs[Once fts_has_cases] >>
      fs[data_node_component_equality, new_dnode_def] >>
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



(*
Theorem fib_heap_meld_mem_thm:
  !frame p fts1 fts2 fts' m dm.
  fts_meld fts1 fts2 = fts' /\
  (fts_mem (ann_fts p fts1) * fts_mem (ann_fts p fts2) * frame)
    (fun2set (m,dm))
  ==>
  ?m'.
  fib_heap_meld (head_key fts1,head_key fts2,m,dm) = (head_key fts',m',T) /\
  (fts_mem (ann_fts p fts') * frame)
    (fun2set (m',dm))
Proof
  rpt gen_tac >> disch_tac >> fs[] >>
  Cases_on `fts1` >> Cases_on `fts2` >>
  fs[fib_heap_meld_def,read_mem_def,write_mem_def,next_off_def,before_off_def,
       head_key_def,head_key_t_def,fts_meld_def]
  >- fs[fts_mem_def,ann_fts_def,SEP_CLAUSES]
  >- (
    Cases_on `h` >> gvs[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> simp[]
    )
  >- (
    gvs[] >>
    fs[fts_mem_def,ann_fts_def,SEP_CLAUSES,STAR_ASSOC]
    ) >>
  Cases_on `h` >> Cases_on `h'` >> gvs[] >>
  rename[`(fts_mem (ann_fts p (FibTree k v l::t)) *
     fts_mem (ann_fts p (FibTree k' v' l'::t')) * frame) (fun2set(m,dm))`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  Cases_on `t` using SNOC_CASES >>
  Cases_on `t'` using SNOC_CASES >>
  fs[SNOC_APPEND,REVERSE_APPEND,fts_meld_def] >>
  IF_CASES_TAC >>
  SEP_R_TAC >> fs[head_key_t_def] >>
  SEP_R_TAC >> simp[]
  >- (
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >> fs[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    )
  >- (
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[AC STAR_ASSOC STAR_COMM]
    )
  >- (
    Cases_on `x` >> fs[head_key_t_def] >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[head_key_t_pull_last_thm]
    )
  >- (
    Cases_on `x` >> fs[head_key_t_def] >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[head_key_t_pull_last_thm,last_key_t_pull_thm,head_key_def,head_key_t_def] >>
    fs[AC STAR_ASSOC STAR_COMM]
    )
  >- (
    Cases_on `x` >> fs[head_key_t_def] >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[head_key_t_pull_last_thm,last_key_t_pull_thm,head_key_def,head_key_t_def] >>
    fs[AC STAR_ASSOC STAR_COMM]
    )
  >- (
    Cases_on `x` >> fs[head_key_t_def] >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[head_key_t_pull_last_thm,last_key_t_pull_thm,head_key_def,head_key_t_def] >>
    fs[AC STAR_ASSOC STAR_COMM]
    )
  >- (
    Cases_on `x` >> Cases_on `x'` >> fs[head_key_t_def] >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
       ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[head_key_t_pull_last_thm,last_key_t_pull_thm,head_key_def,head_key_t_def] >>
    fs[head_key_t_append_thm,head_key_t_pull_last_thm] >>
    fs[AC STAR_ASSOC STAR_COMM]
    ) >>
  Cases_on `x` >> Cases_on `x'` >> fs[head_key_t_def] >>
  fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  SEP_R_TAC >>
  SEP_W_TAC >> simp[] >>
  SEP_R_TAC >>
  fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
     ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[head_key_t_pull_last_thm,last_key_t_pull_thm,head_key_def,head_key_t_def] >>
  fs[head_key_t_append_thm,head_key_t_pull_last_thm] >>
  fs[AC STAR_ASSOC STAR_COMM]
QED
*)


(* -------------------------------------------------------
  Rebalancing of FTS
----------------------------------------------------------*)

Definition fts_rm_min_def:
  (fts_rm_min [] = (0w,[])) /\
  (fts_rm_min (FibTree k v l::ts) =
    (k,fts_meld l ts))
End

Theorem lemma_fts_rm_min_length:
  fts_size fts <= n /\
  fts_rm_min fts = (min,fts')
  ==>
  LENGTH fts' <= n
Proof
  Cases_on `fts` >> simp[fts_rm_min_def] >>
  Cases_on `h` >> simp[fts_rm_min_def] >>
  strip_tac >> gvs[] >>
  fs[fts_size_def,lemma_fts_meld_length] >>
  qspec_then `l` assume_tac lemma_length_less_eq_fts_size >>
  qspec_then `t` assume_tac lemma_length_less_eq_fts_size >>
  simp[]
QED

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
    ∃m. fts_has k3 (new_dnode v3 e m)
      (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'')) /\
    fts_all_dist
      (FibTree k v (FibTree k' v' l::t')::FibTree k'' v'' l'::t'')
  ==>
  !k3 v e. FLOOKUP (fhx \\ k) k3 = SOME (v,e) ⇔
    ∃m. fts_has k3 (new_dnode v e m)
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
  !fh fts min fts'.
  fib_heap_inv fh fts /\
  fts_rm_min fts = (min,fts') ==>
  fib_heap_inv_weak (fh \\ min) fts' /\
  min = head_key fts
Proof
  rpt gen_tac >>
  Cases_on `fts`
  >- (
    simp[fts_rm_min_def] >>
    rpt strip_tac >>
    fs[fib_heap_inv_weak_def,fib_heap_inv_def] >>
    simp[Once fts_has_cases] >>
    rpt strip_tac >>
    fs[Once fts_has_cases] >>
    Cases_on `k = 0w` >> gvs[DOMSUB_FLOOKUP_THM] >>
    simp[head_key_t_def,head_key_def]
    ) >>
  Cases_on `h` >>
  rename[`FibTree k v l::t`] >>
  fs[fib_heap_inv_def,fib_heap_inv_weak_def] >>
  strip_tac >>
  fs[fts_rm_min_def] >>
  Cases_on `l` >> Cases_on `t`>> fs[fts_meld_def]
  >- (
    gvs[] >>
    simp[every_fts_def, fts_parent_lower_eq_def, fts_all_dist_def] >>
    simp[fib_heap_shape_ok_def, Once fts_has_cases] >>
    rpt strip_tac
    >- fs[DOMSUB_FLOOKUP_THM] >>
    fs[DOMSUB_FLOOKUP_THM] >>
    res_tac >>
    pop_assum mp_tac >>
    simp[Once fts_has_cases] >>
    simp[Once fts_has_cases] >>
    simp[head_key_t_def,head_key_def]
    )
  >- (
    Cases_on `h` >> gvs[] >>
    rename [`fts_all_dist (FibTree k v []::FibTree k' v' l'::t')`] >>
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
      >- ( pop_assum mp_tac >> simp[Once fts_has_cases])
      >- (
        fs[fts_all_dist_def] >>
        last_x_assum(qspec_then `new_dnode v'' e m` assume_tac) >> fs[]
        ) >>
      qexists `m` >> simp[]
     )
    >- fs[fts_all_dist_def]
    >- (
      fs[Once every_fts_def,fts_parent_lower_eq_def] >>
      rpt gen_tac >>
      rpt strip_tac >> res_tac >> simp[]
      )
    >- fs[fib_heap_shape_ok_def] >>
    simp[head_key_t_def,head_key_def]
   )
  >- (
    Cases_on `h` >>
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
    >- fs[Once every_fts_def]
    >- fs[fib_heap_shape_ok_def] >>
    simp[head_key_t_def,head_key_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  rename [`head_key (FibTree min v (FibTree k' v' l'::t')::
    FibTree k'' v'' l''::t'')`] >>
  fs[fts_meld_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> strip_tac >> gvs[]
  >- (
    rpt conj_tac
    >- simp[DOMSUB_FLOOKUP_THM]
    >- (imp_res_tac lemma_fh_eq_fts_has_rm_hd >> simp[])
    >- imp_res_tac lemma_fts_all_dist_rm_hd
    >- imp_res_tac lemma_fts_parent_lower_eq_rm_hd
    >- (
      fs[fib_heap_shape_ok_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[fib_heap_shape_ok_append_thm] >>
      simp[fib_heap_shape_ok_def]
      ) >>
    simp[head_key_t_def,head_key_def]
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
    )
  >- (
    fs[fib_heap_shape_ok_def] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC] >>
    simp[fib_heap_shape_ok_append_thm] >>
    simp[fib_heap_shape_ok_def]
    ) >>
  simp[head_key_t_def,head_key_def]
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
!k v e. FLOOKUP fh k = SOME(v,e) <=> ?m. fts_has k (new_dnode v e m) fts

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
  fib_heap_inv_union fh fh_ft <=>
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


Theorem fib_heap_inv_union_empty_thm:
  !x.
  fib_heap_inv_union FEMPTY (REPLICATE x (FEMPTY,NONE))
Proof
  Induct
  >- simp[fib_heap_inv_union_def,fh_union_def,all_disjoint_def] >>
  simp[fib_heap_inv_union_def] >>
  simp[fh_union_def,fh_union_replicate_empty_thm,fib_heap_inv_empty_thm] >>
  simp[all_disjoint_def] >>
  fs[fib_heap_inv_union_def] >>
  rpt strip_tac >>
  Cases_on `n` >> fs[] >>
  gvs[rich_listTheory.EL_REPLICATE]
QED


Definition fib_heap_inv_list_def:
  fib_heap_inv_list fh ftss <=>
    ?fh_fts. fib_heap_inv_union fh fh_fts /\ ftss = MAP SND fh_fts
End


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



Theorem lemma_mem_eq_fts_has:
 !fts k v e.
    MEM (k,v,e) (flat_fts fts) <=>
    ?m. fts_has k (new_dnode v e m) fts
Proof
  ho_match_mp_tac flat_fts_ind >>
  rpt strip_tac >> fs[flat_fts_def]
  >- simp[Once fts_has_cases] >>
  iff_tac >> rpt strip_tac
  >- (
    qexists `fts.mark` >>
    simp[Once fts_has_cases,new_dnode_def,data_node_component_equality]
    )
  >- (qexists `m` >> simp[Once fts_has_cases])
  >- (qexists `m` >> simp[Once fts_has_cases]) >>
  pop_assum mp_tac >> simp[Once fts_has_cases] >>
  disch_tac >> fs[]
  >- fs[new_dnode_def, data_node_component_equality]
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
  fs[new_dnode_def]
QED



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
  first_x_assum (qspecl_then [`k'`,`(new_dnode v e m')`,`(new_dnode v' e' m)`]
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
  last_x_assum (qspecl_then [`k`,`new_dnode v e m`,`new_dnode q r m'`]
    assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases] >>
  simp[Once fts_has_cases] >>
  simp[new_dnode_def,data_node_component_equality] >>
  strip_tac >> fs[]
QED



Theorem lemma_alookup_eq_fts_has:
  !xs k v e.
  fts_all_dist xs ==>
  (ALOOKUP (flat_fts xs) k = SOME (v,e) <=> ?m. fts_has k (new_dnode v e m) xs)
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
  !v e m. ~fts_has x (new_dnode v e m) xs
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
    ∃m. fts_has x (new_dnode v e m) (xs ++ ys)) /\
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
    ∃m. fts_has k (new_dnode v e m) (xs ++ ys)) ==>
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
      ∃m. fts_has x (new_dnode v e m) (xs ++ ys)` mp_tac >>
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
  (!k v e. FLOOKUP fh k = SOME(v,e) <=> ?m. fts_has k (new_dnode v e m) (xs ++ ys))
  <=>
  ?fhx fhy.
    (!k v e. FLOOKUP fhx k = SOME(v,e) <=> ?m. fts_has k (new_dnode v e m) xs) /\
    fts_all_dist xs /\
    (!k v e. FLOOKUP fhy k = SOME(v,e) <=> ?m. fts_has k (new_dnode v e m) ys) /\
    fts_all_dist ys /\
    DISJOINT (FDOM fhx) (FDOM fhy) /\ fh = FUNION fhx fhy
Proof
  rpt gen_tac >>
  iff_tac
  >- (
    rpt strip_tac >>
    qexistsl [`alist_to_fmap (flat_fts xs)`,`alist_to_fmap (flat_fts ys)`] >>
    simp[lemma_alist_to_fmap_disjoint] >>
    rpt conj_tac
    >- (
      fs[fts_all_dist_append_thm] >>
      imp_res_tac lemma_alookup_eq_fts_has >> simp[]
      )
    >- fs[fts_all_dist_append_thm]
    >- (
      imp_res_tac fts_all_dist_sym_thm >>
      qpat_x_assum `∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
        ∃m. fts_has k (new_dnode v e m) (xs ++ ys)` mp_tac >>
      fs[fts_has_append_thm] >>
      pure_rewrite_tac[Once DISJ_COMM] >>
      simp[GSYM fts_has_append_thm] >>
      disch_tac >>
      fs[fts_all_dist_append_thm] >>
      imp_res_tac lemma_alookup_eq_fts_has >> simp[]
      )
    >- fs[fts_all_dist_append_thm] >>
    imp_res_tac lemma_finite_map_split
    ) >>
  disch_tac >> fs[] >>
  `fts_all_dist (xs ++ ys)` by imp_res_tac lemma_merge_all_dist >> simp[] >>
  rpt gen_tac >>
  irule lemma_merge_fts_has >> simp[]
QED



Theorem lemma_fib_heap_inv_weak_split:
  !x xs fh.
  fib_heap_inv_weak fh (x::xs) ==>
  ?fh1 fh2.
  fib_heap_inv_weak fh1 [x]  /\ fib_heap_inv_weak fh2 xs /\
  fh = FUNION fh1 fh2 /\ DISJOINT (FDOM fh1) (FDOM fh2)
Proof
  rpt gen_tac >>
  simp[fib_heap_inv_weak_def] >>
  rpt strip_tac >>
  qpat_x_assum `fts_all_dist(x::xs)` mp_tac >>
  pure_rewrite_tac[Once lemma_cons_eq_append] >>
  disch_tac >>
  qpat_x_assum `∀k v e. FLOOKUP fh k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) (x::xs)` mp_tac >>
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





Theorem fib_heap_inv_union_rm_thm:
  !fh1 ys fht t zs.
  fib_heap_inv_union fh1 (ys ++ (fht,SOME(t))::zs) ==>
  ?fh2.
    fib_heap_inv_union fh2 (ys ++ (FEMPTY,NONE)::zs) /\
    fib_heap_inv fht [t] /\
    DISJOINT (FDOM fht) (FDOM fh2)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
  imp_res_tac lemma_all_disjoint_split >>
  fs[EVERY_MEM] >>
  Cases_on `t` >> fs[] >>
  rename [`FibTree k v l`] >>
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



Theorem lemma_inv_imp_inv_weak:
  fib_heap_inv fh xs ==> fib_heap_inv_weak fh xs
Proof
  simp[fib_heap_inv_def,fib_heap_inv_weak_def]
QED


Theorem lemma_inv_weak_imp_inv:
  fib_heap_inv_weak fh [x] ==> fib_heap_inv fh [x]
Proof
  Cases_on `x` >> fs[fib_heap_inv_weak_def, fib_heap_inv_def] >>
  rpt strip_tac >>
  simp[fts_is_min_def] >>
  fs[Once every_fts_def,fts_parent_lower_eq_def] >>
  simp[fts_hd_value_def]
QED





(*
  first_x_assum $ irule_at $ Pos hd >>
  first_x_assum $ irule_at $ Pos hd >>
  fs[EVERY_MEM,FORALL_PROD] >>
  metis_tac[]
*)

(*-------------------------------------------------------------------
 Rebalancing of Trees
-------------------------------------------------------------------*)

Definition fts_merge_trees_def:
  fts_merge_trees (FibTree k1 v1 l1) (FibTree k2 v2 l2) =
    if v1.value <=+ v2.value then
      FibTree k1 v1 (fts_meld l1 [FibTree k2 v2 l2])
    else
      FibTree k2 v2 (fts_meld l2 [FibTree k1 v1 l1])
End

Theorem lemma_fts_merge_trees_length:
  LENGTH l1 = LENGTH l2 /\
  fts_merge_trees (FibTree k1 v1 l1) (FibTree k2 v2 l2) = (FibTree k3 v3 l3)
  ==>
  LENGTH l3 = LENGTH l1 + 1
Proof
  simp[fts_merge_trees_def] >> IF_CASES_TAC >>
  strip_tac >> gvs[] >>
  simp[lemma_fts_meld_length]
QED

Theorem lemma_alookup_in_disjoint:
  fts_all_dist (FibTree k3 v3 l::t) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v (FibTree k3 v3 l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) /\
  fts_has k'' (new_dnode v'' e m) [FibTree k' v' ys] /\
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e) ==>
    ∃m. fts_has k'' (new_dnode v'' e m)
      [FibTree k v (fts_meld xs [FibTree k' v' ys])]
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  Cases_on `xs`
  >- (
    simp[FLOOKUP_SIMP] >> CASE_TAC
    >- (
      strip_tac >>
      simp[fts_meld_def] >>
      res_tac >>
      qexists `m` >> simp[Once fts_has_cases]
      ) >>
    strip_tac >> gvs[] >>
    qexists `m` >> simp[fts_meld_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac[fts_has_cases] >> simp[] >>
    simp[Once fts_has_cases]
    ) >>
  Cases_on `h` >>
  simp[fts_meld_def] >>
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    (∃m. fts_has k'' (new_dnode v'' e m)
      [FibTree k v (fts_meld xs [FibTree k' v' ys])]) ==>
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e)
Proof
  rpt strip_tac >>
  Cases_on `xs`
  >- (
    fs[fts_meld_def] >>
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
      fs[Once fts_has_cases,new_dnode_def,data_node_component_equality] >>
      fs[Once fts_has_cases]
      )
    >- fs[Once fts_has_cases] >>
    res_tac >>
    simp[FLOOKUP_SIMP] >> CASE_TAC >>
    fs[FLOOKUP_DEF,DISJOINT_ALT] >> res_tac
    ) >>
  Cases_on `h` >> fs[fts_meld_def] >>
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
      >- fs[new_dnode_def,data_node_component_equality] >>
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
      first_x_assum(qspecl_then [`k''`,`(new_dnode q r m')`,`(new_dnode v'' e m)`]
        assume_tac) >>
      rfs[] >>
      pop_assum mp_tac >> simp[Once fts_has_cases] >>
      simp[new_dnode_def,data_node_component_equality]
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
    >- fs[new_dnode_def,data_node_component_equality] >>
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
  first_x_assum(qspecl_then [`k''`,`(new_dnode q r m')`,`(new_dnode v'' e m)`]
    assume_tac) >>
  rfs[] >>
  pop_assum mp_tac >> simp[Once fts_has_cases] >>
  simp[new_dnode_def,data_node_component_equality]
QED




Theorem lemma_fts_has_merge_trees:
  !xs ys fh1 fh2 k v k' v'.
  fts_all_dist [FibTree k v xs] /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) ==>
  ∀k'' v'' e.
    FLOOKUP (fh1 ⊌ fh2) k'' = SOME (v'',e) ⇔
    ∃m. fts_has k'' (new_dnode v'' e m)
      [FibTree k v (fts_meld xs [FibTree k' v' ys])]
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
  fts_is_min v.value (fts_meld xs [FibTree k' v' ys])
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_meld_def] >>
    simp[fts_is_min_def] >>
    drule_all lemma_lower_eq_fts_is_min >> fs[]
    ) >>
  Cases_on `h` >>
  simp[fts_meld_def] >>
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
   [FibTree k v (fts_meld xs [FibTree k' v' ys])]
Proof
  fs[Once every_fts_def] >>
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_meld_def] >>
    fs[Once every_fts_def] >>
    fs[Once every_fts_def,fts_parent_lower_eq_def] >>
    simp[Once every_fts_def,fts_is_min_def] >>
    gvs[fts_is_min_def] >>
    imp_res_tac lemma_lower_eq_fts_is_min >> fs[] >>
    rpt strip_tac >> res_tac
    ) >>
  Cases_on `h` >> simp[fts_meld_def] >>
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
  fib_heap_shape_ok [FibTree k v (fts_meld xs [FibTree k' v' ys])]
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_meld_def] >>
    fs[fib_heap_shape_ok_def] >>
    simp[fts_size_def] >>
    simp[Ntimes fib_num_def 5] >>
    simp[Once fib_num_def] >>
    simp[Once fib_num_def]
    ) >>
  Cases_on `h` >>
  simp[fts_meld_def] >>
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
   ∃m. fts_has k (new_dnode v.value v.edges m) (FibTree k v l::rest))
  ==>
  FLOOKUP fh k = SOME (v.value,v.edges)
Proof
  strip_tac >>
  fs[fts_all_dist_def] >>
  Cases_on `?m. fts_has k (new_dnode v.value v.edges m) (FibTree k v l::rest)` >>
  fs[]
  >- (qexists `m` >> simp[]) >>
  first_x_assum(qspec_then `v.mark` assume_tac) >>
  pop_assum mp_tac >>
  simp[Once fts_has_cases,new_dnode_def,data_node_component_equality]
QED



Theorem lemma_fts_has_in_map:
  (!k' v' e'. FLOOKUP fh k' = SOME (v',e') ⇔
   ∃m. fts_has k' (new_dnode v' e' m) xs) /\
  fts_has k' v' xs
  ==>
  FLOOKUP fh k' = SOME (v'.value,v'.edges)
Proof
  strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum(qspecl_then [`k'`,`v'.value`,`v'.edges`] assume_tac) >>
  fs[] >>
  first_x_assum(qspec_then `v'.mark` assume_tac) >>
  fs[new_dnode_def,lemma_data_node_cases]
QED




Theorem lemma_fts_has_both_maps_first_contra:
  fts_has k v2 ys /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v xs]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) ys) /\
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v (FibTree k2 v2 l::t)]) ==>
  FLOOKUP fh k3 = SOME (v3.value,v3.edges)
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum(qspecl_then [`k3`,`v3.value`,`v3.edges`] assume_tac) >> fs[] >>
  first_x_assum(qspec_then `v3.mark` assume_tac) >>
  fs[new_dnode_def,lemma_data_node_cases] >>
  pop_assum mp_tac >> simp[Once fts_has_cases]
QED


Theorem lemma_fts_has_both_maps_child_contra:
  fts_has k3 v3 (FibTree k2 v2 l::t) /\
  fts_has k3 v4 ys /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (∀k' v' e.
    FLOOKUP fh1 k' = SOME (v',e) ⇔
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v (FibTree k2 v2 l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) ys) ==>
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v (FibTree k'' v'' l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) /\
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v (FibTree k'' v'' l::t)]) /\
  (∀k v e.
    FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) /\
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
    ∃m. fts_has k' (new_dnode v' e m) [FibTree k v xs]) /\
  fts_all_dist [FibTree k v xs] /\
  (∀k v e.
     FLOOKUP fh2 k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' ys]) /\
  fts_all_dist [FibTree k' v' ys] /\
  DISJOINT (FDOM fh1) (FDOM fh2) ==>
  fts_all_dist [FibTree k v (fts_meld xs [FibTree k' v' ys])]
Proof
  strip_tac >>
  Cases_on `xs`
  >- (
    simp[fts_meld_def] >>
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
  Cases_on `h` >> simp[fts_meld_def] >>
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
  fib_heap_inv (FUNION fh1 fh2) [FibTree k v (fts_meld xs [FibTree k' v' ys])]
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
  rfs[DISJOINT_SYM] >>
  simp[DISJOINT_SYM,fib_heap_inv_comm_thm]
QED



Definition fts_link_trees_def:
  fts_link_trees (n: num) rl (FibTree k v l) =
    if n = 0 then (rl,F) else
    if max_rank <= (LENGTH l) then (rl,F) else
    case EL (LENGTH l) rl of
     |NONE =>
        (LUPDATE (SOME(FibTree k v l)) (LENGTH l) rl,T)
     |SOME(FibTree k' v' l') =>
        if (max_rank - 1) <= (LENGTH l) then (rl,F) else
        fts_link_trees (n - 1) (LUPDATE NONE (LENGTH l) rl)
          (fts_merge_trees (FibTree k v l) (FibTree k' v' l'))
End


Theorem lemma_fts_link_trees_length_rl:
  !n rl t.
  LENGTH (FST (fts_link_trees n rl t)) = LENGTH rl
Proof
  Induct >> rpt gen_tac >> Cases_on `t` >> simp[Once fts_link_trees_def] >>
  IF_CASES_TAC >> simp[] >>
  CASE_TAC >> simp[]
  >- (
    CASE_TAC >> simp[] >>
    CASE_TAC >> simp[]
    ) >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED


(*
This is another way to implement the fts_link_trees operation.


Theorem lemma_fts_meld_suc_length:
  LENGTH (fts_meld l [FibTree k' v' l']) = if l = [] then 1 else LENGTH l + 1
Proof
  Cases_on `l` >> gvs[fts_meld_def] >>
  Cases_on `h` >> gvs[fts_meld_def] >>
  rw[]
QED



Definition fts_link_trees2_def:
  fts_link_trees2 rl (FibTree k v l) =
    if max_rank <= (LENGTH l) then (rl,F) else
    case EL (LENGTH l) rl of
     |SOME(FibTree k' v' l') =>
        if LENGTH l <> LENGTH l' then (rl,F) else
        fts_link_trees2 (LUPDATE NONE (LENGTH l) rl)
          (fts_merge_trees (FibTree k v l) (FibTree k' v' l'))
     |NONE =>
        (LUPDATE (SOME(FibTree k v l)) (LENGTH l) rl,T)
Termination
  WF_REL_TAC `measure $ \(rl,ft). case ft of FibTree k v l => max_rank - LENGTH l` >>
  rw[] >>
  CASE_TAC >> gvs[] >>
  fs[fts_merge_trees_def,AllCaseEqs()] >> gvs[] >>
  rw[lemma_fts_meld_suc_length] >> gvs[]
End
*)

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


Theorem ts_to_fhts_length_thm:
  LENGTH (ts_to_fhts ts) = LENGTH ts
Proof
  simp[LENGTH_MAP,lemma_ts_to_fhts_to_map]
QED



Theorem lemma_fhts_to_ts_absorp:
  fhts_to_ts (ts_to_fhts rl) = rl
Proof
  rewrite_tac[lemma_ts_to_fhts_to_map,fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  simp[MAP_MAP_o] >>
  simp[MAP_EQ_ID] >>
  rpt strip_tac >>
  CASE_TAC >> fs[]
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



Theorem lemma_inv_imp_alist_to_fmap_inv:
  fib_heap_inv fh fts ==>
  fib_heap_inv (alist_to_fmap (flat_fts fts)) fts
Proof
  strip_tac >>
  Cases_on `fts`
  >- fs[alist_to_fmap_def,flat_fts_def,fib_heap_inv_empty_thm] >>
  Cases_on `h` >>
  rename [`FibTree k v l::t`] >>
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
      simp[Once fts_has_cases,new_dnode_def,data_node_component_equality]
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
  qexists `(new_dnode v'' e'' m)`>> simp[]
QED




Theorem lemma_fdom_fh_eq_fdom_alist_to_fmap:
  !fh fts.
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (new_dnode v e m) fts)
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
    fs[new_dnode_def,data_node_component_equality,lemma_data_node_cases]
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
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (new_dnode v e m) fts) /\
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


Theorem fib_heap_inv_union_el_thm:
  !i list m x fh1.
  i < LENGTH list /\
  (EL i list) = (m,SOME(x)) /\
  fib_heap_inv_union fh1 list ==>
  ?fh2. fib_heap_inv fh2 [x] /\ fh2 SUBMAP fh1
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
  drule_all lemma_inv_union_el >> strip_tac >>
  drule_all EL_MEM >> strip_tac >>
  gvs[] >>
  qexists `m` >> fs[] >>
  imp_res_tac fh_union_mem_submap_thm
QED


Theorem lemma_fh_union_el_snd:
  i < LENGTH list /\
  SND (EL i list) = SOME(x) /\
  fib_heap_inv_union (fh_union list) list
  ==>
  ?fh. fib_heap_inv fh [x] /\ fh SUBMAP (fh_union list)
Proof
  strip_tac >>
  fs[fib_heap_inv_union_def] >>
  Cases_on `EL i list` >> gvs[] >>
  drule_all lemma_inv_union_el >> strip_tac >>
  drule_all EL_MEM >> strip_tac >>
  gvs[] >>
  qexists `q` >> fs[] >>
  imp_res_tac fh_union_mem_submap_thm
QED


Theorem lemma_fts_link_list_upd_all_disjoint_lupdate:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (MAP SND rl)❲i❳ = SOME x /\
  i < LENGTH rl
  ==>
  DISJOINT (set (MAP FST (flat_fts [x])))
    (set (MAP FST (flat_fts [FibTree k v l])))
Proof
  strip_tac >>
  fs[EL_MAP] >>
  fs[fib_heap_inv_def] >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >> gvs[] >>
  imp_res_tac lemma_fh_union_el_snd >>
  fs[fib_heap_inv_union_def] >> gvs[] >>
  imp_res_tac SUBMAP_FDOM_SUBSET >>
  imp_res_tac DISJOINT_SUBSET >>
  qpat_x_assum `fib_heap_inv fh [x]` mp_tac >>
  simp[fib_heap_inv_def] >> strip_tac >>
  drule lemma_fdom_fh_eq_fdom_alist_to_fmap >>
  strip_tac >> fs[DISJOINT_SYM]
QED


Theorem lemma_fts_link_list_upd_all_disjoint:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
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
  fs[fib_heap_inv_union_def] >>
  `i < LENGTH rl /\ j < LENGTH rl` by gvs[] >>
  drule_all all_disjoint_el_thm >>
  strip_tac >> gvs[] >>
  fs[fib_heap_inv_weak_def] >>
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
    (!k v e. FLOOKUP fh k = SOME (v,e) <=> ?m. fts_has k (new_dnode v e m) fts) /\
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
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
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
  rename[`fib_heap_inv (alist_to_fmap (flat_fts [FibTree k' v' l']))
    [FibTree k' v' l']`] >>
  fs[EL_LUPDATE] >>
  pop_assum mp_tac >> IF_CASES_TAC >> fs[]
  >- (
    strip_tac >> gvs[] >>
    irule lemma_inv_imp_alist_to_fmap_inv >>
    qexists `fh1` >> simp[]
    ) >>
  strip_tac >>
  rfs[EL_MAP] >>
  fs[fib_heap_inv_union_def] >>
  fs[EVERY_EL] >>
  res_tac >>
  Cases_on `EL i rl` >> fs[] >>
  gvs[] >>
  `∀k v e. FLOOKUP q k = SOME (v,e) ⇔
    ∃m. fts_has k (new_dnode v e m) [FibTree k' v' l']` by fs[fib_heap_inv_def] >>
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
  fs[fib_heap_inv_union_def] >>
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


Theorem lemma_fts_link_list_upd_all_disjoint_lupdate2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  (rl❲i❳ = SOME x) /\
  i < LENGTH rl
  ==>
  DISJOINT (set (MAP FST (flat_fts [x])))
    (set (MAP FST (flat_fts [FibTree k v l])))
Proof
  strip_tac >>
  fs[fib_heap_inv_def] >>
  imp_res_tac lemma_fdom_fh_eq_fdom_alist_to_fmap >> gvs[] >>
  fs[fib_heap_inv_union_def] >>
  qpat_x_assum `fh2 = fh_union (ts_to_fhts rl)` mp_tac >>
  drule LESS_LENGTH >> strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  simp[lemma_ts_to_fhts_to_map] >>
  fs[EL_APPEND_EQN] >>
  simp[fh_union_append_thm,fh_union_def] >>
  strip_tac >> gvs[]
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
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
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
  fs[fib_heap_inv_union_def] >>
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
  qpat_x_assum `fib_heap_inv fh1 [Fibtree k v l]` mp_tac >>
  simp[Once fib_heap_inv_def] >>
  strip_tac >>
  imp_res_tac lemma_fh_eq_alist_to_fmap >> gvs[] >>
  fs[MAP_MAP_o] >>
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
  qabbrev_tac `ys' =
        (MAP
             ((λn.
                   case n of
                     NONE => (FEMPTY,NONE)
                   | SOME t => (alist_to_fmap (flat_fts [t]),SOME t)) ∘ SND)
             ys1)` >>
  qspecl_then [`alist_to_fmap (flat_fts [FibTree k v l])`,`fh_union ys'`]
    assume_tac FUNION_COMM >>
  res_tac >> simp[]
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
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  (∀n map k' v' l'.
    (n < LENGTH (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)) /\
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)❲n❳ =
    (map,SOME (FibTree k' v' l')) ⇒
    LENGTH l' = n)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
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
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 rl /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  (fhts_to_ts rl)❲LENGTH l❳ = NONE ==>
  fib_heap_inv_union (fh1 ⊌ fh2)
    (ts_to_fhts (fhts_to_ts rl)❲LENGTH l ↦ SOME (FibTree k v l)❳)
Proof
  strip_tac >>
  simp[fib_heap_inv_union_def] >>
  rpt conj_tac
  >- imp_res_tac lemma_fts_link_list_upd_inv
  >- imp_res_tac lemma_fts_link_list_upd_all_disjoint
  >- imp_res_tac lemma_fts_link_list_upd_fh_union >>
  rpt strip_tac >>
  imp_res_tac lemma_fts_link_list_upd_array_inv
QED



Theorem lemma_fts_link_list_upd_inv2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  rl❲LENGTH l❳ = NONE ==>
  EVERY
    (λ(fh,O_ft).
         case O_ft of
           NONE => fib_heap_inv fh []
         | SOME ft => fib_heap_inv fh [ft])
    (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))
Proof
  strip_tac >>
  simp[lemma_ts_to_fhts_to_map,EVERY_MAP,EVERY_EL,EL_MAP] >>
  rpt strip_tac >>
  Cases_on `n = LENGTH l` >> CASE_TAC >> simp[fib_heap_inv_empty_thm]
  >- (
    gvs[EL_LUPDATE] >>
    irule lemma_inv_imp_alist_to_fmap_inv >>
    qexists `fh1` >> simp[]
    ) >>
  gvs[EL_LUPDATE] >>
  fs[fib_heap_inv_union_def] >>
  qpat_x_assum `EVERY (λ(fh,O_ft). case O_ft of
    NONE => fib_heap_inv fh []
    | SOME ft => fib_heap_inv fh [ft]) (ts_to_fhts rl) ` mp_tac >>
  simp[lemma_ts_to_fhts_to_map,EVERY_MAP,EVERY_EL] >>
  strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[EL_MAP]
QED






Theorem lemma_fh_union_eq_fh_union_alist_to_fmap2:
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
  fs[fib_heap_inv_union_def] >>
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



Theorem lemma_fts_link_list_upd_all_disjoint2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  rl❲LENGTH l❳ = NONE ==>
  all_disjoint
    (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))
Proof
  strip_tac >>
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[all_disjoint_genlist_thm] >>
  rpt strip_tac >> simp[] >>
  Cases_on `i = LENGTH l` >> Cases_on `j = LENGTH l` >> fs[]
  >- (
    `j < LENGTH rl` by simp[] >>
    fs[EL_LUPDATE] >>
    Cases_on `EL j rl` >> simp[] >>
    drule_all lemma_fts_link_list_upd_all_disjoint_lupdate2 >>
    gvs[DISJOINT_SYM]
    )
  >- (
    `i < LENGTH rl` by simp[] >>
    fs[EL_LUPDATE] >>
    Cases_on `EL i rl` >> simp[] >>
    drule_all lemma_fts_link_list_upd_all_disjoint_lupdate2 >>
    gvs[DISJOINT_SYM]
    ) >>
  fs[EL_LUPDATE] >>
  fs[fib_heap_inv_union_def] >>
  `i < LENGTH (ts_to_fhts rl) /\ j < LENGTH (ts_to_fhts rl)`
    by fs[ts_to_fhts_length_thm] >>
  drule_all all_disjoint_el_thm >>
  simp[lemma_ts_to_fhts_to_map,EL_MAP]
QED



Theorem lemma_fts_link_list_upd_fh_union2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  rl❲LENGTH l❳ = NONE ==>
  fh1 ⊌ fh2 =
  fh_union (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))
Proof
  strip_tac >>
  simp[lemma_ts_to_fhts_to_map] >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  drule LESS_LENGTH >> strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  `LENGTH l  = LENGTH ys1` by simp[] >>
  qpat_x_assum `LENGTH ys1 = LENGTH l` kall_tac >>
  simp[] >>
  fs[EL_APPEND_EQN] >>
  fs[fib_heap_inv_union_def] >>
  qpat_x_assum `fh2 = fh_union (ts_to_fhts (ys1 ++ NONE::ys))` mp_tac >>
  simp[lemma_ts_to_fhts_to_map] >>
  strip_tac >>
  gvs[fh_union_append_thm,fh_union_def] >>
  qpat_x_assum `fib_heap_inv_def fh1 [FibTree k v l]` mp_tac >>
  simp[fib_heap_inv_def] >> strip_tac >>
  imp_res_tac lemma_fh_eq_alist_to_fmap >>
  gvs[] >>
  qabbrev_tac `ys' =
        (MAP
             (λn.
                   case n of
                     NONE => (FEMPTY,NONE)
                   | SOME t => (alist_to_fmap (flat_fts [t]),SOME t))
             ys1)` >>
  qpat_x_assum `DISJOINT (FDOM (fh_union ys'))
    (set (MAP FST (flat_fts [FibTree k v l])))` mp_tac >>
  rewrite_tac[GSYM FDOM_alist_to_fmap] >> strip_tac >>
  qspecl_then [`alist_to_fmap (flat_fts [FibTree k v l])`,`fh_union ys'`]
    assume_tac FUNION_COMM >>
  rfs[DISJOINT_SYM] >>
  simp[FUNION_ASSOC]
QED


Theorem lemma_fts_link_list_upd_array_inv2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  rl❲LENGTH l❳ = NONE ==>
  (∀n map k' v' l'.
    (n < LENGTH (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))) /\
    (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))❲n❳ =
    (map,SOME (FibTree k' v' l')) ⇒
    LENGTH l' = n)
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  simp[lemma_ts_to_fhts_to_map,EL_MAP] >>
  simp[EL_LUPDATE] >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum (qspecl_then [`n`,`map'`,`k'`,`v'`,`l'`] assume_tac) >>
  pop_assum mp_tac >>
  simp[lemma_ts_to_fhts_to_map,EL_MAP,LENGTH_MAP,EL_MAP]
QED


Theorem lemma_fts_link_list_upd2:
  fib_heap_inv fh1 [FibTree k v l] /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  LENGTH rl = max_rank /\
  ¬(max_rank ≤ LENGTH l) /\
  rl❲LENGTH l❳ = NONE ==>
  fib_heap_inv_union (fh1 ⊌ fh2)
    (ts_to_fhts (rl❲LENGTH l ↦ SOME (FibTree k v l)❳))
Proof
  strip_tac >>
  simp[fib_heap_inv_union_def] >>
  rpt conj_tac
  >- imp_res_tac lemma_fts_link_list_upd_inv2
  >- imp_res_tac lemma_fts_link_list_upd_all_disjoint2
  >- imp_res_tac lemma_fts_link_list_upd_fh_union2 >>
  rpt strip_tac >>
  imp_res_tac lemma_fts_link_list_upd_array_inv2
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


Theorem lemma_fib_heap_inv_union_rm_fh_union:
  fib_heap_inv_union fh list /\
  i < LENGTH list /\
  EL i list = (m,SOME t)
  ==>
  fh = FUNION m (fh_union (LUPDATE (FEMPTY,NONE) i list))
Proof
  strip_tac >>
  drule_all lemma_el_index_split >> strip_tac >>
  gvs[] >>
  fs[fib_heap_inv_union_def] >>
  simp[lupdate_append2] >>
  simp[fh_union_append_thm,fh_union_def] >>
  simp[FUNION_ASSOC] >>
  qpat_x_assum `all_disjoint (xs ++ [(m,SOME t)] ++ ys)` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,GSYM lemma_cons_eq_append] >>
  strip_tac >> imp_res_tac lemma_all_disjoint_split >>
  fs[fh_union_append_thm] >>
  simp[DISJOINT_SYM,FUNION_COMM]
QED




Theorem lemma_fib_heap_inv_union_el:
  !fh1 rl k v l.
    LENGTH l < LENGTH rl /\
    fib_heap_inv_union fh1 rl /\
    (fhts_to_ts rl)❲LENGTH l❳ = SOME (FibTree k v l)
    ==>
    ?fh2.
      fib_heap_inv fh2 [FibTree k v l] /\
      DISJOINT (FDOM fh2) (FDOM (fh_union (LUPDATE (FEMPTY,NONE) (LENGTH l) rl))) /\
      fh1 = FUNION fh2 (fh_union (LUPDATE (FEMPTY,NONE) (LENGTH l) rl))
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac[fhts_to_ts_def] >>
  rewrite_tac[GENLIST_EL_MAP] >>
  simp[EL_MAP] >> strip_tac >>
  `EVERY (\(fh,O_ft). case O_ft of
    |NONE => fib_heap_inv fh []
    |SOME(ft) => fib_heap_inv fh [ft]) rl` by fs[fib_heap_inv_union_def] >>
  fs[EVERY_EL] >>
  res_tac >>
  Cases_on `EL (LENGTH l) rl` >>
  gvs[] >>
  `all_disjoint rl` by fs[fib_heap_inv_union_def] >>
  drule_all lemma_all_disjoint_lupdate >> strip_tac >>
  drule_all lemma_fib_heap_inv_union_rm_fh_union >> strip_tac >>
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




Theorem lemma_fib_heap_inv_union_imp_lupdate_fempty:
  x < LENGTH rl /\
  fib_heap_inv_union (fh_union rl) rl ==>
  fib_heap_inv_union (fh_union (LUPDATE (FEMPTY,NONE) x rl))
    (LUPDATE (FEMPTY,NONE) x rl)
Proof
  strip_tac >>
  gvs[] >>
  fs[fib_heap_inv_union_def] >>
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



Theorem fts_link_trees2:
  !rl' n rl fh1 fh2 k v l.
    fib_heap_inv fh1 [FibTree k v l] /\
    fib_heap_inv_union fh2 (ts_to_fhts rl) /\
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    LENGTH rl = max_rank /\
    fts_link_trees n rl
      (FibTree k v l) =
      (rl',T)
    ==>
    fib_heap_inv_union (FUNION fh1 fh2) (ts_to_fhts rl') /\ LENGTH rl = LENGTH rl'
Proof
  strip_tac >> Induct >> strip_tac
  >- fs[Once fts_link_trees_def] >>
  rpt gen_tac >> disch_tac >> fs[] >>
  pop_assum mp_tac >>
  simp[Once fts_link_trees_def] >>
  IF_CASES_TAC >> fs[] >>
  CASE_TAC >> CASE_TAC
  >- (
    strip_tac >> gvs[]  >>
    irule lemma_fts_link_list_upd2 >> simp[]
    )
  >- (CASE_TAC >> simp[])
  >- (
   strip_tac >> gvs[] >>
   irule lemma_fts_link_list_upd2 >> simp[]
    ) >>
  CASE_TAC >> simp[] >>
  rename [`fts_merge_trees (FibTree k v l) (FibTree k' v' l')`] >>
  Cases_on `fts_merge_trees (FibTree k v l) (FibTree k' v' l')` >>
  rename [`fts_merge_trees (FibTree k v l) (FibTree k' v' l') =
    FibTree k'' v'' l''`] >>
  `LENGTH l < LENGTH rl` by gvs[] >>
  `∀n map k3 v3 l3. n < LENGTH (ts_to_fhts rl) ∧ (ts_to_fhts rl)❲n❳ =
    (map,SOME (FibTree k3 v3 l3)) ⇒ LENGTH l3 = n` by fs[fib_heap_inv_union_def] >>
  first_x_assum(qspecl_then [`LENGTH l`,`alist_to_fmap(flat_fts [FibTree k' v' l'])`,
    `k'`,`v'`,`l'`] assume_tac) >>
  rfs[ts_to_fhts_length_thm] >>
  pop_assum mp_tac >>
  simp[Once lemma_ts_to_fhts_to_map,EL_MAP] >>
  strip_tac >>
  qspecl_then [`fh2`,`ts_to_fhts rl`,`k'`,`v'`,`l'`]
    assume_tac lemma_fib_heap_inv_union_el >>
  rfs[lemma_fhts_to_ts_absorp,ts_to_fhts_length_thm] >>
  qspecl_then [`fh1`,`fh2'`,`k`,`v`,`l`,`k'`,`v'`,`l'`] assume_tac fts_merge_trees >>
  rfs[DISJOINT_SYM] >>
  first_x_assum(qspecl_then [`LUPDATE NONE (LENGTH l) rl`,`FUNION fh1 fh2'`,
    `(fh_union (LUPDATE (FEMPTY,NONE) (LENGTH l) (ts_to_fhts rl)))`,
    `k''`,`v''`,`l''`] assume_tac) >>
  `fh2 = fh_union (ts_to_fhts rl)` by fs[fib_heap_inv_union_def] >>
  `fib_heap_inv_union (fh_union (ts_to_fhts rl)) (ts_to_fhts rl)` by fs[] >>
  `LENGTH l < LENGTH (ts_to_fhts rl)` by fs[ts_to_fhts_length_thm] >>
  drule lemma_fib_heap_inv_union_imp_lupdate_fempty >> strip_tac >> rfs[] >>
  drule_all EQ_SYM >> strip_tac >>
  qpat_x_assum `fh2' ⊌ fh_union ((ts_to_fhts rl)❲LENGTH l ↦ (FEMPTY,NONE)❳) =
    fh_union (ts_to_fhts rl)` kall_tac >>
  drule lemma_fib_heap_inv_union_imp_lupdate_fempty >> strip_tac >>
  gvs[lemma_ts_to_fhts_lupdate_none,DISJOINT_SYM] >>
  simp[FUNION_ASSOC]
QED


Definition fts_link_root_list_def:
  (fts_link_root_list (n:num) rl [] = (rl,T)) /\
  (fts_link_root_list n rl (FibTree k v l::fts) =
    if n = 0 then (rl,F) else
    let (n_rl,flag) = (fts_link_trees max_rank rl (FibTree k v l)) in
      if flag = F then (n_rl,F) else
      fts_link_root_list (n - 1) n_rl fts)
End


Theorem lemma_fts_link_root_list_length_rl:
  !n rl list.
  LENGTH rl = LENGTH (FST (fts_link_root_list n rl list))
Proof
  ho_match_mp_tac fts_link_root_list_ind >>
  rpt strip_tac
  >- simp[fts_link_root_list_def] >>
  simp[fts_link_root_list_def] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC
  >- (
    qspecl_then [`max_rank`,`rl`,`(FibTree k rl' l)`]
      mp_tac lemma_fts_link_trees_length_rl >>
    simp[]
    ) >>
  Cases_on `fts_link_root_list (n-1) n_rl list` >> simp[] >>
  IF_CASES_TAC >> gvs[] >>
  qspecl_then [`max_rank`,`rl`,`(FibTree k n' l)`]
     mp_tac lemma_fts_link_trees_length_rl >>
  simp[]
QED

Theorem lemma_fts_link_root_list_clock_cap:
  !n fts rl l_rl.
  LENGTH fts <= n /\
  fts_link_root_list (LENGTH fts) rl fts = (l_rl,T)
  ==>
  fts_link_root_list n rl fts = (l_rl,T)
Proof
  Induct >> rpt strip_tac
  >- gvs[fts_link_root_list_def] >>
  Cases_on `fts` >> fs[Once fts_link_root_list_def] >>
  Cases_on `h` >> fs[Once fts_link_root_list_def] >>
  pop_assum mp_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED


Theorem fts_link_root_list:
  !n rl fts rl' fh1 fh2.
  LENGTH rl = max_rank /\
  fib_heap_inv_weak fh1 fts /\
  fib_heap_inv_union fh2 (ts_to_fhts rl) /\
  DISJOINT (FDOM fh1) (FDOM fh2) /\
  fts_link_root_list n rl fts = (rl',T)
  ==>
  fib_heap_inv_union (FUNION fh1 fh2) (ts_to_fhts rl') /\ LENGTH rl = LENGTH rl'
Proof
  Induct >> rpt gen_tac >> disch_tac >> fs[] >> pop_assum mp_tac
  >- (
    Cases_on `fts`
    >- (
      simp[Once fts_link_root_list_def] >>
      strip_tac >> gvs[lemma_fib_heap_inv_weak_empty_fts_imp_empty_map]
      ) >>
    Cases_on `h` >> simp[Once fts_link_root_list_def]
    ) >>
  Cases_on `fts`
  >- (
    simp[fts_link_root_list_def] >>
    strip_tac >> gvs[lemma_fib_heap_inv_weak_empty_fts_imp_empty_map]
    ) >>
  Cases_on `h` >>
  rename [`FibTree k v l::t`] >>
  simp[fts_link_root_list_def] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> gvs[] >>
  disch_tac >>
  imp_res_tac lemma_fib_heap_inv_weak_split >>
  drule_all lemma_inv_weak_imp_inv >> strip_tac >>
  qspecl_then [`n_rl`,`max_rank`,`rl`,`fh1'`, `fh2`, `k`, `v`,`l`]
    mp_tac fts_link_trees2 >>
  `DISJOINT (FDOM fh1') (FDOM fh2)` by gvs[] >> simp[] >>
  strip_tac >>
  first_x_assum (qspecl_then [`n_rl`,`t`,`rl'`,`fh2'`,`FUNION fh1' fh2`] mp_tac) >>
  gvs[] >>
  metis_tac[FUNION_COMM,DISJOINT_SYM,FUNION_ASSOC,lemma_fts_link_root_list_length_rl]
QED



Definition fts_collect_array_def:
  fts_collect_array (r:num) rl acc =
    if r = 0 then
      case EL r rl of
       |SOME (FibTree k v l) => (fts_meld [FibTree k v l] acc,(LUPDATE NONE r rl))
       |NONE => (acc,rl)
    else
      case EL r rl of
       |SOME (FibTree k v l) =>
          fts_collect_array (r-1) (LUPDATE (NONE) r rl)
            (fts_meld [FibTree k v l] acc)
       |NONE => fts_collect_array (r-1) rl acc
End


Theorem lemma_fts_collect_array_length_rl:
  !r rl acc.
  LENGTH (SND (fts_collect_array r rl acc)) = LENGTH rl
Proof
  Induct >> rpt strip_tac
  >- (
    simp[Once fts_collect_array_def] >>
    CASE_TAC >> simp[] >>
    CASE_TAC >> simp[]
    ) >>
  simp[Once fts_collect_array_def] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED




Theorem lemma_hd_ts_to_fhts:
  LENGTH rl = max_rank /\
  HD rl = SOME (FibTree k v l) /\
  fib_heap_inv_union fh1 (ts_to_fhts rl)
  ==>
  ?fh2. fib_heap_inv fh2 [FibTree k v l] /\ fh2 SUBMAP fh1
Proof
  strip_tac >>
  irule fib_heap_inv_union_el_thm >>
  qexistsl [`0`,`(ts_to_fhts rl)`,`alist_to_fmap(flat_fts [FibTree k v l])`] >>
  simp[] >>
  `0 < LENGTH rl` by fs[] >>
  rewrite_tac[ts_to_fhts_def] >>
  rewrite_tac[LENGTH_GENLIST] >>
  dep_rewrite.DEP_REWRITE_TAC[HD_GENLIST_COR] >>
  simp[]
QED


Theorem lemma_suc_ts_to_fhts:
  LENGTH rl = max_rank /\
  SUC r < LENGTH rl /\
  EL (SUC r) rl = SOME (FibTree k v l) /\
  fib_heap_inv_union fh1 (ts_to_fhts rl)
  ==>
  ?fh2. fib_heap_inv fh2 [FibTree k v l] /\ fh2 SUBMAP fh1
Proof
  strip_tac >>
  irule fib_heap_inv_union_el_thm >>
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








Theorem lemma_inv_union_lupdate_none_submap:
  !x list fh1 fh2.
  x < LENGTH list /\
  fib_heap_inv_union fh1 list /\
  fib_heap_inv_union fh2 (LUPDATE (FEMPTY,NONE) x list)
  ==>
  fh2 SUBMAP fh1
Proof
  rpt strip_tac >>
  fs[fib_heap_inv_union_def] >>
  irule lemma_fh_union_lupdate_fempty_submap >>
  simp[]
QED


Theorem lemma_rl_ind_lupdate_none:
  (!x. x < max_rank /\ SUC r < x ==> EL x rl = NONE) /\
  EL (SUC r) rl = NONE
  ==>
  !x. x < max_rank /\ r < x ==> EL x rl = NONE
Proof
  rpt strip_tac >>
  res_tac >>
  Cases_on `SUC r < x` >> fs[] >>
  `x = SUC r` by fs[] >>
  simp[]
QED


Theorem lemma_rl_ind_lupdate_none2:
  (!x. x < LENGTH rl /\ SUC r < x ==> EL x rl = NONE) /\
  EL (SUC r) rl = NONE
  ==>
  !x. x < LENGTH rl /\ r < x ==> EL x rl = NONE
Proof
  rpt strip_tac >>
  res_tac >>
  Cases_on `SUC r < x` >> fs[] >>
  `x = SUC r` by fs[] >>
  simp[]
QED



Theorem lemma_rl_ind_lupdate_some:
  LENGTH rl = max_rank /\
  (!x. x < max_rank /\ SUC r < x ==> EL x rl = NONE) /\
  EL (SUC r) rl = SOME t
  ==>
  !x. x < max_rank /\ r < x ==> EL x (LUPDATE NONE (SUC r) rl) = NONE
Proof
  rpt strip_tac >>
  res_tac >>
  Cases_on `SUC r < x` >> fs[]
  >- simp[EL_LUPDATE] >>
  `x = SUC r` by fs[] >>
  simp[EL_LUPDATE]
QED





Theorem lemma_rl_all_none_0:
  LENGTH rl = max_rank /\
  (!x. x < max_rank /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = NONE
  ==>
  !x. x < LENGTH rl ==> EL x rl = NONE
Proof
  rpt strip_tac >> fs[] >>
  Cases_on `x` >> fs[]
QED



Theorem lemma_rl_all_none_lupdate_0:
  LENGTH rl = max_rank /\
  (!x. x < max_rank /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = SOME x
  ==>
  !x. x < LENGTH rl ==> EL x (LUPDATE NONE 0 rl) = NONE
Proof
  rpt strip_tac >>
  fs[EL_LUPDATE]
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
  LENGTH rl = max_rank /\
  (!x. x < LENGTH rl /\ 0 < x ==> EL x rl = NONE) /\
  HD rl = SOME t /\
  fib_heap_inv_union fh1 (ts_to_fhts rl)
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
  fs[fib_heap_inv_union_def] >>
  gvs[] >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map,MAP_APPEND] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[fh_union_append_thm] >>
  simp[Once ts_to_fhts_def,fh_union_def]
QED


Theorem lemma_fib_heap_inv_union_fmap_split:
  (!x. x < LENGTH (xs ++ [SOME t] ++ ys) /\
     r < x ==> EL x (xs ++ [SOME t] ++ ys) = NONE) /\
  fib_heap_inv_union fh (ts_to_fhts (xs ++ [SOME t] ++ ys)) /\
  LENGTH xs = r
  ==>
  fh = FUNION (fh_union (ts_to_fhts (xs))) (alist_to_fmap (flat_fts [t]))
Proof
  strip_tac >>
  drule lemma_rl_ts_to_fhts_empty >> strip_tac >>
  gvs[Excl "LENGTH", Excl "LENGTH_APPEND"] >>
  drule lemma_ts_to_fhts_split_empty >> strip_tac >>
  fs[fib_heap_inv_union_def] >>
  rewrite_tac[Once lemma_ts_to_fhts_to_map] >>
  rewrite_tac[MAP_APPEND] >>
  simp[] >>
  rewrite_tac[GSYM lemma_ts_to_fhts_to_map] >>
  simp[fh_union_append_thm,fh_union_def] >>
  drule fh_union_empty_thm >>
  simp[]
QED



Theorem lemma_fib_heap_inv_union_split_empty:
  (!x. x < LENGTH (xs ++ [y] ++ ys) /\
    LENGTH xs < x ==> EL x (xs ++ [y] ++ ys) = NONE) /\
  fib_heap_inv_union fh (ts_to_fhts xs ++ ((FEMPTY,NONE)::(ts_to_fhts ys)))
  ==>
  fh = fh_union (ts_to_fhts xs)
Proof
  strip_tac >>
  drule lemma_rl_ts_to_fhts_empty >> strip_tac >>
  drule lemma_ts_to_fhts_split_empty >> strip_tac >>
  drule fh_union_empty_thm >> strip_tac >>
  fs[fib_heap_inv_union_def] >>
  simp[fh_union_append_thm, fh_union_def]
QED






Theorem lemma_ts_to_fhts_rm:
  LENGTH rl = max_rank /\
  (!x. x < LENGTH rl /\ r < x ==> EL x rl = NONE) /\
  r < LENGTH rl /\
  EL r rl = SOME (FibTree k v l) /\
  fib_heap_inv_union fh (ts_to_fhts rl)
  ==>
  ?fh1 fh2.
    fib_heap_inv fh1 [FibTree k v l] /\
    fib_heap_inv_union fh2 (ts_to_fhts (LUPDATE NONE r rl)) /\
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
  drule lemma_fib_heap_inv_union_fmap_split >> strip_tac >>
  first_x_assum(qspec_then `fh` assume_tac) >> gvs[] >>
  qabbrev_tac `fh = FUNION (fh_union (ts_to_fhts xs))
    (alist_to_fmap (flat_fts [FibTree k v l]))` >>
  qpat_x_assum `fib_heap_inv_union fh
    (ts_to_fhts (xs ++ [SOME (FibTree k v l)] ++ ys))` mp_tac >>
  simp[Once lemma_ts_to_fhts_to_map] >>
  simp[GSYM lemma_ts_to_fhts_to_map] >>
  rewrite_tac[GSYM APPEND_ASSOC,Once (GSYM lemma_cons_eq_append)] >>
  strip_tac >>
  drule_all fib_heap_inv_union_rm_thm >> strip_tac >>
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
  drule_all lemma_fib_heap_inv_union_split_empty >> strip_tac >>
  simp[FUNION_COMM]
QED







Theorem lemma_fib_heap_inv_union_imp_hd_fib_heap_inv:
  LENGTH rl = max_rank /\
  HD (ts_to_fhts rl) = (fh1, SOME (FibTree k v l)) /\
  fib_heap_inv_union fh2 (ts_to_fhts rl)
  ==>
  fib_heap_inv fh1 [FibTree k v l]
Proof
  strip_tac >>
  pop_assum mp_tac >>
  simp[fib_heap_inv_union_def] >>
  simp[Once lemma_ts_to_fhts_to_map] >>
  simp[EVERY_MAP] >>
  Cases_on `rl` >> fs[] >>
  pop_assum mp_tac >>
  simp[Once lemma_ts_to_fhts_to_map]
QED



Theorem fts_collect_array:
  !fts rl' r rl fh2 fh1 acc.
    fib_heap_inv fh1 acc /\
    fib_heap_inv_union fh2 (ts_to_fhts rl) /\
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    LENGTH rl = max_rank /\
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
      imp_res_tac lemma_rl_all_none_0 >> rfs[] >>
      `∀x. x < LENGTH rl ⇒ rl❲x❳ = NONE` by simp[] >>
      imp_res_tac lemma_rl_all_none_imp_ts_to_fhts_fempty >>
      drule_all fh_union_empty_thm >> strip_tac >>
      fs[fib_heap_inv_union_def]
      ) >>
    CASE_TAC >> strip_tac >>
    rename [`HD rl = SOME (FibTree k v l)`] >>
    fs[GSYM max_rank_def,Excl "max_rank_def"] >>
    drule_all lemma_rl_none_except_hd_eq_fh >> strip_tac >>
    qspecl_then [`fh2`,`[FibTree k v l]`,`fh1`,`acc`,`fts`]
      assume_tac fts_meld >> gvs[] >>
    rfs[DISJOINT_SYM] >>
    fs[GSYM max_rank_def,Excl "max_rank_def"] >>
    drule_all lemma_fib_heap_inv_union_imp_hd_fib_heap_inv >> strip_tac >>
    fs[] >>
    qspecl_then [`fh2`,`fh1`,`(fts_meld [FibTree k v l] acc)`]
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
    metis_tac[lemma_rl_ind_lupdate_none,max_rank_def]
    ) >>
  CASE_TAC >> strip_tac >>
  rename [`EL (SUC r) rl =  SOME (FibTree k v l)`] >>
  fs[GSYM max_rank_def,Excl "max_rank_def"] >>
  drule_all lemma_ts_to_fhts_rm >> strip_tac >>
  qspecl_then [`fh1'`,`[FibTree k v l]`,`fh1`,`acc`,
    `fts_meld [FibTree k v l] acc`] assume_tac fts_meld >>
  gvs[] >>
  first_x_assum(qspecl_then [`LUPDATE NONE (SUC r) rl`,`fh2'`,
    `FUNION fh1 fh1'`,`fts_meld [FibTree k v l] acc`] assume_tac) >>
  rfs[DISJOINT_SYM,fib_heap_inv_comm_thm] >>
  simp[FUNION_ASSOC] >>
  first_x_assum irule >>
  simp[lemma_rl_ind_lupdate_some]
QED






Definition fts_reb_def:
  fts_reb rl fts =
    let (l_rl,flag) = fts_link_root_list (LENGTH fts) rl fts in
    let (fts',e_rl) = fts_collect_array (LENGTH l_rl - 1) l_rl [] in
      (fts',e_rl,flag)
End





Theorem lemma_fib_heap_inv_union_replicate_imp_fempty:
  fib_heap_inv_union fh2 (ts_to_fhts emp_rl)
  ==>
  fh2 = FEMPTY
Proof
  simp[emp_rl_def,lemma_ts_to_fhts_to_map] >>
  strip_tac >>
  fs[fib_heap_inv_union_def] >>
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
  !fh1 fts fts' e_rl.
    fib_heap_inv_weak fh1 fts /\
    fts_reb emp_rl fts = (fts',e_rl,T)
    ==>
    fib_heap_inv fh1 fts' /\ e_rl = emp_rl
Proof
  rpt gen_tac >> disch_tac >> fs[] >>
  pop_assum mp_tac >>
  simp[fts_reb_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  qspecl_then [`LENGTH fts`,`emp_rl`,`fts`,`l_rl`,`fh1`,`FEMPTY`]
    mp_tac fts_link_root_list >> simp[] >>
  `fib_heap_inv_union FEMPTY (ts_to_fhts emp_rl)` by
    simp[emp_rl_def,lemma_ts_to_fhts_to_map,fib_heap_inv_union_empty_thm] >>
  simp[Once emp_rl_def,LENGTH_REPLICATE] >>
  strip_tac >>
  qspecl_then [`fts'`,`e_rl`,`(LENGTH l_rl - 1)`,`l_rl`,`fh1`,`FEMPTY`,`[]`]
    mp_tac fts_collect_array >>
  simp[fib_heap_inv_empty_thm] >>
  strip_tac >>
  imp_res_tac lemma_e_rl_eq_replicate >>
  gvs[emp_rl_def]
QED




(*-------------------------------------------------------------
  Extract Minimum
--------------------------------------------------------------*)



Definition fts_extract_min_def:
  fts_extract_min fts =
    let (min,fts) = fts_rm_min fts in
    let (fts',e_rl,flag) = fts_reb emp_rl fts in
      (min,fts',e_rl,flag)
End




Theorem lemma_fib_heap_inv_union_emp_rl:
  fib_heap_inv_union FEMPTY (ts_to_fhts emp_rl)
Proof
  simp[lemma_ts_to_fhts_to_map,emp_rl_def] >>
  simp[fib_heap_inv_union_empty_thm]
QED


Theorem fts_extract_min:
  !fh fts min fts'.
  fib_heap_inv fh fts /\
  fts_extract_min fts = (min,fts',emp_rl,T)
  ==>
  fib_heap_inv (fh \\ min) fts' /\
  min = head_key fts
Proof
  rpt gen_tac >> disch_tac >>
  pop_assum mp_tac >> simp[fts_extract_min_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  strip_tac >> gvs[] >>
  drule_all fts_rm_min >> strip_tac >>
  assume_tac lemma_fib_heap_inv_union_emp_rl >>
  drule_all fts_reb >> fs[]
QED


