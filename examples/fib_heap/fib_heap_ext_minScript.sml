(*
  Memory Level Implementation and Verification for fts_ext_min
*)

Theory fib_heap_ext_min
Ancestors
  misc words arithmetic list alist set_sep pair finite_map combin panSem rich_list
  fibonacci_heap pred_set fib_heap_meld
Libs
  wordsLib helperLib


(*-------------------------------------------------------------
  Refinements for the memory implementation of fts_rm_min
---------------------------------------------------------------*)



Definition fib_heap_pop_def:
  fib_heap_pop (a:'a word, m:'a word -> 'a word_lab,dm: 'a word set)
  =
  if a = 0w then (0w,a,m,T) else
  let (n_a,c) = read_mem (a + next_off) m dm T in
  if n_a = a then (a,0w,m,T) else
  let (l_a,c) = read_mem (a + before_off) m dm c in

  let (m,c) = write_mem (n_a + before_off) l_a m dm c in
  let (m,c) = write_mem (l_a + next_off) n_a m dm c in

  let (m,c) = write_mem (a + next_off) a m dm c in
  let (m,c) = write_mem (a + before_off) a m dm c in
    (a,n_a,m,c)
End



Theorem lemma_fdiff_id_eq_empty:
  FDIFF fh (FDOM fh) = FEMPTY
Proof
  simp[GSYM fmap_EQ_THM] >>
  simp[FDIFF_def] >>
  simp[DRESTRICT_DEF]
QED


Theorem lemma_fdiff_disjoint:
  DISJOINT (FDOM fh1) (FDOM fh2) ==> FDIFF fh2 (FDOM fh1) = fh2
Proof
  strip_tac >>
  simp[FDIFF_def] >>
  simp[disjoint_drestrict]
QED


Theorem fib_heap_pop_mem_thm:
  !frame p fts m dm top a' m' c.
    (fts_mem (ann_fts p fts) * frame) (fun2set (m,dm)) /\
    fib_heap_pop (head_key fts,m,dm) = (top,a',m',c)
    ==>
    (empty_node2 (head_key fts) p (HD fts) *
     fts_mem (ann_fts p (TL fts))  * frame)
      (fun2set (m',dm)) /\
    a' = head_key (TL fts) /\
    head_key fts = top /\
    c
Proof
  rpt gen_tac >> disch_tac >> fs[] >> pop_assum mp_tac >>
  simp[fib_heap_pop_def,read_mem_def,write_mem_def,next_off_def,
       before_off_def] >>
  Cases_on `fts`
  >- (
    strip_tac >>
    gvs[head_key_def,head_key_t_def,empty_node2_def,SEP_CLAUSES,STAR_ASSOC]
    ) >>
  Cases_on `h` >>
  rename [`head_key (FibTree k v l::t)`] >>
  Cases_on `t`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node2_def]
    ) >>
  Cases_on `h` >>
  rename [`(fts_mem (ann_fts p (FibTree k v l::FibTree k' v' l'::t')) * frame)
    (fun2set (m,dm))`] >>
  Cases_on `t'` using SNOC_CASES
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> simp[] >>
    `k <> k'` by SEP_NEQ_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node2_def] >>
    SEP_W_TAC
    ) >>
  Cases_on `x` >>
  fs[SNOC_APPEND,REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm,
     ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  SEP_R_TAC >> simp[] >>
  `k <> k'` by SEP_NEQ_TAC >> simp[] >>
  SEP_R_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node2_def] >>
  SEP_W_TAC >>
  fs[head_key_t_pull_last_thm]
QED





Definition fib_heap_set_parent_def:
  fib_heap_set_parent (n:num) (a,v,m,dm)
  =
  if a = 0w then (a,m,T) else
  if n = 0 then
  let (m,c) = write_mem (a + parent_off) v m dm T in
      (a,m,c)
  else
    let (m,c) = write_mem (a + parent_off) v m dm T in
    let (n_a,c) = read_mem (a + next_off) m dm c in
    let (_,m,c') = fib_heap_set_parent (n - 1) (n_a,v,m,dm) in
      (a,m,c /\ c')
End


Theorem fib_heap_set_parent:
  !n np p xs ys m dm frame a m' c.
  n = LENGTH ys /\
  (fts_mem (ann_fts_seg np (head_key_t (head_key xs) ys)
    (last_key_t (last_key xs) ys)
    (head_key_t (head_key xs) (TL xs ++ ys)) xs) *
   fts_mem (ann_fts_seg p (head_key_t (head_key ys) xs)
    (last_key_t (last_key ys) xs)
    (head_key_t (head_key_t (head_key ys) xs) (TL ys)) ys) *
   frame) (fun2set(m,dm)) /\
  fib_heap_set_parent n (head_key ys,np,m,dm) =
    (a,m',c)
  ==>
  (fts_mem (ann_fts np (xs ++ ys)) * frame) (fun2set(m',dm)) /\ head_key ys = a /\
  c
Proof
  Induct
  >- (
    rpt gen_tac  >> disch_tac >> fs[] >>
    pop_assum mp_tac >>
    simp[Once fib_heap_set_parent_def, head_key_def,head_key_t_def,
         read_mem_def,write_mem_def,parent_off_def] >>
    strip_tac >> gvs[] >>
    Cases_on `xs`
    >- fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
          SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
          new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    Cases_on `h` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    ) >>
  rpt gen_tac  >> disch_tac >> fs[] >>
  pop_assum mp_tac >>
  simp[Once fib_heap_set_parent_def, head_key_def,head_key_t_def,
       read_mem_def,write_mem_def,next_off_def,parent_off_def] >>
  Cases_on `ys` >> fs[] >>
  Cases_on `h` >>
  rename [`FibTree k v l::t`] >>
  simp[head_key_t_def] >>
  `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,
     ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[] >>
  pairarg_tac >> simp[] >>
  pop_assum mp_tac >>
  Cases_on `t` >> simp[]
  >- (
    simp[Once fib_heap_set_parent_def] >>
    qpat_x_assum `n = LENGTH []` kall_tac >>
    pop_assum mp_tac >> pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >> strip_tac >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,
       ann_fts_seg_append_thm,fts_mem_append_thm,head_key_t_append_thm] >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    Cases_on `xs`
    >- (
      simp[head_key_t_def,write_mem_def,parent_off_def] >>
      strip_tac >> gvs[] >>
      SEP_R_TAC >>
      strip_tac >> gvs[] >>
      fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
         SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
         new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
      ) >>
    Cases_on `h` >>
    rename [`head_key_t k (FibTree k' v' l'::t')`] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    `k' <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,
      ann_fts_def, ann_fts_seg_def, ones_def, STAR_ASSOC] >>
    simp[write_mem_def,parent_off_def] >>
    SEP_R_TAC >>
    strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    simp[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
         fts_mem_def, SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
         new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,
         fts_mem_append_thm,ann_fts_seg_append_thm,REVERSE_APPEND] >>
    SEP_W_TAC >> fs[lemma_head_keys_eq_last_key_t]
    ) >>
  strip_tac >>
  first_x_assum (qspecl_then [`np`,`p`,`xs ++ [FibTree k v l]`,`(h::t')`,
    `m (| k + 6w * bytes_in_word |-> Word np |)`,`dm`,`frame`,
    `_0`,`m''`] mp_tac) >> simp[] >>
  Cases_on `h` >>
  rename [`head_key (FibTree k' v' l'::t')`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,
     ann_fts_seg_append_thm,fts_mem_append_thm,head_key_t_append_thm] >>
  Cases_on `xs`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,
       ann_fts_seg_append_thm,fts_mem_append_thm,head_key_t_append_thm] >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >> fs[lemma_head_keys_eq_last_key_t] >>
    Cases_on `c''`
    >- (
      strip_tac >> gvs[] >>
      strip_tac >> gvs[]
      ) >>
    simp[]
    ) >>
  Cases_on `h` >>
  rename [`FibTree k'' b'' l''::t'' ++ FibTree a v l::FibTree k' v' l'::t'`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,
     ann_fts_seg_append_thm,fts_mem_append_thm,head_key_t_append_thm] >>
  SEP_W_TAC >> simp[] >>
  SEP_R_TAC >>
  fs[lemma_head_keys_eq_last_key_t,REVERSE_APPEND,head_key_t_def] >>
  pop_assum mp_tac >>
  once_rewrite_tac[lemma_cons_eq_append] >>
  simp[head_key_t_append_thm] >>
  strip_tac >>
  Cases_on `c''` >> simp[]
  >- (
    strip_tac >> strip_tac >> gvs[] >>
    fs[last_key_t_pull_thm,head_key_def,head_key_t_def]
    ) >>
  simp[]
QED

(*--------------------------------------------------------------
  fib_heap_rm_min with memory refinements
----------------------------------------------------------------*)

Definition fib_heap_rm_min_def:
  fib_heap_rm_min (a:'a word,m:'a word -> 'a word_lab,dm: 'a word set)
  =
  if a = 0w then (a,a,m,T) else
  let (min,n_a,m,c) = fib_heap_pop (a,m,dm) in
  let c' = in_mem (a + child_off) dm in
  let c = (c /\ c') in
  let (child_a,c) = read_mem (a + child_off) m dm c in
  let (rank_a,c) = read_mem (a + rank_off) m dm c in
  let (child_a,m,c') =
     if child_a = 0w then (0w,m,T) else
     fib_heap_set_parent (w2n rank_a) (child_a,0w,m,dm) in
  let (new_a,m,c'') = fib_heap_meld (child_a,n_a,m,dm) in
  let (m,c) = write_mem (a + rank_off) 0w m dm (c /\ c' /\ c'') in
  let (m,c) = write_mem (a + child_off) 0w m dm c in
  let (m,c) = write_mem (a + mark_off) 0w m dm c in
    (min,new_a,m,c)
End


Theorem lemma_fdom_disjoint_delete:
  DISJOINT (FDOM fh2) (FDOM (FDIFF fh1 (FDOM fh2))) ==>
  DISJOINT (FDOM fh2 DELETE a) (FDOM (FDIFF fh1 (FDOM fh2)))
Proof
  strip_tac >>
  metis_tac[DISJOINT_SUBSET',DELETE_SUBSET]
QED

Theorem lemma_funion_domsub_fdiff:
  fh1 SUBMAP fh2 /\ a IN FDOM fh1
  ==>
  FUNION (fh1 \\ a) (FDIFF fh2 (FDOM fh1)) = fh2 \\ a
Proof
  strip_tac >>
  simp[fmap_eq_flookup] >>
  strip_tac >>
  Cases_on `x = a`
  >- simp[FLOOKUP_SIMP] >>
  simp[FLOOKUP_SIMP,DOMSUB_FLOOKUP_THM] >>
  CASE_TAC >> simp[FLOOKUP_DEF] >>
  fs[SUBMAP_DEF]
QED



Theorem fib_heap_rm_min_mem:
  !frame fts fts' m dm min.
  fts_rm_min fts = (min,fts') /\
  (fts_mem (ann_fts 0w fts) * frame) (fun2set(m,dm)) /\
  max_rank < dimword (:'a) ==>
  ?a' m' v e.
  fib_heap_rm_min (head_key fts,m,dm) = (min,(a':'a word),m',T) /\
  (fts_mem (ann_fts 0w fts') * empty_node min (v,e) * frame)
    (fun2set(m',dm)) /\
  head_key fts' = a'
Proof
  simp[fib_heap_rm_min_def,read_mem_def,write_mem_def,child_off_def] >>
  rpt strip_tac >>
  Cases_on `fts`
  >- (
    fs[head_key_t_def,head_key_def, fts_rm_min_def] >>
    simp[empty_node_def,SEP_CLAUSES]
    ) >>
  Cases_on `h`>>
  rename[`FibTree k v l::t`] >>
  simp[head_key_t_def,head_key_def] >>
  `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,
     ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  simp[rank_off_def,mark_off_def,read_mem_def,write_mem_def,
       head_key_def,head_key_t_def] >>
  pairarg_tac >> simp[] >>
  qspecl_then [`frame`,`0w`,`(FibTree k v l::t)`,`m`,`dm`,`min'`,`n_a`,`m'`]
    mp_tac fib_heap_pop_mem_thm >> simp[head_key_def,head_key_t_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(fts_mem (ann_fts 0w (FibTree k v l::t)) * frame)
    (fun2set (m,dm))` kall_tac >>
  gvs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
      fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
      new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node2_def] >>
  SEP_R_TAC >>
  Cases_on `l`
  >- (
    gvs[head_key_t_def,head_key_def] >>
    fs[fts_rm_min_def] >>
    qspecl_then [`ones k [v.value;FST v.edges; b2w T; b2w v.mark;k;k;
      0w;0w;0w] * edges_ones (FST v.edges) (SND v.edges) * frame`,
       `0w`,`[]`,`t`,`fts'`,`m'`,`dm`] mp_tac fib_heap_meld_mem_thm >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
       fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    gvs[AC STAR_ASSOC STAR_COMM] >>
    fs[STAR_ASSOC] >>
    strip_tac >> gvs[] >>
    qexistsl [`v.value`,`v.edges`] >>
    simp[empty_node_def,ones_def,SEP_CLAUSES,STAR_ASSOC] >>
    SEP_W_TAC >>
    fs[b2w_def] >>
    fs[AC STAR_ASSOC STAR_COMM]
    ) >>
  Cases_on `h` >>
  rename [`FibTree k' v' l'::t'`] >>
  fs[head_key_t_eq_head_key_thm,last_key_t_eq_last_key_thm] >>
  simp[head_key_t_def,head_key_def] >>
  `k' <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,
     ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`SUC (LENGTH t')`,`0w`,`k`,`[]`,`(FibTree k' v' l'::t')`,
    `m'`,`dm`,`ones k [v.value;FST v.edges; b2w T; b2w v.mark;k;k;
     0w;k';(n2w (SUC (LENGTH t')))] * fts_mem (ann_fts 0w t) *
     edges_ones (FST v.edges) (SND v.edges) * frame`,
    `child_a`,`m''`,`c'`] mp_tac fib_heap_set_parent >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  strip_tac >> gvs[] >>
  fs[fts_rm_min_def] >>
  qspecl_then [`ones k [v.value;FST v.edges;b2w T;b2w v.mark;k;k;0w;child_a;
    n2w (SUC (LENGTH t'))] * edges_ones (FST v.edges) (SND v.edges) * frame`,
    `0w`,`(FibTree child_a v' l'::t')`,`t`,`fts'`,`m''`,`dm`]
     mp_tac fib_heap_meld_mem_thm >>
  simp[] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  gvs[] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  strip_tac >> simp[] >>
  qexistsl [`v.value`,`v.edges`] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node_def] >>
  SEP_W_TAC >> fs[b2w_def] >>
  fs[AC STAR_ASSOC STAR_COMM]
QED

Definition fib_heap_merge_trees_def:
  fib_heap_merge_trees (a1,a2,m,dm) =
    if a1 = 0w then (a2,m,F) else
    if a2 = 0w then (a1,m,F) else
    let (v_a1,c) = read_mem a1 m dm T in
    let (v_a2,c) = read_mem a2 m dm c in
    if v_a1 <=+ v_a2 then
      let (child,c) = read_mem (a1 + child_off) m dm c in
      let (rank,c) = read_mem (a1 + rank_off) m dm c in
      let (m,c) = write_mem (a2 + parent_off) a1 m dm c in
      let (new_child,m,c') = fib_heap_meld (child,a2,m,dm) in
      let c = (c /\ c') in
      let (m,c) = write_mem (a1 + child_off) new_child m dm c in
      let (m,c) = write_mem (a1 + rank_off) (rank + 1w) m dm c in
        (a1,m,c)
    else
      let (child,c) = read_mem (a2 + child_off) m dm c in
      let (rank,c) = read_mem (a2 + rank_off) m dm c in
      let (m,c) = write_mem (a1 + parent_off) a2 m dm c in
      let (new_child,m,c') = fib_heap_meld (child,a1,m,dm) in
      let c = (c /\ c') in
      let (m,c) = write_mem (a2 + child_off) new_child m dm c in
      let (m,c) = write_mem (a2 + rank_off) (rank + 1w) m dm c in
        (a2,m,c)
End


Theorem fib_heap_merge_trees_mem_thm:
  !frame k v l k' v' l' t m dm.
  fts_merge_trees (FibTree k v l) (FibTree k' v' l') = t /\
  (fts_mem (ann_fts 0w [FibTree k v l]) * fts_mem (ann_fts 0w [FibTree k' v' l'])
    * frame) (fun2set(m,dm)) /\
  LENGTH l = LENGTH l' /\
  LENGTH l < (max_rank - 1) /\
  LENGTH l' < (max_rank - 1)
  ==>
  ?m'.
  fib_heap_merge_trees ((k:'a word),k',m,dm) = (head_key [t],m',T) /\
  (fts_mem (ann_fts 0w [t]) * frame) (fun2set(m',dm))
Proof
  rpt gen_tac >> disch_tac >> fs[] >>
  simp[fib_heap_merge_trees_def,fts_merge_trees_def,child_off_def,rank_off_def,
       parent_off_def,read_mem_def,write_mem_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  fs[fts_merge_trees_def] >>
  SEP_R_TAC >> simp[] >>
  IF_CASES_TAC >> fs[]
  >- (
    qabbrev_tac `ts = fts_meld l [FibTree k' v' l']` >>
    qspecl_then [`frame * ones k [v.value;FST v.edges;b2w T; b2w v.mark;
      k;k;0w;head_key l; n2w (LENGTH l)] * edges_ones (FST v.edges) (SND v.edges)`,
      `k`,`l`,`[FibTree k' v' l']`,`ts`,`m⦇k' + 6w * bytes_in_word ↦ Word k⦈`,`dm`]
      mp_tac fib_heap_meld_mem_thm >>
    simp[] >>
    fs[GSYM head_key_def,GSYM last_key_def] >>
    fs[GSYM lemma_ann_fts_arb_list] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
       fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_W_TAC >> simp[] >>
    fs[GSYM head_key_def,GSYM last_key_def] >>
    fs[GSYM lemma_ann_fts_arb_list] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    strip_tac >> gvs[STAR_ASSOC] >>
    simp[head_key_def,head_key_t_def] >>
    SEP_W_TAC >> simp[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
       fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    pop_assum mp_tac >>
    simp[GSYM lemma_ann_fts_arb_list,GSYM head_key_def,GSYM last_key_def] >>
    strip_tac >>
    unabbrev_all_tac >>
    `LENGTH l' + 1 = 1 + LENGTH l'` by simp[] >>
    simp[lemma_fts_meld_length,n2w_SUC,GSYM SUC_ONE_ADD] >>
    pop_assum kall_tac >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    fs[AC STAR_ASSOC STAR_COMM]
    ) >>
  qabbrev_tac `ts = fts_meld l' [FibTree k v l]` >>
  qspecl_then [`frame * ones k' [v'.value;FST v'.edges;b2w T; b2w v'.mark;k';k';
    0w;head_key l'; n2w (LENGTH l')] * edges_ones (FST v'.edges) (SND v'.edges)`,
    `k'`,`l'`,`[FibTree k v l]`,`ts`,`m⦇k + 6w * bytes_in_word ↦ Word k'⦈`,`dm`]
    mp_tac fib_heap_meld_mem_thm >> simp[] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[GSYM head_key_def,GSYM last_key_def] >>
  fs[GSYM lemma_ann_fts_arb_list] >>
  SEP_W_TAC >> simp[] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  strip_tac >> fs[STAR_ASSOC] >>
  unabbrev_all_tac >> gvs[head_key_def,head_key_t_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  SEP_W_TAC >> simp[] >>
  pop_assum mp_tac >>
  simp[GSYM lemma_ann_fts_arb_list,GSYM head_key_def,GSYM last_key_def] >>
  strip_tac >>
  `LENGTH l' + 1 = 1 + LENGTH l'` by simp[] >>
  simp[lemma_fts_meld_length,n2w_SUC,GSYM SUC_ONE_ADD] >>
  pop_assum kall_tac >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  fs[AC STAR_ASSOC STAR_COMM]
QED



Definition fib_heap_link_trees_def:
  fib_heap_link_trees (n: num) (arr,a,m,dm,c) =
    if n = 0 then (m,F) else
    if a = 0w then (m,c) else
    let (rank,c) = read_mem (a + rank_off) m dm T in
    if max_rank <= (w2n rank) then (m,F) else
    let (arr_t,c) = read_mem (arr + rank) m dm c in
    if arr_t = 0w then
       let (m,c) = write_mem (arr + rank) a m dm c in
        (m,c)
    else
       if (max_rank - 1) <= (w2n rank) then (m,F) else
       let (new_t,m,c') = fib_heap_merge_trees (a,arr_t,m,dm) in
       let c = (c /\ c') in
       let (m,c) = write_mem (arr + rank) 0w m dm c in
         fib_heap_link_trees (n - 1) (arr,new_t,m,dm,c)
End


Definition reb_array_mem_def:
  (reb_array_mem a off [] = emp) /\
  reb_array_mem a off (op::rest) =
    (case op of
      |NONE                => one(a + off, Word 0w)
      |SOME(FibTree k v l) => one(a + off, Word k) *
        fts_mem(ann_fts 0w [FibTree k v l])) *
    reb_array_mem a (off + 1w) rest
End

Theorem reb_array_mem_append_thm:
  !xs ys off a.
  reb_array_mem a off (xs ++ ys) =
    reb_array_mem a off xs * reb_array_mem a (off + n2w (LENGTH xs)) ys
Proof
  Induct >> simp[reb_array_mem_def,SEP_CLAUSES] >>
  rpt strip_tac >>
  Cases_on `h` >> simp[]
  >- simp[n2w_SUC,STAR_ASSOC] >>
  CASE_TAC >>
  simp[n2w_SUC,STAR_ASSOC]
QED


Theorem lemma_reb_array_mem_el:
  !r a off rl frame m dm.
  (reb_array_mem a off rl * frame) (fun2set(m,dm)) /\
  (r < LENGTH rl)
  ==>
  ?xs y ys.
  (reb_array_mem a off (xs ++ (y::ys)) * frame) (fun2set(m,dm)) /\
  r = LENGTH xs
Proof
  rpt strip_tac >>
  drule LESS_LENGTH >> strip_tac >> gvs[] >>
  first_x_assum $ irule_at $ Pos hd >>
  simp[]
QED


Theorem lemma_fib_heap_link_trees_inv_ih:
  (∀x k v l.
    x < max_rank ∧
    (ys1 ++ [SOME (FibTree k' v' l')] ++ ys2)❲x❳ = SOME (FibTree k v l)
    ⇒
    LENGTH l = x)
  ==>
  (!x k v l.
    x < max_rank /\
    EL x (ys1 ++ [NONE] ++ ys2) = SOME (FibTree k v l)
    ==>
    LENGTH l = x)
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  simp[EL_APPEND] >>
  IF_CASES_TAC
  >- (
    IF_CASES_TAC
    >- (strip_tac >> res_tac >> fs[EL_APPEND]) >>
    fs[NOT_LESS] >>
    `LENGTH ys1 = x` by simp[] >>
    gvs[]
    ) >>
  strip_tac >> res_tac >> fs[EL_APPEND]
QED



Theorem fib_heap_link_trees_mem_thm:
  !n frame k v l arr rl rl' m dm.
  fts_link_trees n rl (FibTree k v l) = (rl',T) /\
  (fts_mem (ann_fts 0w [FibTree k v l]) *
   reb_array_mem arr 0w rl *
   frame) (fun2set(m,dm)) /\
  LENGTH rl = max_rank /\
  max_rank < dimword (:'a) /\
  (!x k v l. x < LENGTH rl /\ EL x rl = SOME(FibTree k v l) ==> LENGTH l = x)
  ==>
  ?m'.
  fib_heap_link_trees n (arr,(k:'a word),m,dm,T) = (m',T) /\
  (reb_array_mem arr 0w rl' * frame) (fun2set(m',dm))
Proof
  Induct >> rpt gen_tac >> disch_tac >> fs[] >> pop_assum mp_tac
  >- (fs[Once fib_heap_link_trees_def,Once fts_link_trees_def]) >>
  qpat_x_assum `fts_link_trees (SUC n) rl (FibTree k v l) = (rl',T)` mp_tac >>
  simp[Once fib_heap_link_trees_def,Once fts_link_trees_def] >>
  IF_CASES_TAC >> simp[] >>
  CASE_TAC >> CASE_TAC
  >- (
    strip_tac >> strip_tac >>
    `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
      ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
    simp[read_mem_def,write_mem_def,rank_off_def] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
       fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    qspecl_then [`rl`,`LENGTH l`] assume_tac LESS_LENGTH >> gvs[] >>
    fs[reb_array_mem_def,reb_array_mem_append_thm] >>
    Cases_on `y`
    >- (
      fs[] >>
      SEP_R_TAC >> simp[] >>
      simp[LUPDATE_APPEND,LUPDATE_DEF] >>
      simp[reb_array_mem_append_thm,reb_array_mem_def] >>
      SEP_W_TAC >>
      fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
         fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
         new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
      fs[AC STAR_ASSOC STAR_COMM]
      ) >>
    Cases_on `x` >> fs[] >>
    fs[EL_APPEND]
    )
  >- CASE_TAC
  >- (
    strip_tac >> strip_tac >>
    `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
      ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
    simp[write_mem_def,read_mem_def,rank_off_def] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
       fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
       new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    qspecl_then [`rl`,`LENGTH l`] assume_tac LESS_LENGTH >> gvs[] >>
    fs[reb_array_mem_def,reb_array_mem_append_thm] >>
    Cases_on `y`
    >- (
      fs[] >>
      SEP_R_TAC >> simp[] >>
      simp[LUPDATE_APPEND,LUPDATE_DEF] >>
      simp[reb_array_mem_append_thm,reb_array_mem_def] >>
      SEP_W_TAC >>
      fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
         fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
         new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
      fs[AC STAR_ASSOC STAR_COMM]
      ) >>
    Cases_on `x` >> fs[] >>
    fs[EL_APPEND]
    ) >>
  CASE_TAC >>
  rename [`EL (LENGTH l) rl = SOME (FibTree k' v' l')`] >>
  strip_tac >> strip_tac >>
  qspecl_then [`rl`,`LENGTH l`] assume_tac LESS_LENGTH >> gvs[] >>
  `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
    ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
  simp[read_mem_def,write_mem_def,rank_off_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  SEP_R_TAC >> simp[] >>
  fs[reb_array_mem_def,reb_array_mem_append_thm] >>
  Cases_on `y` >> fs[]
  >- fs[EL_APPEND] >>
  Cases_on `x` >>
  rename [`FibTree k'' v'' l''`] >>
  qpat_x_assum `(ys1 ++ [SOME (FibTree k'' v'' l'')] ++ ys2)❲LENGTH l❳ =
    SOME (FibTree k' v' l')` mp_tac >> simp[EL_APPEND] >>
  strip_tac >> gvs[] >>
  SEP_R_TAC >> simp[] >>
  `k' <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
    ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
  simp[] >>
  Cases_on `fts_merge_trees (FibTree k v l) (FibTree k' v' l')` >>
  rename [`fts_merge_trees (FibTree k v l) (FibTree k' v' l') =
    FibTree k'' v'' l''`] >>
  qpat_x_assum `fts_link_trees n
   (ys1 ++ [SOME (FibTree k' v' l')] ++ ys2)❲LENGTH l ↦ NONE❳
   (FibTree k'' v'' l'') = (rl',T)` mp_tac >>
  simp[LUPDATE_APPEND,LUPDATE_DEF] >>
  qspecl_then [`reb_array_mem arr 0w ys1 * one(arr + n2w (LENGTH l),Word k') *
    reb_array_mem arr (n2w (LENGTH l +1)) ys2 * frame`,`k`,`v`,`l`,`k'`,`v'`,
    `l'`,`FibTree k'' v'' l''`,`m`,`dm`] mp_tac fib_heap_merge_trees_mem_thm >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  first_assum (qspecl_then [`LENGTH l`,`k'`,`v'`,`l'`] mp_tac) >>
  rewrite_tac[EL_APPEND] >>
  strip_tac >> rfs[] >>
  strip_tac >> strip_tac >>
  first_x_assum(qspecl_then [`frame`,`k''`,`v''`,`l''`,`arr`,`ys1 ++ [NONE] ++ ys2`,
    `rl'`,`m'(|arr + n2w (LENGTH l) |-> Word 0w|)`,`dm`] mp_tac) >>
  fs[reb_array_mem_def,reb_array_mem_append_thm,STAR_ASSOC,SEP_CLAUSES] >>
  SEP_W_TAC >> simp[] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  metis_tac[lemma_fib_heap_link_trees_inv_ih,max_rank_def]
QED



Definition fib_heap_link_root_list_def:
  fib_heap_link_root_list (n:num) (arr,a,m,dm,c)
  =
  if a = 0w then (m,T) else
  if n = 0 then (m,F) else
  let (top,a',m,c) = fib_heap_pop (a,m,dm) in
  let (m,c) = fib_heap_link_trees max_rank (arr,top,m,dm,c) in
    fib_heap_link_root_list (n - 1) (arr,a',m,dm,c)
End


Theorem lemma_rl_rm_imp_length_inv:
  !rl l.
  (∀x k' v' l'.
    x < max_rank ∧ rl❲x❳ = SOME (FibTree k' v' l') ⇒ LENGTH l' = x)
  ==>
  (∀x k' v' l'.
    x < max_rank ∧ rl❲LENGTH l ↦ NONE❳❲x❳ = SOME (FibTree k' v' l') ⇒
    LENGTH l' = x)
Proof
  rpt strip_tac >>
  fs[EL_LUPDATE]
QED


Theorem lemma_fib_heap_link_root_list_inv_ih:
  !n rl k v l.
    LENGTH rl = max_rank /\
    (∀x k' v' l'. x < max_rank ∧ rl❲x❳ = SOME (FibTree k' v' l')
      ⇒ LENGTH l' = x)
  ==>
    (∀x k' v' l'.
      x < max_rank ∧
      (FST (fts_link_trees n rl (FibTree k v l)))❲x❳ =
        SOME (FibTree k' v' l')
        ⇒ LENGTH l' = x)
Proof
  Induct >> rpt strip_tac >> pop_assum mp_tac >> simp[Once fts_link_trees_def] >>
  IF_CASES_TAC >> simp[] >>
  CASE_TAC >> CASE_TAC >> simp[]
  >- (
    strip_tac >>
    Cases_on `x = LENGTH l` >> gvs[EL_LUPDATE]
    )
  >- (CASE_TAC >> simp[])
  >- (
    strip_tac >>
    Cases_on `x = LENGTH l` >> gvs[EL_LUPDATE]
    ) >>
  CASE_TAC >> simp[] >>
  rename [`EL (LENGTH l) rl =  SOME (FibTree k2 v2 l2)`] >>
  Cases_on `fts_merge_trees (FibTree k v l) (FibTree k2 v2 l2)` >>
  rename [`fts_merge_trees (FibTree k v l) (FibTree k2 v2 l2) = FibTree k3 v3 l3`] >>
  Cases_on `fts_link_trees n rl❲LENGTH l ↦ NONE❳ (FibTree k3 v3 l3)` >>
  gvs[] >>
  strip_tac >>
  first_x_assum(qspecl_then [`LUPDATE NONE (LENGTH l) rl`,
    `k3`,`v3`,`l3`] assume_tac) >>
  rfs[LENGTH_LUPDATE] >>
  qspecl_then [`rl`,`l`] assume_tac lemma_rl_rm_imp_length_inv >> gvs[]
QED



Theorem fib_heap_link_root_list_mem_thm:
  !n rl fts rl' frame arr m dm.
  fts_link_root_list n rl fts = (rl',T) /\
  (fts_mem (ann_fts 0w fts) * reb_array_mem (arr:'a word) 0w rl *
    frame) (fun2set (m,dm)) ∧
  LENGTH rl = max_rank /\
  max_rank < dimword (:'a) ∧
  (∀x k v l. x < LENGTH rl ∧ rl❲x❳ = SOME (FibTree k v l) ⇒ LENGTH l = x) /\
  LENGTH fts <= n
  ==>
  ?m'.
  fib_heap_link_root_list n (arr,head_key fts,m,dm,T) = (m',T) /\
  (reb_array_mem arr 0w rl' * frame) (fun2set(m',dm))
Proof
  Induct >> rpt strip_tac
  >- (
    simp[Once fib_heap_link_root_list_def] >>
    Cases_on `fts`
    >- (
      simp[head_key_def,head_key_t_def] >>
      gvs[fts_link_root_list_def] >>
      fs[fts_mem_def,ann_fts_def,SEP_CLAUSES,STAR_ASSOC]
      ) >>
    Cases_on `h` >>
    `a <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
      ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
    simp[head_key_def,head_key_t_def] >>
    fs[fts_link_root_list_def]
    ) >>
  Cases_on `fts`
  >- (
    gvs[fts_link_root_list_def] >>
    simp[Once fib_heap_link_root_list_def,head_key_def,head_key_t_def] >>
    fs[fts_mem_def,ann_fts_def,SEP_CLAUSES]
    ) >>
  Cases_on `h` >>
  rename [`FibTree k v l::t`] >>
  simp[Once fib_heap_link_root_list_def,head_key_def,head_key_t_def] >>
  `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
     ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
  simp[] >>
  pairarg_tac >> simp[] >>
  qspecl_then [`reb_array_mem arr 0w rl * frame`,`0w`,`(FibTree k v l::t)`,
    `m`,`dm`,`top'`,`a'`,`m'`,`c'`] mp_tac fib_heap_pop_mem_thm >>
  simp[head_key_def,head_key_t_def,STAR_ASSOC] >>
  strip_tac >> gvs[] >>
  pairarg_tac >> simp[] >>
  qpat_x_assum `fts_link_root_list (SUC n) rl (FibTree k v l::t) = (rl',T)` mp_tac >>
  simp[Once fts_link_root_list_def] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qspecl_then [`max_rank`,`fts_mem (ann_fts 0w t) * frame`,`k`,`v`,`l`,
   `arr`,`rl`,`n_rl`,`m'`,`dm`] mp_tac fib_heap_link_trees_mem_thm >>
  simp[] >>
  rfs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def,
     fts_mem_def,SEP_CLAUSES, head_key_def, ft_mem_def, new_anode_def,
     new_dnode_def, head_key_t_def, ones_def, STAR_ASSOC,empty_node2_def] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  fs[STAR_ASSOC] >>
  strip_tac >>  strip_tac >>
  first_x_assum (qspecl_then [`n_rl`,`t`,`rl'`,`frame`,`arr`,`m''`,`dm`] mp_tac) >>
  simp[] >>
  qspecl_then [`max_rank`,`rl`,`(FibTree k v l)`]
    assume_tac  lemma_fts_link_trees_length_rl >> rfs[] >>
  qspecl_then [`max_rank`,`rl`,`k`,`v`,`l`]
    assume_tac lemma_fib_heap_link_root_list_inv_ih >> gvs[]
QED




Definition fib_heap_collect_array_def:
  fib_heap_collect_array (n:num) (arr,acc,m,dm,c)
  =
  let (arr_t,c) = read_mem (arr + (n2w n)) m dm c in
  let (acc,m,c) = fib_heap_meld (arr_t,acc,m,dm) in
  let (m,c) =
    (if arr_t = 0w then
      (m,c)
    else
      write_mem (arr + (n2w n)) 0w m dm c) in
  if n = 0 then
    (acc,m,c)
  else
    fib_heap_collect_array (n-1) (arr,acc,m,dm,c)
End


Theorem fib_heap_collect_array_mem_thm:
  !n rl acc fts' rl' arr frame m dm c.
  fts_collect_array n rl acc = (fts',rl') /\
  (fts_mem (ann_fts 0w acc) * reb_array_mem (arr:'a word) 0w rl * frame)
    (fun2set(m,dm)) /\
  LENGTH rl = max_rank /\
  max_rank < dimword (:'a) ∧
  n < LENGTH rl
  ==>
  ?m'.
  fib_heap_collect_array n (arr,head_key acc,m,dm,c) = (head_key fts',m',T) /\
  (fts_mem (ann_fts 0w fts') * reb_array_mem arr 0w rl' * frame) (fun2set(m',dm))
Proof
  Induct >> rpt strip_tac >> fs[]
  >- (
    simp[Once fib_heap_collect_array_def,read_mem_def,write_mem_def] >>
    qpat_x_assum `fts_collect_array 0 rl acc = (fts',rl')` mp_tac >>
    simp[Once fts_collect_array_def] >>
    CASE_TAC
    >- (
      strip_tac >> gvs[] >>
      `0 < LENGTH rl` by simp[] >>
      drule_all LESS_LENGTH  >> strip_tac >>
      fs[reb_array_mem_def] >>
      SEP_R_TAC >> simp[] >>
      `fts_meld [] acc = acc` by simp[fts_meld_def] >>
      qspecl_then [`one(arr,Word 0w) * reb_array_mem arr 1w ys2 * frame`,
        `0w`,`[]`,`acc`,`acc`,`m`,`dm`] mp_tac fib_heap_meld_mem_thm >>
      simp[fts_mem_def,ann_fts_def,STAR_ASSOC,SEP_CLAUSES] >>
      fs[AC STAR_ASSOC STAR_COMM] >>
      simp[head_key_def,head_key_t_def] >>
      strip_tac >> simp[]
      ) >>
    CASE_TAC >> simp[] >> strip_tac >>
    rename [`FibTree k v l`] >>
    drule_all LESS_LENGTH  >> strip_tac >>
    fs[reb_array_mem_def] >>
    SEP_R_TAC >> simp[] >>
    `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
     ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
    simp[] >>
    qspecl_then [`one(arr,Word k) * reb_array_mem arr 1w ys2 * frame`, `0w`,
      `[FibTree k v l]`,`acc`,`fts'`,`m`,`dm`] mp_tac fib_heap_meld_mem_thm >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    simp[head_key_def,head_key_t_def] >>
    strip_tac >> gvs[] >>
    simp[LUPDATE_DEF,reb_array_mem_def] >>
    SEP_W_TAC >>
    fs[AC STAR_ASSOC STAR_COMM]
    ) >>
  qpat_x_assum `fts_collect_array (SUC n) rl acc = (fts',rl')` mp_tac >>
  simp[Once fts_collect_array_def,Once fib_heap_collect_array_def,
       read_mem_def,write_mem_def] >>
  CASE_TAC
  >- (
    strip_tac >>
    drule_all LESS_LENGTH  >> strip_tac >>
    fs[reb_array_mem_def,reb_array_mem_append_thm,EL_APPEND] >>
    SEP_R_TAC >> simp[] >>
    `fts_meld [] acc = acc` by simp[fts_meld_def] >>
    qspecl_then[`one(arr + n2w (SUC n),Word 0w) * reb_array_mem arr 0w ys1 *
      reb_array_mem arr (n2w (SUC n +1)) ys2 * frame`,
      `0w`,`[]`,`acc`,`acc`,`m`,`dm`] mp_tac fib_heap_meld_mem_thm >>
    fs[fts_mem_def,ann_fts_def,STAR_ASSOC,SEP_CLAUSES] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    simp[head_key_def,head_key_t_def] >>
    strip_tac >> simp[] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    rfs[] >>
    first_x_assum(qspecl_then [`ys1 ++ [NONE] ++ ys2`,`acc`,`fts'`,`rl'`,`arr`,
      `frame`,`m'`,`dm`,`T`] mp_tac) >>
    simp[reb_array_mem_def,reb_array_mem_append_thm,SEP_CLAUSES] >>
    fs[AC STAR_ASSOC STAR_COMM] >>
    simp[head_key_def] >> strip_tac >> simp[]
    ) >>
  CASE_TAC >> simp[] >> strip_tac >>
  rename [`EL (SUC n) rl  = SOME (FibTree k v l)`] >>
  qabbrev_tac `ts = fts_meld [FibTree k v l] acc` >>
  drule_all LESS_LENGTH  >> strip_tac >>
  fs[reb_array_mem_def,reb_array_mem_append_thm,EL_APPEND] >>
  SEP_R_TAC >> simp[] >>
  `k <> 0w` by full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR,fts_mem_def,
     ann_fts_def,ones_def,SEP_CLAUSES,STAR_ASSOC,ann_fts_seg_def,ft_mem_def] >>
  simp[] >>
  qspecl_then [`reb_array_mem arr 0w ys1 * one(arr + n2w (SUC n),Word k) *
    reb_array_mem arr (n2w (SUC n + 1)) ys2 * frame`, `0w`,
    `[FibTree k v l]`,`acc`,`ts`,`m`,`dm`] mp_tac fib_heap_meld_mem_thm >>
  fs[STAR_ASSOC,SEP_CLAUSES] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  simp[head_key_def,head_key_t_def] >>
  strip_tac >> simp[] >>
  fs[LUPDATE_APPEND,LUPDATE_DEF] >>
    first_x_assum(qspecl_then [`ys1 ++ [NONE] ++ ys2`,`ts`,`fts'`,`rl'`,`arr`,
      `frame`,`m'(|arr + n2w (SUC n) |-> Word 0w |)`,`dm`,`T`] mp_tac) >>
  simp[reb_array_mem_append_thm,reb_array_mem_def] >>
  SEP_W_TAC >>
  fs[STAR_ASSOC,SEP_CLAUSES] >>
  simp[head_key_def]
QED



Definition fib_heap_reb_def:
  fib_heap_reb n (arr,a,m,dm)
  =
  let (m,c) = fib_heap_link_root_list n (arr,a,m,dm,T) in
    fib_heap_collect_array (max_rank - 1) (arr,0w,m,dm,c)
End

Theorem lemma_emp_rl_imp_reb_inv:
  (∀x k v l.
    x < LENGTH emp_rl ∧ emp_rl❲x❳ = SOME (FibTree k v l) ⇒
   LENGTH l = x) <=> T
Proof
  iff_tac >> simp[] >>
  rpt strip_tac >>
  fs[emp_rl_def] >>
  pop_assum mp_tac >>
  simp[EL_REPLICATE]
QED


Theorem lemma_rl_lupdate_none_step:
  (∀x. x < LENGTH rl ∧ SUC r < x ⇒ rl❲x❳ = NONE) ==>
  (∀x. x < LENGTH rl❲SUC r ↦ NONE❳ ∧ r < x ⇒ rl❲SUC r ↦ NONE❳❲x❳ = NONE)
Proof
  rpt strip_tac >>
  Cases_on `SUC r = x` >> fs[EL_LUPDATE]
QED


Theorem lemma_fts_collect_array_empty:
  !r rl acc fts rl'.
  (∀x. x < LENGTH rl ∧ r < x ⇒ rl❲x❳ = NONE) ∧
  fts_collect_array r rl acc = (fts,rl')
  ⇒
  (∀x. x < LENGTH rl' ⇒ rl'❲x❳ = NONE)
Proof
  Induct >> rpt strip_tac
  >- (
    qspecl_then [`0`,`rl`,`acc`] assume_tac lemma_fts_collect_array_length_rl >>
    rfs[] >>
    qpat_x_assum `fts_collect_array 0 rl acc = (fts,rl')` mp_tac >>
    rewrite_tac[Once fts_collect_array_def] >>
    CASE_TAC
    >- (strip_tac >> Cases_on `x` >> fs[]) >>
    CASE_TAC >> strip_tac >> gvs[] >>
    Cases_on `x` >> simp[EL_LUPDATE]
    ) >>
  qspecl_then [`0`,`rl`,`acc`] assume_tac lemma_fts_collect_array_length_rl >>
  rfs[] >>
  qpat_x_assum `fts_collect_array (SUC r) rl acc = (fts,rl')` mp_tac >>
  rewrite_tac[Once fts_collect_array_def] >>
  CASE_TAC >> simp[]
  >- (
    strip_tac >>
    res_tac >>
    metis_tac[lemma_rl_ind_lupdate_none2]
    ) >>
  CASE_TAC >> simp[] >> strip_tac >>
  res_tac >>
  simp[lemma_rl_lupdate_none_step]
QED



Theorem lemma_fts_reb_empty_array:
  fts_reb emp_rl fts = (fts',rl,flag) ==> emp_rl = rl
Proof
  simp[fts_reb_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `(!x. x < LENGTH l_rl ∧ (LENGTH l_rl - 1) < x ⇒ l_rl❲x❳ = NONE)` by simp[] >>
  qspecl_then [`(LENGTH l_rl - 1)`,`l_rl`,`[]`,`fts'`,`e_rl`]
    mp_tac lemma_fts_collect_array_empty >>
  simp[] >>
  strip_tac >>
  imp_res_tac lemma_e_rl_eq_replicate >>
  qspecl_then [`(LENGTH l_rl - 1)`,`l_rl`,`[]`]
    assume_tac lemma_fts_collect_array_length_rl >> rfs[] >>
  qspecl_then [`LENGTH fts`,`emp_rl`,`fts`]
    assume_tac lemma_fts_link_root_list_length_rl >>
  gvs[] >>
  simp[emp_rl_def,LENGTH_REPLICATE]
QED




Theorem fib_heap_reb_mem_thm:
  !frame n fts fts' rl' arr m dm.
  fts_reb emp_rl fts = (fts',rl',T) /\
  (fts_mem (ann_fts 0w fts) * reb_array_mem (arr:'a word) 0w emp_rl * frame)
    (fun2set(m,dm)) /\
  max_rank < dimword (:'a) /\
  LENGTH fts <= n
  ==>
  ?m'.
  fib_heap_reb n (arr,head_key fts,m,dm) = (head_key fts',m',T) /\
  (fts_mem (ann_fts 0w fts') * reb_array_mem arr 0w rl' * frame) (fun2set(m',dm))
Proof
  rpt gen_tac >> disch_tac >> fs[] >>
  qpat_x_assum `fts_reb emp_rl fts = (fts',rl',T)` mp_tac >>
  simp[Once fib_heap_reb_def,Once fts_reb_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `flag`
  >- (
    qspecl_then [`n`,`emp_rl`,`fts`,`l_rl`,`frame`,`arr`,`m`,`dm`]
      mp_tac fib_heap_link_root_list_mem_thm >>
    simp[lemma_fts_link_root_list_clock_cap] >>
    simp[] >> simp[Once emp_rl_def,LENGTH_REPLICATE] >>
    simp[lemma_emp_rl_imp_reb_inv] >>
    strip_tac >> simp[] >>
    pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
    qspecl_then [`LENGTH l_rl - 1`,`l_rl`,`[]`,`fts'`,`e_rl`,`arr`,`frame`,`m'`,
      `dm`,`T`] mp_tac fib_heap_collect_array_mem_thm >>
    simp[fts_mem_def,ann_fts_def,SEP_CLAUSES,STAR_ASSOC] >>
    qabbrev_tac `n' = LENGTH fts` >>
    qspecl_then [`n'`,`emp_rl`,`fts`] mp_tac lemma_fts_link_root_list_length_rl >>
    simp[] >> strip_tac >> simp[emp_rl_def,LENGTH_REPLICATE] >>
    simp[head_key_def,head_key_t_def] >>
    strip_tac
    ) >>
  simp[] >>
  pairarg_tac >> simp[]
QED






Definition fib_heap_ext_min_def:
  fib_heap_ext_min (n:num) (arr,a,m,dm)
  =
  let (min,a,m,c) = fib_heap_rm_min (a,m,dm) in
  let (a,m,c') = fib_heap_reb n (arr,a,m,dm) in
    (min,a,m,c /\ c')
End




Theorem fib_heap_ext_min_mem:
  !frame n fts arr m dm fts' rl min.
  fts_extract_min fts = ((min:'a word),fts',rl,T) /\
  (fts_mem (ann_fts 0w fts) * reb_array_mem arr 0w emp_rl * frame)
    (fun2set (m,dm)) ∧
  max_rank < dimword (:α) /\
  fts_size fts <= n
  ==>
  ?a' m' v e.
  fib_heap_ext_min n (arr,head_key fts,m,dm) = (min,head_key fts',m',T) /\
  (fts_mem (ann_fts 0w fts') * reb_array_mem arr 0w emp_rl * empty_node min (v,e) *
    frame) (fun2set (m',dm))
Proof
  rpt strip_tac >>
  qpat_x_assum `fts_extract_min fts = (min,fts',rl,T)` mp_tac >>
  simp[fts_extract_min_def,fib_heap_ext_min_def] >>
  pairarg_tac >> simp[] >>
  qspecl_then [`frame * reb_array_mem arr 0w emp_rl`,`fts`,`fts''`,`m`,`dm`,`min'`]
    mp_tac fib_heap_rm_min_mem >>
  simp[STAR_ASSOC] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  strip_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  rename [`fts_reb emp_rl fts2 = (fts3,e_rl,flage)`] >>
  strip_tac >> gvs[] >>
  qspecl_then [`frame * empty_node min (v,e)`,`n`,`fts2`,`fts'`,`e_rl`,`arr`,
    `m'`,`dm`] mp_tac fib_heap_reb_mem_thm >>
  imp_res_tac lemma_fts_rm_min_length >> simp[] >>
  fs[AC STAR_ASSOC STAR_COMM] >>
  strip_tac >> simp[] >>
  qexistsl [`v`,`e`] >> simp[] >>
  imp_res_tac lemma_fts_reb_empty_array >> gvs[]
QED



