(*
  Memory Level Verification for the Extract Minimum Operation on a Fibonacci heap
*)

Theory fib_heap_ext_min
Ancestors
  misc words arithmetic list alist set_sep pair finite_map combin panSem
  fibonacci_heap pred_set fib_heap_meld
Libs
  wordsLib helperLib

Definition fib_heap_weak_def:
  fib_heap_weak a fh =
    SEP_EXISTS fts.
      fts_mem (ann_fts 0w fts) *
      cond (fib_heap_inv_weak fh fts /\ a = head_key fts)
End


Definition fib_heap_pop_def:
  fib_heap_pop (a:'a word, m:'a word -> 'a word_lab,dm: 'a word set)
  =
  if a = 0w then (a,0w,m,T) else
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





Theorem fib_heap_pop:
  !frame.
    (fib_heap_weak a fh1 * frame) (fun2set (m,dm)) /\
    fib_heap_pop (a,m,dm) = (a,a',m',c)
    ==>
    ?fts fh2.
    (fib_heap a fh2 * fib_heap_weak a' (FDIFF fh1 (FDOM fh2)) * frame)
      (fun2set (m',dm)) /\ DISJOINT (FDOM fh2) (FDOM (FDIFF fh1 (FDOM fh2))) /\ c
Proof
  simp[fib_heap_weak_def,fib_heap_def] >>
  rpt strip_tac >>
  fs[SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS] >>
  pop_assum mp_tac >>
  Cases_on `fts`
  >- (
    fs[head_key_def,head_key_t_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    simp[fib_heap_pop_def, read_mem_def, write_mem_def] >>
    strip_tac >> gvs[] >>
    qexistsl [`FEMPTY`,`[]`,`[]`] >> simp[fib_heap_def] >>
    simp[fib_heap_inv_empty_thm,head_key_def,head_key_t_def] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    ) >>
  Cases_on `h` >>
  Cases_on `t`
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    gvs[] >>
    simp[fib_heap_pop_def, read_mem_def, write_mem_def,next_off_def,before_off_def] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    qexistsl [`fh1`,`[FibTree a v l]`,`[]`] >>
    simp[head_key_t_def] >>
    simp[lemma_fdiff_id_eq_empty,fib_heap_inv_weak_empty_thm] >>
    simp[lemma_inv_weak_imp_inv] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC]
    ) >>
  Cases_on `h` >>
  Cases_on `t'` using SNOC_CASES
  >- (
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    gvs[] >>
    simp[fib_heap_pop_def, read_mem_def, write_mem_def,next_off_def,before_off_def] >>
    SEP_R_TAC >> simp[] >>
    `k' <> a` by SEP_NEQ_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_R_TAC >> simp[] >>
    drule_all lemma_fib_heap_inv_weak_split >>
    strip_tac >> fs[] >>
    qexistsl [`fh1'`,`[FibTree a v l]`,`[FibTree a' v' l']`] >>
    gvs[head_key_t_def] >>
    simp[FDIFF_FUNION,lemma_fdiff_id_eq_empty,lemma_fdiff_disjoint] >>
    simp[DISJOINT_SYM] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_W_TAC >>
    simp[AC STAR_ASSOC STAR_COMM] >>
    irule lemma_inv_weak_imp_inv >> simp[]
    ) >>
  Cases_on `x` >> fs[SNOC_APPEND,REVERSE_APPEND] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[fts_mem_append_thm,ann_fts_seg_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  gvs[] >>
  simp[fib_heap_pop_def, read_mem_def, write_mem_def,next_off_def,before_off_def] >>
  SEP_R_TAC >> simp[] >>
  `k' <> a` by SEP_NEQ_TAC >> simp[] >>
  simp[REVERSE_APPEND,head_key_t_def] >>
  drule_all lemma_fib_heap_inv_weak_split >>
  SEP_R_TAC >> simp[] >>
  rpt strip_tac >> gvs[] >>
  rename [`fib_heap_inv_weak fh2 (FibTree a' v' l'::
    (rest ++ [FibTree lk lv ll]))`] >>
  qexistsl [`fh1'`,`[FibTree a v l]`,`(FibTree a' v' l'::
    (rest ++ [FibTree lk lv ll]))`] >>
  simp[head_key_t_def] >>
  simp[FDIFF_FUNION,lemma_fdiff_id_eq_empty,lemma_fdiff_disjoint] >>
  simp[DISJOINT_SYM] >>
  simp[lemma_inv_weak_imp_inv] >>
  rewrite_tac[GSYM (cj 2 APPEND)] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[fts_mem_append_thm,ann_fts_seg_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  SEP_W_TAC >>
  simp[REVERSE_APPEND,head_key_t_def] >>
  fs[head_key_t_pull_last_thm]
QED



Definition fib_heap_parent_to_null_def:
  fib_heap_parent_to_null (n: num) (a,m,dm)
  =
  if a = 0w then (a,m,T) else
  if n = 0 then
  let (m,c) = write_mem (a + parent_off) 0w m dm T in
      (a,m,c)
  else
    let (n_a,c) = read_mem (a + next_off) m dm T in
    let (_,m,c') = fib_heap_parent_to_null (n - 1) (n_a,m,dm) in
    let (m,c) = write_mem (a + parent_off) 0w m dm (c /\ c') in
      (a,m,c)
End

Definition get_key_def[simp]:
  get_key (FibTree k v l) = k
End



Theorem lemma_fib_heap_parent_is_null:
  n < LENGTH fts /\
  (!x. x < n ==>
    read_mem (get_key(EL x fts) + parent_off) m dm T = (0w,T)) ==>
  !p. (fts_mem (ann_fts_seg
Proof

QED


print_find "ann_fts_append_thm"



Theorem fib_heap_parent_to_null:
  !n fts m dm frame m' c.
  (fts_mem (ann_fts p fts) * frame) (fun2set(m,dm)) /\
  n < LENGTH fts /\
  (!x. n < x /\ x < LENGTH fts ==>
    read_mem (get_key(EL x fts) + parent_off) m dm T = (0w,T)) /\
  fib_heap_parent_to_null n (get_key(EL n fts),m,dm) =
    (head_key fts,m',T)
  ==>
  (fts_mem (ann_fts 0w fts) * frame) (fun2set(m',dm))
Proof
  Induct
  >- (
    rpt gen_tac  >> disch_tac >> fs[] >>
    pop_assum mp_tac >>
    simp[Once fib_heap_parent_to_null_def, head_key_def,head_key_t_def,
         read_mem_def,write_mem_def,parent_off_def] >>
    Cases_on `fts` >> fs[] >>
    Cases_on `h` >> simp[] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    fs[fts_mem_def,ann_fts_def,SEP_CLAUSES]
    ) >>
  rpt gen_tac  >> disch_tac >> fs[] >>
  pop_assum mp_tac >>
  simp[Once fib_heap_parent_to_null_def, head_key_def,head_key_t_def,
       read_mem_def,write_mem_def,next_off_def,parent_off_def] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  SEP_R_TAC >> simp[] >>
  Cases_on `fts` >> simp[head_key_t_def]
  >- (
    strip_tac >> gvs[] >>
    SEP_W_TAC >>
    fs[ann_fts_seg_def,head_key_def,head_key_t_def]
  ) >>
  Cases_on `h` >>
  pop_assum mp_tac >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  `k <> k'` by SEP_NEQ_TAC >> simp[] >>

  first_x_assum(qspecl_then [`m⦇k + 6w * bytes_in_word ↦ Word 0w⦈`


  strip_tac >>

QED




Definition fib_heap_rm_min_def:
  fib_heap_rm_min (a:'a word,m:'a word -> 'a word_lab,dm: 'a word set)
  =
  if a = 0w then (a,a,m,T) else
  let (min,n_a,m,c) = fib_heap_pop (a,m,dm) in
  let c' = in_mem (a + child_off) dm in
  let c = (c /\ c') in
  let child_a = a + child_off in
  let (rank_a,c) = read_mem (a + rank_off) m dm c in
  let (child_a,m,c') = fib_heap_parent_to_null (rank_a + 1w)
                        (child_a,child_a,m,dm) in
  let c = (c /\ c') in
  let (new_a,m,c') = fib_heap_meld (child_a,n_a,m,dm) in
    (min,new_a,m,c /\ c')
End



