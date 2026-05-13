(*
  Memory Level Verification for Fibonacci heap
*)
Theory fib_heap_meld
Ancestors
  misc words arithmetic list alist set_sep pair finite_map combin panSem
  fibonacci_heap pred_set
Libs
  wordsLib helperLib



Definition fib_heap_meld_def:
  fib_heap_meld
    (a1:'a word,a2:'a word,m:'a word -> 'a word_lab, dm: 'a word set)
  =
    if a2 = 0w then (a1,m,T) else
    let c = in_mem a2 dm in
    if a1 = 0w then (*list a is empty*)
      (a2,m,c)
    else
      let (l_a1,c) = read_mem (a1 + before_off) m dm c in
      let (l_a2,c) = read_mem (a2 + before_off) m dm c in

      let (m,c) = write_mem (l_a1 + next_off) a2   m dm c in
      let (m,c) = write_mem (a2 + before_off) l_a1 m dm c in
      let (m,c) = write_mem (l_a2 + next_off) a1   m dm c in
      let (m,c) = write_mem (a1 + before_off) l_a2 m dm c in

      let (v_a2,c) = read_mem a2 m dm c in
      let (v_a1,c) = read_mem a1 m dm c in
      if v_a2 <=+ v_a1 then
        (a2,m,c)
      else
        (a1,m,c)
End


Theorem lemma_mem_fib_heap_meld:
  (fts_mem (ann_fts 0w fts) * fts_mem (ann_fts 0w fts') * frame)
    (fun2set (m,dm)) /\
  fib_heap_meld (head_key fts,head_key fts',m,dm) = (a',m',c) ==>
  (fts_mem (ann_fts 0w (fts ++ fts')) * frame)
    (fun2set (m',dm)) /\
  c = T /\
  (a' = head_key (fts ++ fts') /\ fts_hd_value fts <=+ fts_hd_value fts' \/
  a' = head_key (fts' ++ fts) /\ fts_hd_value fts' <=+ fts_hd_value fts)
Proof
  disch_tac >> fs[] >>
  pop_assum mp_tac >>
  Cases_on `fts` >> Cases_on `fts'` >>
  simp[fib_heap_meld_def,read_mem_def,write_mem_def,next_off_def,before_off_def,
       head_key_def,head_key_t_def]
  >- (
    strip_tac >> gvs[] >>
    fs[ann_fts_def,fts_mem_def,SEP_CLAUSES]
    )
  >- (
    Cases_on `h` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> strip_tac >> gvs[] >>
    simp[fts_hd_value_def]
    )
  >- (
    Cases_on `h` >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def,fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> strip_tac >> gvs[] >>
    simp[fts_hd_value_def]
    ) >>
  Cases_on `h` >> Cases_on `h'` >>
  Cases_on `t` using SNOC_CASES >>
  Cases_on `t'` using SNOC_CASES >>
  fs[SNOC_APPEND,REVERSE_APPEND] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def,last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  IF_CASES_TAC
  >- (
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >> fs[fts_hd_value_def]
    )
  >- (
    SEP_R_TAC >> simp[] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    SEP_R_TAC >> fs[fts_hd_value_def] >>
    imp_res_tac WORD_NOT_LOWER_EQUAL >>
    simp[WORD_LOWER_IMP_LOWER_OR_EQ]
    )
  >- (
    Cases_on `x` >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    fs[head_key_t_pull_last_thm] >>
    SEP_R_TAC >> fs[fts_hd_value_def]
    )
  >- (
    Cases_on `x` >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    fs[head_key_t_pull_last_thm] >>
    SEP_R_TAC >> fs[fts_hd_value_def] >>
    imp_res_tac WORD_NOT_LOWER_EQUAL >>
    simp[WORD_LOWER_IMP_LOWER_OR_EQ]
    )
  >- (
    Cases_on `x` >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    fs[head_key_t_pull_last_thm] >>
    SEP_R_TAC >> fs[fts_hd_value_def] >>
    simp[last_key_t_append_thm,last_key_t_def,head_key_t_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR]
    )
  >- (
    Cases_on `x` >>
    SEP_R_TAC >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    fs[head_key_t_pull_last_thm,last_key_t_pull_thm] >>
    SEP_R_TAC >> fs[fts_hd_value_def] >>
    imp_res_tac WORD_NOT_LOWER_EQUAL >>
    simp[WORD_LOWER_IMP_LOWER_OR_EQ] >>
    simp[head_key_def,head_key_t_def]
    )
  >- (
    Cases_on `x` >> Cases_on `x'` >>
    fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    fs[ann_fts_seg_append_thm,fts_mem_append_thm] >>
    fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
       SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
       fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
    SEP_R_TAC >> simp[] >>
    strip_tac >> gvs[] >>
    SEP_W_TAC >> simp[] >>
    fs[head_key_t_append_thm,head_key_t_pull_last_thm] >>
    simp[last_key_t_append_thm,last_key_t_def,head_key_t_def] >>
    full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
    SEP_R_TAC >> fs[fts_hd_value_def]
    ) >>
  Cases_on `x` >> Cases_on `x'` >>
  fs[REVERSE_APPEND,ann_fts_seg_append_thm,fts_mem_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  fs[ann_fts_seg_append_thm,fts_mem_append_thm] >>
  fs[ann_fts_def, ann_fts_seg_def, last_key_def, last_key_t_def, fts_mem_def,
     SEP_CLAUSES, head_key_def, ft_mem_def, fill_anode_def,
     fill_dnode_def, head_key_t_def, ones_def, STAR_ASSOC] >>
  SEP_R_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  SEP_W_TAC >> simp[] >>
  fs[head_key_t_pull_last_thm] >>
  SEP_R_TAC >> fs[fts_hd_value_def] >>
  imp_res_tac WORD_NOT_LOWER_EQUAL >>
  simp[WORD_LOWER_IMP_LOWER_OR_EQ] >>
  simp[head_key_def,head_key_t_def] >>
  simp[head_key_t_append_thm,head_key_t_pull_last_thm] >>
  simp[last_key_t_append_thm,last_key_t_def,head_key_t_def]
QED



Theorem fib_heap_meld:
  ∀frame.
    (fib_heap a fh1 * fib_heap b fh2 * frame)
      (fun2set (m,dm)) ∧
    DISJOINT (FDOM fh1) (FDOM fh2) /\
    fib_heap_meld (a, b, m, dm) = (a', m', c) ⇒
    (fib_heap a' (FUNION fh1 fh2) * frame) (fun2set (m',dm)) ∧ c
Proof
  fs[fib_heap_def] >>
  fs[SEP_CLAUSES, STAR_ASSOC, SEP_EXISTS_THM] >>
  full_simp_tac (std_ss ++ sep_cond_ss) [cond_STAR] >>
  rpt gen_tac >> strip_tac >>
  simp [PULL_EXISTS] >>
  gvs[] >>
  imp_res_tac lemma_mem_fib_heap_meld
  >- (
    qexists `fts ++ fts'` >> simp[] >>
    qspecl_then [`fh2`,`fh1`,`fts'`,`fts`] assume_tac lemma_logical_melt >>
    rfs[DISJOINT_SYM,fib_heap_inv_comm_thm]
    )
  >- (
    qexists `fts' ++ fts` >> simp[] >>
    qspecl_then [`fh1`,`fh2`,`fts`,`fts'`] assume_tac lemma_logical_melt >>
    rfs[DISJOINT_SYM,fib_heap_inv_comm_thm] >>
    simp[fts_mem_ann_sym_thm]
    )
  >- (
    qexists `fts ++ fts'` >> simp[] >>
    qspecl_then [`fh2`,`fh1`,`fts'`,`fts`] assume_tac lemma_logical_melt >>
    rfs[DISJOINT_SYM,fib_heap_inv_comm_thm]
    ) >>
  qexists `fts' ++ fts` >> simp[] >>
  qspecl_then [`fh1`,`fh2`,`fts`,`fts'`] assume_tac lemma_logical_melt >>
  rfs[DISJOINT_SYM,fib_heap_inv_comm_thm] >>
  simp[fts_mem_ann_sym_thm]
QED


