(*
  Memory Level Implementation and Verification for fts_meld
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

