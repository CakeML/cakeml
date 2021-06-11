(*
  Lemmas about size_of
*)

open preamble dataSemTheory dataPropsTheory;

val _ = new_theory "size_ofProps";

Theorem delete_mk_BN:
  (delete 0 (mk_BN t1 t2) = mk_BN t1 t2) ∧
  (k ≠ 0 ⇒ delete k (mk_BN t1 t2) = delete k (BN t1 t2))
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ fs [mk_BN_def]
  \\ fs [delete_def,mk_BN_def]
QED

Theorem delete_mk_BS:
  (delete 0 (mk_BS t1 s t2) = mk_BN t1 t2) ∧
  (k ≠ 0 ⇒ delete k (mk_BS t1 s t2) = delete k (BS t1 s t2))
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ fs [mk_BS_def]
  \\ fs [delete_def,mk_BS_def,mk_BN_def]
QED

Triviality DIV_2_lemma:
  n DIV 2 = m DIV 2 ∧ EVEN m = EVEN n ⇒ m = n
Proof
  rw []
  \\ ‘0 < 2n’ by fs [] \\ drule DIVISION
  \\ fs [EVEN_MOD2]
  \\ disch_then (fn th => once_rewrite_tac [th]) \\ fs []
  \\ Cases_on ‘m MOD 2 = 0’ \\ fs []
  \\ ‘n MOD 2 < 2’ by fs [MOD_LESS]
  \\ ‘m MOD 2 < 2’ by fs [MOD_LESS]
  \\ decide_tac
QED

Theorem delete_delete:
  ∀f n k.
    delete n (delete k f) =
    if n = k then delete n f else delete k (delete n f)
Proof
  Induct \\ fs [delete_def]
  \\ rw [] \\ fs [delete_def]
  \\ simp [delete_mk_BN,delete_mk_BS]
  \\ rpt (qpat_x_assum ‘∀x. _’ (mp_tac o GSYM)) \\ rw []
  \\ fs [delete_def]
  \\ rpt (qpat_x_assum ‘∀x. _’ (fn th => simp [Once (GSYM th)])) \\ rw []
  \\ rpt (rename [‘kk ≠ 0’] \\ Cases_on ‘kk’ \\ fs [])
  \\ drule DIV_2_lemma \\ fs [EVEN]
QED

Theorem size_zero_empty:
  ∀x. size x = 0 ⇔ domain x = EMPTY
Proof
  Induct \\ fs [size_def]
QED

Definition sane_timestamps_def:
  sane_timestamps l =
  ∀ts tag bl tag' bl'.
    MEM (Block ts tag bl) l ∧ MEM (Block ts tag' bl') l ⇒
    tag = tag' ∧ bl = bl'
End

Definition all_blocks_def[simp]:
  (all_blocks [] = []) ∧
  (all_blocks (Block ts tag bl :: ys) =
   Block ts tag bl :: all_blocks bl ++ all_blocks ys) ∧
  (all_blocks (_ :: ys) = all_blocks ys)
Termination
  WF_REL_TAC ‘measure v1_size’
End

Theorem all_blocks_append:
  ∀xs ys. all_blocks (xs ++ ys) = all_blocks xs ++ all_blocks ys
Proof
  Induct \\ fs [] \\ Cases \\ fs []
QED

Theorem all_blocks_cons:
  ∀x xs. all_blocks (x::xs) = all_blocks [x] ++ all_blocks xs
Proof
  rw [] \\ qspecl_then [‘[x]’,‘xs’] assume_tac all_blocks_append
  \\ fs []
QED

Theorem all_blocks_cons_simp:
  ∀x xs ys. all_blocks (x::xs::ys) = all_blocks [x] ++ all_blocks (xs::ys)
Proof
  rw [] \\ qspecl_then [‘[x]’,‘xs::ys’] assume_tac all_blocks_append
  \\ fs []
QED

Theorem size_of_cons:
  size_of lims (x::xs) refs seen =
    let (n1,refs1,seen1) = size_of lims xs refs seen in
    let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
       (n1 + n2,refs2,seen2)
Proof
  Cases_on ‘xs’ \\ fs [size_of_def] \\ fs [UNCURRY]
QED

Theorem size_of_append_eq:
  ∀lims xs ys refs seen.
    size_of lims (xs++ys) refs seen =
      let (n1,refs1,seen1) = size_of lims ys refs seen in
      let (n2,refs2,seen2) = size_of lims xs refs1 seen1 in
         (n1 + n2,refs2,seen2)
Proof
  Induct_on ‘xs’ \\ fs []
  THEN1 (fs [size_of_def] \\ fs [UNCURRY])
  \\ once_rewrite_tac [size_of_cons] \\ fs [UNCURRY]
QED

Theorem size_of_refs_subspt:
  ∀lims ts refs seen n refs1 seen1.
    size_of lims ts refs seen = (n,refs1,seen1) ⇒ subspt refs1 refs
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw []
  THEN1
   (‘∃w. size_of lims (y::ys) refs seen = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs []
    \\ imp_res_tac subspt_trans \\ fs [])
  THEN1
   (fs [AllCaseEqs()]
    THEN1
     (‘∃w. size_of lims vs (delete r refs) seen = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete])
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_delete])
  \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem size_of_refs_size:
  ∀lims ts refs seen n refs1 seen1.
    size_of lims ts refs seen = (n,refs1,seen1) ⇒ size refs1 ≤ size refs
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw []
  THEN1
   (‘∃w. size_of lims (y::ys) refs seen = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs [])
  THEN1
   (fs [AllCaseEqs()]
    THEN1
     (‘∃w. size_of lims vs (delete r refs) seen = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete]
      \\ match_mp_tac LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [size_delete])
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_delete]
    \\ fs [size_delete])
  \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem size_of_refs_shirnk:
  ∀lims ts refs seen n refs1 seen1.
    size_of lims ts refs seen = (n,refs1,seen1) ∧ refs ≠ refs1 ⇒
    size refs1 < size refs
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw []
  THEN1
   (‘∃w. size_of lims (y::ys) refs seen = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs []
    \\ imp_res_tac subspt_trans \\ fs []
    \\ Cases_on ‘w1 = refs’ \\ fs []
    \\ imp_res_tac size_of_refs_size
    \\ fs [])
  THEN1
   (fs [AllCaseEqs()]
    THEN1
     (‘∃w. size_of lims vs (delete r refs) seen = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete]
      \\ rveq \\ imp_res_tac size_of_refs_size
      \\ match_mp_tac LESS_EQ_LESS_TRANS
      \\ asm_exists_tac \\ fs []
      \\ imp_res_tac lookup_zero \\ fs [size_delete])
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_delete]
    \\ imp_res_tac lookup_zero \\ fs [size_delete])
  \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem size_of_refs_pres:
  ∀x1 lims xs refs1 seen1 n refs2 seen2.
    size_of lims xs refs1 seen1 = (n,refs2,seen2) ∧
    lookup x1 refs1 = NONE ⇒
    lookup x1 refs2 = NONE
Proof
  gen_tac \\ ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw []
  THEN1
   (‘∃w. size_of lims (y::ys) refs1 seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs [])
  THEN1
   (fs [AllCaseEqs()] \\ rveq \\ fs []
    THEN1
     (‘∃w. size_of lims vs (delete r refs1) seen1 = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete])
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_delete])
  \\ ‘∃w. size_of lims (v20::v21) refs1 (insert ts () seen1) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem size_of_refs_ignored:
  ∀lims xs refs1 seen1 n refs2 seen2 r x.
    size_of lims xs refs1 seen1 = (n,refs2,seen2) ∧
    lookup r refs2 = SOME x ⇒
    size_of lims xs (delete r refs1) seen1 = (n,delete r refs2,seen2) ∧
    lookup r refs1 = SOME x
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  THEN1
   (‘∃w. size_of lims (y::ys) refs1 seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs []
    \\ res_tac \\ fs [])
  THEN1
   (fs [AllCaseEqs()] \\ rveq \\ fs [lookup_delete]
    THEN1
     (‘∃w. size_of lims vs (delete r refs1) seen1 = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete]
      \\ rveq \\ fs [] \\ res_tac \\ fs []
      \\ simp [Once delete_delete])
    \\ simp [Once delete_delete])
  \\ fs [AllCaseEqs()]
  \\ ‘∃w. size_of lims (v20::v21) refs1 (insert ts () seen1) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem size_of_seen_pres:
  ∀lims xs refs seen1 n refs2 seen2.
    size_of lims xs refs seen1 = (n,refs2,seen2) ⇒ subspt seen1 seen2
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  THEN1
   (‘∃w. size_of lims (y::ys) refs seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs []
    \\ imp_res_tac subspt_trans)
  THEN1
   (fs [AllCaseEqs()] \\ rveq \\ fs [lookup_delete]
    \\ ‘∃w. size_of lims vs (delete r refs) seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete])
  \\ fs [AllCaseEqs()]
  \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen1) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
  \\ fs [subspt_lookup,lookup_insert]
QED

Theorem size_of_seen_ignored:
  ∀x1 lims xs refs seen1 n refs2 seen2.
    size_of lims xs refs seen1 = (n,refs2,seen2) ∧
    lookup x1 seen2 = NONE ⇒
    size_of lims xs refs (insert x1 () seen1) = (n,refs2,insert x1 () seen2) ∧
    lookup x1 seen1 = NONE
Proof
  gen_tac \\ ho_match_mp_tac size_of_ind \\ fs [size_of_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  THEN1
   (‘∃w. size_of lims (y::ys) refs seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims [x] w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [] \\ rveq  \\ fs [])
  THEN1
   (fs [AllCaseEqs()] \\ rveq \\ fs [lookup_delete]
    \\ ‘∃w. size_of lims vs (delete r refs) seen1 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs [] \\ fs [subspt_lookup,lookup_delete])
  \\ Cases_on ‘ts = x1’ \\ fs []
  THEN1
   (Cases_on ‘lookup x1 seen1’ \\ fs [] \\ rveq \\ fs []
    \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen1) = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs [])
  \\ fs [lookup_insert]
  \\ simp [Once insert_insert]
  \\ Cases_on ‘lookup ts seen1’ \\ fs []
  \\ ‘∃w. size_of lims (v20::v21) refs (insert ts () seen1) = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
QED

Theorem v_size_append:
  ∀xs ys. v1_size (xs ++ ys) = v1_size xs + v1_size ys
Proof
  Induct \\ fs [v_size_def]
QED

Definition refs_in_def:
  refs_in refs bs ⇔
    ∀n vals. lookup n refs = SOME (ValueArray vals) ⇒
             set (all_blocks vals) SUBSET set bs
End

Theorem size_of_lemma:
  ∀refs qs seen1 k0 refs1 seen2.
    size_of lims qs refs seen1 = (k0,refs1,seen2) ∧ bb ≠ [] ∧
    (∀refs' xs ys zs seen.
       (if refs ≠ refs' then size refs' < size refs else
          v1_size (xs ++ ys ++ zs) ≤ v1_size (bb ++ qs)) ∧
       sane_timestamps bs ∧ refs_in refs' bs ∧
       set (all_blocks xs ++ all_blocks ys ++ all_blocks zs) SUBSET set bs ⇒
       size_of lims (xs ++ ys ++ zs) refs' seen =
       size_of lims (ys ++ xs ++ zs) refs' seen) ∧
    lookup x1 seen1 = NONE ∧ IS_SOME (lookup x1 seen2) ∧
    sane_timestamps bs ∧ refs_in refs bs ∧
    MEM (Block x1 x2 bb) bs ∧
    set (all_blocks bb ++ all_blocks qs) SUBSET set bs ⇒
    size_of lims qs refs seen1 =
      let (n1,refs1,seen1) = size_of lims (bb ++ qs) refs (insert x1 () seen1) in
        (n1 + LENGTH bb + 1,refs1,seen1)
Proof
  gen_tac
  \\ completeInduct_on ‘size refs’
  \\ simp [Once PULL_FORALL]
  \\ completeInduct_on ‘v1_size qs’
  \\ rpt strip_tac \\ rpt var_eq_tac
  \\ Cases_on ‘qs’ \\ fs []
  THEN1 (fs [size_of_def] \\ rw [] \\ fs [] \\ rfs [])
  \\ Cases_on ‘t = []’
  THEN1
   (rveq
    \\ reverse (Cases_on ‘h’) \\ fs [size_of_def,AllCaseEqs()]
    \\ rveq \\ fs [] \\ rfs []
    THEN1
     (rewrite_tac [size_of_append_eq,size_of_def] \\ simp []
      \\ Cases_on ‘size_of lims vs (delete n refs) seen1’ \\ fs []
      \\ PairCases_on ‘r’ \\ fs [] \\ rveq
      \\ last_x_assum (qspec_then ‘size (delete n refs)’ mp_tac)
      \\ impl_tac
      THEN1 (fs [size_delete] \\ imp_res_tac lookup_zero \\ fs [])
      \\ disch_then (qspec_then ‘delete n refs’ mp_tac)
      \\ rewrite_tac []
      \\ disch_then (qspecl_then [‘vs’,‘seen1’] mp_tac)
      \\ simp []
      \\ reverse impl_tac
      THEN1 (fs [size_of_append_eq] \\ fs [UNCURRY])
      \\ rpt strip_tac
      THEN1
       (first_x_assum match_mp_tac \\ fs []
        \\ Cases_on ‘refs'' = delete n refs’ \\ rveq \\ fs []
        THEN1
         (rw [] THEN1 (fs [size_delete] \\ imp_res_tac lookup_zero \\ fs [])
          \\ rpt (qpat_x_assum ‘lookup _ _ = _’ mp_tac)
          \\ pop_assum (fn th => once_rewrite_tac [th])
          \\ simp [lookup_delete])
        \\ rw [] \\ fs [size_delete] \\ rfs [])
      \\ fs [refs_in_def,lookup_delete] \\ metis_tac [])
    \\ Cases_on ‘l’ \\ fs [size_of_def,CaseEq"bool"]
    \\ rveq \\ fs [] \\ rfs []
    \\ ‘∃rr. size_of lims (h::t) refs (insert n0 () seen1) = rr’ by fs []
    \\ PairCases_on ‘rr’ \\ fs [] \\ rveq \\ fs []
    \\ asm_rewrite_tac [size_of_append_eq,size_of_def,lookup_insert]
    \\ rename [‘if t1 = t2 then SOME () else NONE’]
    \\ Cases_on ‘t1 = t2’ \\ fs []
    THEN1 (‘bb = h::t’by (fs [sane_timestamps_def] \\ res_tac \\ fs []) \\ fs [])
    \\ first_x_assum (qspec_then ‘v1_size (h::t)’ mp_tac)
    \\ impl_tac THEN1 fs [v_size_def,v_size_append]
    \\ disch_then (qspec_then ‘h::t’ mp_tac)
    \\ rewrite_tac []
    \\ disch_then (qspec_then ‘refs’ mp_tac)
    \\ rewrite_tac []
    \\ disch_then (qspecl_then [‘(insert t1 () seen1)’] mp_tac) \\ simp []
    \\ impl_tac THEN1
     (fs [lookup_insert] \\ rw []
      \\ first_x_assum match_mp_tac
      \\ fs [v_size_def,v_size_append])
    \\ strip_tac
    \\ once_rewrite_tac [insert_insert]
    \\ simp []
    \\ ‘∃w. size_of lims (h::t) refs (insert t2 () (insert t1 () seen1)) = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ntac 4 (pop_assum mp_tac)
    \\ rewrite_tac [size_of_append_eq]
    \\ rpt strip_tac \\ fs [] \\ rfs []
    \\ ‘∃v. size_of lims bb w1 w2 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs [])
  \\ ‘size_of lims ([h] ++ t) refs seen1 = (k0,refs1,seen2)’ by fs []
  \\ pop_assum mp_tac
  \\ simp [Once size_of_append_eq]
  \\ strip_tac
  \\ ‘size_of lims (bb ++ h::t) refs = size_of lims (bb ++ ([h] ++ t)) refs’
      by rewrite_tac [APPEND]
  \\ asm_rewrite_tac [] \\ rewrite_tac [size_of_append_eq]
  \\ ‘∃v. size_of lims t refs seen1 = v’ by fs []
  \\ PairCases_on ‘v’ \\ fs []
  \\ rename [‘_ = (n7,refs7,seen7)’]
  \\ ‘∃w. size_of lims [h] refs7 seen7 = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs [] \\ rveq
  \\ reverse (Cases_on ‘IS_SOME (lookup x1 seen7)’) \\ fs []
  THEN1
   (qpat_x_assum ‘size_of lims t refs seen1 = (n7,refs7,seen7)’ assume_tac
    \\ drule size_of_seen_ignored
    \\ disch_then drule
    \\ asm_rewrite_tac []
    \\ strip_tac \\ simp []
    \\ Cases_on ‘refs7 = refs’ \\ fs []
    THEN1
     (first_x_assum (qspec_then ‘v1_size [h]’ mp_tac)
      \\ impl_tac THEN1 (Cases_on ‘t’ \\ fs [v_size_def])
      \\ disch_then (qspec_then ‘[h]’ mp_tac) \\ rewrite_tac []
      \\ disch_then (qspec_then ‘refs’ mp_tac) \\ rewrite_tac []
      \\ disch_then (qspec_then ‘seen7’ mp_tac) \\ simp []
      \\ impl_tac
      THEN1
       (reverse conj_tac THEN1 (Cases_on ‘h’ \\ fs [])
        \\ rveq \\ rpt strip_tac
        \\ first_x_assum match_mp_tac \\ fs []
        \\ rw [] \\ fs [] \\ fs [v_size_def,v_size_append])
      \\ rewrite_tac [size_of_append_eq]
      \\ fs [UNCURRY])
    \\ last_x_assum (qspec_then ‘size refs7’ mp_tac)
    \\ impl_keep_tac
    THEN1
     (match_mp_tac (GEN_ALL size_of_refs_shirnk)
      \\ asm_exists_tac \\ fs [])
    \\ disch_then (qspec_then ‘refs7’ mp_tac) \\ rewrite_tac []
    \\ disch_then drule
    \\ reverse impl_tac
    THEN1 (rewrite_tac [size_of_append_eq] \\ fs [UNCURRY])
    \\ fs []
    \\ reverse (rpt strip_tac)
    THEN1 (Cases_on ‘h’ \\ fs [])
    THEN1
     (imp_res_tac size_of_refs_subspt
      \\ fs [refs_in_def,subspt_lookup]
      \\ metis_tac [])
    \\ first_x_assum match_mp_tac \\ fs []
    \\ reverse IF_CASES_TAC
    THEN1 (fs [] \\ rfs [])
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac ‘size refs7’ \\ fs []
    \\ Cases_on ‘refs'' = refs7’ \\ fs [])
  \\ first_x_assum (qspec_then ‘v1_size t’ mp_tac)
  \\ impl_tac THEN1 (Cases_on ‘t’ \\ fs [v_size_def])
  \\ disch_then (qspec_then ‘t’ mp_tac) \\ rewrite_tac []
  \\ disch_then (qspec_then ‘refs’ mp_tac) \\ rewrite_tac []
  \\ disch_then (qspec_then ‘seen1’ mp_tac) \\ simp []
  \\ impl_tac
  THEN1
   (reverse conj_tac THEN1 (Cases_on ‘h’ \\ fs [])
    \\ rpt strip_tac
    \\ first_x_assum match_mp_tac \\ fs []
    \\ rw [] \\ fs [v_size_append,v_size_def])
  \\ rewrite_tac [size_of_append_eq]
  \\ ‘∃v. size_of lims t refs (insert x1 () seen1) = v’ by fs []
  \\ PairCases_on ‘v’ \\ fs []
  \\ ‘∃w. size_of lims bb v1 v2 = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ qsuff_tac
       ‘size_of lims ([h] ++ bb ++ []) v1 v2 =
        size_of lims (bb ++ [h] ++ []) v1 v2’
  THEN1 (rewrite_tac [APPEND_NIL] \\ rewrite_tac [size_of_append_eq] \\ fs [UNCURRY])
  \\ first_x_assum match_mp_tac \\ fs []
  \\ reverse (rpt strip_tac)
  THEN1 (Cases_on ‘h’ \\ fs [])
  THEN1
   (pop_assum kall_tac
    \\ drule size_of_refs_subspt
    \\ fs [subspt_lookup,refs_in_def] \\ metis_tac [])
  \\ rw []
  THEN1 metis_tac [size_of_refs_shirnk]
  \\ fs [v_size_def,v_size_append]
QED

Definition array_vals_def:
  array_vals (ValueArray vs) = vs ∧
  array_vals _ = []
End

Definition array_len_def:
  array_len lims (ValueArray vs) = LENGTH vs + 1 ∧
  array_len lims (ByteArray _ b) = LENGTH b DIV (arch_size lims DIV 8) + 2
End

Triviality size_of_ref:
  size_of lims [RefPtr r] refs seen =
    case lookup r refs of
    | NONE => (0,refs,seen)
    | SOME x =>
        let (n,refs',seen') = size_of lims (array_vals x) (delete r refs) seen in
          (n + array_len lims x,refs',seen')
Proof
  fs [size_of_def]
  \\ Cases_on ‘lookup r refs’ \\ fs []
  \\ Cases_on ‘x’ \\ fs [size_of_def,array_vals_def,array_len_def]
QED

Theorem size_of_lemma_ref:
  ∀refs qs r x seen1 k0 refs1 seen2.
    size_of lims qs refs seen1 = (k0,refs1,seen2) ∧
    (∀refs' xs ys zs seen.
       (if refs ≠ refs' then size refs' < size refs else
          v1_size (xs ++ ys ++ zs) ≤ v1_size qs) ∧
       sane_timestamps bs ∧ refs_in refs' bs ∧
       set (all_blocks xs ++ all_blocks ys ++ all_blocks zs) SUBSET set bs ⇒
       size_of lims (xs ++ ys ++ zs) refs' seen =
       size_of lims (ys ++ xs ++ zs) refs' seen) ∧
    lookup r refs = SOME x ∧ lookup r refs1 = NONE ∧
    sane_timestamps bs ∧ refs_in refs bs ∧
    set (all_blocks qs) SUBSET set bs ⇒
    size_of lims qs refs seen1 =
      let (n1,refs1,seen1) = size_of lims (array_vals x ++ qs) (delete r refs) seen1 in
        (n1 + array_len lims x,refs1,seen1)
Proof
  gen_tac
  \\ completeInduct_on ‘size refs’
  \\ simp [Once PULL_FORALL]
  \\ completeInduct_on ‘v1_size qs’
  \\ rpt strip_tac \\ rpt var_eq_tac
  \\ Cases_on ‘qs’ \\ fs []
  THEN1 (fs [size_of_def] \\ rw [] \\ fs [] \\ rfs [])
  \\ Cases_on ‘t = []’
  THEN1
   (rveq \\ Cases_on ‘h’ \\ fs [size_of_ref]
    \\ fs [size_of_def,AllCaseEqs()]
    \\ TRY (Cases_on ‘l’ \\ fs [size_of_def])
    \\ rveq \\ fs [] \\ rfs []
    THEN1
     (Cases_on ‘IS_SOME (lookup n0 seen1)’ \\ fs [] \\ rfs []
      \\ ‘∃b. size_of lims (h::t) refs (insert n0 () seen1) = b’ by fs []
      \\ PairCases_on ‘b’ \\ fs [] \\ rveq
      \\ first_x_assum (qspec_then ‘v1_size (h::t)’ mp_tac)
      \\ impl_tac THEN1 fs [v_size_def]
      \\ disch_then (qspec_then ‘h::t’ mp_tac)
      \\ rewrite_tac []
      \\ disch_then (qspecl_then [‘refs’] mp_tac) \\ simp []
      \\ disch_then (qspecl_then [‘r’,‘x’,‘insert n0 () seen1’] mp_tac) \\ simp []
      \\ impl_tac
      THEN1
       (rpt strip_tac
        \\ first_x_assum match_mp_tac \\ fs []
        \\ rw [] \\ fs [v_size_def])
      \\ rewrite_tac [size_of_append_eq,size_of_def]
      \\ fs [UNCURRY])
    \\ Cases_on ‘n = r’ \\ fs [] \\ rveq
    THEN1
     (rewrite_tac [size_of_append_eq,size_of_def,lookup_delete] \\ fs []
      \\ fs [UNCURRY])
    \\ ‘∃rr. size_of lims (array_vals x') (delete n refs) seen1 = rr’ by fs []
    \\ PairCases_on ‘rr’ \\ fs [] \\ rveq \\ fs []
    \\ asm_rewrite_tac [size_of_append_eq,size_of_ref,lookup_insert,lookup_delete]
    \\ simp []
    \\ last_x_assum (qspec_then ‘size (delete n refs)’ mp_tac)
    \\ impl_tac THEN1 (imp_res_tac lookup_zero \\ fs [size_delete])
    \\ disch_then (qspec_then ‘delete n refs’ mp_tac)
    \\ rewrite_tac []
    \\ disch_then drule
    \\ disch_then (qspecl_then [‘r’,‘x’] mp_tac) \\ simp []
    \\ impl_tac
    THEN1
     (fs [lookup_delete] \\ reverse (rw [])
      THEN1
       (fs [refs_in_def] \\ res_tac
        \\ Cases_on ‘x'’ \\ fs [array_vals_def] \\ metis_tac [])
      THEN1 (fs [refs_in_def,lookup_delete] \\ metis_tac [])
      \\ first_x_assum match_mp_tac \\ fs []
      \\ rw [] \\ fs []
      THEN1 (imp_res_tac lookup_zero \\ fs [size_delete])
      THEN1 (‘lookup n refs = lookup n (delete n refs)’ by metis_tac []
        \\ fs [lookup_delete] \\ rfs [])
      THEN1
       (match_mp_tac LESS_TRANS \\ asm_exists_tac \\ fs []
        \\ imp_res_tac lookup_zero \\ fs [size_delete])
      \\ imp_res_tac lookup_zero \\ fs [size_delete] \\ rfs [])
    \\ simp [Once delete_delete]
    \\ rewrite_tac [size_of_append_eq]
    \\ fs [UNCURRY])
  \\ ‘size_of lims ([h] ++ t) refs seen1 = (k0,refs1,seen2)’ by fs []
  \\ pop_assum mp_tac
  \\ simp [Once size_of_append_eq]
  \\ strip_tac
  \\ ‘size_of lims (array_vals x ++ h::t) =
      size_of lims (array_vals x ++ ([h] ++ t))’
        by rewrite_tac [APPEND]
  \\ asm_rewrite_tac [] \\ rewrite_tac [size_of_append_eq]
  \\ ‘∃v. size_of lims t refs seen1 = v’ by fs []
  \\ PairCases_on ‘v’ \\ fs []
  \\ rename [‘_ = (n7,refs7,seen7)’]
  \\ ‘∃w. size_of lims [h] refs7 seen7 = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs [] \\ rveq
  \\ reverse (Cases_on ‘lookup r refs7’) \\ fs []
  THEN1
   (qpat_x_assum ‘size_of lims t refs seen1 = (n7,refs7,seen7)’ assume_tac
    \\ drule size_of_refs_ignored
    \\ disch_then drule
    \\ asm_rewrite_tac []
    \\ strip_tac \\ simp []
    \\ fs [] \\ rveq
    \\ Cases_on ‘refs7 = refs’ \\ fs []
    THEN1
     (first_x_assum (qspec_then ‘v1_size [h]’ mp_tac)
      \\ impl_tac THEN1 (Cases_on ‘t’ \\ fs [v_size_def])
      \\ disch_then (qspec_then ‘[h]’ mp_tac) \\ rewrite_tac []
      \\ disch_then (qspec_then ‘refs’ mp_tac) \\ rewrite_tac []
      \\ disch_then (qspecl_then [‘r’,‘x’,‘seen7’] mp_tac) \\ simp []
      \\ impl_tac
      THEN1
       (reverse conj_tac THEN1 (Cases_on ‘h’ \\ fs [])
        \\ rveq \\ rpt strip_tac
        \\ first_x_assum match_mp_tac \\ fs []
        \\ rw [] \\ fs [] \\ fs [v_size_def,v_size_append])
      \\ rewrite_tac [size_of_append_eq]
      \\ fs [UNCURRY])
    \\ last_x_assum (qspec_then ‘size refs7’ mp_tac)
    \\ impl_keep_tac
    THEN1
     (match_mp_tac (GEN_ALL size_of_refs_shirnk)
      \\ asm_exists_tac \\ fs [])
    \\ disch_then (qspec_then ‘refs7’ mp_tac) \\ rewrite_tac []
    \\ disch_then drule
    \\ disch_then (qspecl_then [‘r’,‘x’] mp_tac) \\ rewrite_tac []
    \\ reverse impl_tac
    THEN1 (rewrite_tac [size_of_append_eq] \\ fs [UNCURRY])
    \\ fs []
    \\ reverse (rpt strip_tac)
    THEN1 (Cases_on ‘h’ \\ fs [])
    THEN1
     (imp_res_tac size_of_refs_subspt
      \\ fs [refs_in_def,subspt_lookup]
      \\ metis_tac [])
    \\ first_x_assum match_mp_tac \\ fs []
    \\ reverse IF_CASES_TAC
    THEN1 (fs [] \\ rfs [])
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac ‘size refs7’ \\ fs []
    \\ Cases_on ‘refs'' = refs7’ \\ fs [])
  \\ first_x_assum (qspec_then ‘v1_size t’ mp_tac)
  \\ impl_tac THEN1 (Cases_on ‘t’ \\ fs [v_size_def])
  \\ disch_then (qspec_then ‘t’ mp_tac) \\ rewrite_tac []
  \\ disch_then (qspec_then ‘refs’ mp_tac) \\ rewrite_tac []
  \\ disch_then (qspecl_then [‘r’,‘x’,‘seen1’] mp_tac) \\ simp []
  \\ impl_tac
  THEN1
   (reverse conj_tac THEN1 (Cases_on ‘h’ \\ fs [])
    \\ rpt strip_tac
    \\ first_x_assum match_mp_tac \\ fs []
    \\ rw [] \\ fs [v_size_append,v_size_def])
  \\ rewrite_tac [size_of_append_eq]
  \\ ‘∃v. size_of lims t (delete r refs) seen1 = v’ by fs []
  \\ PairCases_on ‘v’ \\ fs []
  \\ ‘∃w. size_of lims (array_vals x) v1 v2 = w’ by fs []
  \\ PairCases_on ‘w’ \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ qsuff_tac
       ‘size_of lims ([h] ++ array_vals x ++ []) v1 v2 =
        size_of lims (array_vals x ++ [h] ++ []) v1 v2’
  THEN1 (rewrite_tac [APPEND_NIL] \\ rewrite_tac [size_of_append_eq] \\ fs [UNCURRY])
  \\ first_x_assum match_mp_tac \\ fs []
  \\ reverse (rpt strip_tac)
  THEN1 (Cases_on ‘x’ \\ fs [array_vals_def,refs_in_def] \\ metis_tac [])
  THEN1 (Cases_on ‘h’ \\ fs [])
  THEN1
   (pop_assum kall_tac
    \\ drule size_of_refs_subspt
    \\ fs [subspt_lookup,refs_in_def,lookup_delete] \\ metis_tac [])
  \\ pop_assum kall_tac
  \\ drule size_of_refs_size
  \\ strip_tac
  \\ ‘size (delete r refs) < size refs’ by
        (imp_res_tac lookup_zero \\ fs [size_delete])
  \\ ‘size v1 < size refs’ by fs []
  \\ IF_CASES_TAC \\ fs []
QED

Theorem size_of_swap:
  ∀bs lims refs xs ys zs seen.
    sane_timestamps bs ∧ refs_in refs bs ∧
    set (all_blocks xs ++ all_blocks ys ++ all_blocks zs) SUBSET set bs ⇒
    size_of lims (xs ++ ys ++ zs) refs seen =
    size_of lims (ys ++ xs ++ zs) refs seen
Proof
  gen_tac \\ Cases_on ‘sane_timestamps bs’ \\ fs []
  \\ gen_tac \\ gen_tac
  \\ completeInduct_on ‘size refs’
  \\ fs [PULL_FORALL]
  \\ completeInduct_on ‘v1_size (xs ++ ys ++ zs)’
  \\ fs [PULL_FORALL]
  \\ rw [] \\ fs [AND_IMP_INTRO]
  \\ Cases_on ‘xs’ \\ fs []
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac ‘size_of lims (h::(ys ++ t ++ zs)) refs seen’
  \\ conj_tac
  THEN1
   (qsuff_tac ‘size_of lims (t ++ ys ++ zs) refs seen =
               size_of lims (ys ++ t ++ zs) refs seen’
    THEN1
     (once_rewrite_tac [size_of_cons]
      \\ fs [size_of_def,UNCURRY]
      \\ metis_tac [PAIR,PAIR_EQ])
    \\ first_x_assum match_mp_tac
    \\ fs [v_size_def]
    \\ fs [sane_timestamps_def,all_blocks_def]
    \\ rpt gen_tac
    \\ Cases_on ‘h’ \\ fs [])
  \\ qsuff_tac
     ‘size_of lims (h::ys ++ (t ++ zs)) refs seen =
      size_of lims (ys ++ [h] ++ (t ++ zs)) refs seen’
  THEN1 (fs [] \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC])
  \\ qabbrev_tac ‘ts = (t ++ zs)’
  \\ qabbrev_tac ‘xs2 = ys ++ [h]’
  \\ simp [size_of_append_eq]
  \\ ‘∃q. size_of lims ts refs seen = q’ by fs []
  \\ PairCases_on ‘q’ \\ fs []
  \\ AP_TERM_TAC \\ fs [Abbr‘xs2’]
  \\ rename [‘size_of lims ts refs seen = (n,refs1,seen1)’]
  \\ drule size_of_refs_shirnk
  \\ Cases_on ‘refs ≠ refs1’ \\ fs []
  THEN1
   (rw [] \\ last_x_assum drule
    \\ disch_then (qspecl_then [‘[h]’,‘ys’,‘[]’] mp_tac) \\ fs []
    \\ disch_then match_mp_tac
    \\ conj_tac
    THEN1
     (imp_res_tac size_of_refs_subspt
      \\ fs [refs_in_def,subspt_lookup] \\ metis_tac [])
    \\ Cases_on ‘h’ \\ fs []) \\ fs []
  \\ var_eq_tac
  \\ qsuff_tac ‘size_of lims ([h] ++ ys) refs seen1 =
                size_of lims (ys ++ [h]) refs seen1’
  THEN1 fs []
  \\ Cases_on ‘h’
  \\ TRY (rename [‘Block x1 x2 x3’] \\ Cases_on ‘x3’)
  \\ TRY (rewrite_tac [size_of_append_eq] \\ simp [size_of_def] \\ NO_TAC)
  (* only non-empty Block and RefPtr cases left *)
  THEN1
   (rewrite_tac [size_of_append_eq] \\ simp [size_of_def]
    \\ Cases_on ‘IS_SOME (lookup x1 seen1)’ \\ fs []
    THEN1
     (‘∃q. size_of lims ys refs seen1 = q’ by fs []
      \\ PairCases_on ‘q’ \\ fs []
      \\ imp_res_tac size_of_seen_pres \\ fs []
      \\ fs [subspt_lookup]
      \\ Cases_on ‘lookup x1 seen1’ \\ fs [])
    \\ ‘∃q. size_of lims ys refs seen1 = q’ by fs []
    \\ PairCases_on ‘q’ \\ fs []
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (drule size_of_seen_ignored
      \\ disch_then drule \\ fs []
      \\ strip_tac
      \\ ‘∃w. size_of lims (h::t') q1 (insert x1 () q2) = w’ by fs []
      \\ PairCases_on ‘w’ \\ fs []
      \\ ‘∃v. size_of lims (h::t') refs (insert x1 () seen1) = v’ by fs []
      \\ PairCases_on ‘v’ \\ fs []
      \\ ‘∃x. size_of lims ys v1 v2 = x’ by fs []
      \\ PairCases_on ‘x’ \\ fs []
      \\ last_x_assum (qspecl_then [‘ys’,‘h::t'’,‘[]’,‘refs’,‘insert x1 () seen1’] mp_tac)
      \\ impl_tac THEN1 fs [v_size_def,v_size_append]
      \\ rewrite_tac [APPEND_NIL]
      \\ asm_rewrite_tac [size_of_append_eq] \\ fs [])
    \\ qsuff_tac ‘size_of lims ys refs seen1 =
       size_of lims (ys ++ [Block x1 x2 (h::t')]) refs seen1’
    THEN1
     (fs [] \\ disch_then kall_tac
      \\ simp [Once size_of_append_eq]
      \\ fs [size_of_def])
    \\ asm_rewrite_tac [size_of_append_eq,size_of_def,EVAL “IS_SOME NONE”]
    \\ drule size_of_lemma
    \\ rename [‘Block x1 x2 (x3::x4)’]
    \\ disch_then (qspecl_then [‘x2’,‘x1’,‘bs’,‘x3::x4’] mp_tac)
    \\ impl_tac
    THEN1
     (fs [SUBSET_DEF] \\ rw [] \\ fs []
      \\ first_x_assum match_mp_tac \\ fs []
      \\ fs [v_size_append,v_size_def])
    \\ first_assum (qspecl_then [‘x3::x4’,‘ys’,‘[]’,‘refs’,‘insert x1 () seen1’] mp_tac)
    \\ impl_tac THEN1 fs [v_size_def,v_size_append]
    \\ rewrite_tac [APPEND_NIL]
    \\ rewrite_tac [size_of_append_eq]
    \\ fs [UNCURRY])
  \\ rewrite_tac [size_of_append_eq] \\ simp [size_of_def]
  \\ rename [‘lookup r’]
  \\ Cases_on ‘lookup r refs’ \\ fs []
  THEN1
   (‘∃q. size_of lims ys refs seen1 = q’ by fs []
    \\ PairCases_on ‘q’ \\ fs []
    \\ imp_res_tac size_of_refs_pres \\ fs [])
  \\ ‘∃q. size_of lims ys refs seen1 = q’ by fs []
  \\ PairCases_on ‘q’ \\ fs []
  \\ reverse (Cases_on ‘lookup r q1’) \\ fs []
  THEN1
   (drule size_of_refs_ignored
    \\ disch_then drule \\ fs []
    \\ strip_tac \\ rveq
    \\ Cases_on ‘x’ \\ fs []
    \\ ‘∃w. size_of lims l (delete r q1) q2 = w’ by fs []
    \\ PairCases_on ‘w’ \\ fs []
    \\ ‘∃v. size_of lims l (delete r refs) seen1 = v’ by fs []
    \\ PairCases_on ‘v’ \\ fs []
    \\ ‘∃x. size_of lims ys v1 v2 = x’ by fs []
    \\ PairCases_on ‘x’ \\ fs []
    \\ first_x_assum (qspecl_then [‘delete r refs’,‘ys’,‘l’,‘[]’,‘seen1’] mp_tac)
    \\ impl_tac THEN1
     (fs [] \\ rpt strip_tac
      THEN1 (imp_res_tac lookup_zero \\ fs [size_delete])
      THEN1 (fs [refs_in_def,lookup_delete] \\ metis_tac [])
      \\ fs [array_vals_def,refs_in_def] \\ res_tac)
    \\ rewrite_tac [APPEND_NIL] \\ asm_rewrite_tac [size_of_append_eq] \\ fs [])
  \\ qsuff_tac ‘size_of lims ys refs seen1 =
                size_of lims (ys ++ [RefPtr r]) refs seen1’
  THEN1
   (fs [] \\ disch_then kall_tac
    \\ simp [Once size_of_append_eq]
    \\ fs [size_of_def])
  \\ asm_rewrite_tac [size_of_append_eq,size_of_def]
  \\ drule size_of_lemma_ref
  \\ disch_then (qspecl_then [‘bs’,‘r’] mp_tac) \\ simp []
  \\ impl_tac
  THEN1
   (fs [SUBSET_DEF] \\ rw [] \\ fs []
    \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [v_size_append,v_size_def])
  \\ first_assum (qspecl_then [‘delete r refs’,‘array_vals x’,‘ys’,‘[]’,‘seen1’] mp_tac)
  \\ impl_tac THEN1
   (fs [] \\ rpt strip_tac
    THEN1 (imp_res_tac lookup_zero \\ fs [size_delete])
    THEN1 (fs [refs_in_def,lookup_delete] \\ metis_tac [])
    \\ Cases_on ‘x’ \\ fs [array_vals_def,refs_in_def] \\ res_tac)
  \\ rewrite_tac [APPEND_NIL]
  \\ rewrite_tac [size_of_append_eq]
  \\ Cases_on ‘x’ \\ fs [array_vals_def,array_len_def]
  \\ fs [size_of_def]
  \\ fs [UNCURRY] \\ rw [] \\ fs []
QED

Theorem size_of_perm_bs:
  ∀xs ys lims bs refs seen.
    PERM xs ys ∧ sane_timestamps bs ∧
    refs_in refs bs ∧ set (all_blocks xs) ⊆ set bs ⇒
    size_of lims xs refs seen =
    size_of lims ys refs seen
Proof
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ simp [GSYM PULL_FORALL,PERM_RTC]
  \\ ho_match_mp_tac RTC_INDUCT \\ rw []
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac ‘size_of lims xs' refs seen’
  \\ reverse conj_tac
  THEN1
   (fs [PULL_FORALL,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ asm_exists_tac \\ fs []
    \\ fs [PERM_SINGLE_SWAP_DEF]
    \\ rveq \\ fs [all_blocks_append])
  \\ qpat_x_assum ‘∀x. _’ kall_tac
  \\ fs [PERM_SINGLE_SWAP_DEF]
  \\ rveq \\ fs []
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [size_of_append_eq]
  \\ simp [] \\ AP_TERM_TAC
  \\ qsuff_tac ‘size_of lims (x2 ++ x3 ++ []) refs seen =
                size_of lims (x3 ++ x2 ++ []) refs seen’
  THEN1 fs [APPEND_NIL]
  \\ match_mp_tac size_of_swap
  \\ asm_exists_tac \\ fs []
  \\ fs [all_blocks_append]
QED

Definition all_bs_refs_def:
  all_bs_refs refs = FLAT (MAP (all_blocks o array_vals) (toList refs))
End

Theorem refs_in_all_bs_refs:
  ∀refs. refs_in refs (all_bs_refs refs)
Proof
  rw [refs_in_def,SUBSET_DEF,all_bs_refs_def,MEM_FLAT]
  \\ qexists_tac ‘all_blocks vals’
  \\ rw [MEM_MAP]
  \\ qexists_tac ‘ValueArray vals’
  \\ rw [array_vals_def,MEM_toList]
  \\ asm_exists_tac \\ simp []
QED

Theorem size_of_perm_gen:
  ∀xs ys lims refs seen.
    PERM xs ys ∧
    sane_timestamps (all_bs_refs refs ++ all_blocks xs) ⇒
    size_of lims xs refs seen =
    size_of lims ys refs seen
Proof
  rw [] \\ irule size_of_perm_bs
  \\ simp []
  \\ asm_exists_tac \\ fs []
  \\ qspec_then ‘refs’ assume_tac refs_in_all_bs_refs
  \\ fs [refs_in_def]
  \\ rw [] \\ first_x_assum drule
  \\ rw [] \\ irule SUBSET_TRANS
  \\ asm_exists_tac \\ fs []
QED

Theorem sane_timestamps_cons:
  ∀x xs. sane_timestamps (x::xs) ⇔
         (sane_timestamps xs ∧
          ∀ts tag tag' vl vl'.
            x = Block ts tag vl ∧
            MEM (Block ts tag' vl') xs ⇒
            tag = tag' ∧ vl = vl')
Proof
  rw [] \\ EQ_TAC
  \\ rpt disch_tac
  >- (conj_tac >- (fs [sane_timestamps_def] \\ metis_tac [])
      \\ rpt gen_tac \\ disch_tac \\ fs []
      \\ last_x_assum (assume_tac o ONCE_REWRITE_RULE [sane_timestamps_def])
      \\ first_x_assum irule \\ qexists_tac ‘ts’ \\ rw [])
  \\ fs [sane_timestamps_def]
  \\ rpt gen_tac \\ disch_tac \\ fs []
  >- (rveq \\ fs [])
  \\ metis_tac []
QED

Theorem sane_timestamps_PERM_eq:
  ∀xs ys. PERM xs ys ⇒ sane_timestamps xs = sane_timestamps ys
Proof
  rw [] \\  EQ_TAC \\ pop_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘ys’,‘xs’]
  \\ ho_match_mp_tac PERM_STRONG_IND \\ rw []
  >- (ONCE_REWRITE_TAC [sane_timestamps_cons]
      \\ conj_tac >- fs [sane_timestamps_cons]
      \\ rpt gen_tac \\ disch_tac \\ fs []
      \\ first_x_assum (irule o el 2 o CONJUNCTS o ONCE_REWRITE_RULE [sane_timestamps_cons])
      \\ metis_tac [MEM_PERM])
  >- (REWRITE_TAC [sane_timestamps_cons]
      \\ ONCE_REWRITE_TAC [GSYM CONJ_ASSOC]
      \\ conj_tac >- fs [sane_timestamps_cons]
      \\ conj_tac
      >- (pop_assum mp_tac
          \\ REWRITE_TAC [sane_timestamps_cons]
          \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
          \\ rpt gen_tac
          \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
          \\ first_x_assum drule \\ disch_then irule
          \\ rw [] \\ metis_tac [MEM_PERM])
      \\ pop_assum mp_tac
      \\ REWRITE_TAC [sane_timestamps_cons]
      \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
      \\ rpt gen_tac
      \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
      \\ reverse (Cases_on ‘x = Block ts tag' vl'’)
      >- (fs [] \\ last_x_assum irule \\ metis_tac [MEM_PERM])
      \\ fs [])
  >- (ONCE_REWRITE_TAC [sane_timestamps_cons]
      \\ conj_tac >- fs [sane_timestamps_cons]
      \\ rpt gen_tac \\ disch_tac \\ fs []
      \\ first_x_assum (irule o el 2 o CONJUNCTS o ONCE_REWRITE_RULE [sane_timestamps_cons])
      \\ metis_tac [MEM_PERM])
  \\ REWRITE_TAC [sane_timestamps_cons]
  \\ ONCE_REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ conj_tac >- fs [sane_timestamps_cons]
  \\ conj_tac
  >- (pop_assum mp_tac
      \\ REWRITE_TAC [sane_timestamps_cons]
      \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
      \\ rpt gen_tac
      \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
      \\ first_x_assum drule \\ disch_then irule
      \\ rw [] \\ metis_tac [MEM_PERM])
  \\ pop_assum mp_tac
  \\ REWRITE_TAC [sane_timestamps_cons]
  \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  \\ rpt gen_tac
  \\ disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  \\ reverse (Cases_on ‘x = Block ts tag' vl'’)
  >- (fs [] \\ last_x_assum irule \\ metis_tac [MEM_PERM])
  \\ fs []
QED

Theorem sane_timestamps_PERM:
  ∀xs ys. PERM xs ys ∧ sane_timestamps xs ⇒ sane_timestamps ys
Proof
  rw[] \\ drule sane_timestamps_PERM_eq \\ gs[]
QED

(* sane_heap is a more simple interface for sane_timestamps and all the appending and permutation in it *)
Definition sane_heap_def:
  sane_heap refs xs = sane_timestamps (all_bs_refs refs ++ all_blocks xs)
End

Theorem all_blocks_PERM:
  ∀xs ys. PERM xs ys ⇒ PERM (all_blocks xs) (all_blocks ys)
Proof
  ho_match_mp_tac PERM_STRONG_IND \\ rw[all_blocks_def]
  \\ ONCE_REWRITE_TAC [all_blocks_cons] \\ simp [PERM_APPEND_IFF]
  \\ ONCE_REWRITE_TAC [all_blocks_cons] \\ simp [PERM_APPEND_IFF]
  >- (qmatch_goalsub_abbrev_tac ‘a ++ b ++ c’ \\ irule PERM_TRANS
      \\ qexists_tac ‘b ++ a ++ c’ \\ simp [PERM_APPEND_IFF,APPEND_PERM_SYM])
  \\ metis_tac[PERM_TRANS]
QED

Theorem sane_timestamps_APPEND_left:
  ∀xs ys. sane_timestamps (xs ++ ys) ⇒ sane_timestamps xs
Proof
  simp[sane_timestamps_def]
  \\ ntac 9 strip_tac
  \\ first_x_assum irule
  \\ qexists_tac ‘ts’
  \\ rw []
QED

Theorem sane_timestamps_APPEND_right:
  ∀xs ys. sane_timestamps (xs ++ ys) ⇒ sane_timestamps ys
Proof
  rw[] \\ first_x_assum (mp_then Any mp_tac sane_timestamps_PERM)
  \\ disch_then (qspec_then ‘ys ++ xs’ mp_tac)
  \\ impl_tac >- simp[APPEND_PERM_SYM]
  \\ metis_tac [sane_timestamps_APPEND_left]
QED

Theorem sane_timestamps_APPEND:
  ∀xs ys. sane_timestamps (xs ++ ys) ⇒ sane_timestamps xs ∧ sane_timestamps ys
Proof
  metis_tac [sane_timestamps_APPEND_right,sane_timestamps_APPEND_left]
QED

Theorem sane_heap_PERM_eq:
  ∀s xs ys. PERM xs ys ⇒ (sane_heap s xs ⇔ sane_heap s ys)
Proof
  rw[sane_heap_def] \\ irule sane_timestamps_PERM_eq
  \\ qmatch_goalsub_abbrev_tac ‘PERM (a ++ b) (a ++ c)’
  \\ irule PERM_TRANS
  \\ irule_at Any APPEND_PERM_SYM
  \\ qexists_tac ‘c ++ a’
  \\ simp [PERM_APPEND_IFF,APPEND_PERM_SYM]
  \\ drule all_blocks_PERM \\ simp []
QED

Theorem sane_heap_PERM:
  ∀s xs ys. PERM xs ys ∧ sane_heap s xs ⇒ sane_heap s ys
Proof
  rw[] \\ drule sane_heap_PERM_eq \\ metis_tac[]
QED

Theorem sane_heap_block_cons:
  ∀refs x xs ts tag vl. sane_heap refs (Block ts tag vl::xs) ⇔
         (sane_heap refs (vl ++ xs) ∧
          ∀tag' vl'.
            MEM (Block ts tag' vl') (all_bs_refs refs ++ all_blocks (xs ++ vl)) ⇒
             tag = tag' ∧ vl = vl')
Proof
  rw[sane_heap_def]
  \\ ONCE_REWRITE_TAC [all_blocks_cons,all_blocks_append]
  \\ qmatch_goalsub_abbrev_tac ‘sane_timestamps (refs1 ++ x1::xs1)’
  \\ ‘PERM (refs1 ++ (x1::xs1)) (x1::(xs1 ++ refs1))’
     by simp[APPEND_PERM_SYM]
  \\ dxrule_then (ONCE_REWRITE_TAC o single) sane_timestamps_PERM_eq
  \\ ‘PERM (refs1 ++ xs1) (xs1 ++ refs1)’
     by simp[APPEND_PERM_SYM]
  \\ dxrule_then (ONCE_REWRITE_TAC o single) sane_timestamps_PERM_eq
  \\ UNABBREV_ALL_TAC
  \\ EQ_TAC
  \\ strip_tac
  >- (gs[sane_timestamps_cons]
      \\ ntac 3 strip_tac
      \\ first_x_assum irule \\ simp[])
  \\ gs [sane_timestamps_cons]
  \\ ntac 3 strip_tac
  \\ first_x_assum irule \\ simp[]
QED

Theorem sane_heap_APPEND_right:
  ∀s xs ys. sane_heap s (xs ++ ys) ⇒ sane_heap s ys
Proof
  rw [sane_heap_def,all_blocks_append]
  \\ qmatch_asmsub_abbrev_tac ‘sane_timestamps (a ++ b ++ c)’
  \\ ntac 3 (pop_assum kall_tac)
  \\ irule sane_timestamps_APPEND_left
  \\ qexists_tac ‘b’
  \\ first_x_assum (mp_then Any irule sane_timestamps_PERM)
  \\ SIMP_TAC (std_ss++permLib.PERM_SIMPLE_ss) []
QED

Theorem sane_heap_APPEND_left:
  ∀s xs ys. sane_heap s (xs ++ ys) ⇒ sane_heap s xs
Proof
  rw[] \\ irule sane_heap_APPEND_right
  \\ irule_at Any sane_heap_PERM
  \\ metis_tac [PERM_APPEND]
QED

Theorem sane_heap_cons_simp:
  (∀refs x xs. sane_heap refs (Number  x::xs) = sane_heap refs xs)
∧ (∀refs x xs. sane_heap refs (CodePtr x::xs) = sane_heap refs xs)
∧ (∀refs x xs. sane_heap refs (Word64  x::xs) = sane_heap refs xs)
∧ (∀refs x xs. sane_heap refs (RefPtr  x::xs) = sane_heap refs xs)
Proof
  rw[sane_heap_def,sane_timestamps_def]
QED

Theorem size_of_perm:
  ∀xs ys lims refs seen.
    PERM xs ys ∧
    sane_heap refs xs ⇒
    size_of lims xs refs seen =
    size_of lims ys refs seen
Proof
  rw [sane_heap_def] \\ metis_tac [size_of_perm_gen]
QED

Theorem all_blocks_MEM_aux:
  ∀vs x y.
    MEM x (all_blocks vs) ∧
    MEM y (all_blocks [x])
    ⇒ MEM y (all_blocks vs)
Proof
  ho_match_mp_tac all_blocks_ind
  \\ rw[all_blocks_def]
  \\ gs[all_blocks_def]
  \\ metis_tac []
QED

Theorem all_blocks_v_size:
  ∀vs x. MEM x (all_blocks vs) ⇒ v_size x ≤ v1_size vs
Proof
  ho_match_mp_tac all_blocks_ind
  \\ rw[all_blocks_def,v_size_def]
  \\ gs[all_blocks_def,v_size_def]
  \\ first_x_assum drule \\ rw[]
QED

Theorem all_blocks_no_self_containment:
  ∀vs ts tag. ¬MEM (Block ts tag vs) (all_blocks vs)
Proof
  rw[] \\ goal_assum (mp_then Any assume_tac all_blocks_v_size o SIMP_RULE std_ss [])
  \\ gs[v_size_def]
QED

Theorem sane_heap_block_MEM:
  ∀refs ts tag vs.
    sane_heap refs [Block ts tag vs]
    ⇒ ∀tag0 vs0. ¬MEM (Block ts tag0 vs0) (all_blocks vs)
Proof
  rw[sane_heap_block_cons] \\ CCONTR_TAC \\ gs[]
  \\ first_x_assum (qspecl_then [‘tag0’,‘vs0’] assume_tac)
  \\ gs[] \\ rveq \\ gs[all_blocks_no_self_containment]
QED

Definition no_ptrs_list_def:
  (no_ptrs_list [] = T) ∧
  (no_ptrs_list [RefPtr p] = F) ∧
  (no_ptrs_list [Block ts tag l] = no_ptrs_list l) ∧
  (no_ptrs_list [x] = T) ∧
  (no_ptrs_list (v::vs) = (no_ptrs_list [v] ∧ no_ptrs_list vs))
Termination
  WF_REL_TAC `(inv_image (measure v1_size) I)`
End

Theorem size_of_seen_no_ptrs_list_ignore:
  ∀lims vs refs seen ts n refs1 seen1.
    (size_of lims vs refs seen = (n,refs1,seen1)) ∧
    (∀tag l. ¬MEM (Block ts tag l) (all_blocks vs)) ∧
    no_ptrs_list vs
    ⇒ (size_of lims vs refs (insert ts () seen) = (n,refs1,insert ts () seen1))
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def,no_ptrs_list_def]
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  >- (rpt (pairarg_tac \\ fs []) \\ rveq
      \\ gs[all_blocks_cons_simp,MEM_APPEND,FORALL_AND_THM,no_ptrs_list_def]
      \\ res_tac \\ gs[] \\ rveq \\ gs[])
  >- (Cases_on ‘ts = ts'’ \\ gs[lookup_insert]
      >-(Cases_on ‘lookup ts' seen’ \\ gs[]
         \\ rpt (pairarg_tac \\ fs []) \\ rveq
         \\ gs[MEM_APPEND,FORALL_AND_THM])
      >- (Cases_on ‘lookup ts seen’ \\ gs[]
          \\ rpt (pairarg_tac \\ fs []) \\ rveq
          \\ first_x_assum drule
          \\ simp[insert_swap]))
QED

Theorem sane_heap_cons_split:
  ∀refs x xs.
    sane_heap refs (x::xs) ⇒ sane_heap refs [x] ∧ sane_heap refs xs
Proof
  rw[]
  >- (irule sane_heap_APPEND_left \\ simp[] \\ asm_exists_tac \\ simp[])
  >- (irule sane_heap_APPEND_right \\ qexists_tac ‘[x]’ \\ simp[])
QED

Theorem sane_timestamps_smaller:
  ∀l l'.
    sane_timestamps l ∧
    (∀x. MEM x l' ⇒ MEM x l)
    ⇒ sane_timestamps l'
Proof
  Induct \\ rw[sane_timestamps_def,sane_timestamps_cons]
  \\ first_assum dxrule \\ first_assum dxrule
  \\ rw[] \\ metis_tac []
QED

Theorem toList_subspt_smaller:
  ∀refs1 refs2 x.
    subspt refs1 refs2 ∧
    MEM x (toList refs1)
    ⇒ MEM x (toList refs2)
Proof
  rw[MEM_toList,subspt_lookup] \\ metis_tac[]
QED

Theorem all_bs_refs_subspt_smaller:
  ∀refs1 refs2 x.
    subspt refs1 refs2 ∧
    MEM x (all_bs_refs refs1)
    ⇒ MEM x (all_bs_refs refs2)
Proof
  rw[all_bs_refs_def]
  \\ drule toList_subspt_smaller
  \\ qmatch_goalsub_abbrev_tac ‘MEM _ l1’
  \\ qmatch_goalsub_abbrev_tac ‘MAP _ l2’
  \\ rw[] \\ gs[MEM_FLAT,MEM_MAP] \\ rveq
  \\ metis_tac[]
QED

Theorem sane_heap_refs_subspt:
  ∀refs1 vs refs2.
    subspt refs2 refs1 ∧
    sane_heap refs1 vs
    ⇒ sane_heap refs2 vs
Proof
  rw[sane_heap_def]
  \\ irule sane_timestamps_smaller
  \\ first_x_assum (irule_at Any)
  \\ simp[MEM_APPEND] \\ rw[]
  \\ metis_tac[all_bs_refs_subspt_smaller]
QED

Theorem size_of_seen_ts_cases:
  ∀lims vs refs seen n refs1 seen1 ts tag x xs.
    size_of lims vs refs seen = (n,refs1,seen1) ∧
    IS_SOME(lookup ts seen1)
    ⇒ IS_SOME(lookup ts seen) ∨
      ∃tag l. MEM (Block ts tag l) (all_blocks vs) ∨
              MEM (Block ts tag l) (all_bs_refs refs)
Proof
  ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw[] \\ simp[]
  >- (rpt (pairarg_tac \\ fs []) \\ rveq
      \\ simp[all_blocks_cons_simp]
      \\ metis_tac[size_of_refs_subspt,all_bs_refs_subspt_smaller])
  >- (Cases_on ‘lookup r refs’ \\ gs[] \\ Cases_on ‘x’ \\ gs[]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ first_x_assum drule \\ rw[] \\ simp[]
      >- (simp[all_bs_refs_def,MEM_FLAT,MEM_MAP,MEM_toList]
          \\ metis_tac[array_vals_def])
      >- (gs[all_bs_refs_def,MEM_FLAT,MEM_MAP,MEM_toList]
          \\ Cases_on ‘y’ \\ gs[array_vals_def] \\ rveq
          \\ Cases_on ‘k = r’ \\ gs[lookup_delete]
          \\ metis_tac[array_vals_def]))
  >- (rpt (pairarg_tac \\ fs []) \\ rveq \\ gs[]
      \\ first_x_assum drule \\ rw[] \\ simp[]
      >- metis_tac[lookup_insert]
      >- metis_tac[]
      >- metis_tac[])
QED

val _ = export_theory();
