(*
  Converting sptree to vector
*)
Theory spt_to_vec
Ancestors
  mlvector
Libs
  preamble

Definition prepend_def:
  prepend n x xs = if n = 0:num then xs else prepend (n-1) x (x::xs)
End

Definition to_flat_def:
  to_flat n l acc =
    case l of
    | [] => REVERSE acc
    | ((m,x)::xs) => to_flat (m+1) xs (SOME x :: prepend (m-n) NONE acc)
End

Definition spt_to_vec_def:
  spt_to_vec t =
    Vector (to_flat 0 (toSortedAList t) [])
End

Definition vec_lookup_def:
  vec_lookup opt_vec n =
    if n < length opt_vec then sub opt_vec n else NONE
End

Triviality prepend_eq:
  ∀n x xs. prepend n x xs = REPLICATE n x ++ xs
Proof
  Induct \\ rewrite_tac [GSYM SNOC_REPLICATE, SNOC_APPEND]
  \\ fs [ADD1] \\ once_rewrite_tac [prepend_def] \\ fs []
QED

Triviality to_flat_lemma:
  ∀xs xs0 n.
    SORTED $< (MAP FST (xs0 ++ xs)) ∧ EVERY (λm. m < n) (MAP FST xs0) ∧
    (xs ≠ [] ⇒ n ≤ FST (HD xs)) ⇒
    ∃k. to_flat n xs (REVERSE $ GENLIST (ALOOKUP (xs0 ++ xs)) n) =
        GENLIST (ALOOKUP (xs0 ++ xs)) k ∧
        EVERY (λn. n < k) (MAP FST (xs0 ++ xs))
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [to_flat_def] \\ fs [prepend_eq]
  >- (rw [] \\ qexists_tac ‘n’ \\ fs [])
  \\ rw [] \\ PairCases_on ‘h’ \\ gvs []
  \\ last_x_assum $ qspecl_then [‘xs0 ++ [(h0,h1)]’,‘h0+1’] mp_tac
  \\ impl_tac >-
   (asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND,MAP_APPEND,MAP,FST,EVERY_APPEND]
    \\ fs [] \\ gvs [EVERY_MEM]
    \\ rw [] \\ res_tac \\ fs []
    \\ Cases_on ‘xs’ \\ fs []
    \\ fs [SORTED_APPEND_GEN]
    \\ gvs [less_sorted_eq])
  \\ qsuff_tac ‘(SOME h1:: (REPLICATE (h0 − n) NONE ++
                  REVERSE (GENLIST (ALOOKUP (xs0 ++ [(h0,h1)] ++ xs)) n))) =
      REVERSE (GENLIST (ALOOKUP (xs0 ++ [(h0,h1)] ++ xs)) (h0 + 1))’
  >- (strip_tac \\ fs [] \\ strip_tac \\ qexists_tac ‘k’ \\ fs [])
  \\ simp [GSYM ADD1,GENLIST,ALOOKUP_APPEND,AllCaseEqs(),
           ALOOKUP_NONE]
  \\ conj_tac
  >- (CCONTR_TAC \\ fs [EVERY_MEM] \\ res_tac \\ gvs [])
  \\ gvs [LESS_EQ_EXISTS]
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [GENLIST_APPEND] \\ fs []
  \\ once_rewrite_tac [GSYM SWAP_REVERSE] \\ fs []
  \\ rewrite_tac [REPLICATE_GENLIST,GENLIST_FUN_EQ]
  \\ fs [ALOOKUP_NONE]
  \\ fs [SORTED_APPEND_GEN]
  \\ gvs [less_sorted_eq]
  \\ CCONTR_TAC \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
QED

Theorem vec_lookup_num_man_to_vec:
  vec_lookup (spt_to_vec t) n = lookup n t
Proof
  fs [spt_to_vec_def,vec_lookup_def,length_def,sub_def]
  \\ ‘SORTED $< (MAP FST ([] ++ toSortedAList t))’ by fs [SORTED_toSortedAList]
  \\ drule to_flat_lemma
  \\ disch_then $ qspec_then ‘0’ mp_tac \\ fs []
  \\ strip_tac \\ fs [ALOOKUP_toSortedAList] \\ rw []
  \\ Cases_on ‘lookup n t’ \\ gvs []
  \\ gvs [GSYM ALOOKUP_toSortedAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ res_tac \\ fs []
QED

