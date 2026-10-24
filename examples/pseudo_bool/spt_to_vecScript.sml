(*
  Converting sptree to vector
*)
Theory spt_to_vec
Ancestors
  mlvector mllist
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
    if n < length opt_vec then sub_unsafe opt_vec n else NONE
End

Theorem prepend_eq[local]:
  ∀n x xs. prepend n x xs = REPLICATE n x ++ xs
Proof
  Induct \\ rewrite_tac [GSYM SNOC_REPLICATE, SNOC_APPEND]
  \\ fs [ADD1] \\ once_rewrite_tac [prepend_def] \\ fs []
QED

Theorem to_flat_lemma[local]:
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
  fs [spt_to_vec_def,vec_lookup_def,length_def,sub_unsafe_def]
  \\ ‘SORTED $< (MAP FST ([] ++ toSortedAList t))’ by fs [SORTED_toSortedAList]
  \\ drule to_flat_lemma
  \\ disch_then $ qspec_then ‘0’ mp_tac \\ fs []
  \\ strip_tac \\ fs [ALOOKUP_toSortedAList] \\ rw []
  \\ Cases_on ‘lookup n t’ \\ gvs []
  \\ gvs [GSYM ALOOKUP_toSortedAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ res_tac \\ fs []
QED

(* A finite map from num keys: an offset vector (Dense lo v maps lo + i to
   the i-th element of v), or a vector of pairs with strictly increasing
   keys. For maps whose keys form many disjoint dense runs, this generalises
   to a sorted vector of Dense segments: one segment is Dense, and one-entry
   segments are Sorted *)
Datatype:
  lmap = Dense num ('a option vector) | Sorted ((num # 'a) vector)
End

Definition bsearch_def:
  bsearch (v:(num # 'a) vector) n lo hi =
  if lo < hi then
    let mid = (lo + hi) DIV 2 in
    case sub_unsafe v mid of
      (k,x) =>
      if n = k then SOME x
      else if n < k then bsearch v n lo mid
      else bsearch v n (mid + 1) hi
  else NONE
Termination
  WF_REL_TAC ‘measure (λ(v,n,lo,hi). hi - lo)’
  \\ rpt strip_tac
  \\ gvs []
  \\ ‘lo ≤ (hi + lo) DIV 2 ∧ (hi + lo) DIV 2 < hi’ by simp [X_LE_DIV, DIV_LT_X]
  \\ decide_tac
End

Definition map_lookup_def:
  map_lookup m n =
  case m of
    Dense lo v =>
      if lo ≤ n ∧ n - lo < length v then sub_unsafe v (n - lo) else NONE
  | Sorted v => bsearch v n 0 (length v)
End

(* Drops the later entries of each key from a key-sorted list;
   the result is in decreasing key order *)
Definition sorted_dedup_def:
  sorted_dedup [] acc = acc ∧
  sorted_dedup ((k,x)::xs) acc =
  case acc of
    [] => sorted_dedup xs [(k,x)]
  | ((k',_)::_) =>
    if k = k' then sorted_dedup xs acc
    else sorted_dedup xs ((k,x)::acc)
End

Definition has_at_least_def:
  has_at_least k l =
  if k = 0n then T
  else
    case l of
      [] => F
    | (_::xs) => has_at_least (k - 1) xs
End

(* Dense when the span is at most twice the number of entries plus the
   length of rinds *)
Definition dense_ok_def:
  dense_ok m span rinds ⇔
  span ≤ 2 * m ∨ has_at_least (span - 2 * m) rinds
End

(* The map of the first entry per key of l *)
Definition mk_map_def:
  mk_map (rinds:num list) (l:(num # 'a) list) =
  case mllist$sort (λx y. FST x ≤ FST y) l of
    [] => Sorted (Vector [])
  | ((lo,x)::xs) =>
    case sorted_dedup xs [(lo,x)] of
      [] => Sorted (Vector [])
    | ((hi,y)::ys) =>
      let s = REVERSE ((hi,y)::ys) in
      if dense_ok (LENGTH s) (hi + 1 - lo) rinds
      then Dense lo (Vector (to_flat lo s []))
      else Sorted (Vector s)
End

Theorem to_flat_shift[local]:
  ∀xs n acc. to_flat (n + d) (MAP (λ(k,x). (k + d, x)) xs) acc = to_flat n xs acc
Proof
  Induct \\ once_rewrite_tac [to_flat_def] \\ simp [FORALL_PROD]
  \\ qx_genl_tac [‘m’,‘x’,‘n’,‘acc’]
  \\ first_x_assum $ qspecl_then [‘m + 1’,‘SOME x::prepend (m − n) NONE acc’] mp_tac
  \\ simp []
QED

Theorem ALOOKUP_sort[local]:
  ALOOKUP (sort (λx y. FST x ≤ FST y) (l:(num # 'a) list)) n = ALOOKUP l n
Proof
  ‘total (λx y:num # 'a. FST x ≤ FST y) ∧ transitive (λx y:num # 'a. FST x ≤ FST y)’
    by simp [total_def, transitive_def]
  \\ ‘STABLE mergesort (λx y:num # 'a. FST x ≤ FST y)’
    by simp [mergesortTheory.mergesort_STABLE_SORT]
  \\ fs [sortingTheory.STABLE_DEF, sort_thm]
  \\ simp [mergesortTheory.mergesort_tail_correct]
  \\ ‘∀ls. ALOOKUP (FILTER (λ(k,v). k = n) ls) n = ALOOKUP ls n’
    by simp [alistTheory.ALOOKUP_FILTER]
  \\ qpat_x_assum ‘∀p. _ ⇒ ∀l. FILTER p l = _’ $ qspec_then ‘λ(k,v). k = n’ mp_tac
  \\ simp [FORALL_PROD]
  \\ disch_then $ qspec_then ‘l’ strip_assume_tac
  \\ qpat_x_assum ‘∀ls. ALOOKUP _ _ = _’ (once_rewrite_tac o single o GSYM)
  \\ simp []
QED

Theorem SORTED_GT_REVERSE[local]:
  ∀l:num list. SORTED $> l ⇒ SORTED $< (REVERSE l)
Proof
  ‘transitive ($> : num -> num -> bool)’ by simp [transitive_def]
  \\ Induct \\ simp [SORTED_EQ]
  \\ rw [SORTED_APPEND, arithmeticTheory.transitive_LESS, MEM_REVERSE]
  \\ qpat_x_assum ‘∀y. MEM y l ⇒ _’ drule \\ simp []
QED

Theorem sorted_dedup_thm[local]:
  ∀xs acc.
    SORTED (λx y. FST x ≤ FST y) xs ∧ SORTED $> (MAP FST acc) ∧
    (acc ≠ [] ∧ xs ≠ [] ⇒ FST (HD acc) ≤ FST (HD xs)) ⇒
    SORTED $> (MAP FST (sorted_dedup xs acc)) ∧
    (∀k. MEM k (MAP FST (sorted_dedup xs acc)) ⇒
         MEM k (MAP FST acc) ∨ MEM k (MAP FST xs)) ∧
    ∀n:num. ALOOKUP (REVERSE (sorted_dedup xs acc)) n = ALOOKUP (REVERSE acc ++ xs) n
Proof
  recInduct sorted_dedup_ind \\ conj_tac
  >- simp [sorted_dedup_def]
  \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ ‘SORTED (λx y. FST x ≤ FST y) xs ∧ (xs ≠ [] ⇒ k ≤ FST (HD xs))’
    by (Cases_on ‘xs’ \\ gvs [])
  \\ namedCases_on ‘acc’ ["", "e rest"]
  >- gvs [sorted_dedup_def]
  \\ PairCases_on ‘e’ \\ rename1 ‘sorted_dedup (_::_) ((k0,v0)::_)’
  \\ Cases_on ‘k = k0’ \\ gvs [sorted_dedup_def]
  >- (
    rw [ALOOKUP_APPEND]
    >- (qpat_x_assum ‘∀k'. MEM _ _ ⇒ _’ drule \\ metis_tac [])
    \\ Cases_on ‘ALOOKUP (REVERSE rest) k’ \\ simp [])
  \\ conj_tac >- metis_tac []
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
QED

Theorem MAP_shift_unshift[local]:
  ∀s. EVERY (λk. (lo:num) ≤ k) (MAP FST s) ⇒
      MAP (λ(k,x). (k + lo, x)) (MAP (λ(k,x:'a). (k - lo, x)) s) = s
Proof
  Induct \\ simp [FORALL_PROD]
QED

Theorem ALOOKUP_MAP_shift[local]:
  ∀s0. ALOOKUP (MAP (λ(k,x:'a). (k + lo, x)) s0) n =
       if (lo:num) ≤ n then ALOOKUP s0 (n - lo) else NONE
Proof
  Induct \\ simp [FORALL_PROD] \\ rw [] \\ gvs []
QED

Theorem map_lookup_Dense[local]:
  SORTED $< (MAP FST s) ∧ EVERY (λk. lo ≤ k) (MAP FST s) ⇒
  map_lookup (Dense lo (Vector (to_flat lo s []))) n = ALOOKUP s n
Proof
  strip_tac
  \\ qabbrev_tac ‘s0 = MAP (λ(k,x:'a). (k - lo, x)) s’
  \\ ‘MAP (λ(k,x). (k + lo, x)) s0 = s’ by simp [Abbr ‘s0’, MAP_shift_unshift]
  \\ ‘to_flat lo s [] = to_flat 0 s0 []’ by (
    qpat_x_assum ‘MAP _ s0 = s’ (SUBST1_TAC o GSYM)
    \\ qspecl_then [‘s0’,‘0’,‘[]’] mp_tac (Q.INST [‘d’ |-> ‘lo’] to_flat_shift)
    \\ simp [])
  \\ ‘SORTED $< (MAP FST s0)’ by (
    qpat_x_assum ‘SORTED _ _’ mp_tac \\ qpat_x_assum ‘EVERY _ _’ mp_tac
    \\ simp [Abbr ‘s0’, MAP_MAP_o, sortingTheory.sorted_map]
    \\ rw [] \\ irule sortingTheory.SORTED_weaken
    \\ qexists_tac ‘inv_image $< FST’
    \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD, relationTheory.inv_image_def]
    \\ rw [] \\ res_tac \\ decide_tac)
  \\ qspecl_then [‘s0’,‘[]’,‘0’] mp_tac to_flat_lemma
  \\ simp [] \\ strip_tac
  \\ qpat_x_assum ‘MAP _ s0 = s’ (SUBST1_TAC o GSYM)
  \\ simp [map_lookup_def, length_def, sub_unsafe_def, ALOOKUP_MAP_shift]
  \\ rw [] \\ simp [ALOOKUP_NONE]
  \\ strip_tac \\ fs [EVERY_MEM] \\ res_tac \\ decide_tac
QED

Theorem bsearch_thm[local]:
  ∀v n lo hi.
    v = Vector s ∧ SORTED $< (MAP FST s) ∧ hi ≤ LENGTH s ⇒
    bsearch v n lo hi =
    if ∃i. lo ≤ i ∧ i < hi ∧ FST (EL i s) = n then ALOOKUP s n else NONE
Proof
  recInduct bsearch_ind \\ rpt strip_tac \\ gvs []
  \\ ‘∀i j. i < j ∧ j < LENGTH s ⇒ FST (EL i s) < FST (EL j s)’ by (
    qpat_x_assum ‘SORTED _ _’ mp_tac
    \\ simp [sortingTheory.SORTED_EL_LESS, arithmeticTheory.transitive_LESS, EL_MAP])
  \\ once_rewrite_tac [bsearch_def]
  \\ Cases_on ‘lo < hi’ \\ simp []
  \\ qabbrev_tac ‘mid = (hi + lo) DIV 2’
  \\ ‘lo ≤ mid ∧ mid < hi’ by simp [Abbr ‘mid’, X_LE_DIV, DIV_LT_X]
  \\ fs [sub_unsafe_def]
  \\ Cases_on ‘EL mid s’ \\ rename1 ‘EL mid s = (k,x)’
  \\ ‘ALL_DISTINCT (MAP FST s)’ by (
    irule sortingTheory.SORTED_ALL_DISTINCT \\ qexists_tac ‘$<’
    \\ simp [relationTheory.irreflexive_def, arithmeticTheory.transitive_LESS])
  \\ ‘MEM (k,x) s’ by (simp [MEM_EL] \\ qexists_tac ‘mid’ \\ simp [])
  \\ Cases_on ‘n = k’
  >- (simp [ALOOKUP_ALL_DISTINCT_MEM] \\ qexists_tac ‘mid’ \\ simp [])
  \\ Cases_on ‘n < k’ \\ simp []
  >- (
    ‘(∃i. lo ≤ i ∧ i < mid ∧ FST (EL i s) = n) ⇔
     (∃i. lo ≤ i ∧ i < hi ∧ FST (EL i s) = n)’ suffices_by simp []
    \\ eq_tac \\ rw []
    >- (qexists_tac ‘i’ \\ simp [])
    \\ qexists_tac ‘i’ \\ simp []
    \\ CCONTR_TAC \\ Cases_on ‘i = mid’ >- gvs []
    \\ qpat_x_assum ‘∀i j. _’ (qspecl_then [‘mid’,‘i’] mp_tac) \\ simp [])
  \\ ‘(∃i. mid + 1 ≤ i ∧ i < hi ∧ FST (EL i s) = n) ⇔
      (∃i. lo ≤ i ∧ i < hi ∧ FST (EL i s) = n)’ suffices_by simp []
  \\ eq_tac \\ rw []
  >- (qexists_tac ‘i’ \\ simp [])
  \\ qexists_tac ‘i’ \\ simp []
  \\ CCONTR_TAC \\ Cases_on ‘i = mid’ >- gvs []
  \\ qpat_x_assum ‘∀i j. _’ (qspecl_then [‘i’,‘mid’] mp_tac) \\ simp []
QED

Theorem map_lookup_Sorted[local]:
  SORTED $< (MAP FST s) ⇒ map_lookup (Sorted (Vector s)) n = ALOOKUP s n
Proof
  rw [map_lookup_def, length_def]
  \\ qspecl_then [‘Vector s’,‘n’,‘0’,‘LENGTH s’] mp_tac bsearch_thm
  \\ rw [] \\ fs [ALOOKUP_NONE, MEM_MAP, MEM_EL]
QED

Theorem map_lookup_empty:
  map_lookup (Sorted (Vector [])) n = NONE
Proof
  EVAL_TAC
QED

Theorem map_lookup_mk_map:
  map_lookup (mk_map rinds l) n = ALOOKUP l n
Proof
  once_rewrite_tac [GSYM ALOOKUP_sort]
  \\ ‘SORTED (λx y. FST x ≤ FST y) (sort (λx y. FST x ≤ FST y) l)’
    by (irule sort_SORTED \\ simp [total_def, transitive_def])
  \\ simp [mk_map_def]
  \\ qabbrev_tac ‘sl = sort (λx y. FST x ≤ FST y) l’
  \\ namedCases_on ‘sl’ ["", "p xs"]
  >- simp [map_lookup_empty]
  \\ PairCases_on ‘p’ \\ simp [] \\ rename1 ‘sorted_dedup xs [(lo,v0)]’
  \\ ‘transitive (λx y:num # 'a. FST x ≤ FST y)’ by simp [transitive_def]
  \\ qpat_x_assum ‘SORTED _ (_::_)’ mp_tac \\ simp [SORTED_EQ] \\ strip_tac
  \\ qspecl_then [‘xs’,‘[(lo,v0)]’] mp_tac sorted_dedup_thm
  \\ impl_tac >- (Cases_on ‘xs’ \\ fs [])
  \\ strip_tac
  \\ qabbrev_tac ‘d = sorted_dedup xs [(lo,v0)]’
  \\ ‘(if lo = n then SOME v0 else ALOOKUP xs n) = ALOOKUP (REVERSE d) n’ by simp []
  \\ pop_assum SUBST1_TAC
  \\ qpat_x_assum ‘∀n. ALOOKUP _ _ = _’ kall_tac
  \\ ‘SORTED $< (MAP FST (REVERSE d))’ by simp [MAP_REVERSE, SORTED_GT_REVERSE]
  \\ ‘EVERY (λk. lo ≤ k) (MAP FST (REVERSE d))’ by (
    simp [MAP_REVERSE, EVERY_REVERSE, EVERY_MEM] \\ rpt strip_tac
    \\ res_tac \\ gvs [MEM_MAP] \\ res_tac)
  \\ namedCases_on ‘d’ ["", "q ys"]
  >- simp [map_lookup_empty]
  \\ PairCases_on ‘q’ \\ rw []
  >- (irule map_lookup_Dense \\ fs [])
  \\ irule map_lookup_Sorted \\ fs []
QED

