(*
  Pure functions for the List module.
*)
Theory mllist
Libs
  preamble
Ancestors
  indexedLists[qualified] toto[qualified]
  sorting mergesort

(* ===== TODO: TO BE PORTED TO HOL (better theorems for mergesort_tail) ===== *)
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc))
Proof
  ho_match_mp_tac merge_tail_ind
  \\ rpt strip_tac
  \\ fs[merge_tail_def]
  >- (simp[REV_REVERSE_LEM] \\ metis_tac[])
  >- (simp[REV_REVERSE_LEM] \\ metis_tac[])
  >- (
      rw[]
      \\ fs[]
      \\ metis_tac[]
    )
QED

Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst))
Proof
  ho_match_mp_tac mergesortN_tail_ind
  \\ reverse (rw[])
  >- (
      reverse (rw[Once $ mergesortN_tail_def])
      >- (
        gvs[]
        \\ simp[merge_tail_MEM]
        \\ `DIV2 length ≤ length` by (
            fs[DIV2_def]
            \\ qspecl_then [`length`, `2`] assume_tac DIV_LESS
            \\ `0 < length /\ 1 < 2 ` by fs[]
            \\ fs[arithmeticTheory.LT_IMP_LE]
          )
        \\ simp[TAKE_DROP_SWAP]
        \\ metis_tac[MEM_APPEND, TAKE_TAKE_T, TAKE_DROP]
      )
      \\ EVERY_CASE_TAC
      \\ rw[mergesortN_tail_def, sort2_tail_def, sort3_tail_def]
      \\ metis_tac[]
    )
    \\ rw[mergesortN_tail_def, sort2_tail_def, sort3_tail_def]
    \\ metis_tac[]
QED

Theorem sort3_tail_sort3:
  !negate R x y z. sort3_tail negate R x y z =
    (if negate then REVERSE(sort3 R x y z) else sort3 R x y z)
Proof
  simp[sort3_tail_def, sort3_def]
  \\ rw[]
  \\ fs[]
QED

Theorem sort2_tail_sort2:
  !negate R x y. sort2_tail negate R x y =
    (if negate then REVERSE(sort2 R x y) else sort2 R x y)
Proof
  simp[sort2_tail_def, sort2_def]
  \\ rw[]
  \\ fs[]
QED

Theorem mergetail_merge:
  !negate R xs ys acc.
     merge_tail negate R xs ys acc =
     (if negate then REVERSE (merge (\x y. ¬ R x y) xs ys) ++ acc
      else REVERSE (merge R xs ys) ++ acc)
Proof
  ho_match_mp_tac merge_tail_ind
  \\ rw[merge_tail_def, merge_def, REV_REVERSE_LEM, merge_empty]
  \\ fs[]
QED

Theorem merge_tail_acc:
  ∀negate R xs ys acc acc'. merge_tail negate R xs ys (acc ++ acc')
    = (merge_tail negate R xs ys acc) ++ acc'
Proof
  ho_match_mp_tac merge_tail_ind
  \\ rw[merge_tail_def, REV_REVERSE_LEM, merge_empty]
QED

Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l
Proof
  simp[mergesort_tail_def, mergesortN_tail_MEM]
QED

Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc)
Proof
  ho_match_mp_tac merge_tail_ind
  \\ fs[merge_tail_def]
  \\ reverse (rpt strip_tac)
  >- (
      rw[]
      >- (
        gvs[]
        \\ `PERM (x::(xs ++ y::ys ++ acc)) (xs ++ y::ys ++ x::acc)` by (
            rename1 `PERM (x::(mid ++ acc)) (mid ++ x::acc)`
            \\ match_mp_tac CONS_PERM
            \\ rw[]
          )
        \\ qspecl_then [ `(x::(xs ⧺ y::ys ⧺ acc))`,
                         `(xs ++ y::ys ++ x::acc)`,
                         `(merge_tail negate R xs (y::ys) (x::acc))`
            ] assume_tac PERM_TRANS
        \\ fs[]
      )
      >- (
          `PERM (x::(xs ++ y::ys ++ acc)) (x::(xs ++ ys ++ y::acc))` by simp[PERM_TO_APPEND_SIMPS]
          \\ qspecl_then [ `(x::(xs ++ y::ys ++ acc))`,
                           `(x::(xs ++ ys ++ y::acc))`,
                           `(merge_tail (R x y) R (x::xs) ys (y::acc))`
              ] assume_tac PERM_TRANS
          \\ fs[]
        )
    )
    \\ simp[REV_REVERSE_LEM]
    \\ pure_rewrite_tac [GSYM APPEND_ASSOC, GSYM CONS_APPEND]
    \\ match_mp_tac CONS_PERM
    \\ simp[PERM_APPEND_IFF]
QED

Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y)
Proof
  rw[sort2_tail_def]
  \\ `[y;x] = (REVERSE [x;y])` by rw[]
  \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
QED

Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z)
Proof
  reverse (rw[sort3_tail_def])
  >- (
      `[z;y;x] = REVERSE [x;y;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[x;y;z] = REVERSE [z;y;x]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
      \\ `PERM ([z;y] ++ [x]) ([y;z] ++ [x])` suffices_by rw[]
      \\ `PERM [z;y] [y;z]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;z] = REVERSE [z;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `PERM ([x;y] ++ [z]) ([y;x] ++ [z])` suffices_by rw[]
      \\ `PERM [x;y] [y;x]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;x] = REVERSE [x;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[z;x;y] = REVERSE [y;x;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
      \\ `PERM ([x;y] ++ [z]) ([y;x] ++ [z])` suffices_by rw[]
      \\ `PERM [x;y] [y;x]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;x] = REVERSE [x;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[z;y] = REVERSE [y;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
    )
QED

Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l)
Proof
  ho_match_mp_tac mergesortN_tail_ind
  \\ reverse(rw[])
  \\ fs[]
  >- (
      rw[Once $ mergesortN_tail_def]
      >- (Cases_on `l` \\ fs[])
      >- (
          Cases_on `l`
          \\ fs[]
          \\ Cases_on `t`
          \\ fs[]
          \\ simp[sort2_tail_PERM]
        )
      >- (
          Cases_on `l`
              \\ fs[]
              \\ Cases_on `t`
              \\ fs[]
              \\ Cases_on `t'`
              \\ fs[]
              \\ simp[sort2_tail_PERM, sort3_tail_PERM]
        )
      >- (
          fs[]
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) merge_tail_PERM
          \\ rw[]
          \\ irule PERM_FUN_SPLIT
          \\ irule_at (Pos last) (iffRL PERM_SYM)
          \\ first_x_assum (irule_at Any)
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) PERM_APPEND
          \\ irule PERM_FUN_SPLIT
          \\ irule_at (Pos last) (iffRL PERM_SYM)
          \\ first_x_assum (irule_at Any)
          \\ simp[TAKE_DROP_SWAP]
          \\ `DIV2 len < len` by (simp[DIV2_def])
          \\ `DIV2 len + (len - (DIV2 len)) = len` by (
                simp[DIV2_def, SUB_LEFT_ADD]
                \\ rw[]
                \\ gvs[DIV2_def]
             )
          \\ fs[]
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) PERM_APPEND
          \\ `TAKE len l = (TAKE (DIV2 len) l ⧺ DROP (DIV2 len) (TAKE len l))` suffices_by metis_tac[PERM_REFL]
          \\ simp[LIST_EQ_REWRITE]
          \\ conj_tac
          >- (
              Cases_on `len <= (LENGTH l)`
              \\ fs[]
              >- (
                  Cases_on `DIV2 len <= LENGTH l`
                  \\ `!n l. n > LENGTH l ==> (LENGTH (TAKE n l) = LENGTH l)` by (
                      rw[]
                      \\ `TAKE n l' = l'` by fs[]
                      \\ pop_assum (fn x => pure_rewrite_tac [x])
                      \\ REFL_TAC
                    )
                  \\ fs[]
                )
            )
          >- (
              rw[EL_APPEND]
              >- (
                  Cases_on `(DIV2 len) <= (LENGTH l)`
                  \\ fs[EL_TAKE]
                  >- (
                      `!n l. n > LENGTH l ==> (TAKE n l = l)` by rw[]
                      \\ `DIV2 len > LENGTH l` by fs[]
                      \\ simp[EL_TAKE]
                    )
                )
              >- (
                  Cases_on `DIV2 len <= LENGTH l`
                  \\ fs[]
                  >- (simp[EL_DROP])
                  >- (
                      (* False case. *)
                      `LENGTH (TAKE (DIV2 len) l) = (LENGTH l)` by (
                        `TAKE (DIV2 len) l = l` by fs[]
                        \\ pop_assum (fn x => rw [x])
                        )
                      \\ `x >= LENGTH l` by fs[]
                      \\ `x < LENGTH l` by (
                           `l = TAKE len l` by fs[]
                            \\ pop_assum (fn x => pure_rewrite_tac [Once $ x])
                            \\ rfs[]
                        )
                      \\ fs[]
                    )
                )
            )
        )
    )
  \\ rw[mergesortN_tail_def]
  \\ simp[sort2_tail_PERM, sort3_tail_PERM]
QED
(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

Definition sort_def:
  sort = mergesort$mergesort_tail
End

Theorem sort_thm:
  !R l. sort R l = mergesort$mergesort_tail R l
Proof
  rw[sort_def]
QED

Theorem sort_SORTED:
  !R L. transitive R ∧ total R ==> sorting$SORTED R (sort R L)
Proof
  simp[sort_def, mergesort_tail_def, mergesortN_correct, mergesortN_sorted]
QED

Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L
Proof
  simp[sort_def, mergesort_tail_MEM]
QED

Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L)
Proof
  simp[sort_def, mergesort_tail_def]
  \\ rpt strip_tac
  \\ `L = TAKE (LENGTH L) L` by rw[]
  \\ pop_assum (fn x => pure_rewrite_tac [Once $ x])
  \\ rw[mergesortN_tail_PERM]
QED

Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l
Proof
  simp[sort_def, PERM_LENGTH, sort_PERM]
QED

Theorem sort_SORTS:
  !R. (transitive R /\ total R) ==> SORTS sort R
Proof
  simp[SORTS_DEF, sort_PERM, sort_SORTED]
QED

Theorem sort_set[simp]:
  set (sort R ls) = set ls
Proof
  rw[EXTENSION]
QED

Definition getItem_def:
  (getItem [] = NONE) /\
  (getItem (h::t) = SOME(h, t))
End

Definition nth_def:
  nth l i = EL i l
End

Definition take_def:
  take l i = TAKE i l
End

Definition drop_def:
  drop l i = DROP i l
End

Definition takeUntil_def:
  (takeUntil p [] = []) /\
  (takeUntil p (x::xs) = if p x then [] else x :: takeUntil p xs)
End

Definition dropUntil_def:
  (dropUntil p [] = []) /\
  (dropUntil p (x::xs) = if p x then x::xs else dropUntil p xs)
End

Definition mapi_def:
  (mapi f (n: num) [] = []) /\
  (mapi f n (h::t) = (let y = f n h in (y::(mapi f (n + 1) t))))
End

Theorem MAPI_thm_gen[local]:
  ∀f l x. MAPi (\a. f (a + x)) l = mapi f x l
Proof
  Induct_on `l` \\ rw [MAPi_def, mapi_def] \\
  rw [o_DEF, ADD1] \\
  fs [] \\
  pop_assum (fn th => rw[GSYM th] ) \\
  rw[AC ADD_ASSOC ADD_COMM] \\
  match_mp_tac MAPi_CONG \\ rw[]
QED

Theorem MAPI_thm:
   !f l. MAPi f l = mapi f 0 l
Proof
  rw [(MAPI_thm_gen |> Q.SPECL[`f`,`l`,`0`]
  |> SIMP_RULE (srw_ss()++ETA_ss) [])]
QED

Definition mapPartial_def:
  (mapPartial f [] = []) /\
  (mapPartial f (h::t) = case (f h) of
    NONE => mapPartial f t
    |(SOME x) => x::mapPartial f t)
End

Theorem mapPartial_thm:
   !f l. mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))
Proof
  Induct_on `l` \\ rw [mapPartial_def] \\ Cases_on `f h` \\ rw [THE_DEF] \\ fs [IS_SOME_DEF]
QED

Theorem index_find_thm:
   !x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)
Proof
  Induct_on`l` \\ rw[INDEX_FIND_def]
QED

Theorem FIND_thm:
   (FIND f [] = NONE) ∧
   (∀h t. FIND f (h::t) = if f h then SOME h else FIND f t)
Proof
  rw[FIND_def,INDEX_FIND_def,index_find_thm]
QED

Definition partition_aux_def:
  (partition_aux f [] pos neg =
    (REVERSE pos, REVERSE neg)) /\
    (partition_aux f (h::t) pos neg = if f h then partition_aux f t (h::pos) neg
      else partition_aux f t pos (h::neg))
End

Definition partition_def:
  partition (f : 'a -> bool) l = partition_aux f l [] []
End

Theorem partition_aux_thm[local]:
  ∀f l l1 l2.
    partition_aux f l l1 l2 =
    (REVERSE l1++(FILTER f l), REVERSE l2++(FILTER ($~ o f) l))
Proof
  Induct_on `l` \\
  rw [partition_aux_def] \\
  rw [partition_aux_def]
QED

Theorem partition_pos_thm:
   !f l. FST (partition f l) = FILTER f l
Proof
  rw [partition_def, FILTER, partition_aux_thm]
QED

Theorem partition_neg_thm:
   !f l. SND (partition f l) = FILTER ($~ o f) l
Proof
  rw [partition_def, FILTER, partition_aux_thm]
QED

Definition foldl_def:
  (foldl f e [] = e) /\
  (foldl f e (h::t) = foldl f (f h e) t)
End

Definition foldli_aux_def:
  (foldli_aux f e n [] = e) /\
  (foldli_aux f e n (h::t) = foldli_aux f (f n h e) (SUC n) t)
End

Definition foldli_def:
  foldli f e l = foldli_aux f e 0 l
End

Theorem foldli_aux_thm[local]:
  ∀l f e n.  foldli_aux f e n l = FOLDRi (\n'. f (LENGTH l + n - (SUC n'))) e (REVERSE l)
Proof
  Induct_on `l` \\
  rw [foldli_aux_def] \\
  rw [FOLDRi_APPEND] \\
  rw [ADD1]
QED

Theorem foldl_intro:
  ∀xs x f. FOLDL f x xs = foldl (λx acc. f acc x) x xs
Proof
  Induct \\ fs [foldl_def]
QED

Theorem foldli_thm:
   !f e l. foldli f e l = FOLDRi (\n. f (LENGTH l - (SUC n))) e (REVERSE l)
Proof
  rw [foldli_def, foldli_aux_thm]
QED

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

Definition tabulate_aux_def:
  tabulate_aux n m f acc =
    let b = (n >= m) in
    if b then REVERSE acc
    else
      let v = f n in
      let n = n+1n in
      let acc = v::acc in
      tabulate_aux n m f acc
Termination
  wf_rel_tac`measure (λ(n,m,_,_). m-n)`
End

Definition tabulate_def:
  tabulate n f = let l = [] in tabulate_aux 0 n f l
End

Theorem tabulate_aux_GENLIST:
   ∀n m f acc. tabulate_aux n m f acc = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m-n)
Proof
  recInduct(theorem"tabulate_aux_ind") \\ rw[]
  \\ rw[Once tabulate_aux_def]
  >- ( `m - n = 0` by simp[] \\ rw[] )
  \\ Cases_on`m` \\ fs[]
  \\ rename1`SUC m - n` \\ `SUC m - n = SUC (m - n)` by simp[]
  \\ simp[GENLIST_CONS,FUNPOW,o_DEF,FUNPOW_SUC_PLUS]
  \\ simp[ADD1]
QED

Theorem tabulate_GENLIST:
   !n. tabulate n f = GENLIST f n
Proof
  rw[tabulate_def,tabulate_aux_GENLIST,FUNPOW_SUC_PLUS,o_DEF,ETA_AX]
QED

Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End

Theorem collate_equal_thm:
   !l. (!x. MEM x l ==> (f x x = EQUAL)) ==> (collate f l l = EQUAL)
Proof
  Induct_on `l` \\ rw [collate_def] \\ rw [collate_def]
QED

Theorem collate_short_thm:
   !f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l1 ≼ l2) ==>
        (collate f l1 l2 = LESS)
Proof
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
QED

Theorem collate_long_thm:
   !f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l2 ≼ l1) ==>
        (collate f l1 l2 = GREATER)
Proof
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
QED

Definition cpn_to_reln_def:
  cpn_to_reln f x1 x2 = (f x1 x2 = LESS)
End

Theorem collate_cpn_reln_thm:
   !f l1 l2. (!x1 x2. (f x1 x2 = EQUAL) <=>
    (x1 = x2)) ==> (cpn_to_reln (collate f) l1 l2 = LLEX (cpn_to_reln f) l1 l2)
Proof
  ho_match_mp_tac collate_ind \\ rw [collate_def, cpn_to_reln_def, LLEX_def] \\
  first_assum (qspecl_then [`h1`, `h1`] (fn th => assume_tac (GSYM th))) \\
  `(h1 = h1) = T` by DECIDE_TAC \\ rw[] \\`EQUAL ≠ LESS` by fs[] \\ rw[]
QED

(* from std_preludeLib *)
Definition LENGTH_AUX_def:
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))
End

Theorem LENGTH_AUX_THM = Q.prove(`
  !xs n. LENGTH_AUX xs n = LENGTH xs + n`,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];

Theorem list_compare_def =
  ternaryComparisonsTheory.list_compare_def

(* tail-recursive MAP *)

Definition map_rev'_def:
  map_rev' f [] acc = acc ∧
  map_rev' f (x :: xs) acc = map_rev' f xs (f x :: acc)
End

Definition map_rev_def:
  map_rev f xs = map_rev' f xs []
End

Theorem map_rev'_lemma[local]:
  ∀acc. map_rev' f xs acc = (map_rev' f xs []) ⧺ acc
Proof
  Induct_on ‘xs’
  >- rw[map_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[map_rev'_def]
  \\ first_assum $ once_rewrite_tac o single
  \\ rw[]
QED

Theorem map_rev_thm:
  map_rev f xs = REVERSE (MAP f xs)
Proof
  rw[map_rev_def]
  \\ Induct_on ‘xs’
  \\ rw[map_rev'_def, map_rev'_lemma]
QED

(* tail-recursive FILTER *)

Definition filter_rev'_def:
  filter_rev' P [] acc = acc ∧
  filter_rev' P (h::t) acc = if P h then filter_rev' P t (h::acc) else filter_rev' P t acc
End

Definition filter_rev_def:
  filter_rev P xs = filter_rev' P xs []
End

Theorem filter_rev'_lemma[local]:
  ∀acc. filter_rev' P xs acc = (filter_rev' P xs []) ⧺ acc
Proof
  Induct_on ‘xs’
  >- rw[filter_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[filter_rev'_def]
  \\ Cases_on ‘P h’
  >- (last_x_assum $ once_rewrite_tac o single
      \\ rw[])
  \\ metis_tac[]
QED

Theorem filter_rev_thm:
  filter_rev f xs = REVERSE (FILTER f xs)
Proof
  rw[filter_rev_def]
  \\ Induct_on ‘xs’
  >- rw[filter_rev'_def]
  \\ strip_tac
  \\ rw[filter_rev'_def, filter_rev'_lemma]
QED

(* tail-recursive FLAT *)

Definition flat_rev'_def:
  flat_rev' [] acc = acc ∧
  flat_rev' (x::xs) acc = flat_rev' xs (REV x acc)
End

Definition flat_rev_def:
  flat_rev xs = flat_rev' xs []
End

Theorem flat_rev'_lemma[local]:
  ∀acc. flat_rev' l acc = (flat_rev' l []) ⧺ acc
Proof
  Induct_on ‘l’
  >- rw[flat_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[flat_rev'_def]
  \\ first_assum $ once_rewrite_tac o single
  \\ rw[REV_REVERSE_LEM]
QED

Theorem flat_rev_thm:
  flat_rev xs = REVERSE (FLAT xs)
Proof
  rw[flat_rev_def]
  \\ Induct_on ‘xs’
  \\ rw[flat_rev'_def, flat_rev'_lemma, REV_REVERSE_LEM]
QED
