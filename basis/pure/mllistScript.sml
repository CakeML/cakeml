(*
  Pure functions for the List module.
*)
open preamble

val _ = new_theory"mllist"

val _ = set_grammar_ancestry ["indexedLists", "toto"]

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

val _ = export_theory()
