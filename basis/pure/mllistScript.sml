open preamble

val _ = new_theory"mllist"

val _ = set_grammar_ancestry ["indexedLists", "toto"]

val tl_def = Define`
  (tl [] = []) /\
  (tl (h::t) = t)`;


val getItem_def = Define`
  (getItem [] = NONE) /\
  (getItem (h::t) = SOME(h, t))`;


val nth_def = Define`
  nth l i = EL i l`;


val take_def = Define`
  take l i = TAKE i l`;


val drop_def = Define`
  drop l i = DROP i l`;


val mapi_def = Define `
  (mapi f (n: num) [] = []) /\
  (mapi f n (h::t) = (f n h)::(mapi f (n + 1) t))`

val MAPI_thm_gen = Q.prove (
  `!f l x. MAPi (\a. f (a + x)) l = mapi f x l`,
  Induct_on `l` \\ rw [MAPi_def, mapi_def] \\
  rw [o_DEF, ADD1] \\
  fs [] \\
  pop_assum (fn th => rw[GSYM th] ) \\
  rw[AC ADD_ASSOC ADD_COMM] \\
  match_mp_tac MAPi_CONG \\ rw[]
);

val MAPI_thm = Q.store_thm (
  "MAPI_thm",
  `!f l. MAPi f l = mapi f 0 l`,
  rw [(MAPI_thm_gen |> Q.SPECL[`f`,`l`,`0`]
  |> SIMP_RULE (srw_ss()++ETA_ss) [])]
);


val mapPartial_def = Define`
  (mapPartial f [] = []) /\
  (mapPartial f (h::t) = case (f h) of
    NONE => mapPartial f t
    |(SOME x) => x::mapPartial f t)`;

val mapPartial_thm = Q.store_thm (
  "mapPartial_thm",
  `!f l. mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  Induct_on `l` \\ rw [mapPartial_def] \\ Cases_on `f h` \\ rw [THE_DEF] \\ fs [IS_SOME_DEF]
);


val index_find_thm = Q.store_thm (
  "index_find_thm",
  `!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)`,
  Induct_on`l` \\ rw[INDEX_FIND_def]
);


val FIND_thm = Q.store_thm(
  "FIND_thm",
  `(FIND f [] = NONE) ∧
   (∀h t. FIND f (h::t) = if f h then SOME h else FIND f t)`,
  rw[FIND_def,INDEX_FIND_def,index_find_thm]
);

val partition_aux_def = Define`
  (partition_aux f [] pos neg =
    (REVERSE pos, REVERSE neg)) /\
    (partition_aux f (h::t) pos neg = if f h then partition_aux f t (h::pos) neg
      else partition_aux f t pos (h::neg))`;

val partition_def = Define`
  partition (f : 'a -> bool) l = partition_aux f l [] []`;

val partition_aux_thm = Q.prove(
  `!f l l1 l2. partition_aux f l l1 l2 = (REVERSE l1++(FILTER f l), REVERSE l2++(FILTER ($~ o f) l))`,
  Induct_on `l` \\
  rw [partition_aux_def] \\
  rw [partition_aux_def]
);

val partition_pos_thm = Q.store_thm(
  "partition_pos_thm",
  `!f l. FST (partition f l) = FILTER f l`,
  rw [partition_def, FILTER, partition_aux_thm]
);

val partition_neg_thm = Q.store_thm(
  "partition_neg_thm",
  `!f l. SND (partition f l) = FILTER ($~ o f) l`,
  rw [partition_def, FILTER, partition_aux_thm]
);

val foldl_aux_def = Define`
  (foldl_aux f e n [] = e) /\
  (foldl_aux f e n (h::t) = foldl_aux f (f h e) (SUC n) t)`;

val foldl_def = Define`
  foldl f e l = foldl_aux f e 0 l`;


val foldli_aux_def = Define`
  (foldli_aux f e n [] = e) /\
  (foldli_aux f e n (h::t) = foldli_aux f (f n h e) (SUC n) t)`;

val foldli_def = Define`
  foldli f e l = foldli_aux f e 0 l`;

val foldli_aux_thm = Q.prove (
  `!l f e n.  foldli_aux f e n l = FOLDRi (\n'. f (LENGTH l + n - (SUC n'))) e (REVERSE l)`,
  Induct_on `l` \\
  rw [foldli_aux_def] \\
  rw [FOLDRi_APPEND] \\
  rw [ADD1]
);

val foldli_thm = Q.store_thm (
  "foldli_thm",
  `!f e l. foldli f e l = FOLDRi (\n. f (LENGTH l - (SUC n))) e (REVERSE l)`,
  rw [foldli_def, foldli_aux_thm]
);

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

val tabulate_aux_def = tDefine"tabulate_aux"`
  tabulate_aux n m f acc =
    let b = (n >= m) in
    if b then REVERSE acc
    else
      let v = f n in
      let n = n+1n in
      let acc = v::acc in
      tabulate_aux n m f acc`
(wf_rel_tac`measure (λ(n,m,_,_). m-n)`);

val tabulate_def = Define
  `tabulate n f = let l = [] in tabulate_aux 0 n f l`;

val tabulate_aux_GENLIST = Q.store_thm("tabulate_aux_GENLIST",
  `∀n m f acc. tabulate_aux n m f acc = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m-n)`,
  recInduct(theorem"tabulate_aux_ind") \\ rw[]
  \\ rw[Once tabulate_aux_def]
  >- ( `m - n = 0` by simp[] \\ rw[] )
  \\ Cases_on`m` \\ fs[]
  \\ rename1`SUC m - n` \\ `SUC m - n = SUC (m - n)` by simp[]
  \\ simp[GENLIST_CONS,FUNPOW,o_DEF,FUNPOW_SUC_PLUS]
  \\ simp[ADD1]);

val tabulate_GENLIST = Q.store_thm("tabulate_GENLIST",
  `!n. tabulate n f = GENLIST f n`,
  rw[tabulate_def,tabulate_aux_GENLIST,FUNPOW_SUC_PLUS,o_DEF,ETA_AX]);

val collate_def = Define`
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)`;

val collate_ind = theorem"collate_ind";

val collate_equal_thm = Q.store_thm (
  "collate_equal_thm",
  `!l. (!x. MEM x l ==> (f x x = EQUAL)) ==> (collate f l l = EQUAL)`,
  Induct_on `l` \\ rw [collate_def] \\ rw [collate_def]
);

val collate_short_thm = Q.store_thm (
  "collate_short_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l1 ≼ l2) ==>
        (collate f l1 l2 = LESS)`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);

val collate_long_thm = Q.store_thm (
  "collate_long_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l2 ≼ l1) ==>
        (collate f l1 l2 = GREATER)`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);

val cpn_to_reln_def = Define`
  cpn_to_reln f x1 x2 = (f x1 x2 = LESS)`;

val collate_cpn_reln_thm = Q.store_thm (
  "collate_cpn_reln_thm",
  `!f l1 l2. (!x1 x2. (f x1 x2 = EQUAL) <=>
    (x1 = x2)) ==> (cpn_to_reln (collate f) l1 l2 = LLEX (cpn_to_reln f) l1 l2)`,
  ho_match_mp_tac collate_ind \\ rw [collate_def, cpn_to_reln_def, LLEX_def] \\
  first_assum (qspecl_then [`h1`, `h1`] (fn th => assume_tac (GSYM th))) \\
  `(h1 = h1) = T` by DECIDE_TAC \\ rw[] \\`EQUAL ≠ LESS` by fs[] \\ rw[]
);

(* from std_preludeLib *)
val LENGTH_AUX_def = Define `
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))`;

val LENGTH_AUX_THM = Q.store_thm(
  "LENGTH_AUX_THM",
  `!xs n. LENGTH_AUX xs n = LENGTH xs + n`,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];


val _ = export_theory()
