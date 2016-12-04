open preamble

val _ = new_theory"list"



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


val mapPartial_def = Define`
  (mapPartial f [] = []) /\ 
  (mapPartial f (h::t) = case (f h) of
    NONE => mapPartial f t 
    |(SOME x) => x::mapPartial f t)`;

val mapPartial_thm = Q.store_thm (
  "mapPartial_thm",
  `!f l. mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  Induct_on `l` \\ rw [mapPartial_def] \\ Cases_on `f h` \\ rw [THE_DEF] \\ fs [IS_SOME_DEF]
)


val index_find_thm = Q.prove (
  `!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)`,
  Induct_on`l` \\ rw[INDEX_FIND_def]
);


val FIND_thm = Q.store_thm(
  "FIND_thm",
  `(FIND f [] = NONE) ∧
   (∀h t. FIND f (h::t) = if f h then SOME h else FIND f t)`,
  rw[FIND_def,INDEX_FIND_def,index_find_thm]);


val partition_aux_def = Define`
  partition_aux f l (pos, neg) = case l of
    [] => (REVERSE pos, REVERSE neg)
    | (h::t) => if f h then partition_aux f t ((h::pos), neg)
      else partition_aux f t (pos, (h::neg))`;

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


val tabulate_def = Define`
  tabulate n f = GENLIST f n`;


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
  `!l. (!x. MEM x l ==> f x x = EQUAL) ==> collate f l l = EQUAL`,
  Induct_on `l` \\ rw [collate_def] \\ rw [collate_def]
);

val collate_short_thm = Q.store_thm (
  "collate_short_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l1 ≼ l2) ==>
        collate f l1 l2 = LESS`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);

val collate_long_thm = Q.store_thm (
  "collate_long_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l2 ≼ l1) ==>
        collate f l1 l2 = GREATER`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);

val zip_ind = theorem"zip_ind";

val zip_thm = Q.store_thm("zip_thm",
  `!l1 l2. ((LENGTH l1) = (LENGTH l2)) ==> ((zip l1 l2) = (ZIP (l1, l2)))`,
  ho_match_mp_tac zip_ind \\ rw[zip_def,ZIP]);


val zip_def = Define`
  (zip [] [] = []) /\
  (zip [] (h::t) = []) /\
  (zip (h::t) [] = []) /\
  (zip (h1::t1) (h2::t2) = (h1, h2)::(zip t1 t2))`;


(* from std_preludeLib *)
val LENGTH_AUX_def = Define `
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))`;

val LENGTH_AUX_THM = Q.prove(
  `!xs n. LENGTH_AUX xs n = LENGTH xs + n`,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];

val SUC_LEMMA = Q.prove(`SUC = \x. x+1`,SIMP_TAC std_ss [FUN_EQ_THM,ADD1]);

val _ = export_theory()
