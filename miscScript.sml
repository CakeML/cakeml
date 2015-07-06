open HolKernel bossLib boolLib boolSimps lcsymtacs miscLib Parse
open optionTheory listTheory pred_setTheory finite_mapTheory alistTheory rich_listTheory arithmeticTheory pairTheory sortingTheory relationTheory bitTheory sptreeTheory

(* Misc. lemmas (without any compiler constants) *)
val _ = new_theory "misc"
val _ = ParseExtras.temp_tight_equality()

val _ = export_rewrites["list.EVERY2_THM"]
val _ = export_rewrites["rich_list.LIST_REL_APPEND_SING"]
val _ = export_rewrites["alist.set_MAP_FST_fmap_to_alist"]
val _ = export_rewrites["alist.MAP_KEYS_I"]
val _ = export_rewrites["finite_map.FUNION_FEMPTY_1"]
val _ = export_rewrites["finite_map.FUNION_FEMPTY_2"]

(* TODO: move/categorize *)

val REPLICATE_NIL = Q.store_thm("REPLICATE_NIL",
  `REPLICATE x y = [] ⇔ x = 0`,
  Cases_on`x`>>EVAL_TAC>>simp[]);

val REPLICATE_APPEND = Q.store_thm("REPLICATE_APPEND",
  `REPLICATE n a ++ REPLICATE m a = REPLICATE (n+m) a`,
  simp[LIST_EQ_REWRITE,LENGTH_REPLICATE] >> rw[] >>
  Cases_on`x < n` >> simp[EL_APPEND1,LENGTH_REPLICATE,EL_REPLICATE,EL_APPEND2])

val DROP_REPLICATE = Q.store_thm("DROP_REPLICATE",
  `DROP n (REPLICATE m a) = REPLICATE (m-n) a`,
  simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,EL_REPLICATE,EL_DROP])

val INJ_EXTEND = store_thm("INJ_EXTEND",
  ``INJ b s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) b) (x INSERT s) (y INSERT t)``,
  fs [INJ_DEF,combinTheory.APPLY_UPDATE_THM] \\ METIS_TAC []);

val IMP_EVERY_LUPDATE = store_thm("IMP_EVERY_LUPDATE",
  ``!xs h i. P h /\ EVERY P xs ==> EVERY P (LUPDATE h i xs)``,
  Induct \\ fs [LUPDATE_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `i` \\ fs [LUPDATE_def]);

val MAP_APPEND_MAP_EQ = store_thm("MAP_APPEND_MAP_EQ",
  ``!xs ys.
      ((MAP f1 xs ++ MAP g1 ys) = (MAP f2 xs ++ MAP g2 ys)) <=>
      (MAP f1 xs = MAP f2 xs) /\ (MAP g1 ys = MAP g2 ys)``,
  Induct \\ fs [] \\ METIS_TAC []);

val LUPDATE_SOME_MAP = store_thm("LUPDATE_SOME_MAP",
  ``!xs n f h.
      LUPDATE (SOME (f h)) n (MAP (OPTION_MAP f) xs) =
      MAP (OPTION_MAP f) (LUPDATE (SOME h) n xs)``,
  Induct THEN1 (EVAL_TAC \\ fs []) \\ Cases_on `n` \\ fs [LUPDATE_def]);

val MEM_LIST_REL = store_thm("MEM_LIST_REL",
  ``!xs ys P x. LIST_REL P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y``,
  Induct \\ Cases_on `ys` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
  \\ RES_TAC \\ METIS_TAC []);

val LIST_REL_MEM = store_thm("LIST_REL_MEM",
  ``!xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys``,
  fs [LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]);

val lookup_fromList_NONE = store_thm("lookup_fromList_NONE",
  ``!k. LENGTH args <= k ==> (lookup k (fromList args) = NONE)``,
  SIMP_TAC std_ss [lookup_fromList] \\ DECIDE_TAC);

(* similar to half of EVERY2_APPEND, which could maybe be strengthened? *)
val LIST_REL_APPEND_IMP = store_thm("LIST_REL_APPEND_IMP",
  ``!xs ys xs1 ys1.
      LIST_REL P (xs ++ xs1) (ys ++ ys1) /\ (LENGTH xs = LENGTH ys) ==>
      LIST_REL P xs ys /\ LIST_REL P xs1 ys1``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val LIST_REL_REVERSE_EQ =
  IMP_ANTISYM_RULE
    (EVERY2_REVERSE |> SPEC_ALL)
    (EVERY2_REVERSE |> Q.SPECL[`R`,`REVERSE l1`,`REVERSE l2`]
                    |> SIMP_RULE std_ss [REVERSE_REVERSE])
  |> SYM |> curry save_thm"LIST_REL_REVERSE_EQ";

val LIST_REL_GENLIST_I = store_thm("LIST_REL_GENLIST_I",
  ``!xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,GENLIST,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [LIST_REL_APPEND_SING]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `n < LENGTH xs`
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1]
    \\ `n = LENGTH xs` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD])
  THEN1 (`n < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
    \\ POP_ASSUM MP_TAC \\ Q.PAT_ASSUM `!x.bb` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1])
  \\ POP_ASSUM (MP_TAC o Q.SPEC `LENGTH xs`)
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD]);

val LIST_REL_lookup_fromList = store_thm("LIST_REL_lookup_fromList",
  ``LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args``,
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]);

val lemmas = prove(
  ``(2 + 2 * n - 1 = 2 * n + 1:num) /\
    (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'':num) /\
    (2 * m = 2 * n <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 2 = n MOD 2)``)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 2:num``)]
  \\ EVAL_TAC \\ fs [MOD_EQ_0,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

val IN_domain = store_thm("IN_domain",
  ``!n x t1 t2.
      (n IN domain LN <=> F) /\
      (n IN domain (LS x) <=> (n = 0)) /\
      (n IN domain (BN t1 t2) <=>
         n <> 0 /\ (if EVEN n then ((n-1) DIV 2) IN domain t1
                              else ((n-1) DIV 2) IN domain t2)) /\
      (n IN domain (BS t1 x t2) <=>
         n = 0 \/ (if EVEN n then ((n-1) DIV 2) IN domain t1
                             else ((n-1) DIV 2) IN domain t2))``,
  fs [domain_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `n = 0` \\ fs []
  \\ Cases_on `EVEN n` \\ fs []
  \\ fs [GSYM ODD_EVEN]
  \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ fs [ADD1] \\ fs [lemmas]
  \\ Cases_on `m` \\ fs [MULT_CLAUSES]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ fs [lemmas])

val map_LN = store_thm("map_LN[simp]",
  ``!t. map f t = LN <=> t = LN``,
  Cases \\ EVAL_TAC);

val wf_map = store_thm("wf_map[simp]",
  ``!t f. wf (map f t) = wf t``,
  Induct \\ fs [wf_def,map_def]);

val map_map_K = store_thm("map_map_K",
  ``!t. map (K a) (map (K a) t) = map (K a) t``,
  Induct \\ fs [map_def]);

val lookup_map_K = store_thm("lookup_map_K",
  ``!t n. lookup n (map (K x) t) = if n IN domain t then SOME x else NONE``,
  Induct \\ fs [IN_domain,map_def,lookup_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ fs []
  \\ Cases_on `EVEN n` \\ fs []);

val alist_insert_def = Define `
  (alist_insert [] xs t = t) /\
  (alist_insert vs [] t = t) /\
  (alist_insert (v::vs) (x::xs) t = insert v x (alist_insert vs xs t))`

val fromList2_def = Define `
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)`

val EVEN_fromList2_lemma = prove(
  ``!l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x``,
  Induct \\ fs [FOLDL] \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ fs [] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ fs [] \\ fs [EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC);

val EVEN_fromList2 = store_thm("EVEN_fromList2",
  ``!l n. n IN domain (fromList2 l) ==> EVEN n``,
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ fs []);

val SUBMAP_FDOM_SUBSET = Q.store_thm("SUBMAP_FDOM_SUBSET",
  `f1 ⊑ f2 ⇒ FDOM f1 ⊆ FDOM f2`,
  rw[SUBMAP_DEF,SUBSET_DEF])

val SUBMAP_FRANGE_SUBSET = Q.store_thm("SUBMAP_FRANGE_SUBSET",
  `f1 ⊑ f2 ⇒ FRANGE f1 ⊆ FRANGE f2`,
  rw[SUBMAP_DEF,SUBSET_DEF,IN_FRANGE] >> metis_tac[])

val FDIFF_def = Define `
  FDIFF f1 s = DRESTRICT f1 (COMPL s)`;

val FDOM_FDIFF = store_thm("FDOM_FDIFF",
  ``x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN f2)``,
  fs [FDIFF_def,DRESTRICT_DEF]);

val INJ_FAPPLY_FUPDATE = Q.store_thm("INJ_FAPPLY_FUPDATE",
  `INJ ($' f) (FDOM f) (FRANGE f) ∧
   s = k INSERT FDOM f ∧ v ∉ FRANGE f ∧
   t = v INSERT FRANGE f
  ⇒
   INJ ($' (f |+ (k,v))) s t`,
  rw[INJ_DEF,FAPPLY_FUPDATE_THM] >> rw[] >>
  pop_assum mp_tac >> rw[] >>
  fs[IN_FRANGE] >>
  METIS_TAC[])

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]
  |> curry save_thm "NUM_NOT_IN_FDOM";

val EXISTS_NOT_IN_FDOM_LEMMA = prove(
  ``?x. ~(x IN FDOM (refs:num|->'a))``,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NOTIN_FDOM = store_thm("LEAST_NOTIN_FDOM",
  ``(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs``,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs []);

val lookup_inter_assoc = store_thm("lookup_inter_assoc",
  ``lookup x (inter t1 (inter t2 t3)) =
    lookup x (inter (inter t1 t2) t3)``,
  fs [lookup_inter] \\ BasicProvers.EVERY_CASE_TAC)

val lookup_inter_domain = store_thm("lookup_inter_domain",
  ``x IN domain t2 ==> (lookup x (inter t1 t2) = lookup x t1)``,
  fs [lookup_inter,domain_lookup] \\ BasicProvers.EVERY_CASE_TAC);

val lookup_inter_alt = store_thm("lookup_inter_alt",
  ``lookup x (inter t1 t2) =
      if x IN domain t2 then lookup x t1 else NONE``,
  fs [lookup_inter,domain_lookup]
  \\ Cases_on `lookup x t2` \\ fs [] \\ Cases_on `lookup x t1` \\ fs []);

val lookup_inter_EQ = store_thm("lookup_inter_EQ",
  ``((lookup x (inter t1 t2) = SOME y) <=>
       (lookup x t1 = SOME y) /\ lookup x t2 <> NONE) /\
    ((lookup x (inter t1 t2) = NONE) <=>
       (lookup x t1 = NONE) \/ (lookup x t2 = NONE))``,
  fs [lookup_inter] \\ BasicProvers.EVERY_CASE_TAC);

val list_to_num_set_def = Define `
  (list_to_num_set [] = LN) /\
  (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))`;

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

val domain_list_to_num_set = store_thm("domain_list_to_num_set",
  ``!xs. x IN domain (list_to_num_set xs) <=> MEM x xs``,
  Induct \\ fs [list_to_num_set_def]);

val domain_list_insert = store_thm("domain_list_insert",
  ``!xs x t.
      x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t``,
  Induct \\ fs [list_insert_def] \\ METIS_TAC []);

val lookup_list_to_num_set = store_thm("lookup_list_to_num_set",
  ``!xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME () else NONE``,
  Induct \\ srw_tac [] [list_to_num_set_def,lookup_def,lookup_insert] \\ fs []);

val OPTION_BIND_SOME = store_thm("OPTION_BIND_SOME",
  ``∀f. OPTION_BIND f SOME = f``,
  Cases >> simp[])

val hd_drop = Q.store_thm ("hd_drop",
  `!n l. n < LENGTH l ⇒ HD (DROP n l) = EL n l`,
  Induct_on `l` >>
  rw [] >>
  `n - 1 < LENGTH l` by decide_tac >>
  res_tac >>
  `0 < n` by decide_tac >>
  rw [EL_CONS] >>
  `n - 1 = PRE n` by decide_tac >>
  rw []);

val take1 = Q.store_thm ("take1",
  `!l. l ≠ [] ⇒ TAKE 1 l = [EL 0 l]`,
  Induct_on `l` >> rw []);

val SPLIT_LIST = store_thm("SPLIT_LIST",
  ``!xs.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)``,
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ fs [TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ fs [DIV_LE_X] \\ DECIDE_TAC);

val less_sorted_eq = MATCH_MP SORTED_EQ transitive_LESS |> curry save_thm"less_sorted_eq";

val SORTED_GENLIST_PLUS = store_thm("SORTED_GENLIST_PLUS",
  ``∀n k. SORTED $< (GENLIST ($+ k) n)``,
  Induct >> simp[GENLIST_CONS,less_sorted_eq,MEM_GENLIST] >> gen_tac >>
  `$+ k o SUC = $+ (k+1)` by (
    simp[FUN_EQ_THM] ) >>
  metis_tac[])

val EXISTS_ZIP = Q.store_thm ("EXISTS_ZIP",
  `!l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)`,
  Induct_on `l` >>
  rw [] >>
  Cases_on `h` >>
  fs [] >>
  metis_tac []);

val EVERY_ZIP = Q.store_thm ("EVERY_ZIP",
  `!l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)`,
  Induct_on `l` >>
  rw [] >>
  Cases_on `h` >>
  fs [] >>
  metis_tac []);

val LIST_REL_GENLIST = store_thm("LIST_REL_GENLIST",
  ``EVERY2 P (GENLIST f l) (GENLIST g l) <=>
    !i. i < l ==> P (f i) (g i)``,
  Induct_on `l`
  \\ fs [GENLIST,rich_listTheory.LIST_REL_APPEND_SING,SNOC_APPEND]
  \\ fs [DECIDE ``i < SUC n <=> i < n \/ (i = n)``] \\ METIS_TAC []);

val LENGTH_TAKE_EQ = store_thm("LENGTH_TAKE_EQ",
  ``LENGTH (TAKE n xs) = if n <= LENGTH xs then n else LENGTH xs``,
  SRW_TAC [] [] \\ fs [GSYM NOT_LESS] \\ AP_TERM_TAC
  \\ MATCH_MP_TAC TAKE_LENGTH_TOO_LONG \\ DECIDE_TAC);

val tlookup_def = Define `
  tlookup m k = case lookup m k of NONE => 0:num | SOME k => k`;

val any_el_def = Define `
  (any_el n [] d = d) /\
  (any_el n (x::xs) d = if n = 0 then x else any_el (n-1:num) xs d)`

val list_max_def = Define `
  (list_max [] = 0:num) /\
  (list_max (x::xs) =
     let m = list_max xs in
       if m < x then x else m)`

val index_of_def = Define `
  (index_of i [] = (0:num)) /\
  (index_of i (x::xs) = if i = x then 0 else 1 + index_of i xs)`;

val list_inter_def = Define `
  list_inter xs ys = FILTER (\y. MEM y xs) ys`;

val SING_HD = store_thm("SING_HD",
  ``(([HD xs] = xs) <=> (LENGTH xs = 1)) /\
    ((xs = [HD xs]) <=> (LENGTH xs = 1))``,
  Cases_on `xs` \\ fs [LENGTH_NIL] \\ METIS_TAC []);

val list_rel_lastn = Q.store_thm("list_rel_lastn",
  `!f l1 l2 n.
    n ≤ LENGTH l1 ∧
    LIST_REL f l1 l2 ⇒
    LIST_REL f (LASTN n l1) (LASTN n l2)`,
  Induct_on `l1` >>
  rw [LASTN] >>
  imp_res_tac EVERY2_LENGTH >>
  Cases_on `n = LENGTH l1 + 1`
  >- metis_tac [LASTN_LENGTH_ID, ADD1, LENGTH, LIST_REL_def] >>
  `n ≤ LENGTH l1` by decide_tac >>
  `n ≤ LENGTH ys` by decide_tac >>
  res_tac >>
  fs [LASTN_CONS]);

val list_rel_butlastn = Q.store_thm ("list_rel_butlastn",
  `!f l1 l2 n.
    n ≤ LENGTH l1 ∧
    LIST_REL f l1 l2 ⇒
    LIST_REL f (BUTLASTN n l1) (BUTLASTN n l2)`,
  Induct_on `l1` >>
  rw [BUTLASTN] >>
  imp_res_tac EVERY2_LENGTH >>
  Cases_on `n = LENGTH l1 + 1`
  >- metis_tac [BUTLASTN_LENGTH_NIL, ADD1, LENGTH, LIST_REL_def] >>
  `n ≤ LENGTH l1` by decide_tac >>
  `n ≤ LENGTH ys` by decide_tac >>
  res_tac >>
  fs [BUTLASTN_CONS]);

val SORTED_ALL_DISTINCT = store_thm("SORTED_ALL_DISTINCT",
  ``irreflexive R /\ transitive R ==> !ls. SORTED R ls ==> ALL_DISTINCT ls``,
  STRIP_TAC THEN Induct THEN SRW_TAC[][] THEN
  IMP_RES_TAC SORTED_EQ THEN
  FULL_SIMP_TAC (srw_ss()) [SORTED_DEF] THEN
  METIS_TAC[relationTheory.irreflexive_def])

val ALOOKUP_SNOC = store_thm("ALOOKUP_SNOC",
  ``∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE``,
  Induct >> simp[] >>
  Cases >> simp[] >> rw[])

val ALOOKUP_GENLIST = store_thm("ALOOKUP_GENLIST",
  ``∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE``,
  gen_tac >> Induct >> simp[GENLIST] >> rw[] >> fs[ALOOKUP_SNOC] >>
  rw[] >> fsrw_tac[ARITH_ss][])

val anub_def = Define`
  (anub [] acc = []) ∧
  (anub ((k,v)::ls) acc =
   if MEM k acc then anub ls acc else
   (k,v)::(anub ls (k::acc)))`

val anub_ind = theorem"anub_ind"

val EVERY_anub_imp = store_thm("EVERY_anub_imp",
  ``∀ls acc x y.
      EVERY P (anub ((x,y)::ls) acc) ∧ x ∉ set acc
      ⇒
      P (x,y) ∧ EVERY P (anub ls (x::acc))``,
  ho_match_mp_tac anub_ind >> rw[anub_def] >>
  fs[MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD])

val ALOOKUP_anub = store_thm("ALOOKUP_anub",
  ``ALOOKUP (anub ls acc) k =
    if MEM k acc then ALOOKUP (anub ls acc) k
    else ALOOKUP ls k``,
  qid_spec_tac`acc` >>
  Induct_on`ls` >>
  rw[anub_def] >>
  Cases_on`h`>>rw[anub_def]>>fs[] >- (
    first_x_assum(qspec_then`acc`mp_tac) >>
    rw[] ) >>
  first_x_assum(qspec_then`q::acc`mp_tac) >>
  rw[])

val anub_eq_nil = store_thm("anub_eq_nil",
  ``anub x y = [] ⇔ EVERY (combin$C MEM y) (MAP FST x)``,
  qid_spec_tac`y` >>
  Induct_on`x`>>rw[anub_def]>>
  Cases_on`h`>>rw[anub_def])

val EVERY_anub_suff = store_thm("EVERY_anub_suff",
  ``∀ls acc.
    (∀x. ¬MEM x acc ⇒ case ALOOKUP ls x of SOME v => P (x,v) | NONE => T)
    ⇒ EVERY P (anub ls acc)``,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> rw[] >- (
    first_x_assum(match_mp_tac) >>
    rw[] >>
    res_tac >>
    pop_assum mp_tac >> IF_CASES_TAC >> fs[] )
  >- (
    res_tac >> fs[] ) >>
  first_x_assum match_mp_tac >>
  rw[] >> res_tac >> fs[] >>
  `q ≠ x` by fs[] >> fs[])

val anub_notin_acc = store_thm("anub_notin_acc",
  ``∀ls acc. MEM x acc ⇒ ¬MEM x (MAP FST (anub ls acc))``,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> rw[] >>
  metis_tac[])

val anub_tl_anub = store_thm("anub_tl_anub",
  ``∀x y h t. anub x y = h::t ⇒ ∃a b. t = anub a b ∧ set a ⊆ set x ∧ set b ⊆ set ((FST h)::y)``,
  Induct >> rw[anub_def] >>
  Cases_on`h`>>fs[anub_def] >>
  pop_assum mp_tac  >> rw[] >>
  res_tac >> rw[] >>
  fs[SUBSET_DEF] >>
  metis_tac[MEM] )

val anub_all_distinct_keys = store_thm("anub_all_distinct_keys",
  ``∀ls acc.
    ALL_DISTINCT acc ⇒
    ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)``,
  Induct>>rw[anub_def]>>PairCases_on`h`>>fs[anub_def]>>
  rw[]>>
  `ALL_DISTINCT (h0::acc)` by fs[ALL_DISTINCT]>>res_tac>>
  fs[ALL_DISTINCT_APPEND]>>
  metis_tac[])

val MEM_anub_ALOOKUP = store_thm("MEM_anub_ALOOKUP",
  ``MEM (k,v) (anub ls []) ⇒
    ALOOKUP ls k = SOME v``,
  rw[]>>
  Q.ISPECL_THEN[`ls`,`[]`] assume_tac anub_all_distinct_keys>>
  Q.ISPECL_THEN [`ls`,`k`,`[]`] assume_tac (GEN_ALL ALOOKUP_anub)>>
  fs[]>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM])

val LIST_REL_REPLICATE_same = store_thm("LIST_REL_REPLICATE_same",
  ``LIST_REL P (REPLICATE n x) (REPLICATE n y) ⇔ (n > 0 ⇒ P x y)``,
  simp[LIST_REL_EL_EQN,rich_listTheory.REPLICATE_GENLIST] >>
  Cases_on`n`>>simp[EQ_IMP_THM] >> rw[] >>
  first_x_assum MATCH_MP_TAC >>
  qexists_tac`0`>>simp[])

val FEMPTY_FUPDATE_EQ = store_thm("FEMPTY_FUPDATE_EQ",
  ``∀x y. (FEMPTY |+ x = FEMPTY |+ y) ⇔ (x = y)``,
  Cases >> Cases >> rw[fmap_eq_flookup,FDOM_FUPDATE,FLOOKUP_UPDATE] >>
  Cases_on`q=q'`>>rw[] >- (
    rw[EQ_IMP_THM] >>
    pop_assum(qspec_then`q`mp_tac) >> rw[] ) >>
  qexists_tac`q`>>rw[])

val ZIP_EQ_NIL = store_thm("ZIP_EQ_NIL",
  ``∀l1 l2. LENGTH l1 = LENGTH l2 ⇒ (ZIP (l1,l2) = [] ⇔ (l1 = [] ∧ l2 = []))``,
  rpt gen_tac >> Cases_on`l1`>>rw[LENGTH_NIL_SYM]>> Cases_on`l2`>>fs[])

val FUPDATE_LIST_EQ_FEMPTY = store_thm("FUPDATE_LIST_EQ_FEMPTY",
  ``∀fm ls. fm |++ ls = FEMPTY ⇔ fm = FEMPTY ∧ ls = []``,
  rw[EQ_IMP_THM,FUPDATE_LIST_THM] >>
  fs[GSYM fmap_EQ_THM,FDOM_FUPDATE_LIST])

val LUPDATE_SAME = store_thm("LUPDATE_SAME",
  ``∀n ls. n < LENGTH ls ⇒ (LUPDATE (EL n ls) n ls = ls)``,
  rw[LIST_EQ_REWRITE,EL_LUPDATE]>>rw[])

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x``,
  Cases >> simp[])

val _ = type_abbrev("num_set",``:unit spt``);
val _ = type_abbrev("num_map",``:'a spt``);

val domain_nat_set_from_list = store_thm("domain_nat_set_from_list",
  ``∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls``,
  Induct >> simp[sptreeTheory.domain_insert] >>
  rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["domain_nat_set_from_list"]

val wf_nat_set_from_list = store_thm("wf_nat_set_from_list",
  ``∀ls ns. wf ns ⇒ wf (FOLDL (λs n. insert n z s) ns ls)``,
  Induct >> simp[] >> rw[sptreeTheory.wf_insert])

val BIT_11 = store_thm("BIT_11",
  ``∀n m. (BIT n = BIT m) ⇔ (n = m)``,
  simp[EQ_IMP_THM] >>
  Induct >> simp[BIT0_ODD,FUN_EQ_THM] >- (
    Cases >> simp[] >>
    qexists_tac`1` >> simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  simp[GSYM BIT_DIV2] >>
  Cases >> simp[GSYM BIT_DIV2] >- (
    qexists_tac`1` >>
    simp[BIT_ZERO] >>
    simp[BIT_def,BITS_THM] ) >>
  rw[] >>
  first_x_assum MATCH_MP_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  first_x_assum(qspec_then`x*2`mp_tac) >>
  simp[arithmeticTheory.MULT_DIV])

val BIT_11_2 = store_thm("BIT_11_2",
  ``∀n m. (∀z. (z < 2 ** (MAX n m)) ⇒ (BIT n z ⇔ BIT m z)) ⇔ (n = m)``,
  simp[Once EQ_IMP_THM] >>
  Induct >- (
    simp[] >>
    Cases >> simp[] >>
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  Cases >> simp[] >- (
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  strip_tac >>
  first_x_assum MATCH_MP_TAC >>
  qx_gen_tac`z` >>
  first_x_assum(qspec_then`z*2`mp_tac) >>
  simp[GSYM BIT_DIV2,arithmeticTheory.MULT_DIV] >>
  rw[] >> first_x_assum MATCH_MP_TAC >>
  fs[arithmeticTheory.MAX_DEF] >>
  rw[] >> fs[] >>
  simp[arithmeticTheory.EXP])

val binary_induct = store_thm("binary_induct",
  ``∀P. P (0:num) ∧ (∀n. P n ⇒ P (2*n) ∧ P (2*n+1)) ⇒ ∀n. P n``,
  gen_tac >> strip_tac >>
  completeInduct_on`n` >>
  Cases_on`n=0`>>simp[]>>
  `n DIV 2 < n ∧ ((n = 2 * (n DIV 2)) ∨ (n = 2 * (n DIV 2) + 1))` by (
    simp[DIV_MULT_THM2] >>
    `n MOD 2 < 2` by (
      MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
      simp[] ) >>
    simp[] ) >>
  metis_tac[])

val BIT_TIMES2 = store_thm("BIT_TIMES2",
  ``BIT z (2 * n) ⇔ 0 < z ∧ BIT (PRE z) n``,
  Cases_on`z`>>simp[]>-(
    simp[BIT0_ODD] >>
    simp[arithmeticTheory.ODD_EVEN] >>
    simp[arithmeticTheory.EVEN_DOUBLE] ) >>
  qmatch_rename_tac`BIT (SUC z) (2 * n) ⇔ BIT z n` >>
  qspecl_then[`z`,`n`,`1`]mp_tac BIT_SHIFT_THM >>
  simp[arithmeticTheory.ADD1])

val BIT_TIMES2_1 = store_thm("BIT_TIMES2_1",
  ``∀n z. BIT z (2 * n + 1) ⇔ (z=0) ∨ BIT z (2 * n)``,
  Induct >> simp[] >- (
    simp[BIT_ZERO] >>
    Cases_on`z`>>simp[BIT0_ODD] >>
    simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  Cases >> simp[BIT0_ODD] >- (
    simp[arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  simp[GSYM BIT_DIV2] >>
  qspec_then`2`mp_tac arithmeticTheory.ADD_DIV_RWT >>
  simp[] >>
  disch_then(qspecl_then[`2 * SUC n`,`1`]mp_tac) >>
  simp[] >>
  simp[arithmeticTheory.MOD_EQ_0_DIVISOR] >>
  metis_tac[] )

val LOG2_TIMES2 = store_thm("LOG2_TIMES2",
  ``0 < n ⇒ (LOG2 (2 * n) = SUC (LOG2 n))``,
  rw[LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1])

val LOG2_TIMES2_1 = store_thm("LOG2_TIMES2_1",
  ``∀n. 0 < n ⇒ (LOG2 (2 * n + 1) = LOG2 (2 * n))``,
  rw[LOG2_def] >>
  MATCH_MP_TAC logrootTheory.LOG_UNIQUE >>
  simp[GSYM LOG2_def,LOG2_TIMES2] >>
  simp[arithmeticTheory.EXP] >>
  conj_tac >- (
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac`2*n` >> simp[] >>
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`2 ** LOG2 n ≤ X` >- rw[] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] ) >>
  simp[GSYM arithmeticTheory.ADD1] >>
  match_mp_tac arithmeticTheory.LESS_NOT_SUC >>
  `4:num = 2 * 2` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[Once (GSYM arithmeticTheory.MULT_ASSOC)] >>
  simp[] >>
  conj_asm1_tac >- (
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`X < 2 * 2 ** LOG2 n` >- rw[] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] >>
    qmatch_abbrev_tac`(a:num) + b < 2 * a` >>
    qsuff_tac`n MOD a < a` >- simp[] >>
    MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
    simp[Abbr`a`] ) >>
  qmatch_abbrev_tac`X ≠ Y` >>
  qsuff_tac`EVEN X ∧ ODD Y` >- metis_tac[arithmeticTheory.EVEN_ODD] >>
  conj_tac >- (
    simp[Abbr`X`,arithmeticTheory.EVEN_EXISTS] >>
    qexists_tac`2 * 2 ** LOG2 n` >>
    simp[] ) >>
  simp[Abbr`Y`,arithmeticTheory.ODD_EXISTS] >>
  metis_tac[])

val C_BIT_11 = store_thm("C_BIT_11",
  ``∀n m. (∀z. (z ≤ LOG2 (MAX n m)) ⇒ (BIT z n ⇔ BIT z m)) ⇔ (n = m)``,
  simp[Once EQ_IMP_THM] >>
  ho_match_mp_tac binary_induct >>
  simp[] >>
  conj_tac >- (
    Cases >> simp[] >>
    qexists_tac`LOG2 (SUC n)` >>
    simp[BIT_LOG2,BIT_ZERO] ) >>
  gen_tac >> strip_tac >>
  simp[BIT_TIMES2,BIT_TIMES2_1] >>
  rw[] >- (
    Cases_on`n=0`>>fs[]>-(
      Cases_on`m=0`>>fs[]>>
      first_x_assum(qspec_then`LOG2 m`mp_tac)>>simp[BIT_ZERO] >>
      simp[BIT_LOG2]) >>
    `¬ODD m` by (
      simp[SYM BIT0_ODD] >>
      first_x_assum(qspec_then`0`mp_tac) >>
      simp[] ) >>
    fs[arithmeticTheory.ODD_EVEN] >>
    fs[arithmeticTheory.EVEN_EXISTS] >>
    simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
    first_x_assum MATCH_MP_TAC >>
    rw[] >>
    first_x_assum(qspec_then`SUC z`mp_tac) >>
    discharge_hyps >- (
      fs[arithmeticTheory.MAX_DEF] >>
      rw[] >> fs[] >> simp[LOG2_TIMES2] ) >>
    simp[BIT_TIMES2] ) >>
  Cases_on`n=0`>>fs[]>-(
    fs[BIT_ZERO] >>
    Cases_on`m=0`>>fs[BIT_ZERO] >>
    Cases_on`m=1`>>fs[]>>
    first_x_assum(qspec_then`LOG2 m`mp_tac) >>
    simp[arithmeticTheory.MAX_DEF,BIT_LOG2] >>
    spose_not_then strip_assume_tac >>
    qspec_then`m`mp_tac logrootTheory.LOG_MOD >>
    simp[GSYM LOG2_def] ) >>
  `ODD m` by (
    simp[SYM BIT0_ODD] >>
    first_x_assum(qspec_then`0`mp_tac) >>
    simp[] ) >>
  fs[arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
  simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
  first_x_assum MATCH_MP_TAC >>
  rw[] >>
  first_x_assum(qspec_then`SUC z`mp_tac) >>
  discharge_hyps >- (
    fs[arithmeticTheory.MAX_DEF] >>
    rw[] >> fs[] >> simp[LOG2_TIMES2_1,LOG2_TIMES2] ) >>
  simp[BIT_TIMES2_1,BIT_TIMES2])

val BIT_num_from_bin_list_leading = store_thm("BIT_num_from_bin_list_leading",
  ``∀l x. EVERY ($> 2) l ∧ LENGTH l ≤ x ⇒ ¬BIT x (num_from_bin_list l)``,
  simp[numposrepTheory.num_from_bin_list_def] >>
  rw[] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH l` >>
  simp[numposrepTheory.l2n_lt] )

val least_from_def = Define`
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P`

val LEAST_thm = store_thm("LEAST_thm",
  ``$LEAST P = least_from P 0``,
  rw[least_from_def,ETA_AX])

val least_from_thm = store_thm("least_from_thm",
  ``least_from P n = if P n then n else least_from P (n+1)``,
  rw[least_from_def] >>
  numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >- metis_tac[] >>
    qmatch_rename_tac`a = b` >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    fs[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    fs[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    fs[] ))

val FILTER_F = store_thm("FILTER_F",
  ``∀ls. FILTER (λx. F) ls = []``,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

val OPTREL_SOME = store_thm("OPTREL_SOME",
  ``(!R x y. OPTREL R (SOME x) y <=> (?z. y = SOME z /\ R x z)) /\
    (!R x y. OPTREL R x (SOME y) <=> (?z. x = SOME z /\ R z y))``,
    rw[optionTheory.OPTREL_def])

val LIST_REL_O = store_thm("LIST_REL_O",
  ``∀R1 R2 l1 l2. LIST_REL (R1 O R2) l1 l2 ⇔ ∃l3. LIST_REL R2 l1 l3 ∧ LIST_REL R1 l3 l2``,
  rpt gen_tac >>
  simp[EVERY2_EVERY,EVERY_MEM,EQ_IMP_THM,GSYM AND_IMP_INTRO,MEM_ZIP,PULL_EXISTS,O_DEF] >>
  rw[] >- (
    fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH l2)` >>
    simp[MEM_ZIP,PULL_EXISTS] ) >>
  metis_tac[])

val OPTREL_O_lemma = prove(
  ``∀R1 R2 l1 l2. OPTREL (R1 O R2) l1 l2 ⇔ ∃l3. OPTREL R2 l1 l3 ∧ OPTREL R1 l3 l2``,
  rw[optionTheory.OPTREL_def,EQ_IMP_THM,O_DEF,PULL_EXISTS] >> metis_tac[])

val OPTREL_O = store_thm("OPTREL_O",
  ``∀R1 R2. OPTREL (R1 O R2) = OPTREL R1 O OPTREL R2``,
  rw[FUN_EQ_THM,OPTREL_O_lemma,O_DEF])

val FUNPOW_mono = store_thm("FUNPOW_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y``,
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> rw[])

val OPTREL_trans = store_thm("OPTREL_trans",
  ``∀R x y z. (∀a b c. (x = SOME a) ∧ (y = SOME b) ∧ (z = SOME c) ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z``,
  rw[optionTheory.OPTREL_def])

val UPDATE_LIST_def = Define`
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`
val _ = Parse.add_infix("=++",500,Parse.LEFT)
val _ = Parse.overload_on("=++",``UPDATE_LIST``)

val UPDATE_LIST_THM = store_thm("UPDATE_LIST_THM",
  ``∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)``,
  rw[UPDATE_LIST_def,pairTheory.UNCURRY])

val APPLY_UPDATE_LIST_ALOOKUP = store_thm("APPLY_UPDATE_LIST_ALOOKUP",
  ``∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y``,
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> BasicProvers.CASE_TAC)

val IS_SUFFIX_CONS = store_thm("IS_SUFFIX_CONS",
  ``∀l1 l2 a. IS_SUFFIX l1 l2 ⇒ IS_SUFFIX (a::l1) l2``,
  rw[rich_listTheory.IS_SUFFIX_APPEND] >>
  qexists_tac`a::l` >>rw[])

val INFINITE_INJ_NOT_SURJ = store_thm("INFINITE_INJ_NOT_SURJ",
  ``∀s. INFINITE s ⇔ (s ≠ ∅) ∧ (∃f. INJ f s s ∧ ¬SURJ f s s)``,
  rw[EQ_IMP_THM] >- (
    PROVE_TAC[INFINITE_INHAB,MEMBER_NOT_EMPTY] )
  >- (
    fs[infinite_num_inj] >>
    qexists_tac`λx. if ∃n. x = f n then f (SUC (LEAST n. x = f n)) else x` >>
    conj_asm1_tac >- (
      fs[INJ_IFF] >>
      conj_asm1_tac >- rw[] >>
      rw[] >- (
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- PROVE_TAC[] >>
        rw[] ) >>
      numLib.LEAST_ELIM_TAC >>
      rw[] >>
      metis_tac[] ) >>
    fs[SURJ_DEF,INJ_IFF] >>
    qexists_tac`f 0` >>
    simp[] >>
    rw[] >>
    metis_tac[]) >>
  fs[SURJ_DEF] >- (fs[INJ_IFF] >> metis_tac[]) >>
  simp[infinite_num_inj] >>
  qexists_tac`λn. FUNPOW f n x` >>
  simp[INJ_IFF] >>
  conj_asm1_tac >- (
    Induct >>
    simp[arithmeticTheory.FUNPOW_SUC] >>
    fs[INJ_IFF] ) >>
  Induct >> simp[] >- (
    Cases >> simp[arithmeticTheory.FUNPOW_SUC] >>
    metis_tac[] ) >>
  Cases >> simp[arithmeticTheory.FUNPOW_SUC] >> fs[INJ_IFF] >>
  metis_tac[] )


val find_index_def = Define`
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))`

val find_index_NOT_MEM = store_thm("find_index_NOT_MEM",
  ``∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)``,
  Induct >> rw[find_index_def])

val find_index_MEM = store_thm("find_index_MEM",
  ``!ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)``,
  Induct >> rw[find_index_def] >- (
    qexists_tac`0`>>rw[] ) >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  rw[]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1])

val find_index_LEAST_EL = store_thm("find_index_LEAST_EL",
  ``∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE``,
  Induct >- rw[find_index_def] >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>fs[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> rw[]) >>
    Cases >> rw[] >>
    first_x_assum (qspec_then`0`mp_tac) >> rw[] ) >>
  rw[] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  rw[] >>
  Cases_on`n`>>fs[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  qmatch_rename_tac`m = n` >>
  Cases_on`m < n` >- (res_tac >> fs[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> fs[GSYM ADD1] ) >>
  DECIDE_TAC )

val find_index_LESS_LENGTH = store_thm(
"find_index_LESS_LENGTH",
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val ALOOKUP_find_index_NONE = store_thm("ALOOKUP_find_index_NONE",
  ``(ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)``,
  rw[ALOOKUP_FAILS] >> rw[GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD])

val ALOOKUP_find_index_SOME = prove(
  ``∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))``,
  Induct >> simp[] >> Cases >> rw[find_index_def] >-
    (qexists_tac`0`>>simp[]) >> fs[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>rw[]>>rw[]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]
val ALOOKUP_find_index_SOME = store_thm("ALOOKUP_find_index_SOME",
  ``(ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))``,
  rw[] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> fs[EL_MAP])

val find_index_ALL_DISTINCT_EL = store_thm(
"find_index_ALL_DISTINCT_EL",
``∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))``,
Induct >- rw[] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_ALL_DISTINCT_EL_eq = store_thm("find_index_ALL_DISTINCT_EL_eq",
  ``∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)``,
  rw[EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    fs[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    fs[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL])

val find_index_APPEND_same = store_thm("find_index_APPEND_same",
  ``!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)``,
  Induct >> rw[find_index_def])

val find_index_ALL_DISTINCT_REVERSE = store_thm("find_index_ALL_DISTINCT_REVERSE",
  ``∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))``,
  rw[] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by rw[ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  qmatch_assum_rename_tac`z < LENGTH ls` >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

val THE_find_index_suff = store_thm("THE_find_index_suff",
  ``∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val find_index_APPEND1 = store_thm("find_index_APPEND1",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)``,
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  rw[] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[])

val find_index_APPEND2 = store_thm("find_index_APPEND2",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)``,
  Induct >> simp[find_index_def] >>
  rw[] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1])

val find_index_is_MEM = store_thm("find_index_is_MEM",
  ``∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls``,
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE])

val find_index_MAP_inj = store_thm("find_index_MAP_inj",
  ``∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)``,
  Induct >- simp[find_index_def] >>
  rw[] >> rw[find_index_def] >>
  metis_tac[])

val find_index_shift_0 = store_thm("find_index_shift_0",
  ``∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)``,
  Induct >> simp_tac(srw_ss())[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x` >- (
    BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  first_assum(qspecl_then[`x`,`k+1`]mp_tac) >>
  first_x_assum(qspecl_then[`x`,`1`]mp_tac) >>
  rw[] >>
  Cases_on`find_index x ls 0`>>rw[] >>
  simp[])

val find_index_shift = store_thm("find_index_shift",
  ``∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)``,
  Induct >> simp[find_index_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][])

val find_index_APPEND = store_thm("find_index_APPEND",
  ``∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x``,
  Induct >> simp[find_index_def] >> rw[] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1])

val find_index_in_FILTER_ZIP_EQ = store_thm("find_index_in_FILTER_ZIP_EQ",
  ``∀P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) ∧
      (FILTER (P o FST) (ZIP(l1,v1)) = l2) ∧
      (find_index x l1 n1 = SOME (n1+j1)) ∧
      (find_index x (MAP FST l2) n2 = SOME (n2+j2)) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      (EL j1 (ZIP(l1,v1)) = EL j2 l2)``,
  gen_tac >> Induct >> simp[find_index_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >> fs[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    fs[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][] >>
    Cases_on`v1`>>fsrw_tac[ARITH_ss][find_index_def]) >>
  strip_tac >>
  Cases_on`v1`>>fs[] >>
  Cases_on`P h`>>fs[find_index_def] >- (
    rfs[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`n2+1`,`t`]mp_tac) >> simp[] >>
    Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`j2=0`>>fsrw_tac[ARITH_ss][]>>
    disch_then(qspecl_then[`PRE j1`,`PRE j2`]mp_tac) >>
    simp[rich_listTheory.EL_CONS] ) >>
  first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`n2`,`t`]mp_tac) >> simp[] >>
  imp_res_tac find_index_LESS_LENGTH >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
  disch_then(qspec_then`PRE j1`mp_tac) >>
  simp[rich_listTheory.EL_CONS] )

val ALL_DISTINCT_PERM_ALOOKUP_ZIP = store_thm("ALL_DISTINCT_PERM_ALOOKUP_ZIP",
  ``∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))``,
  rw[EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1` >>
    imp_res_tac PERM_LENGTH >> fs[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ (x = EL m l2)` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    rw[ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1` >>
  imp_res_tac PERM_LENGTH >>
  fs[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  qexists_tac`m` >>
  simp[EL_MAP] >>
  Cases_on`EL m l1`>>simp[ALOOKUP_APPEND] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    metis_tac[MEM_EL] ) >>
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF])

val PERM_ZIP = store_thm("PERM_ZIP",
  ``∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. (l1 = ZIP(a,b)) ∧ (l2 = ZIP(c,d)) ∧ (LENGTH a = LENGTH b) ∧ (LENGTH c = LENGTH d) ⇒
    PERM a c ∧ PERM b d``,
  ho_match_mp_tac PERM_IND >>
  conj_tac >- (
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] ) >>
  conj_tac >- (
    Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    metis_tac[PERM_MONO]) >>
  conj_tac >- (
    ntac 2 Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LENGTH a = LENGTH b` >>
    pop_assum mp_tac >>
    qmatch_assum_rename_tac`LENGTH c = LENGTH d` >>
    strip_tac >>
    Cases_on`a`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`b`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`c`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`d`>>fs[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  `∀l. l = ZIP (MAP FST l, MAP SND l)` by (
    simp[ZIP_MAP] >>
    simp[LIST_EQ_REWRITE,EL_MAP] ) >>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS])

val PERM_BIJ = store_thm("PERM_BIJ",
  ``∀l1 l2. PERM l1 l2 ⇒ ∃f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ (l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1)))``,
  ho_match_mp_tac PERM_IND >> simp[BIJ_EMPTY] >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(f i)` >>
    simp[EL_CONS,PRE_SUB1] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- ( Cases >> simp[] ) >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(g i)` >>
    conj_tac >- ( Cases >> simp[] ) >>
    conj_tac >- ( Cases >> simp[] ) >>
    ( Cases >> simp[] )) >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))` >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))` >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[])) >>
  ntac 2 (rw[LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  fs[LENGTH_GENLIST] >>
  qexists_tac`f o f'` >>
  simp[combinTheory.o_DEF] >>
  fs[BIJ_IFF_INV] >>
  qexists_tac`g' o g` >>
  simp[combinTheory.o_DEF] )

val RTC_RINTER = store_thm("RTC_RINTER",
  ``!R1 R2 x y. RTC (R1 RINTER R2) x y ⇒ ((RTC R1) RINTER (RTC R2)) x y``,
  ntac 2 gen_tac >>
  match_mp_tac RTC_INDUCT >>
  simp[RINTER] >>
  metis_tac[RTC_CASES1] )

val RTC_invariant = store_thm("RTC_invariant",
  ``!R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y``,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> res_tac >> fs[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER])

val RTC_RSUBSET = store_thm("RTC_RSUBSET",
  ``!R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)``,
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1])

val PERM_PART = store_thm("PERM_PART",
  ``∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)``,
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> rw[] >- (
    first_x_assum(qspecl_then[`h::l1`,`l2`,`p`,`q`]mp_tac) >>
    simp[] >>
    REWRITE_TAC[Once CONS_APPEND] >>
    strip_tac >>
    REWRITE_TAC[Once CONS_APPEND] >>
    full_simp_tac std_ss [APPEND_ASSOC] >>
    metis_tac[PERM_REWR,PERM_APPEND] ) >>
  first_x_assum(qspecl_then[`l1`,`h::l2`,`p`,`q`]mp_tac) >>
  simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >>
  strip_tac >>
  REWRITE_TAC[Once CONS_APPEND] >>
  full_simp_tac std_ss [APPEND_ASSOC] >>
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC] )

val PERM_PARTITION = store_thm("PERM_PARTITION",
  ``∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)``,
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL])

val transitive_LESS = store_thm("transitive_LESS",
  ``transitive ($< : (num->num->bool))``,
  rw[relationTheory.transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = store_thm("OPTION_EVERY_cong",
  ``!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)``,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = store_thm("OPTION_EVERY_mono",
  ``(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op``,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val option_case_NONE_F = store_thm("option_case_NONE_F",
  ``(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)``,
  Cases_on`X`>>rw[])

val IS_PREFIX_THM = store_thm("IS_PREFIX_THM",
 ``!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)``,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val EVERY2_RC_same = store_thm("EVERY2_RC_same",
  ``EVERY2 (RC R) l l``,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]

val FOLDL_invariant = store_thm("FOLDL_invariant",
  ``!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)``,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val FOLDL_invariant_rest = store_thm("FOLDL_invariant_rest",
  ``∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)``,
  ntac 2 gen_tac >>
  Induct >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> rw[] ) >>
  rw[] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> rw[])

val between_def = Define`
  between x y z ⇔ x:num ≤ z ∧ z < y`

val SUC_LEAST = store_thm("SUC_LEAST",
  ``!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))``,
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC)

val fmap_linv_def = Define`
  fmap_linv f1 f2 ⇔ (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`

val fmap_linv_unique = store_thm("fmap_linv_unique",
  ``!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)``,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = store_thm("INJ_has_fmap_linv",
  ``INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g``,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = store_thm("has_fmap_linv_inj",
  ``(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))``,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = store_thm("fmap_linv_FAPPLY",
  ``fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)``,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val o_f_cong = store_thm("o_f_cong",
  ``!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')``,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

val plus_compose = store_thm("plus_compose",
  ``!n:num m. $+ n o $+ m = $+ (n + m)``,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

(* TODO: move elsewhere? export as rewrite? *)
val IN_option_rwt = store_thm(
"IN_option_rwt",
``(x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)``,
Cases_on `opt` >> rw[EQ_IMP_THM])

val IN_option_rwt2 = store_thm(
"IN_option_rwt2",
``x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y``,
Cases_on `opt` >> rw[])

(* Re-expressing folds *)

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_CONS_5tup = store_thm(
"FOLDR_CONS_5tup",
``!f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_transitive_property = store_thm(
"FOLDR_transitive_property",
``!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

(* Re-expressing curried lambdas *)

val FST_triple = store_thm(
"FST_triple",
``(λ(n,ns,b). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_5tup = store_thm(
"FST_5tup",
``(λ(n,ns,b,x,y). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val MAP_ZIP_SND_triple = store_thm(
"MAP_ZIP_SND_triple",
``(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)``,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

(* Specialisations to identity function *)

val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t ⇔ s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])


val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* Specialisations to FEMPTY *)

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(* FUPDATE_LIST stuff *)

(* Misc. *)

val LESS_1 = store_thm(
"LESS_1",
``x < 1 ⇔ (x = 0:num)``,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]



  (* --------- SO additions --------- *)

val map_fst = Q.store_thm ("map_fst",
`!l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l`,
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
fs []);

val map_some_eq = Q.store_thm ("map_some_eq",
`!l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)`,
 Induct_on `l1` >>
 rw [] >>
 Cases_on `l2` >>
 rw []);

val map_some_eq_append = Q.store_thm ("map_some_eq_append",
`!l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)`,
metis_tac [map_some_eq, MAP_APPEND]);

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];


(* list misc *)

val LAST_N_def = Define `
  LAST_N n xs = REVERSE (TAKE n (REVERSE xs))`;

val LAST_N_LENGTH = store_thm("LAST_N_LENGTH",
  ``!xs. LAST_N (LENGTH xs) xs = xs``,
  fs [LAST_N_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [TAKE_LENGTH_ID] \\ fs []);

val LAST_N_LEMMA = store_thm("LAST_N_LEMMA",
  ``(LAST_N (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LAST_N (LENGTH xs + 1) (x::xs) = x::xs)``,
  MP_TAC (Q.SPEC `x::y::xs` LAST_N_LENGTH)
  \\ MP_TAC (Q.SPEC `x::xs` LAST_N_LENGTH) \\ fs [ADD1]);

val LAST_N_TL = store_thm("LAST_N_TL",
  ``n < LENGTH xs ==>
    (LAST_N (n+1) (x::xs) = LAST_N (n+1) xs)``,
  fs [LAST_N_def] \\ REPEAT STRIP_TAC
  \\ `n+1 <= LENGTH (REVERSE xs)` by (fs [] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ fs []);

val _ = export_theory()
