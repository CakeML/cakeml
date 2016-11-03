open HolKernel bossLib boolLib boolSimps lcsymtacs Parse
open optionTheory combinTheory listTheory pred_setTheory finite_mapTheory alistTheory rich_listTheory llistTheory arithmeticTheory pairTheory sortingTheory relationTheory totoTheory comparisonTheory bitTheory sptreeTheory wordsTheory set_sepTheory indexedListsTheory
ASCIInumbersLib

(* Misc. lemmas (without any compiler constants) *)
val _ = new_theory "misc"
val _ = ParseExtras.temp_tight_equality()

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))
(* -- *)

(* TODO: move/categorize *)

val _ = numLib.prefer_num();

val IMP_IMP = save_thm("IMP_IMP",METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``);

val SUBSET_IMP = Q.store_thm("SUBSET_IMP",
  `s SUBSET t ==> (x IN s ==> x IN t)`,
  fs[pred_setTheory.SUBSET_DEF]);

val fmap_eq_flookup = save_thm("fmap_eq_flookup",FLOOKUP_EXT |> REWRITE_RULE[FUN_EQ_THM]);

val oHD_def = Define`oHD l = case l of [] => NONE | h::_ => SOME h`
val oHD_thm = Q.store_thm("oHD_thm[simp]",
  `oHD [] = NONE ∧ oHD (h::t) = SOME h`,
  rw[oHD_def]);
val safeTL_def = Define`safeTL [] = [] ∧ safeTL (h::t) = t`

val revdroprev = Q.store_thm("revdroprev",
  `∀l n.
     n ≤ LENGTH l ⇒ (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l)`,
  ho_match_mp_tac listTheory.SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `n ≤ SUC (LENGTH l)` >>
  `n = 0 ∨ ∃m. n = SUC m` by (Cases_on `n` >> simp[]) >> simp[]
  >- simp[TAKE_APPEND2] >>
  simp[TAKE_APPEND1] >>
  `LENGTH l + 1 - SUC m = LENGTH l - m`
     suffices_by (disch_then SUBST_ALL_TAC >> simp[]) >>
  simp[]);

val revtakerev = Q.store_thm("revtakerev",
  `∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l`,
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]);

val times_add_o = Q.store_thm("times_add_o",
  `(λn:num. k * n + x) = ($+ x) o ($* k)`,
  rw[FUN_EQ_THM]);

val SORTED_inv_image_LESS_PLUS = Q.store_thm("SORTED_inv_image_LESS_PLUS",
  `SORTED (inv_image $< (arithmetic$+ k)) = SORTED $<`,
  simp[FUN_EQ_THM]
  \\ Induct
  \\ Q.ISPEC_THEN`$+ k`(fn th => simp[MATCH_MP SORTED_EQ th])
      (MATCH_MP transitive_inv_image transitive_LESS)
  \\ simp[MATCH_MP SORTED_EQ transitive_LESS]);

val SORTED_GENLIST_TIMES = Q.store_thm("SORTED_GENLIST_TIMES",
  `0 < k ⇒ ∀n. SORTED prim_rec$< (GENLIST ($* k) n)`,
  strip_tac
  \\ Induct \\ simp[GENLIST,SNOC_APPEND]
  \\ match_mp_tac SORTED_APPEND
  \\ simp[MEM_GENLIST,PULL_EXISTS]);

val read_bytearray_def = Define `
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))`

val read_bytearray_LENGTH = Q.store_thm("read_bytearray_LENGTH",
  `!n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)`,
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac);

val shift_seq_def = Define `
  shift_seq k s = \i. s (i + k:num)`;

val SUM_SET_IN_LT = Q.store_thm("SUM_SET_IN_LT",
  `!s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s`,
  metis_tac[SUM_SET_IN_LE,LESS_LESS_EQ_TRANS]);

val BIJ_IMP_11 = Q.store_thm("BIJ_IMP_11",
  `BIJ f UNIV UNIV ==> !x y. (f x = f y) = (x = y)`,
  full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF] \\ metis_tac []);

val ALOOKUP_MAP_gen = Q.store_thm("ALOOKUP_MAP_gen",
  `∀f al x.
    ALOOKUP (MAP (λ(x,y). (x,f x y)) al) x =
    OPTION_MAP (f x) (ALOOKUP al x)`,
  gen_tac >> Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][]);

val FST_EQ_EQUIV = store_thm("FST_EQ_EQUIV",
  ``(FST x = y) <=> ?z. x = (y,z)``,
  Cases_on `x` \\ full_simp_tac(srw_ss())[]);

val map_fromAList = Q.store_thm("map_fromAList",
  `map f (fromAList ls) = fromAList (MAP (λ(k,v). (k, f v)) ls)`,
  Induct_on`ls` >> simp[fromAList_def] >>
  Cases >> simp[fromAList_def] >>
  simp[wf_fromAList,map_insert])

val LLOOKUP_def = Define `
  (LLOOKUP [] n = NONE) /\
  (LLOOKUP (x::xs) n = if n = 0 then SOME x else LLOOKUP xs (n-1:num))`;

val LLOOKUP_EQ_EL = Q.store_thm("LLOOKUP_EQ_EL",
  `!xs n y. LLOOKUP xs n = SOME y <=> n < LENGTH xs /\ (y = EL n xs)`,
  Induct \\ fs [LLOOKUP_def] \\ rw [] THEN1 metis_tac []
  \\ Cases_on `n` \\ fs [ADD1] \\ eq_tac \\ rw []);

val LLOOKUP_THM = Q.store_thm("LLOOKUP_THM",
  `!xs n. LLOOKUP xs n = if n < LENGTH xs then SOME (EL n xs) else NONE`,
  Induct \\ full_simp_tac(srw_ss())[LLOOKUP_def] \\ srw_tac[][] THEN1 decide_tac
  \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ decide_tac);

val LLOOKUP_DROP = Q.store_thm("LLOOKUP_DROP",
  `(LLOOKUP (DROP f xs) n = LLOOKUP xs (f + n))`,
  Cases_on `DROP f xs = []` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[DROP_NIL]
  \\ full_simp_tac(srw_ss())[LLOOKUP_THM] THEN1 decide_tac
  \\ `f + n < LENGTH xs <=> n < LENGTH xs - f` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ match_mp_tac (GSYM EL_DROP) \\ decide_tac);

val LLOOKUP_TAKE_IMP = Q.store_thm("LLOOKUP_TAKE_IMP",
  `(LLOOKUP (TAKE f xs) n = SOME x) ==>
    (LLOOKUP xs n = SOME x)`,
  simp[LLOOKUP_THM,LENGTH_TAKE_EQ] >>
  srw_tac[ARITH_ss][]
  \\ match_mp_tac (GSYM EL_TAKE)
  \\ fsrw_tac[ARITH_ss][]);

val LLOOKUP_LUPDATE = Q.store_thm("LLOOKUP_LUPDATE",
  `!xs i n x. LLOOKUP (LUPDATE x i xs) n =
               if i <> n then LLOOKUP xs n else
               if i < LENGTH xs then SOME x else NONE`,
  Induct \\ full_simp_tac(srw_ss())[LLOOKUP_def,LUPDATE_def]
  \\ Cases_on `i` \\ full_simp_tac(srw_ss())[LLOOKUP_def,LUPDATE_def]
  \\ rpt strip_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ `F` by decide_tac);

val _ = Datatype `
  app_list = List ('a list) | Append app_list app_list | Nil`

val append_aux_def = Define `
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))`;

val append_def = Define `
  append l = append_aux l []`;

val append_aux_thm = Q.store_thm("append_aux_thm",
  `!l xs. append_aux l xs = append_aux l [] ++ xs`,
  Induct \\ metis_tac [APPEND,APPEND_ASSOC,append_aux_def]);

val append_thm = Q.store_thm("append_thm[simp]",
  `append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []`,
  fs [append_def,append_aux_def]
  \\ once_rewrite_tac [append_aux_thm] \\ fs []);

val SmartAppend_def = Define`
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)`;
val _ = export_rewrites["SmartAppend_def"];

val SmartAppend_thm = Q.store_thm("SmartAppend_thm",
  `∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2`,
  Cases \\ Cases \\ rw[]);

val append_SmartAppend = Q.store_thm("append_SmartAppend[simp]",
  `append (SmartAppend l1 l2) = append l1 ++ append l2`,
  rw[append_def,SmartAppend_thm,append_aux_def]
  \\ rw[Once append_aux_thm]);

val GENLIST_eq_MAP = Q.store_thm("GENLIST_eq_MAP",
  `GENLIST f n = MAP g ls ⇔
   LENGTH ls = n ∧ ∀m. m < n ⇒ f m = g (EL m ls)`,
  srw_tac[][LIST_EQ_REWRITE,EQ_IMP_THM,EL_MAP])

val GENLIST_ID = Q.store_thm("GENLIST_ID",
  `!x. GENLIST (\i. EL i x) (LENGTH x) = x`,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ full_simp_tac(srw_ss())[] \\ simp_tac std_ss [GENLIST,GSYM ADD1]
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,rich_listTheory.EL_LENGTH_APPEND]
  \\ rpt strip_tac \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp_tac std_ss [Once (GSYM th)])
  \\ full_simp_tac(srw_ss())[GENLIST_FUN_EQ] \\ srw_tac[][]
  \\ match_mp_tac (GSYM rich_listTheory.EL_APPEND1) \\ full_simp_tac(srw_ss())[]);

val ZIP_GENLIST1 = Q.store_thm("ZIP_GENLIST1",
  `∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n`,
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]);

val MAP2i_def = Define`
  (MAP2i f [] [] = []) /\
  (MAP2i f (h1::t1) (h2::t2) = f 0 h1 h2::MAP2i (f o SUC) t1 t2)`;
val _ = export_rewrites["MAP2i_def"];

val MAP2i_ind = theorem"MAP2i_ind";

val LENGTH_MAP2i = Q.store_thm("LENGTH_MAP2i[simp]",
  `∀f l1 l2. LENGTH l1 = LENGTH l2 ⇒ LENGTH (MAP2i f l1 l2) = LENGTH l2`,
  ho_match_mp_tac MAP2i_ind \\ rw[]);

val EL_MAP2i = Q.store_thm("EL_MAP2i",
  `∀f l1 l2 n. n < LENGTH l1 ∧ n < LENGTH l2 ⇒
    EL n (MAP2i f l1 l2) = f n (EL n l1) (EL n l2)`,
  ho_match_mp_tac MAP2i_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]);

val MAP3_def = Define`
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)`;
val _ = export_rewrites["MAP3_def"];

val MAP3_ind = theorem"MAP3_ind";

val LENGTH_MAP3 = Q.store_thm("LENGTH_MAP3[simp]",
  `∀f l1 l2 l3. LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3 ⇒ LENGTH (MAP3 f l1 l2 l3) = LENGTH l3`,
  ho_match_mp_tac MAP3_ind \\ rw[]);

val EL_MAP3 = Q.store_thm("EL_MAP3",
  `∀f l1 l2 l3 n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ n < LENGTH l3 ⇒
    EL n (MAP3 f l1 l2 l3) = f (EL n l1) (EL n l2) (EL n l3)`,
  ho_match_mp_tac MAP3_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]);

val LENGTH_TAKE_EQ_MIN = Q.store_thm("LENGTH_TAKE_EQ_MIN",
  `!n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)`,
  simp[LENGTH_TAKE_EQ] \\ full_simp_tac(srw_ss())[MIN_DEF] \\ decide_tac);

val hd_drop = Q.store_thm ("hd_drop",
  `!n l. n < LENGTH l ⇒ HD (DROP n l) = EL n l`,
  Induct_on `l` >>
  srw_tac[][DROP_def] >>
  `n - 1 < LENGTH l` by decide_tac >>
  res_tac >>
  `0 < n` by decide_tac >>
  srw_tac[][EL_CONS] >>
  `n - 1 = PRE n` by decide_tac >>
  srw_tac[][]);

val INJ_EXTEND = Q.store_thm("INJ_EXTEND",
  `INJ b s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) b) (x INSERT s) (y INSERT t)`,
  full_simp_tac(srw_ss())[INJ_DEF,combinTheory.APPLY_UPDATE_THM] \\ METIS_TAC []);

val MEM_LIST_REL = Q.store_thm("MEM_LIST_REL",
  `!xs ys P x. LIST_REL P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y`,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ RES_TAC \\ METIS_TAC []);

val LIST_REL_MEM = Q.store_thm("LIST_REL_MEM",
  `!xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys`,
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]);

val LIST_REL_REVERSE_EQ =
  IMP_ANTISYM_RULE
    (EVERY2_REVERSE |> SPEC_ALL)
    (EVERY2_REVERSE |> Q.SPECL[`R`,`REVERSE l1`,`REVERSE l2`]
                    |> SIMP_RULE std_ss [REVERSE_REVERSE])
  |> SYM |> curry save_thm"LIST_REL_REVERSE_EQ";

val LIST_REL_GENLIST_I = Q.store_thm("LIST_REL_GENLIST_I",
  `!xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)`,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,GENLIST,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [LIST_REL_APPEND_SING]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `n < LENGTH xs`
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1]
    \\ `n = LENGTH xs` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD])
  THEN1 (`n < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
    \\ POP_ASSUM MP_TAC \\ Q.PAT_X_ASSUM `!x.bb` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1])
  \\ POP_ASSUM (MP_TAC o Q.SPEC `LENGTH xs`)
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,EL,HD]);

val LIST_REL_lookup_fromList = Q.store_thm("LIST_REL_lookup_fromList",
  `LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args`,
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]);

val lookup_fromList_outside = Q.store_thm("lookup_fromList_outside",
  `!k. LENGTH args <= k ==> (lookup k (fromList args) = NONE)`,
  SIMP_TAC std_ss [lookup_fromList] \\ DECIDE_TAC);

val lemmas = Q.prove(
  `(2 + 2 * n - 1 = 2 * n + 1:num) /\
    (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'':num) /\
    (2 * m = 2 * n <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)`,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 2 = n MOD 2)``)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 2:num``)]
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[MOD_EQ_0,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

val IN_domain = Q.store_thm("IN_domain",
  `!n x t1 t2.
      (n IN domain LN <=> F) /\
      (n IN domain (LS x) <=> (n = 0)) /\
      (n IN domain (BN t1 t2) <=>
         n <> 0 /\ (if EVEN n then ((n-1) DIV 2) IN domain t1
                              else ((n-1) DIV 2) IN domain t2)) /\
      (n IN domain (BS t1 x t2) <=>
         n = 0 \/ (if EVEN n then ((n-1) DIV 2) IN domain t1
                             else ((n-1) DIV 2) IN domain t2))`,
  full_simp_tac(srw_ss())[domain_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `n = 0` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `EVEN n` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM ODD_EVEN]
  \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[lemmas]
  \\ Cases_on `m` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[lemmas])

val map_map_K = Q.store_thm("map_map_K",
  `!t. map (K a) (map (K a) t) = map (K a) t`,
  Induct \\ full_simp_tac(srw_ss())[map_def]);

val lookup_map_K = Q.store_thm("lookup_map_K",
  `!t n. lookup n (map (K x) t) = if n IN domain t then SOME x else NONE`,
  Induct \\ full_simp_tac(srw_ss())[IN_domain,map_def,lookup_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `EVEN n` \\ full_simp_tac(srw_ss())[]);

val lookup_any_def = Define `
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m`;

val alist_insert_def = Define `
  (alist_insert [] xs t = t) /\
  (alist_insert vs [] t = t) /\
  (alist_insert (v::vs) (x::xs) t = insert v x (alist_insert vs xs t))`

val lookup_alist_insert = store_thm("lookup_alist_insert",
  ``!x y t z. LENGTH x = LENGTH y ==>
    (lookup z (alist_insert x y t) =
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)``,
    ho_match_mp_tac (fetch "-" "alist_insert_ind")>>
    srw_tac[][]>-
      (Cases_on`y`>>
      full_simp_tac(srw_ss())[LENGTH,alist_insert_def]) >>
    Cases_on`z=x`>>
      srw_tac[][lookup_def,alist_insert_def]>>
    full_simp_tac(srw_ss())[lookup_insert])

val domain_alist_insert = Q.store_thm("domain_alist_insert",
  `!a b locs. LENGTH a = LENGTH b ==>
    domain (alist_insert a b locs) = domain locs UNION set a`,
  Induct_on`a`>>Cases_on`b`>>full_simp_tac(srw_ss())[alist_insert_def]>>srw_tac[][]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM])

val fromList2_def = Define `
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)`

val EVEN_fromList2_lemma = prove(
  ``!l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x``,
  Induct \\ full_simp_tac(srw_ss())[FOLDL] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC);

val EVEN_fromList2 = Q.store_thm("EVEN_fromList2",
  `!l n. n IN domain (fromList2 l) ==> EVEN n`,
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ full_simp_tac(srw_ss())[]);

val SUBMAP_FDOM_SUBSET = Q.store_thm("SUBMAP_FDOM_SUBSET",
  `f1 ⊑ f2 ⇒ FDOM f1 ⊆ FDOM f2`,
  srw_tac[][SUBMAP_DEF,SUBSET_DEF])

val SUBMAP_FRANGE_SUBSET = Q.store_thm("SUBMAP_FRANGE_SUBSET",
  `f1 ⊑ f2 ⇒ FRANGE f1 ⊆ FRANGE f2`,
  srw_tac[][SUBMAP_DEF,SUBSET_DEF,IN_FRANGE] >> metis_tac[])

val FDIFF_def = Define `
  FDIFF f1 s = DRESTRICT f1 (COMPL s)`;

val FDOM_FDIFF = Q.store_thm("FDOM_FDIFF",
  `x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN f2)`,
  full_simp_tac(srw_ss())[FDIFF_def,DRESTRICT_DEF]);

val INJ_FAPPLY_FUPDATE = Q.store_thm("INJ_FAPPLY_FUPDATE",
  `INJ ($' f) (FDOM f) (FRANGE f) ∧
   s = k INSERT FDOM f ∧ v ∉ FRANGE f ∧
   t = v INSERT FRANGE f
  ⇒
   INJ ($' (f |+ (k,v))) s t`,
  srw_tac[][INJ_DEF,FAPPLY_FUPDATE_THM] >> srw_tac[][] >>
  pop_assum mp_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[IN_FRANGE] >>
  METIS_TAC[])

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]
  |> curry save_thm "NUM_NOT_IN_FDOM";

val EXISTS_NOT_IN_FDOM_LEMMA = Q.prove(
  `?x. ~(x IN FDOM (refs:num|->'a))`,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NOTIN_FDOM = Q.store_thm("LEAST_NOTIN_FDOM",
  `(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs`,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ full_simp_tac(srw_ss())[]);

val list_to_num_set_def = Define `
  (list_to_num_set [] = LN) /\
  (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))`;

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

val domain_list_to_num_set = Q.store_thm("domain_list_to_num_set",
  `!xs. x IN domain (list_to_num_set xs) <=> MEM x xs`,
  Induct \\ full_simp_tac(srw_ss())[list_to_num_set_def]);

val domain_list_insert = Q.store_thm("domain_list_insert",
  `!xs x t.
      x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t`,
  Induct \\ full_simp_tac(srw_ss())[list_insert_def] \\ METIS_TAC []);

val domain_FOLDR_delete = Q.store_thm("domain_FOLDR_delete",
  `∀ls live. domain (FOLDR delete live ls) =
  (domain live) DIFF (set ls)`,
  Induct>>
  full_simp_tac(srw_ss())[DIFF_INSERT,EXTENSION]>>
  metis_tac[])

val lookup_list_to_num_set = Q.store_thm("lookup_list_to_num_set",
  `!xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME () else NONE`,
  Induct \\ srw_tac [] [list_to_num_set_def,lookup_def,lookup_insert] \\ full_simp_tac(srw_ss())[]);

val OPTION_BIND_SOME = Q.store_thm("OPTION_BIND_SOME",
  `∀f. OPTION_BIND f SOME = f`,
  Cases >> simp[])

val take1 = Q.store_thm ("take1",
  `!l. l ≠ [] ⇒ TAKE 1 l = [EL 0 l]`,
  Induct_on `l` >> srw_tac[][]);

val SPLIT_LIST = Q.store_thm("SPLIT_LIST",
  `!xs.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)`,
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ full_simp_tac(srw_ss())[DIV_LE_X] \\ DECIDE_TAC);

val EXISTS_ZIP = Q.store_thm ("EXISTS_ZIP",
  `!l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)`,
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []);

val EVERY_ZIP = Q.store_thm ("EVERY_ZIP",
  `!l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)`,
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []);

val ZIP_MAP_FST_SND_EQ = store_thm("ZIP_MAP_FST_SND_EQ",
  ``∀ls. ZIP (MAP FST ls,MAP SND ls) = ls``,
  Induct>>full_simp_tac(srw_ss())[])

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

val list_inter_def = Define `
  list_inter xs ys = FILTER (\y. MEM y xs) ys`;

val SING_HD = Q.store_thm("SING_HD",
  `(([HD xs] = xs) <=> (LENGTH xs = 1)) /\
    ((xs = [HD xs]) <=> (LENGTH xs = 1))`,
  Cases_on `xs` \\ full_simp_tac(srw_ss())[LENGTH_NIL] \\ METIS_TAC []);

val ALOOKUP_SNOC = Q.store_thm("ALOOKUP_SNOC",
  `∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE`,
  Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][])

val ALOOKUP_GENLIST = store_thm("ALOOKUP_GENLIST",
  ``∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE``,
  gen_tac >> Induct >> simp[GENLIST] >> srw_tac[][] >> full_simp_tac(srw_ss())[ALOOKUP_SNOC] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][])

val ALOOKUP_ZIP_FAIL = store_thm("ALOOKUP_ZIP_FAIL",
  ``∀A B x.
  LENGTH A = LENGTH B ⇒
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)``,
  srw_tac[][]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  full_simp_tac(srw_ss())[MAP_ZIP])

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
  ho_match_mp_tac anub_ind >> srw_tac[][anub_def] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD])

val ALOOKUP_anub = Q.store_thm("ALOOKUP_anub",
  `ALOOKUP (anub ls acc) k =
    if MEM k acc then ALOOKUP (anub ls acc) k
    else ALOOKUP ls k`,
  qid_spec_tac`acc` >>
  Induct_on`ls` >>
  srw_tac[][anub_def] >>
  Cases_on`h`>>srw_tac[][anub_def]>>full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`acc`mp_tac) >>
    srw_tac[][] ) >>
  first_x_assum(qspec_then`q::acc`mp_tac) >>
  srw_tac[][])

val anub_eq_nil = Q.store_thm("anub_eq_nil",
  `anub x y = [] ⇔ EVERY (combin$C MEM y) (MAP FST x)`,
  qid_spec_tac`y` >>
  Induct_on`x`>>srw_tac[][anub_def]>>
  Cases_on`h`>>srw_tac[][anub_def])

val EVERY_anub_suff = store_thm("EVERY_anub_suff",
  ``∀ls acc.
    (∀x. ¬MEM x acc ⇒ case ALOOKUP ls x of SOME v => P (x,v) | NONE => T)
    ⇒ EVERY P (anub ls acc)``,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >- (
    first_x_assum(match_mp_tac) >>
    srw_tac[][] >>
    res_tac >>
    pop_assum mp_tac >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] )
  >- (
    res_tac >> full_simp_tac(srw_ss())[] ) >>
  first_x_assum match_mp_tac >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  `q ≠ x` by full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[])

val anub_notin_acc = Q.store_thm("anub_notin_acc",
  `∀ls acc. MEM x acc ⇒ ¬MEM x (MAP FST (anub ls acc))`,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >>
  metis_tac[])

val anub_tl_anub = Q.store_thm("anub_tl_anub",
  `∀x y h t. anub x y = h::t ⇒ ∃a b. t = anub a b ∧ set a ⊆ set x ∧ set b ⊆ set ((FST h)::y)`,
  Induct >> srw_tac[][anub_def] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[anub_def] >>
  pop_assum mp_tac  >> srw_tac[][] >>
  res_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac[MEM] )

val anub_all_distinct_keys = Q.store_thm("anub_all_distinct_keys",
  `∀ls acc.
    ALL_DISTINCT acc ⇒
    ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)`,
  Induct>>srw_tac[][anub_def]>>PairCases_on`h`>>full_simp_tac(srw_ss())[anub_def]>>
  srw_tac[][]>>
  `ALL_DISTINCT (h0::acc)` by full_simp_tac(srw_ss())[ALL_DISTINCT]>>res_tac>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND]>>
  metis_tac[])

val MEM_anub_ALOOKUP = store_thm("MEM_anub_ALOOKUP",
  ``MEM (k,v) (anub ls []) ⇒
    ALOOKUP ls k = SOME v``,
  srw_tac[][]>>
  Q.ISPECL_THEN[`ls`,`[]`] assume_tac anub_all_distinct_keys>>
  Q.ISPECL_THEN [`ls`,`k`,`[]`] assume_tac (GEN_ALL ALOOKUP_anub)>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM])

val FEMPTY_FUPDATE_EQ = Q.store_thm("FEMPTY_FUPDATE_EQ",
  `∀x y. (FEMPTY |+ x = FEMPTY |+ y) ⇔ (x = y)`,
  Cases >> Cases >> srw_tac[][fmap_eq_flookup,FDOM_FUPDATE,FLOOKUP_UPDATE] >>
  Cases_on`q=q'`>>srw_tac[][] >- (
    srw_tac[][EQ_IMP_THM] >>
    pop_assum(qspec_then`q`mp_tac) >> srw_tac[][] ) >>
  qexists_tac`q`>>srw_tac[][])

val FUPDATE_LIST_EQ_FEMPTY = Q.store_thm("FUPDATE_LIST_EQ_FEMPTY",
  `∀fm ls. fm |++ ls = FEMPTY ⇔ fm = FEMPTY ∧ ls = []`,
  srw_tac[][EQ_IMP_THM,FUPDATE_LIST_THM] >>
  full_simp_tac(srw_ss())[GSYM fmap_EQ_THM,FDOM_FUPDATE_LIST])

val IS_SOME_EXISTS = Q.store_thm("IS_SOME_EXISTS",
  `∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x`,
  Cases >> simp[])

val _ = type_abbrev("num_set",``:unit spt``);
val _ = type_abbrev("num_map",``:'a spt``);

val toAList_domain = Q.store_thm("toAList_domain",`
  ∀x. MEM x (MAP FST (toAList t)) ⇔ x ∈ domain t`,
  full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup])

val domain_nat_set_from_list = Q.store_thm("domain_nat_set_from_list",
  `∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls`,
  Induct >> simp[sptreeTheory.domain_insert] >>
  srw_tac[][EXTENSION] >> metis_tac[])
val _ = export_rewrites["domain_nat_set_from_list"]

val wf_nat_set_from_list = Q.store_thm("wf_nat_set_from_list",
  `∀ls ns. wf ns ⇒ wf (FOLDL (λs n. insert n z s) ns ls)`,
  Induct >> simp[] >> srw_tac[][sptreeTheory.wf_insert])

val BIT_11 = Q.store_thm("BIT_11",
  `∀n m. (BIT n = BIT m) ⇔ (n = m)`,
  simp[EQ_IMP_THM] >>
  Induct >> simp[BIT0_ODD,FUN_EQ_THM] >- (
    Cases >> simp[] >>
    qexists_tac`1` >> simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  simp[GSYM BIT_DIV2] >>
  Cases >> simp[GSYM BIT_DIV2] >- (
    qexists_tac`1` >>
    simp[BIT_ZERO] >>
    simp[BIT_def,BITS_THM] ) >>
  srw_tac[][] >>
  first_x_assum MATCH_MP_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  first_x_assum(qspec_then`x*2`mp_tac) >>
  simp[arithmeticTheory.MULT_DIV])

val BIT_11_2 = Q.store_thm("BIT_11_2",
  `∀n m. (∀z. (z < 2 ** (MAX n m)) ⇒ (BIT n z ⇔ BIT m z)) ⇔ (n = m)`,
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
  srw_tac[][] >> first_x_assum MATCH_MP_TAC >>
  full_simp_tac(srw_ss())[arithmeticTheory.MAX_DEF] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  simp[arithmeticTheory.EXP])

val binary_induct = Q.store_thm("binary_induct",
  `∀P. P (0:num) ∧ (∀n. P n ⇒ P (2*n) ∧ P (2*n+1)) ⇒ ∀n. P n`,
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

val BIT_TIMES2 = Q.store_thm("BIT_TIMES2",
  `BIT z (2 * n) ⇔ 0 < z ∧ BIT (PRE z) n`,
  Cases_on`z`>>simp[]>-(
    simp[BIT0_ODD] >>
    simp[arithmeticTheory.ODD_EVEN] >>
    simp[arithmeticTheory.EVEN_DOUBLE] ) >>
  qmatch_rename_tac`BIT (SUC z) (2 * n) ⇔ BIT z n` >>
  qspecl_then[`z`,`n`,`1`]mp_tac BIT_SHIFT_THM >>
  simp[arithmeticTheory.ADD1])

val BIT_TIMES2_1 = Q.store_thm("BIT_TIMES2_1",
  `∀n z. BIT z (2 * n + 1) ⇔ (z=0) ∨ BIT z (2 * n)`,
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

val LOG2_TIMES2 = Q.store_thm("LOG2_TIMES2",
  `0 < n ⇒ (LOG2 (2 * n) = SUC (LOG2 n))`,
  srw_tac[][LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1])

val LOG2_TIMES2_1 = Q.store_thm("LOG2_TIMES2_1",
  `∀n. 0 < n ⇒ (LOG2 (2 * n + 1) = LOG2 (2 * n))`,
  srw_tac[][LOG2_def] >>
  MATCH_MP_TAC logrootTheory.LOG_UNIQUE >>
  simp[GSYM LOG2_def,LOG2_TIMES2] >>
  simp[arithmeticTheory.EXP] >>
  conj_tac >- (
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac`2*n` >> simp[] >>
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`2 ** LOG2 n ≤ X` >- srw_tac[][] >>
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
    qsuff_tac`X < 2 * 2 ** LOG2 n` >- srw_tac[][] >>
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

val C_BIT_11 = Q.store_thm("C_BIT_11",
  `∀n m. (∀z. (z ≤ LOG2 (MAX n m)) ⇒ (BIT z n ⇔ BIT z m)) ⇔ (n = m)`,
  simp[Once EQ_IMP_THM] >>
  ho_match_mp_tac binary_induct >>
  simp[] >>
  conj_tac >- (
    Cases >> simp[] >>
    qexists_tac`LOG2 (SUC n)` >>
    simp[BIT_LOG2,BIT_ZERO] ) >>
  gen_tac >> strip_tac >>
  simp[BIT_TIMES2,BIT_TIMES2_1] >>
  srw_tac[][] >- (
    Cases_on`n=0`>>full_simp_tac(srw_ss())[]>-(
      Cases_on`m=0`>>full_simp_tac(srw_ss())[]>>
      first_x_assum(qspec_then`LOG2 m`mp_tac)>>simp[BIT_ZERO] >>
      simp[BIT_LOG2]) >>
    `¬ODD m` by (
      simp[SYM BIT0_ODD] >>
      first_x_assum(qspec_then`0`mp_tac) >>
      simp[] ) >>
    full_simp_tac(srw_ss())[arithmeticTheory.ODD_EVEN] >>
    full_simp_tac(srw_ss())[arithmeticTheory.EVEN_EXISTS] >>
    simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
    first_x_assum MATCH_MP_TAC >>
    srw_tac[][] >>
    first_x_assum(qspec_then`SUC z`mp_tac) >>
    impl_tac >- (
      full_simp_tac(srw_ss())[arithmeticTheory.MAX_DEF] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[] >> simp[LOG2_TIMES2] ) >>
    simp[BIT_TIMES2] ) >>
  Cases_on`n=0`>>full_simp_tac(srw_ss())[]>-(
    full_simp_tac(srw_ss())[BIT_ZERO] >>
    Cases_on`m=0`>>full_simp_tac(srw_ss())[BIT_ZERO] >>
    Cases_on`m=1`>>full_simp_tac(srw_ss())[]>>
    first_x_assum(qspec_then`LOG2 m`mp_tac) >>
    simp[arithmeticTheory.MAX_DEF,BIT_LOG2] >>
    spose_not_then strip_assume_tac >>
    qspec_then`m`mp_tac logrootTheory.LOG_MOD >>
    simp[GSYM LOG2_def] ) >>
  `ODD m` by (
    simp[SYM BIT0_ODD] >>
    first_x_assum(qspec_then`0`mp_tac) >>
    simp[] ) >>
  full_simp_tac(srw_ss())[arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
  simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
  first_x_assum MATCH_MP_TAC >>
  srw_tac[][] >>
  first_x_assum(qspec_then`SUC z`mp_tac) >>
  impl_tac >- (
    full_simp_tac(srw_ss())[arithmeticTheory.MAX_DEF] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> simp[LOG2_TIMES2_1,LOG2_TIMES2] ) >>
  simp[BIT_TIMES2_1,BIT_TIMES2])

val BIT_num_from_bin_list_leading = Q.store_thm("BIT_num_from_bin_list_leading",
  `∀l x. EVERY ($> 2) l ∧ LENGTH l ≤ x ⇒ ¬BIT x (num_from_bin_list l)`,
  simp[numposrepTheory.num_from_bin_list_def] >>
  srw_tac[][] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH l` >>
  simp[numposrepTheory.l2n_lt] )

val least_from_def = Define`
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P`

val LEAST_thm = Q.store_thm("LEAST_thm",
  `$LEAST P = least_from P 0`,
  srw_tac[][least_from_def,ETA_AX])

val least_from_thm = Q.store_thm("least_from_thm",
  `least_from P n = if P n then n else least_from P (n+1)`,
  srw_tac[][least_from_def] >>
  numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- metis_tac[] >>
    qmatch_rename_tac`a = b` >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] ))

val FILTER_F = Q.store_thm("FILTER_F",
  `∀ls. FILTER (λx. F) ls = []`,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

val OPTREL_SOME = Q.store_thm("OPTREL_SOME",
  `(!R x y. OPTREL R (SOME x) y <=> (?z. y = SOME z /\ R x z)) /\
    (!R x y. OPTREL R x (SOME y) <=> (?z. x = SOME z /\ R z y))`,
    srw_tac[][optionTheory.OPTREL_def])

val LIST_REL_O = Q.store_thm("LIST_REL_O",
  `∀R1 R2 l1 l2. LIST_REL (R1 O R2) l1 l2 ⇔ ∃l3. LIST_REL R2 l1 l3 ∧ LIST_REL R1 l3 l2`,
  rpt gen_tac >>
  simp[EVERY2_EVERY,EVERY_MEM,EQ_IMP_THM,GSYM AND_IMP_INTRO,MEM_ZIP,PULL_EXISTS,O_DEF] >>
  srw_tac[][] >- (
    full_simp_tac(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH l2)` >>
    simp[MEM_ZIP,PULL_EXISTS] ) >>
  metis_tac[])

val OPTREL_O_lemma = Q.prove(
  `∀R1 R2 l1 l2. OPTREL (R1 O R2) l1 l2 ⇔ ∃l3. OPTREL R2 l1 l3 ∧ OPTREL R1 l3 l2`,
  srw_tac[][optionTheory.OPTREL_def,EQ_IMP_THM,O_DEF,PULL_EXISTS] >> metis_tac[])

val OPTREL_O = Q.store_thm("OPTREL_O",
  `∀R1 R2. OPTREL (R1 O R2) = OPTREL R1 O OPTREL R2`,
  srw_tac[][FUN_EQ_THM,OPTREL_O_lemma,O_DEF])

val FUNPOW_mono = Q.store_thm("FUNPOW_mono",
  `(∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y`,
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> srw_tac[][])

val OPTREL_trans = Q.store_thm("OPTREL_trans",
  `∀R x y z. (∀a b c. (x = SOME a) ∧ (y = SOME b) ∧ (z = SOME c) ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z`,
  srw_tac[][optionTheory.OPTREL_def])

val UPDATE_LIST_def = Define`
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`
val _ = Parse.add_infix("=++",500,Parse.LEFT)
val _ = Parse.overload_on("=++",``UPDATE_LIST``)

val UPDATE_LIST_THM = Q.store_thm("UPDATE_LIST_THM",
  `∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)`,
  srw_tac[][UPDATE_LIST_def,pairTheory.UNCURRY])

val APPLY_UPDATE_LIST_ALOOKUP = Q.store_thm("APPLY_UPDATE_LIST_ALOOKUP",
  `∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y`,
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  srw_tac[][] >> BasicProvers.CASE_TAC)

val IS_SUFFIX_CONS = Q.store_thm("IS_SUFFIX_CONS",
  `∀l1 l2 a. IS_SUFFIX l1 l2 ⇒ IS_SUFFIX (a::l1) l2`,
  srw_tac[][rich_listTheory.IS_SUFFIX_APPEND] >>
  qexists_tac`a::l` >>srw_tac[][])

val INFINITE_INJ_NOT_SURJ = Q.store_thm("INFINITE_INJ_NOT_SURJ",
  `∀s. INFINITE s ⇔ (s ≠ ∅) ∧ (∃f. INJ f s s ∧ ¬SURJ f s s)`,
  srw_tac[][EQ_IMP_THM] >- (
    PROVE_TAC[INFINITE_INHAB,MEMBER_NOT_EMPTY] )
  >- (
    full_simp_tac(srw_ss())[infinite_num_inj] >>
    qexists_tac`λx. if ∃n. x = f n then f (SUC (LEAST n. x = f n)) else x` >>
    conj_asm1_tac >- (
      full_simp_tac(srw_ss())[INJ_IFF] >>
      conj_asm1_tac >- srw_tac[][] >>
      srw_tac[][] >- (
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- PROVE_TAC[] >>
        srw_tac[][] ) >>
      numLib.LEAST_ELIM_TAC >>
      srw_tac[][] >>
      metis_tac[] ) >>
    full_simp_tac(srw_ss())[SURJ_DEF,INJ_IFF] >>
    qexists_tac`f 0` >>
    simp[] >>
    srw_tac[][] >>
    metis_tac[]) >>
  full_simp_tac(srw_ss())[SURJ_DEF] >- (full_simp_tac(srw_ss())[INJ_IFF] >> metis_tac[]) >>
  simp[infinite_num_inj] >>
  qexists_tac`λn. FUNPOW f n x` >>
  simp[INJ_IFF] >>
  conj_asm1_tac >- (
    Induct >>
    simp[arithmeticTheory.FUNPOW_SUC] >>
    full_simp_tac(srw_ss())[INJ_IFF] ) >>
  Induct >> simp[] >- (
    Cases >> simp[arithmeticTheory.FUNPOW_SUC] >>
    metis_tac[] ) >>
  Cases >> simp[arithmeticTheory.FUNPOW_SUC] >> full_simp_tac(srw_ss())[INJ_IFF] >>
  metis_tac[] )


val find_index_def = Define`
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))`

val find_index_NOT_MEM = Q.store_thm("find_index_NOT_MEM",
  `∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)`,
  Induct >> srw_tac[][find_index_def])

val find_index_MEM = Q.store_thm("find_index_MEM",
  `!ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)`,
  Induct >> srw_tac[][find_index_def] >- (
    qexists_tac`0`>>srw_tac[][] ) >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  srw_tac[][]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1])

val find_index_LEAST_EL = Q.store_thm("find_index_LEAST_EL",
  `∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE`,
  Induct >- srw_tac[][find_index_def] >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>full_simp_tac(srw_ss())[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> srw_tac[][]) >>
    Cases >> srw_tac[][] >>
    first_x_assum (qspec_then`0`mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  srw_tac[][] >>
  Cases_on`n`>>full_simp_tac(srw_ss())[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  srw_tac[][] >>
  qmatch_rename_tac`m = n` >>
  Cases_on`m < n` >- (res_tac >> full_simp_tac(srw_ss())[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> full_simp_tac(srw_ss())[GSYM ADD1] ) >>
  DECIDE_TAC )

val find_index_LESS_LENGTH = Q.store_thm(
"find_index_LESS_LENGTH",
`∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)`,
Induct >> srw_tac[][find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val ALOOKUP_find_index_NONE = Q.store_thm("ALOOKUP_find_index_NONE",
  `(ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)`,
  srw_tac[][ALOOKUP_FAILS] >> srw_tac[][GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD])

val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >> srw_tac[][find_index_def] >-
    (qexists_tac`0`>>simp[]) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]
val ALOOKUP_find_index_SOME = Q.store_thm("ALOOKUP_find_index_SOME",
  `(ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))`,
  srw_tac[][] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> full_simp_tac(srw_ss())[EL_MAP])

val find_index_ALL_DISTINCT_EL = Q.store_thm(
"find_index_ALL_DISTINCT_EL",
`∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))`,
Induct >- srw_tac[][] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_ALL_DISTINCT_EL_eq = Q.store_thm("find_index_ALL_DISTINCT_EL_eq",
  `∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)`,
  srw_tac[][EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    full_simp_tac(srw_ss())[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    full_simp_tac(srw_ss())[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL])

val find_index_APPEND_same = Q.store_thm("find_index_APPEND_same",
  `!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)`,
  Induct >> srw_tac[][find_index_def])

val find_index_ALL_DISTINCT_REVERSE = Q.store_thm("find_index_ALL_DISTINCT_REVERSE",
  `∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))`,
  srw_tac[][] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by srw_tac[][ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >> srw_tac[][] >>
  qmatch_assum_rename_tac`z < LENGTH ls` >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

val THE_find_index_suff = Q.store_thm("THE_find_index_suff",
  `∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))`,
  srw_tac[][] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val find_index_APPEND1 = Q.store_thm("find_index_APPEND1",
  `∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)`,
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  srw_tac[][] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[])

val find_index_APPEND2 = Q.store_thm("find_index_APPEND2",
  `∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)`,
  Induct >> simp[find_index_def] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1])

val find_index_is_MEM = Q.store_thm("find_index_is_MEM",
  `∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls`,
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE])

val find_index_MAP_inj = Q.store_thm("find_index_MAP_inj",
  `∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)`,
  Induct >- simp[find_index_def] >>
  srw_tac[][] >> srw_tac[][find_index_def] >>
  metis_tac[])

val find_index_shift_0 = Q.store_thm("find_index_shift_0",
  `∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)`,
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
  srw_tac[][] >>
  Cases_on`find_index x ls 0`>>srw_tac[][] >>
  simp[])

val find_index_shift = Q.store_thm("find_index_shift",
  `∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)`,
  Induct >> simp[find_index_def] >> srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][])

val find_index_APPEND = Q.store_thm("find_index_APPEND",
  `∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x`,
  Induct >> simp[find_index_def] >> srw_tac[][] >>
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
    strip_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    full_simp_tac(srw_ss())[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][] >>
    Cases_on`v1`>>fsrw_tac[ARITH_ss][find_index_def]) >>
  strip_tac >>
  Cases_on`v1`>>full_simp_tac(srw_ss())[] >>
  Cases_on`P h`>>full_simp_tac(srw_ss())[find_index_def] >- (
    rev_full_simp_tac(srw_ss())[] >>
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
  srw_tac[][EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1` >>
    imp_res_tac PERM_LENGTH >> full_simp_tac(srw_ss())[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ (x = EL m l2)` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    srw_tac[][ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1` >>
  imp_res_tac PERM_LENGTH >>
  full_simp_tac(srw_ss())[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  full_simp_tac(srw_ss())[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  impl_tac >- simp[] >>
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
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`b`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`c`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`d`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  assume_tac (GSYM ZIP_MAP_FST_SND_EQ)>>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS])

val PERM_BIJ = Q.store_thm("PERM_BIJ",
  `∀l1 l2. PERM l1 l2 ⇒ ∃f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ (l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1)))`,
  ho_match_mp_tac PERM_IND >> simp[BIJ_EMPTY] >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(f i)` >>
    simp[EL_CONS,PRE_SUB1] >>
    full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
    conj_tac >- ( Cases >> simp[] ) >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(g i)` >>
    conj_tac >- ( Cases >> simp[] ) >>
    conj_tac >- ( Cases >> simp[] ) >>
    ( Cases >> simp[] )) >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))` >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >>
    full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))` >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[])) >>
  ntac 2 (srw_tac[][LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  full_simp_tac(srw_ss())[LENGTH_GENLIST] >>
  qexists_tac`f o f'` >>
  simp[combinTheory.o_DEF] >>
  full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
  qexists_tac`g' o g` >>
  simp[combinTheory.o_DEF] )

val PERM_EVERY = Q.store_thm("PERM_EVERY",
`∀ls ls'.
  PERM ls ls' ⇒
  (EVERY P ls ⇔ EVERY P ls')`,
  ho_match_mp_tac PERM_STRONG_IND>>srw_tac[][]>>metis_tac[])

val RTC_RINTER = Q.store_thm("RTC_RINTER",
  `!R1 R2 x y. RTC (R1 RINTER R2) x y ⇒ ((RTC R1) RINTER (RTC R2)) x y`,
  ntac 2 gen_tac >>
  match_mp_tac RTC_INDUCT >>
  simp[RINTER] >>
  metis_tac[RTC_CASES1] )

val RTC_invariant = Q.store_thm("RTC_invariant",
  `!R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y`,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER])

val RTC_RSUBSET = Q.store_thm("RTC_RSUBSET",
  `!R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)`,
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1])

val PERM_PART = store_thm("PERM_PART",
  ``∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)``,
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> srw_tac[][] >- (
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

val transitive_LESS = Q.store_thm("transitive_LESS",
  `transitive ($< : (num->num->bool))`,
  srw_tac[][relationTheory.transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = Q.store_thm("OPTION_EVERY_cong",
  `!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)`,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = Q.store_thm("OPTION_EVERY_mono",
  `(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op`,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val option_case_NONE_F = Q.store_thm("option_case_NONE_F",
  `(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)`,
  Cases_on`X`>>srw_tac[][])

val IS_PREFIX_THM = Q.store_thm("IS_PREFIX_THM",
 `!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)`,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val EVERY2_RC_same = Q.store_thm("EVERY2_RC_same",
  `EVERY2 (RC R) l l`,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]

val FOLDL_invariant = Q.store_thm("FOLDL_invariant",
  `!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)`,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val FOLDL_invariant_rest = Q.store_thm("FOLDL_invariant_rest",
  `∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)`,
  ntac 2 gen_tac >>
  Induct >> srw_tac[][] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> srw_tac[][])

val between_def = Define`
  between x y z ⇔ x:num ≤ z ∧ z < y`

val SUC_LEAST = Q.store_thm("SUC_LEAST",
  `!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))`,
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

val fmap_linv_unique = Q.store_thm("fmap_linv_unique",
  `!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)`,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = Q.store_thm("INJ_has_fmap_linv",
  `INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g`,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = Q.store_thm("has_fmap_linv_inj",
  `(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))`,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = Q.store_thm("fmap_linv_FAPPLY",
  `fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)`,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val o_f_cong = Q.store_thm("o_f_cong",
  `!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')`,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

val plus_compose = Q.store_thm("plus_compose",
  `!n:num m. $+ n o $+ m = $+ (n + m)`,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

(* TODO: move elsewhere? export as rewrite? *)
val IN_option_rwt = Q.store_thm(
"IN_option_rwt",
`(x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)`,
Cases_on `opt` >> srw_tac[][EQ_IMP_THM])

val IN_option_rwt2 = Q.store_thm(
"IN_option_rwt2",
`x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y`,
Cases_on `opt` >> srw_tac[][])

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

val FOLDR_transitive_property = Q.store_thm(
"FOLDR_transitive_property",
`!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)`,
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
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val FST_5tup = store_thm(
"FST_5tup",
``(λ(n,ns,b,x,y). n) = FST``,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

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

val INJ_I = Q.store_thm(
"INJ_I",
`∀s t. INJ I s t ⇔ s ⊆ t`,
SRW_TAC[][INJ_DEF,SUBSET_DEF])


val MAP_EQ_ID = Q.store_thm(
"MAP_EQ_ID",
`!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))`,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* Specialisations to FEMPTY *)

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = Q.store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
`FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)`,
Cases_on `x IN s` >>
srw_tac[][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(* FUPDATE_LIST stuff *)

(* Misc. *)

val LESS_1 = Q.store_thm(
"LESS_1",
`x < 1 ⇔ (x = 0:num)`,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]



  (* --------- SO additions --------- *)

val map_fst = Q.store_thm ("map_fst",
`!l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l`,
Induct_on `l` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]);

val map_some_eq = Q.store_thm ("map_some_eq",
`!l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)`,
 Induct_on `l1` >>
 srw_tac[][] >>
 Cases_on `l2` >>
 srw_tac[][]);

val map_some_eq_append = Q.store_thm ("map_some_eq_append",
`!l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)`,
metis_tac [map_some_eq, MAP_APPEND]);

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];


(* list misc *)

val LASTN_LEMMA = Q.store_thm("LASTN_LEMMA",
  `(LASTN (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LASTN (LENGTH xs + 1) (x::xs) = x::xs)`,
  MP_TAC (Q.SPEC `x::y::xs` LASTN_LENGTH_ID)
  \\ MP_TAC (Q.SPEC `x::xs` LASTN_LENGTH_ID) \\ full_simp_tac(srw_ss())[ADD1]);

val LASTN_TL = save_thm("LASTN_TL",
  LASTN_CONS |> Q.SPECL[`n+1`,`xs`]
  |> C MP (DECIDE``n < LENGTH xs ⇒ n + 1 ≤ LENGTH xs`` |> UNDISCH)
  |> SPEC_ALL |> DISCH_ALL);

val LASTN_LENGTH_LESS_EQ = Q.store_thm("LASTN_LENGTH_LESS_EQ",
  `!xs n. LENGTH xs <= n ==> LASTN n xs = xs`,
  full_simp_tac(srw_ss())[LASTN_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [listTheory.TAKE_LENGTH_TOO_LONG] \\ full_simp_tac(srw_ss())[]);

val LASTN_ALT = Q.store_thm("LASTN_ALT",
  `(LASTN n [] = []) /\
    (LASTN n (x::xs) = if LENGTH (x::xs) <= n then x::xs else LASTN n xs)`,
  srw_tac[][] THEN1 (full_simp_tac(srw_ss())[LASTN_def])
  THEN1 (match_mp_tac LASTN_LENGTH_LESS_EQ \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[LASTN_def] \\ REPEAT STRIP_TAC
  \\ `n <= LENGTH (REVERSE xs)` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ full_simp_tac(srw_ss())[]);

val LENGTH_LASTN_LESS = Q.store_thm("LENGTH_LASTN_LESS",
  `!xs n. LENGTH (LASTN n xs) <= LENGTH xs`,
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `n` assume_tac)
  \\ decide_tac);

val MAP_EQ_MAP_IMP = Q.store_thm("MAP_EQ_MAP_IMP",
  `!xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)`,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP] \\ METIS_TAC []);
(*
NB: this is weaker:
val MAP_EQ_MAP_IMP = save_thm("MAP_EQ_MAP_IMP",
  INJ_MAP_EQ |> SIMP_RULE (srw_ss()) [INJ_DEF]);
*)

val LENGTH_EQ_FILTER_FILTER = Q.store_thm("LENGTH_EQ_FILTER_FILTER",
  `!xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))`,
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]);

val LIST_REL_MAP_FILTER_NEQ = store_thm("LIST_REL_MAP_FILTER_NEQ",
  ``∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))``,
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND])

(* move into HOL? *)

val bytes_in_word_def = Define `
  bytes_in_word = n2w (dimindex (:'a) DIV 8):'a word`;

val word_list_def = Define `
  (word_list a [] = emp) /\
  (word_list a (x::xs) = set_sep$one (a,x) * word_list (a + bytes_in_word) xs)`;

val word_list_exists_def = Define `
  word_list_exists a n =
    SEP_EXISTS xs. word_list a xs * cond (LENGTH xs = n)`;

val lookup_vars_def = Define `
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)`

val isHexDigit_HEX = Q.store_thm("isHexDigit_HEX",
  `∀n. n < 16 ⇒ isHexDigit (HEX n) ∧ (isAlpha (HEX n) ⇒ isUpper (HEX n))`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC);

val EVERY_isHexDigit_num_to_hex_string = Q.store_thm("EVERY_isHexDigit_num_to_hex_string",
  `∀n. EVERY (λc. isHexDigit c ∧ (isAlpha c ⇒ isUpper c)) (num_to_hex_string n)`,
  rw[ASCIInumbersTheory.num_to_hex_string_def,ASCIInumbersTheory.n2s_def]
  \\ rw[rich_listTheory.EVERY_REVERSE,listTheory.EVERY_MAP]
  \\ simp[EVERY_MEM]
  \\ gen_tac\\ strip_tac
  \\ match_mp_tac isHexDigit_HEX
  \\ qspecl_then[`16`,`n`]mp_tac numposrepTheory.n2l_BOUND
  \\ rw[EVERY_MEM]
  \\ res_tac
  \\ decide_tac);

val isHexDigit_isPrint = Q.store_thm("isHexDigit_isPrint",
  `∀x. isHexDigit x ⇒ isPrint x`,
  EVAL_TAC \\ rw[]);

val num_to_hex_string_length_1 = Q.store_thm("num_to_hex_string_length_1",
  `∀x. x < 16 ⇒ (LENGTH (num_to_hex_string x) = 1)`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC);

val num_to_hex_string_length_2 = Q.store_thm("num_to_hex_string_length_2",
  `∀x. 16 ≤ x ∧ x < 256 ⇒ (LENGTH (num_to_hex_string x) = 2)`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV (RAND_CONV EVAL))
  \\ strip_tac \\ var_eq_tac \\ pop_assum mp_tac
  \\ EVAL_TAC);

val num_from_hex_string_length_2 = Q.store_thm("num_from_hex_string_length_2",
  `num_from_hex_string [d1;d2] < 256`,
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`UNHEX d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`UNHEX d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac);

val num_from_hex_string_leading_0 = Q.store_thm("num_from_hex_string_leading_0",
  `∀ls. ls ≠ [] ⇒ (num_from_hex_string (#"0" :: ls) = num_from_hex_string ls)`,
  simp[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def]
  \\ ho_match_mp_tac SNOC_INDUCT \\ simp[]
  \\ simp[REVERSE_SNOC]
  \\ simp[numposrepTheory.l2n_def]
  \\ rw[]
  \\ Cases_on`ls` \\ fs[numposrepTheory.l2n_def]
  \\ EVAL_TAC);

val num_from_hex_string_length_2_less_16 = Q.store_thm("num_from_hex_string_length_2_less_16",
  `∀h1 h2. isHexDigit h1 ⇒ num_from_hex_string [h1;h2] < 16 ⇒ h1 = #"0"`,
  rw[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ Cases_on`UNHEX h1 MOD 16` \\ fs[]
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ fs[stringTheory.isHexDigit_def]
  \\ Cases_on`h1` \\ fs[]
  >- (
    `MEM (n - 48) (COUNT_LIST (58 - 48))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def])
  >- (
    `MEM (n - 97) (COUNT_LIST (103 - 97))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def]
    \\ `n = 97` by decide_tac
    \\ fs[ASCIInumbersTheory.UNHEX_def] )
  \\ `MEM (n - 65) (COUNT_LIST (71 - 65))` by simp[MEM_COUNT_LIST]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac
  \\ rfs[SUB_RIGHT_EQ]
  \\ fs[ASCIInumbersTheory.UNHEX_def]
  \\ `n = 65` by decide_tac
  \\ fs[ASCIInumbersTheory.UNHEX_def] )

val num_from_hex_string_num_to_hex_string = Q.store_thm("num_from_hex_string_num_to_hex_string[simp]",
  `num_from_hex_string (num_to_hex_string n) = n`,
  ASCIInumbersTheory.num_hex_string
  |> SIMP_RULE std_ss [combinTheory.o_DEF,FUN_EQ_THM]
  |> MATCH_ACCEPT_TAC)

val MAPi_ID = Q.store_thm("MAPi_ID[simp]",
  `MAPi (\x y. y) = I`,
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]);

val enumerate_def = Define`
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)`

val LENGTH_enumerate = Q.store_thm("LENGTH_enumerate",`
  ∀xs k. LENGTH (enumerate k xs) = LENGTH xs`,
  Induct>>fs[enumerate_def])

val EL_enumerate = store_thm("EL_enumerate",``
  ∀xs n k.
  n < LENGTH xs ⇒
  EL n (enumerate k xs) = (n+k,EL n xs)``,
  Induct>>fs[enumerate_def]>>rw[]>>
  Cases_on`n`>>fs[])

val MAP_enumerate_MAPi = store_thm("MAP_enumerate_MAPi",``
  ∀f xs.
  MAP f (enumerate 0 xs) = MAPi (λn e. f (n,e)) xs``,
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate])

val MAPi_enumerate_MAP = store_thm("MAPi_enumerate_MAP",``
  ∀f xs.
  MAPi f xs = MAP (λi,e. f i e) (enumerate 0 xs)``,
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate])

val MEM_enumerate = store_thm("MEM_enumerate",``
  ∀xs i e.
  i < LENGTH xs ⇒
  (MEM (i,e) (enumerate 0 xs) ⇔ EL i xs = e)``,
  fs[MEM_EL]>>rw[]>>eq_tac>>rw[LENGTH_enumerate]>>
  imp_res_tac EL_enumerate>>fs[]>>
  qexists_tac`i`>>fs[])

val MEM_enumerate_IMP = store_thm("MEM_enumerate_IMP",``
  ∀xs i e.
  MEM (i,e) (enumerate 0 xs) ⇒ MEM e xs``,
  fs[MEM_EL,LENGTH_enumerate]>>rw[]>>imp_res_tac EL_enumerate>>
  qexists_tac`n`>>fs[])

val SNOC_REPLICATE = Q.store_thm("SNOC_REPLICATE",
  `!n x. SNOC x (REPLICATE n x) = REPLICATE (SUC n) x`,
  Induct \\ fs [REPLICATE]);

val REVERSE_REPLICATE = Q.store_thm("REVERSE_REPLICATE",
  `!n x. REVERSE (REPLICATE n x) = REPLICATE n x`,
  Induct \\ fs [REPLICATE] \\ fs [GSYM REPLICATE,GSYM SNOC_REPLICATE]);

val SUM_REPLICATE = Q.store_thm("SUM_REPLICATE",
  `!n k. SUM (REPLICATE n k) = n * k`,
  Induct \\ full_simp_tac(srw_ss())[REPLICATE,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]);

val LENGTH_FLAT_REPLICATE = Q.store_thm("LENGTH_FLAT_REPLICATE",
  `∀n. LENGTH (FLAT (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val SUM_MAP_LENGTH_REPLICATE = Q.store_thm("SUM_MAP_LENGTH_REPLICATE",
  `∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val FLAT_REPLICATE_NIL = Q.store_thm("FLAT_REPLICATE_NIL",
  `!n. FLAT (REPLICATE n []) = []`,
  Induct \\ fs [REPLICATE]);

(* n.b. used in hol-reflection *)

val FDOM_FLOOKUP = Q.store_thm("FDOM_FLOOKUP",
  `x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v`,
  rw[FLOOKUP_DEF])

val FLAT_MAP_SING = Q.store_thm("FLAT_MAP_SING",
  `∀ls. FLAT (MAP (λx. [f x]) ls) = MAP f ls`,
  Induct \\ simp[]);

val FLAT_MAP_NIL = Q.store_thm("FLAT_MAP_NIL",
  `FLAT (MAP (λx. []) ls) = []`,
  rw[FLAT_EQ_NIL,EVERY_MAP]);

val UPDATE_LIST_NOT_MEM = Q.store_thm("UPDATE_LIST_NOT_MEM",
  `∀ls f x. ¬MEM x(MAP FST ls) ⇒ (f =++ ls) x = f x`,
  Induct >> simp[UPDATE_LIST_THM,combinTheory.APPLY_UPDATE_THM])

val MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same = store_thm("MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same",
  ``∀ks vs f. LENGTH ks = LENGTH vs ∧ ALL_DISTINCT ks ⇒ (MAP (f =++ ZIP (ks,vs)) ks = vs)``,
  Induct >> simp[LENGTH_NIL_SYM] >>
  gen_tac >> Cases >> simp[UPDATE_LIST_THM] >>
  simp[UPDATE_LIST_NOT_MEM,MAP_ZIP,combinTheory.APPLY_UPDATE_THM])

val MULT_LE_EXP = Q.store_thm("MULT_LE_EXP",
  `∀a:num b. a ≠ 1 ⇒ a * b ≤ a ** b`,
  Induct_on`b` >> simp[arithmeticTheory.MULT,arithmeticTheory.EXP] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`SUC n`mp_tac) >>
  simp[arithmeticTheory.MULT] >>
  Cases_on`b=0` >- (
    simp[arithmeticTheory.EXP] ) >>
  `SUC b ≤ b + b * n` suffices_by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  Cases_on`b * n` >> simp[] >>
  fs[arithmeticTheory.MULT_EQ_0] >> fs[])

val domain_rrestrict_subset = Q.store_thm("domain_rrestrict_subset",
  `domain (rrestrict r s) ⊆ domain r ∩ s`,
  rw[set_relationTheory.domain_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

val range_rrestrict_subset = Q.store_thm("range_rrestrict_subset",
  `range (rrestrict r s) ⊆ range r ∩ s`,
  rw[set_relationTheory.range_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

val PERM_MAP_BIJ = Q.store_thm("PERM_MAP_BIJ",
  `∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))`,
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP])

val INJ_MAP_EQ_IFF = Q.store_thm("INJ_MAP_EQ_IFF",
  `∀f l1 l2.
    INJ f (set l1 ∪ set l2) UNIV ⇒
    (MAP f l1 = MAP f l2 ⇔ l1 = l2)`,
  rw[] >> EQ_TAC >- metis_tac[INJ_MAP_EQ] >> rw[])

val bool_case_eq = Q.store_thm("bool_case_eq",
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.store_thm("pair_case_eq",
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val lookup_fromList2 = Q.store_thm("lookup_fromList2",
  `!l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE`,
  recInduct SNOC_INDUCT \\ srw_tac[][]
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  \\ full_simp_tac(srw_ss())[fromList2_def,FOLDL_SNOC]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[GSYM fromList2_def,FOLDL_SNOC]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_fromList,DIV_LT_X]
  \\ `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ full_simp_tac(srw_ss())[FOLDL]
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM DIV_LT_X,EL_SNOC]
  \\ full_simp_tac(srw_ss())[MULT_DIV,SNOC_APPEND,EL_LENGTH_APPEND,EVEN_MOD2,MOD_EQ_0]
  \\ TRY decide_tac
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `n = LENGTH l * 2 + 1` by decide_tac
  \\ full_simp_tac(srw_ss())[MOD_TIMES]);

val domain_fromList2 = Q.store_thm("domain_fromList2",
  `∀q. domain(fromList2 q) = set(GENLIST (λx. 2n*x) (LENGTH q))`,
  rw[EXTENSION,domain_lookup,lookup_fromList2,MEM_GENLIST,
     lookup_fromList,EVEN_EXISTS]
  \\ rw[EQ_IMP_THM] \\ rename1`2 * m`
  \\ qspecl_then[`2`,`m`]mp_tac MULT_DIV \\ simp[]);

val UNCURRY_eq_pair = Q.store_thm("UNCURRY_eq_pair",
  `UNCURRY f v = z ⇔ ∃a b. v = (a,b) ∧ f a b = z`,
  Cases_on`v`\\ rw[UNCURRY]);

val OLEAST_SOME_IMP = Q.store_thm("OLEAST_SOME_IMP",
  `$OLEAST P = SOME i ⇒ P i ∧ (∀n. n < i ⇒ ¬P n)`,
  simp[whileTheory.OLEAST_def]
  \\ metis_tac[whileTheory.LEAST_EXISTS_IMP]);

val EXP2_EVEN = Q.store_thm("EXP2_EVEN",
  `∀n. EVEN (2 ** n) ⇔ n ≠ 0`,
  Induct >> simp[EXP,EVEN_DOUBLE]);

val FST_UNZIP_MAPi = Q.store_thm(
  "FST_UNZIP_MAPi",
  `∀l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`,
  Induct >> simp[]);

val SND_UNZIP_MAPi = Q.store_thm(
  "SND_UNZIP_MAPi",
  `∀l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`,
  Induct >> simp[]);

val ALL_DISTINCT_FLAT = Q.store_thm(
  "ALL_DISTINCT_FLAT",
  `∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))`,
  Induct >> dsimp[ALL_DISTINCT_APPEND, LT_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]);

val TAKE_EQ_NIL = Q.store_thm(
  "TAKE_EQ_NIL[simp]",
  `TAKE n l = [] <=> n = 0 ∨ l = []`,
  Q.ID_SPEC_TAC `l` THEN Induct_on `n` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases THEN ASM_SIMP_TAC (srw_ss()) []);

val GSPEC_o = Q.store_thm(
  "GSPEC_o",
  `GSPEC f o g = { x | ∃y. (g x, T) = f y }`,
  simp[FUN_EQ_THM, GSPECIFICATION]);

val LIST_RELi_APPEND_I = Q.store_thm(
  "LIST_RELi_APPEND_I",
  `LIST_RELi R l1 l2 ∧ LIST_RELi (R o ((+) (LENGTH l1))) m1 m2 ⇒
   LIST_RELi R (l1 ++ m1) (l2 ++ m2)`,
  simp[LIST_RELi_EL_EQN] >> rpt strip_tac >>
  rename1 `i < LENGTH l2 + LENGTH m2` >> Cases_on `i < LENGTH l2`
  >- simp[EL_APPEND1]
  >- (simp[EL_APPEND2] >> first_x_assum (qspec_then `i - LENGTH l2` mp_tac) >>
      simp[]))

val NULL_APPEND = Q.store_thm("NULL_APPEND[simp]",
  `NULL (l1 ++ l2) ⇔ NULL l1 ∧ NULL l2`,
  simp[NULL_LENGTH]);

val MAP_DROP = Q.store_thm("MAP_DROP",
  `∀l i. MAP f (DROP i l) = DROP i (MAP f l)`,
  Induct \\ simp[DROP_def] \\ rw[]);

val MAP_FRONT = Q.store_thm("MAP_FRONT",
  `∀ls. ls ≠ [] ⇒ MAP f (FRONT ls) = FRONT (MAP f ls)`,
  Induct \\ simp[] \\ Cases_on`ls`\\fs[])

val LAST_MAP = Q.store_thm("LAST_MAP",
  `∀ls. ls ≠ [] ⇒ LAST (MAP f ls) = f (LAST ls)`,
  Induct \\ simp[] \\ Cases_on`ls`\\fs[])

val splitAtPki_push = Q.store_thm("splitAtPki_push",
  `f (splitAtPki P k l) = splitAtPki P (λl r. f (k l r)) l`,
  rw[splitAtPki_EQN]
  \\ BasicProvers.CASE_TAC \\ simp[]);

val splitAtPki_MAP = Q.store_thm("splitAtPki_MAP",
  `splitAtPki P k (MAP f l) = splitAtPki (λi x. P i (f x)) (λl r. k (MAP f l) (MAP f r)) l`,
  rw[splitAtPki_EQN,MAP_TAKE,MAP_DROP]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ rw[EQ_IMP_THM] \\ rfs[EL_MAP]);

val splitAtPki_change_predicate = Q.store_thm("splitAtPki_change_predicate",
  `(∀i. i < LENGTH l ⇒ P1 i (EL i l) = P2 i (EL i l)) ⇒
   splitAtPki P1 k l = splitAtPki P2 k l`,
  rw[splitAtPki_EQN]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ metis_tac[]);

val o_PAIR_MAP = Q.store_thm("o_PAIR_MAP",
  `FST o (f ## g) = f o FST ∧
   SND o (f ## g) = g o SND`,
  simp[FUN_EQ_THM]);

val any_el_ALT = Q.store_thm(
  "any_el_ALT",
  `∀l n d. any_el n l d = if n < LENGTH l then EL n l else d`,
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[]);

val _ = export_theory()
